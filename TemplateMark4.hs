
module TemplateMark4 where

import Language
import Utils

import Data.List


{-  (stack,dump,heap,globals)  -}

data Primitive
  = Neg | Add | Sub | Mul | Div
  deriving (Eq, Show)

data Node
  = NPrim Name Primitive
  | NAp  Addr Addr
  | NSupercomb Name [Name] CoreExpr
  | NNum Int
  | NInd Addr
  deriving Show

{-

遷移規則 (2.1)
        a:s  d  h[a:NAp a1 a2] f
 ==> a1:a:s  d  h              f

遷移規則 (2.2)
       a0:a1:...:an:s  d  h[a0:NSupercomb [x1,...,xn] body]  f
                 ar:s  d  h'                                 f
  ここで (h',ar) = instantiate body h f[x1 |-> a1,...,xn |-> an]
-}

run :: String -> String
run = showResults . eval . compile . parse


type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

data Stack a =
  Stack
  { list :: [a]
  , depth :: Int
  , maxDepth :: Int
  }

push :: a -> Stack a -> Stack a
push x Stack { list = xs, depth = d, maxDepth = maxd } =
  Stack { list = x:xs, depth = d+1, maxDepth = max (d + 1) maxd }

pop :: Stack a -> (a, Stack a)
pop s@Stack { list = xs, depth = d } =
  (head xs, s { list = tail xs, depth = d - 1})

discard :: Int -> Stack a -> Stack a
discard n s@(Stack { list = xs, depth = d }) = s { list = drop n xs, depth = max (d - n) 0 }

type TiStack = Stack Addr

-- data TiDump  = DummyTiDump
type TiDump  = [TiStack]

initialTiDump :: TiDump
initialTiDump = []

type TiHeap  = Heap Node

-- スーパーコンビネータ名と定義のリスト
type TiGlobals = Assoc Name Addr

-- とりあえずステップカウント
-- type TiStats = Int
data TiStats =
  TiStats
  { steps :: Int
  , scSteps :: Int
  , primSteps :: Int
  }

tiStatInitial :: TiStats
tiStatInitial = TiStats 0 0 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s { steps = steps s + 1 }
tiStatGetSteps :: TiStats -> Int
tiStatGetSteps = steps

tiStatIncScStep s = s { scSteps = scSteps s + 1 }

tiStatIncPrimStep s = s { primSteps = primSteps s + 1 }

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats f (stack, dump, heap, scDefs, stats) =
  (stack, dump, heap, scDefs, f stats)

compile :: CoreProgram -> TiState
-- compile program = undefined
compile program =
    (initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  where
    scDefs = program ++ preludeDefs ++ extraPreludeDefs
    (initialHeap, globals) = buildInitialHeap scDefs
    istack = [addressOfMain]
    initialStack = Stack { list = istack, depth = length istack, maxDepth = length istack }
    addressOfMain = aLookup globals "main" (error "main is not defined")

extraPreludeDefs :: CoreProgram
extraPreludeDefs = []

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
-- buildInitialHeap scDefs = mapAccumL allocateSc hInitial scDefs
buildInitialHeap scDefs =
    (heap2, scAddrs ++ primAddrs)
  where
    (heap1, scAddrs)   = mapAccumL allocateSc hInitial scDefs
    (heap2, primAddrs) = mapAccumL allocatePrim heap1 primitives

primitives :: Assoc Name Primitive
primitives = [ ("negate", Neg)
             , ("+", Add),  ("-", Sub)
             , ("*", Mul),  ("/", Div)
             , ("add", Add),  ("sub", Sub)
             , ("mul", Mul),  ("div", Div)
             ]
-- TODO: 二項演算の parser を実装する

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap scDefn = case scDefn of
  (name, args, body) -> (heap', (name, addr))
    where
      (heap', addr) = hAlloc heap (NSupercomb name args body)

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) =
    (heap', (name, addr))
  where
    (heap', addr) = hAlloc heap (NPrim name prim)

-- exercise 2.9
--   eval の結果の先頭の state が必ず一つ取れるのでこの方が良い
eval :: TiState -> [TiState]
eval state = state : restStates
  where
    restStates
      | tiFinal state = []
      | otherwise     = eval nextState
    nextState = doAdmin (step state)

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

doAdminScStep :: TiState -> TiState
doAdminScStep state = applyToStats tiStatIncScStep state

doAdminPrimStep :: TiState -> TiState
doAdminPrimStep state = applyToStats tiStatIncPrimStep state

tiFinal :: TiState -> Bool
tiFinal state = case state of
  (Stack { list = [soleAddr] }, [], heap, _, _) ->  isDataNode (hLookup heap soleAddr)
  (Stack { list = [] }, _, _, _, _)             ->  error "Empty stack!"
  _                                             ->  False

isDataNode :: Node -> Bool
isDataNode node = case node of
  NNum {}  ->  True
  _        ->  False

step :: TiState -> TiState
step state =
  case state of
    (stack, _dump, heap, _globals, _stats) -> dispatch (hLookup heap (head $ list stack))
      where
        dispatch (NPrim _n p)               =  primStep state p
        dispatch (NNum n)                   =  numStep state n
        dispatch (NAp a1 a2)                =  doAdminScStep $ apStep  state a1 a2
        dispatch (NSupercomb sc args body)  =  doAdminPrimStep $ scStep  state sc args body
        dispatch (NInd a)                   =  indStep state a

primStep :: TiState -> Primitive -> TiState
primStep state Neg  = primNeg state
primStep state p    = primArith state binOp
  where
    binOp = op p
    op Add = (+)
    op Sub = (-)
    op Mul = (*)
    op Div = div
    op p_  = error $ "primStep: not binary op: " ++ show p_

primNeg :: TiState -> TiState
primNeg _state@(stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b]
      | null (list stack2)  ->  case hLookup heap b of
          NNum n   -> (stack1,               dump, hUpdate heap ar (NNum (- n)), globals, stats)   -- (2.5 引数が評価済み)
          _        -> (push b stack2, stack1:dump,         heap                , globals, stats)   -- (2.6 引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primNeg: invalid stack: " ++ show (list stack)
    as   -> error $ "primNeg: wrong count of arguments" ++ show as
  where
    (_, stack1) = pop stack
    (ar, stack2) = pop stack1

-- exercise 2.17
primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith (stack, dump, heap, globals, stats) (<+>) =
  case getArgs heap stack of
    [b1,b2]
      | null (list stack3) -> case (hLookup heap b1, hLookup heap b2) of
          (NNum x, NNum y) -> (                  stack2,        dump, hUpdate heap ar (NNum $ x <+> y), globals, stats)   -- (2.5 引数が評価済み)
          (NNum _,      _) -> (          push b2 stack3, stack1:dump,         heap                    , globals, stats)   -- (2.6 引数が未評価 - 2.9 適用)
          (     _, NNum _) -> (          push b1 stack3, stack1:dump,         heap                    , globals, stats)   -- (2.6 引数が未評価 - 2.9 適用)
          (     _,      _) -> (push b1 $ push b2 stack3, stack1:dump,         heap                    , globals, stats)   -- (2.6 引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primAirth: invalid stack: " ++ show (list stack)
    as   -> error $ "primAirth: wrong count of arguments" ++ show as
  where
    (_, stack1)  = pop stack
    (_, stack2)  = pop stack1
    (ar, stack3) = pop stack2

numStep :: TiState -> Int -> TiState
-- numStep _state _n = error "Number applied as a function"
numStep state _n =
  case state of
    (stack, s:dump, heap, globals, stats)
      | null (list stack1) -> (s, dump, heap, globals, stats)
      | otherwise          -> error $
                              "numStep: invalid stack: " ++ show (list stack) ++ "\n" ++
                              unlines (map show $ allocs heap) ++ "\n"
                              -- unlines (map show $ dump)
      where
        (_a, stack1) = pop stack
    (    _,     [],     _,      _,     _) -> error $ "numStep: invalid state, dump is empty:\n" ++ showResults [state]

apStep :: TiState -> Addr -> Addr -> TiState
apStep state a1 a2 =
  case state of
    (stack, dump, heap, globals, stats) -> case hLookup heap a2 of
      NInd a3 ->  (        stack, dump, hUpdate (hFree heap a2) ar (NAp a1 a3), globals, stats)  -- (2.8)
      _       ->  (push a1 stack, dump,                heap,                    globals, stats)
      where
        (ar, _) = pop stack
-- TODO: 引数が間接参照になるケースを考える

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep state _scName argNames body = case state of
  (stack, dump, heap, globals, stats)
    | depth stack < length argNames + 1
      -> error "Too few argments given"
    | otherwise
      -> (stackD, dump, heap', globals, tiStatIncScStep stats)
  -- exercise 2.6
  -- (stack, _dump, heap, globals, _stats)
  --   -> (stack', _dump, heap', globals, _stats)
    where
      stackD = discard (length argNames) stack
      (an, _) = pop stackD
      heap' = instantiateAndUpdate body an heap env
      -- exercise 2.14
      env = argBindings ++ globals
      argBindings = zip argNames (getArgs heap stack)

indStep :: TiState -> Addr -> TiState
indStep state addr = case state of
  (stack, dump, heap, globals, stats)
    -> (push addr stack1, dump, heap, globals, stats)
    where
      (_, stack1) = pop stack

getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap stack =
  case list stack of
    []         -> error "Empty stack"
    _sc:stack' -> map getarg stack'
      where
        getarg addr = arg
          where
            NAp _fun arg = hLookup heap addr

instantiate :: CoreExpr
            -> TiHeap
            -> Assoc Name Addr
            -> (TiHeap, Addr)
instantiate expr heap env = case expr of
  ENum n                -> hAlloc heap (NNum n)
  EAp e1 e2             -> hAlloc heap2 (NAp a1 a2)
    where
      (heap1, a1) = instantiate e1 heap  env
      (heap2, a2) = instantiate e2 heap1 env
  EVar v  -> (heap, aLookup env v (error $ "Undefined name" ++ show v))
  EConstr tag arity     -> instantiateConstr tag arity heap env
  ELet isrec defs body  -> instantiateLet isrec defs body heap env
  ECase _e _alts        -> error "Can't instantiate case exprs"
  ELam _vs _e           -> error "Can't instantiate lambda abstractions"

instantiateAndUpdate :: CoreExpr
                     -> Addr
                     -> TiHeap
                     -> Assoc Name Addr
                     -> TiHeap
instantiateAndUpdate expr updAddr heap env = case expr of
  ENum n                -> hUpdate heap  updAddr (NNum n)
  EAp e1 e2             -> hUpdate heap2 updAddr (NAp a1 a2)
    where
      (heap1, a1) = instantiate e1 heap  env
      (heap2, a2) = instantiate e2 heap1 env
  EVar v  ->  hUpdate heap updAddr $ NInd (aLookup env v (error $ "Undefined name" ++ show v))
  EConstr tag arity     -> instantiateConstr tag arity heap env
  ELet isrec defs body  -> instantiateLetUpdate updAddr isrec defs body heap env
  ECase _e _alts        -> error "Can't instantiate case exprs"
  ELam _vs _e           -> error "Can't instantiate lambda abstractions"

instantiateConstr = undefined

instantiateLetUpdate :: Addr
                     -> Bool
                     -> [(Name, CoreExpr)]
                     -> CoreExpr
                     -> Heap Node
                     -> [(Name, Addr)]
                     -> TiHeap
instantiateLetUpdate updAddr isrec defs body heap env =
    instantiateAndUpdate body updAddr letHeap letEnv
  where
    letEnv = envDiff ++ env
    (letHeap, envDiff) = mapAccumL extendHeap heap defs
    extendHeap heap0 (n, expr) = (heap1, (n, a))
      where
        (heap1, a) = instantiate expr heap0
                     $ if isrec then letEnv else env

-- exercise 2.10
instantiateLet :: Bool
               -> [(Name, CoreExpr)]
               -> CoreExpr
               -> Heap Node
               -> [(Name, Addr)]
               -> (TiHeap, Addr)
instantiateLet isrec defs body heap env =
    instantiate body letHeap letEnv
  where
    letEnv = envDiff ++ env
    (letHeap, envDiff) = mapAccumL extendHeap heap defs
    extendHeap heap0 (n, expr) = (heap1, (n, a))
      where
        (heap1, a) = instantiate expr heap0
                     $ if isrec then letEnv else env

showResults :: [TiState] -> String
showResults states =
  unlines (map (iDisplay . showState) states ++
           [iDisplay (showStats $ last states)])
  -- iDisplay (iConcat [ iLayn (map showState states)
  --                   -- , showStats (last states)
  --                   ])

showState :: TiState -> IseqRep
showState (stack, _dump, heap, _globals, _stats)
  | showHeapP =
    iConcat [ showHeap heap, iNewline ]
    `iAppend`
    iConcat [ showStack heap stack, iNewline ]
  | otherwise =
    iConcat [ showStack heap stack, iNewline ]
  where
    showHeapP = True
-- exercise 2.5

showHeap :: TiHeap -> IseqRep
showHeap heap = case heap of
  Heap { allocs = contents, count = c } -> iConcat
    [ iStr "Heap ["
    , iIndent (iInterleave iNewline (map showHeapItem contents))
    , iStr " ]"
    , iNewline, iIndent (iStr "Allocation count = " `iAppend` iNum c)
    ]
  where
    showHeapItem (addr, node) =
      iConcat [ showFWAddr addr, iStr ": "
              , showNode node
              ]

showStack :: TiHeap -> TiStack -> IseqRep
showStack heap stack =
    iConcat
    [ iStr "Stack ["
    , iIndent (iInterleave iNewline (map showStackItem $ list stack))
    , iStr " ]"
    ]
  where
    showStackItem addr =
      iConcat
      [ showFWAddr addr,  iStr ": "
      , showStkNode heap (hLookup heap addr)
      ]

showStackMaxDepth :: TiStack -> IseqRep
showStackMaxDepth stack =
  iConcat [ iStr "Max stack depth = ", iNum (maxDepth stack) ]

showStkNode :: TiHeap -> Node -> IseqRep
showStkNode heap (NAp funAddr argAddr) =
  iConcat
  [ iStr "NAp ", showFWAddr funAddr
  , iStr " ", showFWAddr argAddr, iStr " ("
  , showNode (hLookup heap argAddr), iStr ")"
  ]
showStkNode _heap node = showNode node

showNode :: Node -> IseqRep
showNode node = case node of
  NPrim name _prim            -> iConcat [ iStr "NPrim ", iStr name ]
  NAp a1 a2                   -> iConcat [ iStr "NAp ", showAddr a1
                                         , iStr " ",    showAddr a2
                                         ]
  NSupercomb name _args _body -> iStr ("NSupercomb " ++ name)
  NNum n                      -> iStr "NNum " `iAppend` iNum n
  NInd a                      -> iStr "NInd " `iAppend` showAddr a

showAddr :: Addr -> IseqRep
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> IseqRep
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where
    str = show addr

showStats :: TiState -> IseqRep
showStats (stack, _dump, _heap, _globals, stats) =
  iConcat [ iNewline, iNewline
          , iStr "Total number of steps = ", iNum (tiStatGetSteps stats), iNewline
          , iStr "Super combinator steps = ", iNum (scSteps stats), iNewline
          , iStr "Primitive steps = ", iNum (primSteps stats), iNewline
          , showStackMaxDepth stack ]

-- exercise 2.4 - arranged
testProg0, testProg1, testProg2 :: String
testProg0 = "main = S K K 3"
testProg1 = "main = S K K" -- wrong not saturated
testProg2 = "id = S K K;\n\
            \main = twice twice twice id 3"
testProg3 = "pair x y f = f x y ;\n\
            \fst p = p K ;\n\
            \snd p = p K1 ;\n\
            \f x y = let\n\
            \            a = pair x y\n\
            \        in\n\
            \        fst a ;\n\
            \main = f 3 4"
testProg4 = "pair x y f = f x y ;\n\
            \fst p = p K ;\n\
            \snd p = p K1 ;\n\
            \f x y = letrec\n\
            \            a = pair x b ;\n\
            \            b = pair y a\n\
            \        in\n\
            \        fst (snd (snd (snd a))) ;\n\
            \main = f 3 4"
testFF = "main = letrec f = f f in f"
testFX = "main = letrec f = f x in f"
testFX3 = "main = letrec f = f x in 3"
testFG = "main = letrec f = g in f"
testUpdate = "id x = x ;\n\
             \main = twice twice id 3"
testUpdate2 = "id x = x ;\n\
              \main = twice twice twice id 3"

testDouble0 =
  "double x = x + x ;\n\
  \main = double 1"

testDouble1 =
  "double x = x + x ;\n\
  \main = double (1 + 1)"

testDouble2 =
  "double x = x + x ;\n\
  \main = double (double 1)"

testDouble3 =
  "double x = x + x ;\n\
  \main = double (S K K 3)"

testNeg = "main = negate 3"
testNeg2 = "main = negate (negate 3)"

testTwiceNeg = "main = twice negate 3"

testPlusN = "main = add 3 4"

testPlus = "main = 3 + 4"

testMul = "main = 3 * 4"

testInd = "main = let x = 3 in negate (I x)"

test :: String -> IO ()
test = putStrLn . showResults . eval . compile . parse
-- test = putStrLn . iDisplay . showState . head . eval . compile . parse
