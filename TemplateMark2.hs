
module TemplateMark2 where

import Language
import Utils

import Data.List


{-  (stack,dump,heap,globals)  -}

data Node
  = NAp  Addr Addr
  | NSupercomb Name [Name] CoreExpr
  | NNum Int
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

discard :: Int -> Stack a -> Stack a
discard n s@(Stack { list = xs, depth = d }) = s { list = drop n xs, depth = max (d - n) 0 }

type TiStack = Stack Addr

data TiDump  = DummyTiDump
  deriving Show

initialTiDump :: TiDump
initialTiDump = DummyTiDump

type TiHeap  = Heap Node

-- スーパーコンビネータ名と定義のリスト
type TiGlobals = Assoc Name Addr

-- とりあえずステップカウント
type TiStats = Int

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s + 1
tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

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
buildInitialHeap scDefs = mapAccumL allocateSc hInitial scDefs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap scDefn = case scDefn of
  (name, args, body) -> (heap', (name, addr))
    where
      (heap', addr) = hAlloc heap (NSupercomb name args body)

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

tiFinal :: TiState -> Bool
tiFinal state = case state of
  (Stack { list = [soleAddr] }, _, heap, _, _)  ->  isDataNode (hLookup heap soleAddr)
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
    dispatch (NNum n)                   =  numStep state n
    dispatch (NAp a1 a2)                =  apStep  state a1 a2
    dispatch (NSupercomb sc args body)  =  scStep  state sc args body

numStep :: TiState -> Int -> TiState
numStep _state _n = error "Number applied as a function"

apStep :: TiState -> Addr -> Addr -> TiState
apStep state a1 _a2 =
  case state of
    (stack, dump, heap, globals, stats)  ->  (push a1 stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep state _scName argNames body = case state of
  (stack, _dump, heap, globals, _stats)
    | depth stack < length argNames + 1
      -> error "Too few argments given"
    | otherwise
      -> (stack', _dump, heap', globals, _stats)
  -- exercise 2.6
  -- (stack, _dump, heap, globals, _stats)
  --   -> (stack', _dump, heap', globals, _stats)
    where
      stack' = push resultAddr $ discard (length argNames + 1) stack
      (heap', resultAddr) = instantiate body heap env
      env = argBindings ++ globals
      argBindings = zip argNames (getargs heap stack)

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap stack =
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

instantiateConstr = undefined

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
  iDisplay (iConcat [ iLayn (map showState states)
                    , showStats (last states)
                    ])

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
  NAp a1 a2                   -> iConcat [ iStr "NAp ", showAddr a1
                                         , iStr " ",    showAddr a2
                                         ]
  NSupercomb name _args _body -> iStr ("NSupercomb " ++ name)
  NNum n                      -> iStr "NNum " `iAppend` iNum n

showAddr :: Addr -> IseqRep
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> IseqRep
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where
    str = show addr

showStats :: TiState -> IseqRep
showStats (stack, _dump, _heap, _globals, stats) =
  iConcat [ iNewline, iNewline, iStr "Total number of steps = "
          , iNum (tiStatGetSteps stats)
          , iNewline, showStackMaxDepth stack
          ]

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
testLetrec = "f x y = letrec\n\
             \            a = pair x b ;\n\
             \            b = pair y a\n\
             \        in\n\
             \        fst (snd (snd (snd a)))"

test :: String -> IO ()
test = putStrLn . showResults . eval . compile . parse
