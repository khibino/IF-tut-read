{-# LANGUAGE NPlusKPatterns #-}
module GMachineMark4 where

import Language
import Utils

import Data.List

import Control.Monad (when)
import Data.Either (isLeft)


data Stack a =
  Stack
  { list :: [a]
  , depth :: Int
  , maxDepth :: Int
  }
  deriving Show

stkOfList :: [a] -> Int -> Stack a
stkOfList xs md = Stack { list = xs, depth = length xs, maxDepth = md }

stkPush :: a -> Stack a -> Stack a
stkPush x Stack { list = xs, depth = d, maxDepth = maxd } =
  Stack { list = x:xs, depth = d+1, maxDepth = max (d + 1) maxd }

stkPop :: Stack a -> (a, Stack a)
stkPop s@Stack { list = xs, depth = d } =
  (head xs, s { list = tail xs, depth = d - 1})

stkPopN :: Int -> Stack a -> ([a], Stack a)
stkPopN n s@(Stack { list = xs, depth = d }) = (hd, s { list = tl, depth = max (d - n) 0 })
  where (hd, tl) = splitAt n xs

discard :: Int -> Stack a -> Stack a
discard n s = snd $ stkPopN n s
-- discard n s@(Stack { list = xs, depth = d }) = s { list = drop n xs, depth = max (d - n) 0 }

(<:>) :: a -> Stack a -> Stack a
(<:>) = stkPush

infixr 5 <:>

---

type GmState =
  ( GmCode
  , GmStack
  , GmDump
  , GmHeap
  , GmGlobals
  , GmStats
  )

type GmCode = [Instruction]

getCode :: GmState -> GmCode
getCode (i, _stack, _dump, _heap, _globals, _stats) = i

putCode :: GmCode -> GmState -> GmState
putCode i' (i, stack, dump, heap, globals, stats) =
  (i', stack, dump, heap, globals, stats)

data Instruction
  = Unwind
  | Pushglobal Name
  | Pushint Int
  | Push Int
  | Mkap
  | Slide Int
  | Alloc Int  {- exercise 3.14 -}
  | Update Int
  | Pop Int
  | Eval
  | Add | Sub | Mul | Div | Neg
  | Eq | Ne | Lt | Le | Gt | Ge
  | Cond GmCode GmCode
  deriving (Eq, Show)

type GmStack = Stack Addr
-- type GmStack = [Addr]

getStack :: GmState -> GmStack
getStack (_i, stack, _dump, _heap, _globals, _stats) = stack

putStack :: GmStack -> GmState -> GmState
putStack stack' (i, _stack, dump, heap, globals, stats) =
  (i, stack', dump, heap, globals, stats)

type GmDump = Stack GmDumpItem
type GmDumpItem = (GmCode, GmStack)

getDump :: GmState -> GmDump
getDump (_i, _stack, dump, _heap, _globals, _stats) = dump

putDump :: GmDump -> GmState -> GmState
putDump dump' (i, stack, _dump, heap, globals, stats) =
  (i, stack, dump', heap, globals, stats)

type GmHeap = Heap Node

getHeap :: GmState -> GmHeap
getHeap (_i, _stack, _dump, heap, _globals, _stats) = heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' (i, stack, dump, _heap, globals, stats) =
  (i, stack, dump, heap', globals, stats)

data Node
  = NNum Int             -- Numbers
  | NAp Addr Addr        -- Applications
  | NGlobal Int GmCode   -- Globals
  | NInd Addr            -- Indirections
  deriving (Eq, Show)

type GmGlobals = Assoc Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_i, _stack, _dump, _heap, globals, _stats) = globals

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals globals' (i, stack, dump, heap, _globals, stats) =
  (i, stack, dump, heap, globals', stats)

data GmStats =
  GmStats
  { steps :: Int
  , lastMaxHeap :: Int
  }

statInitial :: GmStats
statInitial = GmStats { steps = 0, lastMaxHeap = 0 }

statIncSteps :: GmStats -> GmStats
statIncSteps s = s { steps = steps s + 1 }

statGetSteps :: GmStats -> Int
statGetSteps = steps

getStats :: GmState -> GmStats
getStats (_i, _stack, _dump, _heap, _globals, stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats' (i, stack, dump, heap, globals, _stats) =
  (i, stack, dump, heap, globals, stats')

---

-- The evaluator

eval :: GmState -> [GmState]
eval state = state : restStates
  where
    restStates | gmFinal state    =  []
               | otherwise        =  eval nextState
    nextState = doAdmin (step state)

doAdmin :: GmState -> GmState
doAdmin s = putStats (statIncSteps (getStats s)) s

gmFinal :: GmState -> Bool
gmFinal s = null $ getCode s

---

step :: GmState -> GmState
step state = dispatch i (putCode is state)
  where (i:is) = getCode state

dispatch :: Instruction -> GmState -> GmState
dispatch = d
  where
    d (Pushglobal f) = pushglobal f
    d (Pushint n)    = pushint n
    d  Mkap          = mkap
    d (Push i)       = push i
    d (Slide i)      = slide i
    d (Alloc i)      = alloc i
    d (Update i)     = update i
    d (Pop i)        = pop i
    d  Unwind        = unwind
    -- exercise 3.9

    -- exercise 3.23
    d Eval           =  evalop
    d Add            =  arithmetic2 (+)
    d Sub            =  arithmetic2 (-)
    d Mul            =  arithmetic2 (*)
    d Div            =  arithmetic2 div
    d Neg            =  arithmetic1 negate

    d Eq             =  comparison (==)
    d Ne             =  comparison (/=)
    d Lt             =  comparison (<)
    d Le             =  comparison (<=)
    d Gt             =  comparison (>)
    d Ge             =  comparison (>=)

    -- d Cond c1 c2     =  cond c1 c2

pushglobal :: Name -> GmState -> GmState
pushglobal f state =
  putStack (a <:> getStack state) state
  where a = aLookup (getGlobals state) f (error ("Undeclared globals " ++ f))

pushint :: Int -> GmState -> GmState
pushint n state =
  putGlobals g (putHeap heap' (putStack (a <:> getStack state) state))
  where --- (heap', a) = hAlloc (getHeap state) (NNum n)
        -- exercise 3.6
        ((heap', a), g) = case aLookup globals name (-1) of
                          a' | a' < 0     ->  (hAlloc (getHeap state) (NNum n), (name, a') : globals)
                             | otherwise  ->  ((getHeap state, a'), globals)
        name = show n
        globals = getGlobals state

mkap :: GmState -> GmState
mkap state =
  putHeap heap' (putStack (a <:> as') state)
  where (heap', a) = hAlloc (getHeap state) (NAp a1 a2)
        (a1, as1) = stkPop $ getStack state
        (a2, as') = stkPop as1
        -- (a1:a2:as') = list $ getStack state

push :: Int -> GmState -> GmState
push n state =
  putStack (a <:> as) state
  where as = getStack state
        a  = list as !! n
        -- exercise 3.12

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2
getArg  n          = error $ "getArg: not NAp node: " ++ show n

slide :: Int -> GmState -> GmState
slide n state =
  putStack (a <:> discard n as) state
  where (a, as) = stkPop $ getStack state

update :: Int -> GmState -> GmState
update n state = putStack stk1 $ putHeap heap' state
  where
    (ea, stk1) = stkPop $ getStack state
    na = list stk1 !! n
    heap' = hUpdate (getHeap state) na (NInd ea)

-- exercise 3.15
alloc :: Int -> GmState -> GmState
alloc n state = putHeap h1 $ putStack s1 state
  where
    (h1, as) = allocNodes n $ getHeap state
    s1 = foldr stkPush (getStack state) as

allocNodes :: Int -> GmHeap -> (GmHeap, [Addr])
allocNodes 0     heap = (heap, [])
allocNodes (n+1) heap = (heap2, a:as)
  where
    (heap1, as) = allocNodes n heap
    (heap2, a)  = hAlloc heap1 (NInd hNull)
allocNodes x     _    = error $ "allocNodes: negative passed: "  ++ show x

pop :: Int -> GmState -> GmState
pop n state = putStack stkn state
  where
    stkn = discard n $ getStack state

unwind :: GmState -> GmState
unwind state =
  newState (hLookup heap a)
  where (a, as) = stkPop $ getStack state
        heap    = getHeap state
        dump    = getDump state

        newState (NNum _n)
          | null (list dump)  = state  {- rule 3.10 -}
          | otherwise         = putCode i' $ putStack (stkPush a s') $ putDump dump' $ state {- rule 3.22-} {- TODO: save maxDepth of as -}
            where ((i',s'), dump') = stkPop dump
        newState (NAp a1 _a2) = putCode [Unwind] (putStack (a1<:>a<:>as) state)
        newState (NGlobal n c)
          | depth as < n   =  error "Unwinding with too few arguments"
          | otherwise      =  putCode c $ putStack rstack state
          where rstack = rearrange n (getHeap state) $ getStack state  {- exercise 3.12 -}
        newState (NInd a1) =  putCode [Unwind] (putStack (a1<:>as) state)
        -- newState  n        =  error $ "unwind.newState: unknown node: " ++ show n

-- exercise 3.12
rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap as = foldr stkPush (discard n as) $ take n as'
  where
    (_, s) = stkPop as
    as' = map (getArg . hLookup heap) (list s)

evalop :: GmState -> GmState
evalop state = putCode [Unwind] $ putStack stack' $ putDump (stkPush (i,s) d) state {- rule 3.23 -}
  where (a, s) = stkPop $ getStack state
        stack' = stkOfList [a] 0 {- TODO: maxDepth s -}
        d = getDump state
        i = case getCode state of
          (_:is) -> is
          []    -> error "evalop: code is null!"


primitive1 :: (b -> GmState -> GmState)  -- boxing function
           -> (Addr -> GmState -> a)     -- unboxing fnction
           -> (a -> b)                   -- operator
           -> (GmState -> GmState)       -- state transition
primitive1 box unbox op state =
  box (op (unbox a state)) (putStack as state)  {- rule 3.25 -}
  where (a, as) = stkPop $ getStack state

primitive2 :: (b -> GmState -> GmState)  -- boxing function
           -> (Addr -> GmState -> a)     -- unboxing fnction
           -> (a -> a -> b)              -- operator
           -> (GmState -> GmState)       -- state transition
primitive2 box unbox op state =
  box (op (unbox a0 state) (unbox a1 state)) (putStack as state)  {-rule 3.24 -} {- rule 3.26 -}
  where (a0, (a1, as)) = stkPop <$> stkPop (getStack state)

boxInteger :: Int -> GmState -> GmState
boxInteger n state =
  putStack (stkPush a $ getStack state) (putHeap h' state)
  where (h', a) = hAlloc (getHeap state) (NNum n)

unboxInteger :: Addr -> GmState -> Int
unboxInteger a state =
  ub (hLookup (getHeap state) a)
  where ub (NNum i) = i
        ub _n       = error "Unboxing a non-integer"

arithmetic1 :: (Int -> Int)           -- arithmetic operator
            -> (GmState -> GmState)   -- state transition
arithmetic1 = primitive1 boxInteger unboxInteger

arithmetic2 :: (Int -> Int -> Int)    -- arithmetic operator
            -> (GmState -> GmState)   -- state transition
arithmetic2  = primitive2 boxInteger unboxInteger

boxBoolean :: Bool -> GmState -> GmState
boxBoolean b state =
  putStack (stkPush a $ getStack state) (putHeap h' state)
  where (h', a) = hAlloc (getHeap state) (NNum b')
        b' | b         = 1
           | otherwise = 0

comparison :: (Int -> Int -> Bool) -> GmState -> GmState
comparison = primitive2 boxBoolean unboxInteger

---

-- Compiling a program

compile :: CoreProgram -> GmState
compile program =
  (initialCode, Stack [] 0 0, Stack [] 0 0, heap, globals, statInitial)
  where (heap, globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program =
  mapAccumL allocateSc hInitial compiled
  where compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives
        -- compiled = map compileSc program

type GmCompiledSC = (Name, Int, GmCode)

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) =
  (heap', (name, addr))
  where (heap', addr) = hAlloc heap (NGlobal nargs instns)

initialCode :: GmCode
initialCode = [Pushglobal "main", Unwind]

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name, env, body) =
  (name, length env, compileR body $ zip env [0..])

type GmEnvironment = Assoc Name Int
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode

compileRslide :: GmCompiler
compileRslide e env = compileC e env ++ [Slide (length env + 1), Unwind]

compileR :: GmCompiler
compileR e env = compileC e env ++ [Update n, Pop n, Unwind]
  where n = length env

compileC :: GmCompiler
compileC (EVar v)     env
  | v `elem` (aDomain env)  =  [Push n]
  | otherwise               =  [Pushglobal v]
  where n = aLookup env v (error "compileC.EVar: Can't happen")
compileC (ENum n)     env   =  [Pushint n]
compileC (EAp e1 e2)  env   =  compileC e2 env ++
                               compileC e1 (argOffset 1 env) ++
                               [Mkap]
compileC (ELet recursive defs e) env
  | recursive  = compileLetrec compileC defs e env
  | otherwise  = compileLet    compileC defs e env

compileLet :: GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLet comp defs expr env =
  compileLet' defs env ++ comp expr env' ++ [Slide (length defs)]
  where env' = compileArgs defs env

compileLet' :: [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileLet' []                   env = []
compileLet' ((_name, expr):defs) env =
  compileC expr env ++ compileLet' defs (argOffset 1 env)

compileArgs :: [(Name, CoreExpr)] -> GmEnvironment -> GmEnvironment
compileArgs defs env =
  zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env
  where n = length defs

-- exercise 3.16
compileLetrec :: GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLetrec  comp defs expr env =
  [Alloc n] ++ compileLetrec' defs env' ++ comp expr env' ++ [Slide n]
  where
    env' = compileArgs defs env
    n = length defs

compileLetrec' :: [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileLetrec' []                   env = []
compileLetrec' ((_name, expr):defs) env =
  compileC expr env ++ [Update (length defs)] ++ compileLetrec' defs env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

---

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives = []

---

cK :: GmCompiledSC
cK = compileSc ("K", ["x", "y"], EVar "x")

cS :: GmCompiledSC
cS = compileSc ("S", ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x")))

skk3 :: CoreProgram
skk3 = [ ("main", [], ap3 (EVar "S") (EVar "K") (EVar "K") (ENum 3)) ]
  where ap2 f x y = EAp (EAp f x) y
        ap3 f x y z = EAp (ap2 f x y) z

test1 :: GmState
test1 = compile (skk3 ++ preludeDefs)

---

run :: String -> String
run = showResults . eval . compile . parse

evalList :: GmState -> [GmState]
evalList = undefined

compileList :: CoreProgram -> GmState
compileList program = undefined

extraPreludeDefs :: CoreProgram
extraPreludeDefs =
  [ ("False", [], EConstr 1 0)
  , ("True", [], EConstr 2 0)
  , ("and",["x","y"],EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "y")) (EVar "False"))

  -- exercise 2.20
  , ("or",["x","y"],EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "True")) (EVar "y"))
  , ("xor",["x","y"],EAp (EAp (EAp (EVar "if") (EAp (EAp (EVar "and") (EVar "x")) (EVar "y"))) (EVar "False")) (EAp (EAp (EVar "or") (EVar "x")) (EVar "y")))
  , ("not",["x"],EAp (EAp (EAp (EVar "if") (EVar "x")) (EVar "False")) (EVar "True"))

  , ("MkPair", ["x", "y"], EAp (EAp (EConstr 1 2) (EVar "x")) (EVar "y"))
  , ("fst", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K"))
  , ("snd", ["p"], EAp (EAp (EVar "casePair") (EVar "p")) (EVar "K1"))

  -- exercise 2.23
  , ("Nil", [], EConstr 1 0)
  , ("Cons", ["x", "xs"], EAp (EAp (EConstr 2 2) (EVar "x")) (EVar "xs"))
  , ("head", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "abort")) (EVar "K"))
  , ("tail", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "abort")) (EVar "K1"))

  , ("length", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (ENum 0)) (EVar "length'"))
  , ("length'", ["x", "xs"], EAp (EAp (EVar "+") (ENum 1)) (EAp (EVar "length") (EVar "xs")))

  , ("printList",["xs"],EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "stop")) (EVar "printCons"))
  , ("printCons",["h","t"],EAp (EAp (EVar "print") (EVar "h")) (EAp (EVar "printList") (EVar "t")))
  ]

showResults :: [GmState] -> String
showResults states =
  concat $
  map iDisplay $
  [ iNewline
  , iStr "Supercombinator definitions", iNewline
  , iInterleave iNewline $ map (showSC s) $ getGlobals s
  , iNewline, iNewline
  , iStr "State transitions", iNewline, iNewline ]
  ++
  (iLaynList $ map showState states)
  ++
  [ showState lastState ]
  ++
  [ iNewline, showStats lastState ]
  where (s:_ss) = states
        lastState = last states

showSC :: GmState -> (Name, Addr) -> IseqRep
showSC s (name, addr) =
  iConcat
  [ iStr "Code for ", iStr name, iNewline
  , showInstructions code ]
  where (NGlobal arity code) = hLookup (getHeap s) addr

showInstructions :: GmCode -> IseqRep
showInstructions is =
  iConcat
  [ iStr "  Code:{"
  , iIndent (iInterleave iNewline (map showInstruction is))
  , iStr "}", iNewline ]

showInstruction :: Instruction -> IseqRep
showInstruction  Unwind         =  iStr "Unwind"
showInstruction (Pushglobal f)  =  iStr "Pushglobal " `iAppend` iStr f
showInstruction (Push n)        =  iStr "Push " `iAppend` iNum n
showInstruction (Pushint n)     =  iStr "Pushint " `iAppend` iNum n
showInstruction  Mkap           =  iStr "Mkap"
showInstruction (Slide n)       =  iStr "Slide " `iAppend` iNum n
showInstruction (Alloc n)       =  iStr "Alloc " `iAppend` iNum n  {- exercise 3.14 -}
showInstruction (Update n)      =  iStr "Update " `iAppend` iNum n
showInstruction (Pop n)         =  iStr "Pop " `iAppend` iNum n
showInstruction (Cond xs ys)    =  iStr "Code " `iAppend` iCodes xs `iAppend` iCodes ys
  where iCodes cs = case cs of
          []    ->  iStr "[]"
          x:_   ->  iConcat [iStr "[", showInstruction x, iStr " ... ]"]
showInstruction  ins
  | ins `elem` [ Eval, Add, Sub, Mul, Div, Neg
               , Eq, Ne, Lt, Le, Gt, Ge]  =  iStr $ show ins
  | otherwise                             =  error $ "showInstruction: unknown instruction: " ++ show ins

showState :: GmState -> IseqRep
showState s =
  iConcat
  [ showStack s, iNewline
  , showDump s, iNewline
  , showInstructions (getCode s), iNewline ]

showDump :: GmState -> IseqRep
showDump s =
  iConcat
  [ iStr "  Dump:["
  , iIndent (iInterleave iNewline
             (map showDumpItem (reverse (list $ getDump s))))
  , iStr "]"
  ]

showDumpItem :: GmDumpItem -> IseqRep
showDumpItem (code, stack) =
  iConcat
  [ iStr "<"
  , shortShowInstructions 3 code, iStr ", "
  , shortShowStack stack,         iStr ">"
  ]

shortShowInstructions :: Int -> GmCode -> IseqRep
shortShowInstructions number code =
  iConcat
  [ iStr "{", iInterleave (iStr ";") dotcodes, iStr "}" ]
  where
    codes = map showInstruction (take number code)
    dotcodes | length code > number  = codes ++ [iStr "..."]
             | otherwise             = codes

shortShowStack :: GmStack -> IseqRep
shortShowStack stack =
  iConcat
  [ iStr "["
  , iInterleave (iStr ", ") (map showAddr $ list stack)
  , iStr "]"
  ]

{-
showHeap :: GmHeap -> IseqRep
showHeap heap = undefined
 -}
  -- Heap { allocs = contents, count = c } -> iConcat
  --   [ iStr "Heap ["
  --   , iIndent (iInterleave iNewline (map showHeapItem contents))
  --   , iStr " ]"
  --   , iNewline, iIndent (iStr "Allocation count = " `iAppend` iNum c)
  --   ]
  -- where
  --   showHeapItem (addr, node) =
  --     iConcat [ showFWAddr addr, iStr ": "
  --             , showNode node
  --             ]

-- showStack :: Bool -> GmHeap -> GmStack -> IseqRep
showStack :: GmState -> IseqRep
showStack s =
  iConcat
  [ iStr " Stack:["
  , iIndent (iInterleave iNewline $ map showStackItem (reverse $ list $ getStack s))
  , iStr "]"
  ]
  where
    showStackItem a =
      iConcat
      [ showFWAddr a,  iStr ": "
      , showNode s a (hLookup (getHeap s) a)
      ]

{-
showStackMaxDepth :: GmStack -> IseqRep
showStackMaxDepth stack = undefined
 -}

{-
showStkNode :: Bool -> GmHeap -> Node -> IseqRep
showStkNode nestedDebug heap n = undefined
-- showStkNode _  _heap node = showNode node
 -}

{-
debugNestedAp :: Heap Node -> Node -> IseqRep
debugNestedAp heap = rec_ id
  where
    paren s = iConcat [iStr "(", s, iStr ")"]
    rec_ pf (NAp fun arg) =
      pf $ iConcat [rec_ id (hLookup heap fun), iStr " ", rec_ paren (hLookup heap arg)]
    rec_ _ x             =
      leaf x
    leaf (NAp {})           =  error "bug: showNestedAp: leaf called for NAp"
    leaf (NPrim n _)        =  iStr n
    leaf (NSupercomb n _ _) =  iStr n
    leaf (NNum i)           =  iStr $ show i
    leaf (NInd a)           =  iStr $ showA a
    leaf (NData t as@[])    =  iStr $ showNData t as
    leaf (NData t as@(_:_)) =  iStr $ "(" ++ showNData t as ++ ")"
    showNData t as = unwords $ ("<" ++ show t ++ ">") : map showA as
    showA a = "[" ++ show a ++ "]"
 -}

showNode :: GmState -> Addr -> Node -> IseqRep
showNode s a node   = case node of
  NNum n       ->  iNum n
  NGlobal n g  ->  iConcat [iStr "Global ", iStr v]
    where v = head [n | (n,b) <- getGlobals s, a == b]
  NAp a1 a2    ->  iConcat
                   [ iStr "Ap ", showAddr a1
                   , iStr " ",   showAddr a2 ]
  NInd a1      ->  iConcat [iStr "NInd ", showAddr a1]
  -- exercise 3.8

showAddr :: Addr -> IseqRep
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> IseqRep
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where
    str = show addr

showStats :: GmState -> IseqRep
showStats s =
  iConcat
  [ iStr "Steps taken = ", iNum (statGetSteps stats), iNewline
  , iStr "Max heap size = ", iNum (hSize heap `max` lastMaxHeap stats)
  , iStr " (last: ", iNum (lastMaxHeap stats), iStr ")" ]
  where
    heap = getHeap s
    stats = getStats s

showOutput :: GmState -> IseqRep
showOutput = undefined

-- exercise 2.4 - arranged
testProg0, testProg1, testProg2 :: String
testProg0 = "main = S K K 3"
testProg1 = "main = S K K" -- wrong not saturated
testProg2 = "id = S K K;\n\
            \main = twice twice twice id 3"
testProg2a = "id = S K K;\n\
             \twic f x = f (f x);\n\
             \main = twic twic twic id 3"
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

testDouble4 =
  "double x = x + x ;\n\
  \main = double (double (S K K 3))"

testTak =
  "tak x y z = if (y < x) (tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y)) y ;\n\
  \main = tak 2 1 0"

testNeg = "main = negate 3"
testNeg2 = "main = negate (negate 3)"

testTwiceNeg = "main = twice negate 3"

testPlusN = "main = add 3 4"

testPlus = "main = 3 + 4"

testPlus2 = "main = (1 + 2) + (4 + 8)"

testMul = "main = 3 * 4"

testInd = "main = let x = 3 in negate (I x)"

testIf = "main = if True 0 1"
testIf2 = "main = if False 0 1"

-- exercise 2.21
testFac = "fac n = if (n == 0) 1 (n * fac (n-1)) ;\
          \main = fac 3"

testCasePair = "main = fst (snd (fst (MkPair (MkPair 1 (MkPair 2 3)) 4)))"

testLength = "main = length (Cons 1 (Cons 2 (Cons 3 Nil)))"

testPrintList = "main = Cons 1 (Cons 2 (Cons 3 Nil))"

testPrintList2 = "main = Cons (1 + 2) (Cons 2 (Cons 3 Nil))"

testY = "Y f = letrec x = f x in x"

-- exercise 3.13
testB11A = "main = I 3"

testB11B = "id = S K K ;\
           \main =id 3"

testB11C = "id = S K K ;\
           \main = twice twice twice id 3"

testB12 = "main = twice (I I I) 3"

test_ :: Bool -> String -> IO ()
test_ nestedDebug = putStrLn . showResults . eval . compile . parse
-- test_ nestedDebug = putStrLn . showResults . eval . setDebug . compile . parse
--   where setDebug = applyToStats (tiStatSetDebugNested nestedDebug)

test :: String -> IO ()
test = test_ True

qtest :: String -> IO ()
qtest = test_ False

testList :: String -> IO ()
testList = putStrLn . showResults . evalList . compileList . parse

check :: Node -> String -> Either String String
check expect prog
  | length states == limit  =  Left  . unlines $ ("expect " ++ show expect) : showProg "too long: "
  | lastv == expect         =  Right . unlines $ showProg "pass: " ++ [show lastv]
  | otherwise               =  Left  . unlines $ ("expect " ++ show expect) : showProg "wrong: "
  where
    states = take limit . eval . compile . parse $ prog
    limit = 1000000
    -- (   _, lastStack, _, lHeap, _, _) = last states
    lastStack = undefined
    lHeap = undefined
    (a, _) = stkPop lastStack
    lastv = hLookup lHeap a :: Node

    showProg word =
      zipWith (++)
      (word : repeat (replicate (length word) ' '))
      (lines prog)

checks :: IO ()
checks = do
  mapM_ (either putLn putLn) results
  when (any isLeft results) $ fail "some checks failed!"
  where
    results = map (uncurry check) checkList
    putLn s = putStrLn "" *> putStr s

checkList :: [(Node, String)]
checkList = []
 {-
  [ (NNum    1, "main = 1")      -- single value

  , (NNum    3, "main = S K K 3") -- supercombinator
  , (NNum    3, "id = S K K;\n\
                \main = twice twice twice id 3") -- supercombinator nested
  , (NNum (-3), "main = negate 3") -- negate
  , (NNum    3, "main = negate (negate 3)") -- negate nested
  , (NNum    3, "main = 1 + 2")  -- plus
  , (NNum   15, "main = (1 + 2) + (4 + 8)") -- plus nested
  , (NNum    6, "main = 2 * 3")  -- mul
  , (NNum   36, "main = (2 * 3) * (2 * 3)")  -- mul nested

  , (NNum    2, "double x = x + x ;\n\
                \main = double 1") -- indirection, supercombinator, plus
  , (NNum    4, "double x = x + x ;\n\
                \main = double (1 + 1)") -- indirection, supercombinator, plus nested
  , (NNum    4, "double x = x + x ;\n\
                \main = double (double 1)") -- indirection, supercombinator, plus nested
  , (NNum    6, "double x = x + x ;\n\
                \main = double (S K K 3)") -- indirection, supercombinator, plus nested

  , (NNum    3, "main = if False 5 3") -- if
  , (NNum    5, "main = if True 5 3") -- if
  , (NNum    6, "fac n = if (n == 0) 1 (n * fac (n-1)) ;\
                \main = fac 3")       -- if, recursive function

  , (NNum    1, "main = fst (MkPair 1 2)") -- casePair
  , (NNum    2, "main = snd (MkPair 1 2)") -- casePair
  , (NNum    2, "main = fst (snd (fst (MkPair (MkPair 1 (MkPair 2 3)) 4)))") -- casePair nested

  , (NNum    3, "main = length (Cons 1 (Cons 2 (Cons 3 Nil)))") -- caseList
  ]
 -}
