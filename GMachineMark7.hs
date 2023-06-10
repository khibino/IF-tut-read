{-# LANGUAGE NPlusKPatterns #-}
module GMachineMark7 where

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
  ( GmOutput
  , GmCode
  , GmStack
  , GmDump
  , GmHeap
  , GmGlobals
  , GmStats
  )

type GmOutput = [Char]

type GmCode = [Instruction]

getOutput :: GmState -> GmOutput
getOutput (out, _i, _stack, _dump, _heap, _globals, _stats) = out

putOutput :: GmOutput -> GmState -> GmState
putOutput out' (_out, i, stack, dump, heap, globals, stats) =
  (out', i, stack, dump, heap, globals, stats)

getCode :: GmState -> GmCode
getCode (_out, i, _stack, _dump, _heap, _globals, _stats) = i

putCode :: GmCode -> GmState -> GmState
putCode i' (out, _i, stack, dump, heap, globals, stats) =
  (out, i', stack, dump, heap, globals, stats)

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
  | Pack Int Int
  | Casejump [(Int, GmCode)]
  | Split Int
  | Print
  deriving (Eq, Show)

type GmStack = Stack Addr
-- type GmStack = [Addr]

getStack :: GmState -> GmStack
getStack (_out, _i, stack, _dump, _heap, _globals, _stats) = stack

putStack :: GmStack -> GmState -> GmState
putStack stack' (out, i, _stack, dump, heap, globals, stats) =
  (out, i, stack', dump, heap, globals, stats)

type GmDump = Stack GmDumpItem
type GmDumpItem = (GmCode, GmStack)

getDump :: GmState -> GmDump
getDump (_out, _i, _stack, dump, _heap, _globals, _stats) = dump

putDump :: GmDump -> GmState -> GmState
putDump dump' (out, i, stack, _dump, heap, globals, stats) =
  (out, i, stack, dump', heap, globals, stats)

type GmHeap = Heap Node

getHeap :: GmState -> GmHeap
getHeap (_out, _i, _stack, _dump, heap, _globals, _stats) = heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' (out, i, stack, dump, _heap, globals, stats) =
  (out, i, stack, dump, heap', globals, stats)

data Node
  = NNum Int             -- Numbers
  | NAp Addr Addr        -- Applications
  | NGlobal Int GmCode   -- Globals
  | NInd Addr            -- Indirections
  | NConstr Int [Addr]
  | NgNode Int Int
  deriving Show

instance Eq Node
  where
    NNum a    ==  NNum b    =  a == b
    _         ==  _         =  False

type GmGlobals = Assoc Name Addr

getGlobals :: GmState -> GmGlobals
getGlobals (_out, _i, _stack, _dump, _heap, globals, _stats) = globals

putGlobals :: GmGlobals -> GmState -> GmState
putGlobals globals' (out, i, stack, dump, heap, _globals, stats) =
  (out, i, stack, dump, heap, globals', stats)

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
getStats (_out, _i, _stack, _dump, _heap, _globals, stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats' (out, i, stack, dump, heap, globals, _stats) =
  (out, i, stack, dump, heap, globals, stats')

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

    d (Cond i1 i2)   =  cond i1 i2

    d (Pack t n)     =  pack t n
    d (Casejump jm)  =  casejump jm
    d (Split n)      =  split n
    d Print          =  print_

pushglobal :: Name -> GmState -> GmState
pushglobal f state = case f `lookup` globals of
  Nothing  ->  case gNodes of
    []     ->  error $ "Undeclared globals " ++ f
    [gn]   ->  putStack (a <:> getStack state) (putHeap heap state)  {- rule 3.38 -}
      where (heap, a) = hAlloc (getHeap state) gn
    _:_:_  ->  error $ "pushglobal: unknown pattern: " ++ show gNodes
  Just a   ->  putStack (a <:> getStack state) state                 {- rule 3.5, rule 3.37 -}
  where
    globals = getGlobals state
    gNodes = [ NgNode t n | (EConstr t n, []) <- pPack $ clex 0 f ]

pushint :: Int -> GmState -> GmState
pushint n state =
  putGlobals g (putHeap heap' (putStack (a <:> getStack state) state))
  where --- (heap', a) = hAlloc (getHeap state) (NNum n)
        -- exercise 3.6
        ((heap', a), g) = case aLookup globals name (-1) of
                          a' | a' < 0     ->  (hAlloc (getHeap state) (NNum n), (name, a') : globals)  {- rule 3.14-}
                             | otherwise  ->  ((getHeap state, a'), globals)                           {- rule 3.13-}
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
          | k < n
          , (ak, _) <- stkPop $ discard (k - 1) as
          , ((i,s), dump') <- stkPop dump
                           =  putCode i $ putStack (stkPush ak s) $ putDump dump' state  {- rule 3.29 -}  {- exercise 3.29 -}
          | otherwise      =  putCode c $ putStack rstack state  {- rule 3.19, updated from rule 3.12 -}
          where k = depth as
                rstack = rearrange n (getHeap state) $ getStack state  {- exercise 3.12 -}
        newState (NInd a1) =  putCode [Unwind] (putStack (a1<:>as) state)
        newState (NConstr _n _as) = putCode i' $ putStack (a<:>s') $ putDump dump' state  {- rule 3.35 -}
          where ((i',s'), dump') = stkPop dump
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
        i = getCode state


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
  where (h', a) = hAlloc (getHeap state) (NConstr b' [])
        b' | b         = 2  {- True  is EConstr 2 0 -}  {- rule 3.36 -}
           | otherwise = 1  {- False is EConstr 1 0 -}  {- rule 3.36 -}

comparison :: (Int -> Int -> Bool) -> GmState -> GmState
comparison = primitive2 boxBoolean unboxInteger

cond :: GmCode -> GmCode -> (GmState -> GmState)
cond i1 i2 state = putCode (ni ++ i) $ putStack s state {- rule 3.27 -} {- rule 3.28 -}
  where (a,s) = stkPop (getStack state)
        ni = case hLookup (getHeap state) a of
          NNum 1  -> i1
          NNum 0  -> i2
          n       -> error $ "cond: not expected NNum node: " ++ show n
        i = getCode state

pack :: Int -> Int -> (GmState -> GmState)
pack t n state = putStack (stkPush a s) (putHeap h state)  {- rule 3.30 -}
  where (as, s) = stkPopN n (getStack state)
        (h, a) = hAlloc (getHeap state) (NConstr t as)

casejump :: [(Int, GmCode)] -> GmState -> GmState
casejump jm state = case hLookup h a of
  NConstr t _ss  ->  case lookup t jm of
    Nothing  ->  error $ "casejump: tag not found: " ++ show t
    Just i'  ->  putCode (i' ++ getCode state) state  {- rule 3.31 -}
  n          ->  error $ "casejump: constructor not found: " ++ show n
  where (a, _s) = stkPop (getStack state)
        h = getHeap state

split :: Int -> GmState -> GmState
split n state = case hLookup (getHeap state) a of
  NConstr _t as
    | length as == n  ->  putStack (foldr stkPush s as) state  {- rule 3.32 -}
    | otherwise       ->  error $ "split: argument count mismatch: " ++ show (length as) ++ " =/= " ++ show n
  node                ->  error $ "split: constructor not found: " ++ show node
  where (a, s) = stkPop (getStack state)

print_ :: GmState -> GmState
print_ state = case hLookup (getHeap state) a of
  NNum n         ->  putOutput (getOutput state ++ show n) state  {- rule 3.33 -}
  NConstr _t as  ->  putCode i' $ putStack s1 state  {- rule 3.34 -}
    where s1 = foldr stkPush s as
          i' = take (length as * 2) (cycle [Eval, Print]) ++ getCode state
  node          ->  error $ "print: not NNum or NConstr: " ++ show node
  where (a,s) = stkPop (getStack state)

---

builtInDyadic :: Assoc Name Instruction
builtInDyadic =
  [ ("+", Add), ("-", Sub), ("*", Mul), ("div", Div)
  , ("==", Eq), ("~=", Ne), (">=", Ge)
  , (">", Gt), ("<=", Le), ("<", Lt)
  ]

-- Compiling a program

compile :: CoreProgram -> GmState
compile program =
  ([], initialCode, Stack [] 0 0, Stack [] 0 0, heap, globals, statInitial)
  where (heap, globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program =
  mapAccumL allocateSc hInitial compiled
  where compiled = map compileSc (preludeDefs ++ extraPreludeDefs ++ program) ++ compiledPrimitives
        -- compiled = map compileSc program

type GmCompiledSC = (Name, Int, GmCode)

allocateSc :: GmHeap -> GmCompiledSC -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) =
  (heap', (name, addr))
  where (heap', addr) = hAlloc heap (NGlobal nargs instns)

initialCode :: GmCode
initialCode = [Pushglobal "main", Eval, Print]
-- initialCode = [Pushglobal "main", Unwind]

{- exercise 3.24
rule 3.23 からすると、 (空命令列, 空スタック) が dump に積まれるかどうかが異なる.

 -}

compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSC
compileSc (name, env, body) =
  (name, length env, compileR body $ zip env [0..])  {- Fig 3.3  p.100 -}

type GmEnvironment = Assoc Name Int
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode

compileRslide :: GmCompiler
compileRslide e env = compileC e env ++ [Slide (length env + 1), Unwind]

compileR :: GmCompiler
compileR e env = compileE e env ++ [Update n, Pop n, Unwind]  {- Fig 3.12  p.127 -} {- exercise 3.28 -}
  where n = length env

compileE' :: Int -> GmCompiler
compileE' offset expr env =
  [Split offset] ++ compileE expr env ++ [Slide offset]  {- Fig 3.14  p.134  𝓐 scheme -}

-- |
--
-- >>> compileE (EAp (EAp (EVar "f") (ENum 3)) (ENum 4)) []
-- [Pushint 4,Pushint 3,Pushglobal "f",Mkap,Mkap,Eval]
--
-- >>> compileE (EAp (EAp (EConstr 1 2) (ENum 3)) (ENum 4)) []
-- [Pushint 4,Pushint 3,Pack 1 2]
--
-- exercise 3.28
compileE :: GmCompiler
compileE (ENum n) _env =  [Pushint n]  {- Fig 3.12  p.127 -}
compileE (ELet recursive defs e) env
  | recursive  = compileLetrec compileE defs e env  {- Fig 3.12  p.127 -}
  | otherwise  = compileLet    compileE defs e env  {- Fig 3.12  p.127 -}
compileE (EAp (EAp (EVar opn) e0) e1) env
  | Just op <- lookup opn builtInDyadic = compileE e1 env ++ compileE e0 env ++ [op]  {- Fig 3.12  p.127 -}
compileE (EAp (EVar "negate") e) env = compileE e env ++ [Neg]  {- Fig 3.12  p.127 -}
-- compileE (EAp (EAp (EAp (EVar "if") e0) e1) e2) env =
--   compileE e0 env ++ [Cond (compileE e1 env) (compileE e2 env)]  {- Fig 3.12  p.127 -}
compileE (ECase e alts) env =
  compileE e env ++ [Casejump (compileAlts compileE' alts env)]  {- Fig 3.14  p.134 -}
compileE (EConstr t n) env  =  [Pack t n]
compileE e@(EAp {}) env
  | EConstr {} <- f  = concatI (++)  {- Fig 3.14  p.134  Pack -}
  where (f, concatI) = compileCaps e env 0
  {- Figure 3.14 のコンパイル規則によると、
     f が EConstr の場合は compileE と compileC は等しいと考えられる.
     しかし、それ以外の、たとえば関数適用の場合には以前の規則が適用されると考えられる.
     するとデフォルトの規則により末尾に Eval が付くかどうかが異なることになる. -}
compileE e env = compileC e env ++ [Eval]  {- Fig 3.12  p.127 -}

-- |
--
-- >>> compileC (EAp (EAp (EVar "f") (ENum 3)) (ENum 4)) []
-- [Pushint 4,Pushint 3,Pushglobal "f",Mkap,Mkap]
--
-- >>> compileC (EAp (EAp (EConstr 1 2) (ENum 3)) (ENum 4)) []
-- [Pushint 4,Pushint 3,Pack 1 2]
compileC :: GmCompiler
compileC (EVar v)     env
  | v `elem` (aDomain env)  =  [Push n]              {- Fig 3.10  p.114, Fig 3.3  p.100 -}
  | otherwise               =  [Pushglobal v]        {- Fig 3.10  p.114, Fig 3.3  p.100 -}
  where n = aLookup env v (error "compileC.EVar: Can't happen")
compileC (ENum n)     env   =  [Pushint n]           {- Fig 3.10  p.114, Fig 3.3  p.100 -}
compileC (EConstr t n) env  =  [Pushglobal $ "Pack{" ++ show t ++ "," ++ show n ++ "}"]
compileC e@(EAp {})   env   =  case f of
  EConstr {}  ->  concatI (++)
  _           ->  concatI (\i2 i1 -> i2 ++ i1 ++ [Mkap])
  where (f, concatI) = compileCaps e env 0
compileC (ELet recursive defs e) env
  | recursive  = compileLetrec compileC defs e env  {- Fig 3.10  p.114 -}
  | otherwise  = compileLet    compileC defs e env  {- Fig 3.10  p.114 -}

compileCaps :: CoreExpr -> GmEnvironment -> Int -> (CoreExpr, (GmCode -> GmCode -> GmCode) -> GmCode)
compileCaps (f@(EConstr t n)) env c
  | c == n                           =  (f, \_      ->  [Pack t n])  {- Fig 3.14  p.134  Pack -}
compileCaps (EAp e1 e2)       env c  =  (f, \ (<+>) ->  compileC e2 env <+> concatI1 (<+>))   {- Fig 3.10  p.114, Fig 3.3  p.100 -}
  where (f, concatI1) = compileCaps e1 (argOffset 1 env) (c+1)
compileCaps f                 env _  =  (f, \_      ->  compileC f env)   {- function and unsaturated constructor case, p.137, last of section 3.8.7 -}

compileLet :: GmCompiler -> [(Name, CoreExpr)] -> GmCompiler
compileLet comp defs expr env =
  compileLet' defs env ++ comp expr env' ++ [Slide (length defs)]  {- Fig 3.10  p.114 -}
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
  [Alloc n] ++ compileLetrec' defs env' ++ comp expr env' ++ [Slide n]  {- Fig 3.10  p.114 -}
  where
    env' = compileArgs defs env
    n = length defs

compileLetrec' :: [(Name, CoreExpr)] -> GmEnvironment -> GmCode
compileLetrec' []                   env = []
compileLetrec' ((_name, expr):defs) env =
  compileC expr env ++ [Update (length defs)] ++ compileLetrec' defs env

argOffset :: Int -> GmEnvironment -> GmEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

compileAlts :: (Int -> GmCompiler)
            -> [CoreAlt]
            -> GmEnvironment
            -> [(Int, GmCode)]
compileAlts comp alts env =
  [ (tag, comp (length names) body (zip names [0..] ++ argOffset (length names) env))
  | (tag, names, body) <- alts]  {- Fig 3.14  p.134  𝓓 scheme -}

---

compiledPrimitives :: [GmCompiledSC]
compiledPrimitives =
  [ op2 "+" Add
  , op2 "-" Sub
  , op2 "*" Mul
  , op2 "/" Div
  , ("negate", 1, [Push 0, Eval, Eval, Neg, Update 1, Pop 1, Unwind])
  , op2 "==" Eq
  , op2 "~=" Ne
  , op2 "<"  Lt
  , op2 "<=" Le
  , op2 ">"  Gt
  , op2 ">=" Ge
  --- , ("if", 3, [Push 0, Eval, Cond [Push 1] [Push 2], Update 3, Pop 3, Unwind])
  ]
  where
    op2 n i = (n, 2, [Push 1, Eval, Push 1, Eval, i, Update 2, Pop 2, Unwind])

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

  -- section 3.8.6
  , ("if", ["c", "t", "f"], ECase (EVar "c") [(1, [], EVar "f"), (2, [], EVar "t")])

  {-
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
   -}
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

showState :: GmState -> IseqRep
showState s =
  iConcat
  [ showOutput s, iNewline
  , showStack s, iNewline
  , showDump s, iNewline
  , showInstructions (getCode s), iNewline ]

showOutput :: GmState -> IseqRep
showOutput s = iConcat [iStr "Output:\"", iStr (getOutput s), iStr "\""]

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
showInstruction (Pack t n)      =  iStr "Pack " `iAppend` iNum t `iAppend` iStr " " `iAppend` iNum n
showInstruction (Casejump alts) =  foldl (\s alt -> s `iAppend` iStr " " `iAppend` iAlt alt) (iStr "Casejump") alts
  where iAlt (t, xs) = iStr "[" `iAppend` iNum t `iAppend` iStr " -> " `iAppend` iCodes xs `iAppend` iStr "]"
showInstruction (Split n)       =  iStr "Split " `iAppend` iNum n
showInstruction  Print          =  iStr "Print"
showInstruction  ins
  | ins `elem` [ Eval, Add, Sub, Mul, Div, Neg
               , Eq, Ne, Lt, Le, Gt, Ge]  =  iStr $ show ins
  | otherwise                             =  error $ "showInstruction: unknown instruction: " ++ show ins

iCodes :: [Instruction] -> IseqRep
iCodes = shortShowInstructions 2

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
  NInd a1      ->  iConcat [iStr "Ind ", showAddr a1]  {- exercise 3.8 -}
  NConstr t as ->  iConcat [ iStr "Cons ", iNum t, iStr " ["
                           , iInterleave (iStr ", ") (map showAddr as), iStr "]" ]

{-
debugNestedAp :: Heap Node -> Node -> IseqRep
debugNestedAp heap = rec_ id
  where
    paren s = iConcat [iStr "(", s, iStr ")"]
    rec_ pf (NAp fun arg) =
      pf $ iConcat [rec_ id (hLookup heap fun), iStr " ", rec_ paren (hLookup heap arg)]
    rec_ _ x             =
      leaf x
    leaf (NNum i)           =  iStr $ show i
    leaf (NAp {})           =  error "bug: showNestedAp: leaf called for NAp"
    leaf (NGlobal {})
    -- leaf (NPrim n _)        =  iStr n
    -- leaf (NSupercomb n _ _) =  iStr n
    -- leaf (NInd a)           =  iStr $ showA a
    -- leaf (NData t as@[])    =  iStr $ showNData t as
    -- leaf (NData t as@(_:_)) =  iStr $ "(" ++ showNData t as ++ ")"
    showNData t as = unwords $ ("<" ++ show t ++ ">") : map showA as
    showA a = "[" ++ show a ++ "]"
 -}

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

testB32fac = "fac n = if (n==0) 1 (n * fac (n-1)) ;\
             \main = fac 5"

testB32gcd = "gcd a b = if (a==b) \
             \             a \
             \          if (a<b) (gcd b a) (gcd b (a-b)) ;\
             \main = gcd 6 10"

testB32gcdS = "gcd a b = if (a==b) \
              \             a \
              \          if (a<b) (gcd b a) (gcd b (a-b)) ;\
              \main = gcd 1 1"

testB32nfib = "nfib n = if (n==0) \
              \            1 \
              \         if (n==1) 1 (nfib (n-1) + nfib (n-2)) ;\
              \main = nfib 4"

-- estimate 6183 step
testB32nfibx = "nfib n = if (n < 2) \
               \            1 \
               \            (nfib (n-1) + nfib (n-2)) ;\
               \main = nfib 10"

testThunk = "fac n = if (n==0) 1 (n * fac (n-1)) ;\
            \main = K 2 (fac 5)"

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
    (   _o, _i, lastStack, _d, lHeap, _, _) = last states
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
checkList =
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

 {-
  , (NNum    1, "main = fst (MkPair 1 2)") -- casePair
  , (NNum    2, "main = snd (MkPair 1 2)") -- casePair
  , (NNum    2, "main = fst (snd (fst (MkPair (MkPair 1 (MkPair 2 3)) 4)))") -- casePair nested

  , (NNum    3, "main = length (Cons 1 (Cons 2 (Cons 3 Nil)))") -- caseList
 -}
  ]
