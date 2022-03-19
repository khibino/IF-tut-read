{-# LANGUAGE FlexibleInstances #-}

module TemplateMark5Alter where

import Language
-- import Language hiding (preludeDefs)
import Utils

import Data.List

import Control.Monad (when)
import Data.Either (isLeft)


{-  (stack,dump,heap,globals)  -}

type Primitive = TiState -> TiState

instance Eq (TiState -> TiState) where
  _ == _  =  False

instance Show (TiState -> TiState) where
  show _ = "<primitive>"

data Node
  = NAp  Addr Addr
  | NSupercomb Name [Name] CoreExpr
  | NNum Int
  | NInd Addr
  | NPrim Name Primitive
  | NData Int [Addr]
  deriving (Eq, Show)

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


type TiState = (TiOutput, TiStack, TiDump, TiHeap, TiGlobals, TiStats)

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

type TiOutput = [Int]

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
applyToStats f (output, stack, dump, heap, scDefs, stats) =
  (output, stack, dump, heap, scDefs, f stats)

compile :: CoreProgram -> TiState
-- compile program = undefined
compile program =
    ([], initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  where
    scDefs = program ++ preludeDefs ++ extraPreludeDefs
    (initialHeap0, globals) = buildInitialHeap scDefs
    addressOfMain = aLookup globals "main" (error "main is not defined")
    addressOfPrintList = aLookup globals "printList" (error "printList is not defined")
    (initialHeap, printAddr) = hAlloc initialHeap0 (NAp addressOfPrintList addressOfMain)
    istack = [printAddr]
    initialStack = Stack { list = istack, depth = length istack, maxDepth = length istack }

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

_extraPrelude :: String
_extraPrelude =
  unlines
  [ "False = Pack{1,0} ;"
  , "True = Pack{2,0} ;"
  , "and x y = if x y False ;"

  , "or x y = if x True y ;"
  , "xor x y = if (and x y) False (or x y) ;"
  , "not x = if x False True ;"

  , "head xs = caseList xs abort K ;"
  , "tail xs = caseList xs abort K1 ;"

  , "length xs = caseList xs 0 length' ;"
  , "length' x xs = 1 + length xs ;"

  , "printList xs = caseList xs stop printCons ;"
  , "printCons h t = print h (printList t)"
  ]

-- preludeDefs :: CoreProgram
-- preludeDefs = []

buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
-- buildInitialHeap scDefs = mapAccumL allocateSc hInitial scDefs
buildInitialHeap scDefs =
    (heap2, scAddrs ++ primAddrs)
  where
    (heap1, scAddrs)   = mapAccumL allocateSc hInitial scDefs
    (heap2, primAddrs) = mapAccumL allocatePrim heap1 primitives

primitives :: Assoc Name Primitive
primitives = [ ("negate", primNeg)
             , ("+", primArith (+)),  ("-", primArith (-))
             , ("*", primArith (*)),  ("/", primArith div)
             , ("add", primArith (+)),  ("sub", primArith (-))
             , ("mul", primArith (*)),  ("div", primArith div)

             , ("if", primIf), ("casePair", primCasePair), ("caseList", primCaseList)
             , ("abort", primAbort)
             , ("stop", primStop), ("print", primPrint)
             , (">", primComp (>)), (">=", primComp (>=))
             , ("<", primComp (<)), ("<=", primComp (<=))
             , ("==", primComp (==)), ("/=", primComp (/=))
             ]

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
   (_, Stack { list = [] }, _, _, _, _)             ->  True
   _                                                ->  False
-- tiFinal state = case state of
--   (_, Stack { list = [soleAddr] }, [], heap, _, _) ->  isDataNode (hLookup heap soleAddr)
--   (_, Stack { list = [] }, _, _, _, _)             ->  error "Empty stack!"
--   _                                                ->  False

isDataNode :: Node -> Bool
isDataNode node = case node of
  NNum {}  ->  True
  NData {} ->  True
  _        ->  False

step :: TiState -> TiState
step state =
  case state of
    (_, stack, _dump, heap, _globals, _stats) -> dispatch (hLookup heap (head $ list stack))
      where
        dispatch (NPrim _n p)               =  doAdminPrimStep $ primStep state p
        dispatch (NNum n)                   =  numStep state n
        dispatch (NAp a1 a2)                =  apStep  state a1 a2
        dispatch (NSupercomb sc args body)  =  doAdminScStep $ scStep  state sc args body
        dispatch (NInd a)                   =  indStep state a
        dispatch (NData t as)               =  dataStep state t as

primStep :: TiState -> Primitive -> TiState
primStep state prim = prim state
{-
primStep state Neg  = primNeg state
primStep state (PrimConstr t n) = primConstr t n state
primStep state If   = primIf state
primStep state CasePair = primCasePair state
primStep state CaseList = primCaseList state
primStep state Abort  = primAbort state
primStep state Stop   = primStop state
primStep state Print  = primPrint state
primStep state p
  | p `elem` [Add, Sub, Mul, Div]                           = primDyadic arithF state
  | p `elem` [Greater, GreaterEq, Less, LessEq, Eq, NotEq]  = primDyadic compF state
  | otherwise                                               = error $ "primStep: unknown primitive: " ++ show p
{-
primStep state p
  | p `elem` [Add, Sub, Mul, Div]                           = primArith state $ arith p
  | p `elem` [Greater, GreaterEq, Less, LessEq, Eq, NotEq]  = primComp  state $ comp p
  | otherwise                                               = error $ "primStep: unknown primitive: " ++ show p
 -}
  where
    arithF (NNum x) (NNum y) = NNum $ x `op` y
      where op = arith p
    arithF _        _        = error $ "primStep: unknown arith bin op: " ++ show p

    arith Add = (+)
    arith Sub = (-)
    arith Mul = (*)
    arith Div = div
    arith p_  = error $ "primStep: not airth bin op: " ++ show p_

    compF (NNum x) (NNum y)
      | x `op` y  =  NData 2 [] {- True  -}
      | otherwise =  NData 1 [] {- False -}
      where op = comp p
    compF _        _ = error $ "primStep: unknown comp bin op: " ++ show p

    comp Greater = (>)
    comp GreaterEq = (>=)
    comp Less = (<)
    comp LessEq = (<=)
    comp Eq = (==)
    comp NotEq = (/=)
    comp p_ = error $ "primStep: not comp bin op: " ++ show p_
 -}

primDyadic :: (Node -> Node -> Node) -> TiState -> TiState
primDyadic op (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b1,b2]
      | null (list se) -> case (hLookup heap b1, hLookup heap b2) of
          (x@(NNum _), y@(NNum _)) -> (output,          sr,    dump, hUpdate heap ar (x `op` y), globals, stats)   -- (2.5 引数が評価済み)
          (NNum _,      n)
            | isDataNode n -> error $ "primDyadic: unknown 2nd data node: " ++ show n
            | otherwise    -> (output,          push b2 se, sr:dump,         heap              , globals, stats)   -- (2.6 第二引数が未評価 - 2.9 適用)
          (     n,      _)
            | isDataNode n -> error $ "primDyadic: unknown 1st data node: " ++ show n
            | otherwise    -> (output,          push b1 se, sr:dump,         heap              , globals, stats)   -- (2.6 第一引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primDyadic: invalid stack: " ++ show (list stack)
    as   -> error $ "primDyadic: wrong count of arguments" ++ show as
  where
    sr = discard 2 stack
    (ar, se) = pop sr

primXXX (stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    as  ->  undefined
    ---   -> error $ "primXXX: wrong count of arguments" ++ show as
  where
    arity = undefined
    sr = discard arity stack
    (ar, se) = pop sr

{-
primXXX (stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    as
      | null (list se)  ->  undefined
      | otherwise       ->  error $ "primXXX: invalid stack" ++ show (list stack)
    ---   -> error $ "primXXX: wrong count of arguments" ++ show as
  where
    arity = undefined
    sr = discard arity stack
    (ar, se) = pop sr
 -}

primNeg :: TiState -> TiState
primNeg _state@(output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b]
      | null (list se)  ->  case hLookup heap b of
          NNum n           -> (output,       sr,    dump, hUpdate heap ar (NNum (- n)), globals, stats)   -- (2.5 引数が評価済み)
          x | isDataNode x -> error $ "primNeg: unknown data node: " ++ show x
            | otherwise    -> (output, push b se, sr:dump,         heap                , globals, stats)   -- (2.6 引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primNeg: invalid stack: " ++ show (list stack)
    as   -> error $ "primNeg: wrong count of arguments" ++ show as
  where
    sr = discard 1 stack
    (ar, se) = pop sr

-- exercise 2.17
primArith :: (Int -> Int -> Int) -> TiState -> TiState
primArith (<+>) (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b1,b2]
      | null (list se) -> case (hLookup heap b1, hLookup heap b2) of
          (NNum x, NNum y) -> (output,                  sr,    dump, hUpdate heap ar (NNum $ x <+> y), globals, stats)   -- (2.5 引数が評価済み)
          (NNum _,      n)
            | isDataNode n -> error $ "primArith: unknown 2nd data node: " ++ show n
            | otherwise    -> (output,          push b2 se, sr:dump,         heap                    , globals, stats)   -- (2.6 第二引数が未評価 - 2.9 適用)
          (     n,      _)
            | isDataNode n -> error $ "primArith: unknown 1st data node: " ++ show n
            | otherwise    -> (output,          push b1 se, sr:dump,         heap                    , globals, stats)   -- (2.6 第一引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primArith: invalid stack: " ++ show (list stack)
    as   -> error $ "primArith: wrong count of arguments" ++ show as
  where
    sr = discard 2 stack
    (ar, se) = pop sr

primComp :: (Int -> Int -> Bool) -> TiState -> TiState
primComp (=!=) (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b1,b2]
      | null (list se) -> case (hLookup heap b1, hLookup heap b2) of
          (NNum x, NNum y) -> (output,                  sr,    dump, hUpdate heap ar (boolNode $ x =!= y), globals, stats)   -- (2.5 引数が評価済み)
          (NNum _,      n)
            | isDataNode n -> error $ "primComp: unknown 2nd data node: " ++ show n
            | otherwise    -> (output,          push b2 se, sr:dump,         heap                    , globals, stats)   -- (2.6 第二引数が未評価 - 2.9 適用)
          (     n,      _)
            | isDataNode n -> error $ "primComp: unknown 1st data node: " ++ show n
            | otherwise    -> (output,          push b1 se, sr:dump,         heap                    , globals, stats)   -- (2.6 第一引数が未評価 - 2.9 適用)
      | otherwise  -> error $ "primComp: invalid stack: " ++ show (list stack)
    as   -> error $ "primComp: wrong count of arguments" ++ show as
  where
    sr = discard 2 stack
    (ar, se) = pop sr
    boolNode p
      | p         = NData 2 []
      | otherwise = NData 1 []

primConstr :: Int -> Int -> TiState -> TiState
primConstr tag arity (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    bs
      | not (null $ list se)  ->  error $ "primConstr: invalid stack depth: " ++ show (list stack)
      | length bs /= arity    ->  error $ "primConstr: wrong count of arguments: " ++ show bs
      | otherwise             ->  (output,   sr, dump, hUpdate heap ar (NData tag bs), globals, stats)  -- (2.10)
  where
    sr = discard arity stack
    (ar, se) = pop sr


-- exercise 2.19
{-
    a:a1:a2:a3:[]  d  h  a:NPrim If    f
                         a1:NAp a b
                         a2:NAp a1 t
                         a3:NAp a2 e
                         b:NData 2 []  -- False

⇒          a3:[]  d  h  a3:NInd e     f

--------------

    a:a1:a2:a3:[]  d  h  a:NPrim If    f
                         a1:NAp a b
                         a2:NAp a1 t
                         a3:NAp a2 e
                         b:NData 1 []  -- True

⇒          a3:[]  d  h  a3:NInd t     f

--------------

    a:a1:a2:a3:[]          d  h  a:NPrim If    f
                                 a1:NAp a b  -- 未評価
                                 a2:NAp a1 t
                                 a3:NAp a2 e

⇒           b:[]  (a3:[]):d  h                f
-}
primIf :: TiState -> TiState
primIf (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b, t, e]
      | null (list se)  ->  case hLookup heap b of
          NData 1 {- False -} []  ->  (output,       sr,    dump, hUpdate heap ar (NInd e), globals, stats)
          NData 2 {- True  -} []  ->  (output,       sr,    dump, hUpdate heap ar (NInd t), globals, stats)
          n | isDataNode n        ->  error $ "primIf: unknown data node: " ++ show n
            | otherwise           ->  (output, push b se, sr:dump,         heap            , globals, stats)
      | otherwise                 ->  error $ "primIf: invalid stack depth: " ++ show (list stack)
    _  ->   error "primIf: wrong count of argument"
  where
    sr = discard 3 stack
    (ar, se) = pop sr

-- exercise 2.22
{-
    a:a1:a2:[]  d  h  a:NPrim CasePair
                      a1:NAp a p
                      a2:NAp a1 f
                      p:NData 1 [b1, b2]  -- MkPair

⇒       a2:[]  d  h  c:NAp f b1
                      a2:NAp c b2

--------------

    a:a1:a2:[]  d  h  a:NPrim CasePair
                      a1:NAp a p  -- 未評価
                      a2:NAp a1 f

⇒        b:[]  (a2:[]):d  h
 -}
primCasePair :: TiState -> TiState
primCasePair (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [p, f]
      | null (list se)  ->  case hLookup heap p of
          NData 1 [b1, b2]  ->  (output,       sr,    dump, hUpdate heap1 ar (NAp b4 b2), globals, stats)
            where (heap1, b4) = hAlloc heap (NAp f b1)
          n | isDataNode n  ->  error $ "primCasePair: unknown data node: " ++ show n
            | otherwise     ->  (output, push p se, sr:dump,         heap                , globals, stats)
      | otherwise       ->  error $ "primCasePair: invalid stack" ++ show (list stack)
    as  ->  error $ "primCasePair: wrong count of arguments: " ++ show as
  where
    arity = 2
    sr = discard arity stack
    (ar, se) = pop sr

-- exercise 2.24
{-
    a:a1:a2:a3:[]  d  h  a:NPrim CaseList
                         a1:NAp a l
                         a2:NAp a1 n
                         a3:NAp a2 c
                         l:NData 1 []  -- Nil

⇒          a3:[]  d  h  a3:NInd n

--------------

    a:a1:a2:a3:[]  d  h  a:NPrim CaseList
                         a1:NAp a l
                         a2:NAp a1 n
                         a3:NAp a2 c
                         l:NData 2 [b1,b2]  -- Cons

⇒          a3:[]  d  h  c1:NAp c b1
                         a3:NAp c1 b2

--------------

    a:a1:a2:a3:[]  d  h  a:NPrim CaseList
                         a1:NAp a l  -- 未評価
                         a2:NAp a1 n
                         a3:NAp a2 c

=>          a1:[]  (a3:[]):d  h
 -}
primCaseList :: TiState -> TiState
primCaseList (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [l, n, c]
      | null (list se)  ->  case hLookup heap l of
          NData 1 []       -> (output,         sr,   dump, hUpdate heap  ar (NInd n)    , globals, stats)
          NData 2 [b1, b2] -> (output,         sr,   dump, hUpdate heap1 ar (NAp c1 b2) , globals, stats)
            where (heap1, c1) = hAlloc heap (NAp c b1)
          n' | isDataNode n'  ->  error $ "primCaseList: unknown data node: " ++ show n'
             | otherwise     ->  (output, push l se, sr:dump,        heap                 , globals, stats)
      | otherwise       ->  error $ "primCaseList: invalid stack" ++ show (list stack)
    as  ->  error $ "primCaseList: wrong count of arguments" ++ show as
  where
    arity = 3
    sr = discard arity stack
    (ar, se) = pop sr

-- exerise 2.25
{-
disadvantage は、
Bool や List といったデータ型ごとにプリミティブを実装する必要があること
 -}

primAbort :: TiState -> TiState
primAbort _ = error "aborted."

primStop :: TiState -> TiState
primStop (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    []
      | null (list se)  ->  (output,  se,  dump, heap , globals, stats)
      | otherwise       ->  error $ "primStop: invalid stack" ++ show (list stack)
    as  ->  error $ "primStop: wrong count of arguments" ++ show as
  where
    arity = 0
    sr = discard arity stack
    (ar, se) = pop sr
-- 規則 (2.11)

primPrint :: TiState -> TiState
primPrint (output, stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    [b1, b2]
      | null (list se)  -> case hLookup heap b1 of
          NNum n        ->  (output ++ [n], push b2 se,  dump, heap , globals, stats)  -- 規則 (2.12)
          _             ->  (output, push b1 se, sr : dump, heap , globals, stats)   -- 規則 (2.13)
      | otherwise       ->  error $ "primPrint: invalid stack" ++ show (list stack)
    as  -> error $ "primXXX: wrong count of arguments" ++ show as
  where
    arity = 2
    sr = discard arity stack
    (_ar, se) = pop sr

{-
primXXX (stack, dump, heap, globals, stats) =
  case getArgs heap stack of
    as
      | null (list se)  ->  undefined
      | otherwise       ->  error $ "primXXX: invalid stack" ++ show (list stack)
    ---   -> error $ "primXXX: wrong count of arguments" ++ show as
  where
    arity = undefined
    sr = discard arity stack
    (ar, se) = pop sr
 -}

numStep :: TiState -> Int -> TiState
-- numStep _state _n = error "Number applied as a function"
numStep state _n =
  case state of
    (output, stack, s:dump, heap, globals, stats)
      | null (list stack1) -> (output, s, dump, heap, globals, stats)  -- (2.7)
      | otherwise          -> error $
                              "numStep: invalid stack: " ++ show (list stack) ++ "\n" ++
                              unlines (map show $ allocs heap) ++ "\n"
                              -- unlines (map show $ dump)
      where
        (_a, stack1) = pop stack
    (     _,    _,     [],     _,      _,     _) -> error $ "numStep: invalid state, dump is empty:\n" ++ showResults [state]

apStep :: TiState -> Addr -> Addr -> TiState
apStep state a1 a2 =
  case state of
    (output, stack, dump, heap, globals, stats) -> case hLookup heap a2 of
      NInd a3 ->  (output,        stack, dump, hUpdate heap ar (NAp a1 a3), globals, stats)  -- (2.8)
      _       ->  (output, push a1 stack, dump,                        heap, globals, stats)
      where
        (ar, _) = pop stack
-- TODO: 引数が間接参照になるケースを考える

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep state _scName argNames body = case state of
  (output, stack, dump, heap, globals, stats)
    | depth stack < length argNames + 1
      -> error "Too few argments given"
    | otherwise
      -> (output, stackD, dump, heap', globals, tiStatIncScStep stats)
  -- exercise 2.6
  -- (stack, _dump, heap, globals, _stats)
  --   -> (stack', _dump, heap', globals, _stats)
    where
      stackD = discard (length argNames) stack
      (an, _) = pop stackD
      heap' = instantiateAndUpdate body an heap env
      -- exercise 2.14
      -- (2.3) は exercise 2.14 で消去
      env = argBindings ++ globals
      argBindings = zip argNames (getArgs heap stack)

indStep :: TiState -> Addr -> TiState
indStep state addr = case state of
  (output, stack, dump, heap, globals, stats)
    -> (output, push addr stack1, dump, heap, globals, stats)   -- (2.4)
    where
      (_, stack1) = pop stack

dataStep :: TiState -> Int -> [Addr] -> TiState
dataStep state tag args =
  case state of
    (output, stack, s:dump, heap, globals, stats)
      | null (list stack1) -> (output, s, dump, heap, globals, stats)  -- (2.7)
      | otherwise          -> error $
                              "dataStep: invalid stack: " ++ show (list stack) ++ "\n" ++
                              unlines (map show $ allocs heap) ++ "\n"
      where
        (_a, stack1) = pop stack
    (output,    _,     [],     _,      _,     _) -> error $ "dataStep: invalid state, dump is empty:\n" ++ showResults [state]

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
  EConstr tag arity     -> instantiateConstrUpdate updAddr tag arity heap env
  ELet isrec defs body  -> instantiateLetUpdate updAddr isrec defs body heap env
  ECase _e _alts        -> error "Can't instantiate case exprs"
  ELam _vs _e           -> error "Can't instantiate lambda abstractions"

instantiateConstrUpdate :: Addr -> Int -> Int -> TiHeap -> Assoc Name Addr -> TiHeap
instantiateConstrUpdate updAddr tag arith heap env =
  hUpdate heap updAddr (NPrim "Constr" (primConstr tag arith))

instantiateConstr :: Int -> Int -> TiHeap -> Assoc Name Addr -> (TiHeap, Addr)
instantiateConstr tag arith heap env =
  hAlloc heap (NPrim "Constr" (primConstr tag arith))

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
  unlines (map iDisplay (iLaynList $ map showState states) ++
           [iDisplay (showStats lastStates)] ++
           [iDisplay (showOutput lastStates)])
  where
    lastStates = last states
  -- iDisplay (iConcat [ iLayn (map showState states)
  --                   , showStats (last states)
  --                   ])

showState :: TiState -> IseqRep
showState (output, stack, dump, heap, _globals, _stats)
  | showHeapP =
    iConcat [ showHeap heap, iNewline ]
    `iAppend`
    iseqState
  | otherwise =
    iseqState
  where
    showHeapP = True
-- exercise 2.5
    iseqState =
      iConcat
      [ showStack heap stack, iNewline
      , iStr "Dump depth: ", iStr $ show (length dump), iNewline
      ]

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
showStkNode heap n@(NAp funAddr argAddr) =
  iConcat
  [ iStr "NAp ", showFWAddr funAddr
  , iStr " ", showFWAddr argAddr, iStr " ("
  , showNode (hLookup heap argAddr), iStr ")"
  , iStr "  -- ", debugNestedAp heap n
  ]
showStkNode _heap node = showNode node

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

showNode :: Node -> IseqRep
showNode node = case node of
  NPrim name _prim            -> iConcat [ iStr "NPrim ", iStr name ]
  NAp a1 a2                   -> iConcat [ iStr "NAp ", showAddr a1
                                         , iStr " ",    showAddr a2
                                         ]
  NSupercomb name _args _body -> iStr ("NSupercomb " ++ name)
  NNum n                      -> iStr "NNum " `iAppend` iNum n
  NInd a                      -> iStr "NInd " `iAppend` showAddr a
  NData t as                  -> iStr "NData " `iAppend` iStr (show t) `iAppend` iConcat (map ((iStr " " `iAppend`) . showAddr) as)

showAddr :: Addr -> IseqRep
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> IseqRep
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where
    str = show addr

showStats :: TiState -> IseqRep
showStats (output, stack, _dump, _heap, _globals, stats) =
  iConcat [ iNewline, iNewline
          , iStr "Total number of steps = ", iNum (tiStatGetSteps stats), iNewline
          , iStr "Super combinator steps = ", iNum (scSteps stats), iNewline
          , iStr "Primitive steps = ", iNum (primSteps stats), iNewline
          , showStackMaxDepth stack ]

showOutput :: TiState -> IseqRep
showOutput (output, _, _, _, _, _) =
  iConcat [iStr "Output: ", iStr (show output), iNewline]

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

testList = "main = Cons 1 (Cons 2 (Cons 3 Nil))"

testList2 = "main = Cons (1 + 2) (Cons 2 (Cons 3 Nil))"

test :: String -> IO ()
test = putStrLn . showResults . eval . compile . parse
-- test = putStrLn . iDisplay . showState . head . eval . compile . parse

check :: Node -> String -> Either String String
check expect prog
  | length states == limit  =  Left  . unlines $ ("expect " ++ show expect) : showProg "too long: "
  | lastv == expect         =  Right . unlines $ showProg "pass: " ++ [show lastv]
  | otherwise               =  Left  . unlines $ ("expect " ++ show expect) : showProg "wrong: "
  where
    states = take limit . eval . compile . parse $ prog
    limit = 1000000
    (   _, lastStack, _, lHeap, _, _) = last states
    (a, _) = pop lastStack
    lastv = hLookup lHeap a

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

  , (NNum    1, "main = fst (MkPair 1 2)") -- casePair
  , (NNum    2, "main = snd (MkPair 1 2)") -- casePair
  , (NNum    2, "main = fst (snd (fst (MkPair (MkPair 1 (MkPair 2 3)) 4)))") -- casePair nested

  , (NNum    3, "main = length (Cons 1 (Cons 2 (Cons 3 Nil)))") -- caseList
  ]
