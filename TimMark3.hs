{-# LANGUAGE RecordWildCards #-}

module TimMark3 where

import Utils
import Language

---

import GHC.Stack (HasCallStack)
import Control.Monad (when)
import Data.Either (isLeft)
import Data.List (mapAccumL)
import Data.Set (Set)
import qualified Data.Set as Set

---

data Stack a =
  Stack
  { list :: [a]
  , depth :: Int
  , maxDepth :: Int
  }
  deriving Show

stkOfList :: [a] -> Int -> Stack a
stkOfList xs md = Stack { list = xs, depth = d, maxDepth = d `max` md }
  where d = length xs

stkPush :: a -> Stack a -> Stack a
stkPush x Stack { list = xs, depth = d, maxDepth = maxd } =
  Stack { list = x:xs, depth = d+1, maxDepth = max (d + 1) maxd }

stkPop :: HasCallStack => Stack a -> (a, Stack a)
stkPop s@Stack { list = xxs, depth = d } = case xxs of
  []    -> error "stkPop: empty stack!"
  x:xs  -> (x, s { list = xs, depth = d - 1})

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

data Instruction
  = Take Int Int
  | Move Int TimAMode
  | Push TimAMode
  | PushV ValueAMode
  | Enter TimAMode
  | Return
  | Op Op
  | Cond [Instruction] [Instruction]
  deriving Show

data Op
  = Add | Sub | Mul | Div | Neg
  | Gt | Ge | Lt | Le | Eq | Ne
  deriving (Eq, Show)

data TimAMode
  = Arg Int
  | Label [Char]
  | Code CCode
  | IntConst Int
  deriving Show

type CCode = ([Instruction], Slots)
type Slots = Set Int

data ValueAMode
  = FramePtr
  | IntVConst Int
  deriving Show

---

modify :: (s -> a) -> (a -> s -> s) -> (a -> a) -> s -> s
modify get set update s = set (update (get s)) s

---

data TimState =
  TimState
  { instr_    :: [Instruction]
  , islots_   :: Slots
  , fptr_     :: FramePtr
  , stack_    :: TimStack
  , vstack_   :: TimValueStack
  , dump_     :: TimDump
  , heap_     :: TimHeap
  , cstore_   :: CodeStore
  , stats_    :: TimStats
  , gcDump_  :: IseqRep
  }
  deriving Show

putFptr_ :: FramePtr -> TimState -> TimState
putFptr_ a s = s { fptr_ = a }

putStack_ :: TimStack -> TimState -> TimState
putStack_ a s = s { stack_ = a }

putStats_ :: TimStats -> TimState -> TimState
putStats_ a s = s { stats_ = a }

---

data FramePtr
  = FrameAddr Addr  -- The address of a frame
  | FrameInt Int    -- An integer value
  | FrameNull       -- Uninitialized
  deriving (Eq, Show)

---

type TimStack = Stack Closure
type Closure = (CCode, FramePtr)

---

type TimValueStack = Stack Int
data TimDump = DummyTimDump deriving Show

type TimHeap = Heap Frame

data Frame
  = Frame [Closure]
  | Forward Addr
  deriving Show

type CodeStore = Assoc Name CCode

data TimStats =
  TimStats
  { steps_ :: Int
  , extime_ :: Int
  , ahsize_ :: Int
  }
  deriving Show

---

data HowMuchToPrint = Full | Terse | None deriving Show

---

fAlloc   :: TimHeap -> [Closure] -> (TimHeap, FramePtr)
fAlloc heap xs = (heap', FrameAddr addr)
  where
    (heap', addr) = hAlloc heap $ Frame xs

fGet     :: TimHeap -> FramePtr -> Int -> Closure
fGet heap (FrameAddr addr) n = case nf of
  Frame f    -> f !! (n-1)
  Forward {}  -> error $ "fGet: " ++ show nf
  where
    nf = hLookup heap addr
fGet _h f _n = error $ "fGet: not impl: " ++ show f

fUpdate  :: TimHeap -> FramePtr -> Int -> Closure -> TimHeap
fUpdate heap (FrameAddr addr) n closure = result
  where
    result = case hLookup heap addr of
      Frame frame -> hUpdate heap addr $ Frame new_frame
        where new_frame = take (n-1) frame ++ [closure] ++ drop n frame
      f@(Forward {})  -> error $ "fUpdate :" ++ show f
fUpdate _h f _n _cl = error $ "fUpdate: not impl: " ++ show f

fList    :: Frame -> [Closure]
fList (Frame f) = f
fList nf@(Forward {}) = error $ "fList: " ++ show nf

---

codeLookup :: CodeStore -> Name -> CCode
codeLookup cstore l =
  aLookup cstore l (error $ "Attempt to jump to unknown label " ++ show l)

---

statInitial :: TimStats
statInitial = TimStats { steps_ = 0, extime_ = 0, ahsize_ = 0 }

statIncSteps :: TimStats -> TimStats
statIncSteps = modify (steps_) (\x s -> s { steps_ = x }) (+ 1)

statGetSteps :: TimStats -> Int
statGetSteps = steps_

statIncExtime :: TimStats -> TimStats
statIncExtime = modify (extime_) (\x s -> s { extime_ = x }) (+ 1)

statAddAllocated :: Int -> TimStats -> TimStats
statAddAllocated n = modify (ahsize_) (\x s -> s { ahsize_ = x }) (+ n)

---

initialArgStack :: TimStack
initialArgStack = stkPush (mempty, FrameNull) $ Stack [] 0 0

initialValueStack :: TimValueStack
initialValueStack = Stack [] 0 0

initialDump :: TimDump
initialDump = DummyTimDump

---

applyToStats :: (TimStats -> TimStats) -> TimState -> TimState
applyToStats = modify stats_ putStats_

---

defSlot :: [Int] -> Slots
defSlot = Set.fromList

mapCode :: (a -> b) -> (a, Slots) -> (b, Slots)
mapCode f (x, slots) = (f x, slots)

---

{- |
>>> lookup "+" compiledPrimitives
Just ([Take 2 2,Push (Code ([Push (Code ([Op Add,Return],fromList [])),Enter (Arg 1)],fromList [1])),Enter (Arg 2)],fromList [1,2])
 -}
compiledPrimitives :: [(Name, CCode)]
compiledPrimitives = [ ("+", op2code Add)
                     , ("-", op2code Sub)
                     , ("*", op2code Mul)
                     , ("/", op2code Div)

                     , (">" , op2code Gt)
                     , (">=", op2code Ge)
                     , ("<" , op2code Lt)
                     , ("<=", op2code Le)
                     , ("==", op2code Eq)
                     , ("/=", op2code Ne)

                     , ("negate", op1code Neg)
                     , ("if", ifcode)
                     ]
  where
    pzero op = ([Op op, Return], mempty)
    psucc n x = ([ Push (Code x), Enter (Arg n) ], snd x <> defSlot [n])
    prim1 op = psucc 1 $ pzero op  {- <prim1> := [ Push (Code [Op op, Return], Enter (Arg 1)) ] -}
    prim2 op = psucc 2 $ prim1 op  {- <prim2> := [ Push (Code <prim1>, Enter (Arg 2)) ] -}

    op1code op = mapCode (Take 1 1 :) $ prim1 op
    op2code op = mapCode (Take 2 2 :) $ prim2 op

    {- exercise 4.5 -}
    {- 0 is True, otherwise False
       if 0 t f = t
       if n t f = f -}
    ifcode = ( [ Take 3 3
               , Push (Code ([Cond [Enter (Arg 2)] [Enter (Arg 3)]], defSlot [2,3]))
               , Enter (Arg 1)
               ]
             , defSlot [1,2,3]
             )
    {-  if c t f

        if:  Take 3
             Push (Label L1)
             Enter (Arg 1)         -- Evaluate c

        L1:  Cond [Enter (Arg 2)]  -- Evaluate t
                  [Enter (Arg 3)]  -- Evaluate f
     -}

---

type TimCompilerEnv = [(Name, TimAMode)]

{- exercise 4.11
   FrameIx things and let impl finalize Take and Move instruction -}
type FrameIx = Int

compileSC :: TimCompilerEnv -> CoreScDefn -> (Name, CCode)
compileSC env (name, args, body)
  | d' == 0   =  (name, (instructions, slots))  {- exercise 4.3 -}
  | otherwise =  (name, (Take d' n : instructions, slots))
  where
    n = length args
    (d', (instructions, slots)) = compileR body new_env n
    new_env = zip args (map Arg [1..]) ++ env

compileR :: CoreExpr -> TimCompilerEnv -> FrameIx -> (FrameIx, CCode)
compileR e@(EAp (EVar "negate") _)    env d = compileB e env (d, ([Return], mempty))
compileR e@(EAp (EAp (EVar opn) _) _) env d
  | isArith2 opn                            = compileB e env (d, ([Return], mempty))
compileR   (EAp (EAp (EAp (EVar "if") e) et) ee)  {- exercise 4.7 -}
                                      env d = compileB e env (dt `max` de, ([Cond ct ce], st <> se))
  where
    (dt, (ct, st)) = compileR et env d
    (de, (ce, se)) = compileR ee env d
{- DONE: case for let expr -}
compileR (ELet rec_ defns body)      env d = (d', (moves ++ is, gcslots))
  where
    gcslots = Set.unions (slotR : slots)
    moves = zipWith (\k am -> Move (d + k) am) [1..n] ams
    (d', (is, slotR)) = compileR body env' dn
    env'
      | rec_       = envrec
      | otherwise  = zipWith (\x k -> (x, Arg (d + k))) xs [1..n] ++ env
    (ams, slots) = unzip ps
    (dn, ps) = mapAccumL astep (d + n) es
    (xs, es) = unzip defns
    astep d_ e = compileA e envlet d_
    envlet
      | rec_       = envrec
      | otherwise  = env
    {- exercise 4.14
       implement letrec env by applying mkIndMode -}
    envrec         = zipWith (\x k -> (x, mkIndMode (d + k))) xs [1..n] ++ env
    n = length defns
compileR e@(ENum {})                  env d = compileB e env (d, ([Return], mempty))
compileR (EAp e1 e2)  env  d = (d2, mapAR Push am <> is)
  where
    (d1, am) = compileA e2 env d
    (d2, is) = compileR e1 env d1
compileR (EVar v)     env  d = (d', mapAR Enter am)
  where
    (d', am) = compileA (EVar v) env d
compileR  e          _env _d = error $ "compileR: cannot for " ++ show e

mkIndMode :: Int -> TimAMode
mkIndMode n = Code ([Enter (Arg n)], defSlot [n])

mapAR :: (TimAMode -> Instruction) -> (TimAMode, Slots) -> ([Instruction], Slots)
mapAR f = mapCode (\instA -> [f instA])

compileA :: CoreExpr -> TimCompilerEnv -> FrameIx -> (FrameIx, (TimAMode, Slots))
compileA (EVar v)  env d = case aLookup env v (error $ "Unknown variable " ++ v) of
  a@(Arg n)            -> (d, (a, defSlot [n]))
  {- extract slots for local lexical-closure.
     `Code :: AMode` is not global. global-closure (super-combinator) is `Label :: AMode`. -}
  a@(Code (_, slots))  -> (d, (a, slots))
  a                    -> (d, (a, mempty))
compileA (ENum n) _env d = (d, (IntConst n, mempty))
compileA  e        env d = (d', (Code ccode, slots))
  where (d', ccode@(_, slots)) = compileR e env d

mapFCode :: (a -> b) -> (FrameIx, (a, Slots)) -> (FrameIx, (b, Slots))
mapFCode f (ix, (x, s)) = (ix, (f x, s))

{- exercise 4.6 -}
{-
"factorial n = if n 1 (n * factorial (n-1)); main = factorial 3"
  without vstack        :  204 steps
  with vstack (+,-,*,/) :  126 steps

"fib n = if (n < 2) 1 (fib (n-1) + fib (n-2)); main = fib 3"
  without vstack        :  230 steps
  with vstack (+,-,*,/) :  176 steps
 -}
compileB :: CoreExpr -> TimCompilerEnv -> (FrameIx, CCode) -> (FrameIx, CCode)
compileB (EAp (EVar "negate") e)      env cont    =  compileB e  env  (mapFCode (Op Neg :) cont)
compileB (EAp (EAp (EVar opn) e1) e2) env cont
  | Just op <- lookup opn arith2                  =  compileB e2 env (compileB e1 env (mapFCode (Op op :) cont))
compileB (ENum n)                    _env cont    =  mapFCode (PushV (IntVConst n) :) cont
compileB  e                           env (d, c)  =  fmap (([Push (Code c)], slots) <>) (compileR e env d)
  where (_, slots) = c

isArith2 :: String -> Bool
isArith2 opn = case lookup opn arith2 of
  Nothing -> False
  Just {} -> True

arith2 :: [(String, Op)]
arith2
  | not ex46   = arith2_
  | otherwise  = arith2Ex46
  where ex46 = False

arith2_ :: [(String, Op)]
arith2_ =
  [ ("+", Add), ("-", Sub)
  , ("*", Mul), ("/", Div)
  , (">", Gt), (">=", Ge)
  , ("<", Lt), ("<=", Le)
  , ("==", Eq), ("/=", Ne)
  , ("negate", Neg)
  ]

{- arith op2 for exercise 4.6 -}
arith2Ex46 :: [(String, Op)]
arith2Ex46 =
  [ ("+", Add), ("-", Sub)
  , ("*", Mul), ("/", Div)
  , ("negate", Neg)
  ]

---

runProg :: [Char] -> [Char]
runProg = showResults . eval . compile . parse

compile :: CoreProgram -> TimState
compile program =
  TimState
  { instr_   = [Enter (Label "main")]
  , islots_  = mempty
  , fptr_    = FrameNull
  , stack_   = initialArgStack
  , vstack_  = initialValueStack
  , dump_    = initialDump
  , heap_    = hInitial
  , cstore_  = compiled_code
  , stats_   = statInitial
  , gcDump_  = mempty
  }
  where
    sc_defs           = preludeDefs ++ program
    compiled_sc_defs  = map (compileSC initial_env) sc_defs
    compiled_code     = compiled_sc_defs ++ compiledPrimitives
    initial_env       =
      [ (name, Label name) | (name, _args, _body) <- sc_defs ] ++
      [ (name, Label name) | (name, _code) <- compiledPrimitives ]

eval' :: Bool -> TimState -> [TimState]
eval' doGC state = state : rest_states
  where
    rest_states | timFinal state = []
                | otherwise      = eval' doGC next_state
    next_state
      | doGC       = doAdmin (gc (step state))
      | otherwise  = doAdmin (step state)

eval :: TimState -> [TimState]
eval = eval' False

fullRun' :: Bool -> [Char] -> [Char]
fullRun' doGC = showFullResults . eval' doGC . compile . parse

fullRun :: [Char] -> [Char]
fullRun = showFullResults . eval . compile . parse

compiledCode :: String -> IO ()
compiledCode = mapM_ print . cstore_ . compile . parse

---

doAdmin :: TimState -> TimState
doAdmin state = applyToStats statIncSteps state

timFinal :: TimState -> Bool
timFinal state = null $ instr_ state

{- exercise 4.10

     Take t n : i f c1:...:cn:s h                                      c

 ⇒             i f'          s h[f':<0:c1,...,n:cn,n+1:_,...,t-1:_>]  c
       (size of f' is t)

     Move n (Code i) : i  f  s  h                  c

 ⇒                    i  f  s  h[f':<n-1:(i,f)>]  c

     Move n (IntConst n) : i f s h    c

⇒                         i
 -}
step :: TimState -> TimState
step state@TimState{..} = case instr_ of
  Take t n : instr
    | depth stack_  >= n   -> applyToStats (statAddAllocated n)
                              state { instr_ = instr, fptr_ = fptr', stack_ = discard n stack_, heap_ = heap' }
    | otherwise            -> error "Too few args for Take instructions"
    where (heap', fptr') = fAlloc heap_ (fst (stkPopN n stack_) ++ nullcs)
          nullcs = replicate (t - n) (mempty, FrameNull)

  Move n am       : instr  -> applyToStats statIncExtime
                              state { instr_ = instr, heap_ = heap' }
    where heap' = fUpdate heap_ fptr_ n (clo, fptr')
          (clo, fptr') = amToClosure am fptr_ heap_ cstore_

  -- Move n (Code c) : instr  -> applyToStats statIncExtime
  --                             state { instr_ = instr, heap_ = heap' }
  --   where heap' = fUpdate heap_ fptr_ n (c, fptr_)

  -- Move {} : _              -> error $ "unknown Move pattern: " ++ show instr_

  [Enter am]               -> applyToStats statIncExtime
                              state { instr_ = instr', islots_ = slots', fptr_ = fptr' }
    where ((instr', slots'), fptr') = amToClosure am fptr_ heap_ cstore_
  Enter {} : instr         -> error $ "instructions found after Enter: " ++ show instr

  Push am : instr          -> applyToStats statIncExtime
                              state { instr_ = instr, stack_ = stkPush (amToClosure am fptr_ heap_ cstore_) stack_ }

  {- rule 4.10 -}
  Op op : instr'  -> case op of
    Neg                    -> applyToStats statIncExtime
                              state { instr_ = instr', vstack_ = vstack1 (- n1) }
    _op2                   -> applyToStats statIncExtime
                              state { instr_ = instr', vstack_ = vstack2 (n1 <+> n2) }
      where (n2, v2) = stkPop v1
            vstack2 rv = stkPush rv v2

            (<+>) = case op of
              Add  ->  (+)
              Sub  ->  (-)
              Mul  ->  (*)
              Div  ->  div
              Gt   ->  comp2 (>)
              Ge   ->  comp2 (>=)
              Lt   ->  comp2 (<)
              Le   ->  comp2 (<=)
              Eq   ->  comp2 (==)
              Ne   ->  comp2 (/=)
              {- exercise 4.8 -}

            comp2 cop x y
              | x `cop` y  =  0  {- 0   is    True -}
              | otherwise  =  1  {- otherwise False-}

    where (n1, v1) = stkPop vstack_
          vstack1 rv = stkPush rv v1

  {- rule 4.13 -} {- exersise 4.5 -}
  [Cond i1 i2]             -> applyToStats statIncExtime
                              state { instr_ = instr', vstack_ = vstack' }
    where (n, vstack') = stkPop vstack_
          instr'
            | n == 0     = i1
            | otherwise  = i2
  Cond {} : instr          -> error $ "instructions found after Cond: " ++ show instr

  {- rule 4.11 -}
  [Return]                 -> applyToStats statIncExtime
                              state { instr_ = instr', islots_ = slots', stack_ = s1, fptr_ = f' }
    where (((instr', slots'), f'), s1) = stkPop stack_
  Return : instr           -> error $ "instructions found after Return: " ++ show instr

  {- rule 4.12 -}
  PushV FramePtr : instr'
    | FrameInt n <- fptr_  -> applyToStats statIncExtime
                              state { instr_ = instr', vstack_ = stkPush n vstack_ }
    | otherwise            -> error $ "unknown PushV frame: " ++ show fptr_
  {- rule 4.14 -}
  PushV (IntVConst n) : instr'
                           -> applyToStats statIncExtime
                              state { instr_ = instr', vstack_ = stkPush n vstack_ }

  []                       -> error $ "instructions is []"

amToClosure :: TimAMode -> FramePtr -> TimHeap -> CodeStore -> Closure
amToClosure amode fptr heap cstore = case amode of
  Arg n         -> fGet heap fptr n
  Code ccode    -> (ccode, fptr)
  Label l       -> (codeLookup cstore l, fptr)
  IntConst n    -> (intCode, FrameInt n)

intCode :: CCode
intCode = ([PushV FramePtr, Return], mempty)

---

gc :: TimState -> TimState
gc s@TimState{..} = s { fptr_ = fptr1, stack_ = stack1, heap_ = dheap, gcDump_ = gcDump }
  where
    dheap = uncurry scavengeHeap heaps2

    -- (heaps2, fptr1) = evacuateFramePtr heaps1 fptr_  {- Not pruned -}
    (heaps2, fptr1) = evacuateFramePtrPruned prune heaps1 fptr_
    prune :: [Closure] -> [Closure]
    prune cs = zipWith pruneBySlot [1..] cs
    pruneBySlot i c
      | i `Set.member` islots_   = c
      | otherwise                = (mempty, FrameNull)

    stack1 :: TimStack
    stack1 = stkOfList clist1 (maxDepth stack_)

    heaps1 :: (TimHeap, TimHeap)
    (heaps1, clist1) = mapAccumL evacuateClosure heaps0 clist0

    clist0 = list stack_
    heaps0 = (heap_, hInitial)

    -----
    gcDump =
      iStr "GC Dump:" <> iNewline <> iStr "  " <>
      iIndent (title "Before GC"                 <> showHeap' "       " heap_   <>
               title "After Evacuate Stack"      <> showHeaps           heaps1  <>
               title "After Evacuate Frame-Ptr"  <> showHeaps           heaps2  <>
               title "After GC (Scavenge)"       <> showHeap' "       " dheap)
    title tag = iStr tag <> iStr ":" <> iNewline
    showHeap' tag h = iStr tag <> showHeap h <> iNewline
    showHeaps (sh, dh) = showHeap' ("  src: ") sh <> showHeap' ("  dst: ") dh

{- |
>>> uncurry evacuateAddr _cyclic1
(((2,[(1,Forward 1),(2,Frame [])],2),(1,[(1,Frame [(([],fromList []),FrameAddr 1)])],1)),1)
>>> uncurry evacuateAddr _cyclic2a
(((3,[(2,Forward 2),(1,Forward 1),(3,Frame [])],3),(2,[(2,Frame [(([],fromList []),FrameAddr 1)]),(1,Frame [(([],fromList []),FrameAddr 2)])],2)),1)
>>> uncurry evacuateAddr _cyclic2b
(((3,[(1,Forward 2),(2,Forward 1),(3,Frame [])],3),(2,[(2,Frame [(([],fromList []),FrameAddr 2)]),(1,Frame [(([],fromList []),FrameAddr 1)])],2)),1)
 -}
evacuateAddr :: (TimHeap, TimHeap) -> Addr -> ((TimHeap, TimHeap), Addr)
evacuateAddr = evacuateAddrPruned id

evacuateAddrPruned :: ([Closure] -> [Closure]) -> (TimHeap, TimHeap) -> Addr -> ((TimHeap, TimHeap), Addr)
evacuateAddrPruned prune heaps0@(srcH0, dstH0) srcA  = case frame0 of
  Forward dstA  -> (heaps0, dstA)
  Frame cs      -> (heaps2, dstA)
    where
      heaps2 = foldl evacuateFramePtr' (srcH1, dstH1) $ map snd cs1
      srcH1 = hUpdate srcH0 srcA (Forward dstA)
      (dstH1, dstA) = hAlloc dstH0 frame1
      frame1 = Frame cs1
      cs1 = prune cs

      evacuateFramePtr' hs0 fptr = fst $ evacuateFramePtr hs0 fptr
  where
    frame0 = hLookup srcH0 srcA

evacuateClosure :: (TimHeap, TimHeap) -> Closure -> ((TimHeap, TimHeap), Closure)
evacuateClosure heaps0 (is, fptr0) = (heaps1, (is, fptr1))
  where (heaps1, fptr1) = evacuateFramePtr heaps0 fptr0

evacuateFramePtr :: (TimHeap, TimHeap) -> FramePtr -> ((TimHeap, TimHeap), FramePtr)
evacuateFramePtr = evacuateFramePtrPruned id

evacuateFramePtrPruned :: ([Closure] -> [Closure]) -> (TimHeap, TimHeap) -> FramePtr -> ((TimHeap, TimHeap), FramePtr)
evacuateFramePtrPruned prune heaps0 (FrameAddr a)  = (heaps1, FrameAddr a1)
  where (heaps1, a1) = evacuateAddrPruned prune heaps0 a
evacuateFramePtrPruned _      heaps0  fptr          = (heaps0, fptr)

_evacuateExample :: ((TimHeap, TimHeap), Addr) -> IO ()
_evacuateExample (hs0@(srcH0, dstH0), a0) =
  putStr $ unlines $
  ["input:"] ++
  map ("  " ++)
  [ show srcH0
  , show dstH0
  , show a0
  ]
  ++
  ["output:"] ++
  map ("  " ++)
  [ show srcH1
  , show dstH1
  , show a1
  ]
  where ((srcH1, dstH1), a1) = evacuateAddr hs0 a0

_cyclic1 :: ((TimHeap, TimHeap), Addr)
_cyclic1 = ((heap, hInitial), addr)
  where
    {- other object -}
    (heap, _) = hAlloc heap1 (Frame [])

    {- one cyclic object -}
    closure :: Closure
    closure = (code, fptr)
    frame :: Frame
    frame = Frame [ closure ]
    fptr = FrameAddr addr
    (heap1, addr) = hAlloc heap0 frame

    code = mempty
    heap0 = hInitial

_cyclic2a, _cyclic2b :: ((TimHeap, TimHeap), Addr)
(_cyclic2a, _cyclic2b) = ((hs, addr1), (hs, addr2))
  where
    hs = (heap, hInitial)
    {- other object -}
    (heap, _) = hAlloc heap2 (Frame [])

    {- two cyclic objects -}
    closure2 :: Closure
    closure2 = (code, fptr1)
    frame2 = Frame [ closure2 ]
    (heap2, addr2) = hAlloc heap1 frame2
    fptr2 = FrameAddr addr2

    closure1 :: Closure
    closure1 = (code, fptr2)
    frame1 = Frame [ closure1 ]
    (heap1, addr1) = hAlloc heap0 frame1
    fptr1 = FrameAddr addr1

    code = mempty
    heap0 = hInitial

scavengeHeap :: TimHeap -> TimHeap -> TimHeap
scavengeHeap heap toHeap = foldl (uncurry . hUpdate) toHeap updates
  where
    updates = [ (a, scavengeFrame frame)
              | (a, frame) <- allocs toHeap
              ]

    scavengeFrame frame = case frame of
      Frame cls   -> Frame $ map scavengeClosure cls
      _           -> frame

    scavengeClosure (is, fptr) = (is, scavengeFramePtr fptr)

    scavengeFramePtr fptr = case fptr of
      FrameAddr a -> FrameAddr $ lookupF a
      _           -> fptr

    lookupF addr = case hLookup heap addr of
      Forward a -> a
      frame     -> error $ "scavengeHeap: not Forward: " ++ show (addr, frame)

---

showFullResults :: [TimState] -> String
showFullResults states =
  concatMap iDisplay $
  [ iStr "Supercombinator definitions", iNewline, iNewline
  , showSCDefns first_state, iNewline, iNewline
  , iStr "State transitions", iNewline ]
  ++
  (iLaynList $ map showState states)
  ++
  [ iNewline, iNewline ]
  ++
  [ showStats $ last states ]
  where
    (first_state:_rest_states) = states

showResults :: [TimState] -> [Char]
showResults states =
  iDisplay $ iConcat [ showState last_state, iNewline, iNewline, showStats last_state ]
  where
    last_state = last states

showSCDefns :: TimState -> IseqRep
showSCDefns TimState{..} = iInterleave iNewline $ map showSC cstore_

showSC :: (Name, CCode) -> IseqRep
showSC (name, (il, slots)) =
  iConcat
  [ iStr "Code for ", iStr name, iStr ":", iNewline
  , iStr "   ", showInstructions Full il, iNewline
  , iStr "   Slots: ", showSlots slots, iNewline
  ]

showState :: TimState -> IseqRep
showState TimState{..} =
  iConcat $
  gcDump_ : iNewline :
  [ iStr "Code:   ", showInstructions Terse instr_, iStr " Slots: ", showSlots islots_ , iNewline
  , showFrame heap_ fptr_
  , showStack stack_
  , showValueStack vstack_
  , showDump dump_
  , showHeap heap_
  , iNewline
  ]

showFrame :: TimHeap -> FramePtr -> IseqRep
showFrame _heap FrameNull        = iStr "Frame (null)" <> iNewline
showFrame heap (FrameAddr addr)  = iConcat [ iStr "Frame (addr): ", showHeapEntry addr (hLookup heap addr), iNewline ]
showFrame _heap (FrameInt n)     = iConcat [ iStr "Frame (int): ", iNum n, iNewline ]

showStack :: TimStack -> IseqRep
showStack stack =
  iConcat
  [ iStr "Arg stack: ["
  , iIndent (iInterleave iNewline $ map showClosure $ list stack)
  , iStr "]", iNewline
  ]

showValueStack :: TimValueStack -> IseqRep
showValueStack vstack = iStr "Value stack: " <> iStr (show $ list vstack) <> iNewline

showDump :: TimDump -> IseqRep
showDump _dump = iNil

showHeap :: TimHeap -> IseqRep
showHeap heap =
  iConcat
  [ iStr "Heap: ["
  , iIndent (iInterleave iNewline $ map showEnt $ allocs heap)
  , iStr "]"
  ]
  where showEnt = uncurry showHeapEntry

showHeapEntry :: Addr -> Frame -> IseqRep
showHeapEntry a f = iStr (showAddr a) <> iStr ": " <> showHeapFrame f

showHeapFrame :: Frame -> IseqRep
showHeapFrame (Frame cls) =
  iConcat
  [ iStr "Frame: <"
  , iIndent (iInterleave iNewline $ map showClosure cls)
  , iStr ">"
  ]
showHeapFrame (Forward a) = iStr "Forward: " <> iStr (showAddr a)

showClosure :: Closure -> IseqRep
showClosure ((i, ss), f) =
  iConcat
  [ iStr "(", showInstructions Terse i, iStr ", "
  , iStr "Slots: ", showSlots ss, iStr ", "
  , iStr "FramePtr: ", showFramePtr f, iStr ")"
  ]

showFramePtr :: FramePtr -> IseqRep
showFramePtr FrameNull = iStr "null"
showFramePtr (FrameAddr a) = iStr (showAddr a)
showFramePtr (FrameInt n) = iStr "int " <> iNum n

showAddr :: Addr -> String
showAddr addr = '#' : show addr

showStats :: TimState -> IseqRep
showStats TimState{..} =
  iConcat
  [ iStr "Steps taken = ", iNum (statGetSteps stats_), iNewline
  , iStr "No of frames allocated = ", iNum (size heap_), iNewline
  {- exercise 4.2 -}
  , iStr "Execution time = ", iNum (extime_ stats_), iNewline
  , iStr "Allocated heap size = ", iNum (ahsize_ stats_), iNewline
  , iStr "Max stack depth = ", iNum (maxDepth stack_), iNewline
  ]

showInstructions :: HowMuchToPrint -> [Instruction] -> IseqRep
showInstructions None _il = iStr "{..}"
showInstructions Terse il =
  iConcat [ iStr "{", iIndent $ iInterleave (iStr ", ") body, iStr "}" ]
  where
    instrs = map (showInstruction None) il
    body | length il <= nTerse = instrs
         | otherwise           = (take nTerse instrs) ++ [iStr ".."]
showInstructions Full il =
  iConcat [ iStr "{ ", iIndent $ iInterleave sep instrs, iStr " }" ]
  where
    sep = iStr "," <> iNewline
    instrs = map (showInstruction Full) il

showInstruction :: HowMuchToPrint -> Instruction -> IseqRep
showInstruction _d (Take t m)  = iStr "Take "  <> iNum t <> iStr " " <> iNum m
showInstruction  d (Move n x) = iStr "Move " <> iNum n <> iStr " " <> showArg d x
showInstruction  d (Enter x) = iStr "Enter " <> showArg d x
showInstruction  d (Push x)  = iStr "Push "  <> showArg d x
showInstruction _d (PushV x) = iStr "PushV " <> iStr (show x)
showInstruction _d  Return   = iStr "Return"
showInstruction _d (Op op)   = iStr $ "Op " <> show op
showInstruction  d (Cond t e) = iStr "Cond"                       <> iNewline <>
                                iStr "  " <> showInstructions d t <> iNewline <>
                                iStr "  " <> showInstructions d e

showArg :: HowMuchToPrint -> TimAMode -> IseqRep
showArg d a = case a of
  Arg m         -> iStr "Arg "  <> iNum m
  Code (il, ss) -> iStr "Code " <> showInstructions d il <> iStr " (Slots: " <> showSlots ss <> iStr ")"
  Label s       -> iStr "Label " <> iStr s
  IntConst n    -> iStr "IntConst " <> iNum n

showSlots :: Slots -> IseqRep
showSlots = iStr . show . Set.toList

nTerse :: Int
nTerse = 3

---

test' :: Bool -> String -> IO ()
test' doGC = putStr . fullRun' doGC

test :: String -> IO ()
test = test' True

check' :: (Eq a, Show a) => (Int -> a) -> (TimState -> a) -> Bool -> Int -> String -> Either String String
check' liftE getV doGC expectI prog
  | length states == limit  =  Left  . unlines $ ("expect  " ++ show expect) : showProg "too long: "
  | lastv == expect         =  Right . unlines $ showProg "pass: " ++ [show lastv]
  | otherwise               =  Left  . unlines $ ("expect  " ++ show expect) : ("but got " ++ show lastv) : showProg "wrong: "
  where
    expect = liftE expectI
    states = take limit . eval' doGC . compile . parse $ prog
    limit = 100000
    lastv = getV $ last states

    showProg word =
      zipWith (++)
      (word : repeat (replicate (length word) ' '))
      (lines prog)

check :: Bool -> Int -> String -> Either String String
check = check' FrameInt fptr_

checkV :: Bool -> Int -> String -> Either String String
checkV = check' (:[]) (list . vstack_)

---

{- exercise 4.1 -}
testEx4_1_a = "main = S K K 4"
testEx4_1_b = "id = S K K ; id1 = id id ; main = id1 4"
testEx4_1_a, testEx4_1_b :: String
testEx4_1_b' = "id x = S K K x ; id1 = id id ; main = id1 4"
testEx4_1_b' :: String

{- exercise 4.4 -}
test_ex44 :: String
test_ex44 = "four = 2 * 2; main = four + four"

test_fact :: String
test_fact = "factorial n = if n 1 (n * factorial (n-1)); main = factorial 3"

test_fib3 :: String
test_fib3 = "fib n = if (n < 2) 1 (fib (n-1) + fib (n-2)); main = fib 3"

test_fib10 :: String
test_fib10 = "fib n = if (n < 2) 1 (fib (n-1) + fib (n-2)); main = fib 10"

test_compose2 :: String
test_compose2 = "compose2 f g x = f (g x x) ; main = compose2 I K 3"

{- exercise 4.9
   * example code - multipleof3
     * condition expression `multipleof3 5` will be executed in VStack
 -}
test_multipleof3 :: String
test_multipleof3 = "multipleof3 x = ((x / 3) * 3) == x ; f y = if (multipleof3 y) 0 1 ; main = f 5"

{- exercise 4.12 -}
-- 35 steps
ex_4_12_with_let = "f x y z = let p = x+y in p+x+y+z ; main = f 1 2 3"

-- 40 steps
ex_4_12_with_nolet = "g p x y z = p+x+y+z ; f x y z = g (x+y) x y z ; main = f 1 2 3"

{- exercise 4.13 -}
ex_4_13_pq =  "f x = letrec p = if (x==0) 1 q ; q = if (x==0) p 2 in p+q ; main = f 1"

---

checks0 :: (Bool -> Int -> String -> Either String String) -> IO ()
checks0 chk = do
  mapM_ putResult results
  when (any isLeft $ map fst results) $ fail "some checks failed!"
  where
    results =
      [ (uncurry (chk doGC) ck, doGC)
      | ck <- checkList
      , doGC <- [False, True]
      ]
    putResult (res, doGC) =
      putLn $ "gc: " ++ (if doGC then "on" else "off") ++ "\n" ++ either id id res
    putLn s = putStrLn "" *> putStr s

checks :: IO ()
checks = checks0 checkV

checkList :: [(Int, String)]
checkList =
  [ (4, "main = S K K 4")
  , (4, "id = S K K ; id1 = id id ; main = id1 4")
  , (3, "compose2 f g x = f (g x x) ; main = compose2 I K 3")
  , (8, "four = 2 * 2; main = four + four")
  , (2, "main = 3 - 1")
  , (0, "main = 3 > 1")  {- True is 0  -}
  , (1, "main = 3 < 1")  {- False is 1  -}
  , (3, "main = if 0 3 4")
  , (4, "main = if 1 3 4")
  , (3, "f = if 0; main = f 3 4")  {- higher-order if -}
  , (6, "factorial n = if n 1 (n * factorial (n-1)); main = factorial 3")
  , (1, "f x y = x == y ; main = f 2 3")  {- DONE: TimMark2 with GC -} {- False is 1 -}
  , (6, "f x y = x * y ; main = f 2 3")  {- DONE: TimMark2 with GC -}
  ]
