{-# LANGUAGE RecordWildCards #-}

module TimMark1CopyGC where

import Utils
import Language

---

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

data Instruction
  = Take Int
  | Enter TimAMode
  | Push TimAMode
  deriving Show

data TimAMode
  = Arg Int
  | Label [Char]
  | Code CCode
  | IntConst Int
  deriving Show

type CCode = ([Instruction], Slots)
type Slots = Set Int

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

data TimValueStack = DummyTimValueStack deriving Show
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
initialArgStack = Stack [] 0 0

initialValueStack :: TimValueStack
initialValueStack = DummyTimValueStack

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

compiledPrimitives :: [(Name, CCode)]
compiledPrimitives = []

---

type TimCompilerEnv = [(Name, TimAMode)]

compileSC :: TimCompilerEnv -> CoreScDefn -> (Name, CCode)
compileSC env (name, args, body)
  | len == 0  =  (name, (instructions, slots))  {- exercise 4.3 -}
  | otherwise =  (name, (Take (length args) : instructions, slots))
  where
    len = length args
    (instructions, slots) = compileR body new_env
    new_env = zip args (map Arg [1..]) ++ env

compileR :: CoreExpr -> TimCompilerEnv -> CCode
compileR (EAp e1 e2)  env = mapAR Push  (compileA e2 env) <> compileR e1 env
compileR (EVar v)     env = mapAR Enter (compileA (EVar v) env)
compileR (ENum n)     env = mapAR Enter (compileA (ENum n) env)
compileR  _e         _env = error "compileR: can't do this yet"

mapAR :: (TimAMode -> Instruction) -> (TimAMode, Slots) -> ([Instruction], Slots)
mapAR f = mapCode (\instA -> [f instA])

compileA :: CoreExpr -> TimCompilerEnv -> (TimAMode, Slots)
compileA (EVar v)  env = case aLookup env v (error $ "Unknown variable " ++ v) of
  a@(Arg n) -> (a, defSlot [n])
  a         -> (a, mempty)
compileA (ENum n) _env = (IntConst n, mempty)
compileA  e        env = (Code ccode, slots)
  where ccode@(_, slots) = compileR e env

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

step :: TimState -> TimState
step state@TimState{..} = case instr_ of
  Take n : instr
    | depth stack_  >= n   -> applyToStats (statAddAllocated n)
                              state { instr_ = instr, fptr_ = fptr', stack_ = discard n stack_, heap_ = heap' }
    | otherwise            -> error "Too few args for Take instructions"
    where (heap', fptr') = fAlloc heap_ (fst $ stkPopN n stack_)

  [Enter am]               -> applyToStats statIncExtime
                              state { instr_ = instr', islots_ = slots', fptr_ = fptr' }
    where ((instr', slots'), fptr') = amToClosure am fptr_ heap_ cstore_
  Enter {} : instr         -> error $ "instructions found after Enter: " ++ show instr

  Push am : instr          -> applyToStats statIncExtime
                              state { instr_ = instr, stack_ = stkPush (amToClosure am fptr_ heap_ cstore_) stack_ }

  []                       -> error $ "instructions is []"

amToClosure :: TimAMode -> FramePtr -> TimHeap -> CodeStore -> Closure
amToClosure amode fptr heap cstore = case amode of
  Arg n         -> fGet heap fptr n
  Code ccode    -> (ccode, fptr)
  Label l       -> (codeLookup cstore l, fptr)
  IntConst n    -> (intCode, FrameInt n)

intCode :: CCode
intCode = mempty

---

gc :: TimState -> TimState
gc s@TimState{..} = s { fptr_ = fptr1, stack_ = stack1, heap_ = dheap }
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
  iConcat
  [ iStr "Code:   ", showInstructions Terse instr_, iNewline
  , showFrameDeref heap_ fptr_
  , showStack stack_
  , showValueStack vstack_
  , showDump dump_
  , showHeap heap_
  , iNewline
  ]

showFrameDeref :: TimHeap -> FramePtr -> IseqRep
showFrameDeref _heap FrameNull = iStr "Null frame ptr" <> iNewline
showFrameDeref heap (FrameAddr addr) =
  iConcat
  [ iStr "Frame: <"
  , iIndent (iInterleave iNewline $ map showClosure $ fList $ hLookup heap addr)
  , iStr ">", iNewline
  ]
showFrameDeref _heap (FrameInt n) = iConcat [ iStr "Frame ptr (int): ", iNum n, iNewline ]

showStack :: TimStack -> IseqRep
showStack stack =
  iConcat
  [ iStr "Arg stack: ["
  , iIndent (iInterleave iNewline $ map showClosure $ list stack)
  , iStr "]", iNewline
  ]

showValueStack :: TimValueStack -> IseqRep
showValueStack _vstack = iNil

showDump :: TimDump -> IseqRep
showDump _dump = iNil

showHeap :: TimHeap -> IseqRep
showHeap heap =
  iConcat
  [ iStr "Heap: ["
  , iIndent (iInterleave iNewline $ map showEnt $ allocs heap)
  , iStr "]"
  ]
  where showEnt (a, f) = iStr (show a) <> iStr ": " <> showFrame f

showFrame :: Frame -> IseqRep
showFrame (Frame cls) =
  iConcat
  [ iStr "Frame: ["
  , iIndent (iInterleave iNewline $ map showClosure cls)
  , iStr "]"
  ]
showFrame (Forward a) = iStr "Forward: " <> iStr (show a)

showClosure :: Closure -> IseqRep
showClosure ((i, ss), f) =
  iConcat
  [ iStr "(", showInstructions Terse i, iStr ", "
  , showSlots ss, iStr ", "
  , showFramePtr f, iStr ")"
  ]

showFramePtr :: FramePtr -> IseqRep
showFramePtr FrameNull = iStr "null"
showFramePtr (FrameAddr a) = iStr (show a)
showFramePtr (FrameInt n) = iStr "int " <> iNum n

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
showInstruction _d (Take m)  = iStr "Take "  <> iNum m
showInstruction  d (Enter x) = iStr "Enter " <> showArg d x
showInstruction  d (Push x)  = iStr "Push "  <> showArg d x

showArg :: HowMuchToPrint -> TimAMode -> IseqRep
showArg d a = case a of
  Arg m         -> iStr "Arg "  <> iNum m
  Code (il, ss) -> iStr "Code " <> showInstructions d il <> iNewline <>
                   iIndent (iStr "     ( Slots: " <> showSlots ss <> iStr " )")
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

check :: FramePtr -> String -> Either String String
check expect prog
  | length states == limit  =  Left  . unlines $ ("expect " ++ show expect) : showProg "too long: "
  | lastv == expect         =  Right . unlines $ showProg "pass: " ++ [show lastv]
  | otherwise               =  Left  . unlines $ ("expect " ++ show expect) : showProg "wrong: "
  where
    states = take limit . eval . compile . parse $ prog
    limit = 100000
    TimState{..} = last states
    lastv = fptr_

    showProg word =
      zipWith (++)
      (word : repeat (replicate (length word) ' '))
      (lines prog)

---

{- exercise 4.1 -}
testEx4_1_a = "main = S K K 4"
testEx4_1_b = "id = S K K ; id1 = id id ; main = id1 4"
testEx4_1_a, testEx4_1_b :: String
testEx4_1_b' = "id x = S K K x ; id1 = id id ; main = id1 4"
testEx4_1_b' :: String

test_compose2 :: String
test_compose2 = "compose2 f g x = f (g x x) ; main = compose2 I K 3"

---

checks :: IO ()
checks = do
  mapM_ (either putLn putLn) results
  when (any isLeft results) $ fail "some checks failed!"
  where
    results = map (uncurry check) checkList
    putLn s = putStrLn "" *> putStr s

checkList :: [(FramePtr, String)]
checkList =
  [ (FrameInt 4, "main = S K K 4")
  , (FrameInt 4, "id = S K K ; id1 = id id ; main = id1 4")
  , (FrameInt 3, "compose2 f g x = f (g x x) ; main = compose2 I K 3")
  ]
