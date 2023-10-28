{-# LANGUAGE RecordWildCards #-}

module TimMark1CopyGC where

import Utils
import Language

---

import Control.Monad (when)
import Data.Either (isLeft)
import Data.List (mapAccumL)

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
  | Code [Instruction]
  | IntConst Int
  deriving Show

---

modify :: (s -> a) -> (a -> s -> s) -> (a -> a) -> s -> s
modify get set update s = set (update (get s)) s

---

data TimState =
  TimState
  { instr_    :: [Instruction]
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

{-
type TimState = ( [Instruction],
                  FramePtr,
                  TimStack,
                  TimValueStack,
                  TimDump,
                  TimHeap,
                  CodeStore,
                  TimStats )
 -}

---

data FramePtr
  = FrameAddr Addr  -- The address of a frame
  | FrameInt Int    -- An integer value
  | FrameNull       -- Uninitialized
  deriving (Eq, Show)

---

type TimStack = Stack Closure
type Closure = ([Instruction], FramePtr)

---

data TimValueStack = DummyTimValueStack deriving Show
data TimDump = DummyTimDump deriving Show

type TimHeap = Heap Frame

data Frame
  = Frame [Closure]
  | Forward Addr
  deriving Show

type CodeStore = Assoc Name [Instruction]

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

codeLookup :: CodeStore -> Name -> [Instruction]
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

compiledPrimitives :: [(Name, [Instruction])]
compiledPrimitives = []

---

type TimCompilerEnv = [(Name, TimAMode)]

compileSC :: TimCompilerEnv -> CoreScDefn -> (Name, [Instruction])
compileSC env (name, args, body)
  | len == 0  =  (name, instructions)  {- exercise 4.3 -}
  | otherwise =  (name, Take (length args) : instructions)
  where
    len = length args
    instructions = compileR body new_env
    new_env = zip args (map Arg [1..]) ++ env

compileR :: CoreExpr -> TimCompilerEnv -> [Instruction]
compileR (EAp e1 e2)  env = Push (compileA e2 env) : compileR e1 env
compileR (EVar v)     env = [Enter (compileA (EVar v) env)]
compileR (ENum n)     env = [Enter (compileA (ENum n) env)]
compileR  _e         _env = error "compileR: can't do this yet"

compileA :: CoreExpr -> TimCompilerEnv -> TimAMode
compileA (EVar v)  env = aLookup env v (error $ "Unknown variable " ++ v)
compileA (ENum n) _env = IntConst n
compileA  e        env = Code (compileR e env)

---

runProg :: [Char] -> [Char]
runProg = showResults . eval . compile . parse

compile :: CoreProgram -> TimState
compile program =
  TimState
  { instr_   = [Enter (Label "main")]
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
                              state { instr_ = instr', fptr_ = fptr' }
    where (instr', fptr') = amToClosure am fptr_ heap_ cstore_
  Enter {} : instr         -> error $ "instructions found after Enter: " ++ show instr

  Push am : instr          -> applyToStats statIncExtime
                              state { instr_ = instr, stack_ = stkPush (amToClosure am fptr_ heap_ cstore_) stack_ }

  []                       -> error $ "instructions is []"

amToClosure :: TimAMode -> FramePtr -> TimHeap -> CodeStore -> ([Instruction], FramePtr)
amToClosure amode fptr heap cstore = case amode of
  Arg n       -> fGet heap fptr n
  Code il     -> (il, fptr)
  Label l     -> (codeLookup cstore l, fptr)
  IntConst n  -> (intCode, FrameInt n)

intCode :: [Instruction]
intCode = []

---

gc :: TimState -> TimState
gc s@TimState{..} = s { fptr_ = fptr1, stack_ = stack1, heap_ = dheap }
  where
    _heaps2 :: (TimHeap, TimHeap)
    (_heaps2@(_, dheap), fptr1) = copyFramePtr heaps1 fptr_

    stack1 :: TimStack
    stack1 = stkOfList scls1 (maxDepth stack_)

    heaps1 :: (TimHeap, TimHeap)
    (heaps1, scls1) = mapAccumL copyClosure heaps0 scls0

    scls0 = list stack_
    heaps0 = (heap_, hInitial)

copyClosure :: (TimHeap, TimHeap) -> Closure -> ((TimHeap, TimHeap), Closure)
copyClosure heaps0 (codes, ptr) = (heaps1, (codes, ptr1))
  where (heaps1, ptr1) = copyFramePtr heaps0 ptr

copyFramePtr :: (TimHeap, TimHeap) -> FramePtr -> ((TimHeap, TimHeap), FramePtr)
copyFramePtr heaps0@(srcH0, _dstH0) (FrameAddr saddr)  = ((srcH2, dstH2), FrameAddr daddr)
  where
    srcH2 = hUpdate srcH1 saddr (Forward daddr)
    (dstH2, daddr) = hAlloc dstH1 f1

    ((srcH1, dstH1), f1) = copyFrame heaps0 f0
    f0 = hLookup srcH0 saddr
copyFramePtr heaps  leaf                             = (heaps, leaf)

copyFrame :: (TimHeap, TimHeap) -> Frame -> ((TimHeap, TimHeap), Frame)
copyFrame heaps0@(_, dstH0) (Forward daddr) = (heaps0, hLookup dstH0 daddr)
copyFrame heaps0            (Frame cs)      = (heaps1, Frame $ zip codes nptrs)
  where
    (codes, ptrs) = unzip cs
    (heaps1, nptrs) = mapAccumL copyFramePtr heaps0 ptrs

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

showSC :: (Name, [Instruction]) -> IseqRep
showSC (name, il) =
  iConcat
  [ iStr "Code for ", iStr name, iStr ":", iNewline
  , iStr "   ", showInstructions Full il, iNewline, iNewline
  ]

showState :: TimState -> IseqRep
showState TimState{..} =
  iConcat
  [ iStr "Code:   ", showInstructions Terse instr_, iNewline
  , showFrame heap_ fptr_
  , showStack stack_
  , showValueStack vstack_
  , showDump dump_
  , iNewline
  ]

showFrame :: TimHeap -> FramePtr -> IseqRep
showFrame _heap FrameNull = iStr "Null frame ptr" <> iNewline
showFrame heap (FrameAddr addr) =
  iConcat
  [ iStr "Frame: <"
  , iIndent (iInterleave iNewline $ map showClosure $ fList $ hLookup heap addr)
  , iStr ">", iNewline
  ]
showFrame _heap (FrameInt n) = iConcat [ iStr "Frame ptr (int): ", iNum n, iNewline ]

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

showClosure :: Closure -> IseqRep
showClosure (i, f) =
  iConcat
  [ iStr "(", showInstructions Terse i, iStr ", "
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
  Arg m       -> iStr "Arg "  <> iNum m
  Code il     -> iStr "Code " <> showInstructions d il
  Label s     -> iStr "Label " <> iStr s
  IntConst n  -> iStr "IntConst " <> iNum n

nTerse :: Int
nTerse = 3

---

test' :: Bool -> String -> IO ()
test' doGC = putStr . fullRun' doGC

test :: String -> IO ()
test = test' False

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
  ]
