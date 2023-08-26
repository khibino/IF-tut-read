module TimMark1 where

import Utils
import Language

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

data TimState =
  TimState
  { insts_ :: [Instruction]
  , frame_ :: FramePtr
  , stack_ :: TimStack
  , vstack_ :: TimValueStack
  , dump_ :: TimDump
  , heap_ :: TimHeap
  , codes_ :: CodeStore
  , stats_ :: TimStats
  }
  deriving Show
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
  deriving Show

---

type TimStack = [Closure]
type Closure = ([Instruction], FramePtr)

---

data TimValueStack = DummyTimValueStack deriving Show
data TimDump = DummyTimDump deriving Show

type TimHeap = Heap Frame

type Frame = [Closure]

type CodeStore = Assoc Name [Instruction]

type TimStats = Int

---

fAlloc   :: TimHeap -> [Closure] -> (TimHeap, FramePtr)
fAlloc heap xs = (heap', FrameAddr addr)
  where
    (heap', addr) = hAlloc heap xs

fGet     :: TimHeap -> FramePtr -> Int -> Closure
fGet heap (FrameAddr addr) n = f !! (n-1)
  where
    f = hLookup heap addr
fGet _h f _n = error $ "fGet: not impl: " ++ show f

fUpdate  :: TimHeap -> FramePtr -> Int -> Closure -> TimHeap
fUpdate heap (FrameAddr addr) n closure =
  hUpdate heap addr new_frame
  where
    frame = hLookup heap addr
    new_frame = take (n-1) frame ++ [closure] ++ drop n frame
fUpdate _h f _n _cl = error $ "fUpdate: not impl: " ++ show f

fList    :: Frame -> [Closure]
fList f = f

---

codeLookup :: CodeStore -> Name -> [Instruction]
codeLookup cstore l =
  aLookup cstore l (error ("Attempt to jump to unknown label " ++ show l))

---

statInitial :: TimStats
statInitial = 0

statIncSteps :: TimStats -> TimStats
statIncSteps s = s + 1

statGetSteps :: TimStats -> Int
statGetSteps s = s

---

runProg :: [Char] -> [Char]
runProg = undefined

compile :: CoreProgram -> TimState
compile = undefined

eval :: TimState -> [TimState]
eval = undefined

showResults :: [TimState] -> [Char]
showResults = undefined

fullRun :: [Char] -> [Char]
fullRun = undefined
