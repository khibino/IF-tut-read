{-# LANGUAGE RecordWildCards #-}

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
  aLookup cstore l (error $ "Attempt to jump to unknown label " ++ show l)

---

statInitial :: TimStats
statInitial = 0

statIncSteps :: TimStats -> TimStats
statIncSteps s = s + 1

statGetSteps :: TimStats -> Int
statGetSteps s = s

---

initialArgStack :: TimStack
initialArgStack = []

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
compileSC env (name, args, body) =
  (name, Take (length args) : instructions)
  where
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
runProg = undefined

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

eval :: TimState -> [TimState]
eval state = state : rest_states
  where
    rest_states | timFinal state = []
                | otherwise      = eval next_state
    next_state = doAdmin (step state)

doAdmin :: TimState -> TimState
doAdmin state = applyToStats statIncSteps state

timFinal :: TimState -> Bool
timFinal state = null $ instr_ state

step :: TimState -> TimState
step state@TimState{..} = case instr_ of
  Take n : instr  | length stack_  >= n  -> state { instr_ = instr, fptr_ = fptr', stack_ = drop n stack_, heap_ = heap' }
                  | otherwise            -> error "Too few args for Take instructions"
    where (heap', fptr') = fAlloc heap_ (take n stack_)

  [Enter am]                             -> state { instr_ = instr', fptr_ = fptr' }
    where (instr', fptr') = amToClosure am fptr_ heap_ cstore_
  Enter {} : instr                       -> error $ "instructions found after Enter: " ++ show instr

  Push am : instr                        -> state { instr_ = instr, stack_ = amToClosure am fptr_ heap_ cstore_ : stack_ }

  []                                     -> error $ "instructions is []"

amToClosure :: TimAMode -> FramePtr -> TimHeap -> CodeStore -> ([Instruction], FramePtr)
amToClosure amode fptr heap cstore = case amode of
  Arg n       -> fGet heap fptr n
  Code il     -> (il, fptr)
  Label l     -> (codeLookup cstore l, fptr)
  IntConst n  -> (intCode, FrameInt n)

intCode :: [Instruction]
intCode = []

showResults :: [TimState] -> [Char]
showResults = undefined

fullRun :: [Char] -> [Char]
fullRun = undefined
