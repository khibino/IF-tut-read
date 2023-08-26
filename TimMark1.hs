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

data HowMuchToPrint = Full | Terse | None deriving Show

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

eval :: TimState -> [TimState]
eval state = state : rest_states
  where
    rest_states | timFinal state = []
                | otherwise      = eval next_state
    next_state = doAdmin (step state)

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
    | length stack_  >= n  -> state { instr_ = instr, fptr_ = fptr', stack_ = drop n stack_, heap_ = heap' }
    | otherwise            -> error "Too few args for Take instructions"
    where (heap', fptr') = fAlloc heap_ (take n stack_)

  [Enter am]               -> state { instr_ = instr', fptr_ = fptr' }
    where (instr', fptr') = amToClosure am fptr_ heap_ cstore_
  Enter {} : instr         -> error $ "instructions found after Enter: " ++ show instr

  Push am : instr          -> state { instr_ = instr, stack_ = amToClosure am fptr_ heap_ cstore_ : stack_ }

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
  , iIndent (iInterleave iNewline $ map showClosure stack)
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
  , iStr "No of frames allocated = ", iNum (size heap_)
  , iNewline
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

test :: String -> IO ()
test = putStr . fullRun
