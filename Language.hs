module Language where
import Utils

import Prelude hiding (seq)
import Data.Char (isDigit, isAlpha, isSpace)

data Expr a
   = EVar Name               -- ^ Variables
   | ENum Int                -- ^ Numbers
   | EConstr Int Int         -- ^ Constructor tag arity
   | EAp (Expr a) (Expr a)   -- ^ Applications
   | ELet                    -- ^ Let(rec) expressions
       IsRec                 -- ^   boolean with True = recursive,
       [(a, Expr a)]         -- ^   Definitions
       (Expr a)              -- ^   Boy of let(rec)
   | ECase                   -- ^ Case expression
       (Expr a)              -- ^   Expression to scrutinise
       [Alter a]             -- ^   Alternatives
   | ELam [a] (Expr a)       -- ^ Lambda abstraction
   deriving (Eq, Show)

type CoreExpr = Expr Name

type Name = String

type IsRec = Bool
-- recursive, nonRecursive :: IsRec
-- recursive    = True
-- nonRecursive = False

bindersOf :: [(a,b)] -> [a]
bindersOf defns =  [name | (name, _rhs) <- defns]

rhssOf       :: [(a, b)] -> [b]
rhssOf defns =  [rhs | (_name, rhs) <- defns]

type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _v) = True
isAtomicExpr (ENum _n) = True
isAtomicExpr _e        = False

type Program a = [ScDefn a]
type CoreProgram = Program Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

sample1 :: CoreProgram
sample1 =
  [("main",   [],    (EAp (EVar "double") (ENum 21))),
   ("double", ["x"], (EAp (EAp (EVar "+") (EVar "x")) (EVar "x")))
  ]

prelude :: String
prelude =
  unlines
  [ "I x = x ;"
  , "K x y = x ;"
  , "K1 x y = y ;"
  , "S f g x = f x (g x) ;"
  , "compose f g x = f (g x) ;"
  , "twice f = compose f f"
  ]

lambdaExample :: String
lambdaExample = "twice = \\ f x . f (f x)"

preludeDefs :: CoreProgram
preludeDefs
 = [ ("I", ["x"], EVar "x")
   , ("K", ["x","y"], EVar "x")
   , ("K1",["x","y"], EVar "y")
   , ("S", ["f","g","x"], EAp (EAp (EVar "f") (EVar "x"))
                              (EAp (EVar "g") (EVar "x")))
   , ("compose", ["f","g","x"], EAp (EVar "f")
                                     (EAp (EVar "g") (EVar "x")))
   , ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))
   ]

-----

mkMultiAp :: Int -> CoreExpr -> CoreExpr -> CoreExpr
mkMultiAp n e1 e2 = foldl EAp e1 $ replicate n e2
-- mkMultiAp n e1 e2 = foldl EAp e1 (take n e2s)
--                    where
--                    e2s = e2 : e2s

class Iseq iseq where
  iNil :: iseq
  iStr :: String -> iseq
  iAppend :: iseq -> iseq -> iseq
  iNewline :: iseq
  iIndent :: iseq -> iseq
  iDisplay :: iseq -> String

infixr 5 `iAppend`

------

data Fixity
    = L | N | R
    deriving (Eq, Show)

relops :: [Name]
relops = ["==", "/=", ">", ">=", "<", "<="]

binops :: [(Name, (Int, Fixity))]
binops = [ ("*", (5, L)), ("/", (5, N))
         , ("+", (4, L)), ("-", (4, N)) ]
         ++
         [ (op, (3, N)) | op <- relops]
         ++
         [ ("&&", (2, L))
         , ("||", (1, L)) ]

pprExpr :: (Int, Fixity) -> CoreExpr -> IseqRep
pprExpr _ (EVar v) = iStr v
pprExpr _ (ENum n) = iStr $ show n
pprExpr _ (EConstr tn a)
  = iConcat [iStr "Pack{", iStr (show tn), iStr ",", iStr (show a), iStr "}"]
pprExpr (cpr, cas) (EAp (EAp (EVar op) e1) e2)
  | Just (f@(p, a)) <- op `lookup` binops
  , let unparened =
          case a of
          L -> iConcat [pprExpr f e1, iStr " ", iStr op, iStr " ", pprExpr (p, N) e2]
          R -> iConcat [pprExpr (p, N) e1, iStr " ", iStr op, iStr " ", pprExpr f e2]
          N -> iConcat [pprExpr f e1, iStr " ", iStr op, iStr " ", pprExpr f e2]
        parened = iConcat [iStr "(", unparened, iStr ")"]
        result
          | p >  cpr                           =  unparened
          | p == cpr && cas == a && cas /= N   =  unparened
          | p == cpr && cas == a  {-cas == N-} =  parened
          | p == cpr  {-cas /= a-}             =  parened
          | {-p < cpr-} otherwise              =  parened
  = result
pprExpr _ (EAp e1 e2)
  = iConcat [pprExpr (6, L) e1, iStr " ", pprExpr (6, L) e2]
pprExpr _ (ELet isrec defns expr)
  = iIndent $
    iConcat [ iStr keyword, iNewline
            , iStr "  ",iIndent (pprDefns defns),iNewline
            , iStr "in ",pprExpr (0, N) expr]
    where
    keyword | not isrec = "let"
            | isrec = "letrec"
pprExpr _ (ECase e as)
  = iConcat [ iStr "case", iStr " ", iIndent $ pprExpr (0, N) e, iStr " of " `iAppend` iNewline
            , iStr "    ", iIndent $ iInterleave (iStr " ;" `iAppend` iNewline) $ map pprAlter as
            ]
    where
    pprAlter (tn, ns, ae)
      = iConcat [ iInterleave (iStr " ") $ iStr ("<" ++ show tn ++ ">") : map iStr ns
                , iStr " -> ", pprExpr (0, N) ae
                ]
pprExpr _ (ELam ns e)
  = iConcat $ [iInterleave (iStr " ") $ map iStr $ "\\" : ns, iStr " . ", pprExpr (0, N) e]

pprExpr1 :: CoreExpr -> IseqRep
pprExpr1 = pprExpr (0, N)

pprAExpr :: CoreExpr -> IseqRep
pprAExpr e
  | isAtomicExpr e = pprExpr (0, N) e
  | otherwise = iStr "(" `iAppend` pprExpr (0, N) e `iAppend` iStr ")"

pprDefns :: [(Name, CoreExpr)] -> IseqRep
pprDefns defns = iInterleave sep (map pprDefn defns)
                 where
                 sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> IseqRep
pprDefn (name, expr)
  = iConcat [ iStr name, iStr " = ", iIndent (pprExpr (0, N) expr) ]

pprScDefn :: CoreScDefn -> IseqRep
pprScDefn (name, ns, e)
  = iInterleave (iStr " ") (map iStr $ name : ns) `iAppend`
    iStr " = " `iAppend` iIndent (pprExpr (0, N) e) --  `iAppend` iNewline

iInterleave :: Iseq a => a -> [a] -> a
iInterleave sep = irec
  where
    irec []     =  iNil
    irec [x]    =  x
    irec (x:xs) =  x `iAppend` sep `iAppend` irec xs

iConcat :: Iseq a => [a] -> a
iConcat = foldr iAppend iNil

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)

pprProgram :: CoreProgram -> IseqRep
pprProgram = iInterleave (iStr " ;" `iAppend` iNewline) . map pprScDefn

data IseqRep
   = INil
   | IStr String
   | IAppend IseqRep IseqRep
   | IIndent IseqRep
   | INewline
   deriving Show

instance Iseq IseqRep where
  iNil              = INil
  iAppend INil seq2 = seq2
  iAppend seq1 INil = seq1
  iAppend seq1 seq2 = IAppend seq1 seq2
  iStr ""           = INil
  iStr str          = case break (== '\n') str of
    (_, [])        -> IStr str
    (w, _:str1)    -> IStr w `iAppend` iNewline `iAppend` iStr str1
  iIndent seq       = IIndent seq
  iNewline          = INewline
  iDisplay seq      = flatten 0 [(seq,0)]

flatten1 :: [IseqRep] -> String
flatten1 [] = ""
flatten1 (INil : seqs) = flatten1 seqs
flatten1 (IStr s : seqs) = s ++ (flatten1 seqs)
flatten1 (IAppend seq1 seq2 : seqs) = flatten1 (seq1 : seq2 : seqs)
flatten1 (_ : _) = error "flatten1: not implemented"

flatten :: Int -> [(IseqRep, Int)] -> String
flatten _    [] = ""
flatten col  ((INil, _) : seqs) = flatten col seqs
flatten col  ((IStr s, _): seqs) = s ++ (flatten (col + length s) seqs)
flatten col  ((IAppend seq1 seq2, indent) : seqs)
  = flatten col ((seq1, indent) : (seq2, indent) : seqs)
flatten _col ((INewline, indent) : seqs)
  = '\n' : (space indent) ++ (flatten indent seqs)
flatten col  ((IIndent seq, _indent) : seqs)
  = flatten col ((seq, col) : seqs)

space :: Int -> String
space n = replicate n ' '

iNum :: Iseq a => Int -> a
iNum n = iStr (show n)

iFNum :: Iseq a => Int -> Int -> a
iFNum width n
   = iStr (space (width - length digits) ++ digits)
  where
    digits = show n

iLayn :: Iseq a => [a] -> a
iLayn = iConcat . iLaynList

iLaynList :: Iseq a => [a] -> [a]
iLaynList seqs = map layItem (zip [1..] seqs)
  where
    layItem (n, seq)
      = iConcat [ iFNum 4 n, iStr ") ", iIndent seq, iNewline ]

instance Semigroup IseqRep where
  (<>) = iAppend

instance Monoid IseqRep where
  mempty = iNil

-- type Token = String
type Token = (Int, String)  -- exercise 1.11

-- clex :: String -> [Token]
clex :: Int -> String -> [Token]
clex n ('-':'-':cs) = skipLine cs
  where skipLine (x:xs) | x == '\n' = clex (n + 1) xs
                        | otherwise = skipLine xs
        skipLine []                 = []
        -- exercise 1.9
clex n (c1:c2:cs) | let tk = [c1,c2],
                        tk `elem` twoCharOps  = (n, tk) : clex n cs
                    -- exercise 1.10
clex n (c:cs) | c == '\n'      = clex (n + 1) cs
              | isWhiteSpace c = clex n cs
              | isDigit c,
                let num_token = c : takeWhile isDigit cs
                    rest_cs   = dropWhile isDigit cs
                      = (n, num_token) : clex n rest_cs
              | isAlpha c,
                let var_tok = c : takeWhile isIdChar cs
                    rest_cs = dropWhile isIdChar cs
                      = (n, var_tok) : clex n rest_cs
clex n (c:cs) = (n, [c]) : clex n cs
clex _ []     = []

twoCharOps :: [String]
twoCharOps = ["==", "/=", ">=", "<=", "->", "&&", "||"]

isIdChar, isWhiteSpace :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_')
-- isWhiteSpace c = c `elem` " \t\n"
isWhiteSpace = isSpace

-----

type Parser a = [Token] -> [(a, [Token])]

pLit1 :: String -> Parser String
pLit1 s ((_,tok):toks)
  | s == tok  =  [(s, toks)]
  | otherwise =  []
pLit1 _ []     =  []

keywords :: [String]
keywords = ["case", "of", "let", "letrec", "in", "Pack"]

pVar1 :: Parser String
pVar1 []  = []
pVar1 ((_,tok):toks)
  | isAlpha (head tok)  =  [(tok, toks)]
    -- 練習問題で keyword を判定
  | otherwise           =  []

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 toks = p1 toks ++ p2 toks

pAltL :: Parser a -> Parser a -> Parser a
pAltL p1 p2 toks =
  p1 toks <+ p2 toks
  where
    [] <+ ys = ys
    xs <+ _  = xs

-- take 1 $ pAlt p1 p2 toks

(|||) :: Parser a -> Parser a -> Parser a
(|||) = pAlt

infixr 3 `pAlt`, `pAltL`, |||

pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = pLit "hello" ||| pLit "goodbye"

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 toks
  = [ ( combine v1 v2, toks2) | (v1, toks1) <- p1 toks,
                                (v2, toks2) <- p2 toks1 ]

pGreeting :: Parser (String, String)
pGreeting = pThen keep_first
            (pThen mkPair pHelloOrGoodbye pVar)
            (pLit "!")
            where
              keep_first = const
              mkPair = (,)
-- pGreeting = pThen keep_first
--             (pThen mkPair pHelloOrGoodbye pVar)
--             (pLit "!")
--             where
--               keep_first = const
--               mkPair = (,)

pThen3 :: (a -> b -> c -> d)
       -> Parser a
       -> Parser b
       -> Parser c
       -> Parser d
pThen3 f pa pb pc toks
  = [ ( f v1 v2 v3, toks3) | (v1, toks1) <- pa toks,
                             (v2, toks2) <- pb toks1,
                             (v3, toks3) <- pc toks2 ]

pThen4 :: (a -> b -> c -> d -> e)
       -> Parser a
       -> Parser b
       -> Parser c
       -> Parser d
       -> Parser e
pThen4 f pa pb pc pd toks
  = [ ( f v1 v2 v3 v4, toks4) | (v1, toks1) <- pa toks,
                                (v2, toks2) <- pb toks1,
                                (v3, toks3) <- pc toks2,
                                (v4, toks4) <- pd toks3 ]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = pOneOrMore p ||| pEmpty []

pZeroOrMoreL :: Parser a -> Parser [a]
pZeroOrMoreL p = pOneOrMoreL p `pAltL` pEmpty []

pGreetings :: Parser [(String, String)]
pGreetings = pZeroOrMore pGreeting

-- exercise 1.13
pEmpty :: a -> Parser a
pEmpty x toks = [(x,toks)]

-- exercise 1.13
pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p = pThen (:) p (pZeroOrMore p)

pOneOrMoreL :: Parser a -> Parser [a]
pOneOrMoreL p = pThen (:) p (pZeroOrMoreL p)
-- exercise 1.19

pGreetingsN :: Parser Int
pGreetingsN = pZeroOrMore pGreetings `pApply` length

many :: Parser a -> Parser [a]
many = pZeroOrMore

some :: Parser a -> Parser [a]
some = pOneOrMore

manyL :: Parser a -> Parser [a]
manyL = pZeroOrMoreL

someL :: Parser a -> Parser [a]
someL = pOneOrMoreL

ppure :: a -> Parser a
ppure = pEmpty

optional :: Parser a -> Parser (Maybe a)
optional p = Just |$| p ||| ppure Nothing

-- exercise 1.14
pApply :: Parser a -> (a -> b) -> Parser b
pApply p f toks = [ (f x, toks') | (x, toks') <- p toks ]

(|$|) :: (a -> b) -> Parser a -> Parser b
(|$|) = flip pApply

pap :: Parser (a -> b) -> Parser a -> Parser b
pap pf pa toks = [ (f x, toks2)
                 | (f, toks1) <- pf toks
                 , (x, toks2) <- pa toks1
                 ]

(|*|) :: Parser (a -> b) -> Parser a -> Parser b
(|*|) = pap

(<**) :: Parser a -> Parser b -> Parser a
(<**) = pThen const

(**>) :: Parser a -> Parser c -> Parser c
(**>) = pThen (\_ y -> y)

infixl 4 |$|, |*|, <**, **>

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep p sep =
  (:) |$| p |*| many (sep **> p)
  {-
  pThen (:) p $ pZeroOrMore (sep `op` p)
  where
    op = pThen (\_ b -> b)
   -}
  -- exercise 1.15

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 = pOneOrMoreWithSep

pSat :: (String -> Bool) -> Parser String
pSat pre toks = case toks of
  ((_, t):toks') | pre t -> [(t, toks')]
  _                      -> []
-- exercise 1.16

-----

pLit :: String -> Parser String
pLit s = pSat (== s)

pVar :: Parser String
pVar = pSat (\tok -> isAlpha (head tok) && (tok `notElem` keywords))
-- exercise 1.17

pNum :: Parser Int
pNum = read |$| pSat (all isDigit)
-- exercise 1.18

runParser :: Parser a -> [Token] -> a
runParser parser = take_first_parse . parser
  where
    take_first_parse ((prog, []) : others) = prog
    take_first_parse (parse      : others) = take_first_parse others
    take_first_parse other                 = error "Syntax error"

syntax :: [Token] -> CoreProgram
syntax = runParser pProgram

pProgram :: Parser CoreProgram
pProgram = pSc `sepBy1` (pLit ";")

pSc :: Parser CoreScDefn
pSc = pThen4 mkSc pVar (pZeroOrMore pVar) (pLit "=") pExpr

mkSc :: Name -> [a] -> b -> Expr a -> ScDefn a
mkSc fun args _ expr = (fun, args, expr)
-- exercise 1.20

pPack :: Parser (Expr a)
pPack =
  ppure EConstr <** pLit "Pack" <**
  pLit "{" |*|
  pNum <** pLit "," |*| pNum <**
  pLit "}"

pAexpr :: Parser CoreExpr
pAexpr =
  EVar |$| pVar
  |||
  ENum |$| pNum
  |||
  pPack
  |||
  pLit "(" **> pExpr <**  pLit ")"
-- exercise 1.21

pDefn :: Parser (Name, CoreExpr)
pDefn = pThen3 (\n _ e -> (n, e)) pVar (pLit "=") pExpr

pLet :: Parser CoreExpr
pLet =
  ELet |$|
  (pLit "letrec" **> ppure True
   |||
   pLit "let"    **> ppure False) |*|
   pDefn `sepBy1` pLit ";" <**
  pLit "in" |*|
  pExpr

pAlter :: Parser CoreAlt
pAlter =
  ppure (,,) <**
  pLit "<" |*| pNum <** pLit ">" |*|
  pZeroOrMore pVar <**
  pLit "->" |*|
  pExpr

pAlters :: Parser [CoreAlt]
pAlters = pAlter `sepBy1` (pLit ";")

pCase :: Parser CoreExpr
pCase =
  ppure ECase <** pLit "case" |*|
  pExpr <** pLit "of" |*|
  pAlters

pLam :: Parser CoreExpr
pLam =
  ppure ELam <** pLit "\\" |*|
  (some pVar) <** pLit "." |*|
  pExpr

pExpr :: Parser CoreExpr
pExpr =
  pLet |||
  pCase |||
  pLam |||
  pExpr1

mkApChain :: [Expr a] -> Expr a
mkApChain (f:as) = foldl EAp f as
mkApChain []     = error "mkApChain: empty expr list"


type PartialExpr = Maybe (Name, CoreExpr)

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e  Nothing = e
assembleOp e1 (Just (op, e2)) = EAp (EAp (EVar op) e1) e2

pExpr1c :: Parser PartialExpr
pExpr1c = optional $ (,) |$| pLit "||" |*| pExpr1

pExpr1 :: Parser CoreExpr
pExpr1 = assembleOp |$| pExpr2 |*| pExpr1c

pExpr2c :: Parser PartialExpr
pExpr2c = optional $ (,) |$| pLit "&&" |*| pExpr2

pExpr2 :: Parser CoreExpr
pExpr2 = assembleOp |$| pExpr3 |*| pExpr2c

pRelop :: Parser Name
pRelop = foldr1 (|||) $ map pLit relops

pExpr3c :: Parser PartialExpr
pExpr3c = optional $ (,) |$| pRelop |*| pExpr4

pExpr3 :: Parser CoreExpr
pExpr3 = assembleOp |$| pExpr4 |*| pExpr3c

pExpr4c :: Parser PartialExpr
pExpr4c = optional $
          (,) |$| pLit "+" |*| pExpr4
          |||
          (,) |$| pLit "-" |*| pExpr5

pExpr4 :: Parser CoreExpr
pExpr4 = assembleOp |$| pExpr5 |*| pExpr4c

testPExpr4 :: IO ()
testPExpr4
   | good      = pure ()
   | otherwise = do
       mapM_ print $ rs
       fail "test pExer4 failed"
  where
    rs = take 1 $ pExpr1 $ clex 1 "a + b - c"
    good = [ x | (x, _) <- rs ]
           ==
           [ EAp (EAp (EVar "+") (EVar "a")) (EAp (EAp (EVar "-") (EVar "b")) (EVar "c")) ]

pExpr5c :: Parser PartialExpr
pExpr5c = optional $
          (,) |$| pLit "*" |*| pExpr5
          |||
          (,) |$| pLit "/" |*| pExpr6

pExpr5 :: Parser CoreExpr
pExpr5 = assembleOp |$| pExpr6 |*| pExpr5c

testPExpr5 :: IO ()
testPExpr5
   | good      = pure ()
   | otherwise = do
       mapM_ print $ rs
       fail "test pExer5 failed"
  where
    rs = take 1 $ pExpr1 $ clex 1 "a * b / c"
    good = [ x | (x, _) <- rs ]
           ==
           [ EAp (EAp (EVar "*") (EVar "a")) (EAp (EAp (EVar "/") (EVar "b")) (EVar "c")) ]

pExpr6 :: Parser CoreExpr
pExpr6 = mkApChain |$| some pAexpr

-- pExpr1 CPS version
-- type MaybeK a r = r -> (a -> r) -> r
type PartialExprK r = r -> (Name -> CoreExpr -> r) -> r

assembleOpK :: CoreExpr -> PartialExprK CoreExpr -> CoreExpr
assembleOpK e1 k = k e1 $ \op e2 -> EAp (EAp (EVar op) e1) e2

partialExprK :: Parser Name -> Parser CoreExpr -> Parser (PartialExprK r)
partialExprK np ep =
  (\n e _ k -> k n e) |$| np |*| ep
  |||
  ppure const

pExpr1cK :: Parser (PartialExprK r)
pExpr1cK = partialExprK (pLit "||") pExpr1

pExpr1K :: Parser CoreExpr
pExpr1K = assembleOpK |$| pExpr6 |*| pExpr1cK


_example_in :: [String]
_example_in =
    [ "f = 3 ;"
    , "g x y = let z = x in z ;"
    , "h x = case (let y = x in y) of"
    , "       <1> -> 2 ;"
    , "       <2> -> 5"
    ]

parse' :: Parser a -> String -> a
parse' parser = runParser parser . clex 1

parse :: String -> CoreProgram
parse = syntax . clex 1

examples :: CoreProgram
examples =
  [ ("f", ["x"],
     ELet True
      [ ("y", EAp (EAp (EVar "+") (EVar "x")) (ENum 1))
      , ("z", EAp (EAp (EVar "+") (EVar "y")) (ENum 1))]
      (EVar "z")),
    ("g", ["x"],
      EAp (EAp (EVar "+") (EVar "x")) (ENum 1)),

    -- h = x + y > p * length xs
    ("h", [],
     EAp
     (EAp
      (EVar ">")
      (EAp (EAp (EVar "+") (EVar "x")) (EVar "y")))
     (EAp
      (EAp
       (EVar "*")
       (EVar "p"))
      (EAp (EVar "length") (EVar "xs")))),

    -- u = 5 / (3 * x * (7 - (2 + x + 1)))
    ("u", [],
     ENum 5 |/|
     (ENum 3 |*| EVar "x" |*| (ENum 7 |-| (ENum 2 |+| EVar "x" |+| ENum 1)))),

    ("v", [],
     (ENum 1 |+| ENum 2) |+| ENum 3),

    ("x", [],
     ENum 1 |+| (ENum 2 |+| ENum 3))
  ]
  where
    ap2 f x y = EAp (EAp f x) y
    (|*|) = ap2 (EVar "*")
    (|/|) = ap2 (EVar "/")
    (|+|) = ap2 (EVar "+")
    (|-|) = ap2 (EVar "-")
    infixr 5 |*|
    infix  5 |/|
    infixr 4 |+|
    infix  4 |-|


---------- old codes -----------

pprExprS :: CoreExpr -> String
pprExprS (ENum n) = show n
pprExprS (EVar v) = v
pprExprS (EAp e1 e2) = pprExprS e1 ++ " " ++ pprAExprS e2

pprAExprS :: CoreExpr -> String
pprAExprS e
  | isAtomicExpr e = pprExprS e
  | otherwise = "(" ++ pprExprS e ++ ")"

-----

pprExprN :: CoreExpr -> IseqRep
pprExprN (EVar v) = iStr v
pprExprN (ENum n) = iStr $ show n
pprExprN (EConstr tn a)
  = iConcat [iStr "Pack{", iStr (show tn), iStr ",", iStr (show a), iStr "}"]
pprExprN (EAp (EAp (EVar op) e1) e2)
  | op `elem` map fst binops
  = iConcat [pprAExprN e1, iStr " ", iStr op, iStr " ", pprAExprN e2]
pprExprN (EAp e1 e2)
  = iConcat [pprExprN e1, iStr " ", pprAExprN e2]
pprExprN (ELet isrec defns expr)
  = iIndent $
    iConcat [ iStr keyword, iNewline
            , iStr "  ",iIndent (pprDefnsN defns),iNewline
          , iStr "in ",pprExprN expr]
    where
    keyword | not isrec = "let"
            | isrec = "letrec"
pprExprN (ECase e as)
  = iConcat [ iStr "case", iStr " ", pprExprN e, iStr " of "
            , iStr "    ", iIndent $ iInterleave (iStr ";" `iAppend` iNewline) $ map pprAlter as
            ]
    where
    pprAlter (tn, ns, ae)
      = iConcat [ iInterleave (iStr " ") $ iStr ("<" ++ show tn ++ ">") : map iStr ns
                , iStr " -> ", pprExprN ae
                ]
pprExprN (ELam ns e)
  = iConcat $ [iInterleave (iStr " ") $ map iStr $ "\\" : ns, iStr " ", pprExprN e]

pprAExprN :: CoreExpr -> IseqRep
pprAExprN e
  | isAtomicExpr e = pprExprN e
  | otherwise = iStr "(" `iAppend` pprExprN e `iAppend` iStr ")"

pprDefnsN :: [(Name, CoreExpr)] -> IseqRep
pprDefnsN defns = iInterleave sep (map pprDefnN defns)
                 where
                 sep = iConcat [ iStr ";", iNewline ]

pprDefnN :: (Name, CoreExpr) -> IseqRep
pprDefnN (name, expr)
  = iConcat [ iStr name, iStr " = ", iIndent (pprExprN expr) ]

pprScDefnN :: CoreScDefn -> IseqRep
pprScDefnN (name, ns, e)
  = iInterleave (iStr " ") (map iStr $ name : ns) `iAppend`
    iStr " = " `iAppend` pprExprN e `iAppend` iNewline
