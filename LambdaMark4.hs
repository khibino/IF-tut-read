
module LambdaMark4 where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Language
import Utils

-----

separateLams :: CoreProgram -> CoreProgram
separateLams prog =
  [ (name, [], mkSepLams args (separateLams_e rhs))
  | (name, args, rhs) <- prog
  ]

separateLams_e :: CoreExpr -> CoreExpr
separateLams_e (EVar v)                  = EVar v
separateLams_e (EConstr t a)             = EConstr t a
separateLams_e (ENum n)                  = ENum n
separateLams_e (EAp e1 e2)               = EAp (separateLams_e e1) (separateLams_e e2)

separateLams_e (ECase e alts)            =
  ECase (separateLams_e e)
  [ (tag, args, separateLams_e e1)
  | (tag, args, e1) <- alts
  ]

separateLams_e (ELam args body)          = mkSepLams args (separateLams_e body)

separateLams_e (ELet is_rec defns body)  =
  ELet is_rec [(name, separateLams_e rhs) | (name, rhs) <- defns] (separateLams_e body)

mkSepLams :: [Name] -> CoreExpr -> CoreExpr
mkSepLams args body = foldr mkSepLam body args where mkSepLam arg body1 = ELam [arg] body1

-----

type Level = Int
addLevels :: CoreProgram -> AnnProgram (Name, Level) Level
addLevels = freeToLevel . freeVars

freeSetToLevel :: Assoc Name Level -> Set Name -> Level
freeSetToLevel env free =
  foldl max 0 [aLookup env n 0 | n <- Set.toList free]
  -- If there are no free variables, return level zero

freeToLevel :: AnnProgram Name (Set Name) -> AnnProgram (Name, Level) Level
freeToLevel prog = map freeToLevel_sc prog

freeToLevel_sc :: AnnScDefn Name (Set Name) -> AnnScDefn (Name, Level) Level
freeToLevel_sc (sc_name, [], rhs) = (sc_name, [], freeToLevel_e 0 [] rhs)
freeToLevel_sc (_scn   , as,_rhs) = error $ "freeToLevel_sc: inconsistent, sc args: " ++ show as

isTerminal :: AnnExpr' a b -> Bool
isTerminal (AAp {})  = False
isTerminal _e        = True

freeToLevel_e
  :: Level                        -- ^ Level of context
  -> Assoc Name Level             -- ^ Level of in-scope names
  -> AnnExpr Name (Set Name)      -- ^ Input expression
  -> AnnExpr (Name, Level) Level  -- ^ Result expression
freeToLevel_e _level _env (_free, ANum k)       = (0, ANum k)
freeToLevel_e _level  env (_free, AVar v)       = (aLookup env v 0, AVar v)
freeToLevel_e _level _env (_free, AConstr t a)  = (0, AConstr t a)
freeToLevel_e  level  env (_free, AAp e1 e2)    = (mlv, AAp (nonTermLv e1') (nonTermLv e2'))
  where e1' = freeToLevel_e level env e1
        e2' = freeToLevel_e level env e2
        mlv = max (levelOf e1') (levelOf e2')
        nonTermLv e@(_lv, re)
          | isTerminal re = e
          | otherwise     = (mlv, re)
freeToLevel_e  level  env ( free, ALam args body)  =
  (freeSetToLevel env free, ALam args' body')
  where
    body' = freeToLevel_e (level + 1) (args' ++ env) body
    args' = [(arg, level + 1) | arg <- args]
freeToLevel_e  level  env (_free, ALet is_rec defns body)  =
  (levelOf new_body, ALet is_rec new_defns new_body)
  where
    binders  = bindersOf defns
    rhss     = rhssOf defns

    new_binders  = [(name, max_rhs_level) | name <- binders]
    new_rhss     = map (freeToLevel_e level rhs_env) rhss
    new_defns    = zip new_binders new_rhss
    new_body     = freeToLevel_e level body_env body

    free_in_rhss   = Set.unions [free | (free, _rhs) <- rhss]
    max_rhs_level  = freeSetToLevel level_rhs_env free_in_rhss

    body_env       = new_binders ++ env
    rhs_env | is_rec           = body_env
            | otherwise        = env
    level_rhs_env | is_rec     = [(name, 0) | name <- binders] ++ env
                  | otherwise  = env
freeToLevel_e  level  env ( free, ACase e alts) =
  (freeSetToLevel env free, ACase e' alts')
  where e' = freeToLevel_e level env e
        alts' = [freeToLevel_alt level env alt | alt <- alts]

freeToLevel_alt
  :: Level
  -> Assoc Name Level
  -> AnnAlt Name (Set Name)
  -> AnnAlt (Name, Level) Level
freeToLevel_alt level env (tn, args, body) = (tn, args', body')
  where
    body' = freeToLevel_e (level + 1) (args' ++ env) body
    args' = [(arg, level + 1) | arg <- args]

levelOf :: AnnExpr a Level -> Level
levelOf (level, _e) = level

-----

identifyMFEs :: AnnProgram (Name, Level) Level -> Program (Name, Level)
identifyMFEs prog =
  [ (sc_name, [], identifyMFEs_e 0 rhs)
  | (sc_name, [], rhs) <- prog
  ]

notMFECandidate :: AnnExpr' a b -> Bool
notMFECandidate (AConstr {})  = True
notMFECandidate (ANum {})     = True
notMFECandidate (AVar {})     = True
notMFECandidate _ae           = False -- For now everything else is a candidate

identifyMFEs_e
  :: Level
  -> AnnExpr (Name, Level) Level
  -> Expr (Name, Level)
identifyMFEs_e cxt (level, e)
  | level == cxt || notMFECandidate e  = e'
  | otherwise                          = transformMFE level e'
  where e' = identifyMFEs_e1 level e

transformMFE
  :: Level
  -> Expr (Name, Level)
  -> Expr (Name, Level)
transformMFE level e = ELet nonRecursive [(("v", level), e)] (EVar "v")

identifyMFEs_e1
  :: Level
  -> AnnExpr' (Name, Level) Level
  -> Expr (Name, Level)
identifyMFEs_e1 _level (AConstr t a)  = EConstr t a
identifyMFEs_e1 _level (ANum n)       = ENum n
identifyMFEs_e1 _level (AVar v)       = EVar v
identifyMFEs_e1  level (AAp e1 e2)    =
  EAp (identifyMFEs_e level e1) (identifyMFEs_e level e2)
identifyMFEs_e1 _level (ALam args body)  =
  ELam args (identifyMFEs_e arg_level body)
  where (_name, arg_level) = head args
identifyMFEs_e1  level (ALet is_rec defns body)  =
  ELet is_rec defns' body'
  where
    body'  = identifyMFEs_e level body
    defns' = [ ((name, rhs_level), identifyMFEs_e rhs_level rhs)
             | ((name, rhs_level), rhs) <- defns
             ]
identifyMFEs_e1 _level _e = _not_yet

-----

-- exercise 6.10, relax type signaure
renameL :: Program (Name, a) -> Program (Name, a)
renameL prog = renameGen newNamesL prog

renameGen
  :: (NameSupply -> [a] -> (NameSupply, [a], Assoc Name Name))
  -> Program a
  -> Program a
renameGen new_binders prog = snd (mapAccumL rename_sc initialNameSupply prog)
  where rename_sc ns (sc_name, args, rhs) = (ns2, (sc_name, args', rhs'))
          where
            (ns1, args', env) = new_binders ns args
            (ns2, rhs') = renameGen_e new_binders env ns1 rhs

renameGen_e
  :: (NameSupply -> [a] -> (NameSupply, [a], Assoc Name Name))
  -> Assoc Name Name
  -> NameSupply
  -> Expr a
  -> (NameSupply, Expr a)

-- exercise 6.9
renameGen_e _new_binders  env  ns (EVar v)       = (ns, EVar (aLookup env v v))
renameGen_e _new_binders _env  ns (EConstr t a)  = (ns, EConstr t a)
renameGen_e _new_binders _env  ns (ENum n)       = (ns, ENum n)

renameGen_e  new_binders  env  ns (EAp e1 e2)    = (ns2, EAp e1' e2')
  where (ns1, e1') = renameGen_e new_binders env ns  e1
        (ns2, e2') = renameGen_e new_binders env ns1 e2

renameGen_e  new_binders  env  ns (ELam args body)  = (ns2, ELam args' body')
  where (ns1, args', env') = new_binders ns args
        (ns2, body') = renameGen_e new_binders (env' ++ env) ns1 body

renameGen_e  new_binders  env  ns (ELet is_rec defns body)  =
  (ns3, ELet is_rec (zip binders' rhss') body')
  where (ns1, body') = renameGen_e new_binders body_env ns body
        binders = bindersOf defns
        (ns2, binders', env') = new_binders ns1 binders
        body_env = env' ++ env
        (ns3, rhss') = mapAccumL (renameGen_e new_binders rhsEnv) ns2 (rhssOf defns)
        rhsEnv | is_rec     = body_env
               | otherwise  = env

renameGen_e  new_binders  env  ns (ECase e alts) = (ns2, ECase e' alts')
  where (ns1, e') = renameGen_e new_binders env ns e
        astep = renameGen_alt new_binders env
        (ns2, alts') = mapAccumL astep ns1 alts

renameGen_alt
  :: (NameSupply -> [a] -> (NameSupply, [a], Assoc Name Name))
  -> Assoc Name Name
  -> NameSupply
  -> Alter a
  -> (NameSupply, Alter a)
renameGen_alt new_binders env ns (tn, args, body) = (ns2, (tn, args', body'))
  where (ns1, args', env') = new_binders ns args
        (ns2, body') = renameGen_e new_binders (env' ++ env) ns1 body

-----

float :: Program (Name, Level) -> CoreProgram
float = _not_yet

-----

freeVars :: CoreProgram -> AnnProgram Name (Set Name)
freeVars prog =
  [ (name, args, freeVars_e (Set.fromList args) body)
  | (name, args, body) <- prog
  ]

freeVars_e :: Set Name -> CoreExpr -> AnnExpr Name (Set Name)

freeVars_e _lv (ENum k) = (Set.empty, ANum k)

freeVars_e  lv (EVar v) | Set.member v lv  = (Set.singleton v , AVar v)
                        | otherwise        = (Set.empty       , AVar v)

freeVars_e  lv (EAp e1 e2) =
  (Set.union (freeVarsOf e1') (freeVarsOf e2'), AAp e1' e2')
  where e1'  = freeVars_e lv e1
        e2'  = freeVars_e lv e2

freeVars_e  lv (ELam args body) =
  (Set.difference (freeVarsOf body') (Set.fromList args), ALam args body')
  where body'   = freeVars_e new_lv body
        new_lv  = Set.union lv (Set.fromList args)

freeVars_e  lv (ELet is_rec defns body) =
  (Set.union defnsFree bodyFree, ALet is_rec defns' body')
  where binders        = bindersOf defns
        binderSet      = Set.fromList binders
        body_lv        = Set.union lv binderSet
        rhs_lv | is_rec     = body_lv
               | otherwise  = lv
        rhss'          = map (freeVars_e rhs_lv) (rhssOf defns)
        defns'         = zip binders rhss'
        freeInValues   = Set.unions (map freeVarsOf rhss')
        defnsFree | is_rec     = Set.difference freeInValues binderSet
                  | otherwise  = freeInValues
        body'          = freeVars_e body_lv body
        bodyFree       = Set.difference (freeVarsOf body') binderSet

freeVars_e  lv (ECase e alts) = freeVars_case lv e alts

freeVars_e _lv (EConstr _t _a) = error "freeVars_e: no case for constructors"

freeVars_case :: Set Name -> CoreExpr -> [CoreAlt] -> AnnExpr Name (Set Name)
freeVars_case  lv  e  alts = (fvset, ACase e' alts')
  where fvset = Set.unions (freeVarsOf e' : map freeVarsOf_alt alts')
        e'     = freeVars_e lv e
        alts'  = [(tag, args, freeVars_e lv rhs) | (tag, args, rhs) <- alts]

freeVarsOf :: AnnExpr Name (Set Name) -> Set Name
freeVarsOf (free_vars, _expr) = free_vars

freeVarsOf_alt :: AnnAlt Name (Set Name) -> Set Name
freeVarsOf_alt (_tag, args, rhs) =
  Set.difference (freeVarsOf rhs) (Set.fromList args)

pprintFreeVars :: AnnProgram Name (Set Name) -> Name
pprintFreeVars = pprintAnn iStr (iStr . ("{" ++) . (++ "}") . intercalate "," . Set.toList)

{- |
>>> putStrLn $ pprintFreeVars $ freeVars $ parse "f x = \\ y . case x of <1> g -> g y ; <2> g h -> h (g y)"
f x = ⦃{x} \ y . ⦃{x,y} case ⦃{x} x⦄ of
          <1> g -> ⦃{y} ⦃{} g⦄ ⦃{y} y⦄⦄ ;
          <2> g h -> ⦃{y} ⦃{} h⦄ ⦃{y} ⦃{} g⦄ ⦃{y} y⦄⦄⦄⦄⦄
 -}

-----

recursive, nonRecursive :: IsRec
recursive     = True
nonRecursive  = False

abstract :: AnnProgram Name (Set Name) -> CoreProgram
abstract prog =
  [ (sc_name, args, abstract_e rhs)
  | (sc_name, args, rhs) <- prog
  ]

abstract_e :: AnnExpr Name (Set Name) -> CoreExpr

abstract_e (_free, AVar v)     = EVar v
abstract_e (_free, ANum k)     = ENum k

abstract_e (_free, AAp e1 e2)  = EAp (abstract_e e1) (abstract_e e2)

abstract_e (_free, ALet is_rec defns body) =
  ELet is_rec [ (name, abstract_e lbody) | (name, lbody) <- defns ] (abstract_e body)

abstract_e ( free, ALam args body) =
  foldl EAp sc (map EVar fvList)
  where fvList = Set.toList free
        sc = ELet nonRecursive [("sc", sc_rhs)] (EVar "sc")
        sc_rhs = ELam (fvList ++ args) (abstract_e body)

abstract_e (_free, AConstr _t _a) = error "abstract_e: no case for Constr"
abstract_e ( free, ACase e alts) = abstract_case free e alts

abstract_case :: Set Name -> AnnExpr Name (Set Name) -> [AnnAlt Name (Set Name)] -> Expr Name
abstract_case _free  e  alts = ECase e' alts'
  where e'     = abstract_e e
        alts'  = [(tag, args, abstract_e alt) | (tag, args, alt) <- alts]

{- |
>>> putStrLn $ pprint $ abstract $ freeVars $ parse "f x = \\ y . case x of <1> g -> g y ; <2> g h -> h (g y)"
f x = let
        sc = \ x y . case x of
                 <1> g -> g y ;
                 <2> g h -> h (g y)
      in sc x
 -}

-----

type NameSupply = Int

initialNameSupply :: NameSupply
initialNameSupply = 0

getName :: NameSupply -> Name -> (NameSupply, Name)
getName name_supply prefix = (name_supply + 1, makeName prefix name_supply)

getNames :: NameSupply -> [Name] -> (NameSupply, [Name])
getNames name_supply prefixes =
  (name_supply + length prefixes, zipWith makeName prefixes [name_supply ..])

makeName :: Name -> NameSupply -> Name
makeName prefix ns = prefix ++ "_" ++ shownum ns

newNames
  :: NameSupply
  -> [Name]
  -> (NameSupply, [Name], Assoc Name Name)
newNames ns old_names = (ns', new_names, env)
  where (ns', new_names) = getNames ns old_names
        env = zip old_names new_names

-- exercise 6.10, relax type signaure
newNamesL
  :: NameSupply
  -> [(Name, a)]
  -> (NameSupply, [(Name, a)], Assoc Name Name)
newNamesL ns old_binders = (ns', new_binders, env)
  where
    old_names         = [name  | ( name, _level) <- old_binders]
    levels            = [level | (_name,  level) <- old_binders]
    (ns', new_names)  = getNames ns old_names
    new_binders       = zip new_names levels
    env               = zip old_names new_names

rename :: CoreProgram -> CoreProgram
rename prog = snd (mapAccumL rename_sc initialNameSupply prog)
  where rename_sc ns (sc_name, args, rhs) = (ns2, (sc_name, args', rhs'))
          where (ns1, args', env) = newNames ns args
                (ns2, rhs') = rename_e env ns1 rhs

rename_e
  :: Assoc Name Name
  -> NameSupply
  -> CoreExpr
  -> (NameSupply, CoreExpr)

rename_e  env  ns (EVar v)     = (ns, EVar (aLookup env v v))
rename_e _env  ns (ENum n)     = (ns, ENum n)

rename_e  env  ns (EAp e1 e2)  = (ns2, EAp e1' e2')
  where (ns1, e1') = rename_e env ns e1
        (ns2, e2') = rename_e env ns1 e2

rename_e  env  ns (ELam args body) = (ns2, ELam args' body')
                                    {- テキストでは ns1 になっている.
                                       ここでは body の rename 結果を NameSupply に反映できるように ns2 を返す. -}
  where (ns1, args', env') = newNames ns args
        (ns2, body') = rename_e (env' ++ env) ns1 body

rename_e  env  ns (ELet is_rec defns body) =
  (ns3, ELet is_rec (zip binders' rhss') body')
  where (ns1, body') = rename_e body_env ns body
        binders = bindersOf defns
        (ns2, binders', env') = newNames ns1 binders
        body_env = env' ++ env
        (ns3, rhss') = mapAccumL (rename_e rhsEnv) ns2 (rhssOf defns)
        rhsEnv | is_rec     = body_env
               | otherwise  = env

rename_e _env _ns (EConstr _t _a) = error "rename_e: no case for constructors"
rename_e  env  ns (ECase e alts) = rename_case env ns e alts

rename_case
  :: Assoc Name Name
  -> NameSupply
  -> CoreExpr
  -> [CoreAlt]
  -> (NameSupply, CoreExpr)
rename_case _env _ns _e _alts = error "rename_case: not yet written"

-----

collectSCs :: CoreProgram -> CoreProgram
collectSCs prog = concat (map collect_one_sc prog)
  where collect_one_sc (sc_name, args, ELet False [(name, ELam args' body')] body)
          | body == EVar name = [(sc_name, args ++ args', body')] {- exercise 6.5 -}
        collect_one_sc (sc_name, args, rhs) =
          (sc_name, args, rhs') : scs
          where (scs, rhs') = collectSCs_e rhs

collectSCs_e :: CoreExpr -> ([CoreScDefn], CoreExpr)

collectSCs_e (ENum k)     = ([], ENum k)
collectSCs_e (EVar v)     = ([], EVar v)

collectSCs_e (EAp e1 e2)  = (scs1 ++ scs2, EAp e1' e2')
  where (scs1, e1') = collectSCs_e e1
        (scs2, e2') = collectSCs_e e2

collectSCs_e (ELam args body)  = (scs, ELam args body')
  where (scs, body') = collectSCs_e body

collectSCs_e (EConstr t a) = ([], EConstr t a)

collectSCs_e (ECase e alts)    = (scs_e ++ scs_alts, ECase e' alts')
  where (scs_e, e') = collectSCs_e e
        (scs_alts, alts') = mapAccumL collectSCs_alt [] alts
        collectSCs_alt scs (tag, args, rhs) = (scs ++ scs_rhs, (tag, args, rhs'))
          where (scs_rhs, rhs') = collectSCs_e rhs

collectSCs_e (ELet is_rec defns body) =
  (rhss_scs ++ body_scs ++ local_scs, mkELet is_rec non_scs' body')
  where (rhss_scs, defns') = mapAccumL collectSCs_d [] defns

        scs'       = [(name, rhs) | (name, rhs) <- defns', isELam rhs]
        non_scs'   = [(name, rhs) | (name, rhs) <- defns', not (isELam rhs)]
        local_scs  = [(name, args, body1) | (name, ELam args body1) <- scs']
        {- scs' は local_scs からしか参照されない.
        local_scs  = [(name, args, body1) | (name, ELam args body1) <- defns']
        のように直接定義した方が、単純でわかりやすいかも.
         -}

        (body_scs, body') = collectSCs_e body

        {- exercise 6.6
           exercise 6.5 と見つけるべきパターンは同じで、
           abstract_e ... ALam で生成された ELet False [("sc",..)] (EVar "sc") を捕捉する.
           ELet の binder の入れ子木を辿りながら、
           ELet の body が EVar name に一致したときに、
           その定義は sc としては取り出さないようにする -}
        collectSCs_d scs (name, ELet False [(name1, ELam argsA bodyA)] bodyL)
          | bodyL == EVar name1 = (scs ++ rhs_scs, (name, ELam argsA rhs'))
          where (rhs_scs, rhs') = collectSCs_e bodyA
        collectSCs_d scs (name, rhs) = (scs ++ rhs_scs, (name, rhs'))
          where (rhs_scs, rhs') = collectSCs_e rhs

isELam :: Expr a -> Bool
isELam ELam {}  = True
isELam _ohter   = False

mkELet :: IsRec -> [(a, Expr a)] -> Expr a -> Expr a
mkELet _      []    body = body  {- exercise 6.3 -}
mkELet is_rec defns body = ELet is_rec defns body

-----

fullyLazyLift :: CoreProgram -> CoreProgram
fullyLazyLift = float . renameL . identifyMFEs . addLevels . separateLams

lambdaLift :: CoreProgram -> CoreProgram
lambdaLift = collectSCs . rename . abstract . freeVars

{- |
>>> putStrLn $ runS "f x = let g = \\y . x*x + y in (g 3 + g 4) ; main = f 6"
f x_0 = let
          g_1 = sc_2 x_0
        in g_1 3 + g_1 4 ;
sc_2 x_3 y_4 = x_3 * x_3 + y_4 ;
main = f 6
 -}
runS :: String -> String
runS = pprint . lambdaLift . parse

runF :: String -> String
runF = pprint . lambdaLift . fullyLazyLift . parse

-----

iShow :: Show a => a -> IseqRep
iShow = iStr . show

iLevel :: Level -> IseqRep
iLevel = iShow

iNL :: (Name, Level) -> IseqRep
iNL (name, level) = iStr $ name ++ "#" ++ show level
