
module LambdaMark4 where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Language
import Utils

-----

separateLams :: CoreProgram -> CoreProgram
separateLams = _not_yet

type Level = Int
addLevels :: CoreProgram -> AnnProgram (Name, Level) Level
addLevels = _not_yet

identifyMFEs :: AnnProgram (Name, Level) Level -> Program (Name, Level)
identifyMFEs = _not_yet

renameL :: Program (Name, a) -> Program (Name, a)
renameL = _not_yet

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
