
module LambdaMark1 where

import Data.Set (Set)
import qualified Data.Set as Set

import Language
import Utils

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
freeVars_case _lv _e _alts = error "freeVars_case: not yet written"

freeVarsOf :: AnnExpr Name (Set Name) -> Set Name
freeVarsOf (free_vars, _expr) = free_vars

freeVarsOf_alt :: AnnAlt Name (Set Name) -> Set Name
freeVarsOf_alt (_tag, args, rhs) =
  Set.difference (freeVarsOf rhs) (Set.fromList args)

-----

abstract :: AnnProgram Name (Set Name) -> CoreProgram
abstract = _

rename :: CoreProgram -> CoreProgram
rename = _

collectSCs :: CoreProgram -> CoreProgram
collectSCs = _

lambdaLift :: CoreProgram -> CoreProgram
lambdaLift = collectSCs . rename . abstract . freeVars

runS :: String -> String
runS = pprint . lambdaLift . parse
