
module LambdaMark1 where

import Data.Set (Set)
import qualified Data.Set as Set

import Language
import Utils

-----

freeVars :: CoreProgram -> AnnProgram Name (Set Name)
freeVars = _

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
