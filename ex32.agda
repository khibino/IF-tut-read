
open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Integer.Base using (ℤ; +0; +_; _+_; _*_)
open import Data.Integer.Properties using (+-comm; *-comm)
import Data.Integer.Properties as Int
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (yes; no)

----------

Int = ℤ
Id = ℕ

Env = List (Id × Int)

data AExpr : Set where
  Num  : Int -> AExpr
  Plus : AExpr -> AExpr -> AExpr
  Mult : AExpr -> AExpr -> AExpr
  Var  : Id -> AExpr
  Let  : Id -> AExpr -> AExpr -> AExpr

varLookup : Env -> Id -> Int
varLookup []             a             = +0
varLookup ((k , v) ∷ ps) a with k Nat.≟ a
...                           | yes p  = v
...                           | no ¬p  = varLookup ps a

aInterpret₁ : Env -> AExpr -> Int
aInterpret₁ env e = recurse e
  where
    recurse : AExpr -> Int
    recurse (Num n) = n
    recurse (Plus e₁ e₂) = recurse e₁ + recurse e₂
    recurse (Mult e₁ e₂) = recurse e₁ * recurse e₂
    recurse (Var a) = varLookup env a
    recurse (Let a e₀ e) = aInterpret₁ lenv e
      where lenv = (a , recurse e₀) ∷ env

pnum : ℕ -> AExpr
pnum n = Num (+ n)

ex0 : AExpr
ex0 = Let 0 (Plus (pnum 1) (pnum 2)) (Mult (pnum 4) (Var 0))

goal0 : aInterpret₁ [] ex0 ≡ (+ 12)
goal0 = refl

data AInstruction : Set where
  INum : Int -> AInstruction
  IPlus : AInstruction
  IMult : AInstruction
  IStore : Id -> AInstruction
  ILoad : Id -> AInstruction
  IDrop : AInstruction

aEval₁ : Env -> List AInstruction -> List Int -> Env × List AInstruction × List Int
aEval₁ env        []              s              =  env , [] , s
aEval₁ env       (INum n ∷ is)    s              =  aEval₁ env is (n ∷ s)
aEval₁ env       (IPlus  ∷ is)    []             =  env , IPlus ∷ is , []
aEval₁ env       (IPlus  ∷ is)    (x ∷ [])       =  env , IPlus ∷ is , x ∷ []
aEval₁ env       (IPlus  ∷ is)    (n₀ ∷ n₁ ∷ s)  =  aEval₁ env is (n₀ + n₁ ∷ s)
aEval₁ env       (IMult  ∷ is)    []             =  env , IMult ∷ is , []
aEval₁ env       (IMult  ∷ is)    (x ∷ [])       =  env , IMult ∷ is , x ∷ []
aEval₁ env       (IMult  ∷ is)    (n₀ ∷ n₁ ∷ s)  =  aEval₁ env is (n₀ * n₁ ∷ s)
aEval₁ env       (IStore a ∷ is)  []             =  env , IStore a ∷ is , []
aEval₁ env       (IStore a ∷ is)  (n ∷ s)        =  aEval₁ ((a , n) ∷ env) is s
aEval₁ env       (ILoad a ∷ is)   s              =  aEval₁ env is (varLookup env a ∷ s)
aEval₁ []        (IDrop  ∷ is)    s              =  [] , IDrop  ∷ is , s
aEval₁ (b ∷ env) (IDrop  ∷ is)    s              =  aEval₁ env is s

aCompile : AExpr -> List AInstruction
aCompile (Num n) = INum n ∷ []
aCompile (Plus e₁ e₂) = aCompile e₁ ++ aCompile e₂ ++ [ IPlus ]
aCompile (Mult e₁ e₂) = aCompile e₁ ++ aCompile e₂ ++ [ IMult ]
aCompile (Var a) = ILoad a ∷ []
aCompile (Let a e₀ e) = aCompile e₀ ++ [ IStore a ] ++ aCompile e ++ [ IDrop ]

-----

pairEq : ∀ {a b : Set} -> ∀ {p q : a} -> ∀ {r s : b} -> (p , r) ≡ (q , s) -> p ≡ q × r ≡ s
pairEq refl = refl , refl

evalTrans₁ : ∀ {e0 : Env} {s0 : List Int} {e1} {s1} {e2} {s2} (xs ys : List AInstruction)
           -> aEval₁ e0 xs s0 ≡ (e1 , [] , s1)
           -> aEval₁ e1 ys s1 ≡ (e2 , [] , s2)
           -> aEval₁ e0 (xs ++ ys) s0 ≡ (e2 , [] , s2)
evalTrans₁ {e0} {s0} [] ys ax ay
           rewrite proj₁ (pairEq ax)
           rewrite proj₂ (pairEq (proj₂ (pairEq ax)))        =  ay
evalTrans₁ {e0}     {s0}           (INum n   ∷ xs) ys ax ay  =  evalTrans₁ {e0} {n       ∷ s0} xs ys ax ay
evalTrans₁ {e0}     {n₀ ∷ n₁ ∷ s0} (IPlus    ∷ xs) ys ax ay  =  evalTrans₁ {e0} {n₀ + n₁ ∷ s0} xs ys ax ay
evalTrans₁ {e0}     {n₀ ∷ n₁ ∷ s0} (IMult    ∷ xs) ys ax ay  =  evalTrans₁ {e0} {n₀ * n₁ ∷ s0} xs ys ax ay
evalTrans₁ {e0}     {n  ∷ s0}      (IStore a ∷ xs) ys ax ay  =  evalTrans₁ {(a , n) ∷ e0} {s0} xs ys ax ay
evalTrans₁ {e0}     {s0}           (ILoad a  ∷ xs) ys ax ay  =  evalTrans₁ {e0} {varLookup e0 a ∷ s0} xs ys ax ay
evalTrans₁ {b ∷ e0} {s0}           (IDrop    ∷ xs) ys ax ay  =  evalTrans₁ {e0} {s0} xs ys ax ay

validEvalCompile : ∀ {env : Env} (s : List Int) (e : AExpr) -> aEval₁ env (aCompile e) s ≡ (env , [] , aInterpret₁ env e ∷ s)
validEvalCompile s (Num x) = refl
validEvalCompile {env} s (Plus e₁ e₂) =
  evalTrans₁ (aCompile e₁) (aCompile e₂ ++ [ IPlus ]) (validEvalCompile s e₁) e₂+
  where aInterpret : AExpr -> Int
        aInterpret = aInterpret₁ env
        e₂+ : aEval₁ env (aCompile e₂ ++ [ IPlus ]) (aInterpret e₁ ∷ s) ≡ (env , [] , aInterpret e₁ + aInterpret e₂ ∷ s)
        e₂+ = evalTrans₁ (aCompile e₂) [ IPlus ] (validEvalCompile (aInterpret e₁ ∷ s) e₂) eq+
          where eq+ : aEval₁ env [ IPlus ] (aInterpret e₂ ∷ aInterpret e₁ ∷ s) ≡ (env , [] , aInterpret e₁ + aInterpret e₂ ∷ s)
                eq+ rewrite +-comm (aInterpret e₁) (aInterpret e₂) = refl
validEvalCompile {env} s (Mult e₁ e₂) =
  evalTrans₁ (aCompile e₁) (aCompile e₂ ++ [ IMult ]) (validEvalCompile s e₁) e₂*
  where aInterpret : AExpr -> Int
        aInterpret = aInterpret₁ env
        e₂* : aEval₁ env (aCompile e₂ ++ [ IMult ]) (aInterpret e₁ ∷ s) ≡ (env , [] , aInterpret e₁ * aInterpret e₂ ∷ s)
        e₂* = evalTrans₁ (aCompile e₂) [ IMult ] (validEvalCompile (aInterpret e₁ ∷ s) e₂) eq*
          where eq* : aEval₁ env [ IMult ] (aInterpret e₂ ∷ aInterpret e₁ ∷ s) ≡ (env , [] , aInterpret e₁ * aInterpret e₂ ∷ s)
                eq* rewrite *-comm (aInterpret e₁) (aInterpret e₂) = refl
validEvalCompile {env} s (Var a) = refl
validEvalCompile {env} s (Let a e₀ e) =
  evalTrans₁
  (aCompile e₀) ([ IStore a ] ++ aCompile e ++ [ IDrop ])
  (validEvalCompile s e₀)
  eWithLet
  where aInterpret : AExpr -> Int
        aInterpret = aInterpret₁ env
        lenv = (a , aInterpret e₀) ∷ env  {- aInterpret (Let a e₀ e) ≡ aInterpret₁ lenv e -}
        eWithLet : aEval₁ env ([ IStore a ] ++ aCompile e ++ [ IDrop ]) (aInterpret e₀ ∷ s) ≡ (env , [] , aInterpret₁ lenv e ∷ s)
        eWithLet = evalTrans₁ {env} {aInterpret e₀ ∷ s} [ IStore a ] (aCompile e ++ [ IDrop ]) refl eqLet
          where eqLet : aEval₁ lenv (aCompile e ++ [ IDrop ]) s ≡ (env , [] , aInterpret₁ lenv e ∷ s)
                eqLet = evalTrans₁ (aCompile e) [ IDrop ] (validEvalCompile s e) refl

aEval : List AInstruction -> List Int -> List AInstruction × List Int
aEval is s = proj₂ (aEval₁ [] is s)

aInterpret : AExpr -> Int
aInterpret = aInterpret₁ []

validEvalCompile₀ : (s : List Int) (e : AExpr) -> aEval (aCompile e) s ≡ ([] , aInterpret e ∷ s)
validEvalCompile₀ s e = proj₂ (pairEq (validEvalCompile s e))
