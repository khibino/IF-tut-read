
-- open import Data.Nat.Base using (ℕ; _+_; _*_)
-- open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Integer.Base using (ℤ; _+_; _*_)
open import Data.Integer.Properties using (+-comm; *-comm)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

----------

{- exercise 3.1 の証明 -}

-----

{- 定義 -}

-- Int = ℕ
Int = ℤ

data AExpr : Set where
  Num  : Int -> AExpr
  Plus : AExpr -> AExpr -> AExpr
  Mult : AExpr -> AExpr -> AExpr

aInterpret : AExpr -> Int
aInterpret (Num n) = n
aInterpret (Plus e₁ e₂) = aInterpret e₁ + aInterpret e₂
aInterpret (Mult e₁ e₂) = aInterpret e₁ * aInterpret e₂

data AInstruction : Set where
  INum : Int -> AInstruction
  IPlus : AInstruction
  IMult : AInstruction

{-
aEval : List AInstruction × List ℕ -> List AInstruction × List ℕ
aEval ([]          , s)             =  [] , s
aEval (INum n ∷ is , s)             =  aEval (is , (n ∷ s))
aEval (IPlus  ∷ is , [])            =  IPlus ∷ is , []
aEval (IPlus  ∷ is , x ∷ [])        =  IPlus ∷ is , x ∷ []
aEval (IPlus  ∷ is , n₀ ∷ n₁ ∷ s)   =  aEval (is , (n₀ + n₁) ∷ s)
aEval (IMult  ∷ is , [])            =  IMult ∷ is , []
aEval (IMult  ∷ is , x ∷ [])        =  IMult ∷ is , x ∷ []
aEval (IMult  ∷ is , n₀ ∷ n₁ ∷ s)   =  aEval (is , (n₀ * n₁) ∷ s)
 -}

aEval : List AInstruction -> List Int -> List AInstruction × List Int
aEval  []            s              =  [] , s
aEval (INum n ∷ is)  s              =  aEval is (n ∷ s)
aEval (IPlus  ∷ is)  []             =  IPlus ∷ is , []
aEval (IPlus  ∷ is)  (x ∷ [])       =  IPlus ∷ is , x ∷ []
aEval (IPlus  ∷ is)  (n₀ ∷ n₁ ∷ s)  =  aEval is (n₀ + n₁ ∷ s)
aEval (IMult  ∷ is)  []             =  IMult ∷ is , []
aEval (IMult  ∷ is)  (x ∷ [])       =  IMult ∷ is , x ∷ []
aEval (IMult  ∷ is)  (n₀ ∷ n₁ ∷ s)  =  aEval is (n₀ * n₁ ∷ s)

aCompile : AExpr -> List AInstruction
aCompile (Num n) = INum n ∷ []
aCompile (Plus e₁ e₂) = aCompile e₁ ++ aCompile e₂ ++ [ IPlus ]
aCompile (Mult e₁ e₂) = aCompile e₁ ++ aCompile e₂ ++ [ IMult ]

-----

{- 証明 -}

pairEq : ∀ {a b : Set} -> ∀ {p q : a} -> ∀ {r s : b} -> (p , r) ≡ (q , s) -> p ≡ q × r ≡ s
pairEq refl = refl , refl

evalTrans : ∀ {s0 s1 s2 : List Int} (xs ys : List AInstruction)
         -> aEval xs s0 ≡ ([] , s1)
         -> aEval ys s1 ≡ ([] , s2)
         -> aEval (xs ++ ys) s0 ≡ ([] , s2)
evalTrans {s0} {s1} {s2}            []           ys ax ay rewrite proj₂ (pairEq ax) = ay
evalTrans {s0} {s1} {s2}           (INum n ∷ xs) ys ax ay = evalTrans {n       ∷ s0} {s1} {s2} xs ys ax ay
evalTrans {n₀ ∷ n₁ ∷ s0} {s1} {s2} (IPlus  ∷ xs) ys ax ay = evalTrans {n₀ + n₁ ∷ s0} {s1} {s2} xs ys ax ay
evalTrans {n₀ ∷ n₁ ∷ s0} {s1} {s2} (IMult  ∷ xs) ys ax ay = evalTrans {n₀ * n₁ ∷ s0} {s1} {s2} xs ys ax ay

validEvalCompile : ∀ (s : List Int) (e : AExpr) -> aEval (aCompile e) s ≡ ([] , aInterpret e ∷ s)
validEvalCompile s (Num n)       =  refl
validEvalCompile s (Plus e₁ e₂)  =
  evalTrans
  (aCompile e₁) (aCompile e₂ ++ [ IPlus ])
  (validEvalCompile s e₁) e₂+
  where e₂+ : aEval (aCompile e₂ ++ [ IPlus ]) (aInterpret e₁ ∷ s) ≡ ([] , aInterpret e₁ + aInterpret e₂ ∷ s)
        e₂+  = evalTrans
               (aCompile e₂) [ IPlus ]
               (validEvalCompile (aInterpret e₁ ∷ s) e₂) eq+
          where eq+ : aEval [ IPlus ] (aInterpret e₂ ∷ aInterpret e₁ ∷ s) ≡ ([] , aInterpret e₁ + aInterpret e₂ ∷ s)
                eq+ rewrite +-comm (aInterpret e₁) (aInterpret e₂) = refl
validEvalCompile s (Mult e₁ e₂)  =
  evalTrans
  (aCompile e₁) (aCompile e₂ ++ [ IMult ])
  (validEvalCompile s e₁) e₂*
  where e₂* : aEval (aCompile e₂ ++ [ IMult ]) (aInterpret e₁ ∷ s) ≡ ([] , aInterpret e₁ * aInterpret e₂ ∷ s)
        e₂*  = evalTrans
               (aCompile e₂) [ IMult ]
               (validEvalCompile (aInterpret e₁ ∷ s) e₂) eq*
          where eq* : aEval [ IMult ] (aInterpret e₂ ∷ aInterpret e₁ ∷ s) ≡ ([] , aInterpret e₁ * aInterpret e₂ ∷ s)
                eq* rewrite *-comm (aInterpret e₁) (aInterpret e₂) = refl

validEvalCompile₀ : ∀ (e : AExpr) -> aEval (aCompile e) [] ≡ ([] , [ aInterpret e ])
validEvalCompile₀ = validEvalCompile []
