{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}

{-- This is derived from https://github.com/cbaberle/Parametricity-via-Cohesion --}

module ExerciseN where

open import Agda.Primitive
open import Data.Empty
open import Data.Product
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module hott where
    J : ∀ {ℓ κ} {A : Set ℓ} {a : A}
        → (B : (b : A) → a ≡ b → Set κ)
        → {b : A} → (p : a ≡ b) → B a refl → B b p
    J B refl b = b


    transp : ∀ {ℓ κ} {A : Set ℓ} {a b : A}
             → (B : A → Set κ) → (a ≡ b) → B a → B b
    transp B p b = J (λ a _ → B a) p b


    J⁻¹ : ∀ {ℓ κ} {A : Set ℓ} {a : A}
          → (B : (b : A) → a ≡ b → Set κ)
          → {b : A} → (p : a ≡ b) → B b p → B a refl
    J⁻¹ B refl b = b

    transp⁻¹ : ∀ {ℓ κ} {A : Set ℓ} {a b : A}
               → (B : A → Set κ) → (a ≡ b) → B b → B a
    transp⁻¹ B p b = J⁻¹ (λ a _ → B a) p b

    ap : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ} {a b : A}
         → (f : A → B) → a ≡ b → f a ≡ f b
    ap f refl = refl


    isContr : ∀ {ℓ} (A : Set ℓ) → Set ℓ
    isContr A = Σ A (λ a → (b : A) → a ≡ b)


    isEquiv : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ}
              → (A → B) → Set (ℓ ⊔ κ)
    isEquiv {A = A} {B = B} f =
        (b : B) → isContr (Σ A (λ a → f a ≡ b))

    mkInv : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ}
            → (f : A → B) → isEquiv f → B → A
    mkInv f e b = fst (fst (e b))

open hott

module cohesion where


    data ♭ {@♭ ℓ : Level} (@♭ A : Set ℓ) : Set ℓ where
        con : (@♭ x : A) → ♭ A


    ε : {@♭ l : Level} {@♭ A : Set l} → ♭ A → A
    ε (con x) = x


    isDiscrete : ∀ {@♭ ℓ : Level} → (@♭ A : Set ℓ) → Set ℓ
    isDiscrete {ℓ = ℓ} A = isEquiv (ε {ℓ} {A})

open cohesion


postulate
    I : Set₀
    i0 i1 : I


postulate
    Path : ∀ {ℓ} (A : I → Set ℓ) (a0 : A i0) (a1 : A i1) → Set ℓ


    pabs : ∀ {ℓ} {A : I → Set ℓ}
           → (f : (i : I) → A i) → Path A (f i0) (f i1)


    papp : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1}
           → Path A a0 a1 → (i : I) → A i


    pβ : ∀ {ℓ} {A : I → Set ℓ} (f : (i : I) → A i)
           → (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    papp0 : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1}
            → (p : Path A a0 a1) → papp p i0 ≡ a0
    {-# REWRITE papp0 #-}
    papp1 : ∀ {ℓ} {A : I → Set ℓ} {a0 : A i0} {a1 : A i1}
            → (p : Path A a0 a1) → papp p i1 ≡ a1
    {-# REWRITE papp1 #-}


idToPath : ∀ {ℓ} {A : Set ℓ} {a b : A}
           → a ≡ b → Path (λ _ → A) a b
idToPath {a = a} refl = pabs (λ _ → a)


isPathDiscrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isPathDiscrete {ℓ = ℓ} A =
    {a b : A} → isEquiv (idToPath {ℓ} {A} {a} {b})


postulate
    pathConst1 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → isDiscrete A → (e : Path (λ _ → A) a b)
                   → Σ (a ≡ b) (λ p → idToPath p ≡ e)
    pathConst2 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → (dA : isDiscrete A) → (e : Path (λ _ → A) a b)
                   → (q : a ≡ b) → (r : idToPath q ≡ e)
                   → pathConst1 dA e ≡ (q , r)


isDisc→isPDisc : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ}
                 → isDiscrete A → isPathDiscrete A
isDisc→isPDisc dA e =
    (pathConst1 dA e , λ (p , q) → pathConst2 dA e p q)


rwPathConst1 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a : A} → (dA : isDiscrete A)
               → pathConst1 dA (pabs (λ _ → a)) ≡ (refl , refl)
rwPathConst1 {a = a} dA = pathConst2 dA (pabs (λ _ → a)) refl refl
{-# REWRITE rwPathConst1 #-}

postulate
    rwPathConst2 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a : A} → (dA : isDiscrete A)
                   → pathConst2 dA (pabs (λ _ → a)) refl refl ≡ refl
    {-# REWRITE rwPathConst2 #-}

postulate
  K : Set
  -- the intent is that
  -- conn k k' i =
  --    i1 if k ≡ k'
  --    i otherwise
  conn : K → K → I → I
  qconn : (k : K) (i : I) → conn k k i ≡ i1

  conn1 : (k k' : K) → conn k k' i1 ≡ i1
  {-# REWRITE conn1 #-}

  conn-refl : (k : K) → qconn k i1 ≡ refl
  {-# REWRITE conn-refl #-}

  funextK : ∀ {ℓ} {B : K → Set ℓ} {b1 b2 : (k : K) → B k}
             → ((k : K) → b1 k ≡ b2 k) → b1 ≡ b2

Π : ∀ {ℓ} (A : K → Set ℓ) → Set ℓ
Π A = (k : K) → A k

ki1 : K → I
ki1 k = i1

postulate
    Gph : ∀ {ℓ} (i : K → I) (A : K → Set ℓ) (B : Π A → Set ℓ) → Set (ℓ)

    g2rw0k : ∀ {ℓ} (A : K → Set ℓ) (B : Π A → Set ℓ) (k : K) → Gph (λ k' → conn k k' i0) A B ≡ A k
    {-# REWRITE g2rw0k #-}

    g-pair : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ} (i : K → I)
             → (a : Π A) (b : ((k : K) → i k ≡ i1) → B a) → Gph i A B

    g-pairk : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ} (k : K)
              → (a : Π A) → (b : ((k' : K) → conn k k' i0 ≡ i1) → B a)
              → g-pair {B = B} (λ k' → conn k k' i0) a b ≡ a k
    {-# REWRITE g-pairk #-}

    g-fst : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ}
            → (i : K → I) (k : K) (q : i k ≡ i1)
            → (g : Gph i A B) → A k

    g-beta1 : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ}
              → (i : K → I) (k : K) (q : i k ≡ i1)
              → (a : Π A) (b : ((k : K) → i k ≡ i1) → B a)
              → g-fst i k q (g-pair {B = B} i a b) ≡ a k
    {-# REWRITE g-beta1 #-}

    g2fst0k : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ} {k : K}
             → (g : Gph (λ k' → conn k k' i0) A B)
             → g-fst {B = B} (λ k' → conn k k' i0) k (qconn k i0) g ≡ g
    {-# REWRITE g2fst0k #-}

    g-snd : ∀ {ℓ} {A : K → Set ℓ} {B : Π A → Set ℓ}
            → (g : Gph ki1 A B) → B (λ k → g-fst ki1 k refl g)

PolyId : (ℓ : Level) → Set (lsuc ℓ)
PolyId ℓ = (X : Set ℓ) → X → X

module paramId {ℓ} (A : K → Set ℓ)
  (pdA : (k : K) → isPathDiscrete (A k))
  (B : Π A → Set ℓ)
  (a : Π A) (b : B a) (α : PolyId ℓ) where

    lemma0 : (i : K → I) → Gph i A B
    lemma0 i = α (Gph i A B) (g-pair i a (λ _ → b))

    lemma1 : B (λ k → g-fst ki1 k refl (lemma0 ki1))
    lemma1 = g-snd (lemma0 ki1)

    lemma2 : (k : K) → Path (λ _ → A k)  (α (A k) (a k)) (g-fst ki1 k refl (lemma0 ki1))

    lemma2 k = pabs (λ i → g-fst (λ k' → conn k k' i) k (qconn k i)
                            (lemma0 (λ k' → conn k k' i)))

    transportPath : (k : K) → α (A k) (a k) ≡ g-fst ki1 k refl (lemma0 ki1)
    transportPath k = mkInv idToPath (pdA k) (lemma2 k)

    substLemma : B (λ k → α (A k) (a k))
    substLemma = transp⁻¹ B (funextK transportPath) lemma1
