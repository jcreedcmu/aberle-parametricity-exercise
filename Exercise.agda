{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}

{-- This is derived from https://github.com/cbaberle/Parametricity-via-Cohesion --}

module Exercise where

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
    Gph2 : ∀ {ℓ} (ix iy : I) (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Set (ℓ)

    g2rw0x : ∀ {ℓ} (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Gph2 i1 i0 A1 A2 B ≡ A1
    {-# REWRITE g2rw0x #-}

    g2rw0y : ∀ {ℓ} (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Gph2 i0 i1 A1 A2 B ≡ A2
    {-# REWRITE g2rw0y #-}


    g2pair : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (ix iy : I)
             → (a : A1 × A2) (b : (ix ≡ i1) → (iy ≡ i1) → B a) → Gph2 ix iy A1 A2 B

    g2pair10 : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
              → (a : A1 × A2) → (b : (i1 ≡ i1) → (i0 ≡ i1) → B a)
              → g2pair {B = B} i1 i0 a b ≡ fst a
    {-# REWRITE g2pair10 #-}

    g2pair01 : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
              → (a : A1 × A2) → (b : (i0 ≡ i1) → (i1 ≡ i1) → B a)
              → g2pair {B = B} i0 i1 a b ≡ snd a
    {-# REWRITE g2pair01 #-}

    g2fstx : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (iy : I)
            → (g : Gph2 i1 iy A1 A2 B) → A1

    g2fsty : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (ix : I)
            → (g : Gph2 ix i1 A1 A2 B) → A2

    g2beta1x : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (iy : I)
              → (a : A1 × A2) (b : (i1 ≡ i1) → (iy ≡ i1) → B a)
              → g2fstx iy (g2pair {B = B} i1 iy a b) ≡ fst a
    {-# REWRITE g2beta1x #-}

    g2beta1y : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (ix : I)
              → (a : A1 × A2) (b : (ix ≡ i1) → (i1 ≡ i1) → B a)
              → g2fsty ix (g2pair {B = B} ix i1 a b) ≡ snd a
    {-# REWRITE g2beta1y #-}

    g2fst0x : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
             → (g : Gph2 i1 i0 A1 A2 B) → g2fstx {B = B} i0 g ≡ g
    {-# REWRITE g2fst0x #-}

    g2fst0y : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
             → (g : Gph2 i0 i1 A1 A2 B) → g2fsty {B = B} i0 g ≡ g
    {-# REWRITE g2fst0y #-}

    g2snd : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
            → (g : Gph2 i1 i1 A1 A2 B) → B (g2fstx i1 g , g2fsty i1 g)

PolyId : (ℓ : Level) → Set (lsuc ℓ)
PolyId ℓ = (X : Set ℓ) → X → X

module paramId {ℓ} (A1 A2 : Set ℓ)
  (pdA1 : isPathDiscrete A1)
  (pdA2 : isPathDiscrete A2)
  (B : A1 × A2 → Set ℓ)
  (a : A1 × A2) (b : B a) (α : PolyId ℓ) where

    a1 = fst a
    a2 = snd a

    lemma0 : (ix iy : I) → Gph2 ix iy A1 A2 B
    lemma0 ix iy = α (Gph2 ix iy A1 A2 B) (g2pair ix iy a (λ _ _ → b))

    lemma2x : Path (λ _ → A1) (α A1 a1) (g2fstx i1 (lemma0 i1 i1))
    lemma2x = pabs (λ i → g2fstx i (lemma0 i1 i))

    lemma2y : Path (λ _ → A2) (α A2 a2) (g2fsty i1 (lemma0 i1 i1))
    lemma2y = pabs (λ i → g2fsty i (lemma0 i i1))

    substLemma1 : B (g2fstx i1 (lemma0 i1 i1) , g2fsty i1 (lemma0 i1 i1))
    substLemma1 = g2snd (lemma0 i1 i1)

    substLemma0 : B (α A1 a1 , g2fsty i1 (lemma0 i1 i1))
    substLemma0 = transp⁻¹ (λ z → B (z , g2fsty i1 (lemma0 i1 i1))) (mkInv idToPath pdA1 lemma2x) substLemma1

    substLemma : B (α A1 a1 , α A2 a2)
    substLemma = transp⁻¹ (λ z → B (α A1 a1 , z)) (mkInv idToPath pdA2 lemma2y) substLemma0
