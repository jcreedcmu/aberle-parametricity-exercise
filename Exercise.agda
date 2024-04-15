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
    ix iy i1 : I


postulate
    Path : ∀ {ℓ} (A : I → Set ℓ) (ax : A ix) (ay : A iy) (a1 : A i1) → Set ℓ


    pabs : ∀ {ℓ} {A : I → Set ℓ}
           → (f : (i : I) → A i) → Path A (f ix) (f iy) (f i1)


    papp : ∀ {ℓ} {A : I → Set ℓ} {ax : A ix} {ay : A iy} {a1 : A i1}
           → Path A ax ay a1 → (i : I) → A i


    pβ : ∀ {ℓ} {A : I → Set ℓ} (f : (i : I) → A i)
           → (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}

    pappx : ∀ {ℓ} {A : I → Set ℓ} {ax : A ix} {ay : A iy} {a1 : A i1}
            → (p : Path A ax ay a1) → papp p ix ≡ ax
    {-# REWRITE pappx #-}

    pappy : ∀ {ℓ} {A : I → Set ℓ} {ax : A ix} {ay : A iy} {a1 : A i1}
            → (p : Path A ax ay a1) → papp p iy ≡ ay
    {-# REWRITE pappy #-}

    papp1 : ∀ {ℓ} {A : I → Set ℓ} {ax : A ix} {ay : A iy} {a1 : A i1}
            → (p : Path A ax ay a1) → papp p i1 ≡ a1
    {-# REWRITE papp1 #-}


idToPath : ∀ {ℓ} {A : Set ℓ} {a b : A}
           → a ≡ b → Path (λ _ → A) a a b
idToPath {a = a} refl = pabs (λ _ → a)


isPathDiscrete : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isPathDiscrete {ℓ = ℓ} A =
    {a b : A} → isEquiv (idToPath {ℓ} {A} {a} {b})


postulate
    pathConst1 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → isDiscrete A → (e : Path (λ _ → A) a a b)
                   → Σ (a ≡ b) (λ p → idToPath p ≡ e)
    pathConst2 : ∀ {@♭ ℓ : Level} {@♭ A : Set ℓ} {a b : A}
                   → (dA : isDiscrete A) → (e : Path (λ _ → A) a a b)
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
    Gph1 : ∀ {ℓ} (i : I) (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Set (ℓ)

    g1rwx : ∀ {ℓ} (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Gph1 ix A1 A2 B ≡ A1
    {-# REWRITE g1rwx #-}

    g1rwy : ∀ {ℓ} (A1 A2 : Set ℓ) (B : A1 × A2 → Set ℓ) → Gph1 iy A1 A2 B ≡ A2
    {-# REWRITE g1rwy #-}

    g1pair : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (i : I)
             → (a : A1 × A2) → (b : (i ≡ i1) → B a) → Gph1 i A1 A2 B

    g1pairx : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
              → (a : A1 × A2) → (b : (ix ≡ i1) → B a)
              → g1pair {B = B} ix a b ≡ fst a
    {-# REWRITE g1pairx #-}

    g1pairy : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
              → (a : A1 × A2) → (b : (iy ≡ i1) → B a)
              → g1pair {B = B} iy a b ≡ snd a
    {-# REWRITE g1pairy #-}

    g1fstx : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
            → (g : Gph1 ix A1 A2 B) → A1

    g1fsty : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
            → (g : Gph1 iy A1 A2 B) → A2

    g1beta1 : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ} (i : I)
              → (a : A1 × A2) → (b : (i ≡ i1) → B a)
              → g1fst i (g1pair {B = B} i a b) ≡ a
    {-# REWRITE g1beta1 #-}

    g1fstx : ∀ {ℓ} {A1 A2 : Set ℓ} {B : A1 × A2 → Set ℓ}
             → (g : Gph1 ix A1 A2 B) → g1fst {B = B} ix g ≡ {!!}
    {-# REWRITE g1fstx #-}


    -- g1snd : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
    --         → (g : Gph1 i1 A B) → B (g1fst i1 g)

    -- g1beta2 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
    --           → (a : A) → (b : (i1 ≡ i1) → B a)
    --           → g1snd (g1pair {B = B} i1 a b) ≡ b refl
    -- {-# REWRITE g1beta2 #-}


-- strBpt : (i0 ≡ i1) → ⊥
-- strBpt p = g1snd (transp (λ i → Gph1 i ⊤ (λ _ → ⊥)) p tt)


-- apg1pair : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
--            → {a b : A} {aB : B a} {bB : B b}
--            → (p : a ≡ b) → aB ≡ transp⁻¹ B p bB
--            → (i : I) → g1pair i a (λ _ → aB) ≡ g1pair i b (λ _ → bB)
-- apg1pair refl refl i = refl

-- apg1pair0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
--             → {a b : A} {aB : B a} {bB : B b}
--             → (p : a ≡ b) → (q : aB ≡ transp⁻¹ B p bB)
--             → apg1pair p q i0 ≡ p
-- apg1pair0 refl refl = refl
-- {-# REWRITE apg1pair0 #-}


-- PolyId : (ℓ : Level) → Set (lsuc ℓ)
-- PolyId ℓ = (X : Set ℓ) → X → X

-- module paramId {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ)
--                    (a : A) (b : B a) (α : PolyId ℓ) where


--     lemma0 : (i : I) → Gph1 i A B
--     lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b))

--     lemma1 : B (g1fst i1 (lemma0 i1))
--     lemma1 = g1snd (lemma0 i1)

--     lemma2 : Path (λ _ → A) (α A a) (g1fst i1 (lemma0 i1))
--     lemma2 = pabs (λ i → g1fst i (lemma0 i))

--     substLemma : B (α A a)
--     substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1
