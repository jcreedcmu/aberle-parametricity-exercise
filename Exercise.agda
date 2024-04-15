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
    ip iq ir : I -- p and q are two arms of a span based at r


postulate
    Path : ∀ {ℓ} (A : I → Set ℓ) (ap : A ip) (aq : A iq) (ar : A ir) → Set ℓ


    pabs : ∀ {ℓ} {A : I → Set ℓ}
           → (f : (i : I) → A i) → Path A (f ip) (f iq) (f ir)


    papp : ∀ {ℓ} {A : I → Set ℓ} {ap : A ip} {aq : A iq} {ar : A ir}
           → Path A ap aq ar → (i : I) → A i


    pβ : ∀ {ℓ} {A : I → Set ℓ} (f : (i : I) → A i)
           → (i : I) → papp (pabs f) i ≡ f i
    {-# REWRITE pβ #-}
    pappp : ∀ {ℓ} {A : I → Set ℓ} {ap : A ip} {aq : A iq} {ar : A ir}
            → (p : Path A ap aq ar) → papp p ip ≡ ap
    {-# REWRITE pappp #-}
    pappq : ∀ {ℓ} {A : I → Set ℓ} {ap : A ip} {aq : A iq} {ar : A ir}
            → (p : Path A ap aq ar) → papp p iq ≡ aq
    {-# REWRITE pappq #-}
    pappr : ∀ {ℓ} {A : I → Set ℓ} {ap : A ip} {aq : A iq} {ar : A ir}
            → (p : Path A ap aq ar) → papp p ir ≡ ar
    {-# REWRITE pappr #-}


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
    Gph2 : ∀ {ℓ} (i : I) (Ap Aq : Set ℓ) (B : Ap × Aq → Set ℓ) → Set (ℓ)

    g2rwp : ∀ {ℓ} (Ap Aq : Set ℓ) (B : Ap × Aq → Set ℓ) → Gph2 ip Ap Aq B ≡ Ap
    {-# REWRITE g2rwp #-}

    g2rwq : ∀ {ℓ} (Ap Aq : Set ℓ) (B : Ap × Aq → Set ℓ) → Gph2 iq Ap Aq B ≡ Aq
    {-# REWRITE g2rwq #-}

    g2pair : ∀ {ℓ} {Ap Aq : Set ℓ} {B : Ap × Aq → Set ℓ} (i : I)
             → (a : Ap × Aq) (b : (i ≡ ir) → B a) → Gph2 i Ap Aq B

    g2pairp : ∀ {ℓ} {Ap Aq : Set ℓ} {B : Ap × Aq → Set ℓ}
              → (a : Ap × Aq) (b : (ip ≡ ir) → B a)
              → g2pair {B = B} ip a b ≡ fst a
    {-# REWRITE g2pairp #-}

    g2fst : ∀ {ℓ} {Ap Aq : Set ℓ} {B : Ap × Aq → Set ℓ} (i : I)
            → (g : Gph2 i Ap Aq B) → (Ap × Aq)

--     g2fst0 : ∀ {ℓ} {Ap Aq : Set ℓ} {B : Ap × Aq → Set ℓ}
--              → (g : Gph2 i0 Ap Aq B) → g2fst {B = B} i0 g ≡ g
--     {-# REWRITE g2fst0 #-}

--     g2snd : ∀ {ℓ} {Ap Aq : Set ℓ} {B : Ap × Aq → Set ℓ}
--             → (g : Gph2 i1 Ap Aq B) → B (g2fst i1 g)



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


-- module paramId2 {ℓ} (Ap Aq : Set ℓ) (pdA1 : isPathDiscrete A1)
--                                     (pdA2 : isPathDiscrete A2)  (B : Ap × Aq → Set ℓ)
--                    (a : Ap × Aq) (b : B a) (α : PolyId ℓ) where

--     lemma0 : (i : I) → Gph2 i Ap Aq B
--     lemma0 i = α (Gph2 i Ap Aq B) (g2pair i a (λ _ → b))

--     lemma1 : B (g2fst i1 (lemma0 i1))
--     lemma1 = g2snd (lemma0 i1)

--     a1 = fst a
--     a2 = snd a
--     lemma2 : Path (λ _ → Ap × Aq) (α A1 a1 , α A2 a2) (g2fst i1 (lemma0 i1))
--     lemma2 = pabs (λ i → {! g2fst i0 (lemma0 i0)!})
--     --    lemma2 = pabs (λ i → g1fst i (lemma0 i))

--     pdA : isPathDiscrete (Ap × Aq)
--     pdA = {!!}

--     substLemma : B (α A1 (fst a) , α A2 (snd a))
--     substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1

-- polyId : ∀ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (a : A)
--          → (α : PolyId ℓ) → α A a ≡ a
-- polyId A pdA a α = paramId.substLemma A pdA (λ b → b ≡ a) a refl α


-- module BoolDiscrete where

--     boolIsDisc : isDiscrete Bool
--     boolIsDisc false = (con false , refl) , λ { (con false , refl) → refl}
--     boolIsDisc true  = (con true  , refl) , λ { (con true , refl) → refl}


--     boolIsPDisc : isPathDiscrete Bool
--     boolIsPDisc = isDisc→isPDisc boolIsDisc

--     polyIdBool : (α : PolyId lzero) → (b : Bool) → α Bool b ≡ b
--     polyIdBool α b = polyId Bool boolIsPDisc b α


--     shouldBeRefl1 : true ≡ true
--     shouldBeRefl1 = polyIdBool (λ X → λ x → x) true


-- Recℕ : Setω
-- Recℕ = ∀ {ℓ} (A : Set ℓ) → A → (A → A) → A


-- postulate
--     ℕ : Set₀
--     zero : ℕ
--     succ : ℕ → ℕ
--     recℕ : ℕ → Recℕ
--     zeroβ : ∀ {ℓ} (A : Set ℓ) (a : A) (f : A → A) → recℕ zero A a f ≡ a
--     {-# REWRITE zeroβ #-}
--     succβ : ∀ {ℓ} (n : ℕ) (A : Set ℓ) (a : A) (f : A → A)
--             → recℕ (succ n) A a f ≡ f (recℕ n A a f)
--     {-# REWRITE succβ #-}
--     ℕη : (n : ℕ) → recℕ n ℕ zero succ ≡ n
--     {-# REWRITE ℕη #-}


-- module paramℕ {ℓ} (α : Recℕ) (A : Set ℓ) (pdA : isPathDiscrete A)
--                   (B : A → Set ℓ) (a : A) (b : B a)
--                   (f : A → A) (ff : (x : A) → B x → B (f x)) where

--     lemma0 : (i : I) → Gph1 i A B
--     lemma0 i = α (Gph1 i A B)
--                  (g1pair i a (λ _ → b))
--                  (λ g → let g' j q = transp (λ k → Gph1 k A B) q g in
--                         g1pair i (f (g1fst i g))
--                                (λ p → J⁻¹ (λ j q → B (f (g1fst j (g' j q)))) p
--                                           (ff (g1fst i1 (g' i1 p))
--                                               (g1snd (g' i1 p)))))

--     lemma1 : B (g1fst i1 (lemma0 i1))
--     lemma1 = g1snd (lemma0 i1)

--     lemma2 : Path (λ _ → A) (α A a f) (g1fst i1 (lemma0 i1))
--     lemma2 = pabs (λ i → g1fst i (lemma0 i))

--     substLemma : B (α A a f)
--     substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1


-- postulate
--     pdℕ1 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n)
--            → Σ (m ≡ n) (λ p → idToPath p ≡ e)
--     pdℕ2 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n)
--            → (q : m ≡ n) (r : idToPath q ≡ e)
--            → pdℕ1 e ≡ (q , r)

-- pdℕ : isPathDiscrete ℕ
-- pdℕ e = (pdℕ1 e , λ (q , r) → pdℕ2 e q r)

-- rwPDℕ1 : (n : ℕ) → pdℕ1 (pabs (λ _ → n)) ≡ (refl , refl)
-- rwPDℕ1 n = pdℕ2 (pabs (λ _ → n)) refl refl
-- {-# REWRITE rwPDℕ1 #-}

-- postulate
--     rwPDℕ2 : (n : ℕ) → pdℕ2 (pabs (λ _ → n)) refl refl ≡ refl
--     {-# REWRITE rwPDℕ2 #-}


-- indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (succ n)) → (n : ℕ) → P n
-- indℕ P pz ps n = paramℕ.substLemma (recℕ n) ℕ pdℕ P zero pz succ ps


-- module ℕexample where
--     _plus_ : ℕ → ℕ → ℕ
--     m plus n = recℕ m ℕ n succ

--     zeroIdR : (n : ℕ) → n plus zero ≡ n
--     zeroIdR n = indℕ (λ m → m plus zero ≡ m) refl (λ m p → ap succ p) n

--     shouldBeRefl2 : succ (succ zero) ≡ succ (succ zero)
--     shouldBeRefl2 = zeroIdR (succ (succ zero))


-- RecS¹ : Setω
-- RecS¹ = ∀ {ℓ} (A : Set ℓ) → (a : A) → a ≡ a → A


-- postulate
--     S¹ : Set₀
--     base : S¹
--     loop : base ≡ base
--     recS¹ : S¹ → RecS¹
--     baseβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a) → recS¹ base A a l ≡ a
--     {-# REWRITE baseβ #-}
--     loopβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a)
--               → ap (λ s → recS¹ s A a l) loop ≡ l
--     {-# REWRITE loopβ #-}
--     S¹η : (s : S¹) → recS¹ s S¹ base loop ≡ s
--     {-# REWRITE S¹η #-}


-- module paramS¹ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ)
--                    (a : A) (b : B a) (l : a ≡ a)
--                    (lB : b ≡ transp⁻¹ B l b) (α : RecS¹) where

--     lemma0 : (i : I) → Gph1 i A B
--     lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b)) (apg1pair l lB i)

--     lemma1 : B (g1fst i1 (lemma0 i1))
--     lemma1 = g1snd (lemma0 i1)

--     lemma2 : Path (λ _ → A) (α A a l) (g1fst i1 (lemma0 i1))
--     lemma2 = pabs (λ i → g1fst i (lemma0 i))

--     substLemma : B (α A a l)
--     substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1


-- postulate
--     pdS¹1 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
--             → Σ (s ≡ t) (λ p → idToPath p ≡ e)
--     pdS¹2 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
--             → (q : s ≡ t) (r : idToPath q ≡ e)
--             → pdS¹1 e ≡ (q , r)

-- pdS¹ : isPathDiscrete S¹
-- pdS¹ e = (pdS¹1 e , λ (q , r) → pdS¹2 e q r)

-- rwPDS¹1 : (s : S¹) → pdS¹1 (pabs (λ _ → s)) ≡ (refl , refl)
-- rwPDS¹1 s = pdS¹2 (pabs (λ _ → s)) refl refl
-- {-# REWRITE rwPDS¹1 #-}

-- postulate
--     rwPDS¹2 : (s : S¹) → pdS¹2 (pabs (λ _ → s)) refl refl ≡ refl
--     {-# REWRITE rwPDS¹2 #-}


-- indS¹ : (P : S¹ → Set) (pb : P base) → pb ≡ transp⁻¹ P loop pb → (s : S¹) → P s
-- indS¹ P pb pl s = paramS¹.substLemma S¹ pdS¹ P base pb loop pl (recS¹ s)
