{-# OPTIONS --rewriting --cohesion --flat-split --without-K #-}

{-- This is derived from https://github.com/cbaberle/Parametricity-via-Cohesion --}

module Clean where

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
    Gph1 : ∀ {ℓ} (i : I) (A : Set ℓ) (B : A → Set ℓ) → Set (ℓ)

    g1rw0 : ∀ {ℓ} (A : Set ℓ) (B : A → Set ℓ) → Gph1 i0 A B ≡ A
    {-# REWRITE g1rw0 #-}


    g1pair : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
             → (a : A) → (b : (i ≡ i1) → B a) → Gph1 i A B

    g1pair0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
              → (a : A) → (b : (i0 ≡ i1) → B a)
              → g1pair {B = B} i0 a b ≡ a
    {-# REWRITE g1pair0 #-}


    g1fst : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
            → (g : Gph1 i A B) → A

    g1beta1 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (i : I)
              → (a : A) → (b : (i ≡ i1) → B a)
              → g1fst i (g1pair {B = B} i a b) ≡ a
    {-# REWRITE g1beta1 #-}

    g1fst0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
             → (g : Gph1 i0 A B) → g1fst {B = B} i0 g ≡ g
    {-# REWRITE g1fst0 #-}


    g1snd : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
            → (g : Gph1 i1 A B) → B (g1fst i1 g)

    g1beta2 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
              → (a : A) → (b : (i1 ≡ i1) → B a)
              → g1snd (g1pair {B = B} i1 a b) ≡ b refl
    {-# REWRITE g1beta2 #-}


strBpt : (i0 ≡ i1) → ⊥
strBpt p = g1snd (transp (λ i → Gph1 i ⊤ (λ _ → ⊥)) p tt)


apg1pair : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
           → {a b : A} {aB : B a} {bB : B b}
           → (p : a ≡ b) → aB ≡ transp⁻¹ B p bB
           → (i : I) → g1pair i a (λ _ → aB) ≡ g1pair i b (λ _ → bB)
apg1pair refl refl i = refl

apg1pair0 : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
            → {a b : A} {aB : B a} {bB : B b}
            → (p : a ≡ b) → (q : aB ≡ transp⁻¹ B p bB)
            → apg1pair p q i0 ≡ p
apg1pair0 refl refl = refl
{-# REWRITE apg1pair0 #-}


PolyId : (ℓ : Level) → Set (lsuc ℓ)
PolyId ℓ = (X : Set ℓ) → X → X

module paramId {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ)
                   (a : A) (b : B a) (α : PolyId ℓ) where


    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b))

    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)

    lemma2 : Path (λ _ → A) (α A a) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))

    substLemma : B (α A a)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1


polyId : ∀ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (a : A)
         → (α : PolyId ℓ) → α A a ≡ a
polyId A pdA a α = paramId.substLemma A pdA (λ b → b ≡ a) a refl α


module BoolDiscrete where

    boolIsDisc : isDiscrete Bool
    boolIsDisc false = (con false , refl) , λ { (con false , refl) → refl}
    boolIsDisc true  = (con true  , refl) , λ { (con true , refl) → refl}


    boolIsPDisc : isPathDiscrete Bool
    boolIsPDisc = isDisc→isPDisc boolIsDisc

    polyIdBool : (α : PolyId lzero) → (b : Bool) → α Bool b ≡ b
    polyIdBool α b = polyId Bool boolIsPDisc b α


    shouldBeRefl1 : true ≡ true
    shouldBeRefl1 = polyIdBool (λ X → λ x → x) true


Recℕ : Setω
Recℕ = ∀ {ℓ} (A : Set ℓ) → A → (A → A) → A


postulate
    ℕ : Set₀
    zero : ℕ
    succ : ℕ → ℕ
    recℕ : ℕ → Recℕ
    zeroβ : ∀ {ℓ} (A : Set ℓ) (a : A) (f : A → A) → recℕ zero A a f ≡ a
    {-# REWRITE zeroβ #-}
    succβ : ∀ {ℓ} (n : ℕ) (A : Set ℓ) (a : A) (f : A → A)
            → recℕ (succ n) A a f ≡ f (recℕ n A a f)
    {-# REWRITE succβ #-}
    ℕη : (n : ℕ) → recℕ n ℕ zero succ ≡ n
    {-# REWRITE ℕη #-}


module paramℕ {ℓ} (α : Recℕ) (A : Set ℓ) (pdA : isPathDiscrete A)
                  (B : A → Set ℓ) (a : A) (b : B a)
                  (f : A → A) (ff : (x : A) → B x → B (f x)) where

    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B)
                 (g1pair i a (λ _ → b))
                 (λ g → let g' j q = transp (λ k → Gph1 k A B) q g in
                        g1pair i (f (g1fst i g))
                               (λ p → J⁻¹ (λ j q → B (f (g1fst j (g' j q)))) p
                                          (ff (g1fst i1 (g' i1 p))
                                              (g1snd (g' i1 p)))))

    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)

    lemma2 : Path (λ _ → A) (α A a f) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))

    substLemma : B (α A a f)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1


postulate
    pdℕ1 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n)
           → Σ (m ≡ n) (λ p → idToPath p ≡ e)
    pdℕ2 : ∀ {m n : ℕ} (e : Path (λ _ → ℕ) m n)
           → (q : m ≡ n) (r : idToPath q ≡ e)
           → pdℕ1 e ≡ (q , r)

pdℕ : isPathDiscrete ℕ
pdℕ e = (pdℕ1 e , λ (q , r) → pdℕ2 e q r)

rwPDℕ1 : (n : ℕ) → pdℕ1 (pabs (λ _ → n)) ≡ (refl , refl)
rwPDℕ1 n = pdℕ2 (pabs (λ _ → n)) refl refl
{-# REWRITE rwPDℕ1 #-}

postulate
    rwPDℕ2 : (n : ℕ) → pdℕ2 (pabs (λ _ → n)) refl refl ≡ refl
    {-# REWRITE rwPDℕ2 #-}


indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (succ n)) → (n : ℕ) → P n
indℕ P pz ps n = paramℕ.substLemma (recℕ n) ℕ pdℕ P zero pz succ ps


module ℕexample where
    _plus_ : ℕ → ℕ → ℕ
    m plus n = recℕ m ℕ n succ

    zeroIdR : (n : ℕ) → n plus zero ≡ n
    zeroIdR n = indℕ (λ m → m plus zero ≡ m) refl (λ m p → ap succ p) n

    shouldBeRefl2 : succ (succ zero) ≡ succ (succ zero)
    shouldBeRefl2 = zeroIdR (succ (succ zero))


RecS¹ : Setω
RecS¹ = ∀ {ℓ} (A : Set ℓ) → (a : A) → a ≡ a → A


postulate
    S¹ : Set₀
    base : S¹
    loop : base ≡ base
    recS¹ : S¹ → RecS¹
    baseβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a) → recS¹ base A a l ≡ a
    {-# REWRITE baseβ #-}
    loopβ : ∀ {ℓ} (A : Set ℓ) (a : A) (l : a ≡ a)
              → ap (λ s → recS¹ s A a l) loop ≡ l
    {-# REWRITE loopβ #-}
    S¹η : (s : S¹) → recS¹ s S¹ base loop ≡ s
    {-# REWRITE S¹η #-}


module paramS¹ {ℓ} (A : Set ℓ) (pdA : isPathDiscrete A) (B : A → Set ℓ)
                   (a : A) (b : B a) (l : a ≡ a)
                   (lB : b ≡ transp⁻¹ B l b) (α : RecS¹) where

    lemma0 : (i : I) → Gph1 i A B
    lemma0 i = α (Gph1 i A B) (g1pair i a (λ _ → b)) (apg1pair l lB i)

    lemma1 : B (g1fst i1 (lemma0 i1))
    lemma1 = g1snd (lemma0 i1)

    lemma2 : Path (λ _ → A) (α A a l) (g1fst i1 (lemma0 i1))
    lemma2 = pabs (λ i → g1fst i (lemma0 i))

    substLemma : B (α A a l)
    substLemma = transp⁻¹ B (mkInv idToPath pdA lemma2) lemma1


postulate
    pdS¹1 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
            → Σ (s ≡ t) (λ p → idToPath p ≡ e)
    pdS¹2 : ∀ {s t : S¹} (e : Path (λ _ → S¹) s t)
            → (q : s ≡ t) (r : idToPath q ≡ e)
            → pdS¹1 e ≡ (q , r)

pdS¹ : isPathDiscrete S¹
pdS¹ e = (pdS¹1 e , λ (q , r) → pdS¹2 e q r)

rwPDS¹1 : (s : S¹) → pdS¹1 (pabs (λ _ → s)) ≡ (refl , refl)
rwPDS¹1 s = pdS¹2 (pabs (λ _ → s)) refl refl
{-# REWRITE rwPDS¹1 #-}

postulate
    rwPDS¹2 : (s : S¹) → pdS¹2 (pabs (λ _ → s)) refl refl ≡ refl
    {-# REWRITE rwPDS¹2 #-}


indS¹ : (P : S¹ → Set) (pb : P base) → pb ≡ transp⁻¹ P loop pb → (s : S¹) → P s
indS¹ P pb pl s = paramS¹.substLemma S¹ pdS¹ P base pb loop pl (recS¹ s)
