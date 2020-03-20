{-# OPTIONS --rewriting #-}
module DualLMRefined where

open import Data.Bool
open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Extensionality
open import Direction

-- variables

variable
  n m : ℕ

----------------------------------------------------------------------
-- auxiliaries for automatic rewriting

n+1=suc-n : n + 1 ≡ suc n
n+1=suc-n {zero} = refl
n+1=suc-n {suc n} = cong suc (n+1=suc-n {n})

{-# REWRITE n+1=suc-n #-}

n+0=n : n + 0 ≡ n
n+0=n {zero} = refl
n+0=n {suc n} = cong suc (n+0=n {n})

{-# REWRITE n+0=n #-}

inject+0-x=x : {x : Fin m} → inject+ 0 x ≡ x
inject+0-x=x {x = zero} = refl
inject+0-x=x {x = suc x} = cong suc inject+0-x=x

{-# REWRITE inject+0-x=x #-}

n+sucm : n + suc m ≡ suc (n + m)
n+sucm {0F} = refl
n+sucm {suc n} = cong suc (n+sucm{n})

{-# REWRITE n+sucm #-}

n=fromℕtoℕn : (toℕ (fromℕ n)) ≡ n
n=fromℕtoℕn {zero}  = refl
n=fromℕtoℕn {suc n} = cong suc (n=fromℕtoℕn {n})

{-# REWRITE n=fromℕtoℕn #-}

sucn∸suctoℕx≡n∸toℕx : {n : ℕ} {x : Fin n} → suc (n ∸ suc (toℕ x)) ≡ n ∸ (toℕ x)
sucn∸suctoℕx≡n∸toℕx {suc n} {0F} = refl
sucn∸suctoℕx≡n∸toℕx {suc n} {suc x} = sucn∸suctoℕx≡n∸toℕx{n}{x}

sym-sucn∸suctoℕx≡n∸toℕx : {n : ℕ} {x : Fin n} → n ∸ (toℕ x) ≡ suc (n ∸ suc (toℕ x))
sym-sucn∸suctoℕx≡n∸toℕx {n} {x} = sym (sucn∸suctoℕx≡n∸toℕx{n}{x})

{-# REWRITE sym-sucn∸suctoℕx≡n∸toℕx #-}

{-# REWRITE m+n∸n≡m #-}

----------------------------------------------------------------------
-- some more required properties on natural numbers and fin

toℕx≤n : {n : ℕ} {x : Fin n} → Data.Nat._≤_ (toℕ x) n
toℕx≤n {suc n} {0F} = z≤n
toℕx≤n {suc n} {suc x} = s≤s toℕx≤n

toℕx≤n' : {n : ℕ} {x : Fin (suc n)} → Data.Nat._≤_ (toℕ x) n
toℕx≤n' {0F} {0F} = z≤n
toℕx≤n' {suc n} {0F} = z≤n
toℕx≤n' {suc n} {suc x} = s≤s (toℕx≤n'{n}{x})

n∸x+x≡n : {n x : ℕ} → Data.Nat._≤_ x n  → n ∸ x + x ≡ n
n∸x+x≡n {0F} {0F} le = refl
n∸x+x≡n {0F} {suc x} ()
n∸x+x≡n {suc n} {0F} le = refl
n∸x+x≡n {suc n} {suc x} (s≤s le) = cong suc (n∸x+x≡n le)

toℕx<n : {n : ℕ} {x : Fin n} → Data.Nat._<_ (toℕ x) n
toℕx<n {suc n} {0F} = s≤s z≤n
toℕx<n {suc n} {suc x} = s≤s toℕx<n

n∸x≡suc[n∸sucx] : {n x : ℕ} → Data.Nat._<_ x n → n ∸ x ≡ suc (n ∸ (suc x))
n∸x≡suc[n∸sucx] {suc n} {0F} le = refl
n∸x≡suc[n∸sucx] {suc n} {suc x} (s≤s le) = n∸x≡suc[n∸sucx] le

suc[n+x]≡n+sucx : {n x : ℕ} → suc (n + x) ≡ (n + suc x)
suc[n+x]≡n+sucx {0F} {x} = refl
suc[n+x]≡n+sucx {suc n} {x} = refl

suc[n∸sucx+x]≡n : {n x : ℕ} → Data.Nat._<_ x n → suc (n ∸ (suc x) + x) ≡ n
suc[n∸sucx+x]≡n {suc n} {0F} le = refl
suc[n∸sucx+x]≡n {suc n} {suc x} (s≤s le) = cong suc (suc[n∸sucx+x]≡n {n} {x} le)

suc[n∸suc[toℕi]+toℕi]≡n : {n : ℕ} {i : Fin n} → suc (n ∸ (suc (toℕ i)) + toℕ i) ≡ n
suc[n∸suc[toℕi]+toℕi]≡n {n} {i} = suc[n∸sucx+x]≡n{n}{toℕ i} toℕx<n

{-# REWRITE suc[n∸suc[toℕi]+toℕi]≡n #-}

<suc : {n x : ℕ} → Data.Nat._<_ x n → Data.Nat._<_ x (suc n)
<suc {suc n} {0F} le = s≤s z≤n
<suc {suc n} {suc x} (s≤s le) = s≤s (<suc {n} {x} le)

----------------------------------------------------------------------

module IND where

  mutual
    data Type (n : ℕ) : Set where
      TUnit TInt : Type n
      TPair : Type n → Type n → Type n
      TChan : SType n → Type n

    data SType (n : ℕ) : Set where
      gdd : (gst : GType n) → SType n
      rec : (gst : GType (suc n)) → SType n
      var : (x : Fin n) → SType n

    data GType (n : ℕ) : Set where
      transmit : (d : Dir) (t : Type n) (s : SType n) → GType n
      choice : (d : Dir) (m : ℕ) (alt : Fin m → SType n) → GType n
      end : GType n

    data MClType (n : ℕ) : Set where
      MClTUnit MClTInt : MClType n
      MClTPair : MClType n → MClType n → MClType n
      MClTChan : SType 0F → MClType n

    data MClSType (n : ℕ) : Set where
      tgdd : (tgst : MClGType n) → MClSType n
      trec : (tgst : MClGType (suc n)) → MClSType n
      tvar : (x : Fin n) → MClSType n

    data MClGType (n : ℕ) : Set where
      ttransmit : (d : Dir) (t : MClType n) (s : MClSType n) → MClGType n
      tchoice : (d : Dir) (m : ℕ) (alt : Fin m → MClSType n) → MClGType n
      end : MClGType n

  ----------------------------------------------------------------------

  weaken1'N : Fin (suc n) → Fin n → Fin (suc n)
  weaken1'N zero x = suc x
  weaken1'N (suc i) zero = zero
  weaken1'N (suc i) (suc x) = suc (weaken1'N i x)

  weaken1'S : Fin (suc n) → SType n → SType (suc n)
  weaken1'G : Fin (suc n) → GType n → GType (suc n)
  weaken1'T : Fin (suc n) → Type n → Type (suc n)

  weaken1'S i (gdd gst) = gdd (weaken1'G i gst)
  weaken1'S i (rec gst) = rec (weaken1'G (suc i) gst)
  weaken1'S i (var x) = var (weaken1'N i x)

  weaken1'G i (transmit d t s) = transmit d (weaken1'T i t) (weaken1'S i s)
  weaken1'G i (choice d m alt) = choice d m (weaken1'S i ∘ alt)
  weaken1'G i end = end

  weaken1'T i TUnit = TUnit
  weaken1'T i TInt = TInt
  weaken1'T i (TPair t₁ t₂) = TPair (weaken1'T i t₁) (weaken1'T i t₂)
  weaken1'T i (TChan x) = TChan (weaken1'S i x)

  weaken1S : SType n → SType (suc n)
  weaken1G : GType n → GType (suc n)
  weaken1T : Type n → Type (suc n)

  weaken1S = weaken1'S zero
  weaken1G = weaken1'G zero
  weaken1T = weaken1'T zero

  weakenS : (n : ℕ) → SType m → SType (m + n)
  weakenG : (n : ℕ) → GType m → GType (m + n)
  weakenT : (n : ℕ) → Type m → Type (m + n)

  weakenS n (gdd gst) = gdd (weakenG n gst)
  weakenS n (rec gst) = rec (weakenG n gst)
  weakenS n (var x) = var (inject+ n x)

  weakenG n (transmit d t s) = transmit d (weakenT n t) (weakenS n s)
  weakenG n (choice d m alt) = choice d m (λ i → weakenS n (alt i))
  weakenG n end = end

  weakenT n TUnit = TUnit
  weakenT n TInt = TInt
  weakenT n (TPair ty ty₁) = TPair (weakenT n ty) (weakenT n ty₁)
  weakenT n (TChan x) = TChan (weakenS n x)

  ----------------------------------------------------------------------

  -- Single substitution with SType 0

  st-substS : SType (suc n) → Fin (suc n) → SType 0 → SType n
  st-substG : GType (suc n) → Fin (suc n) → SType 0 → GType n
  st-substT : Type (suc n) → Fin (suc n) → SType 0 → Type n

  st-substS (gdd gst) i st0 = gdd (st-substG gst i st0)
  st-substS (rec gst) i st0 = rec (st-substG gst (suc i) st0)
  st-substS {n} (var zero) zero st0 = weakenS n st0
  st-substS {suc n} (var zero) (suc i) st0 = var zero
  st-substS {suc n} (var (suc x)) zero st0 = var x
  st-substS {suc n} (var (suc x)) (suc i) st0 = weaken1S (st-substS (var x) i st0)

  st-substG (transmit d t s) i st0 = transmit d (st-substT t i st0) (st-substS s i st0)
  st-substG (choice d m alt) i st0 = choice d m (λ j → st-substS (alt j) i st0)
  st-substG end i st0 = end

  st-substT TUnit i st0 = TUnit
  st-substT TInt i st0 = TInt
  st-substT (TPair ty ty₁) i st0 = TPair (st-substT ty i st0) (st-substT ty₁ i st0)
  st-substT (TChan st) i st0 = TChan (st-substS st i st0)

  -- Single substitution with SType n

  st-substS' : Fin (suc n) → SType n → SType (suc n) → SType n
  st-substG' : Fin (suc n) → SType n → GType (suc n) → GType n 
  st-substT' : Fin (suc n) → SType n → Type (suc n) → Type n

  st-substS' i st (gdd gst) = gdd (st-substG' i st gst)
  st-substS' i st (rec gst) = rec (st-substG' (suc i) (weaken1S st) gst)
  st-substS' i st (var x)
    with compare x i
  st-substS' i st (var .(inject least)) | less .i least = var (inject! least)
  st-substS' .x st (var x) | equal .x = st
  st-substS' .(inject least) st (var (suc x)) | greater .(suc x) least = var x


  st-substG' i st (transmit d t s) = transmit d (st-substT' i st t) (st-substS' i st s)
  st-substG' i st (choice d m alt) = choice d m (λ j → st-substS' i st (alt j))
  st-substG' i st end = end

  st-substT' i st TUnit = TUnit
  st-substT' i st TInt  = TInt
  st-substT' i st (TPair ty ty₁) = TPair (st-substT' i st ty) (st-substT' i st ty₁)
  st-substT' i st (TChan s) = TChan (st-substS' i st s)

  ----------------------------------------------------------------------
  ----------------------------------------------------------------------


----------------------------------------------------------------------

open IND

data Stack : ℕ → Set where
  ε : Stack 0
  ⟪_,_⟫ : Stack n → IND.GType (suc n) → Stack (suc n)

data StackS : ℕ → Set where
  ε : StackS 0
  ⟪_,_⟫ : StackS n → IND.SType n → StackS (suc n)

data StackS0 : ℕ → Set where
  ε : StackS0 0
  ⟪_,_⟫ : StackS0 n → IND.SType 0F → StackS0 (suc n)

data StackMCl : ℕ → Set where
  ε : StackMCl 0
  ⟪_,_⟫ : StackMCl n → IND.MClGType (suc n) → StackMCl (suc n)

-- Stack of length m starting at arbitrary type size n
data Stack' : ℕ → ℕ → Set where
  ε : Stack' n 0
  ⟪_,_⟫ : Stack' n m → IND.GType (suc (n + m)) → Stack' n (suc m)

data Stack'S : ℕ → ℕ → Set where
  ε : Stack'S n 0
  ⟪_,_⟫ : Stack'S n m → IND.SType (n + m) → Stack'S n (suc m)

data Stack'Sn : ℕ → ℕ → Set where
  ε : Stack'Sn n 0
  ⟪_,_⟫ : Stack'Sn n m → IND.SType n → Stack'Sn n (suc m)


get : {n : ℕ} → (i : Fin n) → Stack n → Stack (n ∸ (suc (toℕ i))) × IND.GType (n ∸ (toℕ i))
get {suc n} 0F ⟪ σ , x ⟫ = σ , x
get {suc n} (suc i) ⟪ σ , x ⟫ = get i σ

getS : {n : ℕ} → (i : Fin n) → StackS n → StackS (n ∸ (suc (toℕ i))) × IND.SType (n ∸ (suc (toℕ i)))
getS {suc n} 0F ⟪ σ , x ⟫ = σ , x
getS {suc n} (suc i) ⟪ σ , x ⟫ = getS i σ

getS0 : {n : ℕ} → (i : Fin n) → StackS0 n → StackS0 (n ∸ (suc (toℕ i))) × IND.SType 0F
getS0 {suc n} 0F ⟪ σ , x ⟫ = σ , x
getS0 {suc n} (suc i) ⟪ σ , x ⟫ = getS0 i σ

getMCl : {n : ℕ} → (i : Fin n) → StackMCl n → StackMCl (n ∸ (suc (toℕ i))) × IND.MClGType (n ∸ (toℕ i))
getMCl {suc n} 0F ⟪ σ , x ⟫ = σ , x
getMCl {suc n} (suc i) ⟪ σ , x ⟫ = getMCl i σ

get' : {n m : ℕ} → (i : Fin m) → Stack' n m → Stack' n (m ∸ (suc (toℕ i))) × IND.GType (n + (m ∸ (toℕ i)))
get' {n} {suc m} 0F ⟪ σ , x ⟫ = σ , x
get' {n} {suc m} (suc i) ⟪ σ , x ⟫ = get' i σ

get'S : {n m : ℕ} → (i : Fin m) → Stack'S n m → Stack'S n (m ∸ (suc (toℕ i))) × IND.SType (n + (m ∸ (suc (toℕ i))))
get'S {n} {suc m} 0F ⟪ σ , x ⟫ = σ , x
get'S {n} {suc m} (suc i) ⟪ σ , x ⟫ = get'S i σ

get'Sn : {n m : ℕ} → (i : Fin m) → Stack'Sn n m → Stack'Sn n (m ∸ (suc (toℕ i))) × IND.SType n
get'Sn {n} {suc m} 0F ⟪ σ , x ⟫ = σ , x
get'Sn {n} {suc m} (suc i) ⟪ σ , x ⟫ = get'Sn i σ

----------------------------------------------------------------------


stack-split : (i : Fin n) → Stack n → Stack (n ∸ toℕ i) × Stack' (n ∸ toℕ i) (toℕ i)
stack-split 0F σ = σ , ε
stack-split{n} (suc i) ⟪ σ , x ⟫
  with stack-split i σ
... | σ' , σ'' rewrite (sym (suc[n∸sucx+x]≡n{n}{toℕ i} (<suc toℕx<n))) = σ' , ⟪ σ'' , x ⟫

-- couldn't achieve this by rewriting alone
suc[n+[m∸sucx]+x]≡n+m : {n m x : ℕ} → Data.Nat._<_ x m → suc (n + (m ∸ suc x) + x) ≡ n + m
suc[n+[m∸sucx]+x]≡n+m {0F} {m} {x} le = suc[n∸sucx+x]≡n{m}{x} le
suc[n+[m∸sucx]+x]≡n+m {suc n} {suc m} {0F} le = refl
suc[n+[m∸sucx]+x]≡n+m {suc n} {suc m} {suc x} (s≤s le) = cong suc (cong suc (suc[n+[m∸sucx]+x]≡n+m le))

-- i from the top of the stack
stack'-m-i : {n m : ℕ} → (i : Fin m) → Stack' n m → Stack' (n + (m ∸ (toℕ i))) (toℕ i)
stack'-m-i {n} {m} 0F σ = ε
stack'-m-i {n} {suc m} (suc i) ⟪ σ , x ⟫ rewrite (sym (suc[n+[m∸sucx]+x]≡n+m{n}{m}{toℕ i} toℕx<n)) = ⟪ (stack'-m-i i σ) , x ⟫

weaken1-Stack' : (i : Fin (suc n)) → Stack' n m → Stack' (suc n) m
weaken1-Stack' i ε = ε
weaken1-Stack'{n}{m} i ⟪ σ , x ⟫ = ⟪ (weaken1-Stack' i σ) , (weaken1'G (inject+ m i) x) ⟫

weaken1-Stack'Sn : (i : Fin (suc n)) → Stack'Sn n m → Stack'Sn (suc n) m
weaken1-Stack'Sn i ε = ε
weaken1-Stack'Sn{n}{m} i ⟪ σ , x ⟫ = ⟪ (weaken1-Stack'Sn i σ) , (weaken1'S i x) ⟫

-- substitute after index i, required for rec case
stack-sim-substS-i> : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → SType n → SType (toℕ (suc i))
stack-sim-substG-i> : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → GType n → GType (toℕ (suc i))
stack-sim-substT-i> : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → Type n → Type (toℕ (suc i))

stack-sim-substS-i> i σ (gdd gst) = gdd (stack-sim-substG-i> i σ gst)
stack-sim-substS-i> i σ (rec gst) = rec (stack-sim-substG-i> (suc i) σ gst)
stack-sim-substS-i>{suc n} 0F σ (var 0F) = var 0F
stack-sim-substS-i> 0F σ (var (suc x))
  with getS0 x σ 
... | σ' , s = weaken1S s
stack-sim-substS-i> (suc i) σ (var 0F) = var 0F
stack-sim-substS-i> (suc i) σ (var (suc x)) = weaken1S (stack-sim-substS-i> i σ (var x))

stack-sim-substG-i> i σ (transmit d t s) = transmit d (stack-sim-substT-i> i σ t) (stack-sim-substS-i> i σ s)
stack-sim-substG-i> i σ (choice d m alt) = choice d m (λ x → stack-sim-substS-i> i σ (alt x))
stack-sim-substG-i> i σ end = end

stack-sim-substT-i> i σ TUnit = TUnit
stack-sim-substT-i> i σ TInt = TInt
stack-sim-substT-i> i σ (TPair t t₁) = TPair (stack-sim-substT-i> i σ t) (stack-sim-substT-i> i σ t₁)
stack-sim-substT-i> i σ (TChan x) = TChan (stack-sim-substS-i> i σ x)


-- substitute stack
stack-sim-substS : StackS0 n → SType n → SType 0F
stack-sim-substG : StackS0 n → GType n → GType 0F
stack-sim-substT : StackS0 n → Type n → Type 0F

stack-sim-substS σ (gdd gst) = gdd (stack-sim-substG σ gst)
stack-sim-substS σ (rec gst) = rec (stack-sim-substG-i> 0F σ gst) -- Apply stack substitution to variables 1, ..., suc n; keep 0F; can't extend StackS0 since only SType 0F allowed
stack-sim-substS σ (var x)
  with getS0 x σ
... | σ' , s = s

stack-sim-substG σ (transmit d t s) = transmit d (stack-sim-substT σ t) (stack-sim-substS σ s)
stack-sim-substG σ (choice d m alt) = choice d m (λ x → stack-sim-substS σ (alt x))
stack-sim-substG σ end = end

stack-sim-substT σ TUnit = TUnit
stack-sim-substT σ TInt = TInt
stack-sim-substT σ (TPair t t₁) = TPair (stack-sim-substT σ t) (stack-sim-substT σ t₁)
stack-sim-substT σ (TChan x) = TChan (stack-sim-substS σ x)


stack-sim-substS'-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → SType m → SType (n + toℕ i)
stack-sim-substG'-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → GType m → GType (n + toℕ i)
stack-sim-substT'-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → Type m → Type (n + toℕ i)

stack-sim-substS'-i≥ i σ (gdd gst) = gdd (stack-sim-substG'-i≥ i σ gst)
stack-sim-substS'-i≥ i σ (rec gst) = rec (stack-sim-substG'-i≥ (suc i) σ gst)
stack-sim-substS'-i≥ 0F σ (var x)
  with get'Sn x σ
... | σ' , y = y
stack-sim-substS'-i≥ (suc i) σ (var 0F) = var 0F
stack-sim-substS'-i≥ (suc i) σ (var (suc x)) = weaken1S (stack-sim-substS'-i≥ i σ (var x))

stack-sim-substG'-i≥ i σ g = {!!}

stack-sim-substT'-i≥ i σ t = {!!}

-- substitute stack'
stack-sim-substS' : Stack'Sn n m → SType m → SType n
stack-sim-substG' : Stack'Sn n m → GType m → GType n
stack-sim-substT' : Stack'Sn n m → Type m → Type n

stack-sim-substS' σ (gdd gst) = gdd (stack-sim-substG' σ gst)
stack-sim-substS'{n}{m} σ (rec gst) = rec (stack-sim-substG'-i≥ 1F σ gst)
stack-sim-substS' σ (var x)
  with get'Sn x σ
... | σ' , s = s

stack-sim-substG' σ (transmit d t s) = transmit d (stack-sim-substT' σ t) (stack-sim-substS' σ s)
stack-sim-substG' σ (choice d m alt) = choice d m (λ x → stack-sim-substS' σ (alt x))
stack-sim-substG' σ end = end

stack-sim-substT' σ TUnit = TUnit
stack-sim-substT' σ TInt = TInt
stack-sim-substT' σ (TPair t t₁) = TPair (stack-sim-substT' σ t) (stack-sim-substT' σ t₁)
stack-sim-substT' σ (TChan x) = TChan (stack-sim-substS' σ x)

stack-sim-substS'-top-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → SType (n + m) → SType (n + toℕ i)
stack-sim-substG'-top-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → GType (n + m) → GType (n + toℕ i)
stack-sim-substT'-top-i≥ : (i : Fin (suc m)) → Stack'Sn n (m ∸ toℕ i) → Type (n + m) → Type (n + toℕ i)

stack-sim-substS'-top-i≥ i σ (gdd gst) = {!!}
stack-sim-substS'-top-i≥ i σ (rec gst) = rec (stack-sim-substG'-top-i≥ (suc i) σ gst)
stack-sim-substS'-top-i≥ i σ (var x) = {!!}

-- substitute top variables from stack'
stack-sim-substS'-top : Stack'Sn n m → SType (n + m) → SType n
stack-sim-substG'-top : Stack'Sn n m → GType (n + m) → GType n
stack-sim-substT'-top : Stack'Sn n m → Type (n + m) → Type n

stack-sim-substS'-top σ (gdd gst) = gdd (stack-sim-substG'-top σ gst)
stack-sim-substS'-top{n}{m} σ (rec gst) = rec (stack-sim-substG'-top-i≥ 1F σ gst)
stack-sim-substS'-top σ (var x) = {!!}


-- Transform Stack of STypes to Stack of closed STypes by substitution 
-- ⟪ ε , SType 0 , SType 1               , SType 2                                            , ⋯ ⟫
-- ⟪ ε , SType 0 , SType 1 [0F ↦ SType 0], SType 2 [0F ↦ SType 0, 1F ↦ SType 1 [0F ↦ SType 0]], ⋯ ⟫
-- ⟪ ε , SType 0 , SType 0               , SType 0                                            , ⋯ ⟫
stack-transform : StackS n → StackS0 n
stack-transform ε = ε
stack-transform ⟪ σ , x ⟫
  with stack-transform σ
... | σ' = ⟪ σ' , (stack-sim-substS σ' x) ⟫

stack-transform' : Stack'S n m → Stack'Sn n m
stack-transform' ε = ε
stack-transform'{n} ⟪ σ , x ⟫
  with stack-transform' σ
... | σ' = ⟪ σ' , stack-sim-substS'-top σ' x  ⟫

stack-cat : Stack n → Stack' n m → Stack (n + m)
stack-cat σ ε = σ
stack-cat σ ⟪ σ' , x ⟫ = ⟪ (stack-cat σ σ') , x ⟫

----------------------------------------------------------------------

-- Message closure
mclS : (σ : StackS n) → SType n → MClSType n
mclG : (σ : StackS n) → GType n → MClGType n
mclT : (σ : StackS n) → Type n → MClType n

mclS σ (gdd gst) = tgdd (mclG σ gst)
mclS σ (rec gst) = trec (mclG ⟪ σ , (rec gst) ⟫ gst)
mclS σ (var x) = tvar x

mclG σ (transmit d t s) = ttransmit d (mclT σ t) (mclS σ s)
mclG σ (choice d m alt) = tchoice d m (λ x → mclS σ (alt x))
mclG σ end = end

mclT σ TUnit = MClTUnit
mclT σ TInt = MClTInt
mclT σ (TPair t t₁) = MClTPair (mclT σ t) (mclT σ t₁)
mclT σ (TChan x) = MClTChan (stack-sim-substS (stack-transform σ) x)

----------------------------------------------------------------------

-- Any mcl type is a normal type with weakening
mcl2indS : MClSType n → SType n
mcl2indG : MClGType n → GType n
mcl2indT : MClType n → Type n

mcl2indS (tgdd tgst) = gdd (mcl2indG tgst)
mcl2indS (trec tgst) = rec (mcl2indG tgst)
mcl2indS (tvar x) = var x

mcl2indG (ttransmit d t s) = transmit d (mcl2indT t) (mcl2indS s)
mcl2indG (tchoice d m alt) = choice d m (λ x → mcl2indS (alt x))
mcl2indG end = end

mcl2indT MClTUnit = TUnit
mcl2indT MClTInt = TInt
mcl2indT (MClTPair t t₁) = TPair (mcl2indT t) (mcl2indT t₁)
mcl2indT{n} (MClTChan x) = TChan (weakenS n x)

----------------------------------------------------------------------

stack2StackS : Stack n → StackS n
stack2StackS ε = ε
stack2StackS ⟪ σ , x ⟫ = ⟪ (stack2StackS σ) , (rec x) ⟫

stackMCl2Stack : StackMCl n → Stack n
stackMCl2Stack ε = ε
stackMCl2Stack ⟪ σ , x ⟫ = ⟪ (stackMCl2Stack σ) , (mcl2indG x) ⟫

stackMCl2StackS : StackMCl n → StackS n
stackMCl2StackS ε = ε
stackMCl2StackS ⟪ σ , x ⟫ = ⟪ (stackMCl2StackS σ) , (rec (mcl2indG x)) ⟫

stack2StackMCl : Stack n → StackMCl n
stack2StackMCl ε = ε
stack2StackMCl ⟪ σ , x ⟫ = ⟪ (stack2StackMCl σ) , (mclG ⟪ stack2StackS σ , rec x ⟫ x) ⟫

stack2Stack' : Stack n → Stack' 0 n
stack2Stack' ε = ε
stack2Stack' ⟪ σ , x ⟫ = ⟪ stack2Stack' σ , x ⟫

stack'2Stack'S : Stack' n m → Stack'S n m
stack'2Stack'S ε = ε
stack'2Stack'S ⟪ σ , x ⟫ = ⟪ (stack'2Stack'S σ) , (rec x) ⟫

----------------------------------------------------------------------

naive-dualS : SType n → SType n
naive-dualG : GType n → GType n
naive-dualT : Type n → Type n

naive-dualS (gdd gst) = gdd (naive-dualG gst)
naive-dualS (rec gst) = rec (naive-dualG gst)
naive-dualS (var x) = var x

naive-dualG (transmit d t s) = transmit (dual-dir d) (naive-dualT t) (naive-dualS s)
naive-dualG (choice d m alt) = choice (dual-dir d) m (λ x → naive-dualS (alt x))
naive-dualG end = end

naive-dualT TUnit = TUnit
naive-dualT TInt = TInt
naive-dualT (TPair t t₁) = TPair (naive-dualT t) (naive-dualT t₁)
naive-dualT (TChan x) = TChan (naive-dualS x)

naive-dualSt : MClSType n → MClSType n
naive-dualGt : MClGType n → MClGType n
naive-dualTt : MClType n → MClType n

naive-dualSt (tgdd tgst) = tgdd (naive-dualGt tgst)
naive-dualSt (trec tgst) = trec (naive-dualGt tgst)
naive-dualSt (tvar x) = tvar x

naive-dualGt (ttransmit d t s) = ttransmit (dual-dir d) (naive-dualTt t) (naive-dualSt s)
naive-dualGt (tchoice d m alt) = tchoice (dual-dir d) m (λ x → naive-dualSt (alt x))
naive-dualGt end = end

naive-dualTt MClTUnit = MClTUnit
naive-dualTt MClTInt = MClTInt
naive-dualTt (MClTPair t t₁) = MClTPair (naive-dualTt t) (naive-dualTt t₁)
naive-dualTt (MClTChan x) = MClTChan (naive-dualS x)

----------------------------------------------------------------------

dualS : (σ : StackS n) → SType n → MClSType n
dualG : (σ : StackS n) → GType n → MClGType n
dualT : (σ : StackS n) → Type n → MClType n

dualS σ (gdd gst) = tgdd (dualG σ gst)
dualS σ (rec gst) = trec (dualG ⟪ σ , (rec gst) ⟫ gst)
dualS σ (var x)   = (tvar x)

dualG{n} σ (transmit d t s) = ttransmit (dual-dir d) (dualT σ t) (dualS σ s)
dualG σ (choice d m alt) = tchoice (dual-dir d) m ((dualS σ) ∘ alt)
dualG σ end = end

dualT σ TUnit = MClTUnit
dualT σ TInt = MClTInt
dualT σ (TPair t t₁) = MClTPair (dualT σ t) (dualT σ t₁)
dualT σ (TChan x) = MClTChan (stack-sim-substS (stack-transform σ) x)

module sanity-check where
  -- μx.!x.x → μx.?(μx.!x.x).x
  S : SType 0
  S = rec (transmit SND (TChan (var 0F)) (var 0F))
  DS = rec (transmit RCV (weaken1T (TChan S)) (var 0F))

  _ : mclS ε DS ≡ dualS ε S
  _ = refl

  -- μx.!x.!x.x → μx.?(μx.!x.!x.x).?(μx.!x.!x.x).x
  S' : SType 0
  S' = rec (transmit SND (TChan (var 0F)) (gdd ((transmit SND (TChan (var 0F)) (var 0F)))))
  DS' =  rec (transmit RCV (weaken1T (TChan S')) (gdd ((transmit RCV (weaken1T (TChan S')) (var 0F)))))

  _ : mclS ε DS' ≡ dualS ε S'
  _ = refl

  -- μx.!x.(μy.!y.y) → μx.?(μx.!x.(μy.!y.y)).(μy.?(μy.!y.y).y)
  S'' : SType 0
  S'' = rec (transmit SND (TChan (var 0F)) (rec (transmit SND (TChan (var 0F)) (var 0F))))
  DS'' = rec (transmit RCV (weaken1T (TChan S'')) (weaken1S DS))

  _ : mclS ε DS'' ≡ dualS ε S''
  _ = refl

----------------------------------------------------------------------


open import DualCoinductive hiding (n ; m)

_≈_ = COI._≈_
_≈'_ = COI._≈'_
_≈ᵗ_ = COI._≈ᵗ_

-- IND to Coinductive using two stacks
ind2coiS' : (i : Fin n) → Stack (n ∸ toℕ i) → Stack' (n ∸ toℕ i) (toℕ i) → IND.SType n → COI.SType
ind2coiG' : (i : Fin n) → Stack (n ∸ toℕ i) → Stack' (n ∸ toℕ i) (toℕ i) → IND.GType n → COI.STypeF COI.SType
ind2coiT' : (i : Fin n) → Stack (n ∸ toℕ i) → Stack' (n ∸ toℕ i) (toℕ i) → IND.Type n → COI.Type

COI.SType.force (ind2coiS' i σ σ' (gdd gst)) = ind2coiG' i σ σ' gst
COI.SType.force (ind2coiS'{n} i σ σ' (rec gst)) = ind2coiG' (suc i) σ ⟪ σ' , {!gst!} ⟫ gst
-- Problematic line:
-- COI.SType.force (ind2coiS'{n} i σ σ' (rec gst)) rewrite (sym (suc[n∸suc[toℕi]+toℕi]≡n{n}{i})) = ?
COI.SType.force (ind2coiS' i σ σ' (var x)) = {!!}
 
-- IND to Coinductive
ind2coiS : Stack n → IND.SType n → COI.SType
ind2coiG : Stack n → IND.GType n → COI.STypeF COI.SType
ind2coiT : Stack n → IND.Type n → COI.Type

ind2coiT σ TUnit = COI.TUnit
ind2coiT σ TInt = COI.TInt
ind2coiT σ (TPair t t₁) = COI.TPair (ind2coiT σ t) (ind2coiT σ t₁)
ind2coiT σ (TChan x) = COI.TChan (ind2coiS σ x)

COI.SType.force (ind2coiS σ (gdd gst)) = ind2coiG σ gst
COI.SType.force (ind2coiS σ (rec gst)) = ind2coiG ⟪ σ , gst ⟫ gst
COI.SType.force (ind2coiS{n} σ (var x))
  with get x σ
... | σ' , gxs rewrite (n∸x≡suc[n∸sucx]{n}{toℕ x} toℕx<n) = ind2coiG ⟪ σ' , gxs ⟫ gxs 

ind2coiG σ (transmit d t s) = COI.transmit d (ind2coiT σ t) (ind2coiS σ s)
ind2coiG σ (choice d m alt) = COI.choice d m (λ x → ind2coiS σ (alt x))
ind2coiG σ end = COI.end

-- Equivalence of IND to COI with one stack and IND to COI with two stacks

ind2coi≈ind2coi'-S : (i : Fin n) (σ : Stack (suc n)) (s : IND.SType (suc n))
  → ind2coiS' 0F σ ε s ≈ ind2coiS σ s 

COI.Equiv.force (ind2coi≈ind2coi'-S i σ (gdd gst)) = {!!}
COI.Equiv.force (ind2coi≈ind2coi'-S i σ (rec gst)) = {!!}
COI.Equiv.force (ind2coi≈ind2coi'-S i σ (var x)) = {!!}


-- Message closure to Coinductive
mcl2coiT : StackMCl n → MClType n → COI.Type
mcl2coiS : StackMCl n → MClSType n → COI.SType
mcl2coiG : StackMCl n → MClGType n → COI.STypeF COI.SType

mcl2coiT σ MClTUnit = COI.TUnit
mcl2coiT σ MClTInt = COI.TInt
mcl2coiT σ (MClTPair t t₁) = COI.TPair (mcl2coiT σ t) (mcl2coiT σ t₁)
mcl2coiT σ (MClTChan s) = COI.TChan (ind2coiS ε s)

COI.SType.force (mcl2coiS σ (tgdd g)) = mcl2coiG σ g
COI.SType.force (mcl2coiS σ (trec g)) = mcl2coiG ⟪ σ , g ⟫ g
COI.SType.force (mcl2coiS{n} σ (tvar x))
  with getMCl x σ
... | σ' , gxs rewrite (n∸x≡suc[n∸sucx]{n}{toℕ x} toℕx<n) = mcl2coiG ⟪ σ' , gxs ⟫ gxs 

mcl2coiG σ (ttransmit d t s) = COI.transmit d (mcl2coiT σ t) (mcl2coiS σ s)
mcl2coiG σ (tchoice d m alt) = COI.choice d m (mcl2coiS σ ∘ alt)
mcl2coiG σ end = COI.end

----------------------------------------------------------------------

-- Agda does not recognize this even though rewrite rule was defined
rewrfixS : {n : ℕ} {i : Fin n} → SType (suc (n ∸ suc (toℕ i) + toℕ i)) → SType n
rewrfixG : {n : ℕ} {i : Fin n} → GType (suc (n ∸ suc (toℕ i) + toℕ i)) → GType n
rewrfixS{n}{i} s rewrite (suc[n∸suc[toℕi]+toℕi]≡n{n}{i}) = s
rewrfixG{n}{i} g rewrite (suc[n∸suc[toℕi]+toℕi]≡n{n}{i}) = g

stack-unfoldS'-i : (i : Fin n)  (σ : Stack n) (s : IND.SType (suc (n ∸ suc (toℕ i) + toℕ i)))
  → ind2coiS (proj₁ (stack-split i σ)) (stack-sim-substS'-top (stack-transform' (stack'2Stack'S (proj₂ (stack-split i σ)))) s) ≈ ind2coiS' i (proj₁ (stack-split i σ)) (proj₂ (stack-split i σ)) (rewrfixS{n}{i} s)


{-
-- won't work for the same reason as below
stack-unfoldS-i : (i : Fin n) (σ : Stack n) (s : IND.SType (suc (n ∸ suc (toℕ i) + toℕ i)))
  → ind2coiS (proj₁ (stack-split i σ)) (stack-sim-substS'-top (stack-transform' (stack'2Stack'S (proj₂ (stack-split i σ)))) s) ≈ ind2coiS σ (rewrfixS{n}{i} s)
stack-unfoldG-i : (i : Fin n) (σ : Stack n) (g : IND.GType (suc (n ∸ suc (toℕ i) + toℕ i)))
  → ind2coiG (proj₁ (stack-split i σ)) (stack-sim-substG'-top (stack-transform' (stack'2Stack'S (proj₂ (stack-split i σ)))) g) ≈' ind2coiG σ (rewrfixG{n}{i} g)

COI.Equiv.force (stack-unfoldS-i i σ (gdd gst)) = {!!}
COI.Equiv.force (stack-unfoldS-i{n} i σ (rec gst)) = {!stack-unfoldG-i (suc i) ? gst!}
COI.Equiv.force (stack-unfoldS-i i σ (var x)) = {!!}

-- won't work. rec case adds something to σ on the left side, but something at the end of (stack-cat σ σ') on the right side.

stack-unfoldS' : (σ : Stack n) (σ' : Stack' n m) (s : IND.SType (n + m)) →
  ind2coiS σ (stack-sim-substS'-top (stack-transform' (stack'2Stack'S σ')) s) ≈ ind2coiS (stack-cat σ σ') s
stack-unfoldG' : (σ : Stack n) (σ' : Stack' n m) (g : IND.GType (n + m)) →
  ind2coiG σ (stack-sim-substG'-top (stack-transform' (stack'2Stack'S σ')) g) ≈' ind2coiG (stack-cat σ σ') g

COI.Equiv.force (stack-unfoldS' σ σ' (gdd gst)) = {!!}
COI.Equiv.force (stack-unfoldS'{n}{m} σ σ' (rec gst)) = {!stack-unfoldG'{suc n}{m} ⟪ σ , stack-sim-substG'-top-i≥ 1F (stack-transform' (stack'2Stack'S σ')) gst ⟫ (weaken1-Stack' 0F σ') gst!}
COI.Equiv.force (stack-unfoldS' σ σ' (var x)) = {!!}
-}

----------------------------------------------------------------------

-- proof idea for var case:
-- mcl2coiS (stack2StackMCl σ) (tvar x)
-------- getMCl x (stack2StackMCl σ) = σ' , g
-- => mcl2coiG ⟪ σ' , g ⟫ g
-------- getMCl x (stack2StackMCl σ) = (stack2StackMCl (get x σ).1 , mclG ⟪ stack2StackS (get x σ).1 , rec (get x σ).2 ⟫ (get x σ).2
-- => mcl2coiG ⟪ (stack2StackMCl (get x σ).1 , mclG ⟪ stack2StackS (get x σ).1 , rec (get x σ).2 ⟫ (get x σ).2 ⟫ (mclG ⟪ stack2StackS (get x σ).1 , rec (get x σ).2 ⟫ (get x σ).2)
------- which by definition of stack2StackMCl and stack2StackS is equivalent to
-- = mcl2coiG (stack2StackMCl ⟪ (get x σ).1 , (get x σ).2 ⟫) (mclG (stack2StackS ⟪ (get x σ).1 , (get x σ).2 ⟫) g)
------- which, by mcl-equiv-G
-- ≈' ind2coiG ⟪ (get x σ).1 , (get x σ).2 ⟫ (get x σ).2
-- = ind2coiG σ (var x)

getMCl-get : (x : Fin n) (σ : Stack n)
  → getMCl x (stack2StackMCl σ) ≡ (stack2StackMCl (proj₁ (get x σ)) , mclG ⟪ stack2StackS (proj₁ (get x σ)) , rec (proj₂ (get x σ)) ⟫  (proj₂ (get x σ)))
getMCl-get 0F ⟪ σ , x ⟫ = refl
getMCl-get (suc x) ⟪ σ , x₁ ⟫ = getMCl-get x σ

----------------------------------------------------------------------

mcl-equiv-S : (σ : Stack n) (s : IND.SType n) →
  mcl2coiS (stack2StackMCl σ) (mclS (stack2StackS σ) s) ≈ ind2coiS σ s
mcl-equiv-G : (σ : Stack n) (g : IND.GType n) →
  mcl2coiG (stack2StackMCl σ) (mclG (stack2StackS σ) g) ≈' ind2coiG σ g
mcl-equiv-T : (σ : Stack n) (t : IND.Type n) →
  mcl2coiT (stack2StackMCl σ) (mclT (stack2StackS σ) t) ≈ᵗ ind2coiT σ t

COI.Equiv.force (mcl-equiv-S σ (gdd gst)) = mcl-equiv-G σ gst
COI.Equiv.force (mcl-equiv-S σ (rec gst)) = mcl-equiv-G ⟪ σ , gst ⟫ gst
COI.Equiv.force (mcl-equiv-S{n} σ (var x))
  rewrite (getMCl-get x σ)
  with (proj₁ (get x σ)) | (proj₂ (get x σ))
... | σ' | g  rewrite (n∸x≡suc[n∸sucx]{n}{toℕ x} toℕx<n) = mcl-equiv-G ⟪ σ' , g ⟫ g

mcl-equiv-G σ (transmit d t s) = COI.eq-transmit d (mcl-equiv-T σ t) (mcl-equiv-S σ s)
mcl-equiv-G σ (choice d m alt) = COI.eq-choice d (λ i → mcl-equiv-S σ (alt i))
mcl-equiv-G σ end = COI.eq-end

mcl-equiv-T σ TUnit = COI.eq-unit
mcl-equiv-T σ TInt = COI.eq-int
mcl-equiv-T σ (TPair t t₁) = COI.eq-pair (mcl-equiv-T σ t) (mcl-equiv-T σ t₁)
mcl-equiv-T{n} σ (TChan x) = COI.eq-chan {! !}


-- naive-mcl-dual : (σ : StackMCl n) (s : IND.SType n) →
--  mcl2coiS σ (naive-dualSt (mclS (stackTail2StackS σ) s)) ≈ mcl2coiS σ (dualS (stackTail2StackS σ) s)
