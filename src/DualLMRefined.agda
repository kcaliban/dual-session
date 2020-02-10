{-# OPTIONS --rewriting #-}
module DualLMRefined where

open import Data.Bool
open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
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

  TType = Type

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

  exts : {j : ℕ} → (Fin n → SType j) → (Fin (suc n) → SType (suc j))
  exts {j} map 0F      = var zero
  exts {j} map (suc i) = weaken1S (map i)

  ----------------------------------------------------------------------

  -- Simultaneous substitution

  sim-substS : SType n → (j : Fin (suc n)) → (i : Fin n → SType (toℕ j)) → SType (toℕ j)
  sim-substG : GType n → (j : Fin (suc n)) → (i : Fin n → SType (toℕ j)) → GType (toℕ j)
  sim-substT : Type n → (j : Fin (suc n)) → (i : Fin n → SType (toℕ j)) → Type (toℕ j)

  sim-substS (gdd gst) j ϱ = gdd (sim-substG gst j ϱ)
  sim-substS (rec gst) j ϱ = rec (sim-substG gst (suc j) (exts {j = toℕ j} ϱ)) 
  sim-substS (var x) j ϱ   = ϱ x

  sim-substG (transmit d t s) j ϱ = transmit d (sim-substT t j ϱ) (sim-substS s j ϱ) 
  sim-substG (choice d m alt) j ϱ = choice d m (λ x → sim-substS (alt x) j ϱ)
  sim-substG end j ϱ              = end

  sim-substT TUnit j ϱ        = TUnit
  sim-substT TInt j ϱ         = TInt
  sim-substT (TPair t t₁) j ϱ = TPair (sim-substT t j ϱ) (sim-substT t₁ j ϱ)
  sim-substT (TChan x) j ϱ    = TChan (sim-substS x j ϱ)

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

  -- Single substitution with SType (suc n)

  st-substS'' : Fin (suc n) → SType (suc n) → SType (suc n) → SType (suc n)
  st-substG'' : Fin (suc n) → SType (suc n) → GType (suc n) → GType (suc n) 
  st-substT'' : Fin (suc n) → SType (suc n) → Type (suc n) → Type (suc n)

  st-substS'' i st (gdd gst) = gdd (st-substG'' i st gst)
  st-substS'' i st (rec gst) = rec (st-substG'' (suc i) (weaken1S st) gst)
  st-substS'' i st (var x)
    with compare x i
  st-substS'' i st (var .(inject least)) | less .i least = var (inject least)
  st-substS'' .x st (var x) | equal .x = st
  st-substS'' .(inject least) st (var (suc x)) | greater .(suc x) least = var (suc x)

  st-substG'' i st (transmit d t s) = transmit d (st-substT'' i st t) (st-substS'' i st s)
  st-substG'' i st (choice d m alt) = choice d m (λ j → st-substS'' i st (alt j))
  st-substG'' i st end = end

  st-substT'' i st TUnit = TUnit
  st-substT'' i st TInt  = TInt
  st-substT'' i st (TPair ty ty₁) = TPair (st-substT'' i st ty) (st-substT'' i st ty₁)
  st-substT'' i st (TChan s) = TChan (st-substS'' i st s)

  -- Single substitution limited to TChan

  t-substS : Fin (suc n) → SType (suc n) → SType (suc n) → SType (suc n)
  t-substG : Fin (suc n) → SType (suc n) → GType (suc n) → GType (suc n)
  t-substT : Fin (suc n) → SType (suc n) → Type (suc n) → Type (suc n)

  t-substS i s (gdd gst) = gdd (t-substG i s gst)
  t-substS i s (rec gst) = rec (t-substG (suc i) (weaken1S s) gst)
  t-substS i s (var x) = var x

  t-substG i s (transmit d t s₁) = transmit d (t-substT i s t) (t-substS i s s₁)
  t-substG i s (choice d m alt) = choice d m (λ x → t-substS i s (alt x))
  t-substG i s end = end

  t-substT i s TUnit = TUnit
  t-substT i s TInt = TInt
  t-substT i s (TPair t t₁) = TPair (t-substT i s t) (t-substT i s t₁)
  t-substT i s (TChan x) = TChan (st-substS'' i s x)

  -- Simultaneous substitution limited to TChan

  t-simsubstS : (Fin n → SType n) → SType n → SType n
  t-simsubstG : (Fin n → SType n) → GType n → GType n
  t-simsubstT : (Fin n → SType n) → Type n → Type n

  t-simsubstS ϱ (gdd gst) = gdd (t-simsubstG ϱ gst)
  t-simsubstS ϱ (rec gst) = rec (t-simsubstG (exts ϱ) gst)
  t-simsubstS ϱ (var x) = var x

  t-simsubstG ϱ (transmit d t s) = transmit d (t-simsubstT ϱ t) (t-simsubstS ϱ s)
  t-simsubstG ϱ (choice d m alt) = choice d m (λ x → t-simsubstS ϱ (alt x))
  t-simsubstG ϱ end = end

  t-simsubstT ϱ TUnit = TUnit
  t-simsubstT ϱ TInt = TInt
  t-simsubstT ϱ (TPair t t₁) = TPair (t-simsubstT ϱ t) (t-simsubstT ϱ t₁)
  t-simsubstT{n} ϱ (TChan x) = TChan (sim-substS x (fromℕ n) ϱ)

  ----------------------------------------------------------------------
  ----------------------------------------------------------------------

  dualS' : (σ : SType n → SType n) → SType n → SType n
  dualG' : (σ : SType n → SType n) → GType n → GType n
  dualT' : (σ : SType n → SType n) → Type n → Type n

  dualS' σ (gdd gst) = gdd (dualG' σ gst)
  dualS'{n} σ (rec gst) = rec (dualG' (weaken1S ∘ σ ∘ (st-substS'{n} 0F (rec gst))) gst)
  dualS' σ (var x)   = (var x)

  dualG' σ (transmit d t s) = transmit (dual-dir d) (dualT' σ t) (dualS' σ s)
  dualG' σ (choice d m alt) = choice (dual-dir d) m ((dualS' σ) ∘ alt)
  dualG' σ end = end

  dualT' σ TUnit = TUnit
  dualT' σ TInt = TInt
  dualT' σ (TPair t t₁) = TPair (dualT' σ t) (dualT' σ t₁)
  dualT' σ (TChan x) = TChan (σ x)

  dualS : SType n → SType n
  dualG : GType n → GType n

  dualS s = dualS' (λ x → x) s 
  dualG g = dualG' (λ x → x) g

  ----------------------------------------------------------------------

  module CheckDual where
    -- S    = μx.!x.x
    S : SType 0
    S = rec (transmit SND (TChan (var 0F)) (var 0F))

    -- D(S) = μx.?(μx.!x.x).x
    DS : SType 0
    DS = rec (transmit RCV (weaken1T (TChan S)) (var 0F))

    _ : DS ≡ dualS S
    _ = refl

    -- S' = μx.!x.!x.x
    S' : SType 0
    S' = rec (transmit SND (TChan (var 0F)) (gdd ((transmit SND (TChan (var 0F)) (var 0F)))))

    -- D(S') = μx.?(μx.!x.!x.x).?(μx.!x.!x.x).x
    DS' : SType 0
    DS' =  rec (transmit RCV (weaken1T (TChan S')) (gdd ((transmit RCV (weaken1T (TChan S')) (var 0F)))))

    _ : DS' ≡ dualS S'
    _ = refl

    -- S'' = μx.!x.(μy.!y.y)
    S'' : SType 0
    S'' = rec (transmit SND (TChan (var 0F)) (rec (transmit SND (TChan (var 0F)) (var 0F))))

    -- D(S'') = μx.?(μx.!x.(μy.!y.y)).(μy.?(μy.!y.y).y)
    DS'' = rec (transmit RCV (weaken1T (TChan S'')) (weaken1S DS))

    _ : DS'' ≡ dualS S''
    _ = refl

  ----------------------------------------------------------------------

-- Proof of equivalence to coinductive definition
open import DualCoinductive hiding (n)
open COI
open IND

ind2coiT : IND.Type 0 → COI.Type
ind2coiS : IND.SType 0 → COI.SType
ind2coiG : IND.GType 0 → COI.STypeF COI.SType

ind2coiT TUnit = TUnit
ind2coiT TInt = TInt
ind2coiT (TPair it it₁) = TPair (ind2coiT it) (ind2coiT it₁)
ind2coiT (TChan st) = TChan (ind2coiS st)

ind2coiG (transmit d t ist) = transmit d (ind2coiT t) (ind2coiS ist)
ind2coiG (choice d m alt) = choice d m (ind2coiS ∘ alt)
ind2coiG end = end

SType.force (ind2coiS (gdd gst)) = ind2coiG gst
SType.force (ind2coiS (rec gst)) = ind2coiG (st-substG gst zero (rec gst))

----------------------------------------------------------------------

dual-compatible-trivialT : (t : IND.Type n) → dualT' (λ x → x) t ≡ t
dual-compatible-trivialT TUnit = refl
dual-compatible-trivialT TInt = refl
dual-compatible-trivialT (TPair t t₁) = cong₂ (TPair) (dual-compatible-trivialT t) (dual-compatible-trivialT t₁)
dual-compatible-trivialT (TChan x) = refl

----------------------------------------------------------------------

dual-compatibleS : (ist : IND.SType 0) →
  COI.dual (ind2coiS ist) ≈ ind2coiS (IND.dualS ist)
dual-compatibleG : (gst : IND.GType 0) →
  COI.dualF (ind2coiG gst) ≈' ind2coiG (IND.dualG gst)

Equiv.force (dual-compatibleS (gdd gst)) = dual-compatibleG gst
Equiv.force (dual-compatibleS (rec gst)) = {!!}

dual-compatibleG (transmit d t s) rewrite (dual-compatible-trivialT t) = eq-transmit (dual-dir d) ≈ᵗ-refl (dual-compatibleS s)
dual-compatibleG (choice d m alt) = eq-choice (dual-dir d) (dual-compatibleS ∘ alt)
dual-compatibleG end = eq-end

