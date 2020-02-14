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

  toℕx≤n : {n : ℕ} {x : Fin n} → Data.Nat._≤_ (toℕ x) n
  toℕx≤n {suc n} {0F} = z≤n
  toℕx≤n {suc n} {suc x} = s≤s toℕx≤n
  
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

  ----------------------------------------------------------------------

open IND
open import DualTail hiding (dualS ; dualG ; dual-tailS ; dual-tailG)

data Stack' : ℕ → Set where
  ε : Stack' 0
  ⟪_,_⟫ : Stack' n → IND.GType (suc n) → Stack' (suc n)

get' : {n : ℕ} → (i : Fin n) → Stack' n → Stack' (n ∸ (suc (toℕ i))) × IND.GType (n ∸ (toℕ i))
get' {suc n} 0F ⟪ σ , x ⟫ = σ , x
get' {suc n} (suc i) ⟪ σ , x ⟫ = get' i σ

{-
stack-substG : Stack n → IND.GType n → IND.GType 0F
stack-substT : Stack n → IND.Type n → IND.Type 0F
stack-substS : Stack n → IND.SType n → IND.SType 0F

stack-substS σ (gdd gst) = gdd (stack-substG σ gst)
stack-substS{n} σ (rec gst) = rec (weaken1G (stack-substG ⟪ σ , gst ⟫ gst))
stack-substS{n} σ (var x)
  with get x σ
... | σ' , xt = {!!} 
-- stack-substS{n} σ (var x)
--   with get x σ | weakenG{n ∸ toℕ x} (suc (toℕ x))
-- ... | σ' , xt | w rewrite (n∸x+x≡n{n}{toℕ x} toℕx≤n) = rec (w xt)

stack-substG σ (transmit d t s) = transmit d (stack-substT σ t) (stack-substS σ s)
stack-substG σ (choice d m alt) = choice d m (λ x → stack-substS σ (alt x))
stack-substG σ end = end

stack-substT σ TUnit = TUnit
stack-substT σ TInt = TInt
stack-substT σ (TPair t t₁) = TPair (stack-substT σ t) (stack-substT σ t₁)
stack-substT σ (TChan x) = TChan (stack-substS σ x)

-}

dualS : (σ : Stack' n) → IND.SType n → DualTail.SType n
dualG : (σ : Stack' n) → IND.GType n → DualTail.GType n
dualT : (σ : Stack' n) → IND.Type n → DualTail.Type

dualS σ (gdd gst) = gdd (dualG σ gst)
dualS σ (rec gst) = rec (dualG ⟪ σ , gst ⟫ gst)
dualS σ (var x)   = (var x)

dualG σ (transmit d t s) = transmit (dual-dir d) (dualT σ t) (dualS σ s)
dualG σ (choice d m alt) = choice (dual-dir d) m ((dualS σ) ∘ alt)
dualG σ end = end

dualT σ TUnit = TUnit
dualT σ TInt = TInt
dualT σ (TPair t t₁) = TPair (dualT σ t) (dualT σ t₁)
dualT σ (TChan x) = TChan {!stack-substS σ x!}

----------------------------------------------------------------------

open import DualCoinductive hiding (n)


tail2coiT' : Stack' n → IND.Type n → COI.Type
tail2coiS' : Stack' n → IND.SType n → COI.SType
tail2coiG' : Stack' n → IND.GType n → COI.STypeF COI.SType

tail2coiT' σ TUnit = COI.TUnit
tail2coiT' σ TInt = COI.TInt
tail2coiT' σ (TPair t t₁) = COI.TPair (tail2coiT' σ t) (tail2coiT' σ t₁)
tail2coiT' σ (TChan s) = COI.TChan (tail2coiS' σ s)

COI.SType.force (tail2coiS' σ (gdd g)) = tail2coiG' σ g
COI.SType.force (tail2coiS' σ (rec g)) = tail2coiG' ⟪ σ , g ⟫ g
COI.SType.force (tail2coiS' σ (var x)) = {!!}
{-  with get' x σ
... | σ' , gxs = tail2coiG ⟪ σ' , gxs ⟫ gxs -}

tail2coiG' σ (transmit d t s) = COI.transmit d (tail2coiT' σ t) (tail2coiS' σ s)
tail2coiG' σ (choice d m alt) = COI.choice d m (tail2coiS' σ ∘ alt)
tail2coiG' σ end = COI.end



dual-tailS : (σ : Stack' n) (s : IND.SType n) →
  COI.dual (tail2coiS' σ s) ≈ tail2coiS {!!} (dualS σ s)
dual-tailG : (σ : Stack' n) (g : IND.GType n) →
  COI.dualF (tail2coiG' σ g) ≈' tail2coiG {!!} (dualG σ g)
  

{-
module CheckDual where
  -- S    = μx.!x.x
  S : SType 0
  S = rec (transmit SND (TChan (var 0F)) (var 0F))

  -- D(S) = μx.?(μx.!x.x).x
  DS : SType 0
  DS = rec (transmit RCV (weaken1T (TChan S)) (var 0F))

  _ : DS ≡ dualS ε S
  _ = refl

  -- S' = μx.!x.!x.x
  S' : SType 0
  S' = rec (transmit SND (TChan (var 0F)) (gdd ((transmit SND (TChan (var 0F)) (var 0F)))))

  -- D(S') = μx.?(μx.!x.!x.x).?(μx.!x.!x.x).x
  DS' : SType 0
  DS' =  rec (transmit RCV (weaken1T (TChan S')) (gdd ((transmit RCV (weaken1T (TChan S')) (var 0F)))))

  _ : DS' ≡ dualS ε S'
  _ = refl

  -- S'' = μx.!x.(μy.!y.y)
  S'' : SType 0
  S'' = rec (transmit SND (TChan (var 0F)) (rec (transmit SND (TChan (var 0F)) (var 0F))))

  -- D(S'') = μx.?(μx.!x.(μy.!y.y)).(μy.?(μy.!y.y).y)
  DS'' = rec (transmit RCV (weaken1T (TChan S'')) (weaken1S DS))

  _ : DS'' ≡ dualS ε S''
  _ = refl
-}
