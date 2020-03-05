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

  mutual
    data TailType (n : ℕ) : Set where
      TailTUnit TailTInt : TailType n
      TailTPair : TailType n → TailType n → TailType n
      TailTChan : SType 0F → TailType n

    data TailSType (n : ℕ) : Set where
      tgdd : (tgst : TailGType n) → TailSType n
      trec : (tgst : TailGType (suc n)) → TailSType n
      tvar : (x : Fin n) → TailSType n

    data TailGType (n : ℕ) : Set where
      ttransmit : (d : Dir) (t : TailType n) (s : TailSType n) → TailGType n
      tchoice : (d : Dir) (m : ℕ) (alt : Fin m → TailSType n) → TailGType n
      end : TailGType n

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

data Stack : ℕ → Set where
  ε : Stack 0
  ⟪_,_⟫ : Stack n → IND.GType (suc n) → Stack (suc n)

data StackS : ℕ → Set where
  ε : StackS 0
  ⟪_,_⟫ : StackS n → IND.SType n → StackS (suc n)

data StackS0 : ℕ → Set where
  ε : StackS0 0
  ⟪_,_⟫ : StackS0 n → IND.SType 0F → StackS0 (suc n)

data StackTail : ℕ → Set where
  ε : StackTail 0
  ⟪_,_⟫ : StackTail n → IND.TailGType (suc n) → StackTail (suc n)

get : {n : ℕ} → (i : Fin n) → Stack n → Stack (n ∸ (suc (toℕ i))) × IND.GType (n ∸ (toℕ i))
get {suc n} 0F ⟪ σ , x ⟫ = σ , x
get {suc n} (suc i) ⟪ σ , x ⟫ = get i σ

getS : {n : ℕ} → (i : Fin n) → StackS n → StackS (n ∸ (suc (toℕ i))) × IND.SType (n ∸ (suc (toℕ i)))
getS {suc n} 0F ⟪ σ , x ⟫ = σ , x
getS {suc n} (suc i) ⟪ σ , x ⟫ = getS i σ

getS0 : {n : ℕ} → (i : Fin n) → StackS0 n → StackS0 (n ∸ (suc (toℕ i))) × IND.SType 0F
getS0 {suc n} 0F ⟪ σ , x ⟫ = σ , x
getS0 {suc n} (suc i) ⟪ σ , x ⟫ = getS0 i σ

getTail : {n : ℕ} → (i : Fin n) → StackTail n → StackTail (n ∸ (suc (toℕ i))) × IND.TailGType (n ∸ (toℕ i))
getTail {suc n} 0F ⟪ σ , x ⟫ = σ , x
getTail {suc n} (suc i) ⟪ σ , x ⟫ = getTail i σ

----------------------------------------------------------------------

-- substitute after index i, required for rec case
stack-sim-substS-i : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → SType n → SType (toℕ (suc i))
stack-sim-substG-i : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → GType n → GType (toℕ (suc i))
stack-sim-substT-i : (i : Fin n) → StackS0 (n ∸ (toℕ (suc i))) → Type n → Type (toℕ (suc i))

stack-sim-substS-i i σ (gdd gst) = gdd (stack-sim-substG-i i σ gst)
stack-sim-substS-i i σ (rec gst) = rec (stack-sim-substG-i (suc i) σ gst)
stack-sim-substS-i{suc n} 0F σ (var 0F) = var 0F
stack-sim-substS-i 0F σ (var (suc x))
  with getS0 x σ 
... | σ' , s = weaken1S s
stack-sim-substS-i (suc i) σ (var 0F) = var 0F
stack-sim-substS-i (suc i) σ (var (suc x)) = weaken1S (stack-sim-substS-i i σ (var x))

stack-sim-substG-i i σ (transmit d t s) = transmit d (stack-sim-substT-i i σ t) (stack-sim-substS-i i σ s)
stack-sim-substG-i i σ (choice d m alt) = choice d m (λ x → stack-sim-substS-i i σ (alt x))
stack-sim-substG-i i σ end = end

stack-sim-substT-i i σ TUnit = TUnit
stack-sim-substT-i i σ TInt = TInt
stack-sim-substT-i i σ (TPair t t₁) = TPair (stack-sim-substT-i i σ t) (stack-sim-substT-i i σ t₁)
stack-sim-substT-i i σ (TChan x) = TChan (stack-sim-substS-i i σ x)

-- substitute stack
stack-sim-substS : StackS0 n → SType n → SType 0F
stack-sim-substG : StackS0 n → GType n → GType 0F
stack-sim-substT : StackS0 n → Type n → Type 0F

stack-sim-substS σ (gdd gst) = gdd (stack-sim-substG σ gst)
stack-sim-substS σ (rec gst) = rec (stack-sim-substG-i 0F σ gst) -- Apply stack substitution to variables 1, ..., suc n; keep 0F; can't extend StackS0 since only SType 0F allowed
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

-- Transform Stack of STypes to Stack of closed STypes by substitution 
-- ⟪ ε , SType 0 , SType 1               , SType 2                                            , ⋯ ⟫
-- ⟪ ε , SType 0 , SType 1 [0F ↦ SType 0], SType 2 [0F ↦ SType 0, 1F ↦ SType 1 [0F ↦ SType 0]], ⋯ ⟫
-- ⟪ ε , SType 0 , SType 0               , SType 0                                            , ⋯ ⟫
stack-transform : StackS n → StackS0 n
stack-transform ε = ε
stack-transform ⟪ σ , x ⟫
  with stack-transform σ
... | σ' = ⟪ σ' , (stack-sim-substS σ' x) ⟫

----------------------------------------------------------------------

-- Message closure
mclS : (σ : StackS n) → SType n → TailSType n
mclG : (σ : StackS n) → GType n → TailGType n
mclT : (σ : StackS n) → Type n → TailType n

mclS σ (gdd gst) = tgdd (mclG σ gst)
mclS σ (rec gst) = trec (mclG ⟪ σ , (rec gst) ⟫ gst)
mclS σ (var x) = tvar x

mclG σ (transmit d t s) = ttransmit d (mclT σ t) (mclS σ s)
mclG σ (choice d m alt) = tchoice d m (λ x → mclS σ (alt x))
mclG σ end = end

mclT σ TUnit = TailTUnit
mclT σ TInt = TailTInt
mclT σ (TPair t t₁) = TailTPair (mclT σ t) (mclT σ t₁)
mclT σ (TChan x) = TailTChan (stack-sim-substS (stack-transform σ) x)

----------------------------------------------------------------------

-- Any tail type is a normal type with weakening
tail2noTailS : TailSType n → SType n
tail2noTailG : TailGType n → GType n
tail2noTailT : TailType n → Type n

tail2noTailS (tgdd tgst) = gdd (tail2noTailG tgst)
tail2noTailS (trec tgst) = rec (tail2noTailG tgst)
tail2noTailS (tvar x) = var x

tail2noTailG (ttransmit d t s) = transmit d (tail2noTailT t) (tail2noTailS s)
tail2noTailG (tchoice d m alt) = choice d m (λ x → tail2noTailS (alt x))
tail2noTailG end = end

tail2noTailT TailTUnit = TUnit
tail2noTailT TailTInt = TInt
tail2noTailT (TailTPair t t₁) = TPair (tail2noTailT t) (tail2noTailT t₁)
tail2noTailT{n} (TailTChan x) = TChan (weakenS n x)

----------------------------------------------------------------------

stack2StackS : Stack n → StackS n
stack2StackS ε = ε
stack2StackS ⟪ σ , x ⟫ = ⟪ (stack2StackS σ) , (rec x) ⟫

stackTail2Stack : StackTail n → Stack n
stackTail2Stack ε = ε
stackTail2Stack ⟪ σ , x ⟫ = ⟪ (stackTail2Stack σ) , (tail2noTailG x) ⟫

stackTail2StackS : StackTail n → StackS n
stackTail2StackS ε = ε
stackTail2StackS ⟪ σ , x ⟫ = ⟪ (stackTail2StackS σ) , (rec (tail2noTailG x)) ⟫

stack2StackTail : Stack n → StackTail n
stack2StackTail ε = ε
stack2StackTail ⟪ σ , x ⟫ = ⟪ (stack2StackTail σ) , (mclG ⟪ stack2StackS σ , rec x ⟫ x) ⟫

----------------------------------------------------------------------

-- proj₂ (getTail x (stack2StackTail σ)) ≡ mclG (stack2StackS σ) (get x σ)
getTail-get : (x : Fin n) (σ : Stack n)
  → getTail x (stack2StackTail σ) ≡ map stack2StackTail (mclG {!stack2StackS ⟪ (proj₁ (get x σ)) , (proj₂ (get x σ)) ⟫!}) (get x σ) 

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

naive-dualSt : TailSType n → TailSType n
naive-dualGt : TailGType n → TailGType n
naive-dualTt : TailType n → TailType n

naive-dualSt (tgdd tgst) = tgdd (naive-dualGt tgst)
naive-dualSt (trec tgst) = trec (naive-dualGt tgst)
naive-dualSt (tvar x) = tvar x

naive-dualGt (ttransmit d t s) = ttransmit (dual-dir d) (naive-dualTt t) (naive-dualSt s)
naive-dualGt (tchoice d m alt) = tchoice (dual-dir d) m (λ x → naive-dualSt (alt x))
naive-dualGt end = end

naive-dualTt TailTUnit = TailTUnit
naive-dualTt TailTInt = TailTInt
naive-dualTt (TailTPair t t₁) = TailTPair (naive-dualTt t) (naive-dualTt t₁)
naive-dualTt (TailTChan x) = TailTChan (naive-dualS x)

----------------------------------------------------------------------

dualS : (σ : StackS n) → SType n → TailSType n
dualG : (σ : StackS n) → GType n → TailGType n
dualT : (σ : StackS n) → Type n → TailType n

dualS σ (gdd gst) = tgdd (dualG σ gst)
dualS σ (rec gst) = trec (dualG ⟪ σ , (rec gst) ⟫ gst)
dualS σ (var x)   = (tvar x)

dualG{n} σ (transmit d t s) = ttransmit (dual-dir d) (dualT σ t) (dualS σ s)
dualG σ (choice d m alt) = tchoice (dual-dir d) m ((dualS σ) ∘ alt)
dualG σ end = end

dualT σ TUnit = TailTUnit
dualT σ TInt = TailTInt
dualT σ (TPair t t₁) = TailTPair (dualT σ t) (dualT σ t₁)
dualT σ (TChan x) = TailTChan (stack-sim-substS (stack-transform σ) x)

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

open import DualCoinductive hiding (n)

-- Nontail to Coinductive
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

-- Tail to Coinductive
tail2coiT : StackTail n → TailType n → COI.Type
tail2coiS : StackTail n → TailSType n → COI.SType
tail2coiG : StackTail n → TailGType n → COI.STypeF COI.SType

tail2coiT σ TailTUnit = COI.TUnit
tail2coiT σ TailTInt = COI.TInt
tail2coiT σ (TailTPair t t₁) = COI.TPair (tail2coiT σ t) (tail2coiT σ t₁)
tail2coiT σ (TailTChan s) = COI.TChan (ind2coiS ε s)

COI.SType.force (tail2coiS σ (tgdd g)) = tail2coiG σ g
COI.SType.force (tail2coiS σ (trec g)) = tail2coiG ⟪ σ , g ⟫ g
COI.SType.force (tail2coiS{n} σ (tvar x))
  with getTail x σ
... | σ' , gxs rewrite (n∸x≡suc[n∸sucx]{n}{toℕ x} toℕx<n) = tail2coiG ⟪ σ' , gxs ⟫ gxs 

tail2coiG σ (ttransmit d t s) = COI.transmit d (tail2coiT σ t) (tail2coiS σ s)
tail2coiG σ (tchoice d m alt) = COI.choice d m (tail2coiS σ ∘ alt)
tail2coiG σ end = COI.end


_≈_ = COI._≈_
_≈'_ = COI._≈'_
_≈ᵗ_ = COI._≈ᵗ_


stack-unfoldS : (σ : Stack n) (s : IND.SType n) →
  ind2coiS ε (stack-sim-substS (stack-transform (stack2StackS σ)) s) ≈ ind2coiS σ s
stack-unfoldG : (σ : Stack n) (g : IND.GType n) →
  ind2coiG ε (stack-sim-substG (stack-transform (stack2StackS σ)) g) ≈' ind2coiG σ g
stack-unfoldT : (σ : Stack n) (t : IND.Type n) →
  ind2coiT ε (stack-sim-substT (stack-transform (stack2StackS σ)) t) ≈ᵗ ind2coiT σ t

COI.Equiv.force (stack-unfoldS σ (gdd gst)) = stack-unfoldG σ gst
COI.Equiv.force (stack-unfoldS σ (rec gst)) = {!stack-unfoldG ⟪ σ , gst ⟫ gst!}
COI.Equiv.force (stack-unfoldS σ (var x)) = {!!}

stack-unfoldG σ (transmit d t s) = COI.eq-transmit d (stack-unfoldT σ t) (stack-unfoldS σ s)
stack-unfoldG σ (choice d m alt) = COI.eq-choice d (λ i → stack-unfoldS σ (alt i))
stack-unfoldG σ end = COI.eq-end

stack-unfoldT σ TUnit = COI.eq-unit
stack-unfoldT σ TInt = COI.eq-int
stack-unfoldT σ (TPair t t₁) = COI.eq-pair (stack-unfoldT σ t) (stack-unfoldT σ t₁)
stack-unfoldT σ (TChan x) = COI.eq-chan (stack-unfoldS σ x)


mcl-equiv-S : (σ : Stack n) (s : IND.SType n) →
  tail2coiS (stack2StackTail σ) (mclS (stack2StackS σ) s) ≈ ind2coiS σ s
mcl-equiv-G : (σ : Stack n) (g : IND.GType n) →
  tail2coiG (stack2StackTail σ) (mclG (stack2StackS σ) g) ≈' ind2coiG σ g
mcl-equiv-T : (σ : Stack n) (t : IND.Type n) →
  tail2coiT (stack2StackTail σ) (mclT (stack2StackS σ) t) ≈ᵗ ind2coiT σ t

COI.Equiv.force (mcl-equiv-S σ (gdd gst)) = mcl-equiv-G σ gst
COI.Equiv.force (mcl-equiv-S σ (rec gst)) = mcl-equiv-G ⟪ σ , gst ⟫ gst
COI.Equiv.force (mcl-equiv-S σ (var x)) = {!mcl-equiv-G!}

mcl-equiv-G σ (transmit d t s) = COI.eq-transmit d (mcl-equiv-T σ t) (mcl-equiv-S σ s)
mcl-equiv-G σ (choice d m alt) = COI.eq-choice d (λ i → mcl-equiv-S σ (alt i))
mcl-equiv-G σ end = COI.eq-end

mcl-equiv-T σ TUnit = COI.eq-unit
mcl-equiv-T σ TInt = COI.eq-int
mcl-equiv-T σ (TPair t t₁) = COI.eq-pair (mcl-equiv-T σ t) (mcl-equiv-T σ t₁)
mcl-equiv-T σ (TChan x) = COI.eq-chan (stack-unfoldS σ x)



-- naive-mcl-dual : (σ : StackTail n) (s : IND.SType n) →
--  tail2coiS σ (naive-dualSt (mclS (stackTail2StackS σ) s)) ≈ tail2coiS σ (dualS (stackTail2StackS σ) s)
