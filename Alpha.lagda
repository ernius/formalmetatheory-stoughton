\begin{code}
module Alpha where

open import Chi
open import Term
open import Substitution 

open import Function
open import Data.Empty
open import Relation.Nullary
open import Data.Nat hiding (_*_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)

infix  1 _∼α_ 
\end{code}


\begin{code}
data _∼α_ : Λ → Λ → Set where
  ∼v  : {x : V} → (v x) ∼α v x
  ∼·  : {M M' N N' : Λ} → M ∼α M' → N ∼α N' 
      → M · N ∼α M' · N'
  ∼ƛ  : {M M' : Λ}{x x' y : V} 
      → y # ƛ x M → y # ƛ x' M' 
      → M ∙ ι ≺+ (x , v y) ∼α M' ∙ ι ≺+ (x' , v y)
      → ƛ x M ∼α ƛ x' M'
\end{code}

\begin{code}
_∼α_⇂_ : Σ → Σ → Λ → Set
σ ∼α σ' ⇂ M = (x : V) → x * M → σ x ∼α σ' x
\end{code}

Freshness lemmas used in lemmaM∼M'→free lemmas

\begin{code}
lemmafree1 : {x y z : V}{M : Λ} → x ≢ z → z * M → z * (M ∙ (ι ≺+ (x , v y))) 
lemmafree1 {x} {y} {z} {M} x≢z zfreeM = lemmafreeσ← {z} {M} (z , zfreeM , lemma)
  where lemma : z * ((ι ≺+ (x , v y)) z)
        lemma with x ≟ z
        ... | yes x≡z = ⊥-elim (x≢z x≡z)
        ... | no  _   = *v

lemmafree2 : {x x' y z : V}{M M' : Λ} → y # (ƛ x M) → x ≢ z → 
             z * (M' ∙ (ι ≺+ (x' , v y))) → z * M → 
             x' ≢ z 
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
  with lemmafreeσ→ {z} {M'} zfreeM'ι≺+x'y
... | w , wfreeM' , zfreeι≺+x'yw with x' ≟ w
... | no  x'≢w with zfreeι≺+x'yw 
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
    | .z , wfreeM' , zfreeι≺+x'yw
    | no  x'≢w
    | *v = λ x'≡z → x'≢w (trans (x'≡z) (sym refl)) 
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl 
    with y#λxM | x'freeι≺+x'yw 
lemmafree2 {x} {x'} .{x} .{x} {M} {M'} y#λxM x≢y yfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl 
    | #ƛ≡ | *v = ⊥-elim (x≢y refl)
lemmafree2 {x} {x'} {y} .{y} {M} {M'} y#λxM x≢y yfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl 
    | #ƛ y#M  | *v = ⊥-elim ((lemma-free→¬# zfreeM) y#M) -- x' ≠ y 

lemmafree3 : {x y z : V}{M : Λ} → z ≢ y → z * (M ∙ (ι ≺+ (x , v y))) → z * M 
lemmafree3 {x} {y} {z} {M} z≢y zfreeMι≺+xy 
  with lemmafreeσ→ {z} {M} zfreeMι≺+xy 
... | w , wfreeM , zfreeι≺+xyw with x ≟ w | zfreeι≺+xyw
lemmafree3 {x} {y} .{y} {M} y≢y yfreeMι≺+xy 
    | w , wfreeM , yfreeι≺+xyw 
    | yes x≡w | *v = ⊥-elim (y≢y refl)
lemmafree3 {x} {y} {z} {M} z≢y zfreeMι≺+xy 
    | .z , zfreeM , _
    | no  x≡w | *v = zfreeM

lemmafree4 : {x y z : V}{M : Λ} → x ≢ z → z * M → y # (ƛ x M) → z ≢ y
lemmafree4 {x} .{x} {z} x≢z zfreeM #ƛ≡ = sym≢ x≢z
lemmafree4 {x} {y} {z}  x≢z zfreeM (#ƛ y#M) with z ≟ y
... | no  z≢y = z≢y
lemmafree4 {x} {y} .{y}  x≢y yfreeM (#ƛ  y#M)
    | yes refl = ⊥-elim ((lemma-free→¬# yfreeM) y#M)
\end{code}

\begin{code}
lemmaM∼M'→free→ : {M M' : Λ} → M ∼α M' →
                  (z : V) → z * M → z * M'
lemmaM∼M'→free→ ∼v                                 z zfreex           
  = zfreex
lemmaM∼M'→free→ (∼· M∼M' N∼N')                     z (*·l zfreeM)    
  = *·l (lemmaM∼M'→free→ M∼M' z zfreeM) 
lemmaM∼M'→free→ (∼· M∼M' N∼N')                     z (*·r zfreeN)    
  = *·r (lemmaM∼M'→free→ N∼N' z zfreeN) 
lemmaM∼M'→free→ (∼ƛ {M} {M'} {x} {x'} {y} 
                y#λxM y#λx'M' Mι≺+xy∼M'ι≺+x'y) z (*ƛ zfreeM x≢z) 
  = *ƛ (lemmafree3 {x'} {y} {z} {M'} (lemmafree4 x≢z zfreeM y#λxM) lemma) 
       (lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z lemma zfreeM)  
    where 
    lemma : z * (M' ∙ (ι ≺+ (x' , v y)))
    lemma = lemmaM∼M'→free→ Mι≺+xy∼M'ι≺+x'y z (lemmafree1 x≢z zfreeM)
\end{code}

\begin{code}
lemmaM∼M'→free← : {M M' : Λ} → M ∼α M' → 
                  (z : V) → z * M' → z * M
lemmaM∼M'→free← ∼v                                 z zfreex           
  = zfreex
lemmaM∼M'→free← (∼· M∼M' N∼N')                     z (*·l zfreeM')    
  = *·l (lemmaM∼M'→free← M∼M' z zfreeM') 
lemmaM∼M'→free← (∼· M∼M' N∼N')                     z (*·r zfreeN')    
  = *·r (lemmaM∼M'→free← N∼N' z zfreeN') 
lemmaM∼M'→free← (∼ƛ {M} {M'} {x} {x'} {y} 
                y#λxM y#λx'M' Mι≺+xy∼M'ι≺+x'y) z (*ƛ zfreeM' x'≢z) 
  = *ƛ (lemmafree3 {x} {y} {z} {M} (lemmafree4 x'≢z zfreeM' y#λx'M') lemma) 
       (lemmafree2 {x'} {x} {y} {z} {M'} {M} y#λx'M' x'≢z lemma zfreeM')
  where 
  lemma : z * (M ∙ (ι ≺+ (x , v y)))
  lemma = lemmaM∼M'→free← Mι≺+xy∼M'ι≺+x'y z (lemmafree1 x'≢z zfreeM')
\end{code}
