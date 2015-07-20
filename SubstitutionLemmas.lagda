\begin{code}
module SubstitutionLemmas where

open import Chi
open import Term
open import Substitution
open import Alpha
open import NaturalProp
open import ParallelReduction
open import ListProperties

open import Data.Empty
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary
open import Function hiding (_∘_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; setoid)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)
open import Data.List hiding (any) renaming (length to length') 
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡ 

infix   1 _▹_ 
infixl  7 _∘_
\end{code}

\begin{code}
_∘_ : Σ → Σ → Σ
(σ ∘ σ') x = (σ' x) ∙ σ
\end{code}

Lemma 3.1 (v) Stougthton

\begin{code}
lemmaσ≡σ'→Mσ≡Mσ' : {M : Λ}{σ σ' : Σ} → 
                   ((x : V) → x * M → σ x ≡ σ' x) → M ∙ σ ≡ M ∙ σ'
lemmaσ≡σ'→Mσ≡Mσ' {v x}   {σ} {σ'} f 
  = f x *v
lemmaσ≡σ'→Mσ≡Mσ' {M · N} {σ} {σ'} f 
  = cong₂ _·_
          (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ} {σ'} (λ x xfreeM → f x (*·l xfreeM))) 
          (lemmaσ≡σ'→Mσ≡Mσ' {N} {σ} {σ'} (λ x xfreeN → f x (*·r xfreeN)))
lemmaσ≡σ'→Mσ≡Mσ' {ƛ x M} {σ} {σ'} f 
  with χ (σ , ƛ x M) | χ (σ' , ƛ x M) | 
       χ-lemma3 σ σ' (ƛ x M) (ƛ x M) (λ x x*M → ((lemma σ σ' f x x*M) , (lemma σ' σ f2 x x*M))) ((λ _ → id),(λ _ → id)) 
  where
  lemma : (σ σ' : Σ) → ((y : V) → y * (ƛ x M) → σ y ≡ σ' y) → (z : V) → z * ƛ x M → (y : V) → y * σ z → y * σ' z
  lemma σ σ' f z zfreeλxM y yfreeσz rewrite f z zfreeλxM = yfreeσz
  f2 : (y : V) → y * (ƛ x M) → σ' y ≡ σ y
  f2 y yfreeλxM = sym (f y yfreeλxM)
... | y | .y | refl 
  =  cong (ƛ y) (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} lemma)
  where
  lemma : (z : V) → z * M → (σ ≺+ (x , v y)) z ≡ (σ' ≺+ (x , v y)) z
  lemma z zfreeM with x ≟ z
  ... | yes _   = refl
  ... | no  x≢z = f z (*ƛ zfreeM x≢z)
\end{code}

\begin{code}
lemma1 : {M : Λ}{σ σ' : Σ} → σ ≅ σ' ⇂ M → M ∙ σ ≡ M ∙ σ'
lemma1 (_ , f) = lemmaσ≡σ'→Mσ≡Mσ' f
\end{code}

\begin{code}
lemmaσ∘≺+ : (M : Λ)(σ σ' : Σ)(x y' : V) 
       → (w : V) → w * M 
       → ((σ' ≺+ (χ (σ , ƛ x M) , v y')) ∘ (σ ≺+ (x , v (χ (σ , ƛ x M))))) w ≡ ((σ' ∘ σ) ≺+ (x , v y')) w
lemmaσ∘≺+ M σ σ' x y' w wfreeM with x ≟ w
... | no  x≢w = begin≡
                   ((σ w) ∙ (σ' ≺+ (y , v y')))
                   ≡⟨ lemmaσ≡σ'→Mσ≡Mσ' {σ w} {σ' ≺+ (y , v y')} {σ'} lemma ⟩
                   (σ w) ∙ σ'
                ◻
    where 
    y = χ (σ , ƛ x M)
    lemma : (u : V) → u * σ w → (σ' ≺+ (y , v y')) u ≡ σ' u
    lemma u ufreeσw with (χ-lemma2 σ (ƛ x M)) w (*ƛ wfreeM x≢w)
    ... | y#σw with y ≟ u
    ...        | no  _    = refl
    lemma .y yfreeσw | y#σw
               | yes refl = ⊥-elim ((lemma-free→¬# yfreeσw) y#σw) 
... | yes x≡w with y ≟ y
    where 
    y = χ (σ , ƛ x M)
...           | yes y≡y = refl 
...           | no  y≢y = ⊥-elim (y≢y refl)           
\end{code}
      

\begin{code}
lemma· : {M : Λ}{σ σ' : Σ} → (M ∙ σ) ∙ σ' ≡ M ∙ (σ' ∘ σ)
lemma· {v x}   {σ} {σ'} = refl
lemma· {M · N} {σ} {σ'} = cong₂ _·_ (lemma· {M}) (lemma· {N}) 
lemma· {ƛ x M} {σ} {σ'} 
  = begin≡
      ((ƛ x M) ∙ σ) ∙ σ'
      ≡⟨ refl ⟩
      (ƛ y (M ∙ (σ ≺+ (x , v y)))) ∙ σ'
      ≡⟨ refl ⟩
      ƛ y' ((M ∙ (σ ≺+ (x , v y))) ∙ (σ' ≺+ (y , v y')))
      ≡⟨ cong (λ M → ƛ y' M) (lemma· {M} {σ ≺+ (x , v y)} {σ' ≺+ (y , v y')}) ⟩
      ƛ y' (M ∙ ((σ' ≺+ (y , v y')) ∘ (σ ≺+ (x , v y)))) 
      ≡⟨ cong (λ M → ƛ y' M) (lemmaσ≡σ'→Mσ≡Mσ' {M} {(σ' ≺+ (y , v y')) ∘ (σ ≺+ (x , v y))} {(σ' ∘ σ) ≺+ (x , v y')} (lemmaσ∘≺+ M σ σ' x y')) ⟩
      ƛ y' (M ∙ ((σ' ∘ σ) ≺+ (x , v y')))
      ≡⟨ cong (λ z → ƛ z (M ∙ ((σ' ∘ σ) ≺+ (x , v z)))) lemma ⟩
      ƛ z (M ∙ ((σ' ∘ σ) ≺+ (x , v z)))
      ≡⟨ refl ⟩
      (ƛ x M) ∙ (σ' ∘ σ)
   ◻
  where 
  y = χ (σ , ƛ x M)
  y' = χ (σ' , ƛ y (M ∙ (σ ≺+ (x , v y))))
  z = χ (σ' ∘ σ , ƛ x M)
  -- lemma 3.1 (viii) Stoughton
  lemma3→ :  (y' : V) → ∃ (λ x' →  (x' * ƛ y (M ∙ σ ≺+ (x , v y))) × (y' * σ' x')) → 
             ∃ (λ u → (u * ƛ x M) × (y' * (σ' ∘ σ) u))
  lemma3→ y' (x' , (*ƛ x'freeMσ≺+xy y≢x') , y'freeσ'x') with lemmafreeσ→ {x'} {M} x'freeMσ≺+xy 
  ... | u , ufreeM , x'freeσ≺+xyu with x ≟ u
  ... | no  x≢u =  u , *ƛ ufreeM x≢u ,  lemmafreeσ← {y'} {σ u} {σ'} (x' , x'freeσ≺+xyu , y'freeσ'x') 
  lemma3→ y' (.y , (*ƛ yfreeMσ≺+xy y≢y) , y'freeσ'y )
      | .x , xfreeM , *v
      | yes refl = ⊥-elim (y≢y refl)  
  lemma3← :  (y' : V) → ∃ (λ x' → (x' * ƛ x M) × (y' * (σ' ∘ σ) x')) →
             ∃ (λ u → (u * ƛ y (M ∙ σ ≺+ (x , v y))) × (y' * σ' u))
  lemma3← y' (x' , (*ƛ x'freeM x≢x') , y'freeσσ'x') with lemmafreeσ→ {y'} {σ x'} {σ'} y'freeσσ'x' 
  ... | u , ufreeσx' , y'freeσ'u with lemmafreeσ← {u} {M} {σ ≺+ (x , v y)} (x' , x'freeM  , lemma)
     where lemma : u * ((σ ≺+ (x , v y)) x')
           lemma with x ≟ x' 
           ... | yes x≡x' = ⊥-elim (x≢x' x≡x')
           ... | no  _    = ufreeσx' 
  ... | ufreeMσ≺+xy = u , *ƛ ufreeMσ≺+xy (y≢u ufreeσx') , y'freeσ'u
     where y≢u : {u : V} → u * (σ x') →  y ≢ u
           y≢u {u} ufreeσx' with u | ufreeσx' | y ≟ u 
           ... | .y | yfreeσx' | yes refl 
             = ⊥-elim ((lemma-free→¬# yfreeσx') ((χ-lemma2 σ (ƛ x M)) x' (*ƛ x'freeM x≢x')))  
           ... | _  | _        | no y≢up  =  y≢up
  lemma : y' ≡ z 
  lemma =  χ-lemma4 σ' (σ' ∘ σ) (ƛ y (M ∙ (σ ≺+ (x , v y)))) (ƛ x M) 
                    (lemma3→ , lemma3←)
\end{code}

\begin{code}
lemma≺+ : {x y z : V}{M : Λ}{σ : Σ} → z # (ƛ x M) → M ∙ (σ ≺+ (x , v y)) ≡ (M ∙ ι ≺+ (x , v z)) ∙ (σ ≺+ (z , v y))
lemma≺+ {x} {y} {z} {M} {σ} z#λxM rewrite lemma· {M} {ι ≺+ (x , v z)} {σ ≺+ (z , v y)} 
  = lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , v y)} {(σ ≺+ (z , v y)) ∘ (ι ≺+ (x , v z))} lemma
  where
  lemma : (w : V) → w * M → (σ ≺+ (x , v y)) w ≡ (((σ ≺+ (z , v y)) ∘ (ι ≺+ (x , v z))) w) -- este me sirve ???
  lemma w wfreeM with x ≟ w
  ... | no x≢w  with z ≟ w
  ... | no _    = refl
  ... | yes z≡w = ⊥-elim ((z≢w x y z w M z#λxM wfreeM x≢w) z≡w)
    where
    z≢w : (x y z w : V)(M : Λ) → z # (ƛ x M) → w * M → x ≢ w  → z ≢ w
    z≢w x y .x w M #ƛ≡ wfreeM x≢w = x≢w
    z≢w x y z w M (#ƛ  z#M) wfreeM x≢w with z ≟ w
    ... | no z≢w = z≢w
    z≢w x y z .z M (#ƛ  z#M) zfreeM x≢w
        | yes refl = ⊥-elim ((lemma-free→¬# zfreeM) z#M)
  lemma w wfreeM
      | yes _ with z ≟ z 
  ... | yes _   = refl
  ... | no z≢z  = ⊥-elim (z≢z refl)
\end{code}

\begin{code}
lemmaM∼M'→Mσ≡M'σ : {M M' : Λ}{σ : Σ} 
  → M ∼α M' → M ∙ σ ≡ M' ∙ σ
lemmaM∼M'→Mσ≡M'σ ∼v              = refl
lemmaM∼M'→Mσ≡M'σ (∼· M∼M' N∼N') = cong₂ _·_ (lemmaM∼M'→Mσ≡M'σ M∼M') (lemmaM∼M'→Mσ≡M'σ N∼N')
lemmaM∼M'→Mσ≡M'σ {ƛ x M} {ƛ x' M'} {σ} 
                 (∼ƛ .{M} .{M'} .{x} .{x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z) 
  with χ (σ , ƛ x M) | χ (σ , ƛ x' M') 
    | χ-lemma3 σ σ (ƛ x M) (ƛ x' M') 
         (λ _ _ → (λ _ yfreeσx → yfreeσx) , (λ _ yfreeσx → yfreeσx))
         ( (lemmaM∼M'→free→ {ƛ x M} {ƛ x' M'} (∼ƛ {M} {M'} {x} {x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z)) ,
           (lemmaM∼M'→free← {ƛ x M} {ƛ x' M'} (∼ƛ {M} {M'} {x} {x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z)))
... | y | .y | refl 
  = cong (λ M → ƛ y M) 
         (begin≡
           M ∙ (σ ≺+ (x , v y))
           ≡⟨ lemma≺+ z#λxM ⟩
           (M ∙ (ι ≺+ (x , v z))) ∙ (σ ≺+ (z , v y))
           ≡⟨ lemmaM∼M'→Mσ≡M'σ {M ∙ (ι ≺+ (x , v z))} {M' ∙ (ι ≺+ (x' , v z))} {σ ≺+ (z , v y)} Mι≺+xz∼M'ι≺+x'z ⟩
           (M' ∙ (ι ≺+ (x' , v z))) ∙ (σ ≺+ (z , v y))
           ≡⟨ sym (lemma≺+ z#λx'M') ⟩
           M' ∙ (σ ≺+ (x' , v y))
          ◻)
\end{code}

\begin{code}
open import Induction.Nat

lemma-χι : (M : Λ) → χ (ι , M) # M
lemma-χι M = lemmafree#y→# (χ-lemma2 ι M)

lemmaMι≡M'ι→M∼M'-aux : (n : ℕ) →
  ((y : ℕ) → suc y ≤′ n → (M M' : Λ) → y ≡ length M → M ∙ ι ≡ M' ∙ ι → M ∼α M') →                     
  (M M' : Λ) → n ≡ length M → M ∙ ι ≡ M' ∙ ι → M ∼α M'  
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (v .x)    refl refl = ∼v
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (M · N)   refl () 
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (ƛ y M)   refl () 
lemmaMι≡M'ι→M∼M'-aux n           rec (M · N) (v x)     _    ()
lemmaMι≡M'ι→M∼M'-aux .(length M + length N) rec (M · N) (M' · N') refl MNι≡M'N'ι
  = ∼·  (rec (length M) (lemmam>0→m+1≤m+n (length>0 {N})) M M' refl (proj₁ (lemmaMι≡M'ι MNι≡M'N'ι)))
        (rec (length N) (lemman>0→n+1≤m+n (length>0 {M})) N N' refl (proj₂ (lemmaMι≡M'ι MNι≡M'N'ι)) )
  where 
  lemmaMι≡M'ι : (M · N) ∙ ι ≡ (M' · N') ∙ ι → M ∙ ι ≡ M' ∙ ι × N ∙ ι ≡ N' ∙ ι
  lemmaMι≡M'ι MNι≡M'N'ι with M' ∙ ι | N' ∙ ι | MNι≡M'N'ι
  ... | .(M ∙ ι) | .(N ∙ ι) | refl = refl , refl
lemmaMι≡M'ι→M∼M'-aux n           rec (M · N) (ƛ x M')  _    () 
lemmaMι≡M'ι→M∼M'-aux n           rec (ƛ x M) (v y)     _    () 
lemmaMι≡M'ι→M∼M'-aux n           rec (ƛ x M) (M' · N') _    ()
lemmaMι≡M'ι→M∼M'-aux .(suc (length M)) rec (ƛ x M) (ƛ x' M') refl λxMι≡λx'M' 
  with lemmaλxMι≡λx'M'ι λxMι≡λx'M' 
  where
  lemmaλxMι≡λx'M'ι : (ƛ x M) ∙ ι ≡ (ƛ x' M') ∙ ι → 
                     χ (ι , ƛ x M) ≡ χ (ι , ƛ x' M') × 
                     M ∙ (ι ≺+ (x , v (χ (ι , ƛ x M)))) ≡ M' ∙ (ι ≺+ (x' , v (χ (ι , ƛ x' M')))) 
  lemmaλxMι≡λx'M'ι λxMι#λx'M'ι with χ (ι , ƛ x M)    |   M ∙ (ι ≺+ (x , v (χ (ι , ƛ x M)))) | λxMι#λx'M'ι 
  ... | .(χ (ι , ƛ x' M')) | .(M' ∙ (ι ≺+ (x' , v (χ (ι , ƛ x' M'))))) | refl = refl , refl
... | y≡y' , Mι≺+xy≡M'ι≺+xy' 
  with χ (ι , ƛ x M) | χ (ι , ƛ x' M') | lemma-χι (ƛ x M) | lemma-χι (ƛ x' M') | y≡y' 
... | y | .y | y#λxM | y#λx'M' | refl 
  = ∼ƛ  {M} {M'} {x} {x'} {y} y#λxM y#λx'M' 
        (rec (length (M ∙ (ι ≺+ (x , v y)))) 
             (lemmam≡n→m+1≤n+1 (lemma-length-corolary {x} {y} {M})) 
             (M ∙ (ι ≺+ (x , v y))) 
             (M' ∙ (ι ≺+ (x' , v y))) 
             refl 
             (cong (λ M → M ∙ ι) Mι≺+xy≡M'ι≺+xy'))

lemmaMι≡M'ι→M∼M' : {M M' : Λ} → M ∙ ι ≡ M' ∙ ι → M ∼α M' 
lemmaMι≡M'ι→M∼M' {M} {M'} = (<-rec _ lemmaMι≡M'ι→M∼M'-aux) (length M) M M' refl
\end{code}

\begin{code}
∼ρ : Reflexive _∼α_
∼ρ {M} = lemmaMι≡M'ι→M∼M' refl
\end{code}
\begin{code}
∼σ : Symmetric _∼α_
∼σ {M} {N} M∼N 
  = lemmaMι≡M'ι→M∼M' 
          (sym (lemmaM∼M'→Mσ≡M'σ M∼N))
\end{code}
\begin{code}
∼τ : Transitive _∼α_
∼τ {M} {N} {P} M∼N N∼P 
  = lemmaMι≡M'ι→M∼M' 
         (trans (lemmaM∼M'→Mσ≡M'σ M∼N) 
                (lemmaM∼M'→Mσ≡M'σ N∼P))
\end{code}

\begin{code}
≈-preorder∼ : Preorder _ _ _
≈-preorder∼ =  
    record { 
      Carrier = Λ;
      _≈_ = _≡_;
      _∼_ = _∼α_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid Λ) ;
        reflexive = λ { {M} {.M} refl → ∼ρ};
        trans = ∼τ } }

import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder∼

lemma-σ⇂ : {M : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → ((ι ∘ σ) , M) ≅ρ ((ι ∘ σ') , M)
lemma-σ⇂ σ∼σ'⇂M  = ((λ _ x → x) , (λ _ x → x)) , (λ x xfreeM →  lemmaM∼M'→Mσ≡M'σ (σ∼σ'⇂M  x xfreeM))
--
lemma-subst-σ∼ : {M : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → M ∙ σ ∼α M ∙ σ'
lemma-subst-σ∼ {M} {σ} {σ'} σ∼ασ'⇂M 
  = lemmaMι≡M'ι→M∼M' (begin≡
                        (M ∙ σ) ∙ ι
                        ≡⟨ lemma· {M} {σ} {ι} ⟩
                        M ∙ (ι ∘ σ)
                        ≡⟨  lemma-subst-σ≡ {M} {ι ∘ σ} {ι ∘ σ'} (lemma-σ⇂ σ∼ασ'⇂M) ⟩
                        M ∙ (ι ∘ σ')
                        ≡⟨ sym (lemma· {M} {σ'} {ι}) ⟩
                        (M ∙ σ') ∙ ι
                      ◻)
\end{code}

\begin{code}
lemma-subst : {M M' : Λ}{σ σ' : Σ} → 
  M ∼α M' → σ ∼α σ' ⇂ M → (M ∙ σ) ∼α (M' ∙ σ')
lemma-subst {M} {M'} {σ} {σ'} M∼M' σ∼σ'⇂M 
  =  begin
       M ∙ σ
       ∼⟨ lemma-subst-σ∼ σ∼σ'⇂M ⟩
       M ∙ σ'
       ≈⟨ lemmaM∼M'→Mσ≡M'σ M∼M'  ⟩
       M' ∙ σ'
     ∎
\end{code}

Corollary 4

\begin{code}
postulate
  corollary4-2  : {x y : V}{M : Λ}{σ : Σ}
                → y #⇂ (σ , ƛ x M) 
                → ƛ x M ∙ σ ∼α ƛ y (M ∙ σ ≺+ (x , v y))
\end{code}


Beta contraction

%<*betacontraction>
\begin{code}
data _▹_ : Λ → Λ → Set where
  ▹β  :  {M N : Λ}{x : V} 
      →  ƛ x M · N ▹ M ∙ ι ≺+ (x , N)
\end{code}
%</betacontraction>

Beta contraction preserves typing judge.

%<*typebeta>
\begin{code}
lemma⊢▹  :  {Γ : Cxt}{α : Type}{M N : Λ} 
         →  Γ ⊢ M ∶ α → M ▹ N → Γ ⊢ N ∶ α
\end{code}
%</typebeta>

%<*typebetaproof>
\begin{code}
lemma⊢▹ {Γ} (⊢· .{M = ƛ x M} {N} (⊢ƛ {x} {α} {β} {M} Γ,x:α⊢M:β) Γ⊢N:α) ▹β 
  = lemma⊢σM  {ι ≺+ (x , N)} {Γ ‚ x ∶ α} {Γ} {M} 
              Γ,x:α⊢M:β
              (lemmaι≺+⇀ Γ⊢N:α)
\end{code}
%</typebetaproof>

%<*typeiota>
\begin{code}
postulate
  lemma⊢ι  :  {Γ : Cxt}{α : Type}{M : Λ} 
           →  Γ ⊢ M ∙ ι ∶ α → Γ ⊢ M ∶ α
\end{code}
%</typeiota>

-- %<*typeiotaproof>
-- \begin{code}
-- lemma⊢ι Γ⊢M∙ι 
--   = {!!} --lemmaWeakening⊢++ (lemma⊢σ++ Γ⊢M∙ι (∶⇀ι id))
-- \end{code}
-- %</typeiotaproof>

%<*typealpha>
\begin{code}
lemma⊢α  :  {Γ : Cxt}{α : Type}{M N : Λ} 
         →  M ∼α N → Γ ⊢ M ∶ α → Γ ⊢ N ∶ α
\end{code}
%</typealpha>

%<*typealphaproof>
\begin{code}
lemma⊢α {M = M} {N = N} M∼N Γ⊢M 
  with M ∙ ι    | lemma⊢σM Γ⊢M lemmaι⇀  | lemmaM∼M'→Mσ≡M'σ {σ = ι} M∼N 
... | .(N ∙ ι)  | Γ⊢N∙ι                 | refl 
  = lemma⊢ι Γ⊢N∙ι
\end{code}
%</typealphaproof>

-- \begin{code}
-- lemma≺+swap : {x y u w : V}{P : Λ} 
--             → x ∉ y ∷ fv P
-- --            → w ∉ fv P 
--             → (ι ≺+ (y , P) ≺+ (x , v w)) u ≡ (ι ≺+ (x , v w) ∘ ι ≺+ (y , P)) u
-- lemma≺+swap = {!!}
-- \end{code}

-- %<*naivesubstitution>
-- \begin{code}
-- lemmaƛ∼[] : ∀ {x y : V}{P : Λ} → (M : Λ) → x ∉ y ∷ fv P 
--   → ƛ x M ∙ ι ≺+ (y , P) ∼α  ƛ x (M ∙ ι ≺+ (y , P))
-- \end{code}
-- %</naivesubstitution>

-- \begin{code}
-- lemmaƛ∼[] {x} {y} {P} M x∉y∷fvP
--   = begin
--        ƛ x M ∙ ι ≺+ ( y , P )
--     ≈⟨ refl ⟩  
--        ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z))
--     ∼⟨ ∼ƛ {y = w} w#1 w#2 
--           (begin
--              (M ∙ ι ≺+ (y , P) ≺+ (x , v z)) ∙ ι ≺+ (z , v w) 
--            ≈⟨ lemma· {M} {ι ≺+ (y , P) ≺+ (x , v z)} {ι ≺+ (z , v w)} ⟩
--              M ∙ ( ι ≺+ (z , v w) ∘ ι ≺+ (y , P) ≺+ (x , v z) )
--            ≈⟨ lemmaσ≡σ'→Mσ≡Mσ'  {M} 
--                                 {ι ≺+ (z , v w) ∘ ι ≺+ (y , P) ≺+ (x , v z)}
--                                 {ι ≺+ (x , v w) ∘ ι ≺+ (y , P)} 
--                                 (λ u u*M →
--                                    begin≡
--                                      (ι ≺+ (z , v w) ∘ ι ≺+ (y , P) ≺+ (x , v z)) u
--                                    ≡⟨ lemmaσ∘≺+ M (ι ≺+ (y , P)) ι x w u u*M ⟩
--                                      ((ι ∘ (ι ≺+ (y , P))) ≺+ (x , v w)) u 
--                                    ≡⟨ {! !} ⟩
--                                      (ι ≺+ (y , P) ≺+ (x , v w)) u              
--                                    ≡⟨ lemma≺+swap x∉y∷fvP ⟩
--                                      (ι ≺+ (x , v w) ∘ ι ≺+ (y , P)) u
--                                    ◻) ⟩  
--              M ∙ (ι ≺+ (x , v w) ∘ ι ≺+ (y , P))
--            ≈⟨ sym (lemma· {M} {ι ≺+ (y , P)} {ι ≺+ (x , v w)}) ⟩
--              (M ∙ ι ≺+ (y , P)) ∙ ι ≺+ (x , v w)
--            ∎)⟩ 
--        ƛ x (M ∙ ι ≺+ ( y , P ))
--     ∎
--   where
--   z = χ (ι ≺+ ( y , P ) , ƛ x M)
--   w = χ' (fv (ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z))) ++ fv (ƛ x (M ∙ ι ≺+ ( y , P ))))
--   w∉fv : w ∉ (fv (ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z))) ++ fv (ƛ x (M ∙ ι ≺+ ( y , P ))))
--   w∉fv = lemmaχ∉ (fv (ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z))) ++ fv (ƛ x (M ∙ ι ≺+ ( y , P ))))
--   w#1 : w # ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z))
--   w#1 = lemma∉fv→# (c∉xs++ys→c∉xs w∉fv)
--   w#2 : w # ƛ x (M ∙ ι ≺+ ( y , P ))
--   w#2 = lemma∉fv→# (c∉xs++ys→c∉ys {xs = fv (ƛ z (M ∙ ι ≺+ ( y , P ) ≺+ (x , v z)))} w∉fv)

-- --  w = z ??
--   -- where 
--   -- a≢b : a ≢ b
--   -- a≢b = sym≢ (b∉a∷xs→b≢a b∉a∷fvP)
--   -- a≢d : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → a ≢ d
--   -- a≢d d∉ = sym≢ (b∉a∷xs→b≢a d∉)
--   -- d#M : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → d # M
--   -- d#M d∉ = lemma∉fv→# (c∉xs++ys→c∉ys {xs = fv P} (b∉a∷xs→b∉xs d∉))
--   -- d#P : ∀ {d} → d ∉ (a ∷ fv P ++ fv M) → d # P
--   -- d#P d∉ = lemma∉fv→# (c∉xs++ys→c∉xs (b∉a∷xs→b∉xs d∉))
--   -- c = χ (a ∷ fv P) (ƛ b M)
--   -- c#ƛbM = χ# (a ∷ fv P) (ƛ b M)
--   -- c∉a∷fvP = χ∉ (a ∷ fv P) (ƛ b M)
--   -- c#P : c # P
--   -- c#P = lemma∉fv→# (b∉a∷xs→b∉xs c∉a∷fvP)
--   -- b#P : b # P
--   -- b#P = lemma∉fv→# (b∉a∷xs→b∉xs b∉a∷fvP)
--   -- a≢c : a ≢ c
--   -- a≢c = sym≢ (b∉a∷xs→b≢a c∉a∷fvP)
-- \end{code}

\begin{code}
infix 1 _≅σ_
_≅σ_ : Σ → Σ → Set
σ ≅σ σ' = (x : V) → σ x ≡ σ' x

lemmaι : {σ : Σ} → σ ≅σ σ ∘ ι 
lemmaι x = refl

lemma≅≺+ : {x : V}{N : Λ}{σ σ' : Σ} → σ ≅σ σ' → σ ≺+ (x , N) ≅σ σ' ≺+ (x , N)
lemma≅≺+ {x} σ≌σ' y with x ≟ y
... | yes  _ = refl 
... | no   _ = σ≌σ' y

prop6 : {σ σ' : Σ}{M : Λ} → σ ≅σ σ' → σ ≅ σ' ⇂ M
prop6 σ≅σ' = ((λ _ → id) , (λ _ → id)) , λ x _ → σ≅σ' x

postulate  
  prop7 : {x : V}{σ σ' : Σ}{M : Λ} → (σ' ∘ σ) ≺+ (x , M ∙ σ') ≅σ σ' ∘ (σ ≺+ (x , M))
  prop8 : {x y : V}{σ : Σ}{M N : Λ} → y #⇂ (σ , ƛ x M) → (ι ≺+ (y , N) ∘ σ ≺+ (x , v y)) ≅ σ ≺+ (x , N) ⇂ M

corollary1Prop7 : {M N : Λ}{σ : Σ}{x : V} → M ∙ σ ≺+ (x , N ∙ σ) ≡ (M ∙ ι ≺+ (x , N)) ∙ σ
corollary1Prop7 {M} {N} {σ} {x}
  = begin≡
      M ∙ σ ≺+ (x , N ∙ σ)
   ≡⟨ lemma1 {M} (prop6 (lemma≅≺+ {x} {N ∙ σ} (lemmaι {σ}))) ⟩
      M ∙ (σ ∘ ι) ≺+ (x , N ∙ σ)
   ≡⟨ lemma1  (prop6 {(σ ∘ ι) ≺+ (x , N ∙ σ)} {σ ∘ ι ≺+ (x , N)} {M} (prop7 {x})) ⟩
      M ∙ σ ∘ ι ≺+ (x , N)
   ≡⟨  sym (lemma· {M}) ⟩
      (M ∙ ι ≺+ (x , N)) ∙ σ
    ◻

corollary1SubstLemma : {x y : V} {σ : Σ}{M N : Λ} → y #⇂ (σ , ƛ x M) → (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N) ∼α M ∙ σ ≺+ (x , N)
corollary1SubstLemma {x} {y} {σ} {M} {N} y#⇂σ,ƛxM 
  =  begin
       (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N)
     ≈⟨ lemma· {M} ⟩
       M ∙ (ι ≺+ (y , N) ∘ σ ≺+ (x , v y))
     ≈⟨ lemma1 (prop8 y#⇂σ,ƛxM) ⟩
       M ∙ σ ≺+ (x , N)
     ∎
 \end{code}

Parallel reduction

\begin{code}
lemma⇉  : {M M' : Λ}{σ σ' : Σ} 
        → M ⇉ M' → σ ⇉ₛ σ' 
        → M ∙ σ ⇉ M' ∙ σ'
lemma⇉  (⇉v x)            σ⇉σ' 
  = σ⇉σ' x
lemma⇉  {ƛ .x M} {ƛ .x M'} {σ} {σ'}
        (⇉ƛ x M⇉M')       σ⇉σ' 
  = ⇉α (⇉ƛ y (lemma⇉ M⇉M'  (lemma⇉s x y σ⇉σ'))) 
                           (∼σ (corollary4-2  {x} {y} {M'} {σ'} 
                                              (λ y y*λxM' → lemma⇉# (y#⇂σ,ƛxM y (lemma⇉* y*λxM' (⇉ƛ x M⇉M'))) (σ⇉σ' y) ))) -- (*)
  where
  y = χ (σ , ƛ x M)
  y#⇂σ,ƛxM : y #⇂ (σ , ƛ x M)
  y#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
  z = χ (σ'  , ƛ x M')
  z#⇂σ',ƛxM' : z #⇂ (σ' , ƛ x M')
  z#⇂σ',ƛxM' = χ-lemma2 σ' (ƛ x M')
lemma⇉  (⇉· M⇉M' N⇉N')    σ⇉σ' 
  = ⇉· (lemma⇉ M⇉M' σ⇉σ') (lemma⇉ N⇉N' σ⇉σ')
lemma⇉  .{ƛ x M · N} .{M' ∙ ι ≺+ (x , N')} {σ} {σ'}
        (⇉β x {M} {M'} {N} {N'} M⇉M' N⇉N')  σ⇉σ' 
  = ⇉α (⇉β y (lemma⇉ M⇉M' (lemma⇉s x y σ⇉σ')) (lemma⇉ N⇉N' σ⇉σ')) lemma∼
  where
  y = χ (σ , ƛ x M)
  y#⇂σ,ƛxM : y #⇂ (σ , ƛ x M)
  y#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
  lemma∼ : (M' ∙ σ'  ≺+ (x , v y)) ∙  ι ≺+ (y , N' ∙ σ') ∼α (M' ∙ ι ≺+ (x , N')) ∙ σ'
  lemma∼ = begin 
             (M' ∙ σ'  ≺+ (x , v y)) ∙  ι ≺+ (y , N' ∙ σ')
           ∼⟨ corollary1SubstLemma ((λ y y*λxM' → lemma⇉# (y#⇂σ,ƛxM y (lemma⇉* y*λxM' (⇉ƛ x M⇉M'))) (σ⇉σ' y) )) ⟩ -- arriba en (*) es igual, factorizar en lemma ?
              M' ∙ σ'  ≺+ (x , N' ∙ σ')
           ≈⟨ corollary1Prop7 {M'} {N'} {σ'} {x} ⟩
             (M' ∙ ι ≺+ (x , N')) ∙ σ'
           ∎
lemma⇉  (⇉α M⇉N N∼N')     σ⇉σ' 
  = ⇉α (lemma⇉ M⇉N σ⇉σ') (lemma-subst N∼N' (λ _ _ → ∼ρ)) 
\end{code}
