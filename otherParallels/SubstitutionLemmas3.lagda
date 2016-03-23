\begin{code}
module SubstitutionLemmas3 where

open import Chi
open import Term
open import Substitution
open import Alpha
open import NaturalProp
open import ParallelReduction3
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
\end{code}

Lemma 3.1 (v) Stougthton

\begin{code}
lemmaσ≡σ'→Mσ≡Mσ'  : {M : Λ}{σ σ' : Σ} 
                  → σ ≅ σ' ⇂ M 
                  → M ∙ σ ≡ M ∙ σ'
lemmaσ≡σ'→Mσ≡Mσ' {v x}   {σ} {σ'} (_ , f) 
  = f x *v
lemmaσ≡σ'→Mσ≡Mσ' {M · N} {σ} {σ'} (_ , f) 
  = cong₂ _·_
          (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ} {σ'} (∼*ρ , (λ x xfreeM → f x (*·l xfreeM)))) 
          (lemmaσ≡σ'→Mσ≡Mσ' {N} {σ} {σ'} (∼*ρ , (λ x xfreeN → f x (*·r xfreeN))))
lemmaσ≡σ'→Mσ≡Mσ' {ƛ x M} {σ} {σ'} (_ , f) 
  with χ (σ , ƛ x M) | χ (σ' , ƛ x M) | 
       χ-lemma3 σ σ' (ƛ x M) (ƛ x M) (λ x x*M → ((lemma σ σ' f x x*M) , (lemma σ' σ f2 x x*M))) ∼*ρ
  where
  lemma : (σ σ' : Σ) → ((y : V) → y * (ƛ x M) → σ y ≡ σ' y) → (z : V) → z * ƛ x M → (y : V) → y * σ z → y * σ' z
  lemma σ σ' f z zfreeλxM y yfreeσz rewrite f z zfreeλxM = yfreeσz
  f2 : (y : V) → y * (ƛ x M) → σ' y ≡ σ y
  f2 y yfreeλxM = sym (f y yfreeλxM)
... | y | .y | refl 
  =  cong (ƛ y) (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} (∼*ρ , lemma))
  where
  lemma : (z : V) → z * M → (σ ≺+ (x , v y)) z ≡ (σ' ≺+ (x , v y)) z
  lemma z zfreeM with x ≟ z
  ... | yes _   = refl
  ... | no  x≢z = f z (*ƛ zfreeM x≢z)
\end{code}

\begin{code}
lemma1 : {M : Λ}{σ σ' : Σ} → σ ≅ σ' ⇂ M → M ∙ σ ≡ M ∙ σ'
lemma1 = lemmaσ≡σ'→Mσ≡Mσ'
--
lemmaMι≺+x,x : {x : V}{M : Λ} → M ∙ ι ≺+ (x , v x) ≡ M ∙ ι
lemmaMι≺+x,x {x} {M} = lemmaσ≡σ'→Mσ≡Mσ' {M} (prop6 {ι ≺+ (x , v x)} {ι} (lemmaσ≺+x,x≅σ {x})) 
\end{code}

\begin{code}
lemmaσ∘≺+ : (M N : Λ)(σ σ' : Σ)(x y : V) 
       → y #⇂ (σ , ƛ x M)
       → (w : V) → w * M 
       → ((σ' ≺+ (y , N)) ∘ (σ ≺+ (x , v y))) w ≡ ((σ' ∘ σ) ≺+ (x , N)) w
lemmaσ∘≺+ M N σ σ' x y y#⇂σ,ƛxM w wfreeM with x ≟ w
... | no  x≢w = begin≡
                   ((σ w) ∙ (σ' ≺+ (y , N)))
                   ≡⟨ lemmaσ≡σ'→Mσ≡Mσ' {σ w} {σ' ≺+ (y , N)} {σ'} (∼*ρ , lemma) ⟩
                   (σ w) ∙ σ'
                ◻
    where 
    lemma : (u : V) → u * σ w → (σ' ≺+ (y , N)) u ≡ σ' u
    lemma u ufreeσw with y#⇂σ,ƛxM w (*ƛ wfreeM x≢w)
    ... | y#σw with y ≟ u
    ...        | no  _    = refl
    lemma .y yfreeσw | y#σw
               | yes refl = ⊥-elim ((lemma-free→¬# yfreeσw) y#σw) 
... | yes x≡w with y ≟ y
...           | yes y≡y = refl 
...           | no  y≢y = ⊥-elim (y≢y refl)           
--
lemmaχσ∘≺+ : (M N : Λ)(σ σ' : Σ)(x : V) 
       → (w : V) → w * M 
       → ((σ' ≺+ (χ (σ , ƛ x M) , N)) ∘ (σ ≺+ (x , v (χ (σ , ƛ x M))))) w ≡ ((σ' ∘ σ) ≺+ (x , N)) w
lemmaχσ∘≺+ M N σ σ' x = lemmaσ∘≺+ M N σ σ' x (χ (σ , ƛ x M)) (χ-lemma2 σ (ƛ x M)) 
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
      ≡⟨ cong (λ M → ƛ y' M) (lemmaσ≡σ'→Mσ≡Mσ' {M} {(σ' ≺+ (y , v y')) ∘ (σ ≺+ (x , v y))} {(σ' ∘ σ) ≺+ (x , v y')} ((∼*ρ , lemmaχσ∘≺+ M (v y') σ σ' x))) ⟩
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
lemma≺+ : {x z : V}{M N : Λ}{σ : Σ} → z # (ƛ x M) → M ∙ (σ ≺+ (x , N)) ≡ (M ∙ ι ≺+ (x , v z)) ∙ (σ ≺+ (z , N))
lemma≺+ {x} {z} {M} {N} {σ} z#λxM rewrite lemma· {M} {ι ≺+ (x , v z)} {σ ≺+ (z , N)} 
  = lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , N)} {(σ ≺+ (z , N)) ∘ (ι ≺+ (x , v z))} (∼*ρ , lemma)
  where
  lemma : (w : V) → w * M → (σ ≺+ (x , N)) w ≡ (((σ ≺+ (z , N)) ∘ (ι ≺+ (x , v z))) w) -- este me sirve ???
  lemma w wfreeM with x ≟ w
  ... | no x≢w  with z ≟ w
  ... | no _    = refl
  ... | yes z≡w = ⊥-elim ((z≢w x z w M z#λxM wfreeM x≢w) z≡w)
    where
    z≢w : (x z w : V)(M : Λ) → z # (ƛ x M) → w * M → x ≢ w  → z ≢ w
    z≢w x .x w M #ƛ≡ wfreeM x≢w = x≢w
    z≢w x z w M (#ƛ  z#M) wfreeM x≢w with z ≟ w
    ... | no z≢w = z≢w
    z≢w x z .z M (#ƛ  z#M) zfreeM x≢w
        | yes refl = ⊥-elim ((lemma-free→¬# zfreeM) z#M)
  lemma w wfreeM
      | yes _ with z ≟ z 
  ... | yes _   = refl
  ... | no z≢z  = ⊥-elim (z≢z refl)
--
corollarylemma≺+ : {x y : V}{M : Λ} → y # ƛ x M → (M ∙ ι ≺+ (x , v y)) ∙ ι ≺+ (y , v x) ≡ M ∙ ι ≺+ (x , v x)
corollarylemma≺+ {x} {y} {M} y#ƛxM = sym (lemma≺+ y#ƛxM)
--
lemma≺+ι : {x y : V}{M : Λ} → y # ƛ x M → (M ∙ ι ≺+ (x , v y)) ∙ ι ≺+ (y , v x) ≡ M ∙ ι 
lemma≺+ι {x} {y} {M} y#ƛxM = begin≡
                               (M ∙ ι ≺+ (x , v y)) ∙ ι ≺+ (y , v x)
                             ≡⟨ corollarylemma≺+ y#ƛxM ⟩
                               M ∙ ι ≺+ (x , v x)
                             ≡⟨ lemmaMι≺+x,x {x} {M} ⟩
                               M ∙ ι 
                             ◻
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
open PreR ≈-preorder∼ public

lemma-σ⇂ : {M : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → ((ι ∘ σ) , M) ≅⇂ ((ι ∘ σ') , M)
lemma-σ⇂ σ∼σ'⇂M  = ∼*ρ , (λ x xfreeM → lemmaM∼M'→Mσ≡M'σ (σ∼σ'⇂M  x xfreeM))
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



\begin{code}
lemma∙ι : {M : Λ} → M ∼α M ∙ ι
lemma∙ι {M} =  lemmaMι≡M'ι→M∼M' ( begin≡
                                    M ∙ ι
                                  ≡⟨ lemma1 {M} {ι} {ι ∘ ι} (∼*ρ , (λ _ _ → refl) ) ⟩
                                    M ∙ (ι ∘ ι)
                                  ≡⟨  sym (lemma· {M} {ι} {ι}) ⟩
                                    (M ∙ ι) ∙ ι
                                  ◻)
\end{code}

\begin{code}
lemma∼λ : {M N : Λ}{x : V} → M ∼α N → ƛ x M ∼α ƛ x N
lemma∼λ {M} {N} {x} M∼N = ∼ƛ #ƛ≡ #ƛ≡ lemma∼ƛaux
  where
  lemma∼ƛaux : M ∙ ι ≺+ (x , v x) ∼α N ∙ ι ≺+ (x , v x)
  lemma∼ƛaux rewrite lemmaM∼M'→Mσ≡M'σ {σ = ι ≺+ (x , v x)} M∼N = ∼ρ
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
              (lemma⇀ (lemmaι≺+⇀ Γ⊢N:α))
\end{code}
%</typebetaproof>

%<*typeiota>
\begin{code}
lemma⊢ι  :  {Γ : Cxt}{α : Type}{M : Λ} 
         →  Γ ⊢ M ∙ ι ∶ α → Γ ⊢ M ∶ α
lemma⊢ι {M = v x}    Γ⊢x:α     = Γ⊢x:α
lemma⊢ι {M = M · N}  (⊢· Γ⊢Mι:α⟶β Γ⊢Nι:α) 
  = ⊢· (lemma⊢ι Γ⊢Mι:α⟶β) (lemma⊢ι Γ⊢Nι:α)
lemma⊢ι {M = ƛ x M}  (⊢ƛ Γ,y:α⊢Mι≺+x,y:α)  
  with lemma⊢σM Γ,y:α⊢Mι≺+x,y:α (lemmaι≺+⇀y {x = x} {χ (ι , ƛ x M)} {M})
... | Γ,x:α⊢Mι≺+x,yι≺y,x:β rewrite lemma≺+ι (lemma-χι (ƛ x M))
  = ⊢ƛ (lemma⊢ι Γ,x:α⊢Mι≺+x,yι≺y,x:β)
\end{code}
%</typeiota>

%<*typealpha>
\begin{code}
lemma⊢α  :  {Γ : Cxt}{α : Type}{M N : Λ} 
         →  M ∼α N → Γ ⊢ M ∶ α → Γ ⊢ N ∶ α
\end{code}
%</typealpha>

%<*typealphaproof>
\begin{code}
lemma⊢α {M = M} {N = N} M∼N Γ⊢M 
  with M ∙ ι    | lemma⊢σM Γ⊢M (lemma⇀ lemmaι⇀)  | lemmaM∼M'→Mσ≡M'σ {σ = ι} M∼N 
... | .(N ∙ ι)  | Γ⊢N∙ι                 | refl 
  = lemma⊢ι Γ⊢N∙ι
\end{code}
%</typealphaproof>

\begin{code}
infix 1 _∼ασ_
_∼ασ_ : Σ → Σ → Set
σ ∼ασ σ' = (x : V) → σ x ∼α σ' x

lemma∼ασ : {σ σ' : Σ}{M : Λ} → σ ∼ασ σ' → σ ∼α σ' ⇂ M
lemma∼ασ σ∼ασ' x x*M = σ∼ασ' x

lemmaι∘σ : {σ : Σ} → ι ∘ σ ∼ασ σ 
lemmaι∘σ {σ} x = begin
                   σ x ∙ ι
                 ∼⟨ ∼σ (lemma∙ι) ⟩
                   σ x
                 ∎

lemma∼≺+ : {x : V}{N : Λ}{σ σ' : Σ} → σ ∼ασ σ' → σ ≺+ (x , N) ∼ασ σ' ≺+ (x , N)
lemma∼≺+ {x} σ∼σ' y with x ≟ y
... | yes  _ = ∼ρ
... | no   _ = σ∼σ' y

prop8 : {x y : V}{σ : Σ}{M N : Λ} → y #⇂ (σ , ƛ x M) → (ι ≺+ (y , N) ∘ σ ≺+ (x , v y)) ∼α σ ≺+ (x , N) ⇂ M
prop8 {x} {y} {σ} {M} {N} y#⇂ƛxM z z*M =
                begin
                  (ι ≺+ (y , N) ∘ σ ≺+ (x , v y)) z
                ≈⟨ lemmaσ∘≺+ M N σ ι x y y#⇂ƛxM z z*M ⟩
                  ((ι ∘ σ) ≺+ (x , N)) z
                ∼⟨ (lemma∼≺+ {x} {N} (lemmaι∘σ {σ})) z ⟩
                  (σ ≺+ (x , N)) z
                ∎

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
     ∼⟨ lemma-subst-σ∼ (prop8 y#⇂σ,ƛxM) ⟩
       M ∙ σ ≺+ (x , N)
     ∎
 \end{code}


Corollary 4-2 

\begin{code}
corollary4-2  : {x y : V}{M : Λ}{σ : Σ}
              → y #⇂ (σ , ƛ x M) 
              → ƛ x M ∙ σ ∼α ƛ y (M ∙ σ ≺+ (x , v y))
corollary4-2 {x} {y} {M} {σ} y#⇂σ,ƛxM 
  = begin
      ƛ x M ∙ σ
    ≈⟨ refl ⟩
      ƛ z (M ∙ σ ≺+ (x , v z))
    ∼⟨ ∼ƛ  {y = w} w#ƛzM∙σ≺+x,z w#ƛyM∙σ≺+x,y 
           (begin
             (M ∙ σ ≺+ (x , v z)) ∙ ι ≺+ (z , v w)
           ∼⟨ corollary1SubstLemma z#⇂σ,ƛxM  ⟩
             M ∙ σ ≺+ (x , v w)
           ∼⟨ ∼σ (corollary1SubstLemma y#⇂σ,ƛxM) ⟩
             (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , v w)
           ∎)         ⟩
      ƛ y (M ∙ σ ≺+ (x , v y))
    ∎
  where 
  z = χ (σ , ƛ x M)
  z#⇂σ,ƛxM : z #⇂ (σ , ƛ x M)
  z#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
  w : V
  w = χ' (fv (ƛ z (M ∙ σ ≺+ (x , v z))) ++ fv (ƛ y (M ∙ σ ≺+ (x , v y))))
  w#ƛzM∙σ≺+x,z : w # ƛ z (M ∙ σ ≺+ (x , v z))
  w#ƛzM∙σ≺+x,z = lemma∉fv→# (c∉xs++ys→c∉xs  {w} {fv (ƛ z (M ∙ σ ≺+ (x , v z)))} 
                                            (lemmaχ∉ (fv (ƛ z (M ∙ σ ≺+ (x , v z))) ++ fv (ƛ y (M ∙ σ ≺+ (x , v y))))))
  w#ƛyM∙σ≺+x,y : w # ƛ y (M ∙ σ ≺+ (x , v y))
  w#ƛyM∙σ≺+x,y = lemma∉fv→# (c∉xs++ys→c∉ys  {w} {fv (ƛ z (M ∙ σ ≺+ (x , v z)))} {fv (ƛ y (M ∙ σ ≺+ (x , v y)))} 
                                            (lemmaχ∉ (fv (ƛ z (M ∙ σ ≺+ (x , v z))) ++ fv (ƛ y (M ∙ σ ≺+ (x , v y))))))
\end{code}

%<*naivesubstitution>
\begin{code}
lemmaƛ∼[] : {x : V}{M : Λ}{σ : Σ} → x #⇂ (σ , M) → σ x ≡ v x
  → ƛ x M ∙ σ ∼α  ƛ x (M ∙ σ)
lemmaƛ∼[] {x} {M} {σ} x#⇂σ,M σx≡x
  =  begin
       ƛ x M ∙ σ
     ∼⟨ corollary4-2 {x} {x} {M} {σ} (λ { y (*ƛ y*M _) → x#⇂σ,M y y*M }) ⟩
       ƛ x (M ∙ σ ≺+ (x , v x))
     ∼⟨ ∼ƛ {y = y} y#ƛxM∙σ≺+x,x y#ƛyM∙σ
                   (begin
                     (M ∙ σ ≺+ (x , v x)) ∙ ι ≺+ (x , v y)
                   ≈⟨ lemmaM∼M'→Mσ≡M'σ  {M ∙ σ ≺+ (x , v x)} {M ∙ σ} {ι ≺+ (x , v y)}
                                        (begin
                                          M ∙ σ ≺+ (x , v x)
                                        ≈⟨ lemmaσ≡σ'→Mσ≡Mσ' {M} (∼*ρ , lemma) ⟩
                                          M ∙ σ
                                        ∎) ⟩
                      (M ∙ σ) ∙ ι ≺+ (x , v y)
                   ∎) ⟩
       ƛ x (M ∙ σ)
     ∎
  where
  y = χ' (fv (ƛ x (M ∙ σ ≺+ (x , v x))) ++ fv (ƛ x (M ∙ σ)))
  y#ƛxM∙σ≺+x,x : y # ƛ x (M ∙ σ ≺+ (x , v x))
  y#ƛxM∙σ≺+x,x = lemma∉fv→# (c∉xs++ys→c∉xs  {y} {fv (ƛ x (M ∙ σ ≺+ (x , v x)))} 
                                            (lemmaχ∉ (fv (ƛ x (M ∙ σ ≺+ (x , v x))) ++ fv (ƛ x (M ∙ σ)))))
  y#ƛyM∙σ : y # ƛ x (M ∙ σ)
  y#ƛyM∙σ = lemma∉fv→# (c∉xs++ys→c∉ys  {y} {fv (ƛ x (M ∙ σ ≺+ (x , v x)))} {fv (ƛ x (M ∙ σ))} 
                                       (lemmaχ∉ (fv (ƛ x (M ∙ σ ≺+ (x , v x))) ++ fv (ƛ x (M ∙ σ)))))
  lemma : (z : V) → z * M → (σ ≺+ (x , v x)) z ≡ σ z
  lemma z z*M with x ≟ z
  ... | no _      = refl
  lemma .x x*M
      | yes refl  = sym σx≡x
\end{code}
%</naivesubstitution>

Parallel reduction

\begin{code}
lemma[]≡ :  {x y z : V}{M N : Λ}(u : V) → z # ƛ x M → z # ƛ y N
            → M [ x / v z ] ≡ N [ y / v z ] 
            → M [ x / v u ] ≡ N [ y / v u ]
lemma[]≡ {x} {y} {z} {M} {N} u z#ƛxM z#ƛyN M[x/z]≡N[y/z]
  = begin≡
      M [ x / v u ]
    ≡⟨ lemma≺+ z#ƛxM ⟩
      (M [ x / v z ]) [ z / v u ]
    ≡⟨ cong (λ e → e [ z / v u ]) M[x/z]≡N[y/z] ⟩
      (N [ y / v z ]) [ z / v u ]
    ≡⟨ sym (lemma≺+ z#ƛyN) ⟩
      N [ y / v u ]
    ◻
--
lemmaλα :  {x y z : V}{M N : Λ}
              → ƛ x M ∼α ƛ y N
              → M [ x / v z ] ≡ N [ y / v z ]
lemmaλα {x} {y} {z} (∼ƛ {M} {N} .{x} .{y} {w} w#ƛxM w#ƛyN M[x/w]∼N[y/w])
  = begin≡
      M [ x / v z ]
    ≡⟨ lemma≺+ w#ƛxM ⟩
      (M [ x / v w ]) [ w / v z ]
    ≡⟨ lemmaM∼M'→Mσ≡M'σ {σ = ι ≺+ (w , v z)} M[x/w]∼N[y/w] ⟩
      (N [ y / v w ]) [ w / v z ]
    ≡⟨ sym (lemma≺+ w#ƛyN) ⟩
       N [ y / v z ]
    ◻
--    
corollaryλα : {x : V}{M N : Λ}
              → ƛ x M ∼α N
              → ∃ (λ P → ∃ (λ y → ∃ (λ z → N ≡ ƛ y P × z # ƛ x M × z # ƛ y P × (M [ x / v z ] ≡ P [ y / v z ]))))
corollaryλα (∼ƛ {M} {P} {x} {y} {z} z#ƛxM z#ƛyP M[x/z]∼P[y/z])
  =  P , y , z , refl , z#ƛxM , z#ƛyP , lemmaλα (∼ƛ {M} {P} {x} {y} {z} z#ƛxM z#ƛyP M[x/z]∼P[y/z])               
--
lemma∼⇉ : {M N P : Λ} → M ∼α N → N ⇉ P → M ⇉ P
lemma∼⇉  ∼v           
         (⇉v x) 
  = ⇉v x
lemma∼⇉  (∼· N∼M N'∼M') 
         (⇉· M⇉P M'⇉P') 
  = ⇉· (lemma∼⇉ N∼M M⇉P) (lemma∼⇉ N'∼M' M'⇉P') 
lemma∼⇉  {ƛ w M} {ƛ x N} {ƛ y P}
         ƛwM∼ƛxN
         (⇉ƛ .x .y z .{N} .{P} z#λxN z#ƛyP N[x/z]⇉P[y/z])
  = ⇉ƛ w y z z#ƛwM z#ƛyP M[w/z]⇉P[y/z]
  where
  z#ƛwM = lemmaM∼N# (∼σ ƛwM∼ƛxN) z z#λxN
  M[w/z]⇉P[y/z] : M [ w / v z ] ⇉ P [ y / v z ]
  M[w/z]⇉P[y/z] rewrite lemmaλα {z = z} ƛwM∼ƛxN = N[x/z]⇉P[y/z]
lemma∼⇉  (∼· {N' = N'} (∼ƛ {M} {N} {y} {y = z} z#ƛyM z#ƛxN M[y/z]∼N[x/z]) M'∼N')
         (⇉β x w .{N} {P} .{N'} {P'} w#ƛxN N[z/w]⇉P N'⇉P' _)
  = {!!} --= ⇉β y w w#ƛyM M[w/z]⇉P[y/z] (lemma∼⇉ M'∼N' N'⇉P')
  where
  w#ƛyM = lemmaM∼N# (∼σ (∼ƛ z#ƛyM z#ƛxN M[y/z]∼N[x/z])) w w#ƛxN
  M[w/z]⇉P[y/z] : M [ y / v w ] ⇉ P 
  M[w/z]⇉P[y/z] rewrite lemmaλα {z = w} (∼ƛ z#ƛyM z#ƛxN M[y/z]∼N[x/z]) = N[z/w]⇉P
\end{code}


\begin{code}
lemma⇉#⇂ : {x x' y : V}{M M' : Λ}{σ σ' : Σ} → ƛ x M ⇉ ƛ x' M' → σ ⇉ₛ σ' → y #⇂ (σ , ƛ x M) → y #⇂ (σ' , ƛ x' M')
lemma⇉#⇂ {x} ƛxM⇉ƛx'M' σ⇉σ' y#⇂σ,ƛxM z z*ƛxM' = lemma⇉# (y#⇂σ,ƛxM z (lemma⇉* z*ƛxM' ƛxM⇉ƛx'M')) (σ⇉σ' z) 

lemmaσ≺+[] :  {M N : Λ}{x y z : V}{σ : Σ}
              → y # ƛ x M → z #⇂ (σ , ƛ x M)
              → (M ∙ σ ≺+ (x , v z)) [ z / N ] ∼α (M [ x / v y ]) ∙ σ ≺+ (y , N)
lemmaσ≺+[] {M} {N} {x} {y} {z} {σ} y#ƛxM z#σ,ƛxM
  = begin 
      (M ∙ σ ≺+ (x , v z)) [ z / N ]
    ∼⟨ corollary1SubstLemma z#σ,ƛxM ⟩
      M ∙ σ ≺+ (x , N)
    ≈⟨ lemma≺+ y#ƛxM ⟩
      (M [ x / v y ]) ∙ σ ≺+ (y , N)
    ∎

lemma⇉  : {M M' : Λ}{σ σ' : Σ} 
        → M ⇉ M' → σ ⇉ₛ σ' 
        → M ∙ σ ⇉ M' ∙ σ'
lemma⇉  (⇉v x)                                             σ⇉σ' 
  = σ⇉σ' x
lemma⇉  (⇉· M⇉M' N⇉N')                                     σ⇉σ' 
  = ⇉· (lemma⇉ M⇉M' σ⇉σ') (lemma⇉ N⇉N' σ⇉σ')
lemma⇉  {σ = σ} {σ'}
        (⇉ƛ x y z {M} {M'} z#ƛxM z#ƛyN M[x/z]⇉M'[y/z])     σ⇉σ'
  = {!!}
  -- = ⇉ƛ u w t t#ƛxMσ t#ƛyM'σ'
  --      (⇉α  (lemma∼⇉ (lemmaσ≺+[] z#ƛxM u#σ,ƛxM) (lemma⇉ M[x/z]⇉M'[y/z] (lemma⇉s z t σ⇉σ')))
  --           (∼σ (lemmaσ≺+[] z#ƛyN w#σ',ƛyM')))
  where
  u : V
  u = χ (σ , ƛ x M)
  u#σ,ƛxM : u #⇂ (σ , ƛ x M)
  u#σ,ƛxM = χ-lemma2 σ (ƛ x M)
  w : V
  w = χ (σ' , ƛ y M')
  w#σ',ƛyM' : w #⇂ (σ' , ƛ y M')
  w#σ',ƛyM' = χ-lemma2 σ' (ƛ y M')
  t : V
  t = χₜ (((ƛ x M) ∙ σ) · ((ƛ y M') ∙ σ'))
  t#ƛxMσ : t # (ƛ x M) ∙ σ 
  t#ƛxMσ with lemmaχₜ# {((ƛ x M) ∙ σ) · ((ƛ y M') ∙ σ')}
  ... | #· t# _ = t#
  t#ƛyM'σ' : t # (ƛ y M') ∙ σ' 
  t#ƛyM'σ' with lemmaχₜ# {((ƛ x M) ∙ σ) · ((ƛ y M') ∙ σ')}
  ... | #· _ t# = t#
lemma⇉  {σ = σ} {σ'}
        (⇉β x z {M} {M'} {N} {N'} z#ƛxM M[x/z]⇉M' N⇉N' _)     σ⇉σ'
  = {!!}
  -- = ⇉α (⇉β y w w#ƛxMσ (lemma∼⇉ (lemmaσ≺+[] z#ƛxM y#σ,ƛxM) (lemma⇉ M[x/z]⇉M' (lemma⇉s z w σ⇉σ'))) (lemma⇉ N⇉N' σ⇉σ'))
  --      lemma∼
  where 
  y : V
  y = χ (σ , ƛ x M)
  y#σ,ƛxM : y #⇂ (σ , ƛ x M)
  y#σ,ƛxM = χ-lemma2 σ (ƛ x M)
  w : V
  w = χₜ (((ƛ x M) ∙ σ) · ((ƛ z M') ∙ σ')) 
  w#ƛxMσ : w # (ƛ x M) ∙ σ
  w#ƛxMσ with lemmaχₜ# {((ƛ x M) ∙ σ) · ((ƛ z M') ∙ σ')}
  ... | #· t# _ = t#
  w#ƛzM'σ : w #⇂ (σ' , ƛ z M')
  w#ƛzM'σ with lemmaχₜ# {((ƛ x M) ∙ σ) · ((ƛ z M') ∙ σ')}
  ... | #· _ t# = lemma#→free# t#
  lemma∼ : (M' ∙ σ' ≺+ (z , v w)) [ w / N' ∙ σ' ] ∼α M' [ z / N' ] ∙ σ'
  lemma∼ = begin
             (M' ∙ σ' ≺+ (z , v w)) [ w / N' ∙ σ' ]
           ∼⟨ corollary1SubstLemma w#ƛzM'σ ⟩
             M' ∙ σ' ≺+ (z , N' ∙ σ' )
           ≈⟨ corollary1Prop7 {M'} {N'} {σ'} {z} ⟩
             M' [ z / N' ] ∙ σ'
           ∎
\end{code}
