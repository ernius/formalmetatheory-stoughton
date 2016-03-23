\begin{code}
module Aster2 where

open import Chi
open import Term
open import Substitution
open import SubstitutionLemmas3
open import Alpha
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

infix   6 _*
\end{code}


\begin{code}
_* : Λ → Λ
(v x        ) * = v x
(ƛ x M      ) * = ƛ x (M *)
((v x)   · M) * = v x · M *
((ƛ x M) · N) * = M * [ x / N * ]
((M · N) · P) * = (M · N) * · P *
\end{code}

Renaming.

\begin{code}
ren : Σ → Set
ren σ = (x : V) → ∃ λ y → σ x ≡ v y
\end{code}

\begin{code}
ren[] : {x y : V} → ren (ι ≺+ (x , v y))
ren[] {x} {y} z with x ≟ z
... | yes _  = y , refl
... | no _   = z , refl
\end{code}

\begin{code}
lemmaren≺+ : {x y : V}{σ : Σ} → ren σ → ren (σ ≺+ (x , v y))
lemmaren≺+ {x} {y} {σ} renσ z with x ≟ z
... | yes _ = y , refl
... | no  _ = renσ z
\end{code}

\begin{code}
lemma** : {x : V}{M : Λ} → x * M * → x * M
lemma** {M = v _        }  *v            = *v
lemma** {M = v _     · N}  (*·l *v)      = *·l *v
lemma** {M = v _     · N}  (*·r x*N*)    = *·r (lemma** x*N*)
lemma** {M = (M · N) · P}  (*·l x*MN*)   = *·l (lemma** x*MN*)
lemma** {M = (M · N) · P}  (*·r x*P*)    = *·r (lemma** x*P*)
lemma** {M = ƛ y M      }  (*ƛ x*M* x≢y) = *ƛ (lemma** x*M*) x≢y
lemma** {x} 
        {ƛ y M · N      }  x*M*[y/N*] 
  with lemmafreeσ→ {x} {M *} x*M*[y/N*]
... | z , z*M* , x*[y/N*]z 
  with y ≟ z
lemma** {x} 
        {ƛ y M · N      }  x*M*[y/N*] 
    | .x , x*M* , *v
    | no  y≢x                            = *·l (*ƛ (lemma** x*M*) y≢x)
lemma** {x} 
        {ƛ y M · N      }  x*M*[y/N*] 
    | .y , y*M* , x*N*
    | yes refl                           = *·r (lemma** x*N*)  
\end{code}

\begin{code}
lemma*#⇂ : {x : V}{M : Λ}{σ : Σ} → x #⇂ (σ , M) → x #⇂ (σ , M *)
lemma*#⇂ {x} {M} {σ} x#⇂ƛxM y y*M* = x#⇂ƛxM y (lemma** y*M*)
\end{code}

\begin{code}
lemma*ren : {M : Λ}{σ : Σ} → ren σ → (M ∙ σ) * ∼α M * ∙ σ
lemma*ren {v x}    {σ} renσ
  =  begin
       (v x ∙ σ) *
     ≈⟨ cong (λ e → e *) σx≡y ⟩
       v y *
     ≈⟨ refl ⟩
       v y 
     ≈⟨ sym σx≡y ⟩
       v x ∙ σ
     ≈⟨ refl ⟩
       v x * ∙ σ
     ∎
 where
 y  = proj₁ (renσ x)
 σx≡y = proj₂ (renσ x)
lemma*ren {ƛ x M}  {σ} renσ 
  =  begin
       ((ƛ x M) ∙ σ) *
     ≈⟨ refl ⟩
       (ƛ y  (M ∙ σ ≺+ (x , v y))) *     
     ≈⟨ refl ⟩
       ƛ y   ((M ∙ σ ≺+ (x , v y)) *)
     ∼⟨ lemma∼λ (lemma*ren {M} (lemmaren≺+ {x} renσ)) ⟩
       ƛ y   (M * ∙ σ ≺+ (x , v y))
     ∼⟨ ∼σ (corollary4-2 (lemma*#⇂ y#ƛxM)) ⟩
       ƛ x (M *) ∙ σ 
     ≈⟨ refl ⟩
       (ƛ x M) * ∙ σ 
     ∎
  where
  y = χ (σ , ƛ x M)
  y#ƛxM = χ-lemma2 σ (ƛ x M)
lemma*ren {v x      · N}  {σ} renσ 
  =  begin
        ((v x · N) ∙ σ) *
      ≈⟨ refl ⟩
        ((v x ∙ σ) · (N ∙ σ)) * 
      ≈⟨ cong (λ e → ( e · (N ∙ σ))*) σx≡y  ⟩
        v y · ((N ∙ σ) *)
      ∼⟨  ∼· ∼v (lemma*ren {N} renσ) ⟩
        v y · (N * ∙ σ)
      ≈⟨ cong (λ e → e · (N * ∙ σ)) (sym σx≡y)  ⟩
        (v x ∙ σ) · (N * ∙ σ)
      ≈⟨ refl ⟩
        (v x · N *) ∙ σ
      ≈⟨ refl ⟩
        (v x · N) * ∙ σ 
      ∎
  where
  y = proj₁ (renσ x)
  σx≡y = proj₂ (renσ x)
lemma*ren {(M · N)  · P}  {σ} renσ 
  =  begin
       (((M · N) · P) ∙ σ) *
     ≈⟨ refl ⟩
       (((M · N) ∙ σ) · (P ∙ σ)) *
     ≈⟨ refl ⟩
       ((M · N) ∙ σ) * · (P ∙ σ) *
     ∼⟨ ∼· ( lemma*ren {M · N} renσ) (lemma*ren {P} renσ) ⟩
       ((M · N) * ∙ σ) · (P * ∙ σ)
     ≈⟨ refl  ⟩
       ((M · N) *) · (P *) ∙ σ
     ≈⟨ refl  ⟩
       ((M · N) · P) * ∙ σ
     ∎
lemma*ren {ƛ x M    · N}  {σ} renσ 
  =  begin
       ((ƛ x M · N) ∙ σ) *
     ≈⟨ refl  ⟩
       (ƛ y (M ∙ σ ≺+ (x , v y)) · (N ∙ σ)) *
     ≈⟨ refl  ⟩
       ((M ∙ σ ≺+ (x , v y))*)   [ y / (N ∙ σ) * ]
     ∼⟨ lemma-subst  {(M ∙ σ ≺+ (x , v y))*} {(M * ∙ σ ≺+ (x , v y))} 
                     (lemma*ren {M} (lemmaren≺+ {x} renσ)) 
                     lemma[y/Nσ*]∼[y/N*σ]                              ⟩
       (M * ∙ σ ≺+ (x , v y))  [ y / N * ∙ σ  ]
     ∼⟨ corollary1SubstLemma (lemma*#⇂ y#ƛxM)  ⟩
       M * ∙ σ ≺+ (x , N * ∙ σ)
     ≈⟨ corollary1Prop7 {M *} {N *} {σ} {x} ⟩
      (M * [ x / N * ]) ∙ σ
     ≈⟨ refl  ⟩
      (ƛ x M · N) * ∙ σ
     ∎
  where
  y = χ (σ , ƛ x M)
  y#ƛxM = χ-lemma2 σ (ƛ x M)
  lemma[y/Nσ*]∼[y/N*σ] : (ι ≺+ (y , (N ∙ σ) *)) ∼α ι ≺+ (y , N * ∙ σ) ⇂ ((M ∙ σ ≺+ (x , v y)) *)
  lemma[y/Nσ*]∼[y/N*σ] z _ with y ≟ z
  ... | yes _ = lemma*ren {N} renσ
  ... | no  _ = ∼v
\end{code}


\begin{code}
lemma⇉aster : {M N : Λ} → M ⇉ N → N ⇉ M *
lemma⇉aster M⇉N = ?
\end{code}


-- \begin{code}
-- open import Data.Unit

