\begin{code}
module Aster where

open import Chi
open import Term
open import Substitution
open import SubstitutionLemmas2
open import Alpha
open import ParallelReduction2
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
open import Data.Unit

⇉no2α : {M N : Λ} → M ⇉ N → Set
⇉no2α (⇉v x)                         = ⊤
⇉no2α (⇉· M⇉N M'⇉N')                 = ⇉no2α M⇉N × ⇉no2α M'⇉N'
⇉no2α (⇉ƛ x y z _ _ M[x/z]⇉N[y/z])   = ⇉no2α M[x/z]⇉N[y/z]
⇉no2α (⇉β x y y#ƛxM M[x/y]⇉M' N⇉N')  = ⇉no2α M[x/y]⇉M' × ⇉no2α N⇉N'
⇉no2α (⇉α (⇉α _ _) _)                = ⊥
⇉no2α (⇉α (⇉v x) N∼P)                = ⊤
⇉no2α (⇉α (⇉· M⇉N M'⇉N') M'N'∼P)     = ⇉no2α M⇉N × ⇉no2α M'⇉N'
⇉no2α (⇉α (⇉ƛ x y z z#λxM z#ƛyN M[x/z]⇉N[y/z]) N∼P) = ⇉no2α M[x/z]⇉N[y/z]
⇉no2α (⇉α (⇉β x y y#ƛxM M[x/y]⇉M' N⇉N') M'[y/N']∼P) = ⇉no2α M[x/y]⇉M'

-- {-# NON_TERMINATING #-}
⇉no2α⇉ : {M N : Λ} → M ⇉ N → Σₓ (M ⇉ N) (λ M⇉N → ⇉no2α M⇉N)
⇉no2α⇉ (⇉v x) =  ⇉v x , tt
⇉no2α⇉ (⇉· M⇉N M'⇉N') 
  = ⇉· (proj₁ recM) (proj₁ recN) , proj₂ recM , proj₂ recN
  where
  recM = ⇉no2α⇉ M⇉N
  recN = ⇉no2α⇉ M'⇉N'
⇉no2α⇉ (⇉ƛ x y z z#ƛxM z#ƛyN M[x/z]⇉N[y/z]) 
  = ⇉ƛ x y z z#ƛxM z#ƛyN (proj₁ recM) , proj₂ recM
  where
  recM = ⇉no2α⇉ M[x/z]⇉N[y/z]
⇉no2α⇉ (⇉β x y y#ƛxM M[x/y]⇉M' N⇉N') 
  = ⇉β x y y#ƛxM (proj₁ recM) (proj₁ recN) , proj₂ recM , proj₂ recN
  where
  recM = ⇉no2α⇉ M[x/y]⇉M'
  recN = ⇉no2α⇉ N⇉N'
⇉no2α⇉ (⇉α (⇉v x) ∼v) 
  = ⇉α (⇉v x) ∼v  , tt 
⇉no2α⇉ (⇉α (⇉· M⇉N M'⇉N') NN'∼PP') 
  = ⇉α (⇉· (proj₁ recM) (proj₁ recN)) NN'∼PP' , proj₂ recM , proj₂ recN 
  where
  recM = ⇉no2α⇉ M⇉N
  recN = ⇉no2α⇉ M'⇉N'
⇉no2α⇉ (⇉α (⇉ƛ x y z z#ƛxM z#ƛyN M[x/z]⇉N[y/z]) ƛyN∼P) 
  = ⇉α (⇉ƛ x y z z#ƛxM z#ƛyN (proj₁ recM)) ƛyN∼P , proj₂ recM
  where
  recM = ⇉no2α⇉ M[x/z]⇉N[y/z]
⇉no2α⇉ (⇉α (⇉β x y z M[x/z]⇉M' N⇉N') M'[z/N']∼P) 
  = ⇉α (⇉β x y z (proj₁ recM) N⇉N') M'[z/N']∼P , proj₂ recM
  where
  recM = ⇉no2α⇉ M[x/z]⇉M'
⇉no2α⇉ (⇉α (⇉α (⇉α M⇉R R∼N) N∼P) P∼Q) = {! ⇉α (proj₁ recM) (∼τ N∼P P∼Q) , ?!} --⇉no2α⇉ (⇉α M⇉N (∼τ N∼P P∼Q))
  where
  recM = ⇉no2α⇉ (⇉α M⇉R R∼N)
⇉no2α⇉ (⇉α (⇉α M⇉N N∼P) P∼Q) = {!!} --⇉no2α⇉ (⇉α M⇉N (∼τ N∼P P∼Q))
\end{code}

\begin{code}
lemma⇉aster' : {M N : Λ} → (M⇉N : M ⇉ N) → ⇉no2α M⇉N → N ⇉ M *
lemma⇉aster' (⇉v x) _
  = ⇉v x
lemma⇉aster' {ƛ x M     · N}  (⇉· (⇉ƛ .x y z z#ƛxM z#ƛyM' M[x/z]⇉M'[y/z]) N⇉N') (no2αƛxM⇉ƛyM' , no2αN⇉N')
  = {!!}
lemma⇉aster' {ƛ x M     · N}  (⇉· (⇉α ƛxM⇉Q Q∼P) N⇉N') (no2αƛxM⇉ƛyM' , no2αN⇉N') 
  = {!!}
--   with lemma∼λ⇉ ƛxM⇉M'
-- lemma⇉aster' {ƛ x M     · N}  (⇉· .{M' = ƛ y M'} .{N} {N'} ƛxM⇉λyM' N⇉N') _
--   | M' , y , z , refl , z#ƛxM , z#ƛyM' , M[x/z]⇉M'[y/z]
--   = ⇉β  y x {M'} {M *} {N'} {N *}
--         (lemma⇉# #ƛ≡ ƛxM⇉λyM')
--         lemma⇉aster'-aux
--         (lemma⇉aster' N⇉N')
--   where
--   lemma⇉aster'-aux : M' [ y / v x ] ⇉ M *
--   lemma⇉aster'-aux  rewrite  lemma≺+ {y} {z} {M'} {v x} {ι} z#ƛyM'
--     = {!!} --⇉α (lemma⇉ (⇉α (lemma⇉aster' M[x/z]⇉M'[y/z]) (lemma*ren {M} {ι ≺+ (x , v z)} ren[])) (lemmaσ⇉σ {ι ≺+ (z , v x)})) {!!}  
lemma⇉aster' {v x       · M}   (⇉· x⇉M N⇉N') (no2αx⇉M , no2αN⇉N')
  = ⇉· (lemma⇉aster' x⇉M no2αx⇉M) (lemma⇉aster' N⇉N' no2αN⇉N') 
lemma⇉aster' {(M · M')  · P}   (⇉· MM'⇉N P⇉P') (no2αMM'⇉N , no2αP⇉P')
  = ⇉· (lemma⇉aster' MM'⇉N no2αMM'⇉N) (lemma⇉aster' P⇉P' no2αP⇉P') 
lemma⇉aster' (⇉ƛ x y z z#λxM z#ƛyN M[x/z]⇉N[y/z]) _
  = {!!}
lemma⇉aster' (⇉β x z z#λxM M[x/z]⇉M' N⇉N') _
  = {!!}
lemma⇉aster' (⇉α M⇉N N∼P) _
  = {!!}

lemma⇉aster : {M N : Λ} → M ⇉ N → N ⇉ M *
lemma⇉aster M⇉N = lemma⇉aster' (proj₁ (⇉no2α⇉ M⇉N)) (proj₂ (⇉no2α⇉ M⇉N)) 
\end{code}


-- \begin{code}
-- open import Data.Unit

-- noƛfrom⇉α : {M N : Λ} → M ⇉ N → Set
-- noƛfrom⇉α (⇉v x)                         = ⊤
-- noƛfrom⇉α (⇉· M⇉N M'⇉N')                 = noƛfrom⇉α M⇉N × noƛfrom⇉α M'⇉N'
-- noƛfrom⇉α (⇉ƛ x y z _ _ M[x/z]⇉N[y/z])   = noƛfrom⇉α M[x/z]⇉N[y/z]
-- noƛfrom⇉α (⇉β x y y#ƛxM M[x/y]⇉M' N⇉N')  = noƛfrom⇉α M[x/y]⇉M' × noƛfrom⇉α N⇉N'
-- noƛfrom⇉α (⇉α {ƛ x M} _  _)              = ⊥
-- noƛfrom⇉α (⇉α {v x}   x⇉N   N∼P)         = noƛfrom⇉α x⇉N
-- noƛfrom⇉α (⇉α {M · N} MN⇉N  N∼P)         = noƛfrom⇉α MN⇉N



-- lemma∼λ⇉ :  {x : V}{M N : Λ} → ƛ x M ⇉ N
--             → ∃ (λ N' → ∃ (λ y → ∃ (λ z →  N ≡ ƛ y N' × z # ƛ x M × z # ƛ y N' × (M [ x / v z ] ⇉ N' [ y / v z ]))))
-- lemma∼λ⇉  (⇉ƛ x y z {M' = N} z#ƛxM z#ƛyN M[x/z]⇉N[y/z])
--   = N , y , z , refl , z#ƛxM , z#ƛyN , M[x/z]⇉N[y/z] 
-- lemma∼λ⇉  (⇉α ƛxM⇉N N∼P)
--   with lemma∼λ⇉ ƛxM⇉N
-- lemma∼λ⇉  (⇉α .{N = ƛ y N} ƛxM⇉ƛyN ƛyN∼P)
--   | N , y , z , refl , z#ƛxM , z#ƛyN , M[x/z]⇉N[y/z] 
--   with corollaryλα ƛyN∼P
-- lemma∼λ⇉  (⇉α .{N = ƛ y N} .{ƛ w P} ƛxM⇉ƛyN ƛyN∼ƛwP)
--   | N , y , z , refl , z#ƛxM , z#ƛyN , M[x/z]⇉N[y/z] 
--   | P , w , u , refl , u#ƛyN , u#ƛwP , N[y/u]≡P[w/u] 
--   rewrite lemma[]≡ z u#ƛyN u#ƛwP N[y/u]≡P[w/u] 
--   =  P , w , z , refl , z#ƛxM , lemmaM∼N# ƛyN∼ƛwP z z#ƛyN , M[x/z]⇉N[y/z] 
-- \end{code}

-- \begin{code}
-- open import NaturalProp
-- --
-- elimƛfrom⇉α :  (n : ℕ) 
--                → ((y : ℕ) → suc y ≤′ n → {M N : Λ} → M ⇉ N → y ≡ length M → Σₓ (M ⇉ N) (λ M⇉N' → noƛfrom⇉α M⇉N'))
--                → {M N : Λ} → M ⇉ N → n ≡ length M → Σₓ (M ⇉ N) (λ M⇉N' → noƛfrom⇉α M⇉N')
-- elimƛfrom⇉α .(suc zero) rec (⇉v x) refl = (⇉v x) , tt
-- elimƛfrom⇉α .(length M + length M') rec {M · M'} (⇉· M⇉N M'⇉N') refl 
--   =  ⇉· (proj₁ recM) 
--         (proj₁ recM') , 
--      proj₂ recM , proj₂ recM'
--   where
--   recM  = (rec (length M) (lemmam>0→m+1≤m+n (length>0  {M'})) M⇉N  refl)
--   recM' = (rec (length M') (lemman>0→n+1≤m+n (length>0 {M}))  M'⇉N' refl)
-- elimƛfrom⇉α .(suc (length M)) rec {ƛ x M} (⇉ƛ .x y z z#λxM z#ƛyN M[x/z]⇉N[y/z]) refl
--   =  ⇉ƛ x y z z#λxM z#ƛyN (proj₁ recM[x/z]) , 
--      proj₂ recM[x/z]
--   where
--   recM[x/z] = rec  (length (M ∙ (ι ≺+ (x , v z)))) 
--                    (lemmam≡n→m+1≤n+1 (lemma-length-corolary {x} {z} {M})) 
--                    M[x/z]⇉N[y/z]
--                    refl
-- elimƛfrom⇉α .(suc zero) rec (⇉α {v x} (⇉v .x) ∼v) refl
--   = ⇉v x , tt
-- elimƛfrom⇉α .(length M + length N) rec {M · N} {P} (⇉α (⇉· ) P∼P') refl
--   = {!!}
-- elimƛfrom⇉α .(length M + length N) rec {M · N} {P} (⇉α (⇉β P∼P') refl
--   = {!!}
-- elimƛfrom⇉α _ _ _ _ = {!!}
-- -- elimƛfrom⇉α (⇉β x y y# M[x/y]⇉N N⇉N') 
-- --   =  ⇉β  x y y# (proj₁ (elimƛfrom⇉α M[x/y]⇉N)) (proj₁ (elimƛfrom⇉α N⇉N')) , 
-- --      proj₂ (elimƛfrom⇉α M[x/y]⇉N) , proj₂ (elimƛfrom⇉α N⇉N')
-- -- elimƛfrom⇉α (⇉α {ƛ x M} {N} ƛxM⇉N  N~P)              
-- --   with lemma∼λ⇉ (⇉α {ƛ x M} ƛxM⇉N  N~P)
-- -- elimƛfrom⇉α (⇉α {ƛ x M} {N} .{ƛ w P} ƛxM⇉N  N~ƛwP)              
-- --   | P , w , z , refl , z#ƛxM , z#ƛwP , M[x/z]⇉P[w/z]
-- --   =  ⇉ƛ x w z z#ƛxM z#ƛwP M[x/z]⇉P[w/z] , 
-- --      {!!} 

-- --elimƛfrom⇉α : {M N : Λ} → M ⇉ N → Σₓ (M ⇉ N) (λ M⇉N' → noƛfrom⇉α M⇉N')
-- \end{code}

-- \begin{code}
-- lemma⇉aster : {M N : Λ} → M ⇉ N → N ⇉ M *
-- lemma⇉aster (⇉v x) 
--   = ⇉v x
-- lemma⇉aster {ƛ x M     · N}  (⇉· ƛxM⇉M' N⇉N')
--   with lemma∼λ⇉ ƛxM⇉M'
-- lemma⇉aster {ƛ x M     · N}  (⇉· .{M' = ƛ y M'} .{N} {N'} ƛxM⇉λyM' N⇉N')  
--   | M' , y , z , refl , z#ƛxM , z#ƛyM' , M[x/z]⇉M'[y/z]
--   = ⇉β  y x {M'} {M *} {N'} {N *}
--         (lemma⇉# #ƛ≡ ƛxM⇉λyM')
--         lemma⇉aster-aux
--         (lemma⇉aster N⇉N')
--   where
--   lemma⇉aster-aux : M' [ y / v x ] ⇉ M *
--   lemma⇉aster-aux  rewrite  lemma≺+ {y} {z} {M'} {v x} {ι} z#ƛyM'
--     = {!!} --⇉α (lemma⇉ (⇉α (lemma⇉aster M[x/z]⇉M'[y/z]) (lemma*ren {M} {ι ≺+ (x , v z)} ren[])) (lemmaσ⇉σ {ι ≺+ (z , v x)})) {!!}  
-- lemma⇉aster {v x       · M}   (⇉· x⇉x M⇉N) 
--   = ⇉· (lemma⇉aster x⇉x)    (lemma⇉aster M⇉N)
-- lemma⇉aster {(M · M')  · P}   (⇉· MM'⇉N P⇉P') 
--   = ⇉· (lemma⇉aster MM'⇉N)  (lemma⇉aster P⇉P')
-- lemma⇉aster (⇉ƛ x y z z#λxM z#ƛyN M[x/z]⇉N[y/z]) 
--   = {!!}
-- lemma⇉aster (⇉β x z z#λxM M[x/z]⇉M' N⇉N') 
--   = {!!}
-- lemma⇉aster (⇉α M⇉N N∼P) 
--   = {!!}
-- \end{code}
