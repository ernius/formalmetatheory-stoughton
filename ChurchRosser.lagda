\begin{code}
module ChurchRosser where

open import Chi
open import Term
open import Substitution
open import SubstitutionLemmas
open import Alpha
open import Beta
open import NaturalProp
open import ParallelReduction
open import ListProperties
open import Relation Λ hiding (_++_) renaming (_⊆_ to _⊆R_)

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Function hiding (_∘_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; setoid)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)
open import Data.List hiding (any) renaming (length to length') 
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡ 
\end{code}


%<*noalphaparallel>
\begin{code}
noα : {M N : Λ} → M ⇉ N → Set
noα (⇉v _)            = ⊤
noα (⇉ƛ _ M⇉N)        = noα M⇉N
noα (⇉· M⇉N M'⇉N')    = noα M⇉N × noα M'⇉N'
noα (⇉β x M⇉N M'⇉N')  = noα M⇉N × noα M'⇉N'
noα (⇉α _ _)          = ⊥
\end{code}
%</noalphaparallel>

%<*noalphaparallellemma>
\begin{code}
lemma⇉noα :  {M N : Λ} → M ⇉ N
             → ∃ (λ P → P ∼α N × Σₓ (M ⇉ P) (λ M⇉P → noα M⇉P))
\end{code}
%</noalphaparallellemma>

\begin{code}
lemma⇉noα (⇉v x) 
  = v x , ∼v , ⇉v x , tt
lemma⇉noα (⇉ƛ x M⇉N) 
  with lemma⇉noα M⇉N
... | Q , Q~N , M⇉Q , noαM⇉Q
  = ƛ x Q , lemma∼λ Q~N , ⇉ƛ x M⇉Q , noαM⇉Q
lemma⇉noα (⇉· M⇉N M'⇉N') 
  with lemma⇉noα M⇉N | lemma⇉noα M'⇉N'
... | Q   , Q∼N    , M⇉Q    , noαM⇉Q  
    | Q'  , Q'∼N'  , M'⇉Q'  , noαM'⇉Q'  
  = Q · Q' , ∼· Q∼N Q'∼N' , ⇉· M⇉Q M'⇉Q' , noαM⇉Q , noαM'⇉Q'  
lemma⇉noα (⇉β x M⇉N M'⇉N') 
  with lemma⇉noα M⇉N | lemma⇉noα M'⇉N'
... | Q   , Q∼N    , M⇉Q    , noαM⇉Q  
    | Q'  , Q'∼N'  , M'⇉Q'  , noαM'⇉Q'  
  =  Q ∙ ι ≺+ (x , Q') , 
     lemma-subst Q∼N (lemma≺+∼α⇂ {x} lemmaι∼α⇂ Q'∼N') , 
     ⇉β x M⇉Q M'⇉Q' , 
     noαM⇉Q , noαM'⇉Q'  
lemma⇉noα (⇉α M⇉N' N'~P) 
  with lemma⇉noα M⇉N'
... | Q , Q~N' , M⇉Q , noαM⇉Q
  = Q , ∼τ Q~N' N'~P  , M⇉Q , noαM⇉Q
\end{code}

\begin{code}
lemmaλxM∼λyN→M∼N[y/x] : {x y : V}{M N : Λ} → ƛ x M ∼α ƛ y N → M ∼α N ∙ ι ≺+ (y , v x)
lemmaλxM∼λyN→M∼N[y/x] {x} {y} {M} {N} (∼ƛ {y = z} z#λxM z#λyN M[x/z]∼N[y/z])
  =  begin
       M
     ∼⟨ lemma∙ι ⟩
       M ∙ ι
     ≈⟨ sym (lemma≺+ι z#λxM) ⟩ 
       (M ∙ ι ≺+ (x ∶ v z)) ∙ ι ≺+ (z ∶ v x)
     ∼⟨ lemma-subst {σ = ι ≺+ (z , v x)} {σ' = ι ≺+ (z , v x)} M[x/z]∼N[y/z] lemma∼α⇂ρ ⟩
       (N ∙ ι ≺+ (y ∶ v z)) ∙ ι ≺+ (z ∶ v x)
     ≈⟨ sym (lemma≺+ z#λyN) ⟩
       N ∙ ι ≺+ (y , v x)
     ∎
--
-- lemmaλxM∼λyN←M∼N[y/x] : {x y : V}{M N : Λ} → x # ƛ y N → M ∼α N ∙ ι ≺+ (y , v x) →  ƛ x M ∼α ƛ y N 
-- lemmaλxM∼λyN←M∼N[y/x] {x} {y} {M} {N} x#ƛyN M~N[y/x] 
--   = ∼ƛ  z#ƛxM z#ƛyN 
--         (begin
--           M ∙ ι ≺+ (x , v z) 
--         ∼⟨ lemma-subst M~N[y/x] lemma∼α⇂ρ  ⟩
--           (N ∙ ι ≺+ (y , v x)) ∙ ι ≺+ (x , v z)
--         ≈⟨ sym (lemma≺+ {y} {x} {N} {v z} {ι} x#ƛyN) ⟩
--           N ∙ ι ≺+ (y ∶ v z)
--         ∎)
--   where 
--   z = χₜ (ƛ x M · ƛ y N)
--   z#ƛxM : z # ƛ x M
--   z#ƛxM with lemmaχₜ# {ƛ x M · ƛ y N}
--   ... | #· z# _ = z# 
--   z#ƛyN : z # ƛ y N
--   z#ƛyN with lemmaχₜ# {ƛ x M · ƛ y N}
--   ... | #· _ z# = z# 
\end{code}

%<*parallellnoalphaeftalpha>
\begin{code}
lemma⇉noααleft : {M N P : Λ} → M ∼α N → (N⇉P : N ⇉ P) → noα N⇉P → M ⇉ P
\end{code}
%</parallellnoalphaeftalpha>

\begin{code}
lemma⇉noααleft            _                               (⇉α _ _)             ()
lemma⇉noααleft  {v .x}    ∼v                              (⇉v x)     _         = ⇉v x
lemma⇉noααleft  {M · M'}  (∼· M~N M'~N')                  (⇉· N⇉P N'⇉P')       (noαN⇉P , noαN'⇉P') 
  = ⇉· (lemma⇉noααleft M~N N⇉P noαN⇉P) (lemma⇉noααleft M'~N' N'⇉P' noαN'⇉P')
lemma⇉noααleft  {.(ƛ x M) · M'}  
                (∼· (∼ƛ {M} {N} {x = x} {y = z} z#λxM z#λyN M[x/z]∼N[y/z]) M'~N')                  
                (⇉β y {M' = P} {N' = P'} N⇉P N'⇉P')     
                (noαN⇉P , noαN'⇉P') 
  = ƛxMM'⇉P[y/P'] 
  where
  M~N[y/x] : M ∼α N ∙ ι ≺+ (y , v x)
  M~N[y/x] = lemmaλxM∼λyN→M∼N[y/x] (∼ƛ {M} {N} {x = x} {y = z} z#λxM z#λyN M[x/z]∼N[y/z])
  N[y/x]⇉P[y/x] : N ∙ ι ≺+ (y , v x) ⇉ P ∙ ι ≺+ (y , v x)
  N[y/x]⇉P[y/x] = lemma⇉ N⇉P lemma⇉ₛρ
  Q : Λ
  Q = proj₁ (lemma⇉noα N[y/x]⇉P[y/x])
  Q~P[y/x] : Q ∼α P ∙ ι ≺+ (y , v x)
  Q~P[y/x] = proj₁ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x]))
  N[y/x]⇉Q : N ∙ ι ≺+ (y , v x) ⇉ Q
  N[y/x]⇉Q =  proj₁ (proj₂ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x])))
  noαN[y/x]⇉Q : noα N[y/x]⇉Q
  noαN[y/x]⇉Q = proj₂ (proj₂ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x])))
  M⇉P[y/x] : M ⇉ P ∙ ι ≺+ (y , v x)
  M⇉P[y/x] = ⇉α (lemma⇉noααleft {M} M~N[y/x] N[y/x]⇉Q noαN[y/x]⇉Q) Q~P[y/x]
  M'⇉P' : M' ⇉ P'
  M'⇉P' = lemma⇉noααleft M'~N' N'⇉P' noαN'⇉P'
  x#ƛyP : x # ƛ y P
  x#ƛyP = lemma⇉# (lemmaM∼N# (∼ƛ {M} {N} {x = x} z#λxM z#λyN M[x/z]∼N[y/z]) x #ƛ≡) (⇉ƛ y N⇉P) 
  ƛxMM'⇉P[y/P'] : ƛ x M · M' ⇉ P ∙ ι ≺+ (y , P')
  ƛxMM'⇉P[y/P'] rewrite lemma≺+ {y} {x} {P} {P'} {ι} x#ƛyP = ⇉β x M⇉P[y/x] M'⇉P'
lemma⇉noααleft  {ƛ x M}   (∼ƛ .{M} {N} .{x} {y} {z} z#ƛxM z#λyN M[x/z]~N[y/z])  
                (⇉ƛ .y .{N} {P} N⇉P)     
                noαN⇉Q
  = ⇉α ƛxM⇉ƛxP[y/x] ƛxP[y/x]∼ƛyP
  where
  M∼N[y/x] : M ∼α N ∙ ι ≺+ (y , v x)
  M∼N[y/x] = lemmaλxM∼λyN→M∼N[y/x] (∼ƛ {M} {N} {x} {y} {z} z#ƛxM z#λyN M[x/z]~N[y/z])
  N[y/x]⇉P[y/x] : N  ∙ ι ≺+ (y , v x) ⇉ P  ∙ ι ≺+ (y , v x)
  N[y/x]⇉P[y/x] = lemma⇉ N⇉P lemma⇉ₛρ
  Q : Λ
  Q = proj₁ (lemma⇉noα N[y/x]⇉P[y/x])
  Q~P[y/x] : Q ∼α P ∙ ι ≺+ (y , v x)
  Q~P[y/x] = proj₁ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x]))
  N[y/x]⇉Q : N ∙ ι ≺+ (y , v x) ⇉ Q
  N[y/x]⇉Q =  proj₁ (proj₂ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x])))
  noαN[y/x]⇉Q : noα N[y/x]⇉Q
  noαN[y/x]⇉Q = proj₂ (proj₂ (proj₂ (lemma⇉noα N[y/x]⇉P[y/x])))
  ƛxM⇉ƛxP[y/x] : ƛ x M ⇉ ƛ x (P ∙ ι ≺+ (y , v x))
  ƛxM⇉ƛxP[y/x] = ⇉ƛ x (⇉α (lemma⇉noααleft M∼N[y/x] N[y/x]⇉Q noαN[y/x]⇉Q) Q~P[y/x])
  x#ƛyP : x # ƛ y P
  x#ƛyP = lemma⇉# (lemmaM∼N# (∼ƛ {M} {N} {x} {y} {z} z#ƛxM z#λyN M[x/z]~N[y/z]) x #ƛ≡) (⇉ƛ y {N} {P} N⇉P)
  ƛxP[y/x]∼ƛyP :  ƛ x (P ∙ ι ≺+ (y , v x)) ∼α ƛ y P
  ƛxP[y/x]∼ƛyP = ∼σ (corollary4-2' x#ƛyP)
\end{code}

%<*parallelleftalpha>
\begin{code}
lemma⇉αleft : {M N P : Λ} → M ∼α N → N ⇉ P → M ⇉ P
\end{code}
%</parallelleftalpha>

\begin{code}
lemma⇉αleft M~N N⇉P with lemma⇉noα N⇉P 
... | Q , Q~P , N⇉Q , noαN⇉Q = ⇉α (lemma⇉noααleft M~N N⇉Q noαN⇉Q) Q~P
\end{code}

%<*paralleldiamondnoalpha>
\begin{code}
diam⇉noα :  {M N P : Λ} → (M⇉N : M ⇉ N) → (M⇉P : M ⇉ P) 
            → noα M⇉N → noα M⇉P 
            → ∃ (λ Q → N ⇉ Q × P ⇉ Q)
\end{code}
%</paralleldiamondnoalpha>

\begin{code}
diam⇉noα _      (⇉α _ _) _ ()
diam⇉noα (⇉α _ _) _ () _
diam⇉noα (⇉v x) (⇉v .x) _ _ = v x , ⇉v x , ⇉v x
diam⇉noα (⇉ƛ x M⇉N) (⇉ƛ .x M⇉P) noαM⇉N noαM⇉P 
  with diam⇉noα M⇉N M⇉P noαM⇉N noαM⇉P
...  | Q , N⇉Q , P⇉Q
  = ƛ x Q , ⇉ƛ x N⇉Q , ⇉ƛ x P⇉Q 
diam⇉noα (⇉· M⇉N M'⇉N') (⇉· M⇉P M'⇉P') (noαM⇉N , noαM'⇉N') (noαM⇉P , noαM'⇉P') 
  with  diam⇉noα M⇉N    M⇉P    noαM⇉N    noαM⇉P    |
        diam⇉noα M'⇉N'  M'⇉P'  noαM'⇉N'  noαM'⇉P'
...  | Q , N⇉Q , P⇉Q | Q' , N'⇉Q' , P'⇉Q'
  = Q · Q' , ⇉· N⇉Q N'⇉Q' , ⇉· P⇉Q P'⇉Q'
diam⇉noα (⇉· (⇉α _ _) _) (⇉β _ _ _) (() , _) _
diam⇉noα (⇉· (⇉ƛ x M⇉N) M'⇉N') (⇉β .x M⇉P M'⇉P') (noαM⇉N , noαM'⇉N') (noαM⇉P , noαM'⇉P') 
  with  diam⇉noα M⇉N    M⇉P    noαM⇉N    noαM⇉P    |
        diam⇉noα M'⇉N'  M'⇉P'  noαM'⇉N'  noαM'⇉P'
...  | Q , N⇉Q , P⇉Q | Q' , N'⇉Q' , P'⇉Q'
  = Q ∙ ι ≺+ (x , Q') , ⇉β x N⇉Q N'⇉Q' , lemma⇉ P⇉Q (corollary⇉ₛ≺+ x P'⇉Q')
diam⇉noα (⇉β _ _ _)       (⇉· (⇉α _ _) _)  _ (() , _)
diam⇉noα (⇉β x M⇉N M'⇉N') (⇉· (⇉ƛ .x M⇉P) M'⇉P') (noαM⇉N , noαM'⇉N') (noαM⇉P , noαM'⇉P') 
  with  diam⇉noα M⇉N    M⇉P    noαM⇉N    noαM⇉P    |
        diam⇉noα M'⇉N'  M'⇉P'  noαM'⇉N'  noαM'⇉P'
...  | Q , N⇉Q , P⇉Q | Q' , N'⇉Q' , P'⇉Q'
  = Q ∙ ι ≺+ (x , Q') , lemma⇉ N⇉Q (corollary⇉ₛ≺+ x N'⇉Q') , ⇉β x P⇉Q P'⇉Q'
diam⇉noα (⇉β x M⇉N M'⇉N') (⇉β .x M⇉P M'⇉P') (noαM⇉N , noαM'⇉N') (noαM⇉P , noαM'⇉P') 
  with  diam⇉noα M⇉N    M⇉P    noαM⇉N    noαM⇉P    |
        diam⇉noα M'⇉N'  M'⇉P'  noαM'⇉N'  noαM'⇉P'
...  | Q , N⇉Q , P⇉Q | Q' , N'⇉Q' , P'⇉Q'
  = Q ∙ ι ≺+ (x , Q') , lemma⇉ N⇉Q (corollary⇉ₛ≺+ x N'⇉Q') , lemma⇉ P⇉Q (corollary⇉ₛ≺+ x P'⇉Q')
\end{code}

%<*paralleldiamond>
\begin{code}
diam⇉ :  diamond _⇉_
\end{code}
%</paralleldiamond>

\begin{code}
diam⇉ M⇉N M⇉P 
  with lemma⇉noα M⇉N | lemma⇉noα M⇉P 
...  | N' , N'~N , M⇉N' , noαM⇉N' 
     | P' , P'~P , M⇉P' , noαM⇉P' 
  with diam⇉noα M⇉N' M⇉P' noαM⇉N' noαM⇉P' 
...  | Q ,  N'⇉Q , P'⇉Q   
  = Q , lemma⇉αleft (∼σ N'~N) N'⇉Q , lemma⇉αleft (∼σ P'~P) P'⇉Q 
\end{code}

\begin{code}
lemmaCR : cr _→α_
lemmaCR = cr-⊆ lemma→α⊆⇉ lemma⇉⊆→α* (diamond-cr diam⇉)
\end{code}
