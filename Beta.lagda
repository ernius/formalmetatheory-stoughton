\begin{code}
module Beta where

open import Chi
open import Term
open import Substitution
open import SubstitutionLemmas
open import Alpha
open import Relation Λ hiding (_++_) renaming (_⊆_ to _⊆R_)
open import NaturalProp

open import ListProperties

open import Data.Empty
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
open Any.Membership-≡ hiding (_⊆_)

infix   1 _▹_ 
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
         → Γ ⊢ M ∶ α → M ∼α N → Γ ⊢ N ∶ α
\end{code}
%</typealpha>

%<*typealphaproof>
\begin{code}
lemma⊢α {M = M} {N = N} Γ⊢M M∼N 
  with M ∙ ι    | lemma⊢σM Γ⊢M (lemma⇀ lemmaι⇀)  | lemmaM∼M'→Mσ≡M'σ {σ = ι} M∼N 
... | .(N ∙ ι)  | Γ⊢N∙ι                 | refl 
  = lemma⊢ι Γ⊢N∙ι
\end{code}
%</typealphaproof>

Context clousure of beta contraction.

\end{code}

%<*beta>
\begin{code}
data ctx (r : Rel) : Rel where
  ctxinj : ∀ {t t'}       → r t t'        → ctx r t t'
  ctx·l  : ∀ {t₁ t₁' t₂}  → ctx r t₁ t₁'  → ctx r (t₁ · t₂) (t₁' · t₂)
  ctx·r  : ∀ {t₁ t₂ t₂'}  → ctx r t₂ t₂'  → ctx r (t₁ · t₂) (t₁ · t₂')
  ctxƛ   : ∀ {x t₁ t₁'}   → ctx r t₁ t₁'  → ctx r (ƛ x t₁) (ƛ x t₁')

infix 4 _→β_
_→β_ : Rel
_→β_ = ctx _▹_
\end{code}
%</beta>

\begin{code}
lemma⊢→β :  {Γ : Cxt}{α : Type}{M N : Λ} 
            → Γ ⊢ M ∶ α → M →β N → Γ ⊢ N ∶ α
lemma⊢→β Γ⊢M:α               (ctxinj  M▹N)    = lemma⊢▹ Γ⊢M:α M▹N
lemma⊢→β (⊢· Γ⊢M:α→β Γ⊢N:α)  (ctx·l   M→βM')  = ⊢· (lemma⊢→β Γ⊢M:α→β M→βM') Γ⊢N:α
lemma⊢→β (⊢· Γ⊢M:α→β Γ⊢N:α)  (ctx·r   N→βN')  = ⊢· Γ⊢M:α→β (lemma⊢→β Γ⊢N:α N→βN')
lemma⊢→β (⊢ƛ Γ,x:α⊢M:α)      (ctxƛ    M→βN)   = ⊢ƛ (lemma⊢→β Γ,x:α⊢M:α M→βN)

infix 4 _→α_ 
\end{code}

%<*alphabeta>
\begin{code}
_→α_ : Rel
_→α_ = _→β_ ∪ _∼α_
\end{code}
%</alphabeta>

\begin{code}
lemma⊢→α :  {Γ : Cxt}{α : Type}{M N : Λ} 
            → Γ ⊢ M ∶ α → M →α N → Γ ⊢ N ∶ α
lemma⊢→α Γ⊢M:α (inj₁ M→βN)  = lemma⊢→β Γ⊢M:α M→βN
lemma⊢→α Γ⊢M:α (inj₂ M~N)   = lemma⊢α Γ⊢M:α M~N

infix 4 _→α*_
\end{code}

%<*asteralphabeta>
\begin{code}
_→α*_ : Rel
_→α*_ = star _→α_
\end{code}
%</asteralphabeta>

\begin{code}
abs-step : ∀ {x t t'} → t →α t' → ƛ x t →α ƛ x t'
abs-step (inj₁ M→βN) = inj₁ (ctxƛ M→βN)
abs-step (inj₂ M∼N)  = inj₂ (lemma∼λ M∼N) 

abs-star : ∀ {x M N} → M →α* N → ƛ x M →α* ƛ x N
abs-star refl                 = refl
abs-star (just M→αN)          = just   (abs-step M→αN) 
abs-star (trans M→α*N N→α*P)  = trans  (abs-star M→α*N) (abs-star N→α*P)

app-step-l : ∀ {M N P} → M →α P  → M · N →α P · N
app-step-l (inj₁ t→t') = inj₁ (ctx·l t→t')
app-step-l (inj₂ t∼t') = inj₂ (∼· t∼t' ∼ρ)

app-step-r : ∀ {M N P} → N →α P → M · N →α M · P
app-step-r (inj₁ t→t') = inj₁ (ctx·r t→t')
app-step-r (inj₂ t∼t') = inj₂ (∼· ∼ρ t∼t')

app-star-l : ∀ {M N P} → M →α* P → M · N →α* P · N
app-star-l refl                     = refl
app-star-l (just x)                 = just (app-step-l x)
app-star-l (trans t→α*t' t'→α*t'')  = trans (app-star-l t→α*t') (app-star-l t'→α*t'')

app-star-r : ∀ {M N P} → N →α* P → M · N →α* M · P
app-star-r refl                     = refl
app-star-r (just t→α*t')            = just (app-step-r t→α*t')
app-star-r (trans t→α*t' t'→α*t'')  = trans (app-star-r t→α*t') (app-star-r t'→α*t'')
\end{code}

Reduction is a preorder over terms, hence we can use the combinators of
the standard library for proving the reduction of a term to another.

\begin{code}
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (sym to sym';trans to trans')
open import Relation.Binary using (Preorder)
import Relation.Binary.PreorderReasoning as PreR    

→-preorder : Preorder _ _ _
→-preorder =  
    record { 
      Carrier = Λ;
      _≈_ = _≡_;
      _∼_ = _→α*_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (PropEq.setoid Λ) ;
        reflexive = λ { {M} {.M} refl → refl};
        trans = star.trans } 
    }

open PreR →-preorder renaming (begin_ to begin→_;_∼⟨_⟩_ to _→⟨_⟩_;_≈⟨_⟩_ to _=⟨_⟩_;_∎ to _▣) public
\end{code}

Substitution lemma for $β$-reduction.

\begin{code}
lemma▹* : {x : V} → (_*_ x) preserved-by (dual _▹_) 
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
  with lemmafreeσ→ {x} {M} x*M[y/N]
...  | z , z*M , x*z[y/N] with y ≟ z
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
     | .y , y*M , x*N  | yes refl = *·r x*N
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
     | .x , x*M , *v   | no y≢z   = *·l (*ƛ x*M y≢z)

lemma→α* : {x : V} → (_*_ x) preserved-by (dual _→β_) 
lemma→α* x*N           (ctxinj ▹β)   = lemma▹* x*N ▹β
lemma→α* (*·l x*N)     (ctx·l M→βN)  = *·l (lemma→α* x*N M→βN)
lemma→α* (*·r x*N')    (ctx·l M→βN)  = *·r x*N'
lemma→α* (*·l x*N)     (ctx·r M→βN)  = *·l x*N
lemma→α* (*·r x*N')    (ctx·r M→βN)  = *·r (lemma→α* x*N' M→βN)
lemma→α* (*ƛ x*N y≢x)  (ctxƛ M→βN)   = *ƛ (lemma→α* x*N M→βN) y≢x

lemma→β# : {x : V} → (_#_ x) preserved-by (_→β_) 
lemma→β# = dual-*-# lemma→α*

lemma→α# : {x : V} → (_#_ x) preserved-by (_→α_) 
lemma→α#      x#M (inj₁ M→βN)  = lemma→β# x#M M→βN
lemma→α# {x}  x#M (inj₂ M~N)   = lemmaM∼N# M~N x x#M

lemma→α*# : {x : V} → (_#_ x) preserved-by (_→α*_)
lemma→α*# x#M refl                 = x#M 
lemma→α*# x#M (just M→αN)          = lemma→α# x#M M→αN
lemma→α*# x#M (trans M→α*P P→α*N)  = lemma→α*# (lemma→α*# x#M M→α*P) P→α*N
\end{code}


Subject Reduction

\begin{code}
lemma⊢→α* :  {Γ : Cxt}{α : Type}{M N : Λ} 
             → Γ ⊢ M ∶ α → M →α* N → Γ ⊢ N ∶ α
lemma⊢→α* Γ⊢M:α refl                  = Γ⊢M:α
lemma⊢→α* Γ⊢M:α (just M→βN)           = lemma⊢→α Γ⊢M:α M→βN
lemma⊢→α* Γ⊢M:α (trans M→α*N N→α*P)   = lemma⊢→α* (lemma⊢→α* Γ⊢M:α M→α*N) N→α*P
\end{code}









