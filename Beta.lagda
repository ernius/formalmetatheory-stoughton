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
infix 3 _→α*ₛ_
_→α*ₛ_ : Σ → Σ → Set
σ →α*ₛ σ' = (x : V) → σ x →α* σ' x 

infix 3 _→α*ₛ_⇂_
_→α*ₛ_⇂_ : Σ → Σ → Λ → Set
σ →α*ₛ σ' ⇂ M = (x : V) → x * M → σ x →α* σ' x 

lemma-→α*ₛ→→α*ₛ⇂ : {σ σ' : Σ}(M : Λ) → σ →α*ₛ σ' → σ →α*ₛ σ' ⇂ M
lemma-→α*ₛ→→α*ₛ⇂ {σ} {σ'} M σ→α*ₛσ' z z*M = σ→α*ₛσ' z

lemma-refl-→α*ₛ : Reflexive _→α*ₛ_
lemma-refl-→α*ₛ x = refl

lemma-→α*ₛι : ι →α*ₛ ι
lemma-→α*ₛι = lemma-refl-→α*ₛ

lemma-→α*ₛ≺+ : {x : V}{σ σ' : Σ}{M N : Λ} → σ →α*ₛ σ' → M →α* N → σ ≺+ (x , M) →α*ₛ σ' ≺+ (x , N)
lemma-→α*ₛ≺+ {x} {σ} {σ'} {M} {N} σ→α*σ' M→α*N y with x ≟ y
... | yes _  = M→α*N
... | no _   = σ→α*σ' y

lemma-→α*ₛ⇂≺+ : {x : V}{σ σ' : Σ}{M N P : Λ} → σ →α*ₛ σ' ⇂ ƛ x P → M →α* N → σ ≺+ (x , M) →α*ₛ σ' ≺+ (x , N) ⇂ P
lemma-→α*ₛ⇂≺+ {x} {σ} {σ'} {M} {N} σ→α*σ' M→α*N y y*ƛxP with x ≟ y
... | yes _    = M→α*N
... | no  x≢y  = σ→α*σ' y (*ƛ y*ƛxP x≢y)

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

app-star : ∀ {M M' N N'} → M →α* M' → N →α* N' → M · N →α* M' · N'
app-star M→α*M' N→α*N' = trans (app-star-l M→α*M') (app-star-r N→α*N')
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

open PreR →-preorder renaming (begin_ to begin→_;_∼⟨_⟩_ to _→⟨_⟩_;_≈⟨_⟩_ to _=⟨_⟩_;_∎ to _▣)
\end{code}

Substitution lemma for $β$-reduction.

\begin{code}
lemma▹* : {x : V} → (_*_ x) preserved-by (dual _▹_) --{M N : Λ} → x * N → M ▹ N → x * M
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
  with lemmafreeσ→ {x} {M} x*M[y/N]
...  | z , z*M , x*z[y/N] with y ≟ z
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
     | .y , y*M , x*N  | yes refl = *·r x*N
lemma▹*  {x} .{M ∙ ι ≺+ (y , N)}  {ƛ y M · N}  x*M[y/N] ▹β
     | .x , x*M , *v   | no y≢z   = *·l (*ƛ x*M y≢z)

lemma→α* : {x : V} → (_*_ x) preserved-by (dual _→β_) --{M N : Λ} → x * N → M →β N → x * M
lemma→α* x*N           (ctxinj ▹β)   = lemma▹* x*N ▹β
lemma→α* (*·l x*N)     (ctx·l M→βN)  = *·l (lemma→α* x*N M→βN)
lemma→α* (*·r x*N')    (ctx·l M→βN)  = *·r x*N'
lemma→α* (*·l x*N)     (ctx·r M→βN)  = *·l x*N
lemma→α* (*·r x*N')    (ctx·r M→βN)  = *·r (lemma→α* x*N' M→βN)
lemma→α* (*ƛ x*N y≢x)  (ctxƛ M→βN)   = *ƛ (lemma→α* x*N M→βN) y≢x

lemma→β# : {x : V} → (_#_ x) preserved-by (_→β_) --{M N : Λ} → x # M → M →β N → x # N
lemma→β# = dual-*-# lemma→α*

lemma→α# : {x : V} → (_#_ x) preserved-by (_→α_) -- {M N : Λ} → x # M → M →α N → x # N
lemma→α#      x#M (inj₁ M→βN)  = lemma→β# x#M M→βN
lemma→α# {x}  x#M (inj₂ M~N)   = lemmaM∼N# M~N x x#M

lemma→α*# : {x : V} → (_#_ x) preserved-by (_→α*_) -- {M N : Λ} → x # M → M →α* N → x # N
lemma→α*# x#M refl                 = x#M 
lemma→α*# x#M (just M→αN)          = lemma→α# x#M M→αN
lemma→α*# x#M (trans M→α*P P→α*N)  = lemma→α*# (lemma→α*# x#M M→α*P) P→α*N

lemmaƛ∼ :  {x y y' : V}{M : Λ}{σ : Σ}
           → y #⇂ (σ , ƛ x M) → y' #⇂ (σ , ƛ x M)
           → ƛ y (M ∙ σ ≺+ ( x , v y)) ∼α ƛ y'  (M ∙ σ ≺+ ( x , v y'))  
lemmaƛ∼ {x} {y} {y'} {M} {σ} y#σ,ƛxM y'#σ,ƛxM
  =  begin
       ƛ y   (M ∙ σ ≺+ ( x , v y))
     ∼⟨ ∼σ (corollary4-2 y#σ,ƛxM) ⟩
       ƛ x M ∙ σ
     ∼⟨ corollary4-2 y'#σ,ƛxM ⟩ 
       ƛ y'  (M ∙ σ ≺+ ( x , v y'))  
     ∎

\end{code}

%<*alphabetaastersubstitutionsigma>
\begin{code}
lemma→α*Σ :  {M : Λ}{σ σ' : Σ} 
             → σ →α*ₛ σ' ⇂ M
             → M ∙ σ →α* M ∙ σ'
\end{code}
%</alphabetaastersubstitutionsigma>

\begin{code}
lemma→α*Σ {v x}    σ→α*σ'⇂M   = σ→α*σ'⇂M x *v
lemma→α*Σ {M · N}  σ→α*σ'⇂MN  = app-star  (lemma→α*Σ {M} (λ z z*M → σ→α*σ'⇂MN z (*·l z*M)))
                                          (lemma→α*Σ {N} (λ z z*M → σ→α*σ'⇂MN z (*·r z*M)))
lemma→α*Σ {ƛ x M}  {σ} {σ'}
                   σ→α*σ'⇂ƛxM
  =  begin→
       (ƛ x M) ∙ σ
     =⟨ refl ⟩
       ƛ y   (M ∙ σ ≺+ ( x , v y))
     →⟨ abs-star (lemma→α*Σ  {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)}
                             (lemma-→α*ₛ⇂≺+ {x} σ→α*σ'⇂ƛxM refl)) ⟩
       ƛ y   (M ∙ σ' ≺+ ( x , v y))
     →⟨ just (inj₂ (lemmaƛ∼ y#σ',ƛxM y'#σ',ƛxM)) ⟩
       ƛ y'  (M ∙ σ' ≺+ ( x , v y'))  
     =⟨ refl ⟩
       (ƛ x M) ∙ σ'
     ▣
  where
  y = χ (σ , ƛ x M)
  y#σ,ƛxM = χ-lemma2 σ (ƛ x M)
  y#σ',ƛxM : y #⇂ (σ' , ƛ x M)
  y#σ',ƛxM z z*ƛxM = lemma→α*# (y#σ,ƛxM z z*ƛxM) (σ→α*σ'⇂ƛxM z z*ƛxM)
  y' = χ (σ' , ƛ x M)
  y'#σ',ƛxM = χ-lemma2 σ' (ƛ x M)
\end{code}



-- %<*alphabetaastersubstitutionsigma>
-- \begin{code}
-- lemma→α*Σ :  {M : Λ}{σ σ' : Σ} 
--              → σ →α*ₛ σ'
--              → M ∙ σ →α* M ∙ σ'
-- \end{code}
-- %</alphabetaastersubstitutionsigma>

-- \begin{code}
-- lemma→α*Σ {v x}    σ→α*σ'  = σ→α*σ' x
-- lemma→α*Σ {M · N}  σ→α*σ'  = app-star (lemma→α*Σ {M} σ→α*σ') (lemma→α*Σ {N} σ→α*σ')
-- lemma→α*Σ {ƛ x M}  {σ} {σ'}
--                    σ→α*σ'
--   =  begin→
--        (ƛ x M) ∙ σ
--      =⟨ refl ⟩
--        ƛ y   (M ∙ σ ≺+ ( x , v y))
--      →⟨ abs-star (lemma→α*Σ {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} (lemma-→α*ₛ≺+ {x} σ→α*σ' refl)) ⟩
--        ƛ y   (M ∙ σ' ≺+ ( x , v y))
--      →⟨ just (inj₂ (lemmaƛ∼ y#σ',ƛxM y'#σ',ƛxM)) ⟩
--        ƛ y'  (M ∙ σ' ≺+ ( x , v y'))  
--      =⟨ refl ⟩
--        (ƛ x M) ∙ σ'
--      ▣
--   where
--   y = χ (σ , ƛ x M)
--   y#σ,ƛxM = χ-lemma2 σ (ƛ x M)
--   y#σ',ƛxM : y #⇂ (σ' , ƛ x M)
--   y#σ',ƛxM z z*ƛxM = lemma→α*# (y#σ,ƛxM z z*ƛxM) (σ→α*σ' z)
--   y' = χ (σ' , ƛ x M)
--   y'#σ',ƛxM = χ-lemma2 σ' (ƛ x M)
-- \end{code}

\begin{code}
lemma▹Λ :  {M M' : Λ}{σ : Σ} 
            → M ▹ M'
            → M ∙ σ →α* M' ∙ σ
lemma▹Λ {ƛ x M · N} .{M ∙ ι ≺+ (x , N)} {σ} ▹β
  =  begin→
       (ƛ x M · N) ∙ σ
     =⟨ refl ⟩
       (ƛ y (M ∙ σ ≺+ (x , v y))) · (N ∙ σ)
     →⟨ just (inj₁ (ctxinj ▹β)) ⟩
       (M ∙ σ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ σ)
     →⟨ just (inj₂ (corollary1SubstLemma y#σ,M)) ⟩
       M ∙ σ ≺+ (x , N ∙ σ)
     =⟨ corollary1Prop7 {M} {N} {σ} {x}⟩
       (M ∙ ι ≺+ (x , N)) ∙ σ
     ▣
  where
  y = χ (σ , ƛ x M)
  y#σ,M = χ-lemma2 σ (ƛ x M)

lemma→βΛ :  {M M' : Λ}{σ : Σ} 
            → M →β M'
            → M ∙ σ →α* M' ∙ σ
lemma→βΛ  (ctxinj M▹M')  = lemma▹Λ M▹M'
lemma→βΛ  (ctx·l M→βM')  = app-star (lemma→βΛ M→βM') refl
lemma→βΛ  (ctx·r M→βM')  = app-star refl (lemma→βΛ M→βM')
lemma→βΛ  {ƛ x M} {ƛ .x M'} {σ}
          (ctxƛ M→βM')
  =  begin→
       (ƛ x M) ∙ σ
     =⟨ refl ⟩
       ƛ y   (M   ∙ σ ≺+ ( x , v y))
     →⟨ abs-star (lemma→βΛ M→βM') ⟩
       ƛ y   (M'   ∙ σ ≺+ ( x , v y))
     →⟨ just (inj₂ (lemmaƛ∼ y#σ,ƛxM' y'#σ,ƛxM')) ⟩            
       ƛ y'  (M'  ∙ σ ≺+ ( x , v y'))  
     =⟨ refl ⟩
       (ƛ x M') ∙ σ
     ▣
  where
  y = χ (σ , ƛ x M)
  y#σ,ƛxM = χ-lemma2 σ (ƛ x M)
  y' = χ (σ , ƛ x M')
  y'#σ,ƛxM' : y' #⇂ (σ , ƛ x M')
  y'#σ,ƛxM' = χ-lemma2 σ (ƛ x M')
  y#σ,ƛxM' : y #⇂ (σ , ƛ x M')
  y#σ,ƛxM' z z*λxM' = y#σ,ƛxM z (lemma→α* z*λxM' (ctxƛ M→βM'))
  
\end{code}

%<*betaalphasubstitutionterm>
\begin{code}
lemma→α*Λ :  {M M' : Λ}{σ : Σ} 
             → M →α* M'
             → M ∙ σ →α* M' ∙ σ
\end{code}
%</betaalphasubstitutionterm>

\begin{code}
lemma→α*Λ refl
  = refl
lemma→α*Λ (just (inj₁ M→βM'))
  = lemma→βΛ M→βM'
lemma→α*Λ {σ = σ} (just (inj₂ M∼M'))
  rewrite lemmaM∼M'→Mσ≡M'σ {σ = σ} M∼M' 
  = refl
lemma→α*Λ (trans M→α*N N→α*M')
  = trans (lemma→α*Λ M→α*N) (lemma→α*Λ N→α*M')
\end{code}

-- 
-- \begin{code}
-- lemma→α*subst  : {M M' : Λ}{σ σ' : Σ} 
--         → M →α* M' → σ →α*ₛ σ'
--         → M ∙ σ →α* M' ∙ σ'
-- lemma→α*subst {M} {M'} {σ} {σ'} M→α*M' σ→α*σ'
--   =  begin→
--        M ∙ σ
--      →⟨ lemma→α*Λ M→α*M' ⟩
--        M' ∙ σ
--      →⟨ lemma→α*Σ {M'} σ→α*σ' ⟩
--        M' ∙ σ'
--      ▣
-- \end{code}
-- %</betaastersubstitution>

%<*betaastersubstitution>
\begin{code} 
lemma→α*subst  : {M M' : Λ}{σ σ' : Σ} 
        → M →α* M' → σ →α*ₛ σ' ⇂ M
        → M ∙ σ →α* M' ∙ σ'
lemma→α*subst {M} {M'} {σ} {σ'} M→α*M' σ→α*σ'⇂M
  =  begin→
       M ∙ σ
     →⟨ lemma→α*Σ σ→α*σ'⇂M ⟩
       M ∙ σ'
     →⟨ lemma→α*Λ M→α*M' ⟩
       M' ∙ σ'
     ▣
\end{code}
%</betaastersubstitution>

Subject Reduction

\begin{code}
lemma⊢→α* :  {Γ : Cxt}{α : Type}{M N : Λ} 
             → Γ ⊢ M ∶ α → M →α* N → Γ ⊢ N ∶ α
lemma⊢→α* Γ⊢M:α refl                  = Γ⊢M:α
lemma⊢→α* Γ⊢M:α (just M→βN)           = lemma⊢→α Γ⊢M:α M→βN
lemma⊢→α* Γ⊢M:α (trans M→α*N N→α*P)   = lemma⊢→α* (lemma⊢→α* Γ⊢M:α M→α*N) N→α*P

→β-rdx : ∀ {x M N M' N'} → M →α* M' → N →α* N' → (M ∙ ι ≺+ (x , N)) →α* (M' ∙ ι ≺+ (x , N'))
→β-rdx {x} {M} M→α*N' N→α*N' = lemma→α*subst M→α*N' (lemma-→α*ₛ→→α*ₛ⇂ M (lemma-→α*ₛ≺+ {x} {ι} {ι} lemma-→α*ₛι N→α*N'))

→α*-rdx : ∀ {x M N M' N'} → M →α* M' → N →α* N' → ((ƛ x M) · N) →α* (M' ∙ ι ≺+ (x , N'))
→α*-rdx  {x} {M} {N} {M'} {N'} M→M' N→N' = trans  (just (inj₁ (ctxinj ▹β)))
                                                  (→β-rdx {x} {M} {N} {M'} {N'} M→M' N→N')
\end{code}







