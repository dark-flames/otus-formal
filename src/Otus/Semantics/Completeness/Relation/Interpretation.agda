PER : (D : Set) → Set (lsuc 0ℓ)
PER D = Rel D 0ℓ

data Ty : PER VType
data PER⟦_⟧≡_ : REL VType (PER VType) (lsuc 0ℓ)


_~_∈_ : ∀ { D : Set } → (v₁ v₂ : D) → (R : PER D) → Set
v₁ ~ v₂ ∈ R = R v₁ v₂

PERFamily : Set (lsuc 0ℓ)
PERFamily = Value → PER VType


Π[_,_]  : ∀ (D : PER Value) → (C : PERFamily) → PER Value
Π[ D , C ] = λ { t₁ t₂ → (∀ {u₁ u₂ : Value} → (d : D u₁ u₂) 
  → Σ[ v₁ ∈ Value ]
    Σ[ v₂ ∈ Value ]
    App⟨ t₁ ∣ u₁ ⟩⇝ v₁ ×
    App⟨ t₂ ∣ u₂ ⟩⇝ v₂ ×
    C u₁ v₁ v₂) }

record ClsPER⟦_⟧⇐_ (E : Closure) (v : Value) : Set (lsuc 0ℓ) where
  inductive
  field 
    clsPER : PER VType
    clsR : Value
    clsE : ⟦ E ⟧⇐ [ v ]ₐ ⇝ clsR
    resInterp : PER⟦ clsR ⟧≡ clsPER

open ClsPER⟦_⟧⇐_


record ⟦_⟧⇐_~⟦_⟧⇐_∈_ (E₁ : Closure) (a₁ : Arguments) (E₂ : Closure) (a₂ : Arguments) (R : PER Value) : Set where
  inductive
  field
    lRes : Value
    lEval : ⟦ E₁ ⟧⇐ a₁ ⇝ lRes
    rRes : Value
    rEval : ⟦ E₂ ⟧⇐ a₂ ⇝ rRes
    resEq : lRes ~ rRes ∈ R

-- ⟦_⟧⇐_~⟦_⟧⇐_∈_ : Closure → Arguments → Closure → Arguments → Rel Value 0ℓ → Set
-- ⟦ E₁ ⟧⇐ a₁ ~⟦ E₂ ⟧⇐ a₂ ∈ R = Σ[ lRes ∈ Value ] Σ[ rRes ∈ Value ] (⟦ E₁ ⟧⇐ a₁ ⇝ lRes) × (⟦ E₂ ⟧⇐ a₂ ⇝ rRes) × (lRes ~ rRes ∈ R)

familyOf : ((v : Value) → ClsPER⟦ E ⟧⇐ v) → PERFamily
familyOf c = λ { v → clsPER (c v) }

data PER⟦_⟧≡_ where
  INat : PER⟦ VNat ⟧≡ ⟦Nat⟧
  IUniv : PER⟦ VUniv l ⟧≡ Ty
  -- IPi : PER⟦ T ⟧≡ R₁ → (c : (v : Value) → ClsPER⟦ E ⟧⇐ v )
  --  → PER⟦ VPi T E ⟧≡ Π[ R₁ , familyOf c ]

data Ty where
  PERNat : VNat ~ VNat ∈ Ty 
  PERUniv : VUniv l ~ VUniv l ∈ Ty
  -- PERPi : T₁ ~ T₂ ∈ Ty → PER⟦ T₁ ⟧≡ R₁ → (t₁ ~ t₂ ∈ R₁ → ⟦ E₁ ⟧⇐ [ t₁ ]ₐ ⇝ U₁ → ⟦ E₂ ⟧⇐ [ t₂ ]ₐ ⇝ U₂ → U₁ ~ U₂ ∈ Ty)
  --   → VPi T₁ E₁ ~ VPi T₂ E₂ ∈ Ty