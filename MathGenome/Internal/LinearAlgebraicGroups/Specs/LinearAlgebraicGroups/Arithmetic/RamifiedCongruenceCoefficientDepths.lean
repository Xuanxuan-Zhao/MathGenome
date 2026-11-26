import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Specs.RamifiedCongruenceCoefficientDepths

open ExceptionalAffineBruhat
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex residueMap)
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model)
open ValuativeRel WithZero
open scoped WithZero

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

universe u
noncomputable section

local notation "O(" K ")" => Valuation.valuationSubring (valuation K)
local notation "κ(" K ")" => IsLocalRing.ResidueField (O(K))

/-- The field and coefficient actions of the given scaling at the finite coefficient level. -/
structure AuxiliaryScaling
    {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {σ : Gal(L/F)} (T : DiagramCompositum F L k σ) where
  E : Type u
  [field : Field E]
  [algebra : Algebra T.field E]
  [valuation : ValuativeRel E]
  [topology : TopologicalSpace E]
  [localField : IsNonarchimedeanLocalField E]
  [finite : FiniteDimensional T.field E]
  [extension : ValuativeExtension T.field E]
  d : ℕ
  d_pos : 0 < d
  uniformizer : Lˣ
  uniformizer_value : normalizedValuation L (uniformizer : L) = exp (-1 : ℤ)
  xi : O(E)
  xi_uniformizer : (ValuativeRel.valuation E).IsUniformizer (xi : E)
  xi_power : (xi : E) ^ d = algebraMap T.field E (algebraMap L T.field (uniformizer : L))
  unchanged_residue : Nat.card κ(E) = Nat.card κ(T.field)
  coefficient : Gal(k/F) →* (E ≃+* E)
  coefficient_extends (g : Gal(k/F)) (z : T.field) :
    coefficient g (algebraMap T.field E z) = algebraMap T.field E (T.coefficient g z)
  coefficient_fixes_xi (g : Gal(k/F)) : coefficient g (xi : E) = xi
  integralCoefficient : Gal(k/F) →* (O(E) ≃+* O(E))
  integralCoefficient_eq (g : Gal(k/F)) (z : O(E)) :
    (integralCoefficient g z : E) = coefficient g (z : E)

attribute [instance] AuxiliaryScaling.field AuxiliaryScaling.algebra AuxiliaryScaling.valuation
  AuxiliaryScaling.topology AuxiliaryScaling.localField AuxiliaryScaling.finite
  AuxiliaryScaling.extension

/-- Membership in the actual power of the maximal ideal, viewed in the fraction field. -/
def AtDepth {E : Type*} [Field E] [ValuativeRel E] (n : ℕ) (z : E) : Prop :=
  ∃ a : O(E), a ∈ IsLocalRing.maximalIdeal O(E) ^ n ∧ (a : E) = z

/-- The residue after dividing by the specified auxiliary uniformizer power. -/
def IsLeading {E : Type*} [Field E] [ValuativeRel E]
    (ξ : O(E)) (n : ℕ) (z : E) (r : κ(E)) : Prop :=
  ∃ b : O(E), z = (ξ : E) ^ n * (b : E) ∧ IsLocalRing.residue _ b = r

def scaledEntry {P E : Type*} [Field P] [Field E] [ValuativeRel E]
    (f : P →+* E) (ξ : O(E)) (s : ℤ) (c : O(E)ˣ) (a : P) : E :=
  (ξ : E) ^ s * ((c : O(E)) : E) * f a

/-- The depth and lifting statements for a single slot. -/
def SingleSlot {P E : Type*} [Field P] [Field E] [ValuativeRel P] [ValuativeRel E]
    [TopologicalSpace P] [TopologicalSpace E]
    [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField E]
    (f : P →+* E) (ξ : O(E)) (e n : ℕ) (s : ℤ) (c : O(E)ˣ) : Prop :=
  (∀ a : P, ∀ m : ℤ, normalizedValuation P a = exp (-m) →
    normalizedValuation E (scaledEntry f ξ s c a) = exp (-(s + (e : ℤ) * m))) ∧
  (∀ a : P, AtDepth n (scaledEntry f ξ s c a) →
    ∃! r, IsLeading ξ n (scaledEntry f ξ s c a) r) ∧
  ((¬ ∃ m : ℤ, (n : ℤ) = s + (e : ℤ) * m) → ∀ a : P,
    AtDepth n (scaledEntry f ξ s c a) → IsLeading ξ n (scaledEntry f ξ s c a) 0) ∧
  ∀ m : ℤ, (n : ℤ) = s + (e : ℤ) * m → ∀ r : κ(E), ∃ a : P,
    IsLeading ξ n (scaledEntry f ξ s c a) r ∧
    (r = 0 → a = 0) ∧ (r ≠ 0 → normalizedValuation P a = exp (-m)) ∧
    (s = 0 → ∃ t : O(P)ˣ, ((t : O(P)) : P) - 1 = a)

/-- Reduction of an integral coefficient action on the auxiliary field. -/
def reduceAutomorphism {E : Type*} [Field E] [ValuativeRel E] (g : O(E) ≃+* O(E)) :
    κ(E) →+* κ(E) :=
  letI := IsLocalHom.of_surjective g.toRingHom g.surjective
  IsLocalRing.ResidueField.map g.toRingHom

/-- The residue unit multiplying the first leading coefficient to give the second. -/
def pairedFactor {K E : Type*} [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
    (c₁ c₂ : O(E)ˣ) (ε : O(K)ˣ) (m : ℤ) : κ(E)ˣ :=
  let red := (IsLocalRing.residue O(E)).toMonoidHom
  (Units.map red c₂) * (Units.map red c₁)⁻¹ *
    (Units.map ((residueMap K E).comp (IsLocalRing.residue O(K))).toMonoidHom ε) ^ m

/-- The two actual absolute slots of a paired parameter, with the common shift and
their comparison by the residue of the conjugate-uniformizer unit. -/
def PairedSlots {K E : Type*} [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
    (τ : K ≃+* K) (ξ : O(E)) (ε : O(K)ˣ)
    (d n : ℕ) (s : ℤ) (c₁ c₂ : O(E)ˣ) : Prop :=
  let z₁ := scaledEntry (algebraMap K E) ξ s c₁
  let z₂ := scaledEntry ((algebraMap K E).comp τ.toRingHom) ξ s c₂
  (∀ a : K, ∀ m : ℤ, normalizedValuation K a = exp (-m) →
    normalizedValuation E (z₁ a) = exp (-(s + (d : ℤ) * m)) ∧
    normalizedValuation E (z₂ a) = exp (-(s + (d : ℤ) * m))) ∧
  ((¬ ∃ m : ℤ, (n : ℤ) = s + (d : ℤ) * m) → ∀ a : K,
    AtDepth n (z₁ a) → IsLeading ξ n (z₁ a) 0 ∧ IsLeading ξ n (z₂ a) 0) ∧
  ∀ m : ℤ, (n : ℤ) = s + (d : ℤ) * m →
    (∀ a r, IsLeading ξ n (z₁ a) r →
      IsLeading ξ n (z₂ a) ((pairedFactor c₁ c₂ ε m : κ(E)) * r)) ∧
    ∀ r, ∃ a : K, IsLeading ξ n (z₁ a) r ∧
      IsLeading ξ n (z₂ a) ((pairedFactor c₁ c₂ ε m : κ(E)) * r)

/-- Coefficient depths, residue identifications and leading coefficients for the
given scaling of the actual ramified diagram compositum. -/
def RamifiedCoefficientDepths : Prop :=
  ∀ (F L k : Type u) [Field F] [Field L] [Field k]
    [Algebra F L] [Algebra F k] [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F k] [IsGalois F k]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeExtension F k],
    IsUnramifiedLocalExtension F k →
    ∀ (σ : Gal(L/F)), Module.finrank F L = 2 → σ ≠ 1 → 1 < ramificationIndex F L →
    ∀ {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M)
      (T : DiagramCompositum F L k σ) (A : FoldedApartment (R.diagram σ))
      (_X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
      (S : AuxiliaryScaling T) (galResidue : Gal(k/F) ≃* Gal(κ(k)/κ(F))),
    (∀ (g : Gal(k/F)) (z w : O(k)), (w : k) = g (z : k) →
      galResidue g (IsLocalRing.residue _ z) = IsLocalRing.residue _ w) →
    let π := algebraMap L T.field (S.uniformizer : L)
    (∀ a : T.field, normalizedValuation S.E (algebraMap T.field S.E a) =
      normalizedValuation T.field a ^ S.d) ∧
    (∀ a : k, normalizedValuation S.E (algebraMap T.field S.E (algebraMap k T.field a)) =
      normalizedValuation k a ^ (2 * S.d)) ∧
    (∀ a, normalizedValuation T.field (T.diagram a) = normalizedValuation T.field a) ∧
    (∃ τ₀ : O(T.field) ≃+* O(T.field),
      (∀ a, (τ₀ a : T.field) = T.diagram (a : T.field)) ∧
      ∀ a, IsLocalRing.residue _ (τ₀ a) = IsLocalRing.residue _ a) ∧
    (∃ (i : κ(k) ≃+* κ(T.field)) (j : κ(T.field) ≃+* κ(S.E)),
      i.toRingHom = residueMap k T.field ∧ j.toRingHom = residueMap T.field S.E ∧
      ∀ (g : Gal(k/F)) (r : κ(k)),
        reduceAutomorphism (S.integralCoefficient g) (j (i r)) = j (i (galResidue g r))) ∧
    ∃ ε : O(T.field)ˣ, T.diagram π / π = ((ε : O(T.field)) : T.field) ∧
      ∀ n : ℕ, 0 < n → ∀ (s : ℤ) (c₁ c₂ : O(S.E)ˣ),
      SingleSlot ((algebraMap T.field S.E).comp (algebraMap k T.field))
        S.xi (2 * S.d) n s c₁ ∧
      SingleSlot (algebraMap T.field S.E) S.xi S.d n s c₁ ∧
      PairedSlots T.diagram.toRingEquiv S.xi ε S.d n s c₁ c₂

end
end LinearAlgebraicGroups.Specs.RamifiedCongruenceCoefficientDepths
