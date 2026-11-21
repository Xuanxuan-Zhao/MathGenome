import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.DaniellStoneRepresentation

/-! Independent statements for paper.tex:6304–6311.
The domain remains the original arbitrary type, including an empty type.
The unit hypothesis is explicit and separate from Stone truncation.
-/

open Set MeasureTheory
universe u

namespace Specs.D11.Ch23.UnitImpliesFiniteUnique

open _root_.D11.Ch23.Specs

/-- The positive half-level of the constant unit is the whole domain. -/
def unit_univ_mem : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
    (fun _ : X => (1 : ℝ)) ∈ V → (univ : Set X) ∈ positiveLevelSigmaRing V

/-- A generated sigma-ring containing X is exactly the generated sigma-algebra,
expressed as equality of their families of subsets of X. -/
def sigmaRing_eq_measurableSets_of_univ : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
    (univ : Set X) ∈ positiveLevelSigmaRing V →
      (positiveLevelSigmaRing V : Set (Set X)) =
        {A | MeasurableSet[positiveLevelMeasurableSpace V] A}

/-- Whole-space membership alone suffices for full uniqueness; no finiteness
or unit hypothesis is imposed here. -/
def full_uniqueness_of_univ : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
    IsVectorLattice V → IsStone V →
    ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
    (univ : Set X) ∈ positiveLevelSigmaRing V →
    letI : MeasurableSpace X := positiveLevelMeasurableSpace V
    ∀ μ ν : Measure X,
      (∀ f : V, Integrable (f : X → ℝ) μ ∧ ∫ x, (f : X → ℝ) x ∂μ = L f) →
      (∀ f : V, Integrable (f : X → ℝ) ν ∧ ∫ x, (f : X → ℝ) x ∂ν = L f) →
      μ = ν

/-- Every integrable representation has finite mass L(1). Both the ENNReal
and real versions are recorded, so the embedding cannot conceal finiteness. -/
def unit_mass : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)) (L : V →ₗ[ℝ] ℝ)
    (hunit : (fun _ : X => (1 : ℝ)) ∈ V),
    letI : MeasurableSpace X := positiveLevelMeasurableSpace V
    ∀ μ : Measure X,
      (∀ f : V, Integrable (f : X → ℝ) μ ∧ ∫ x, (f : X → ℝ) x ∂μ = L f) →
      IsFiniteMeasure μ ∧
      μ univ = ENNReal.ofReal (L ⟨fun _ => 1, hunit⟩) ∧
      μ.real univ = L ⟨fun _ => 1, hunit⟩ ∧
      (L ⟨fun _ => 1, hunit⟩ = 1 → IsProbabilityMeasure μ)

/-- Existence, absolute integrability, full uniqueness, finite total mass,
and the probability specialization of the unit corollary. -/
def unit_implies_finite_unique : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
    IsVectorLattice V → IsStone V →
    ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
    ∀ hunit : (fun _ : X => (1 : ℝ)) ∈ V,
    letI : MeasurableSpace X := positiveLevelMeasurableSpace V
    ∃ μ : Measure X,
      (∀ f : V, Measurable (f : X → ℝ) ∧ Integrable (f : X → ℝ) μ ∧
        ∫ x, (f : X → ℝ) x ∂μ = L f) ∧
      IsFiniteMeasure μ ∧
      μ univ = ENNReal.ofReal (L ⟨fun _ => 1, hunit⟩) ∧
      (L ⟨fun _ => 1, hunit⟩ = 1 → IsProbabilityMeasure μ) ∧
      (∀ ν : Measure X,
        (∀ f : V, Integrable (f : X → ℝ) ν ∧ ∫ x, (f : X → ℝ) x ∂ν = L f) →
        ν = μ)

end Specs.D11.Ch23.UnitImpliesFiniteUnique
