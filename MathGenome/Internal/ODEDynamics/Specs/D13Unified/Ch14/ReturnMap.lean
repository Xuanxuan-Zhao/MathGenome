import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ReturnBranch

/-! The complete local first-return theorem, paper.tex d13:14:return-map.
The affine section chart is v ↦ p+v on ker ℓ. The chosen section S may be
larger than the source of the local diffeomorphism. The no-hit condition
refers to this same S, which contains both source and target. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch14.ReturnMap
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u

/-- Actual first-return data, including all flow domains and both derivatives. -/
structure FirstReturnData {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (F : AutonomousODE E) (p : E) (T : ℝ) (ℓ : E →L[ℝ] ℝ) where
  sectionSet : Set ℓ.ker
  section_open : IsOpen sectionSet
  section_zero : (0 : ℓ.ker) ∈ sectionSet
  section_domain : ∀ v ∈ sectionSet, p + (v : E) ∈ F.domain
  section_transverse : ∀ v ∈ sectionSet, ℓ (autonomousEvalValue F (p + (v : E))) ≠ 0
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_period : δ < T
  τ : ℓ.ker → ℝ
  P : OpenPartialHomeomorph ℓ.ker ℓ.ker
  source_zero : (0 : ℓ.ker) ∈ P.source
  target_zero : (0 : ℓ.ker) ∈ P.target
  source_section : P.source ⊆ sectionSet
  target_section : P.target ⊆ sectionSet
  time_zero : τ 0 = T
  map_zero : P 0 = 0
  time_regular : ContDiffOn ℝ k τ P.source
  map_regular : ContDiffOn ℝ k P P.source
  inverse_regular : ContDiffOn ℝ k P.symm P.target
  time_positive : ∀ v ∈ P.source, 0 < τ v
  time_near : ∀ v ∈ P.source, τ v ∈ Ioo (T-δ) (T+δ)
  flow_domain : ∀ v ∈ P.source, ∀ t ∈ Icc 0 (T+δ),
    (t, p + (v : E)) ∈ flowDomain F
  map_formula : ∀ v ∈ P.source, flow F (τ v) (p + (v : E)) = p + (P v : E)
  unique_near : ∀ v ∈ P.source, ∀ t ∈ Ioo (T-δ) (T+δ),
    ℓ (flow F t (p + (v : E)) - p) = 0 ↔ t = τ v
  first_return : ∀ v ∈ P.source, ∀ t : ℝ, 0 < t → t < τ v →
    flow F t (p + (v : E)) ∉ (fun w : ℓ.ker => p + (w : E)) '' sectionSet
  time_derivative : ∀ v : ℓ.ker,
    (fderiv ℝ τ 0) v = -ℓ ((fderiv ℝ (flow F T) p) (v : E)) /
      ℓ (autonomousEvalValue F p)
  map_derivative : ∀ v : ℓ.ker,
    ((fderiv ℝ (P : ℓ.ker → ℓ.ker) 0) v : E) =
      (fderiv ℝ (flow F T) p) (v : E) -
        (ℓ ((fderiv ℝ (flow F T) p) (v : E)) /
          ℓ (autonomousEvalValue F p)) • autonomousEvalValue F p

/-- The section and time width can be chosen within arbitrary prescribed
neighborhoods. Completeness and leastness concern the canonical trajectory. -/
def ReturnMapExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ F : AutonomousODE E,
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, ∀ T : ℝ, 0 < T →
    _root_.D13Unified.Ch11.Orbits.IsComplete F p →
    Function.Periodic (fun t => flow F t p) T →
    (∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R) →
    ¬ _root_.D13Unified.Ch11.Orbits.IsConstant F p →
    ∀ ℓ : E →L[ℝ] ℝ, ℓ (autonomousEvalValue F p) ≠ 0 →
    ∀ S₀ : Set ℓ.ker, IsOpen S₀ → (0 : ℓ.ker) ∈ S₀ →
    ∀ ε : ℝ, 0 < ε → ∃ d : FirstReturnData k F p T ℓ,
      d.sectionSet ⊆ S₀ ∧ d.δ < ε

end Specs.D13Unified.Ch14.ReturnMap
