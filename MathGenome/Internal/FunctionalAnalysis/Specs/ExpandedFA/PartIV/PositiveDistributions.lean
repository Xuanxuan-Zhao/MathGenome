import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.Analysis.RCLike.Basic

/-! Independent statements for `fa2:p4:positive-distribution-measure`.
Measures live on the open subspace Ω, and need not have finite total mass. -/

open Set TopologicalSpace MeasureTheory
open scoped Distributions CompactlySupported ContDiff

namespace ExpandedFA.PartIV.PositiveDistributions
open ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- The scalar-linear distribution is tested on real-valued smooth functions,
embedded by the canonical real inclusion. -/
noncomputable def realTest (φ : Tests ℝ Ω) : Tests 𝕜 Ω :=
  TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) φ

/-- A real continuous compactly supported function, embedded in the scalar field. -/
noncomputable def realCc (f : C_c(Ω, ℝ)) : C_c(Ω, 𝕜) :=
  ⟨⟨fun x => (f x : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left (by simp)⟩

/-- Nonnegative values are real and nonnegative, also for complex distributions. -/
def IsPositive (u : ScalarDistribution 𝕜 Ω) : Prop :=
  ∀ φ : Tests ℝ Ω, (∀ x, 0 ≤ φ x) → ∃ r : ℝ, 0 ≤ r ∧ u (realTest φ) = (r : 𝕜)

/-- Restriction of a test to the open subspace is compactly supported there. -/
noncomputable def testToCc : Tests 𝕜 Ω →ₗ[𝕜] C_c(Ω, 𝕜) where
  toFun φ :=
    ⟨⟨fun x => φ x.val, φ.continuous.comp continuous_subtype_val⟩, by
      have hc : IsCompact (Subtype.val ⁻¹' tsupport φ : Set Ω) :=
        Topology.IsInducing.subtypeVal.isCompact_preimage'
          φ.hasCompactSupport (by simpa using φ.tsupport_subset)
      apply hc.of_isClosed_subset isClosed_closure
      apply closure_minimal
      · intro x hx
        exact subset_tsupport φ hx
      · exact isClosed_closure.preimage continuous_subtype_val⟩
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

/-- Representation includes integrability of each test. The measure has the
paper's three regularity properties, with no finite-mass premise. -/
def Represents (μ : Measure Ω) (u : ScalarDistribution 𝕜 Ω) : Prop :=
  ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ ∧
  ∀ φ : Tests 𝕜 Ω, Integrable (fun x : Ω => φ x.val) μ ∧
    u φ = ∫ x : Ω, φ x.val ∂μ

end ExpandedFA.PartIV.PositiveDistributions

namespace Specs.ExpandedFA.PartIV.PositiveDistributions
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.PartIV.PositiveDistributions

/-- The full equivalence, for either scalar field, all dimensions, all open sets. -/
def characterizationType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  IsPositive u ↔ ∃! μ : Measure Ω, Represents μ u

/-- Positivity improves the compactwise distribution estimate to order zero.
The bound applies to every scalar test and every uniform bound on its values. -/
def localOrderZeroType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω), IsPositive u →
  ∀ (K : Compacts (Domain d)), (K : Set (Domain d)) ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Tests 𝕜 Ω), tsupport φ ⊆ K →
      ∀ M : ℝ, 0 ≤ M → (∀ x, ‖φ x‖ ≤ M) → ‖u φ‖ ≤ C * M

/-- The restriction to real tests extends to a positive real-linear functional
on continuous compactly supported functions on Ω. -/
def extensionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω), IsPositive u →
  ∃! I : C_c(Ω, ℝ) →ₗ[ℝ] ℝ,
    (∀ f : C_c(Ω, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ I f) ∧
    ∀ φ : Tests ℝ Ω, u (realTest φ) = (I (testToCc φ) : 𝕜)

/-- The full scalar-linear functional extends to scalar-valued C_c, with
positivity on the embedded real nonnegative functions. -/
def scalarExtensionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω), IsPositive u →
  ∃ I : C_c(Ω, 𝕜) →ₗ[𝕜] 𝕜,
    (∀ φ : Tests 𝕜 Ω, I (testToCc φ) = u φ) ∧
    ∀ f : C_c(Ω, ℝ), (∀ x, 0 ≤ f x) →
      ∃ r : ℝ, 0 ≤ r ∧ I (realCc f) = (r : 𝕜)

/-- Every compact-finite positive Radon measure gives a positive continuous
scalar-linear distribution for the original LF topology. -/
def converseType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (μ : Measure Ω),
  ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ →
    ∃ u : ScalarDistribution 𝕜 Ω, IsPositive u ∧ Represents μ u

end Specs.ExpandedFA.PartIV.PositiveDistributions
