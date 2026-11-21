import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for `fa2:p2:endpoint-interpolation-bridge`.
The operator starts on L¹. All restrictions are identified with that operator
by the canonical inclusions of a.e. classes into L¹. No positivity of the
measure or prior boundedness of the L∞ restriction is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.BanachGeometry.EndpointInterpolationSpec

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical inclusion into L¹ on a finite measure space. -/
def toL1 (p : ℝ≥0∞) (hp : 1 ≤ p) : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 1 μ where
  toFun f := ⟨(f : X →ₘ[μ] 𝕜), ((Lp.memLp f).mono_exponent hp).eLpNorm_lt_top⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Merely setwise invariance of L∞ for the original bounded L¹ operator. -/
def PreservesInfinity (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) : Prop :=
  ∀ f : Lp 𝕜 ∞ μ, MemLp (T (toL1 ∞ le_top f)) ∞ μ

/-- Automatic boundedness of the actual restriction, over either field. -/
def EndpointBounded : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (𝕜 : Type*) [RCLike 𝕜] (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ),
    PreservesInfinity T → ∃ S : Lp 𝕜 ∞ μ →L[𝕜] Lp 𝕜 ∞ μ,
      ∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f)

/-- The sharp estimate for the given operator and its actual endpoint
restriction. This includes existence, boundedness, and agreement on all Lp,
with the exact two operator norms. The exponent is finite and strictly >1. -/
def InterpolationFor (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ), PreservesInfinity T →
    ∃ S : Lp 𝕜 ∞ μ →L[𝕜] Lp 𝕜 ∞ μ,
      (∀ f, toL1 ∞ le_top (S f) = T (toL1 ∞ le_top f)) ∧
      ∀ (p : ℝ≥0∞) (hp : 1 < p) (_hpt : p < ∞) [Fact (1 ≤ p)],
        ∃ U : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
          (∀ f, toL1 p hp.le (U f) = T (toL1 p hp.le f)) ∧
          ‖U‖ ≤ ‖T‖ ^ (1 / p.toReal) * ‖S‖ ^ (1 - 1 / p.toReal)

/-- The complex scalar specialization of the full source conclusion. -/
def ComplexInterpolation : Prop := InterpolationFor.{u} ℂ

/-- Both scalar fields required by the source, including the zero measure. -/
def EndpointInterpolation : Prop := InterpolationFor.{u} ℂ ∧ InterpolationFor.{u} ℝ

/-- Norm-preserving endpoint complexification. The embedding is the
pointwise isometric inclusion of real functions into complex functions.
This is a helper proposition; it is not a hypothesis of EndpointInterpolation. -/
def ComplexificationAt (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ),
    ∃ C : Lp ℂ p μ →L[ℂ] Lp ℂ p μ, ‖C‖ = ‖T‖ ∧
      ∀ f, C (Complex.ofRealCLM.compLp f) = Complex.ofRealCLM.compLp (T f)

/-- Assembly lemma, conditional on the two separate endpoint constructions.
The main source statement above retains no such assumptions. -/
def RealInterpolationFromComplexification : Prop :=
  ComplexificationAt.{u} 1 → ComplexificationAt.{u} ∞ → InterpolationFor.{u} ℝ

end ExpandedFA.BanachGeometry.EndpointInterpolationSpec
