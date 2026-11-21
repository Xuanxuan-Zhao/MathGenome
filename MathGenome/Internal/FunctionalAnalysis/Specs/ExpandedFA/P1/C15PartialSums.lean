import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15CoordinateContinuity

/-! Partial-sum bounds, paper.tex 3879–3909. Indices start at zero, so
`range N` denotes the manuscript's first N terms. The continuous realizations
below agree with the original algebraic partial sums at every vector.
The real supremum is accompanied by boundedness, including the empty basis. -/
open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.C15PartialSums.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def basisConstant (T : ℕ → E →L[𝕜] E) : ℝ := ⨆ N, ‖T N‖

structure ProjectionBounds (P : ℕ → E → E) (T : ℕ → E →L[𝕜] E) : Prop where
  agrees : ∀ N x, T N x = P N x
  zero : ∀ x, P 0 x = 0
  composition : ∀ N M x, P N (P M x) = P (min N M) x
  converges : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x)
  bounded : BddAbove (Set.range fun N => ‖T N‖)
  nonneg : 0 ≤ basisConstant T
  one_le : Nontrivial E → 1 ≤ basisConstant T
  norm_bound : ∀ N x, ‖P N x‖ ≤ basisConstant T * ‖x‖
  contractive : ∀ N x,
    ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm P (P N x) ≤ ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm P x

def RawBounds : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ T : ℕ → E →L[𝕜] E,
      ProjectionBounds (ExpandedFA.P1.C15Basis.Spec.rawPartialSum h) T ∧
      (∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
        ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a m‖ ≤
          basisConstant T * ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a N‖) ∧
      (∀ i x, ‖ExpandedFA.P1.C15Basis.Spec.rawCoordinates h x i‖ * ‖e i‖ ≤
        2 * basisConstant T * ‖x‖)

def FiniteBounds : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    ∃ T : ℕ → E →L[𝕜] E,
      ProjectionBounds (ExpandedFA.P1.C15Basis.Spec.finitePartialSum h) T ∧
      (∀ (a : Fin d → 𝕜) (m N : ℕ), m ≤ N →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < m), a i • e i‖ ≤
          basisConstant T *
            ‖∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < N), a i • e i‖) ∧
      (∀ i x, ‖ExpandedFA.P1.C15Basis.Spec.finiteCoordinates h x i‖ * ‖e i‖ ≤
        2 * basisConstant T * ‖x‖) ∧
      (∀ N, d ≤ N → ∀ x, ExpandedFA.P1.C15Basis.Spec.finitePartialSum h N x = x) ∧
      (d = 0 → basisConstant T = 0)

/-- Expected polymorphic type and value for the actual real supremum. -/
def basisConstantType : Type _ :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], (ℕ → E →L[𝕜] E) → ℝ

def basisConstantValue : basisConstantType := @basisConstant

end ExpandedFA.P1.C15PartialSums.Spec
