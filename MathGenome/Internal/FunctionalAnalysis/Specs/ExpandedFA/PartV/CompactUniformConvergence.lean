import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03Neumann
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
Independent statements of `fa2:p5:compact-uniform-convergence`, paper.tex
lines 22843–22865. Scalars include both ℝ and ℂ. The first statement makes
no completeness assumption on either space, and the pointwise limit is an
arbitrary function: boundedness and linearity are conclusions. Compact sets
may be empty. The inverse statement uses explicit bounded two-sided inverses,
so it also includes zero spaces without a norm-one assumption on the identity.
-/

open Filter
open scoped Topology

namespace ExpandedFA.PartV.CompactUniformConvergence.Spec

universe u v w

def BoundedPointwiseCompactConvergence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (Tn : ℕ → X →L[𝕜] Y) (T : X → Y) (M : ℝ),
    0 ≤ M → (∀ n, ‖Tn n‖ ≤ M) →
    (∀ x, Tendsto (fun n => Tn n x) atTop (𝓝 (T x))) →
    ∃ S : X →L[𝕜] Y, (∀ x, S x = T x) ∧ ‖S‖ ≤ M ∧
      ∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun n x => Tn n x) T atTop K

def BanachPointwiseCompactConvergence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X]
    (Tn : ℕ → X →L[𝕜] Y) (T : X → Y),
    (∀ x, Tendsto (fun n => Tn n x) atTop (𝓝 (T x))) →
    ∃ M : ℝ, 0 ≤ M ∧ (∀ n, ‖Tn n‖ ≤ M) ∧
      ∃ S : X →L[𝕜] Y, (∀ x, S x = T x) ∧ ‖S‖ ≤ M ∧
        ∀ K : Set X, IsCompact K →
          TendstoUniformlyOn (fun n x => Tn n x) T atTop K

/-- The usual Neumann series, the inverse norm bound, the inverse-difference
bound θ/(1-θ) ‖A⁻¹‖, and the exact identity from the source proof.
`B` denotes any one of the manuscript's approximating maps `A_n`. -/
def InversePerturbation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[𝕜] Y) (Ai : Y →L[𝕜] X),
    A.comp Ai = ContinuousLinearMap.id 𝕜 Y →
    Ai.comp A = ContinuousLinearMap.id 𝕜 X →
    ∀ B : X →L[𝕜] Y, ‖Ai.comp (B - A)‖ < 1 →
    ∃ Bi : Y →L[𝕜] X,
      B.comp Bi = ContinuousLinearMap.id 𝕜 Y ∧
      Bi.comp B = ContinuousLinearMap.id 𝕜 X ∧
      HasSum (fun n : ℕ => ((-(Ai.comp (B - A))) ^ n).comp Ai) Bi ∧
      Bi = ∑' n : ℕ, ((-(Ai.comp (B - A))) ^ n).comp Ai ∧
      Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range (N + 1), ((-(Ai.comp (B - A))) ^ n).comp Ai)
        atTop (𝓝 Bi) ∧
      ‖Bi‖ ≤ ‖Ai‖ / (1 - ‖Ai.comp (B - A)‖) ∧
      ‖Bi - Ai‖ ≤ (‖Ai.comp (B - A)‖ / (1 - ‖Ai.comp (B - A)‖)) * ‖Ai‖ ∧
      Bi - Ai = Bi.comp ((A - B).comp Ai)

/-- Direct applicability to a bounded bijection between Banach spaces:
boundedness of its inverse is established, rather than imposed separately.
The chosen `Ai` is a two-sided inverse of `A` and hence is uniquely determined. -/
def BijectiveInversePerturbation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[𝕜] Y), Function.Bijective A →
    ∃ Ai : Y →L[𝕜] X,
      A.comp Ai = ContinuousLinearMap.id 𝕜 Y ∧
      Ai.comp A = ContinuousLinearMap.id 𝕜 X ∧
      ∀ B : X →L[𝕜] Y, ‖Ai.comp (B - A)‖ < 1 →
      ∃ Bi : Y →L[𝕜] X,
        B.comp Bi = ContinuousLinearMap.id 𝕜 Y ∧
        Bi.comp B = ContinuousLinearMap.id 𝕜 X ∧
        HasSum (fun n : ℕ => ((-(Ai.comp (B - A))) ^ n).comp Ai) Bi ∧
        Bi = ∑' n : ℕ, ((-(Ai.comp (B - A))) ^ n).comp Ai ∧
        Tendsto (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1), ((-(Ai.comp (B - A))) ^ n).comp Ai)
          atTop (𝓝 Bi) ∧
        ‖Bi‖ ≤ ‖Ai‖ / (1 - ‖Ai.comp (B - A)‖) ∧
        ‖Bi - Ai‖ ≤ (‖Ai.comp (B - A)‖ / (1 - ‖Ai.comp (B - A)‖)) * ‖Ai‖ ∧
        Bi - Ai = Bi.comp ((A - B).comp Ai)

end ExpandedFA.PartV.CompactUniformConvergence.Spec
