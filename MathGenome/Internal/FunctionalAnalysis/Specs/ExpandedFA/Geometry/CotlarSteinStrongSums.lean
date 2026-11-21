import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CotlarSteinFinite
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
The infinite-family assertion of `fa2:p2:cotlar`, paper.tex 13048–13077.
The row sums are actual convergent sums of nonnegative real numbers. Summability
is explicit because a nonsummable real `tsum` is assigned zero by convention.
The index type is arbitrary (and may be empty); no separability is imposed.
Strong convergence means norm convergence on each vector. Its hypothesis is
required on the specified dense set, hence in particular on a dense subspace.
The canonical infinite sum uses the net of all finite subsets, ordered by
inclusion. The filter variant also covers prescribed sequences or other nets
of finite partial sums by their image filter. No convergence is asserted from
the row estimates alone.
-/

noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.Geometry.CotlarSteinStrongSums.Spec
universe u v w

/-- Every finite subfamily satisfies the original sharp bound. -/
def PartialSumEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : ι → H →L[𝕜] H) (A B : ℝ),
    0 ≤ A → 0 ≤ B →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).adjoint.comp (T j)‖) ∧
      ∑' j, Real.sqrt ‖(T i).adjoint.comp (T j)‖ ≤ A) →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).comp (T j).adjoint‖) ∧
      ∑' j, Real.sqrt ‖(T i).comp (T j).adjoint‖ ≤ B) →
    ∀ s : Finset ι, ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (A * B)

/-- Convergence on a dense set extends along the same nontrivial filter of
finite partial sums, with a bounded linear limit and the sharp norm bound. -/
def StrongSumAlongFilter : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : ι → H →L[𝕜] H) (A B : ℝ),
    0 ≤ A → 0 ≤ B →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).adjoint.comp (T j)‖) ∧
      ∑' j, Real.sqrt ‖(T i).adjoint.comp (T j)‖ ≤ A) →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).comp (T j).adjoint‖) ∧
      ∑' j, Real.sqrt ‖(T i).comp (T j).adjoint‖ ≤ B) →
    ∀ (D : Set H) (l : Filter (Finset ι)) [NeBot l],
    Dense D →
    (∀ d ∈ D, ∃ y : H,
      Tendsto (fun s => (∑ i ∈ s, T i) d) l (𝓝 y)) →
    ∃ S : H →L[𝕜] H, ‖S‖ ≤ Real.sqrt (A * B) ∧
      ∀ x : H, Tendsto (fun s => (∑ i ∈ s, T i) x) l (𝓝 (S x))

/-- The net of finite partial sums has a strong sum on all of H whenever it
converges strongly on the specified dense subset. -/
def StrongSum : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : ι → H →L[𝕜] H) (A B : ℝ),
    0 ≤ A → 0 ≤ B →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).adjoint.comp (T j)‖) ∧
      ∑' j, Real.sqrt ‖(T i).adjoint.comp (T j)‖ ≤ A) →
    (∀ i, Summable (fun j => Real.sqrt ‖(T i).comp (T j).adjoint‖) ∧
      ∑' j, Real.sqrt ‖(T i).comp (T j).adjoint‖ ≤ B) →
    ∀ D : Set H, Dense D →
    (∀ d ∈ D, ∃ y : H,
      Tendsto (fun s : Finset ι => (∑ i ∈ s, T i) d) atTop (𝓝 y)) →
    ∃ S : H →L[𝕜] H, ‖S‖ ≤ Real.sqrt (A * B) ∧
      ∀ x : H, Tendsto (fun s : Finset ι => (∑ i ∈ s, T i) x) atTop (𝓝 (S x))

end ExpandedFA.Geometry.CotlarSteinStrongSums.Spec
