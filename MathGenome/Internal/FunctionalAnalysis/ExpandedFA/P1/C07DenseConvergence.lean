import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07DenseConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Extending strong convergence from a dense set, without completeness of the
domain. The only use of target completeness is to obtain pointwise limits from
the Cauchy estimate; the given-limit variant is proved directly. -/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C07DenseConvergence

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A common operator norm bound controls distances by the same constant. -/
theorem operator_dist_le_of_norm_le (S : E →L[𝕜] F) {M : ℝ}
    (hS : ‖S‖ ≤ M) (x y : E) : dist (S x) (S y) ≤ M * dist x y :=
  (S.dist_le_opNorm x y).trans (mul_le_mul_of_nonneg_right hS dist_nonneg)

/-- The three-term estimate makes the image sequence Cauchy at every point.
This step uses neither domain nor target completeness. -/
theorem cauchySeq_on_all_of_dense (D : Set E) (M : ℝ)
    (Tn : ℕ → E →L[𝕜] F) (hD : Dense D) (hM : 0 ≤ M)
    (hbound : ∀ n, ‖Tn n‖ ≤ M)
    (hc : ∀ d ∈ D, CauchySeq (fun n => Tn n d)) (x : E) :
    CauchySeq (fun n => Tn n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hden : 0 < 4 * (M + 1) := by positivity
  obtain ⟨d, hd, hxd⟩ := hD.exists_dist_lt x (div_pos hε hden)
  have hsmall : 2 * M * dist x d < ε / 2 := by
    have h := (lt_div_iff₀ hden).mp hxd
    nlinarith [dist_nonneg (x := x) (y := d)]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc d hd) (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  calc
    dist (Tn m x) (Tn n x) ≤
        dist (Tn m x) (Tn m d) + dist (Tn m d) (Tn n d) +
          dist (Tn n d) (Tn n x) := dist_triangle4 _ _ _ _
    _ ≤ M * dist x d + dist (Tn m d) (Tn n d) + M * dist x d := by
      gcongr
      · exact operator_dist_le_of_norm_le _ (hbound m) x d
      · simpa only [dist_comm d x] using
          operator_dist_le_of_norm_le _ (hbound n) d x
    _ < ε := by linarith [hN m hm n hn]

/-- The Banach-target conclusion, including the quantitative norm bound. -/
theorem dense_convergence : Spec.DenseConvergence := by
  intro 𝕜 E F _ _ _ _ _ _ D M Tn hD hbound hconv
  have hM : 0 ≤ M := (norm_nonneg (Tn 0)).trans (hbound 0)
  have hc (x : E) : CauchySeq (fun n => Tn n x) := by
    apply cauchySeq_on_all_of_dense D M Tn hD hM hbound
    intro d hd
    obtain ⟨y, hy⟩ := hconv d hd
    exact hy.cauchySeq
  choose f hf using fun x => cauchySeq_tendsto_of_complete (hc x)
  let L : E →ₗ[𝕜] F :=
    { toFun := f
      map_add' := fun x y => tendsto_nhds_unique
        (by simpa only [map_add] using hf (x + y)) ((hf x).add (hf y))
      map_smul' := fun a x => tendsto_nhds_unique
        (by simpa only [map_smul] using hf (a • x)) ((hf x).const_smul a) }
  have hb (x : E) : ‖L x‖ ≤ M * ‖x‖ :=
    le_of_tendsto (hf x).norm (Eventually.of_forall fun n =>
      (Tn n).le_of_opNorm_le (hbound n) x)
  let T : E →L[𝕜] F := L.mkContinuous M hb
  exact ⟨T, hf, T.opNorm_le_bound hM hb⟩

/-- Convergence to a given bounded operator extends from the dense set even
when the target is incomplete. -/
theorem dense_convergence_to_given_operator :
    Spec.DenseConvergenceToGivenOperator := by
  intro 𝕜 E F _ _ _ _ _ D M Tn T hD hbound hconv x
  have hM : 0 ≤ M := (norm_nonneg (Tn 0)).trans (hbound 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : 0 < 2 * (M + ‖T‖ + 1) := by positivity
  obtain ⟨d, hd, hxd⟩ := hD.exists_dist_lt x (div_pos hε hden)
  have hsmall : (M + ‖T‖) * dist x d < ε / 2 := by
    have h := (lt_div_iff₀ hden).mp hxd
    nlinarith [dist_nonneg (x := x) (y := d)]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hconv d hd) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  calc
    dist (Tn n x) (T x) ≤
        dist (Tn n x) (Tn n d) + dist (Tn n d) (T d) + dist (T d) (T x) :=
      dist_triangle4 _ _ _ _
    _ ≤ M * dist x d + dist (Tn n d) (T d) + ‖T‖ * dist x d := by
      gcongr
      · exact operator_dist_le_of_norm_le _ (hbound n) x d
      · simpa only [dist_comm d x] using T.dist_le_opNorm d x
    _ < ε := by nlinarith [hN n hn]

end ExpandedFA.P1.C07DenseConvergence
