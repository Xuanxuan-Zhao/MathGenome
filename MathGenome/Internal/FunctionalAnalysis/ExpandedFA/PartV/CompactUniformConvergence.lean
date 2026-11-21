import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.CompactUniformConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03Neumann
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
Uniform boundedness supplies a common bound on a Banach domain. Without
completeness, a given common bound passes to the pointwise limit. A finite
net in each compact set then controls convergence uniformly. The inverse
assertion factors B = A (id - Q), Q = -A⁻¹(B-A), and uses the accepted
Neumann theorem, including its remainder after the constant term.
-/

open Filter
open scoped Topology

namespace ExpandedFA.PartV.CompactUniformConvergence

theorem bounded_pointwise_compact_convergence :
    Spec.BoundedPointwiseCompactConvergence := by
  intro 𝕜 X Y _ _ _ _ _ Tn T M hM hbound hlim
  have hb : Bornology.IsBounded (Set.range Tn) := by
    apply (isBounded_iff_forall_norm_le).2
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  let S : X →L[𝕜] Y := ContinuousLinearMap.ofTendstoOfBoundedRange
    T Tn (tendsto_pi_nhds.2 hlim) hb
  have hS (x : X) : S x = T x := rfl
  have hn : ‖S‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro x
    exact le_of_tendsto (hlim x |>.norm) (Eventually.of_forall fun n =>
      (Tn n).le_of_opNorm_le (hbound n) x)
  refine ⟨S, hS, hn, ?_⟩
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, _, hs, hcover⟩ := hK.finite_cover_balls hδ
  have hnet : ∀ᶠ n in atTop, ∀ y ∈ s, dist (T y) (Tn n y) < ε / 2 := by
    apply (hs.eventually_all).2
    intro y _
    exact ((Metric.tendsto_nhds.1 (hlim y)) (ε / 2) (by linarith)).mono
      (fun n hn => (dist_comm _ _).trans_lt hn)
  filter_upwards [hnet] with n hn' x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ s, dist x y < δ := by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover hx
  have hnxy : dist (Tn n x) (Tn n y) ≤ M * dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using
      (Tn n).le_of_opNorm_le (hbound n) (x - y)
  have hSxy : dist (T x) (T y) ≤ M * dist x y := by
    simpa only [← hS, dist_eq_norm, ← map_sub] using
      S.le_of_opNorm_le hn (x - y)
  have hsmall : M * dist x y < ε / 4 := by
    have hle : M * dist x y ≤ (M + 1) * dist x y :=
      mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    have hlt := mul_lt_mul_of_pos_left hxy (show 0 < M + 1 by linarith)
    have heq : (M + 1) * δ = ε / 4 := by
      dsimp [δ]
      field_simp [ne_of_gt (show 0 < M + 1 by linarith)]
    linarith
  calc
    dist (T x) (Tn n x) ≤ dist (T x) (T y) +
        dist (T y) (Tn n y) + dist (Tn n y) (Tn n x) :=
      dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (Tn n y)] ; linarith [hn' y hy]

theorem banach_pointwise_compact_convergence :
    Spec.BanachPointwiseCompactConvergence := by
  intro 𝕜 X Y _ _ _ _ _ _ Tn T hlim
  have hb : ∀ x, ∃ C : ℝ, ∀ n, ‖Tn n x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
      (Metric.isBounded_range_of_tendsto (fun n => Tn n x) (hlim x))
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  obtain ⟨M, hM, hbound⟩ :=
    ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness 𝕜 X Y ℕ Tn hb
  exact ⟨M, hM, hbound,
    bounded_pointwise_compact_convergence 𝕜 X Y Tn T M hM hbound hlim⟩

theorem inverse_perturbation : Spec.InversePerturbation := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A Ai hAAi hAiA B hθ
  let Q : X →L[𝕜] X := -(Ai.comp (B - A))
  have hQ : ‖Q‖ < 1 := by simpa only [Q, norm_neg] using hθ
  obtain ⟨S, hsum, _, _, hleft, hright, hnorm, htail, _⟩ :=
    ExpandedFA.P1.C03Neumann.neumann_inversion 𝕜 X Q hQ
  let Bi : Y →L[𝕜] X := S.comp Ai
  have hfactor : B = A.comp (ContinuousLinearMap.id 𝕜 X - Q) := by
    simp only [Q, sub_neg_eq_add, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_id]
    rw [← ContinuousLinearMap.comp_assoc, hAAi, ContinuousLinearMap.id_comp]
    abel
  have hinner : Ai.comp B = ContinuousLinearMap.id 𝕜 X - Q := by
    simp [Q, ContinuousLinearMap.comp_sub, hAiA]
  have hsumBi : HasSum (fun n : ℕ => (Q ^ n).comp Ai) Bi :=
    ((ContinuousLinearMap.compL 𝕜 Y X X).flip Ai).hasSum hsum
  have hdiff : Bi - Ai = (S - ContinuousLinearMap.id 𝕜 X).comp Ai := by
    simp [Bi, ContinuousLinearMap.sub_comp]
  have hdiffS : ‖S - ContinuousLinearMap.id 𝕜 X‖ ≤ ‖Q‖ / (1 - ‖Q‖) := by
    simpa [ContinuousLinearMap.one_def] using htail 0
  have hBBi : B.comp Bi = ContinuousLinearMap.id 𝕜 Y := by
    calc
      B.comp Bi = A.comp (((ContinuousLinearMap.id 𝕜 X - Q).comp S).comp Ai) := by
        rw [hfactor]; rfl
      _ = ContinuousLinearMap.id 𝕜 Y := by rw [hleft]; simpa using hAAi
  have hBiB : Bi.comp B = ContinuousLinearMap.id 𝕜 X := by
    calc
      Bi.comp B = S.comp (Ai.comp B) := rfl
      _ = ContinuousLinearMap.id 𝕜 X := by rw [hinner, hright]
  refine ⟨Bi, hBBi, hBiB, hsumBi, hsumBi.tsum_eq.symm,
    hsumBi.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1), ?_, ?_, ?_⟩
  · calc
      ‖Bi‖ ≤ ‖S‖ * ‖Ai‖ := S.opNorm_comp_le Ai
      _ ≤ (1 / (1 - ‖Q‖)) * ‖Ai‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg Ai)
      _ = ‖Ai‖ / (1 - ‖Ai.comp (B - A)‖) := by
        simp only [Q, norm_neg, div_eq_mul_inv, one_mul, mul_comm]
  · calc
      ‖Bi - Ai‖ = ‖(S - ContinuousLinearMap.id 𝕜 X).comp Ai‖ := congrArg norm hdiff
      _ ≤ ‖S - ContinuousLinearMap.id 𝕜 X‖ * ‖Ai‖ :=
        (S - ContinuousLinearMap.id 𝕜 X).opNorm_comp_le Ai
      _ ≤ (‖Q‖ / (1 - ‖Q‖)) * ‖Ai‖ :=
        mul_le_mul_of_nonneg_right hdiffS (norm_nonneg Ai)
      _ = _ := by simp only [Q, norm_neg]
  · symm
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      hAAi, ← ContinuousLinearMap.comp_assoc, hBiB,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

theorem bijective_inverse_perturbation : Spec.BijectiveInversePerturbation := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hA
  let e : X ≃L[𝕜] Y := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  let Ai : Y →L[𝕜] X := e.symm.toContinuousLinearMap
  have hAAi : A.comp Ai = ContinuousLinearMap.id 𝕜 Y := by
    ext y
    exact e.apply_symm_apply y
  have hAiA : Ai.comp A = ContinuousLinearMap.id 𝕜 X := by
    ext x
    exact e.symm_apply_apply x
  exact ⟨Ai, hAAi, hAiA, fun B hB =>
    inverse_perturbation 𝕜 X Y A Ai hAAi hAiA B hB⟩

end ExpandedFA.PartV.CompactUniformConvergence
