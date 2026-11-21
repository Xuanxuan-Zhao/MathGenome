import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertBesselParseval
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Conventions
import Mathlib.Tactic.Linarith

noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace ExpandedFA.Hilbert.PreHilbertBesselParseval
universe u v w

theorem finite_projection_identity : Spec.FiniteProjectionIdentity.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x F
  have h₂ :
      (∑ i ∈ F, ∑ j ∈ F, ⟪e i, x⟫_𝕜 * ⟪x, e j⟫_𝕜 * ⟪e j, e i⟫_𝕜) =
        (∑ k ∈ F, ⟪e k, x⟫_𝕜 * ⟪x, e k⟫_𝕜 : 𝕜) :=
    he.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, RCLike.re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [RCLike.mul_conj]
    norm_cast
  unfold fourierPartialSum
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

theorem finite_bessel : Spec.FiniteBessel.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x F
  exact he.sum_inner_products_le x

theorem coefficient_squares_summable : Spec.CoefficientSquaresSummable.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  exact he.inner_products_summable x

theorem bessel : Spec.Bessel.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  exact he.tsum_inner_products_le x

theorem countable_coefficient_support : Spec.CountableCoefficientSupport.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  simpa only [Function.support, ne_eq, sq_eq_zero_iff, norm_eq_zero] using
    (he.inner_products_summable x).countable_support

section Approximation
variable {𝕜 : Type u} {E : Type v} {ι : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {e : ι → E}

theorem fourierPartialSum_add (x y : E) (F : Finset ι) :
    fourierPartialSum 𝕜 e (x + y) F =
      fourierPartialSum 𝕜 e x F + fourierPartialSum 𝕜 e y F := by
  simp [fourierPartialSum, inner_add_right, add_smul, Finset.sum_add_distrib]

theorem fourierPartialSum_smul (c : 𝕜) (x : E) (F : Finset ι) :
    fourierPartialSum 𝕜 e (c • x) F = c • fourierPartialSum 𝕜 e x F := by
  simp [fourierPartialSum, inner_smul_right, Finset.smul_sum, smul_smul]

theorem fourierPartialSum_sub (x y : E) (F : Finset ι) :
    fourierPartialSum 𝕜 e (x - y) F =
      fourierPartialSum 𝕜 e x F - fourierPartialSum 𝕜 e y F := by
  simp [fourierPartialSum, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

theorem norm_sub_fourierPartialSum_le (he : Orthonormal 𝕜 e) (x : E) (F : Finset ι) :
    ‖x - fourierPartialSum 𝕜 e x F‖ ≤ ‖x‖ := by
  have h := finite_projection_identity 𝕜 E ι e he x F
  have hs : 0 ≤ ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (x - fourierPartialSum 𝕜 e x F), norm_nonneg x]

/-- On a finite linear combination the net is eventually constant. -/
theorem fourierPartialSum_eventually_eq (he : Orthonormal 𝕜 e) {z : E}
    (hz : z ∈ Submodule.span 𝕜 (Set.range e)) :
    ∀ᶠ F : Finset ι in atTop, fourierPartialSum 𝕜 e z F = z := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with F hF
    have hi : i ∈ F := hF (Finset.mem_singleton_self i)
    simp [fourierPartialSum, orthonormal_iff_ite.mp he, hi]
  | zero => exact Filter.Eventually.of_forall (by simp [fourierPartialSum])
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with F hx hy
    rw [fourierPartialSum_add, hx, hy]
  | smul c x _ hx =>
    filter_upwards [hx] with F hx
    rw [fourierPartialSum_smul, hx]

end Approximation

theorem closedSpan_iff_net_convergence : Spec.ClosedSpanIffNetConvergence.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  constructor
  · intro hx
    have hx' : x ∈ closure (Submodule.span 𝕜 (Set.range e) : Set E) := hx
    rw [Metric.mem_closure_iff] at hx'
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨z, hz, hzx⟩ := hx' ε hε
    filter_upwards [fourierPartialSum_eventually_eq he hz] with F hF
    have herr : (x - z) - fourierPartialSum 𝕜 e (x - z) F =
        x - fourierPartialSum 𝕜 e x F := by
      rw [fourierPartialSum_sub, hF]
      abel
    calc
      dist (fourierPartialSum 𝕜 e x F) x =
          ‖(x - z) - fourierPartialSum 𝕜 e (x - z) F‖ := by
        rw [herr, dist_eq_norm, norm_sub_rev]
      _ ≤ ‖x - z‖ := norm_sub_fourierPartialSum_le he (x - z) F
      _ < ε := by simpa only [dist_eq_norm] using hzx
  · intro hx
    apply (Submodule.span 𝕜 (Set.range e)).isClosed_topologicalClosure.mem_of_tendsto hx
    apply Filter.Eventually.of_forall
    intro F
    apply Submodule.le_topologicalClosure
    unfold fourierPartialSum
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem net_convergence_iff_parseval : Spec.NetConvergenceIffParseval.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  have hs : Tendsto (fun F : Finset ι => ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2)
      atTop (𝓝 (∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2)) :=
    (he.inner_products_summable x).hasSum
  constructor
  · intro hx
    have hz : Tendsto (fun F => ‖x - fourierPartialSum 𝕜 e x F‖ ^ 2)
        atTop (𝓝 0) := by
      simpa using (((tendsto_const_nhds (x := x)).sub hx).norm.pow 2)
    have hd : Tendsto (fun F => ‖x‖ ^ 2 - ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [finite_projection_identity 𝕜 E ι e he] using hz
    have h := tendsto_nhds_unique (tendsto_const_nhds.sub hs) hd
    exact (sub_eq_zero.mp h).symm
  · intro hp
    have hd : Tendsto (fun F : Finset ι => ‖x‖ ^ 2 - ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2)
        atTop (𝓝 (‖x‖ ^ 2 - ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2)) :=
      tendsto_const_nhds.sub hs
    rw [hp, sub_self] at hd
    have hz : Tendsto (fun F => ‖x - fourierPartialSum 𝕜 e x F‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [finite_projection_identity 𝕜 E ι e he] using hd
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, norm_sub_rev]
      using hz.sqrt

theorem closedSpan_iff_parseval : Spec.ClosedSpanIffParseval.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he x
  exact (closedSpan_iff_net_convergence 𝕜 E ι e he x).trans
    (net_convergence_iff_parseval 𝕜 E ι e he x)

theorem total_iff_parseval : Spec.TotalIffParseval.{u, v, w} := by
  intro 𝕜 E ι _ _ _ e he
  rw [Submodule.eq_top_iff']
  exact forall_congr' (fun x => closedSpan_iff_parseval 𝕜 E ι e he x)

end ExpandedFA.Hilbert.PreHilbertBesselParseval

/- Mathlib proof attribution
Adapted portion near line 12:
The finite orthonormal expansion and squared-norm calculation for Bessel's
inequality.

Upstream: Mathlib/Analysis/InnerProductSpace/Orthonormal.lean (around line 437)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
