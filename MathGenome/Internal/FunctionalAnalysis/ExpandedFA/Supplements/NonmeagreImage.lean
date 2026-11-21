import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.NonmeagreImage
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.QuotientFactorization
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Nonmeagre actual ranges

The category argument uses nonmeagreness of `Set.range T`, without any
completeness hypothesis on the codomain. A geometric residual correction
then gives exact preimages with controlled norms using only completeness
of the domain. Finally the closed kernel quotient transfers completeness
to the original codomain, so the usual open mapping theorem applies.

The rescaling and residual estimates adapt the proofs of
`ContinuousLinearMap.exists_approx_preimage_norm_le` and
`ContinuousLinearMap.exists_preimage_norm_le` in Mathlib (Sébastien Gouëzel,
Apache 2.0), replacing their use of Baire completeness in the codomain by
the actual-range category hypothesis.
-/

open Function Metric Set Filter Finset Topology NNReal

namespace ExpandedFA.Supplements.NonmeagreImage

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Some bounded image has a closure with interior, directly from
nonmeagreness of the actual range in the ambient codomain. -/
theorem exists_image_ball_closure_interior (T : E →L[𝕜] F)
    (hT : ¬ IsMeagre (Set.range T)) :
    ∃ n : ℕ, (interior (closure (T '' ball 0 n))).Nonempty := by
  by_contra! h
  apply hT
  have hmeagre : IsMeagre (⋃ n : ℕ, T '' ball 0 n) := by
    apply isMeagre_iUnion
    intro n
    apply IsNowhereDense.isMeagre
    exact h n
  apply hmeagre.mono
  rintro y ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact mem_iUnion.mpr ⟨n, mem_image_of_mem T (by simpa using hn)⟩

/-- Uniformly bounded approximate preimages with a fixed contraction of
the residual; no completeness is used in this step. -/
theorem exists_approx_preimages (f : E →L[𝕜] F)
    (hT : ¬ IsMeagre (Set.range f)) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have hi := exists_image_ball_closure_interior f hT
  simp only [Set.Nonempty, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hi
  rcases hi with ⟨n, a, ε, εpos, H⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rcases rescale_to_shell hc (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ ≤ 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by grind [dist_eq_norm']
    have J : ‖f (d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ :=
      calc
        ‖f (d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rw [map_smul, inv_mul_cancel₀ hd, one_smul]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = 1 / 2 * ‖y‖ := by simp [δ, field]; norm_num
    rw [← dist_eq_norm] at J
    have K : ‖d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, norm_inv]
        _ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          exact mul_le_mul dinv
            ((norm_sub_le _ _).trans (add_le_add hx₁.le hx₂.le))
            (norm_nonneg _) (by positivity)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨d⁻¹ • x, J, K⟩

/-- Geometric residual lifting takes place in the complete domain; the
codomain remains merely normed. -/
theorem controlled_preimages_of_approx [CompleteSpace E] (f : E →L[𝕜] F)
    (C : ℝ) (C0 : 0 ≤ C)
    (hC : ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    ∃ D > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ D * ‖y‖ := by
  classical
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- Controlled preimages bound the inverse of the closed-kernel quotient
isomorphism. This proves completeness for the original codomain norm. -/
theorem completeSpace_of_controlled_preimages [CompleteSpace E]
    (T : E →L[𝕜] F) (C : ℝ)
    (hC : ∀ y, ∃ x, T x = y ∧ ‖x‖ ≤ C * ‖y‖) : CompleteSpace F := by
  have hsurj : Surjective T := fun y => (hC y).imp fun _ h => h.1
  let : IsClosed (T.ker : Set E) := T.isClosed_ker
  let : CompleteSpace (E ⧸ T.ker) := Submodule.Quotient.completeSpace T.ker
  let e : (E ⧸ T.ker) ≃ₗ[𝕜] F := T.toLinearMap.quotKerEquivOfSurjective hsurj
  have hforward : ∀ z, ‖e z‖ ≤ ‖T‖ * ‖z‖ := by
    intro z
    obtain ⟨x, rfl⟩ := T.ker.mkQ_surjective z
    exact ExpandedFA.P1.QuotientFactorization.quotient_lift_bound T.ker T le_rfl
      (T.ker.mkQ x)
  have hinverse : ∀ y, ‖e.symm y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨x, hx, hnorm⟩ := hC y
    have he : e (T.ker.mkQ x) = y := hx
    have hsym : e.symm y = T.ker.mkQ x := by rw [← he, e.symm_apply_apply]
    rw [hsym]
    exact (Submodule.Quotient.norm_mk_le T.ker x).trans hnorm
  let eL := e.toContinuousLinearEquivOfBounds ‖T‖ C hforward hinverse
  exact (eL.isUniformEmbedding.isUniformInducing.completeSpace_congr eL.surjective).mp
    inferInstance

/-- Nonmeagreness is imposed on the actual range, in the ambient normed
codomain. Completeness of the codomain is a conclusion, not a hypothesis. -/
theorem nonmeagre_image : Spec.ImageConclusion := by
  intro 𝕜 E F _ _ _ _ _ _ T hT
  obtain ⟨C, hC, happ⟩ := exists_approx_preimages T hT
  obtain ⟨D, _, hD⟩ := controlled_preimages_of_approx T C hC happ
  have hsurj : Surjective T := fun y => (hD y).imp fun _ h => h.1
  let : CompleteSpace F := completeSpace_of_controlled_preimages T D hD
  exact ⟨hsurj, T.isOpenMap hsurj, inferInstance⟩

end ExpandedFA.Supplements.NonmeagreImage

/- Mathlib proof attribution
Adapted portion near line 50:
The successive approximation and series construction in the nonmeagre-image
argument.

Upstream: Mathlib/Analysis/Normed/Operator/Banach.lean (around line 92)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
