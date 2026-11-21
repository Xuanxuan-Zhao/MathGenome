import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrongRotundityCriteria
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs

namespace ExpandedFA.P1.StrongRotundityCriteria
open Filter Metric
open scoped Topology
noncomputable section
universe u v
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-one functional's real part is bounded by the norm. -/
lemma realPart_le_norm (f : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1) (x : E) :
    RCLike.re (f x) ≤ ‖x‖ := by
  calc
    RCLike.re (f x) ≤ ‖f x‖ := RCLike.re_le_norm _
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ = ‖x‖ := by rw [hf, one_mul]

/-- Real parts commute with real scalar multiplication, including over ℂ. -/
lemma realPart_smul [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (f : E →L[𝕜] 𝕜) (a : ℝ) (x : E) :
    RCLike.re (f (a • x)) = a * RCLike.re (f x) := by
  change (RCLike.reCLM.comp (f.restrictScalars ℝ)) (a • x) = _
  rw [map_smul]
  rfl

/-- Asymptotically equal sequences have the same Cauchy behavior. -/
lemma cauchySeq_of_norm_sub_tendsto_zero {x y : ℕ → E} (hy : CauchySeq y)
    (hxy : Tendsto (fun n => ‖x n - y n‖) atTop (𝓝 0)) : CauchySeq x := by
  rw [Metric.cauchySeq_iff] at hy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hy (ε / 3) (by positivity)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hxy.eventually (gt_mem_nhds (by positivity : 0 < ε / 3)))
  refine ⟨max N M, fun m hm n hn => ?_⟩
  have hm' := hM m (le_trans (le_max_right _ _) hm)
  have hn' := hM n (le_trans (le_max_right _ _) hn)
  have hmn := hN m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have htri := dist_triangle4 (x m) (y m) (y n) (x n)
  rw [dist_eq_norm] at hmn ⊢
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (y n)] at htri
  linarith

/-- Recover a Cauchy sequence from its Cauchy normalized directions. -/
lemma cauchySeq_of_normalized [NormedSpace ℝ E] {x : ℕ → E} {r : ℝ}
    (hx : ∀ n, x n ≠ 0) (hr : Tendsto (fun n => ‖x n‖) atTop (𝓝 r))
    (hz : CauchySeq (fun n => ‖x n‖⁻¹ • x n)) : CauchySeq x := by
  let z : ℕ → E := fun n => ‖x n‖⁻¹ • x n
  have hzn : ∀ n, ‖z n‖ = 1 := fun n => by
    simp [z, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hx n))]
  have hrec : ∀ n, ‖x n‖ • z n = x n := fun n => by
    simp [z, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (hx n))]
  have hc : CauchySeq (fun n => r • z n) :=
    (uniformContinuous_const_smul r).comp_cauchySeq hz
  apply cauchySeq_of_norm_sub_tendsto_zero hc
  have heq : (fun n => ‖x n - r • z n‖) = (fun n => |‖x n‖ - r|) := by
    funext n
    conv_lhs => rw [← hrec n]
    rw [← sub_smul, norm_smul, hzn n, Real.norm_eq_abs, mul_one]
  rw [heq]
  simpa using (hr.sub_const r).abs

lemma slice_bounded (f : E →L[𝕜] 𝕜) (δ : ℝ) :
    Bornology.IsBounded (Spec.slice 𝕜 E f δ) :=
  (isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    (fun _ hx => by simpa [mem_closedBall_zero_iff] using hx.1)

/-- The ε–δ formulation agrees with the actual right-hand diameter limit.
Monotonicity of slices supplies all smaller positive δ from a single slice. -/
lemma shrinkingSlices_iff_smallSliceDiameters :
    Spec.ShrinkingSlices 𝕜 E ↔ Spec.SmallSliceDiameters 𝕜 E := by
  constructor
  · intro h f hf ε hε
    have hev := (h f hf).eventually (gt_mem_nhds hε)
    obtain ⟨a, ha, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    exact ⟨a / 2, half_pos ha, hsub ⟨half_pos ha, half_lt_self ha⟩⟩
  · intro h f hf
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := h f hf ε hε
    apply (nhdsGT_basis (0 : ℝ)).mem_iff.2
    refine ⟨δ, hδ, fun η hη => ?_⟩
    have hsub : Spec.slice 𝕜 E f η ⊆ Spec.slice 𝕜 E f δ := by
      rintro z ⟨hz, he⟩
      exact ⟨hz, by linarith [hη.2]⟩
    have hdiam := diam_mono hsub (slice_bounded f δ)
    simpa [Real.dist_eq, abs_of_nonneg diam_nonneg] using hdiam.trans_lt hd

/-- Small slices make every unit maximizing sequence Cauchy. -/
theorem unitMaximizersCauchy_of_smallSliceDiameters
    (h : Spec.SmallSliceDiameters 𝕜 E) : Spec.UnitMaximizersCauchy 𝕜 E := by
  intro f hf x hxn hfx
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h f hf ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hfx.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith)))
  exact ⟨N, fun m hm n hn =>
    (dist_le_diam_of_mem (slice_bounded f δ) ⟨(hxn m).le, hN m hm⟩
      ⟨(hxn n).le, hN n hn⟩).trans_lt hd⟩

/-- A bound on the real functional on an open ball also bounds its operator norm.
This uses the supremum on the open unit ball, so norm attainment is unnecessary. -/
lemma radius_mul_norm_le [NormedSpace ℝ E] (h : E →L[ℝ] ℝ) {r α : ℝ}
    (hr : 0 < r) (ha : ∀ x ∈ ball (0 : E) r, h x < α) : r * ‖h‖ ≤ α := by
  have hα : 0 < α := by simpa using ha 0 (mem_ball_self hr)
  have hn : ‖h‖ ≤ α / r := by
    rw [← h.sSup_unit_ball_eq_norm]
    apply csSup_le ((nonempty_ball.mpr zero_lt_one).image _)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < 1 := by simpa using hx
    have hb : r • x ∈ ball (0 : E) r := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hr] using
        (mul_lt_mul_of_pos_left hx' hr)
    have hnb : -(r • x) ∈ ball (0 : E) r := by simpa using hb
    have hp := ha (r • x) hb
    have hm := ha (-(r • x)) hnb
    simp only [map_neg, map_smul, smul_eq_mul] at hp hm
    change ‖h x‖ ≤ α / r
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div]
      apply (div_le_iff₀ hr).2
      nlinarith
    · exact (le_div_iff₀ hr).2 (by nlinarith)
  nlinarith [(le_div_iff₀ hr).1 hn]

/-- Separate the open distance ball from the convex set and normalize the
separator, retaining a scalar-linear dual over either ℝ or ℂ. -/
lemma distance_supporting_functional (C : Set E) (hC : C.Nonempty)
    (p : E) (hr : 0 < infDist p C)
    (hc : let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
      Convex ℝ C) :
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ ∀ c ∈ C, infDist p C ≤ RCLike.re (f (c - p)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨h, α, hn, ha, hb⟩ := C06.real_normed_open_convex_separation
    (ball p (infDist p C)) C (nonempty_ball.mpr hr) hC
    (convex_ball p _) hc (Set.disjoint_left.2 (fun c hball hmem =>
      (mem_ball.1 hball).not_ge (by simpa [dist_comm] using infDist_le_dist_of_mem (x := p) hmem))) isOpen_ball
  have hnorm : 0 < ‖h‖ := norm_pos_iff.2 hn
  have hbound : infDist p C * ‖h‖ ≤ α - h p := by
    apply radius_mul_norm_le h hr
    intro x hx
    have hxp : x + p ∈ ball p (infDist p C) := by
      simpa [dist_eq_norm] using hx
    have := ha (x + p) hxp
    rw [map_add] at this
    linarith
  let f : E →L[𝕜] 𝕜 := StrongDual.extendRCLike (‖h‖⁻¹ • h)
  refine ⟨f, ?_, ?_⟩
  · simp [f, StrongDual.norm_extendRCLike, norm_smul,
      inv_mul_cancel₀ (ne_of_gt hnorm)]
  · intro c hmem
    have hsep := hb c hmem
    simp only [f, StrongDual.re_extendRCLike_apply, smul_apply,
      smul_eq_mul, map_sub]
    rw [← mul_sub, ← div_eq_inv_mul]
    apply (le_div_iff₀ hnorm).2
    nlinarith

/-- Unit maximizing sequences control minimizing sequences at arbitrary points. -/
theorem minimizersCauchy_of_unitMaximizersCauchy
    (h : Spec.UnitMaximizersCauchy 𝕜 E) : Spec.MinimizersCauchy 𝕜 E := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hC hc p x hx hlim
  by_cases hr : infDist p C = 0
  · have hxlim : Tendsto x atTop (𝓝 p) := by
      apply tendsto_iff_dist_tendsto_zero.2
      simpa [hr] using hlim
    exact hxlim.cauchySeq
  · have hrpos : 0 < infDist p C := lt_of_le_of_ne infDist_nonneg (Ne.symm hr)
    obtain ⟨f, hf, hfc⟩ := distance_supporting_functional C hC p hrpos hc
    let y : ℕ → E := fun n => x n - p
    have hyn : Tendsto (fun n => ‖y n‖) atTop (𝓝 (infDist p C)) := by
      simpa [y, dist_eq_norm] using hlim
    have hyp : ∀ n, 0 < ‖y n‖ := fun n => hrpos.trans_le (by
      simpa [y, dist_eq_norm, norm_sub_rev] using infDist_le_dist_of_mem (hx n))
    let z : ℕ → E := fun n => ‖y n‖⁻¹ • y n
    have hzn : ∀ n, ‖z n‖ = 1 := fun n => by
      simp [z, norm_smul, inv_mul_cancel₀ (ne_of_gt (hyp n))]
    have hfz : ∀ n, RCLike.re (f (z n)) = RCLike.re (f (y n)) / ‖y n‖ := by
      intro n
      change RCLike.re (f (‖y n‖⁻¹ • y n)) = _
      rw [realPart_smul]
      exact (div_eq_inv_mul _ _).symm
    have heval : Tendsto (fun n => RCLike.re (f (z n))) atTop (𝓝 1) := by
      have hlo : Tendsto (fun n => infDist p C / ‖y n‖) atTop (𝓝 1) := by
        have hconst : Tendsto (fun _ : ℕ => infDist p C) atTop (𝓝 (infDist p C)) :=
          tendsto_const_nhds
        convert hconst.div hyn hr using 1; simp [hr]
      apply hlo.squeeze tendsto_const_nhds
      · intro n
        change infDist p C / ‖y n‖ ≤ RCLike.re (f (z n))
        rw [hfz n]
        exact (div_le_div_iff_of_pos_right (hyp n)).2 (hfc (x n) (hx n))
      · intro n
        simpa [hzn n] using realPart_le_norm f hf (z n)
    have hz : CauchySeq z := h f hf z hzn heval
    have hy : CauchySeq y := cauchySeq_of_normalized
      (fun n => norm_ne_zero_iff.1 (ne_of_gt (hyp n))) hyn hz
    rw [Metric.cauchySeq_iff] at hy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa [y, dist_eq_norm] using hN m hm n hn

/-- The minimizing-sequence condition also controls closed-ball maximizing
sequences. Rescale into the affine hyperplane Re f = 1. -/
lemma ballMaximizersCauchy_of_minimizersCauchy
    (h : Spec.MinimizersCauchy 𝕜 E) (f : E →L[𝕜] 𝕜) (hf : ‖f‖ = 1)
    (x : ℕ → E) (hxn : ∀ n, ‖x n‖ ≤ 1)
    (hfx : Tendsto (fun n => RCLike.re (f (x n))) atTop (𝓝 1)) : CauchySeq x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hnormx : Tendsto (fun n => ‖x n‖) atTop (𝓝 1) :=
    hfx.squeeze tendsto_const_nhds (fun n => realPart_le_norm f hf (x n)) hxn
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hfx.eventually (lt_mem_nhds zero_lt_one))
  apply (cauchySeq_shift N).1
  let u : ℕ → E := fun n => x (n + N)
  let a : ℕ → ℝ := fun n => RCLike.re (f (u n))
  have hap : ∀ n, 0 < a n := fun n => hN _ (Nat.le_add_left _ _)
  have halim : Tendsto a atTop (𝓝 1) := (tendsto_add_atTop_iff_nat N).2 hfx
  have hunlim : Tendsto (fun n => ‖u n‖) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat N).2 hnormx
  let y : ℕ → E := fun n => (a n)⁻¹ • u n
  let H : Set E := {z | RCLike.re (f z) = 1}
  have hyH : ∀ n, y n ∈ H := by
    intro n
    change RCLike.re (f ((a n)⁻¹ • u n)) = 1
    rw [realPart_smul]
    exact inv_mul_cancel₀ (ne_of_gt (hap n))
  have hH : H.Nonempty := ⟨y 0, hyH 0⟩
  have hcH : Convex ℝ H :=
    (convex_singleton (1 : ℝ)).linear_preimage
      (RCLike.reCLM.comp (f.restrictScalars ℝ)).toLinearMap
  have hynorm : ∀ n, ‖y n‖ = ‖u n‖ / a n := by
    intro n
    simp [y, norm_smul, abs_of_pos (hap n), div_eq_inv_mul]
  have hynlim : Tendsto (fun n => ‖y n‖) atTop (𝓝 1) := by
    convert hunlim.div halim one_ne_zero using 1 <;> try norm_num
    funext n
    exact hynorm n
  have hdist : infDist (0 : E) H = 1 := by
    apply le_antisymm
    · apply ge_of_tendsto hynlim
      exact Eventually.of_forall (fun n => by
        simpa using infDist_le_dist_of_mem (x := (0 : E)) (hyH n))
    · apply (le_infDist hH).2
      intro z hz
      have hh := realPart_le_norm f hf z
      change RCLike.re (f z) = 1 at hz
      simpa [hz] using hh
  have hyc : CauchySeq y := h H hH hcH 0 y hyH (by
    simpa [hdist] using hynlim)
  apply cauchySeq_of_norm_sub_tendsto_zero hyc
  have hrec : ∀ n, a n • y n = u n := by
    intro n
    simp [y, smul_smul, mul_inv_cancel₀ (ne_of_gt (hap n))]
  have heq : (fun n => ‖u n - y n‖) = (fun n => |a n - 1| * ‖y n‖) := by
    funext n
    conv_lhs => rw [← hrec n]
    have hd : a n • y n - y n = (a n - 1) • y n := by
      rw [sub_smul, one_smul]
    rw [hd, norm_smul, Real.norm_eq_abs]
  rw [heq]
  simpa using ((halim.sub_const 1).abs.mul hynlim)

/-- In particular the minimizing-sequence property implies criterion 2. -/
theorem unitMaximizersCauchy_of_minimizersCauchy
    (h : Spec.MinimizersCauchy 𝕜 E) : Spec.UnitMaximizersCauchy 𝕜 E := by
  intro f hf x hx hfx
  exact ballMaximizersCauchy_of_minimizersCauchy h f hf x (fun n => (hx n).le) hfx

/-- If slice diameters did not shrink, interleaving separated points from
successively thinner slices would give a non-Cauchy maximizing sequence. -/
theorem smallSliceDiameters_of_minimizersCauchy
    (h : Spec.MinimizersCauchy 𝕜 E) : Spec.SmallSliceDiameters 𝕜 E := by
  classical
  intro f hf ε hε
  by_contra hnone
  push Not at hnone
  have hpair : ∀ n : ℕ, ∃ x y : E,
      x ∈ Spec.slice 𝕜 E f (1 / ((n : ℝ) + 1)) ∧
      y ∈ Spec.slice 𝕜 E f (1 / ((n : ℝ) + 1)) ∧ ε / 2 < dist x y := by
    intro n
    by_contra hp
    push Not at hp
    have hd := diam_le_of_forall_dist_le (by positivity : 0 ≤ ε / 2)
      (fun x hx y hy => hp x y hx hy)
    have hfails := hnone (1 / ((n : ℝ) + 1)) (by positivity)
    linarith
  choose x y hx hy hsep using hpair
  let z : ℕ → E := fun n => if n % 2 = 0 then x (n / 2) else y (n / 2)
  have hzn : ∀ n, ‖z n‖ ≤ 1 := by
    intro n
    dsimp only [z]
    split_ifs
    · exact (hx _).1
    · exact (hy _).1
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨2 * b, fun n hn =>
      (Nat.le_div_iff_mul_le (by omega)).2 (by omega)⟩
  have hδ : Tendsto (fun n : ℕ => 1 / (((n / 2 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hdiv
  have hlo : Tendsto (fun n : ℕ => 1 - 1 / (((n / 2 : ℕ) : ℝ) + 1))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hδ
  have heval : Tendsto (fun n => RCLike.re (f (z n))) atTop (𝓝 1) := by
    apply hlo.squeeze tendsto_const_nhds
    · intro n
      change 1 - 1 / (((n / 2 : ℕ) : ℝ) + 1) ≤ RCLike.re (f (z n))
      dsimp only [z]
      split_ifs
      · exact (hx _).2.le
      · exact (hy _).2.le
    · intro n
      exact (realPart_le_norm f hf (z n)).trans (hzn n)
  have hz := ballMaximizersCauchy_of_minimizersCauchy h f hf z hzn heval
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hz (ε / 2) (by positivity)
  have heven : z (2 * N) = x N := by simp [z]
  have hodd : z (2 * N + 1) = y N := by simp [z, Nat.add_div]
  have hsmall := hN (2 * N) (by omega) (2 * N + 1) (by omega)
  rw [heven, hodd] at hsmall
  exact (hsep N).not_ge hsmall.le

/-- All three source criteria are equivalent with the displayed norm, including
in incomplete and zero spaces, and for convex sets that are not closed. -/
theorem strong_rotundity_criteria : Spec.Equivalence.{u,v} := by
  intro 𝕜 E _ _ _
  have h12 := @unitMaximizersCauchy_of_smallSliceDiameters 𝕜 E _ _ _
  have h23 := @minimizersCauchy_of_unitMaximizersCauchy 𝕜 E _ _ _
  have h31 := @smallSliceDiameters_of_minimizersCauchy 𝕜 E _ _ _
  have h32 := @unitMaximizersCauchy_of_minimizersCauchy 𝕜 E _ _ _
  exact ⟨shrinkingSlices_iff_smallSliceDiameters.trans
    ⟨h12, fun h => h31 (h23 h)⟩, ⟨h23, h32⟩⟩

end
end ExpandedFA.P1.StrongRotundityCriteria
