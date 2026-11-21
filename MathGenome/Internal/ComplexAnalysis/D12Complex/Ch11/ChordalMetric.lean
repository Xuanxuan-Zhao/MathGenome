import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.Mobius
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open scoped Topology
open Filter
noncomputable section
namespace D12Complex.Chordal

namespace Definitions
abbrev chordal := D12Complex.Chordal.chordal
abbrev stereographic := D12Complex.Chordal.stereographic
abbrev chartRotation := D12Complex.Chordal.chartRotation
abbrev reciprocal := D12Complex.Chordal.reciprocal
end Definitions

@[simp] theorem chordal_finite (z w : ℂ) :
    chordal (sphereFinite z) (sphereFinite w) =
      ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) := rfl
theorem chordal_infty :
    chordal sphereInfty sphereInfty = 0 ∧ ∀ z : ℂ,
      chordal (sphereFinite z) sphereInfty = 1 / Real.sqrt (1 + ‖z‖ ^ 2) ∧
      chordal sphereInfty (sphereFinite z) = 1 / Real.sqrt (1 + ‖z‖ ^ 2) :=
  ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
theorem weight_pos (z : ℂ) : 0 < weight z := by
  unfold weight
  positivity
theorem weight_sq (z : ℂ) : weight z ^ 2 = 1 + ‖z‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)
theorem chordal_nonneg (p q : RiemannSphere) : 0 ≤ chordal p q := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact le_refl 0
    | coe z => exact le_of_lt (one_div_pos.mpr (weight_pos z))
  | coe z =>
    induction q using OnePoint.rec with
    | infty => exact le_of_lt (one_div_pos.mpr (weight_pos z))
    | coe w => exact div_nonneg (norm_nonneg _) (mul_pos (weight_pos z) (weight_pos w)).le
theorem chordal_comm (p q : RiemannSphere) : chordal p q = chordal q p := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec <;> rfl
  | coe z =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe w =>
      change ‖z - w‖ / (weight z * weight w) = ‖w - z‖ / (weight w * weight z)
      rw [norm_sub_rev, mul_comm]
theorem chordal_self (p : RiemannSphere) : chordal p p = 0 := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [chordal]
theorem chordal_eq_zero_iff (p q : RiemannSphere) : chordal p q = 0 ↔ p = q := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => simp [chordal]
    | coe z =>
      change (1 / weight z = 0) ↔ _
      simp [ne_of_gt (weight_pos z)]
  | coe z =>
    induction q using OnePoint.rec with
    | infty =>
      change (1 / weight z = 0) ↔ _
      simp [ne_of_gt (weight_pos z)]
    | coe w =>
      change (‖z - w‖ / (weight z * weight w) = 0) ↔ _
      simp [ne_of_gt (weight_pos z), ne_of_gt (weight_pos w), sub_eq_zero]
theorem chordal_finite_sq (z w : ℂ) :
    chordal (sphereFinite z) (sphereFinite w) ^ 2 =
      Complex.normSq (z - w) / ((1 + Complex.normSq z) * (1 + Complex.normSq w)) := by
  change (‖z - w‖ / (weight z * weight w)) ^ 2 = _
  rw [div_pow, mul_pow, weight_sq, weight_sq]
  simp only [Complex.sq_norm]
theorem chordal_finite_infty_sq (z : ℂ) :
    chordal (sphereFinite z) sphereInfty ^ 2 = 1 / (1 + Complex.normSq z) := by
  change (1 / weight z) ^ 2 = _
  rw [div_pow, weight_sq, one_pow, Complex.sq_norm]

theorem stereographic_dist_finite_sq (z w : ℂ) :
    dist (stereographic (sphereFinite z)) (stereographic (sphereFinite w)) ^ 2 =
      4 * chordal (sphereFinite z) (sphereFinite w) ^ 2 := by
  rw [chordal_finite_sq, dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [stereographic, sphereFinite, OnePoint.elim_some, finiteStereographic,
    Fin.sum_univ_succ, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  have hz : 1 + (z.re * z.re + z.im * z.im) ≠ 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hw : 1 + (w.re * w.re + w.im * w.im) ≠ 0 := by nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  field_simp [hz, hw]
  all_goals ring
theorem stereographic_dist_infty_sq (z : ℂ) :
    dist (stereographic (sphereFinite z)) (stereographic sphereInfty) ^ 2 =
      4 * chordal (sphereFinite z) sphereInfty ^ 2 := by
  rw [chordal_finite_infty_sq, dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [stereographic, sphereFinite, sphereInfty, OnePoint.elim_some,
    OnePoint.elim_infty, finiteStereographic, northPole,
    Fin.sum_univ_succ, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, sub_zero, Complex.sq_norm, Complex.normSq_apply]
  have hz : 1 + (z.re * z.re + z.im * z.im) ≠ 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  field_simp [hz]
  all_goals ring
theorem stereographic_dist_sq (p q : RiemannSphere) :
    dist (stereographic p) (stereographic q) ^ 2 = 4 * chordal p q ^ 2 := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => simp [chordal]
    | coe z =>
      rw [dist_comm, chordal_comm]
      exact stereographic_dist_infty_sq z
  | coe z =>
    induction q using OnePoint.rec with
    | infty => exact stereographic_dist_infty_sq z
    | coe w => exact stereographic_dist_finite_sq z w
theorem chordal_half_chord (p q : RiemannSphere) :
    chordal p q = dist (stereographic p) (stereographic q) / 2 := by
  have h := stereographic_dist_sq p q
  have h₁ := chordal_nonneg p q
  have h₂ := dist_nonneg (x := stereographic p) (y := stereographic q)
  nlinarith
theorem stereographic_injective : Function.Injective stereographic := by
  intro p q hpq
  apply (chordal_eq_zero_iff p q).mp
  rw [chordal_half_chord, hpq, dist_self, zero_div]
theorem stereographic_mem_sphere (p : RiemannSphere) :
    stereographic p ∈ Metric.sphere (0 : Euclidean3) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
    EuclideanSpace.real_norm_sq_eq]
  induction p using OnePoint.rec with
  | infty => norm_num [stereographic, northPole, Fin.sum_univ_succ]
  | coe z =>
    simp only [stereographic, OnePoint.elim_some, finiteStereographic,
      Fin.sum_univ_succ, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, one_pow, Complex.sq_norm, Complex.normSq_apply]
    have hz : 1 + (z.re * z.re + z.im * z.im) ≠ 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    field_simp [hz]
    all_goals ring

theorem continuous_finiteStereographic : Continuous finiteStereographic := by
  have hd : Continuous (fun z : ℂ => 1 + ‖z‖ ^ 2) :=
    continuous_const.add (continuous_norm.pow 2)
  have hn : ∀ z : ℂ, 1 + ‖z‖ ^ 2 ≠ 0 := by intro z; positivity
  unfold finiteStereographic
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (continuous_const.mul Complex.continuous_re).div hd hn
  · exact (continuous_const.mul Complex.continuous_im).div hd hn
  · exact ((continuous_norm.pow 2).sub continuous_const).div hd hn
theorem continuous_stereographic : Continuous stereographic := by
  apply continuous_iff_continuousAt.mpr
  intro p
  induction p using OnePoint.rec with
  | coe z =>
    exact OnePoint.continuousAt_coe.mpr continuous_finiteStereographic.continuousAt
  | infty =>
    apply OnePoint.continuousAt_infty'.mpr
    rw [tendsto_iff_dist_tendsto_zero]
    have hnorm : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_norm_cobounded_atTop
    have hden : Tendsto (fun z : ℂ => 1 + ‖z‖ ^ 2) (Bornology.cobounded ℂ) atTop :=
      tendsto_atTop_mono (fun z => by linarith : ∀ z : ℂ, ‖z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2) hnorm
    have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hden)
    have hlim := hinv.const_mul 2
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hlim
    convert hlim using 1
    · funext z
      have h := chordal_half_chord (sphereFinite z) sphereInfty
      change dist (stereographic (sphereFinite z)) (stereographic sphereInfty) = _
      change 1 / weight z = _ / 2 at h
      simp only [weight, one_div] at h
      dsimp [Function.comp_def]
      linarith
    · norm_num

/-- The induced metric is explicitly rescaled by one half, and its topology is
replaced by the already fixed one-point topology using a compact embedding. -/
theorem chordal_metric : Specs.D12Complex.Ch11.ChordalMetric.chordal_metric_type := by
  let f : RiemannSphere → Euclidean3 := fun p => (1 / 2 : ℝ) • stereographic p
  have hf : Continuous f :=
    (continuous_const : Continuous (fun _ : RiemannSphere => (1 / 2 : ℝ))).smul
      continuous_stereographic
  have hi : Function.Injective f := by
    intro p q h
    apply stereographic_injective
    exact (smul_right_injective Euclidean3 (by norm_num : (1 / 2 : ℝ) ≠ 0)) h
  let m := MetricSpace.induced f hi inferInstance
  have ht : (inferInstance : TopologicalSpace RiemannSphere) =
      m.toUniformSpace.toTopologicalSpace :=
    (hf.isClosedEmbedding hi).isEmbedding.isInducing.eq_induced
  let m' : MetricSpace RiemannSphere := m.replaceTopology ht
  have hd : ∀ p q, @dist RiemannSphere m'.toDist p q = chordal p q := by
    intro p q
    change dist ((1 / 2 : ℝ) • stereographic p) ((1 / 2 : ℝ) • stereographic q) = _
    rw [dist_smul₀, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      chordal_half_chord]
    ring
  letI : MetricSpace RiemannSphere := m'
  exact ⟨m', rfl, hd, inferInstance, inferInstance⟩

theorem stereographic_surjective (v : Euclidean3)
    (hv : v ∈ Metric.sphere (0 : Euclidean3) 1) : ∃ p, stereographic p = v := by
  have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
  have hs : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have hh := congrArg (fun t : ℝ => t ^ 2) hn
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, add_assoc] using hh
  by_cases htop : v 2 = 1
  · have hx : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have hy : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    refine ⟨sphereInfty, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [stereographic, sphereInfty, northPole, hx, hy, htop]
  · have hd : 1 - v 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm htop)
    let z : ℂ := ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩
    have hz : 1 + ‖z‖ ^ 2 = 2 / (1 - v 2) := by
      simp only [z, Complex.sq_norm, Complex.normSq_mk]
      field_simp [hd]
      <;> nlinarith [hs]
    refine ⟨sphereFinite z, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · change 2 * z.re / (1 + ‖z‖ ^ 2) = v 0
      rw [hz]
      dsimp [z]
      field_simp [hd]
    · change 2 * z.im / (1 + ‖z‖ ^ 2) = v 1
      rw [hz]
      dsimp [z]
      field_simp [hd]
    · change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = v 2
      rw [show ‖z‖ ^ 2 - 1 = (1 + ‖z‖ ^ 2) - 2 by ring, hz]
      field_simp [hd]
      all_goals ring
theorem stereographic_homeomorph :
    Specs.D12Complex.Ch11.ChordalMetric.stereographic_homeomorph_type := by
  let f : RiemannSphere → Metric.sphere (0 : Euclidean3) 1 :=
    fun p => ⟨stereographic p, stereographic_mem_sphere p⟩
  have hc : Continuous f := continuous_stereographic.subtype_mk _
  have hi : Function.Injective f := fun p q h => stereographic_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨p, hp⟩ := stereographic_surjective v.val v.property
    exact ⟨p, Subtype.ext hp⟩
  let e := Equiv.ofBijective f ⟨hi, hs⟩
  exact ⟨e.toHomeomorphOfContinuousClosed hc hc.isClosedMap, fun _ => rfl⟩

/-- Squared chordal distance is the normalized determinant of homogeneous
coordinates. Nonzero representatives are required, including at infinity. -/
theorem chordal_pair_sq (x y u v : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0)
    (huv : u ≠ 0 ∨ v ≠ 0) :
    chordal (Mobius.spherePair x y) (Mobius.spherePair u v) ^ 2 =
      Complex.normSq (x * v - u * y) /
        ((Complex.normSq x + Complex.normSq y) * (Complex.normSq u + Complex.normSq v)) := by
  have hxy' : Complex.normSq x + Complex.normSq y ≠ 0 := by
    rcases hxy with hx | hy
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hx) (Complex.normSq_nonneg _))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr hy))
  have huv' : Complex.normSq u + Complex.normSq v ≠ 0 := by
    rcases huv with hu | hv
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hu) (Complex.normSq_nonneg _))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr hv))
  have hxyrev : Complex.normSq y + Complex.normSq x ≠ 0 := by simpa only [add_comm] using hxy'
  have huvrev : Complex.normSq v + Complex.normSq u ≠ 0 := by simpa only [add_comm] using huv'
  by_cases hy : y = 0
  · simp only [hy, Complex.normSq_zero, add_zero] at hxy'
    by_cases hv : v = 0
    · simp [Mobius.spherePair, hy, hv, chordal, sphereInfty]
    · have hv' := ne_of_gt (Complex.normSq_pos.mpr hv)
      simp only [Mobius.spherePair, hy, hv, ite_true, ite_false]
      rw [chordal_comm, chordal_finite_infty_sq]
      simp only [Complex.normSq_div, mul_zero, sub_zero, Complex.normSq_mul,
        Complex.normSq_zero, add_zero] at *
      field_simp [hxy', huv', huvrev, hv']
      all_goals ring
  · have hy' := ne_of_gt (Complex.normSq_pos.mpr hy)
    by_cases hv : v = 0
    · simp only [hv, Complex.normSq_zero, add_zero] at huv'
      simp only [Mobius.spherePair, hy, hv, ite_true, ite_false]
      rw [chordal_finite_infty_sq]
      simp only [Complex.normSq_div, mul_zero, zero_sub, Complex.normSq_neg,
        Complex.normSq_mul, Complex.normSq_zero, add_zero] at *
      field_simp [hxy', hxyrev, huv', hy']
      all_goals ring
    · have hv' := ne_of_gt (Complex.normSq_pos.mpr hv)
      simp only [Mobius.spherePair, hy, hv, ite_false]
      rw [chordal_finite_sq]
      have hsub : x / y - u / v = (x * v - u * y) / (y * v) := by
        field_simp
      rw [hsub]
      simp only [Complex.normSq_div, Complex.normSq_mul]
      rw [one_add_div hy', one_add_div hv']
      field_simp [hxy', huv', hxyrev, huvrev, hy', hv']
      all_goals ring
theorem spherePair_representation (p : RiemannSphere) :
    ∃ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) ∧ p = Mobius.spherePair x y := by
  induction p using OnePoint.rec with
  | infty => exact ⟨1, 0, Or.inl one_ne_zero, by simp [Mobius.spherePair, sphereInfty]⟩
  | coe z => exact ⟨z, 1, Or.inr one_ne_zero, (Mobius.spherePair_self z).symm⟩
theorem rotation_pair_weight (a x y : ℂ) :
    Complex.normSq (x - a * y) + Complex.normSq (star a * x + y) =
      (1 + Complex.normSq a) * (Complex.normSq x + Complex.normSq y) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  all_goals ring
theorem rotation_pair_nonzero (a x y : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    x - a * y ≠ 0 ∨ star a * x + y ≠ 0 := by
  by_contra h
  push Not at h
  have hw := rotation_pair_weight a x y
  rw [h.1, h.2] at hw
  have ha : 0 < 1 + Complex.normSq a := by have := Complex.normSq_nonneg a; linarith
  have hp : 0 < Complex.normSq x + Complex.normSq y := by
    rcases hxy with hx | hy
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hx) (Complex.normSq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr hy)
  have := mul_pos ha hp
  simp only [Complex.normSq_zero, add_zero] at hw
  linarith
theorem chartRotation_pair (a x y : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    chartRotation a (Mobius.spherePair x y) =
      Mobius.spherePair (x - a * y) (star a * x + y) := by
  rw [chartRotation, Mobius.mobiusMap_pair _ x y hxy]
  simp [sub_eq_add_neg]
theorem chartRotation_chordal (a : ℂ) (p q : RiemannSphere) :
    chordal (chartRotation a p) (chartRotation a q) = chordal p q := by
  obtain ⟨x, y, hxy, rfl⟩ := spherePair_representation p
  obtain ⟨u, v, huv, rfl⟩ := spherePair_representation q
  apply (sq_eq_sq₀ (chordal_nonneg _ _) (chordal_nonneg _ _)).mp
  rw [chartRotation_pair _ _ _ hxy, chartRotation_pair _ _ _ huv,
    chordal_pair_sq _ _ _ _ (rotation_pair_nonzero a x y hxy) (rotation_pair_nonzero a u v huv),
    chordal_pair_sq _ _ _ _ hxy huv, rotation_pair_weight, rotation_pair_weight]
  have he : (x - a * y) * (star a * u + v) - (u - a * v) * (star a * x + y) =
      (1 + a * star a) * (x * v - u * y) := by ring
  rw [he, Complex.normSq_mul]
  have hf : Complex.normSq (1 + a * star a) = (1 + Complex.normSq a) ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    all_goals ring
  rw [hf]
  have ha : 1 + Complex.normSq a ≠ 0 := by have := Complex.normSq_nonneg a; linarith
  field_simp [ha]

/-- The reciprocal map preserves the determinant modulus and swaps each
pair's two coordinate weights, so zero and infinity require no exceptions. -/
theorem reciprocal_chordal (p q : RiemannSphere) :
    chordal (reciprocal p) (reciprocal q) = chordal p q := by
  obtain ⟨x, y, hxy, rfl⟩ := spherePair_representation p
  obtain ⟨u, v, huv, rfl⟩ := spherePair_representation q
  have hp : reciprocal (Mobius.spherePair x y) = Mobius.spherePair y x := by
    rw [reciprocal, Mobius.mobiusMap_pair _ x y hxy]
    simp
  have hq : reciprocal (Mobius.spherePair u v) = Mobius.spherePair v u := by
    rw [reciprocal, Mobius.mobiusMap_pair _ u v huv]
    simp
  apply (sq_eq_sq₀ (chordal_nonneg _ _) (chordal_nonneg _ _)).mp
  rw [hp, hq, chordal_pair_sq _ _ _ _ hxy.symm huv.symm, chordal_pair_sq _ _ _ _ hxy huv]
  rw [show y * u - v * x = -(x * v - u * y) by ring, Complex.normSq_neg]
  simp only [add_comm]


theorem chartRotation_bijective (a : ℂ) : Function.Bijective (chartRotation a) := by
  apply Mobius.mobiusMap_bijective
  have ha : (1 : ℂ) + a * star a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [Complex.mul_re] at hr
    nlinarith [sq_nonneg a.re, sq_nonneg a.im]
  simpa [Mobius.Regular, Matrix.det_fin_two] using ha

theorem reciprocal_bijective : Function.Bijective reciprocal := by
  apply Mobius.mobiusMap_bijective
  simp [Mobius.Regular, Matrix.det_fin_two]

end D12Complex.Chordal
