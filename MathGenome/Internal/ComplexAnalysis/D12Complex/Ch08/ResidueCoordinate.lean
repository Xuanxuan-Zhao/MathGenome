import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueCoordinate
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace D12Complex.ResidueCoordinate

open Metric
open Laurent Residue

lemma mem_puncturedDisk_iff {a z : ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ annulus a 0 (ENNReal.ofReal r) ↔ z ≠ a ∧ z ∈ ball a r := by
  simp only [annulus, mem_ofPred_eq, norm_pos_iff, sub_ne_zero,
    mem_ball, dist_eq_norm]
  rw [← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff hr]
  rfl

lemma isOpen_puncturedDisk (a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen (annulus a 0 (ENNReal.ofReal r)) := by
  have he : annulus a 0 (ENNReal.ofReal r) = ball a r \ {a} := by
    ext z
    simpa only [Set.mem_sdiff, mem_singleton_iff, and_comm] using mem_puncturedDisk_iff hr
  rw [he]
  exact isOpen_ball.sdiff isClosed_singleton

theorem local_coordinate_neighborhood :
    Specs.D12Complex.Ch08.ResidueCoordinate.local_coordinate_neighborhood_type := by
  intro f φ a b R Ω hR hf hφ hb hφb hn
  obtain ⟨U, V, ψ, hbU, haV, hUΩ, hp, _, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse Ω φ b hφ hb hn
  rw [hφb] at haV
  obtain ⟨t, ht, htR⟩ := Laurent.exists_admissible_radius (le_refl (0 : ℝ))
    (by simpa using hR)
  have he : ∀ᶠ w in 𝓝 b, φ w ∈ ball a t := by
    apply (hφ.2 b hb).continuousAt
    rw [hφb]
    exact ball_mem_nhds a ht
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hp.1.1.mem_nhds hbU) he)
  have hball : ball b δ ⊆ U := fun w hw => (hδsub hw).1
  have hmap : MapsTo φ (annulus b 0 (ENNReal.ofReal δ)) (annulus a 0 R) := by
    intro w hw
    obtain ⟨hwb, hwd⟩ := (mem_puncturedDisk_iff hδ).mp hw
    have hne : φ w ≠ a := by
      intro heq
      apply hwb
      apply hp.2.2.2.2.1.injOn (hball hwd) hbU
      exact heq.trans hφb.symm
    refine ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hne), ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal
      (mem_ball_iff_norm.mp (hδsub hwd).2).le).trans_lt htR
  refine ⟨U, V, ψ, δ, hbU, haV, hUΩ, hp, hδ, hball, hmap,
    isOpen_puncturedDisk b hδ, ?_⟩
  intro w hw
  have hwΩ := hUΩ (hball ((mem_puncturedDisk_iff hδ).mp hw).2)
  have hd : DifferentiableOn ℂ φ Ω := fun z hz => (hφ.2 z hz).differentiableWithinAt
  exact ((hf.2 _ (hmap hw)).comp w (hφ.2 w hwΩ)).mul
    ((DifferentiableOn.deriv hd hφ.1).differentiableAt (hφ.1.mem_nhds hwΩ))

/-- Every pulled-back Laurent monomial other than exponent -1 is exact. -/
theorem circleIntegral_monomial_of_ne (φ : ℂ → ℂ) (a b : ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hd : ∀ w ∈ sphere b ρ, DifferentiableAt ℂ φ w)
    (hne : ∀ w ∈ sphere b ρ, φ w ≠ a) {n : ℤ} (hn : n ≠ -1) :
    circleIntegral (fun w => (φ w - a) ^ n * deriv φ w) b ρ = 0 := by
  have hn' : (n + 1 : ℂ) ≠ 0 := by
    rw [← Int.cast_one, ← Int.cast_add, Ne, Int.cast_eq_zero]
    omega
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hρ
    (f := fun w => (φ w - a) ^ (n + 1) / (n + 1))
  intro w hw
  have h := ((hasDerivAt_zpow (n + 1) (φ w - a)
    (Or.inl (sub_ne_zero.mpr (hne w hw)))).comp w
      ((hd w hw).hasDerivAt.sub_const a)).div_const (n + 1 : ℂ)
  apply HasDerivAt.hasDerivWithinAt
  convert h using 1 <;>
    simp only [Function.comp_def, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  field_simp

/-- The simple-zero factorization computes the one remaining monomial. -/
theorem circleIntegral_logarithmic (φ : ℂ → ℂ) (a b : ℂ) (U : Set ℂ)
    (hφ : HolomorphicOn U φ) (hb : b ∈ U) (hφb : φ b = a)
    (hn : deriv φ b ≠ 0) (hinj : InjOn φ U) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall b ρ ⊆ U) :
    circleIntegral (fun w => (φ w - a) ^ (-1 : ℤ) * deriv φ w) b ρ =
      (2 * Real.pi * Complex.I : ℂ) := by
  let h := dslope φ b
  have hdφ : DifferentiableOn ℂ φ U := fun z hz => (hφ.2 z hz).differentiableWithinAt
  have hdh : DifferentiableOn ℂ h U :=
    (Complex.differentiableOn_dslope (hφ.1.mem_nhds hb)).mpr hdφ
  have hdh' : DifferentiableOn ℂ (deriv h) U := DifferentiableOn.deriv hdh hφ.1
  have hne : ∀ w ∈ U, h w ≠ 0 := by
    intro w hw
    by_cases hwb : w = b
    · simpa [h, hwb] using hn
    · rw [show h w = (w - b)⁻¹ * (φ w - φ b) by
        simp [h, dslope_of_ne φ hwb, slope, smul_eq_mul]]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hwb))
        (sub_ne_zero.mpr (fun he => hwb (hinj hw hb he)))
  have hfac : ∀ w, (w - b) * h w = φ w - a := by
    intro w
    simpa only [h, smul_eq_mul, hφb] using sub_smul_dslope φ b w
  have heq : ∀ w ∈ sphere b ρ,
      (φ w - a) ^ (-1 : ℤ) * deriv φ w =
        (w - b)⁻¹ + deriv h w / h w := by
    intro w hw
    have hwU := hball (sphere_subset_closedBall hw)
    have hwb : w - b ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [mem_sphere_iff_norm.mp hw]
      exact hρ.ne'
    have hd := ((hasDerivAt_id w).sub_const b).mul
      (hdh.differentiableAt (hφ.1.mem_nhds hwU)).hasDerivAt
    have hde : h w + (w - b) * deriv h w = deriv φ w := by
      have hd' := hd.congr_of_eventuallyEq (Eventually.of_forall (fun w => (hfac w).symm))
      simpa only [one_mul, id_eq] using hd'.unique ((hφ.2 w hwU).hasDerivAt.sub_const a)
    rw [← hfac w, ← hde, zpow_neg_one]
    field_simp [hne w hwU]
  have hdq : ∀ w ∈ U, DifferentiableAt ℂ (fun w => deriv h w / h w) w := by
    intro w hw
    exact (hdh'.differentiableAt (hφ.1.mem_nhds hw)).div
      (hdh.differentiableAt (hφ.1.mem_nhds hw)) (hne w hw)
  have hzero : circleIntegral (fun w => deriv h w / h w) b ρ = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le countable_empty
    · exact fun w hw => (hdq w (hball hw)).continuousAt.continuousWithinAt
    · exact fun w hw => hdq w (hball (ball_subset_closedBall hw.1))
  rw [circleIntegral.integral_congr hρ.le heq,
    circleIntegral.integral_add, circleIntegral.integral_sub_center_inv b hρ.ne', hzero, add_zero]
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => by
        apply sub_ne_zero.mpr
        exact ne_of_mem_of_not_mem hw (by simpa using hρ.ne))).circleIntegrable hρ.le
  · have hc : ContinuousOn (fun w => deriv h w / h w) (sphere b ρ) :=
      fun w hw => (hdq w (hball (sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
    exact hc.circleIntegrable hρ.le

/-- The compact coordinate image stays in one closed subannulus. -/
theorem image_circle_in_subannulus (φ : ℂ → ℂ) (a b : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) {R : ℝ≥0∞} (hc : ContinuousOn φ (sphere b ρ))
    (hm : MapsTo φ (sphere b ρ) (annulus a 0 R)) :
    ∃ s t : ℝ, 0 < s ∧ s ≤ t ∧ ENNReal.ofReal t < R ∧
      MapsTo φ (sphere b ρ) (closedSubannulus a s t) := by
  have hK : (sphere b ρ).Nonempty := by
    refine ⟨b + (ρ : ℂ), ?_⟩
    simp [mem_sphere_iff_norm, abs_of_pos hρ]
  have hc' : ContinuousOn (fun w => ‖φ w - a‖) (sphere b ρ) :=
    (hc.sub continuousOn_const).norm
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere b ρ).exists_isMinOn hK hc'
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere b ρ).exists_isMaxOn hK hc'
  refine ⟨‖φ u - a‖, ‖φ v - a‖, (hm hu).1, hmin hv, ?_, ?_⟩
  · simpa only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm] using (hm hv).2
  · exact fun w hw => ⟨hmin hw, hmax hw⟩

/-- Integrate a full Laurent expansion on the coordinate image. The two
one-sided series are handled separately, without a finite-principal-part
assumption or a change in summation convention. -/
theorem circleIntegral_pullback (f φ : ℂ → ℂ) (a b : ℂ) (R : ℝ≥0∞)
    (U : Set ℂ) (hφ : HolomorphicOn U φ) (hb : b ∈ U) (hφb : φ b = a)
    (hn : deriv φ b ≠ 0) (hinj : InjOn φ U) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall b ρ ⊆ U) (hm : MapsTo φ (sphere b ρ) (annulus a 0 R))
    (c : ℤ → ℂ) (hc : HasLaurentSeriesOn f a 0 R c)
    (hf : HolomorphicOn (annulus a 0 R) f) :
    circleIntegral (fun w => f (φ w) * deriv φ w) b ρ =
      c (-1) * (2 * Real.pi * Complex.I : ℂ) := by
  have hdφ : DifferentiableOn ℂ φ U := fun w hw => (hφ.2 w hw).differentiableWithinAt
  have hdφ' := DifferentiableOn.deriv hdφ hφ.1
  have hsU : sphere b ρ ⊆ U := fun w hw => hball (sphere_subset_closedBall hw)
  have hcs : ContinuousOn φ (sphere b ρ) :=
    fun w hw => (hφ.2 w (hsU hw)).continuousAt.continuousWithinAt
  have hcd : ContinuousOn (deriv φ) (sphere b ρ) :=
    hdφ'.continuousOn.mono hsU
  obtain ⟨s, t, hs, hst, htR, him⟩ := image_circle_in_subannulus φ a b hρ hcs hm
  obtain ⟨⟨p, hp, hpb⟩, ⟨q, hq, hqb⟩⟩ :=
    Laurent.exists_majorants_of_convergent (le_refl 0)
      (Laurent.convergent_of_hasLaurentSeriesOn hc) hs hst htR
  obtain ⟨M, hM⟩ := (isCompact_sphere b ρ).exists_bound_of_continuousOn hcd
  let B := max M 0
  have hdb : ∀ w ∈ sphere b ρ, ‖deriv φ w‖ ≤ B :=
    fun w hw => (hM w hw).trans (le_max_left _ _)
  have hcp (n : ℕ) : ContinuousOn
      (fun w => positiveTerm c a n (φ w) * deriv φ w) (sphere b ρ) := by
    exact (continuousOn_const.mul ((hcs.sub continuousOn_const).pow n)).mul hcd
  have hcq (n : ℕ) : ContinuousOn
      (fun w => negativeTerm c a n (φ w) * deriv φ w) (sphere b ρ) := by
    apply ContinuousOn.mul _ hcd
    apply ContinuousOn.mul continuousOn_const
    exact (hcs.sub continuousOn_const).zpow₀ (-(n : ℤ) - 1)
      (fun w hw => Or.inl (Laurent.sub_ne_zero_of_mem_annulus (le_refl 0) (hm hw)))
  have hip := Laurent.hasSum_circleIntegral_of_majorant b ρ hρ.le (hp.mul_right B)
    (u := fun n w => positiveTerm c a n (φ w) * deriv φ w)
    (g := fun w => positivePart c a (φ w) * deriv φ w)
    (fun n w hw => by
      rw [norm_mul]
      exact mul_le_mul (hpb n _ (him hw)) (hdb w hw) (norm_nonneg _)
        ((norm_nonneg _).trans (hpb n _ (him hw)))) hcp
    (fun w hw => (hc _ (hm hw)).1.hasSum.mul_right (deriv φ w))
  have hiq := Laurent.hasSum_circleIntegral_of_majorant b ρ hρ.le (hq.mul_right B)
    (u := fun n w => negativeTerm c a n (φ w) * deriv φ w)
    (g := fun w => negativePart c a (φ w) * deriv φ w)
    (fun n w hw => by
      rw [norm_mul]
      exact mul_le_mul (hqb n _ (him hw)) (hdb w hw) (norm_nonneg _)
        ((norm_nonneg _).trans (hqb n _ (him hw)))) hcq
    (fun w hw => (hc _ (hm hw)).2.1.hasSum.mul_right (deriv φ w))
  have hdp : ∀ w ∈ sphere b ρ, DifferentiableAt ℂ φ w := fun w hw => hφ.2 w (hsU hw)
  have hne : ∀ w ∈ sphere b ρ, φ w ≠ a :=
    fun w hw => sub_ne_zero.mp (Laurent.sub_ne_zero_of_mem_annulus (le_refl 0) (hm hw))
  have heip (n : ℕ) : circleIntegral
      (fun w => positiveTerm c a n (φ w) * deriv φ w) b ρ = 0 := by
    simp only [positiveTerm, mul_assoc, ← zpow_natCast]
    rw [circleIntegral.integral_const_mul,
      circleIntegral_monomial_of_ne φ a b hρ.le hdp hne (by omega), mul_zero]
  have heiq (n : ℕ) : circleIntegral
      (fun w => negativeTerm c a n (φ w) * deriv φ w) b ρ =
        if n = 0 then c (-1) * (2 * Real.pi * Complex.I : ℂ) else 0 := by
    simp only [negativeTerm, mul_assoc]
    rw [circleIntegral.integral_const_mul]
    split_ifs with hn0
    · subst n
      simpa only [Nat.cast_zero, neg_zero, zero_sub, mul_assoc] using congrArg (c (-1) * ·)
        (circleIntegral_logarithmic φ a b U hφ hb hφb hn hinj hρ hball)
    · rw [circleIntegral_monomial_of_ne φ a b hρ.le hdp hne (by omega), mul_zero]
  simp_rw [heip] at hip
  simp_rw [heiq] at hiq
  have hep := hip.unique (hasSum_zero (α := ℂ) (β := ℕ))
  have heq := hiq.unique (hasSum_ite_eq 0 (c (-1) * (2 * Real.pi * Complex.I : ℂ)))
  have hcalc := (Laurent.laurent_calculus a 0 R f c (le_refl 0) hf
    (Laurent.convergent_of_hasLaurentSeriesOn hc)).1
  have hcsp : ContinuousOn (fun w => positivePart c a (φ w) * deriv φ w) (sphere b ρ) := by
    apply ContinuousOn.mul _ hcd
    intro w hw
    have hdp' : DifferentiableAt ℂ (positivePart c a) (φ w) := by
      simpa only [iteratedDeriv_zero] using (hcalc 0 (φ w) (hm hw)).1
    exact (hdp'.continuousAt.comp (hdp w hw).continuousAt).continuousWithinAt
  have hcsq : ContinuousOn (fun w => negativePart c a (φ w) * deriv φ w) (sphere b ρ) := by
    apply ContinuousOn.mul _ hcd
    intro w hw
    have hdq' : DifferentiableAt ℂ (negativePart c a) (φ w) := by
      simpa only [iteratedDeriv_zero] using (hcalc 0 (φ w) (hm hw)).2.1
    exact (hdq'.continuousAt.comp (hdp w hw).continuousAt).continuousWithinAt
  rw [circleIntegral.integral_congr hρ.le (fun w hw => by
    rw [(hc _ (hm hw)).2.2, add_mul]), circleIntegral.integral_add,
    hep, heq, zero_add]
  · exact hcsp.circleIntegrable hρ.le
  · exact hcsq.circleIntegrable hρ.le

theorem residue_coordinate_invariant :
    Specs.D12Complex.Ch08.ResidueCoordinate.residue_coordinate_invariant_type := by
  intro f φ a b R Ω hR hf hφ hb hφb hn
  obtain ⟨U, V, ψ, r, hbU, haV, hUΩ, hp, hr, hball, hmap, hpull⟩ :=
    local_coordinate_neighborhood f φ a b R Ω hR hf hφ hb hφb hn
  obtain ⟨c, hc, hres⟩ := Residue.exists_laurent_with_residue f a R hR hf
  have hρ : 0 < r / 2 := half_pos hr
  have hρr : r / 2 < r := half_lt_self hr
  have hclosed : closedBall b (r / 2) ⊆ U := by
    intro w hw
    apply hball
    exact (closedBall_subset_ball hρr) hw
  have him : MapsTo φ (sphere b (r / 2)) (annulus a 0 R) := by
    intro w hw
    apply hmap
    apply (mem_puncturedDisk_iff hr).mpr
    refine ⟨?_, (closedBall_subset_ball hρr) (sphere_subset_closedBall hw)⟩
    intro he
    have he' := mem_sphere_iff_norm.mp hw
    rw [he, sub_self, norm_zero] at he'
    linarith
  rw [Residue.residue_eq_circleIntegral _ b (ENNReal.ofReal r) hpull (r / 2) hρ
    ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hρr),
    circleIntegral_pullback f φ a b R U hp.1 hbU hφb hn hp.2.2.2.2.1.injOn
      hρ hclosed him c hc hf, hres]
  have hC : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [mul_left_comm, inv_mul_cancel₀ hC, mul_one]

end D12Complex.ResidueCoordinate
