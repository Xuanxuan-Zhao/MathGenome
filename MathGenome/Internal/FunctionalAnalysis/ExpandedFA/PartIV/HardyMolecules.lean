import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMolecules
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyPAtoms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
universe v

namespace ExpandedFA.PartIV.HardyMolecules
open HardyMoleculesSpec Hardy.HardyPAtomsSpec

variable {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]

/-- Translation of the checked radial integral. -/
lemma radial_tail_center (hd : 0 < d) (c : Point d) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : Point d =>
      (Ioi R).indicator (fun t : ℝ => 1 / t ^ (d + 1)) ‖x - c‖) volume ∧
    (∫ x : Point d, (Ioi R).indicator (fun t : ℝ => 1 / t ^ (d + 1)) ‖x - c‖) =
      (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R := by
  obtain ⟨hi, he⟩ := SingularIntegrals.CZWeak.radial_tail hd R hR
  exact ⟨hi.comp_sub_right c, (integral_sub_right_eq_self _ c).trans he⟩

/-- The displayed L² and tail hypotheses imply actual integrability, rather
than relying on the totalized value of the Bochner integral. -/
theorem molecule_integrable : Integrability.{v} := by
  intro d 𝕜 _ f c r A h
  rcases h with ⟨hr, hA, hf, hn, hz, ht⟩
  let B := Metric.closedBall c (2 * r)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  haveI : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_closedBall_lt_top : volume B < ∞)⟩
  have hin : IntegrableOn f B volume :=
    (hf.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  by_cases hd : 0 < d
  · obtain ⟨hi, _⟩ := radial_tail_center hd c (2 * r) (by positivity)
    have hout : IntegrableOn f Bᶜ volume :=
      (hi.const_mul (A * r)).integrableOn.mono' hf.aestronglyMeasurable.restrict (by
        filter_upwards [ae_restrict_mem hB.compl, ae_restrict_of_ae ht] with x hx htx
        have hgt : 2 * r < ‖x - c‖ := by
          simpa only [B, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] using hx
        simpa only [Set.indicator_of_mem (show ‖x - c‖ ∈ Ioi (2 * r) from hgt),
          mul_one_div] using htx hgt.le)
    simpa only [union_compl_self, integrableOn_univ] using hin.union hout
  · have hd : d = 0 := by omega
    subst d
    have hBu : B = univ := by
      ext x
      simp [B, Subsingleton.elim x c, show 0 ≤ 2 * r by positivity]
    simpa only [hBu, integrableOn_univ] using hin

/-- A zero a.e. function has a zero-coefficient expansion even in dimension zero. -/
lemma conclusion_of_ae_zero (f : Point d → 𝕜) (hf : f =ᵐ[volume] 0)
    {M : ℝ} (hM : 0 ≤ M) : Conclusion f M := by
  have hi : Integrable f volume := (integrable_zero _ _ _).congr hf.symm
  have he : hi.toL1 f = (0 : L1 d 𝕜) :=
    Lp.ext (hi.coeFn_toL1.trans (hf.trans (Lp.coeFn_zero _ _ _).symm))
  letI := Hardy.AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  let a : InfinityAtom d 𝕜 := Classical.choice inferInstance
  refine ⟨hi, 0, by simpa [he], by simpa using hM,
    fun _ => a, fun _ => 0, by simp, ?_, ?_⟩
  · simpa [he] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : L1 d 𝕜)) 0)
  · simpa using hM

/-- The degenerate amplitude is proved from the finite L² norm. -/
lemma zero_amplitude (f : Point d → 𝕜) (c : Point d) (r : ℝ)
    (h : IsMolecule f c r 0) : Conclusion f 0 := by
  have hn : eLpNorm f 2 volume = 0 := by
    apply (ENNReal.toReal_eq_zero_iff _).mp ?_ |>.resolve_right h.2.2.1.eLpNorm_ne_top
    apply le_antisymm ?_ ENNReal.toReal_nonneg
    simpa only [zero_mul] using h.2.2.2.1
  exact conclusion_of_ae_zero f ((eLpNorm_eq_zero_iff (by norm_num)).mp hn) le_rfl

/-- On the mass-one singleton, cancellation forces the molecule to vanish. -/
lemma zero_dimension {𝕜 : Type v} [RCLike 𝕜] (f : Point 0 → 𝕜)
    (c : Point 0) (r A : ℝ) (h : IsMolecule f c r A) : Conclusion f A := by
  have hz : f 0 = 0 := by
    simpa only [volume_euclideanSpace_eq_dirac, integral_dirac] using h.2.2.2.2.1
  apply conclusion_of_ae_zero f (ae_of_all _ fun x => ?_) h.2.1
  simpa only [Subsingleton.elim x 0, Pi.zero_apply] using hz

/-- Quantitative use of the accepted 2-atom theorem; no additive error is
introduced into the homogeneous estimate. -/
lemma l2_ball_hardy_bound (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (f : L1 d 𝕜), MemLp f 2 volume →
      (∫ x, f x) = 0 → ∀ (c : Point d) (R K : ℝ), 0 < R → 0 < K →
      (∀ᵐ x ∂volume, x ∉ Metric.ball c R → f x = 0) →
      (eLpNorm f 2 volume).toReal ≤ K * (volume.real (Metric.ball c R)) ^ (-1 / 2 : ℝ) →
      ∃ u : H1 d 𝕜, Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧
        ‖u‖ ≤ C * K := by
  obtain ⟨C, hC, hb⟩ := Hardy.HardyPAtoms.pAtom_hardy_bound.{v} d 2 (by norm_num)
  refine ⟨C, hC, fun {𝕜} _ f hf hz c R K hR hK hs hn => ?_⟩
  let k : 𝕜 := (K : 𝕜)
  have hk : k ≠ 0 := by dsimp [k]; exact_mod_cast hK.ne'
  have hkn : ‖k‖ = K := by simp [k, abs_of_pos hK]
  have hsm : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hm : MemLp (⇑(k⁻¹ • f)) 2 volume := (hf.const_smul k⁻¹).ae_eq hsm.symm
  have hsize : (eLpNorm (⇑(k⁻¹ • f)) 2 volume).toReal ≤
      (volume.real (Metric.ball c R)) ^ (1 / (2 : ℝ) - 1) := by
    rw [eLpNorm_congr_ae hsm, eLpNorm_const_smul, ENNReal.toReal_mul,
      ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), norm_inv, hkn]
    have he : (1 / (2 : ℝ) - 1) = -1 / 2 := by norm_num
    rw [he]
    exact (inv_mul_le_iff₀ hK).mpr hn
  have hzero : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae hsm]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have hsup : ∀ᵐ x ∂volume, x ∉ Metric.ball c R → (k⁻¹ • f) x = 0 := by
    filter_upwards [hsm, hs] with x hx hxs hxB
    simp [hx, hxs hxB]
  let a : PAtom d 2 𝕜 := ⟨k⁻¹ • f, by simpa using hm,
    hzero, c, R, hR, hsup, by simpa using hsize⟩
  obtain ⟨u, hu, hnu⟩ := hb a
  refine ⟨k • u, ?_, ?_⟩
  · rw [map_smul, hu]
    exact smul_inv_smul₀ hk f
  · rw [norm_smul, hkn, mul_comm C K]
    exact mul_le_mul_of_nonneg_left hnu hK.le

/-- Normalize a bounded ball-supported mean-zero class into an original
infinity-atom, retaining its quantitative coefficient. -/
lemma bounded_ball_hardy_bound (f : L1 d 𝕜) (hz : (∫ x, f x) = 0)
    (c : Point d) (R K : ℝ) (hR : 0 < R) (hK : 0 < K)
    (hb : ∀ᵐ x ∂volume, (x ∉ Metric.ball c R → f x = 0) ∧
      ‖f x‖ ≤ K / volume.real (Metric.ball c R)) :
    ∃ u : H1 d 𝕜, Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u = f ∧ ‖u‖ ≤ K := by
  let k : 𝕜 := (K : 𝕜)
  have hk : k ≠ 0 := by dsimp [k]; exact_mod_cast hK.ne'
  have hkn : ‖k‖ = K := by simp [k, abs_of_pos hK]
  have hsm : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hzero : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae hsm]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have hb' : ∀ᵐ x ∂volume, (x ∉ Metric.ball c R → (k⁻¹ • f) x = 0) ∧
      ‖(k⁻¹ • f) x‖ ≤ (volume.real (Metric.ball c R))⁻¹ := by
    filter_upwards [hsm, hb] with x hx hbx
    rw [hx]
    refine ⟨fun hn => by simp [hbx.1 hn], ?_⟩
    rw [Pi.smul_apply, norm_smul, norm_inv, hkn]
    apply (inv_mul_le_iff₀ hK).mpr
    simpa only [div_eq_mul_inv] using hbx.2
  let a : InfinityAtom d 𝕜 := ⟨k⁻¹ • f, hzero, c, R, hR,
    (Metric.measure_ball_pos volume c hR).ne', measure_ball_ne_top, hb'⟩
  refine ⟨k • Hardy.AtomicHardySpace.atomElement volume a, ?_, ?_⟩
  · rw [map_smul, Hardy.AtomicHardySpace.embedding_atomElement]
    exact smul_inv_smul₀ hk f
  · rw [norm_smul, hkn]
    exact mul_le_of_le_one_right hK.le (Hardy.AtomicHardySpace.atomElement_norm volume a)

/-- Ball truncation in the actual L¹ quotient. -/
def truncation (f : L1 d 𝕜) (R : ℝ) : L1 d 𝕜 :=
  ((MeasureTheory.L1.integrable_coeFn f).indicator Metric.isOpen_ball.measurableSet).toL1
    ((Metric.ball (0 : Point d) R).indicator f)

lemma truncation_coe (f : L1 d 𝕜) (R : ℝ) :
    ⇑(truncation f R) =ᵐ[volume] (Metric.ball (0 : Point d) R).indicator f :=
  Integrable.coeFn_toL1 _

/-- Normalized indicator, of integral and L¹ norm one. -/
def ballDensity (R : ℝ) : L1 d 𝕜 :=
  indicatorConstLp 1 (s := Metric.ball (0 : Point d) R)
    Metric.isOpen_ball.measurableSet measure_ball_ne_top
    ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)

lemma ballDensity_coe (R : ℝ) :
    ⇑(ballDensity (𝕜 := 𝕜) (d := d) R) =ᵐ[volume]
      (Metric.ball (0 : Point d) R).indicator
        (fun _ => ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)) :=
  indicatorConstLp_coeFn

lemma ballDensity_integral (R : ℝ) (hR : 0 < R) :
    (∫ x, ballDensity (𝕜 := 𝕜) (d := d) R x) = 1 := by
  have hV : volume.real (Metric.ball (0 : Point d) R) ≠ 0 :=
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hR).ne' measure_ball_ne_top).ne'
  rw [integral_congr_ae (ballDensity_coe R), integral_indicator_const _
    Metric.isOpen_ball.measurableSet]
  rw [RCLike.real_smul_eq_coe_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hV)

lemma ballDensity_norm (R : ℝ) (hR : 0 < R) :
    ‖ballDensity (𝕜 := 𝕜) (d := d) R‖ = 1 := by
  have hV : 0 < volume.real (Metric.ball (0 : Point d) R) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hR).ne' measure_ball_ne_top
  rw [ballDensity, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [RCLike.norm_ofReal, abs_of_pos hV, hV.ne']

/-- Subtract the mean without changing the supporting ball. -/
def compensated (f : L1 d 𝕜) (R : ℝ) : L1 d 𝕜 :=
  truncation f R - (∫ x, truncation f R x) • ballDensity R

lemma compensated_integral (f : L1 d 𝕜) (R : ℝ) (hR : 0 < R) :
    (∫ x, compensated f R x) = 0 := by
  unfold compensated
  rw [integral_congr_ae (Lp.coeFn_sub _ _)]
  simp only [Pi.sub_apply]
  rw [integral_sub
    (MeasureTheory.L1.integrable_coeFn _) (MeasureTheory.L1.integrable_coeFn _),
    integral_congr_ae (Lp.coeFn_smul _ _)]
  change (∫ x, truncation f R x) -
    (∫ x, (∫ y, truncation f R y) * ballDensity R x) = 0
  rw [integral_const_mul, ballDensity_integral R hR, mul_one, sub_self]

lemma compensated_coe (f : L1 d 𝕜) (R : ℝ) :
    ⇑(compensated f R) =ᵐ[volume] fun x =>
      (Metric.ball (0 : Point d) R).indicator f x -
      (∫ y, truncation f R y) *
        (Metric.ball (0 : Point d) R).indicator
          (fun _ => ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)) x := by
  filter_upwards [Lp.coeFn_sub (truncation f R)
      ((∫ y, truncation f R y) • ballDensity (d := d) (𝕜 := 𝕜) R),
    Lp.coeFn_smul (∫ y, truncation f R y) (ballDensity (d := d) (𝕜 := 𝕜) R),
    truncation_coe f R, ballDensity_coe (𝕜 := 𝕜) R] with x hs hsm ht hd
  change (compensated f R) x = _
  simpa only [compensated, hs, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, ht, hd]

lemma compensated_support (f : L1 d 𝕜) (R : ℝ) :
    ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Point d) R → compensated f R x = 0 := by
  filter_upwards [compensated_coe f R] with x hx hB
  simp [hx, Set.indicator_of_notMem hB]

lemma ball_volume (R : ℝ) (hR : 0 < R) :
    volume.real (Metric.ball (0 : Point d) R) =
      R ^ d * volume.real (Metric.ball (0 : Point d) 1) := by
  simp only [measureReal_def, Measure.addHaar_ball_of_pos volume _ hR,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ Module.finrank ℝ (Point d))]
  simp [Point]

/-- Tail domination for any radius beyond the source's threshold. -/
lemma molecule_tail_bound (hd : 0 < d) (f : Point d → 𝕜) {A : ℝ}
    (h : IsMolecule f 0 1 A) (R : ℝ) (hR : 2 ≤ R) :
    (∫ x in (Metric.closedBall (0 : Point d) R)ᶜ, ‖f x‖) ≤
      A * ((d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) := by
  have hi : Integrable f volume := molecule_integrable d f 0 1 A h
  obtain ⟨hiT, heT⟩ := radial_tail_center hd (0 : Point d) R (by linarith)
  have hfm := h.2.2.2.2.2
  have hT : ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Point d) R)ᶜ,
      ‖f x‖ ≤ A * (Ioi R).indicator (fun t : ℝ => 1 / t ^ (d + 1)) ‖x - 0‖ := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet.compl,
      ae_restrict_of_ae hfm] with x hx htx
    have hgt : R < ‖x - 0‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] using hx
    simpa only [mul_one, Set.indicator_of_mem (show ‖x - 0‖ ∈ Ioi R from hgt),
      mul_one_div] using htx (by linarith)
  calc
    (∫ x in (Metric.closedBall (0 : Point d) R)ᶜ, ‖f x‖) ≤
        ∫ x in (Metric.closedBall (0 : Point d) R)ᶜ,
          A * (Ioi R).indicator (fun t : ℝ => 1 / t ^ (d + 1)) ‖x - 0‖ :=
      integral_mono_ae hi.norm.integrableOn (hiT.const_mul A).integrableOn hT
    _ = A * ∫ x : Point d, (Ioi R).indicator (fun t : ℝ => 1 / t ^ (d + 1)) ‖x - 0‖ := by
      rw [integral_const_mul]
      congr 1
      rw [← integral_indicator Metric.isClosed_closedBall.measurableSet.compl]
      congr 1
      funext x
      by_cases hx : x ∈ (Metric.closedBall (0 : Point d) R)ᶜ
      · exact Set.indicator_of_mem hx _
      · have hx' : ‖x - 0‖ ≤ R := by
          simpa only [mem_compl_iff, not_not, Metric.mem_closedBall, dist_eq_norm] using hx
        simp only [Set.indicator_of_notMem hx, sub_zero] at *
        rw [Set.indicator_of_notMem (show ‖x‖ ∉ Ioi R from not_lt.mpr hx')]
    _ = _ := by rw [heT]

lemma outer_ball_norm_bound (hd : 0 < d) (f : L1 d 𝕜) {A : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) (R : ℝ) (hR : 4 ≤ R) :
    (∫ x in (Metric.ball (0 : Point d) R)ᶜ, ‖f x‖) ≤
      A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) := by
  have hsub : (Metric.ball (0 : Point d) R)ᶜ ⊆
      (Metric.closedBall (0 : Point d) (R / 2))ᶜ := by
    intro x hx hxC
    have hb : R ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hc : ‖x‖ ≤ R / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hxC
    linarith
  calc
    (∫ x in (Metric.ball (0 : Point d) R)ᶜ, ‖f x‖) ≤
        ∫ x in (Metric.closedBall (0 : Point d) (R / 2))ᶜ, ‖f x‖ :=
      integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (ae_of_all _ fun _ => norm_nonneg _) (MeasureTheory.L1.integrable_coeFn f).norm.integrableOn
    _ ≤ A * ((d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / (R / 2)) :=
      molecule_tail_bound hd f h (R / 2) (by linarith)
    _ = _ := by ring

lemma truncation_error_norm (f : L1 d 𝕜) (R : ℝ) :
    ‖truncation f R - f‖ = ∫ x in (Metric.ball (0 : Point d) R)ᶜ, ‖f x‖ := by
  rw [MeasureTheory.L1.norm_eq_integral_norm, ← integral_indicator
    Metric.isOpen_ball.measurableSet.compl]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (truncation f R) f, truncation_coe f R] with x hs ht
  simp only [hs, Pi.sub_apply, ht]
  by_cases hx : x ∈ Metric.ball (0 : Point d) R <;> simp [hx]

/-- Cancellation converts the integral over the central ball into a tail.
Using R/2 in the majorant avoids imposing a boundary-null hypothesis. -/
lemma truncation_mean_bound (hd : 0 < d) (f : L1 d 𝕜) {A : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) (R : ℝ) (hR : 4 ≤ R) :
    ‖∫ x, truncation f R x‖ ≤
      A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) := by
  let B := Metric.ball (0 : Point d) R
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hz : (∫ x in B, f x) = -(∫ x in Bᶜ, f x) := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [integral_add_compl hB (MeasureTheory.L1.integrable_coeFn f)]
    exact h.2.2.2.2.1
  rw [integral_congr_ae (truncation_coe f R), integral_indicator hB, hz, norm_neg]
  exact (norm_integral_le_integral_norm _).trans (outer_ball_norm_bound hd f h R hR)

lemma compensated_error_bound (hd : 0 < d) (f : L1 d 𝕜) {A : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) (R : ℝ) (hR : 4 ≤ R) :
    ‖compensated f R - f‖ ≤
      A * (4 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) := by
  calc
    ‖compensated f R - f‖ =
        ‖(truncation f R - f) - (∫ x, truncation f R x) • ballDensity R‖ := by
      congr 1
      simp only [compensated]
      abel
    _ ≤ ‖truncation f R - f‖ + ‖(∫ x, truncation f R x) • ballDensity R‖ := norm_sub_le _ _
    _ = ‖truncation f R - f‖ + ‖∫ x, truncation f R x‖ := by
      rw [norm_smul, ballDensity_norm R (by linarith), mul_one]
    _ ≤ A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) +
        A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) :=
      add_le_add (by rw [truncation_error_norm]; exact outer_ball_norm_bound hd f h R hR)
        (truncation_mean_bound hd f h R hR)
    _ = _ := by ring

/-- Dyadic radii begin at four so no sphere-null lemma is required. -/
def radius (n : ℕ) : ℝ := 4 * 2 ^ n

lemma radius_ge_four (n : ℕ) : 4 ≤ radius n := by
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  dsimp [radius]
  linarith

lemma radius_pos (n : ℕ) : 0 < radius n := lt_of_lt_of_le (by norm_num) (radius_ge_four n)

lemma radius_succ (n : ℕ) : radius (n + 1) = 2 * radius n := by
  simp [radius, pow_succ]
  ring

lemma compensated_tendsto (hd : 0 < d) (f : L1 d 𝕜) {A : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) :
    Tendsto (fun n => compensated f (radius n)) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ =>
      A * ((d : ℝ) * volume.real (Metric.ball (0 : Point d) 1)) * (1 / 2 : ℝ)^n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (A * ((d : ℝ) * volume.real (Metric.ball (0 : Point d) 1)))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  calc
    ‖compensated f (radius n) - f‖ ≤
        A * (4 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / radius n) :=
      compensated_error_bound hd f h _ (radius_ge_four n)
    _ = _ := by simp [radius, div_pow]; ring

lemma ballDensity_memLp_two (R : ℝ) :
    MemLp (ballDensity (d := d) (𝕜 := 𝕜) R : Point d → 𝕜) 2 volume := by
  exact (memLp_indicator_const 2 Metric.isOpen_ball.measurableSet.nullMeasurableSet
    ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)
    (Or.inr measure_ball_ne_top)).ae_eq (ballDensity_coe R).symm

lemma ballDensity_l2_norm (R : ℝ) (hR : 0 < R) :
    lpNorm (ballDensity (d := d) (𝕜 := 𝕜) R : Point d → 𝕜) 2 volume =
      (volume.real (Metric.ball (0 : Point d) R))⁻¹ *
        (volume.real (Metric.ball (0 : Point d) R)) ^ (1 / 2 : ℝ) := by
  have hV : 0 < volume.real (Metric.ball (0 : Point d) R) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hR).ne' measure_ball_ne_top
  rw [← toReal_eLpNorm, eLpNorm_congr_ae (ballDensity_coe R),
    eLpNorm_indicator_const Metric.isOpen_ball.measurableSet.nullMeasurableSet
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp [abs_of_pos hV, Measure.real]

lemma compensated_memLp_two (f : L1 d 𝕜) (hf : MemLp f 2 volume) (R : ℝ) :
    MemLp (compensated f R : Point d → 𝕜) 2 volume := by
  have ht := (MemLp.indicator Metric.isOpen_ball.measurableSet.nullMeasurableSet hf).ae_eq (truncation_coe f R).symm
  have hd := ((ballDensity_memLp_two (d := d) (𝕜 := 𝕜) R).const_smul
    (∫ x, truncation f R x)).ae_eq (Lp.coeFn_smul _ _).symm
  exact (ht.sub hd).ae_eq (Lp.coeFn_sub _ _).symm

lemma compensated_l2_bound (hd : 0 < d) (f : L1 d 𝕜) {A : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) (R : ℝ) (hR : 4 ≤ R) :
    lpNorm (compensated f R : Point d → 𝕜) 2 volume ≤
      A * (1 + (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R) *
        ((volume.real (Metric.ball (0 : Point d) R))⁻¹ *
          (volume.real (Metric.ball (0 : Point d) R)) ^ (1 / 2 : ℝ))) := by
  let t : L1 d 𝕜 := truncation f R
  let q : L1 d 𝕜 := ballDensity R
  let m : 𝕜 := ∫ x, t x
  have ht : MemLp (t : Point d → 𝕜) 2 volume :=
    (MemLp.indicator Metric.isOpen_ball.measurableSet.nullMeasurableSet h.2.2.1).ae_eq
      (truncation_coe f R).symm
  have hq : MemLp (q : Point d → 𝕜) 2 volume := ballDensity_memLp_two R
  have htn : lpNorm (t : Point d → 𝕜) 2 volume ≤ A := by
    change (eLpNorm (⇑t) 2 volume).toReal ≤ A
    rw [eLpNorm_congr_ae (truncation_coe f R)]
    exact (ENNReal.toReal_mono h.2.2.1.eLpNorm_ne_top
      (eLpNorm_indicator_le _ Metric.isOpen_ball.measurableSet.nullMeasurableSet)).trans
        (by simpa using h.2.2.2.1)
  have hco : ⇑(compensated f R) =ᵐ[volume] (⇑t - m • ⇑q) :=
    (Lp.coeFn_sub t (m • q)).trans (by
      filter_upwards [Lp.coeFn_smul m q] with x hx
      simp only [Pi.sub_apply, hx])
  have hn : lpNorm (compensated f R : Point d → 𝕜) 2 volume ≤
      lpNorm (t : Point d → 𝕜) 2 volume + ‖m‖ * lpNorm (q : Point d → 𝕜) 2 volume := by
    rw [← toReal_eLpNorm, eLpNorm_congr_ae hco, toReal_eLpNorm]
    exact (lpNorm_sub_le ht (g := m • ⇑q) (by norm_num)).trans_eq
      (by simp only [lpNorm_const_smul, coe_nnnorm])
  calc
    _ ≤ lpNorm (t : Point d → 𝕜) 2 volume + ‖m‖ * lpNorm (q : Point d → 𝕜) 2 volume := hn
    _ ≤ A + (A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R)) *
        lpNorm (q : Point d → 𝕜) 2 volume :=
      add_le_add htn (mul_le_mul_of_nonneg_right (truncation_mean_bound hd f h R hR) lpNorm_nonneg)
    _ = _ := by dsimp [q]; rw [ballDensity_l2_norm R (by linarith)]; ring

/-- The first compensated truncation has a dimension-only Hardy bound. -/
lemma initial_compensated_bound (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {𝕜 : Type v} [RCLike 𝕜]
      (f : L1 d 𝕜) (A : ℝ), 0 < A → IsMolecule (⇑f) 0 1 A →
      ∃ u : H1 d 𝕜, Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u = compensated f 4 ∧
        ‖u‖ ≤ C * A := by
  obtain ⟨C, hC, hb⟩ := l2_ball_hardy_bound.{v} d
  let V := volume.real (Metric.ball (0 : Point d) 4)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ (by norm_num : (0 : ℝ) < 4)).ne' measure_ball_ne_top
  let Q := 1 + (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / 4) *
    (V⁻¹ * V ^ (1 / 2 : ℝ))
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let K := Q * V ^ (1 / 2 : ℝ)
  have hK : 0 < K := mul_pos hQ (Real.rpow_pos_of_pos hV _)
  refine ⟨C * K, mul_pos hC hK, fun {𝕜} _ f A hA h => ?_⟩
  obtain ⟨u, hu, hnu⟩ := hb (compensated f 4) (compensated_memLp_two f h.2.2.1 4)
    (compensated_integral f 4 (by norm_num)) 0 4 (K * A) (by norm_num) (mul_pos hK hA)
    (compensated_support f 4) (by
      have hmul : V ^ (1 / 2 : ℝ) * V ^ (-1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hV]; norm_num
      have he : (K * A) * V ^ (-1 / 2 : ℝ) = A * Q := by
        dsimp [K]
        calc
          Q * V ^ (1 / 2 : ℝ) * A * V ^ (-1 / 2 : ℝ) =
              A * Q * (V ^ (1 / 2 : ℝ) * V ^ (-1 / 2 : ℝ)) := by ring
          _ = _ := by rw [hmul, mul_one]
      change lpNorm (compensated f 4 : Point d → 𝕜) 2 volume ≤ (K * A) * V ^ (-1 / 2 : ℝ)
      rw [he]
      exact compensated_l2_bound hd f h 4 le_rfl)
  exact ⟨u, hu, hnu.trans_eq (by ring)⟩

/-- The two annular truncations differ only where the tail estimate applies. -/
lemma annular_indicator_bound (f : Point d → 𝕜) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 4 ≤ R)
    (ht : ∀ᵐ x ∂volume, 2 ≤ ‖x‖ → ‖f x‖ ≤ A / ‖x‖ ^ (d + 1)) :
    ∀ᵐ x ∂volume,
      ‖(Metric.ball (0 : Point d) (2 * R)).indicator f x -
        (Metric.ball (0 : Point d) R).indicator f x‖ ≤ A / R ^ (d + 1) := by
  filter_upwards [ht] with x hx
  by_cases hxs : x ∈ Metric.ball (0 : Point d) R
  · have hxb : x ∈ Metric.ball (0 : Point d) (2 * R) :=
      Metric.ball_subset_ball (by linarith) hxs
    simp only [Set.indicator_of_mem hxs, Set.indicator_of_mem hxb, sub_self, norm_zero]
    positivity
  · by_cases hxb : x ∈ Metric.ball (0 : Point d) (2 * R)
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_mem hxb, sub_zero]
      have hnx : R ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hxs
      exact (hx (by linarith)).trans (div_le_div_of_nonneg_left hA (by positivity)
        (pow_le_pow_left₀ (by linarith) hnx _))
    · simp only [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxb, sub_zero, norm_zero]
      positivity

lemma density_indicator_bound (R : ℝ) (hR : 0 < R) (x : Point d) :
    ‖(Metric.ball (0 : Point d) R).indicator
      (fun _ => ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)) x‖ ≤
      (volume.real (Metric.ball (0 : Point d) R))⁻¹ := by
  have hV : 0 < volume.real (Metric.ball (0 : Point d) R) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ hR).ne' measure_ball_ne_top
  by_cases hx : x ∈ Metric.ball (0 : Point d) R
  · simp [Set.indicator_of_mem hx, abs_of_pos hV]
  · simp only [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-- A pointwise bound on the compensated increment before normalizing its
supporting ball. -/
lemma compensated_increment_bound (hd : 0 < d) (f : L1 d 𝕜) {A R : ℝ}
    (h : IsMolecule (⇑f) 0 1 A) (hR : 4 ≤ R) :
    ∀ᵐ x ∂volume, ‖(compensated f (2 * R) - compensated f R) x‖ ≤
      A / R ^ (d + 1) +
      (A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / (2 * R))) *
        (volume.real (Metric.ball (0 : Point d) (2 * R)))⁻¹ +
      (A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R)) *
        (volume.real (Metric.ball (0 : Point d) R))⁻¹ := by
  have hA := h.2.1
  have hRp : 0 < R := by linarith
  have htail : ∀ᵐ x ∂volume, 2 ≤ ‖x‖ → ‖f x‖ ≤ A / ‖x‖ ^ (d + 1) := by
    simpa using h.2.2.2.2.2
  filter_upwards [Lp.coeFn_sub (compensated f (2 * R)) (compensated f R),
    compensated_coe f (2 * R), compensated_coe f R,
    annular_indicator_bound f h.2.1 hR htail] with x hs hb ha hdiff
  rw [hs]
  simp only [Pi.sub_apply, hb, ha]
  let U := (Metric.ball (0 : Point d) (2 * R)).indicator f x
  let V := (Metric.ball (0 : Point d) R).indicator f x
  let P := (Metric.ball (0 : Point d) (2 * R)).indicator
    (fun _ => ((volume.real (Metric.ball (0 : Point d) (2 * R)))⁻¹ : 𝕜)) x
  let Q := (Metric.ball (0 : Point d) R).indicator
    (fun _ => ((volume.real (Metric.ball (0 : Point d) R))⁻¹ : 𝕜)) x
  change ‖(U - (∫ y, truncation f (2 * R) y) * P) -
    (V - (∫ y, truncation f R y) * Q)‖ ≤ _
  calc
    _ = ‖(U - V) - (∫ y, truncation f (2 * R) y) * P + (∫ y, truncation f R y) * Q‖ := by
      congr 1; ring
    _ ≤ ‖U - V‖ + ‖(∫ y, truncation f (2 * R) y) * P‖ +
        ‖(∫ y, truncation f R y) * Q‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add hdiff
        (mul_le_mul (truncation_mean_bound hd f h _ (by linarith))
          (density_indicator_bound (𝕜 := 𝕜) (2 * R) (by linarith) x)
          (norm_nonneg _) (by positivity)))
        (mul_le_mul (truncation_mean_bound hd f h R hR)
          (density_indicator_bound (𝕜 := 𝕜) R (by linarith) x)
          (norm_nonneg _) (by positivity))

def stepConstant (d : ℕ) : ℝ :=
  (2 : ℝ)^d * volume.real (Metric.ball (0 : Point d) 1) +
    (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) +
    (2 : ℝ)^d * 2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) + 1

lemma stepConstant_pos (d : ℕ) : 0 < stepConstant d := by
  dsimp [stepConstant]
  positivity

lemma increment_budget (R : ℝ) (hR : 0 < R) (A : ℝ) :
    (A / R ^ (d + 1) +
      (A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / (2 * R))) *
        (volume.real (Metric.ball (0 : Point d) (2 * R)))⁻¹ +
      (A * (2 * (d : ℝ) * volume.real (Metric.ball (0 : Point d) 1) / R)) *
        (volume.real (Metric.ball (0 : Point d) R))⁻¹) *
        volume.real (Metric.ball (0 : Point d) (2 * R)) =
      (stepConstant d - 1) * A / R := by
  have hV : 0 < volume.real (Metric.ball (0 : Point d) 1) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  rw [ball_volume R hR, ball_volume (2 * R) (by positivity)]
  simp only [mul_pow, pow_succ, stepConstant]
  field_simp
  <;> ring

lemma compensated_step_hardy (hd : 0 < d) (f : L1 d 𝕜) {A R : ℝ}
    (hA : 0 < A) (h : IsMolecule (⇑f) 0 1 A) (hR : 4 ≤ R) :
    ∃ u : H1 d 𝕜, Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u =
      compensated f (2 * R) - compensated f R ∧ ‖u‖ ≤ stepConstant d * A / R := by
  have hRp : 0 < R := by linarith
  let f' := compensated f (2 * R) - compensated f R
  have hz : (∫ x, f' x) = 0 := by
    rw [integral_congr_ae (Lp.coeFn_sub _ _)]
    simp only [Pi.sub_apply]
    rw [integral_sub (MeasureTheory.L1.integrable_coeFn _) (MeasureTheory.L1.integrable_coeFn _),
      compensated_integral f R hRp, compensated_integral f (2 * R) (by positivity), sub_self]
  have hs : ∀ᵐ x ∂volume, x ∉ Metric.ball (0 : Point d) (2 * R) → f' x = 0 := by
    filter_upwards [Lp.coeFn_sub (compensated f (2 * R)) (compensated f R),
      compensated_support f (2 * R), compensated_support f R] with x hx hxb hxs hB
    have hBs : x ∉ Metric.ball (0 : Point d) R :=
      fun hx => hB (Metric.ball_subset_ball (by linarith) hx)
    change (compensated f (2 * R) - compensated f R) x = 0
    rw [hx]
    change compensated f (2 * R) x - compensated f R x = 0
    rw [hxb hB, hxs hBs, sub_self]
  have hW : 0 < volume.real (Metric.ball (0 : Point d) (2 * R)) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ (by positivity : 0 < 2 * R)).ne' measure_ball_ne_top
  have hK : 0 < stepConstant d := stepConstant_pos d
  apply bounded_ball_hardy_bound f' hz 0 (2 * R) (stepConstant d * A / R)
    (by positivity) (by positivity)
  filter_upwards [hs, compensated_increment_bound hd f h hR] with x hxs hx
  refine ⟨hxs, hx.trans ?_⟩
  apply (le_div_iff₀ hW).mpr
  rw [increment_budget R hRp A]
  exact (div_le_div_iff_of_pos_right hRp).mpr (by nlinarith)

/-- A Hardy lift produces an actual sequence with any strictly positive
coefficient slack. This keeps the eventual estimate homogeneous in A. -/
lemma conclusion_of_hardy (f : Point d → 𝕜) (hi : Integrable f volume)
    (u : H1 d 𝕜) (hu : Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u = hi.toL1 f)
    (C A : ℝ) (hA : 0 < A) (hn : ‖u‖ ≤ C * A) :
    Conclusion f ((C + 1) * A) := by
  classical
  letI := Hardy.AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt u hA
  obtain ⟨a, b, hb, hs⟩ := Hardy.AtomicHardySpace.coefficient_sequence volume c
  have he : Hardy.AtomicHardySpaceSpec.SynthesisValue volume c = hi.toL1 f :=
    (congrArg (Hardy.AtomicHardySpaceSpec.EmbeddingValue volume) hc).trans hu
  refine ⟨hi, u, hu, by nlinarith, a, b, hb.summable, he ▸ hs, ?_⟩
  rw [hb.tsum_eq]
  nlinarith [hcn]

lemma isMolecule_ae_eq {f g : Point d → 𝕜} {c : Point d} {r A : ℝ}
    (h : IsMolecule f c r A) (he : f =ᵐ[volume] g) : IsMolecule g c r A := by
  rcases h with ⟨hr, hA, hf, hn, hz, ht⟩
  refine ⟨hr, hA, hf.ae_eq he, ?_, ?_, ?_⟩
  · rwa [eLpNorm_congr_ae he] at hn
  · exact (integral_congr_ae he).symm.trans hz
  · filter_upwards [he, ht] with x hx htx
    simpa only [← hx] using htx

/-- The complete unit-scale molecule theorem, including its summable actual
infinity-atomic series and the zero amplitude and zero dimension cases. -/
theorem unit_molecule : UnitResult.{v} := by
  intro d
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, fun {𝕜} _ f A h => ?_⟩
    simpa only [one_mul] using zero_dimension f 0 1 A h
  have hd : 0 < d := Nat.pos_of_ne_zero hd
  obtain ⟨C, hC, hinit⟩ := initial_compensated_bound.{v} d hd
  let K := stepConstant d
  have hK : 0 < K := stepConstant_pos d
  refine ⟨C + 2 * K + 1, by positivity, fun {𝕜} _ f A h => ?_⟩
  by_cases hA : A = 0
  · subst A
    simpa only [mul_zero] using zero_amplitude f 0 1 h
  have hA : 0 < A := lt_of_le_of_ne h.2.1 (Ne.symm hA)
  have hi : Integrable f volume := molecule_integrable d f 0 1 A h
  let F : L1 d 𝕜 := hi.toL1 f
  have hF : IsMolecule (⇑F) 0 1 A := isMolecule_ae_eq h hi.coeFn_toL1.symm
  obtain ⟨u₀, hu₀, hn₀⟩ := hinit F A hA hF
  have hv : ∀ n : ℕ, ∃ u : H1 d 𝕜,
      Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u =
        compensated F (radius (n + 1)) - compensated F (radius n) ∧
      ‖u‖ ≤ K * A * (1 / 2 : ℝ)^n := by
    intro n
    obtain ⟨u, hu, hnu⟩ := compensated_step_hardy hd F hA hF (radius_ge_four n)
    refine ⟨u, by simpa only [radius_succ] using hu, hnu.trans ?_⟩
    calc
      K * A / radius n ≤ K * A / (2 : ℝ)^n :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by
            dsimp [radius]
            nlinarith [show (0 : ℝ) ≤ 2 ^ n by positivity])
      _ = _ := by rw [one_div_pow]; ring
  classical
  choose v hv hn using hv
  have hbudget : HasSum (fun n : ℕ => K * A * (1 / 2 : ℝ)^n) (2 * K * A) := by
    convert hasSum_geometric_two.mul_left (K * A) using 1 <;> ring
  have hvs : Summable v := hbudget.summable.of_norm_bounded hn
  have him : HasSum (fun n => compensated F (radius (n + 1)) - compensated F (radius n))
      (Hardy.AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n)) := by
    simpa only [hv] using hvs.hasSum.mapL (Hardy.AtomicHardySpaceSpec.EmbeddingValue volume)
  have hlim : Hardy.AtomicHardySpaceSpec.EmbeddingValue volume (∑' n, v n) = F - compensated F 4 := by
    apply tendsto_nhds_unique him.tendsto_sum_nat
    have ht := (compensated_tendsto hd F hF).sub_const (compensated F (radius 0))
    have htel (n : ℕ) := Finset.sum_range_sub (fun i => compensated F (radius i)) n
    simpa only [radius, pow_zero, mul_one] using
      ht.congr' (Filter.Eventually.of_forall fun n => (htel n).symm)
  let u : H1 d 𝕜 := u₀ + ∑' n, v n
  have hu : Hardy.AtomicHardySpaceSpec.EmbeddingValue volume u = F := by
    rw [map_add, hu₀, hlim, add_sub_cancel]
  have hnu : ‖u‖ ≤ (C + 2 * K) * A := by
    calc
      ‖u‖ ≤ ‖u₀‖ + ‖∑' n, v n‖ := norm_add_le _ _
      _ ≤ C * A + 2 * K * A := add_le_add hn₀ (hvs.hasSum.norm_le_of_bounded hbudget hn)
      _ = _ := by ring
  exact conclusion_of_hardy f hi u hu (C + 2 * K) A hA hnu

/-- The mass-preserving affine transport on ordinary functions. -/
def affineRaw (c : Point d) (r : ℝ) (f : Point d → 𝕜) (x : Point d) : 𝕜 :=
  (r ^ d)⁻¹ • f (r⁻¹ • (x - c))

lemma affine_integrable (c : Point d) {r : ℝ} (hr : 0 < r)
    {f : Point d → 𝕜} (hf : Integrable f volume) :
    Integrable (affineRaw c r f) volume :=
  by
    change Integrable (fun x : Point d => ((r ^ d)⁻¹ : ℝ) • f (r⁻¹ • (x - c))) volume
    exact ((hf.comp_smul (inv_ne_zero hr.ne')).comp_sub_right c).smul ((r ^ d)⁻¹)

lemma affine_integral (c : Point d) {r : ℝ} (hr : 0 < r) (f : Point d → 𝕜) :
    (∫ x, affineRaw c r f x) = ∫ x, f x := by
  unfold affineRaw
  rw [integral_smul, integral_sub_right_eq_self (fun x => f (r⁻¹ • x)) c,
    Measure.integral_comp_inv_smul_of_nonneg volume f hr.le]
  simp only [Point, finrank_euclideanSpace, Fintype.card_fin]
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]

lemma affine_norm_integral (c : Point d) {r : ℝ} (hr : 0 < r) (f : Point d → 𝕜) :
    (∫ x, ‖affineRaw c r f x‖) = ∫ x, ‖f x‖ := by
  simp only [affineRaw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr _))]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => ‖f (r⁻¹ • x)‖) c,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖f x‖) hr.le]
  simp only [Point, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

lemma affine_quasi (c : Point d) {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving (fun x : Point d => r⁻¹ • (x - c)) volume volume :=
  (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).comp
    (measurePreserving_sub_right volume c).quasiMeasurePreserving

/-- Affine transport as a continuous scalar-linear map on the actual L¹ space. -/
def affineL1 (c : Point d) (r : ℝ) (hr : 0 < r) : L1 d 𝕜 →L[𝕜] L1 d 𝕜 :=
  LinearMap.mkContinuous
    ({ toFun := fun f => (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).toL1
          (affineRaw c r f)
       map_add' f g := by
         apply Lp.ext
         have he := (affine_quasi c hr).ae_eq_comp (Lp.coeFn_add f g)
         filter_upwards [Integrable.coeFn_toL1 (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn (f + g))),
           Lp.coeFn_add
             ((affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).toL1 (affineRaw c r f))
             ((affine_integrable c hr (MeasureTheory.L1.integrable_coeFn g)).toL1 (affineRaw c r g)),
           Integrable.coeFn_toL1 (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)),
           Integrable.coeFn_toL1 (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn g)), he]
           with x ha hb hf hg he
         simp only [Function.comp_apply, Pi.add_apply] at he
         simp only [ha, hb, Pi.add_apply, hf, hg, affineRaw, he, smul_add]
       map_smul' k f := by
         change (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn (k • f))).toL1
           (affineRaw c r (k • f)) = k •
           (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).toL1 (affineRaw c r f)
         apply Lp.ext
         have he := (affine_quasi c hr).ae_eq_comp (Lp.coeFn_smul k f)
         filter_upwards [Integrable.coeFn_toL1 (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn (k • f))),
           Lp.coeFn_smul k ((affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).toL1 (affineRaw c r f)),
           Integrable.coeFn_toL1 (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)), he]
           with x ha hb hf he
         simp only [Function.comp_apply, Pi.smul_apply] at he
         simp only [ha, hb, Pi.smul_apply, hf, affineRaw, he]
         exact smul_comm _ _ _ } : L1 d 𝕜 →ₗ[𝕜] L1 d 𝕜)
    1 (fun f => by
      change ‖(affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).toL1
        (affineRaw c r f)‖ ≤ 1 * ‖f‖
      rw [MeasureTheory.L1.norm_eq_integral_norm,
        integral_congr_ae ((Integrable.coeFn_toL1
          (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f))).mono fun x hx => congrArg norm hx),
        affine_norm_integral c hr, ← MeasureTheory.L1.norm_eq_integral_norm f, one_mul])

lemma affineL1_coe (c : Point d) {r : ℝ} (hr : 0 < r) (f : L1 d 𝕜) :
    ⇑(affineL1 c r hr f) =ᵐ[volume] affineRaw c r f :=
  (affine_integrable c hr (MeasureTheory.L1.integrable_coeFn f)).coeFn_toL1

lemma ball_volume_center (c : Point d) (R : ℝ) (hR : 0 < R) :
    volume.real (Metric.ball c R) = R ^ d * volume.real (Metric.ball (0 : Point d) 1) := by
  simp only [measureReal_def, Measure.addHaar_ball_of_pos volume _ hR,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ Module.finrank ℝ (Point d))]
  simp [Point]

lemma affine_ball (c b : Point d) {r : ℝ} (hr : 0 < r) (R : ℝ) (x : Point d) :
    x ∈ Metric.ball (c + r • b) (r * R) ↔
      r⁻¹ • (x - c) ∈ Metric.ball b R := by
  have he : x - (c + r • b) = r • (r⁻¹ • (x - c) - b) := by
    rw [smul_sub, smul_inv_smul₀ hr.ne']
    abel
  simp only [Metric.mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_mul_iff_right₀ hr

lemma affine_atom (c : Point d) {r : ℝ} (hr : 0 < r) (a : InfinityAtom d 𝕜) :
    Hardy.AtomicHardySpaceSpec.IsAtomValue volume (affineL1 c r hr a.val) := by
  obtain ⟨b, R, hR, h0, htop, hb⟩ := a.property.2
  have hV : 0 < volume.real (Metric.ball b R) := ENNReal.toReal_pos h0 htop
  have hvol : volume.real (Metric.ball (c + r • b) (r * R)) =
      r ^ d * volume.real (Metric.ball b R) := by
    rw [ball_volume_center _ _ (mul_pos hr hR), ball_volume_center b R hR, mul_pow]
    ring
  refine ⟨?_, c + r • b, r * R, mul_pos hr hR,
    (Metric.measure_ball_pos volume _ (mul_pos hr hR)).ne', measure_ball_ne_top, ?_⟩
  · rw [integral_congr_ae (affineL1_coe c hr a.val), affine_integral c hr]
    exact a.property.1
  · filter_upwards [affineL1_coe c hr a.val, (affine_quasi c hr).ae hb] with x hx hax
    change (r⁻¹ • (x - c) ∉ Metric.ball b R → a.val (r⁻¹ • (x - c)) = 0) ∧
      ‖a.val (r⁻¹ • (x - c))‖ ≤ (volume.real (Metric.ball b R))⁻¹ at hax
    rw [hx]
    refine ⟨fun hB => ?_, ?_⟩
    · have hnot : r⁻¹ • (x - c) ∉ Metric.ball b R := fun hB' =>
        hB ((affine_ball c b hr R x).mpr hB')
      simp [affineRaw, hax.1 hnot]
    · rw [affineRaw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hr _)), hvol,
        mul_inv_rev]
      exact (mul_le_mul_of_nonneg_left hax.2 (by positivity)).trans_eq (mul_comm _ _)

/-- Transport an entire atomic sequence in L¹ without changing its coefficient sum. -/
lemma affine_conclusion (c : Point d) {r : ℝ} (hr : 0 < r)
    (f : Point d → 𝕜) {M : ℝ} (h : Conclusion f M) :
    Conclusion (affineRaw c r f) M := by
  classical
  obtain ⟨hi, u, hu, hnu, a, b, hb, hs, hn⟩ := h
  let a' : ℕ → InfinityAtom d 𝕜 := fun n => ⟨affineL1 c r hr (a n).val, affine_atom c hr (a n)⟩
  have hi' : Integrable (affineRaw c r f) volume := affine_integrable c hr hi
  have he : affineL1 c r hr (hi.toL1 f) = hi'.toL1 (affineRaw c r f) := by
    apply Lp.ext
    filter_upwards [affineL1_coe c hr (hi.toL1 f), hi'.coeFn_toL1,
      (affine_quasi c hr).ae_eq_comp hi.coeFn_toL1] with x h1 h2 h3
    change (hi.toL1 f) (r⁻¹ • (x - c)) = f (r⁻¹ • (x - c)) at h3
    rw [h1, h2]
    exact congrArg (fun z : 𝕜 => ((r ^ d)⁻¹ : ℝ) • z) h3
  have hs' : HasSum (fun n => b n • (a' n).val) (hi'.toL1 (affineRaw c r f)) := by
    simpa only [map_smul, he] using hs.mapL (affineL1 c r hr)
  obtain ⟨u', hu', hnu'⟩ := Hardy.AtomicHardySpace.sequence_series volume a' b hb
  exact ⟨hi', u', hu'.unique hs', hnu'.trans hn, a', b, hb, hs', hn⟩

def normalizedRaw (c : Point d) (r : ℝ) (f : Point d → 𝕜) (x : Point d) : 𝕜 :=
  (r ^ d : ℝ) • f (c + r • x)

lemma normalized_quasi (c : Point d) {r : ℝ} (hr : 0 < r) :
    QuasiMeasurePreserving (fun x : Point d => c + r • x) volume volume :=
  (measurePreserving_add_left volume c).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hr.ne')

lemma l2_norm_sq (f : Point d → 𝕜) (hf : MemLp f 2 volume) :
    (eLpNorm f 2 volume).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have he : ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    calc
      ‖hf.toLp f‖ ^ 2 = ∫ x, ‖hf.toLp f x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp_rw [real_inner_self_eq_norm_sq]
      _ = _ := integral_congr_ae (hf.coeFn_toLp.mono fun x hx => congrArg (fun z : 𝕜 => ‖z‖ ^ 2) hx)
  simpa only [Lp.norm_toLp] using he

lemma normalized_energy (c : Point d) {r : ℝ} (hr : 0 < r) (f : Point d → 𝕜) :
    (∫ x, ‖normalizedRaw c r f x‖ ^ 2) = r ^ d * ∫ x, ‖f x‖ ^ 2 := by
  simp only [normalizedRaw, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _), mul_pow]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun x => ‖f (c + x)‖ ^ 2) r (hR := hr.le),
    integral_add_left_eq_self (fun x => ‖f x‖ ^ 2) c]
  simp only [Point, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp

lemma normalized_molecule (f : Point d → 𝕜) (c : Point d) (r A : ℝ)
    (h : IsMolecule f c r A) : IsMolecule (normalizedRaw c r f) 0 1 A := by
  rcases h with ⟨hr, hA, hf, hn, hz, ht⟩
  have hm : AEStronglyMeasurable (normalizedRaw c r f) volume := by
    exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving (normalized_quasi c hr)).const_smul (r ^ d : ℝ)
  have hi : Integrable (fun x => ‖normalizedRaw c r f x‖ ^ 2) volume := by
    have he := ((hf.integrable_norm_pow (by norm_num)).comp_add_left c).comp_smul hr.ne'
    convert he.const_mul ((r ^ d) ^ 2) using 1
    funext x
    simp only [normalizedRaw, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _), mul_pow]
  have hu : MemLp (normalizedRaw c r f) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hm).mpr hi
  refine ⟨zero_lt_one, hA, hu, ?_, ?_, ?_⟩
  · simp only [Real.one_rpow, mul_one]
    have hid : r ^ d * (r ^ (-(d : ℝ) / 2)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le,
        ← Real.rpow_natCast r d, ← Real.rpow_add hr]
      have he : (d : ℝ) + -(d : ℝ) / 2 * 2 = 0 := by ring
      norm_num only [Nat.cast_ofNat]
      rw [he, Real.rpow_zero]
    have hsq : r ^ d * (eLpNorm f 2 volume).toReal ^ 2 ≤ A ^ 2 := by
      calc
        _ ≤ r ^ d * (A * r ^ (-(d : ℝ) / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hn 2) (by positivity)
        _ = A ^ 2 := by rw [mul_pow]; nlinarith [hid]
    have hsq' : (eLpNorm (normalizedRaw c r f) 2 volume).toReal ^ 2 ≤ A ^ 2 := by
      rw [l2_norm_sq _ hu, normalized_energy c hr, ← l2_norm_sq _ hf]
      exact hsq
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (normalizedRaw c r f) 2 volume)]
  · simp only [normalizedRaw]
    rw [integral_smul,
      Measure.integral_comp_smul_of_nonneg volume (fun x => f (c + x)) r (hR := hr.le),
      integral_add_left_eq_self f c, hz, smul_zero, smul_zero]
  · filter_upwards [(normalized_quasi c hr).ae ht] with x hx hxnorm
    change (2 * r ≤ ‖c + r • x - c‖ →
      ‖f (c + r • x)‖ ≤ A * r / ‖c + r • x - c‖ ^ (d + 1)) at hx
    have hnx : 2 ≤ ‖x‖ := by simpa only [mul_one, sub_zero] using hxnorm
    have hnarg : ‖c + r • x - c‖ = r * ‖x‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hbound := hx (by rw [hnarg]; nlinarith)
    rw [normalizedRaw, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _)]
    simp only [mul_one]
    calc
      r ^ d * ‖f (c + r • x)‖ ≤ r ^ d * (A * r / ‖c + r • x - c‖ ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = A / ‖x - 0‖ ^ (d + 1) := by
        rw [hnarg, sub_zero, mul_pow, pow_succ]
        field_simp

/-- Every normalized affine molecule, with one common dimension constant. -/
theorem molecule : HardyMoleculesSpec.MainResult.{v} := by
  intro d
  obtain ⟨C, hC, hb⟩ := unit_molecule.{v} d
  refine ⟨C, hC, fun {𝕜} _ f c r A h => ?_⟩
  have hu := hb (normalizedRaw c r f) A (normalized_molecule f c r A h)
  have ht := affine_conclusion c h.1 (normalizedRaw c r f) hu
  have he : affineRaw c r (normalizedRaw c r f) = f := by
    funext x
    have hearg : c + r • (r⁻¹ • (x - c)) = x := by
      rw [smul_inv_smul₀ h.1.ne']
      abel
    change ((r ^ d)⁻¹ : ℝ) • ((r ^ d : ℝ) • f (c + r • (r⁻¹ • (x - c)))) = f x
    rw [hearg, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ h.1.ne'), one_smul]
  rwa [he] at ht

end ExpandedFA.PartIV.HardyMolecules
