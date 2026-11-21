import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.HolderCancellation
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise NNReal ENNReal

namespace P201.Elliptic.HolderCancellation
open P201Specs.Elliptic.HolderCancellation

private abbrev line := P102.Trace.Ordinary.lineIsometry

private lemma positive_cone :
    Ioo (0 : ℝ) 1 • ({line 1} : Set (Space 1)) = line '' Ioo (0 : ℝ) 1 := by
  rw [Set.smul_singleton]
  congr 1
  funext t
  simpa using (line.map_smul t (1 : ℝ)).symm

private lemma negative_cone :
    Ioo (0 : ℝ) 1 • ({line (-1)} : Set (Space 1)) = -(line '' Ioo (0 : ℝ) 1) := by
  rw [Set.smul_singleton, ← Set.image_neg_eq_neg, Set.image_image]
  congr 1
  funext t
  ext i
  change t * (-1) = -t
  ring

private lemma positive_cone_volume :
    volume (Ioo (0 : ℝ) 1 • ({line 1} : Set (Space 1))) = 1 := by
  rw [positive_cone]
  have hm : MeasurableSet (line '' Ioo (0 : ℝ) 1) :=
    line.toHomeomorph.measurableEmbedding.measurableSet_image.mpr measurableSet_Ioo
  have h := line.measurePreserving.measure_preimage hm.nullMeasurableSet
  rw [Set.preimage_image_eq _ line.injective] at h
  rw [← h, Real.volume_Ioo]
  norm_num

/-- The shared endpoint normalization agrees with the polar-coordinate
surface measure, including the one-dimensional case. -/
lemma unitSurface_eq_polar (m : ℕ) :
    P201.unitSurface m = Measure.map
      (Subtype.val : sphere (0 : Space m) 1 → Space m)
      (volume : Measure (Space m)).toSphere := by
  by_cases hm : m = 1
  · subst m
    have hne : line 1 ≠ line (-1) := by
      exact line.injective.ne (by norm_num)
    have hpair : ∀ θ : sphere (0 : Space 1) 1,
        (θ : Space 1) = line 1 ∨ (θ : Space 1) = line (-1) := by
      intro θ
      obtain ⟨t, ht⟩ := line.surjective (θ : Space 1)
      have hn : |t| = 1 := by
        calc
          |t| = ‖line t‖ := (line.norm_map t).symm
          _ = 1 := by rw [ht]; exact mem_sphere_zero_iff_norm.mp θ.property
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with h | h
      · exact Or.inl (ht ▸ congrArg line h)
      · exact Or.inr (ht ▸ congrArg line h)
    have hmass (t : ℝ) (ht : t = 1 ∨ t = -1) :
        (volume : Measure (Space 1)).toSphere
          ((Subtype.val : sphere (0 : Space 1) 1 → Space 1) ⁻¹' {line t}) = 1 := by
      rw [Measure.toSphere_apply' _ (measurableSet_singleton _ |>.preimage (by fun_prop))]
      have hn : line t ∈ sphere (0 : Space 1) 1 := by
        rw [mem_sphere_zero_iff_norm, line.norm_map]
        rcases ht with rfl | rfl <;> norm_num
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe, singleton_inter_of_mem hn,
        finrank_euclideanSpace, Fintype.card_fin, Nat.cast_one, one_mul]
      rcases ht with rfl | rfl
      · exact positive_cone_volume
      · rw [negative_cone, Measure.measure_neg, ← positive_cone]
        exact positive_cone_volume
    have he := (Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac
      (μ := (volume : Measure (Space 1)).toSphere)
      (f := (Subtype.val : sphere (0 : Space 1) 1 → Space 1))
      (by fun_prop) hne).mp (Eventually.of_forall hpair)
    rw [hmass 1 (Or.inl rfl), hmass (-1) (Or.inr rfl), one_smul, one_smul] at he
    rw [he]
    exact P201.unitSurfaceDimensionOne
  · simp [P201.unitSurface, P201Specs.unitSurface, hm]

variable {m : ℕ} {𝕜 : Type} [RCLike 𝕜]

section RadialMoments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Nontrivial E] [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma radial_ball_scale (p : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z in ball (0 : E) r, ‖z‖ ^ p) =
      r ^ (p + Module.finrank ℝ E) * ∫ z in ball (0 : E) 1, ‖z‖ ^ p := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure E)
    (fun z : E => ‖z‖ ^ p) (ball (0 : E) 1) hr
  simp only [_root_.smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr,
    mul_one, smul_eq_mul] at h
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    Real.mul_rpow hr.le (norm_nonneg _), integral_const_mul] at h
  calc
    _ = r ^ Module.finrank ℝ E *
        ((r ^ Module.finrank ℝ E)⁻¹ * ∫ z in ball (0 : E) r, ‖z‖ ^ p) := by
      rw [mul_inv_cancel_left₀ (pow_ne_zero _ hr.ne')]
    _ = r ^ Module.finrank ℝ E * (r ^ p * ∫ z in ball (0 : E) 1, ‖z‖ ^ p) := by rw [h]
    _ = _ := by rw [Real.rpow_add hr, Real.rpow_natCast]; ring

lemma radial_exterior_scale (p : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z in {z : E | r < ‖z‖}, ‖z‖ ^ p) =
      r ^ (p + Module.finrank ℝ E) * ∫ z in {z : E | 1 < ‖z‖}, ‖z‖ ^ p := by
  have hs : r • {z : E | 1 < ‖z‖} = {z : E | r < ‖z‖} := by
    ext z
    rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    simp only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    rw [← div_eq_inv_mul, lt_div_iff₀ hr, one_mul]
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure E)
    (fun z : E => ‖z‖ ^ p) {z : E | 1 < ‖z‖} hr
  rw [hs] at h
  simp only [smul_eq_mul] at h
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    Real.mul_rpow hr.le (norm_nonneg _), integral_const_mul] at h
  calc
    _ = r ^ Module.finrank ℝ E *
        ((r ^ Module.finrank ℝ E)⁻¹ * ∫ z in {z : E | r < ‖z‖}, ‖z‖ ^ p) := by
      rw [mul_inv_cancel_left₀ (pow_ne_zero _ hr.ne')]
    _ = r ^ Module.finrank ℝ E * (r ^ p * ∫ z in {z : E | 1 < ‖z‖}, ‖z‖ ^ p) := by rw [h]
    _ = _ := by rw [Real.rpow_add hr, Real.rpow_natCast]; ring

lemma radial_exterior_integrable {p r : ℝ} (hp : p < -(Module.finrank ℝ E : ℝ))
    (hr : 0 < r) :
    IntegrableOn (fun z : E => ‖z‖ ^ p) {z : E | r < ‖z‖} volume := by
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have ht : IntegrableOn (fun t : ℝ => t ^ (p + Module.finrank ℝ E - 1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have hti := (ht.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi (0 : ℝ))
  have hw : IntegrableOn (fun t : ℝ => t ^ (Module.finrank ℝ E - 1) •
      (Ioi r).indicator (fun u : ℝ => u ^ p) t) (Ioi 0) := by
    apply hti.congr_fun ?_ measurableSet_Ioi
    intro t ht
    by_cases htr : r < t
    · simp only [indicator_of_mem (mem_Ioi.mpr htr), smul_eq_mul]
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]
      congr 1
      rw [Nat.cast_sub hn]
      ring
    · simp [htr]
  rw [← integrable_fun_norm_addHaar (volume : Measure E)] at hw
  rw [← integrable_indicator_iff (by measurability : MeasurableSet {z : E | r < ‖z‖})]
  exact hw.congr (.of_forall fun z => by
    by_cases hz : r < ‖z‖ <;> simp [hz])

lemma radial_ball_integrable {α r : ℝ} (hα : 0 < α) :
    IntegrableOn (fun z : E => ‖z‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball 0 r) volume := by
  apply integrableOn_ball_of_norm_le_rpow (Module.finrank_pos (R := ℝ) (M := E))
    (α := (Module.finrank ℝ E : ℝ) - α) (C := 1) (by linarith)
  · exact Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        one_mul, neg_sub]
      exact le_rfl
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma radial_ball_moment {α : ℝ} (hα : 0 < α) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ r : ℝ, 0 < r →
      IntegrableOn (fun z : E => ‖z‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball 0 r) volume ∧
      (∫ z in ball (0 : E) r, ‖z‖ ^ (α - (Module.finrank ℝ E : ℝ))) = J * r ^ α := by
  refine ⟨∫ z in ball (0 : E) 1, ‖z‖ ^ (α - (Module.finrank ℝ E : ℝ)),
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro r hr
  refine ⟨radial_ball_integrable hα, ?_⟩
  rw [radial_ball_scale _ hr, sub_add_cancel, mul_comm]

lemma radial_tail_moment {β : ℝ} (hβ : β < 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r : ℝ, 0 < r →
      IntegrableOn (fun z : E => ‖z‖ ^ (β - (Module.finrank ℝ E : ℝ)))
        {z : E | r < ‖z‖} volume ∧
      (∫ z in {z : E | r < ‖z‖}, ‖z‖ ^ (β - (Module.finrank ℝ E : ℝ))) = L * r ^ β := by
  refine ⟨∫ z in {z : E | 1 < ‖z‖}, ‖z‖ ^ (β - (Module.finrank ℝ E : ℝ)),
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro r hr
  refine ⟨radial_exterior_integrable (by linarith) hr, ?_⟩
  rw [radial_exterior_scale _ hr, sub_add_cancel, mul_comm]

end RadialMoments

section ShellVolumes

lemma power_shell_bound {m : ℕ} {R h : ℝ} (hR : 0 < R) (hh : 0 ≤ h) (hhR : h ≤ R/2) :
    (R+h)^m - (R-h)^m ≤ (2*(m : ℝ)*2^(m-1))*h*R^(m-1) := by
  have hRm : 0 ≤ R-h := by linarith
  have hRp : 0 ≤ R+h := by positivity
  have hb := abs_pow_sub_pow_le (a := R+h) (b := R-h) m
  rw [abs_of_nonneg hRp, abs_of_nonneg hRm, max_eq_left (by linarith),
    show R+h-(R-h) = 2*h by ring, abs_of_nonneg (by positivity : 0 ≤ 2*h)] at hb
  calc
    (R+h)^m - (R-h)^m ≤ |(R+h)^m - (R-h)^m| := le_abs_self _
    _ ≤ 2*h*(m : ℝ)*(R+h)^(m-1) := hb
    _ ≤ 2*h*(m : ℝ)*(2*R)^(m-1) := by
      gcongr
      linarith
    _ = _ := by rw [mul_pow]; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma shell_volume_bound (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {R h : ℝ} (hR : 0 < R) (hh : 0 ≤ h) (hhR : h ≤ R/2) :
    μ.real {z : E | R-h ≤ ‖z‖ ∧ ‖z‖ ≤ R+h} ≤
      (2*(Module.finrank ℝ E : ℝ)*2^(Module.finrank ℝ E - 1)*μ.real (ball (0:E) 1))*
        h*R^(Module.finrank ℝ E - 1) := by
  have hRm : 0 ≤ R-h := by linarith
  have hRp : 0 ≤ R+h := by positivity
  have heq : {z : E | R-h ≤ ‖z‖ ∧ ‖z‖ ≤ R+h} =
      closedBall (0:E) (R+h) \ ball (0:E) (R-h) := by
    ext z
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
    tauto
  rw [heq, measureReal_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    measurableSet_ball (isCompact_closedBall (0:E) (R+h)).measure_lt_top.ne,
    ← Measure.addHaar_real_closedBall_eq_addHaar_real_ball μ (0:E) (R-h),
    Measure.addHaar_real_closedBall μ (0:E) hRp,
    Measure.addHaar_real_closedBall μ (0:E) hRm,
    ← sub_mul]
  have hv := mul_le_mul_of_nonneg_right (power_shell_bound (m := Module.finrank ℝ E) hR hh hhR) (measureReal_nonneg (μ := μ) (s := ball (0:E) 1))
  convert hv using 1 <;> ring

end ShellVolumes

lemma kernel_difference_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : E → F} {m : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hs : ContDiffOn ℝ 1 K ({0}ᶜ : Set E))
    (hder : ∀ w : E, w ≠ 0 → ‖fderiv ℝ K w‖ ≤ B / ‖w‖ ^ (m + 1))
    {z h : E} (hz : z ≠ 0) (hh : ‖h‖ ≤ ‖z‖ / 2) :
    ‖K (z + h) - K z‖ ≤ (2 : ℝ) ^ (m + 1) * B * ‖h‖ / ‖z‖ ^ (m + 1) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlow : ∀ w ∈ closedBall z (‖z‖ / 2), ‖z‖ / 2 ≤ ‖w‖ := by
    intro w hw
    have hw' : ‖w - z‖ ≤ ‖z‖ / 2 := by simpa [dist_eq_norm] using mem_closedBall.mp hw
    have ht := norm_sub_norm_le z w
    rw [norm_sub_rev] at ht
    linarith
  have hnw : ∀ w ∈ closedBall z (‖z‖ / 2), w ≠ 0 := by
    intro w hw he
    have hl := hlow w hw
    rw [he, norm_zero] at hl
    linarith
  have hb : ∀ w ∈ closedBall z (‖z‖ / 2),
      ‖fderiv ℝ K w‖ ≤ (2 : ℝ) ^ (m + 1) * B / ‖z‖ ^ (m + 1) := by
    intro w hw
    calc
      ‖fderiv ℝ K w‖ ≤ B / ‖w‖ ^ (m + 1) := hder w (hnw w hw)
      _ ≤ B / (‖z‖ / 2) ^ (m + 1) := by
        exact div_le_div_of_nonneg_left hB (pow_pos (by positivity) _)
          (pow_le_pow_left₀ (by positivity) (hlow w hw) _)
      _ = (2 : ℝ) ^ (m + 1) * B / ‖z‖ ^ (m + 1) := by rw [div_pow, div_div_eq_mul_div]; ring
  have hd : ∀ w ∈ closedBall z (‖z‖ / 2), DifferentiableAt ℝ K w := by
    intro w hw
    exact (hs.differentiableOn (by simp)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (hnw w hw))
  have hc := (convex_closedBall z (‖z‖ / 2)).norm_image_sub_le_of_norm_fderiv_le hd hb
    (mem_closedBall_self (by positivity : 0 ≤ ‖z‖ / 2))
    (show z + h ∈ closedBall z (‖z‖ / 2) by simpa [mem_closedBall, dist_eq_norm] using hh)
  simpa [div_mul_eq_mul_div, mul_assoc] using hc

def annularCutoff {E F : Type*} [Norm E] [Zero F] (K : E → F) (r R : ℝ) (z : E) : F :=
  if r < ‖z‖ ∧ ‖z‖ < R then K z else 0

lemma annularCutoff_eq_indicator {E F : Type*} [Norm E] [Zero F]
    (K : E → F) (r R : ℝ) :
    annularCutoff K r R = {z : E | r < ‖z‖ ∧ ‖z‖ < R}.indicator K := by
  funext z
  by_cases hz : r < ‖z‖ ∧ ‖z‖ < R <;> simp [annularCutoff, indicator, hz]

lemma annular_difference_pointwise {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedDivisionRing F] [NormedSpace ℝ F] {K g : E → F} {m : ℕ} {A B H α r R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hs : ContDiffOn ℝ 1 K ({0}ᶜ : Set E))
    (hsize : ∀ w : E, w ≠ 0 → ‖K w‖ ≤ A / ‖w‖ ^ m)
    (hder : ∀ w : E, w ≠ 0 → ‖fderiv ℝ K w‖ ≤ B / ‖w‖ ^ (m + 1))
    (hg : ∀ u v : E, ‖g u - g v‖ ≤ H * dist u v ^ α)
    {d : E} (hr : 0 < r) (hrd : r = 2 * ‖d‖) (hR : 2 * r ≤ R) (x z : E) :
    ‖(annularCutoff K r R z - annularCutoff K r R (z+d)) * (g (x-z) - g x)‖ ≤
      (if r < ‖z‖ then ((2 : ℝ)^(m+1)*B*‖d‖ / ‖z‖^(m+1)) * (H*‖z‖^α) else 0) +
      (if ‖z‖ ≤ 2*r then A/r^m * (H*(2*r)^α) else 0) +
      (if R-‖d‖ ≤ ‖z‖ ∧ ‖z‖ ≤ R+‖d‖ then A/(R/2)^m * (H*(2*R)^α) else 0) := by
  have hRp : 0 < R := by linarith
  have hdp : ‖d‖ ≤ R/2 := by linarith
  have hzadd : ‖z+d‖ ≤ ‖z‖+‖d‖ := norm_add_le z d
  have hzsub : ‖z‖ ≤ ‖z+d‖+‖d‖ := by
    have hh := norm_sub_norm_le z (z+d)
    have heq : z-(z+d) = -d := by abel
    rw [heq, norm_neg] at hh
    linarith
  have hg' : ‖g (x-z) - g x‖ ≤ H*‖z‖^α := by
    simpa [dist_eq_norm, sub_sub_cancel_left] using hg (x-z) x
  let bulk : ℝ := if r < ‖z‖ then ((2 : ℝ)^(m+1)*B*‖d‖ / ‖z‖^(m+1)) * (H*‖z‖^α) else 0
  let inner : ℝ := if ‖z‖ ≤ 2*r then A/r^m * (H*(2*r)^α) else 0
  let outer : ℝ := if R-‖d‖ ≤ ‖z‖ ∧ ‖z‖ ≤ R+‖d‖ then A/(R/2)^m * (H*(2*R)^α) else 0
  change _ ≤ bulk + inner + outer
  have hb0 : 0 ≤ bulk := by unfold bulk; split_ifs <;> positivity
  have hi0 : 0 ≤ inner := by unfold inner; split_ifs <;> positivity
  have ho0 : 0 ≤ outer := by unfold outer; split_ifs <;> positivity
  have hib (w : E) (hw : r < ‖w‖) (hz : ‖z‖ ≤ 2*r) :
      ‖K w‖ * ‖g (x-z)-g x‖ ≤ inner := by
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hr.trans hw)
    have hk : ‖K w‖ ≤ A/r^m := (hsize w hw0).trans
      (div_le_div_of_nonneg_left hA (pow_pos hr _) (pow_le_pow_left₀ hr.le hw.le _))
    have hgg : ‖g (x-z)-g x‖ ≤ H*(2*r)^α := hg'.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hz hα) hH)
    simp only [inner, ite_eq_left hz]
    exact mul_le_mul hk hgg (norm_nonneg _) (by positivity)
  have hob (w : E) (hw : R/2 ≤ ‖w‖)
      (hz : R-‖d‖ ≤ ‖z‖ ∧ ‖z‖ ≤ R+‖d‖) :
      ‖K w‖ * ‖g (x-z)-g x‖ ≤ outer := by
    have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < R/2) hw)
    have hk : ‖K w‖ ≤ A/(R/2)^m := (hsize w hw0).trans
      (div_le_div_of_nonneg_left hA (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hw _))
    have hz2 : ‖z‖ ≤ 2*R := by linarith [hz.2]
    have hgg : ‖g (x-z)-g x‖ ≤ H*(2*R)^α := hg'.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hz2 hα) hH)
    simp only [outer, ite_eq_left hz]
    exact mul_le_mul hk hgg (norm_nonneg _) (by positivity)
  by_cases hz : r < ‖z‖ ∧ ‖z‖ < R
  · by_cases hzd : r < ‖z+d‖ ∧ ‖z+d‖ < R
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz.1)
      have hhalf : ‖d‖ ≤ ‖z‖/2 := by linarith [hz.1]
      have hk := kernel_difference_bound hB hs hder hz0 hhalf
      rw [norm_sub_rev] at hk
      have hb : ‖(annularCutoff K r R z - annularCutoff K r R (z+d)) * (g (x-z) - g x)‖ ≤ bulk := by
        simp only [annularCutoff, ite_eq_left hz, ite_eq_left hzd, norm_mul, bulk, ite_eq_left hz.1]
        exact mul_le_mul hk hg' (norm_nonneg _) (by positivity)
      linarith
    · simp only [annularCutoff, ite_eq_left hz, ite_eq_right hzd, sub_zero, norm_mul]
      push Not at hzd
      by_cases hin : ‖z+d‖ ≤ r
      · have hzi : ‖z‖ ≤ 2*r := by linarith
        have hb := hib z hz.1 hzi
        linarith
      · have hout : R ≤ ‖z+d‖ := hzd (by linarith)
        have hzo : R-‖d‖ ≤ ‖z‖ ∧ ‖z‖ ≤ R+‖d‖ := by constructor <;> linarith [hz.2]
        have hw : R/2 ≤ ‖z‖ := by linarith [hzo.1]
        have hb := hob z hw hzo
        linarith
  · by_cases hzd : r < ‖z+d‖ ∧ ‖z+d‖ < R
    · simp only [annularCutoff, ite_eq_right hz, ite_eq_left hzd, zero_sub, norm_neg, norm_mul]
      push Not at hz
      by_cases hin : ‖z‖ ≤ r
      · have hzi : ‖z‖ ≤ 2*r := by linarith
        have hb := hib (z+d) hzd.1 hzi
        linarith
      · have hout : R ≤ ‖z‖ := hz (by linarith)
        have hzo : R-‖d‖ ≤ ‖z‖ ∧ ‖z‖ ≤ R+‖d‖ := by constructor <;> linarith [hzd.2]
        have hw : R/2 ≤ ‖z+d‖ := by linarith
        have hb := hob (z+d) hw hzo
        linarith
    · simp only [annularCutoff, ite_eq_right hz, ite_eq_right hzd, sub_self, zero_mul, norm_zero]
      positivity


lemma bulk_rpow_identity {m : ℕ} {t : ℝ} (ht : 0 < t) (α B H d : ℝ) :
    ((2 : ℝ)^(m+1)*B*d / t^(m+1)) * (H*t^α) =
      ((2 : ℝ)^(m+1)*B*d*H) * t^(α-(m:ℝ)-1) := by
  have he : α-(m:ℝ)-1 = α-((m+1:ℕ):ℝ) := by push_cast; ring
  rw [he, Real.rpow_sub ht, Real.rpow_natCast]
  ring

lemma inner_cutoff_majorant_eq (m : ℕ) (α A H V : ℝ) {r : ℝ} (hr : 0 < r) :
    (A / r ^ m) * H * (2 * r) ^ α * (V * (2 * r) ^ m) =
      (A * V * (2 : ℝ) ^ m * (2 : ℝ) ^ α) * H * r ^ α := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le, mul_pow]
  field_simp
  <;> ring

lemma normalized_inner_cutoff_majorant_eq (m : ℕ) (α A H V : ℝ) {h : ℝ} (hh : 0 < h) :
    (A / (2 * h) ^ m) * H * (4 * h) ^ α * (V * (4 * h) ^ m) =
      (A * V * (2 : ℝ) ^ m * (4 : ℝ) ^ α) * H * h ^ α := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hh.le]
  have hp : (4 * h) ^ m = (2 : ℝ) ^ m * (2 * h) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hp]
  field_simp
  <;> ring

lemma outer_cutoff_majorant_eq {m : ℕ} (hm : 1 ≤ m) (α A H D : ℝ) {h R : ℝ} (hR : 0 < R) :
    (A / (R / 2) ^ m) * H * (2 * R) ^ α * (D * h * R ^ (m - 1)) =
      (A * D * (2 : ℝ) ^ m * (2 : ℝ) ^ α) * H * (h * R ^ (α - 1)) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le]
  have hp : R ^ m = R ^ (m - 1) * R := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  rw [Real.rpow_sub hR, Real.rpow_one, div_pow, hp]
  field_simp
  <;> ring

lemma radius_decay_bound {α h R : ℝ} (hα1 : α < 1) (hh : 0 < h) (hhR : h ≤ R) :
    h * R ^ (α - 1) ≤ h ^ α := by
  calc
    _ ≤ h * h ^ (α - 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hh hhR (by linarith)) hh.le
    _ = _ := by rw [Real.rpow_sub hh, Real.rpow_one]; field_simp

lemma outer_cutoff_majorant_bound {m : ℕ} (hm : 1 ≤ m) {α A H D h R : ℝ}
    (hα1 : α < 1) (hA : 0 ≤ A) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hh : 0 < h) (hhR : h ≤ R) :
    (A / (R / 2) ^ m) * H * (2 * R) ^ α * (D * h * R ^ (m - 1)) ≤
      (A * D * (2 : ℝ) ^ m * (2 : ℝ) ^ α) * H * h ^ α := by
  rw [outer_cutoff_majorant_eq hm α A H D (hh.trans_le hhR)]
  exact mul_le_mul_of_nonneg_left (radius_decay_bound hα1 hh hhR) (by positivity)

lemma normalized_bulk_majorant_eq (α D H L : ℝ) {h : ℝ} (hh : 0 < h) :
    D * H * h * L * (2 * h) ^ (α - 1) =
      (D * L * (2 : ℝ) ^ (α - 1)) * H * h ^ α := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le,
    Real.rpow_sub hh, Real.rpow_one]
  field_simp

lemma normalized_near_majorant_eq (α A H J c : ℝ) (hc : 0 ≤ c) {h : ℝ} (hh : 0 < h) :
    A * H * J * (c * h) ^ α = (A * J * c ^ α) * H * h ^ α := by
  rw [Real.mul_rpow hc hh.le]
  ring

section AnnularIntegralBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Nontrivial E] [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma annular_difference_integral_bound {α A B : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {𝕜 : Type*} [RCLike 𝕜] (K g : E → 𝕜) (H : ℝ), 0 ≤ H →
    ContDiffOn ℝ 1 K ({0}ᶜ : Set E) →
    (∀ w : E, w ≠ 0 → ‖K w‖ ≤ A / ‖w‖ ^ Module.finrank ℝ E) →
    (∀ w : E, w ≠ 0 → ‖fderiv ℝ K w‖ ≤ B / ‖w‖ ^ (Module.finrank ℝ E + 1)) →
    (∀ u v : E, ‖g u - g v‖ ≤ H * dist u v ^ α) →
    ∀ (x d : E), d ≠ 0 → ∀ R : ℝ, 4 * ‖d‖ ≤ R →
    ‖∫ z, (annularCutoff K (2 * ‖d‖) R z - annularCutoff K (2 * ‖d‖) R (z+d)) *
      (g (x-z) - g x)‖ ≤ C * H * ‖d‖ ^ α := by
  let n := Module.finrank ℝ E
  let V := (volume : Measure E).real (ball (0:E) 1)
  let D := 2 * (n : ℝ) * 2 ^ (n-1) * V
  have hn : 1 ≤ n := Module.finrank_pos (R := ℝ) (M := E)
  have hV : 0 ≤ V := measureReal_nonneg
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨L, hL, hLm⟩ := radial_tail_moment (E := E) (β := α - 1) (by linarith)
  let C := (2 : ℝ)^(n+1) * B * L * (2 : ℝ)^(α-1) +
    A * V * (2 : ℝ)^n * (4 : ℝ)^α + A * D * (2 : ℝ)^n * (2 : ℝ)^α
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro 𝕜 _ K g H hH hs hsize hder hg x d hd R hRd
  let h := ‖d‖
  let r := 2*h
  have hh : 0 < h := norm_pos_iff.mpr hd
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [h] at hh ⊢; linarith
  have hhR : h ≤ R := by dsimp [h]; linarith
  have hhR2 : h ≤ R/2 := by dsimp [h]; linarith
  let S : Set E := {z | R-h ≤ ‖z‖ ∧ ‖z‖ ≤ R+h}
  have hSm : MeasurableSet S := by dsimp [S]; measurability
  have hSfinite : volume S ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (show S ⊆ closedBall (0:E) (R+h) by
      intro z hz
      exact mem_closedBall_zero_iff.mpr hz.2)).trans_lt
      (isCompact_closedBall (0:E) (R+h)).measure_lt_top
  let bulk : E → ℝ := {z : E | r < ‖z‖}.indicator
    (fun z => ((2 : ℝ)^(n+1)*B*h*H) * ‖z‖^(α-(n:ℝ)-1))
  let inner : E → ℝ := (closedBall (0:E) (2*r)).indicator
    (fun _ => A/r^n * (H*(2*r)^α))
  let outer : E → ℝ := S.indicator (fun _ => A/(R/2)^n * (H*(2*R)^α))
  have ht := (hLm r hr).1
  have he : (α - 1) - (n:ℝ) = α - (n:ℝ) - 1 := by ring
  change IntegrableOn (fun z : E => ‖z‖ ^ ((α-1)-(n:ℝ))) {z : E | r < ‖z‖} volume at ht
  rw [he] at ht
  have ht' : IntegrableOn (fun z : E => ((2 : ℝ)^(n+1)*B*h*H) * ‖z‖^(α-(n:ℝ)-1)) {z : E | r < ‖z‖} volume := ht.const_mul _
  have hbulk : Integrable bulk volume := ht'.integrable_indicator (by measurability)
  have hinner : Integrable inner volume :=
    (integrableOn_const (μ := volume)
      (s := closedBall (0:E) (2*r)) (C := A/r^n*(H*(2*r)^α))
      (isCompact_closedBall (0:E) (2*r)).measure_lt_top.ne).integrable_indicator measurableSet_closedBall
  have houter : Integrable outer volume :=
    (integrableOn_const (μ := volume) (s := S) (C := A/(R/2)^n*(H*(2*R)^α)) hSfinite).integrable_indicator hSm
  have hpoint (z : E) :
      ‖(annularCutoff K r R z - annularCutoff K r R (z+d)) * (g (x-z)-g x)‖ ≤
        bulk z + inner z + outer z := by
    have ht := annular_difference_pointwise hA hB hH hα.le hs hsize hder hg
      hr (show r = 2*‖d‖ from rfl) (show 2*r ≤ R by dsimp [r,h]; linarith) x z
    convert ht using 1
    dsimp [bulk, inner, outer, S]
    simp only [indicator, mem_ofPred_eq, mem_closedBall, dist_zero_right, n]
    congr 2
    split_ifs with hz
    · exact (bulk_rpow_identity (hr.trans hz) α B H ‖d‖).symm
    · rfl
  have hbval : (∫ z, bulk z) = ((2 : ℝ)^(n+1)*B*L*(2 : ℝ)^(α-1))*H*h^α := by
    rw [show (∫ z, bulk z) = ((2 : ℝ)^(n+1)*B*h*H) *
      ∫ z in {z : E | r < ‖z‖}, ‖z‖^(α-(n:ℝ)-1) by
        dsimp [bulk]; rw [integral_indicator (by measurability), integral_const_mul]]
    have hev := (hLm r hr).2
    change (∫ z in {z : E | r < ‖z‖}, ‖z‖ ^ ((α-1)-(n:ℝ))) = L*r^(α-1) at hev
    rw [he] at hev
    rw [hev]
    dsimp [r]
    have hc := normalized_bulk_majorant_eq α ((2 : ℝ)^(n+1)*B) H L hh
    nlinarith [hc]
  have hival : (∫ z, inner z) = (A*V*(2 : ℝ)^n*(4 : ℝ)^α)*H*h^α := by
    dsimp [inner]
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
      Measure.addHaar_real_closedBall volume (0:E) (by positivity : 0 ≤ 2*r)]
    dsimp [r]
    have hc := normalized_inner_cutoff_majorant_eq n α A H V hh
    convert hc using 1 <;> dsimp [V,n] <;> ring
  have hoval : (∫ z, outer z) ≤ (A*D*(2 : ℝ)^n*(2 : ℝ)^α)*H*h^α := by
    dsimp [outer]
    rw [integral_indicator_const _ hSm, smul_eq_mul]
    have hsv : volume.real S ≤ D*h*R^(n-1) := shell_volume_bound volume hR hh.le hhR2
    calc
      volume.real S * (A/(R/2)^n*(H*(2*R)^α)) ≤
          (D*h*R^(n-1)) * (A/(R/2)^n*(H*(2*R)^α)) :=
        mul_le_mul_of_nonneg_right hsv (by positivity)
      _ = (A/(R/2)^n)*H*(2*R)^α*(D*h*R^(n-1)) := by ring
      _ ≤ _ := outer_cutoff_majorant_bound hn hα1 hA hH hD hh hhR
  have hadd : Integrable (fun z => bulk z + inner z) volume := hbulk.add hinner
  calc
    _ ≤ ∫ z, bulk z + inner z + outer z :=
      norm_integral_le_of_norm_le ((hbulk.add hinner).add houter) (.of_forall hpoint)
    _ ≤ C*H*h^α := by
      rw [integral_add hadd houter, integral_add hbulk hinner, hbval, hival]
      dsimp [C]
      nlinarith

end AnnularIntegralBound

lemma finite_kernel_translation_identity {F g : Space m → 𝕜} {M : ℝ}
    (hF : Integrable F volume) (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ x, ‖g x‖ ≤ M) (x y : Space m) :
    (∫ z, F z * g (x-z)) - (∫ z, F z * g (y-z)) =
    ∫ z, (F z - F (z+(y-x))) * (g (x-z)-g x) := by
  let h := y-x
  have hgx : AEStronglyMeasurable (fun z => g (x-z)) volume :=
    hg.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hgy : AEStronglyMeasurable (fun z => g (y-z)) volume :=
    hg.comp_measurePreserving (volume.measurePreserving_sub_left y)
  have hFx : Integrable (fun z => F z * g (x-z)) volume :=
    hF.mul_bdd hgx (Filter.Eventually.of_forall fun z => hbound (x-z))
  have hFy : Integrable (fun z => F z * g (y-z)) volume :=
    hF.mul_bdd hgy (Filter.Eventually.of_forall fun z => hbound (y-z))
  have hFh : Integrable (fun z => F (z+h)) volume := hF.comp_add_right h
  have hFhx : Integrable (fun z => F (z+h) * g (x-z)) volume :=
    hFh.mul_bdd hgx (Filter.Eventually.of_forall fun z => hbound (x-z))
  have he : (∫ z, F z * g (y-z)) = ∫ z, F (z+h) * g (x-z) := by
    rw [← integral_add_right_eq_self (fun z => F z * g (y-z)) h]
    congr 1
    funext z
    have : y-(z+h) = x-z := by dsimp [h]; abel
    rw [this]
  rw [he, ← integral_sub hFx hFhx]
  have hsum : Integrable (fun z => (F z-F (z+h))*g x) volume :=
    (hF.sub hFh).mul_const (g x)
  have hzero : (∫ z, (F z-F (z+h))*g x) = 0 := by
    rw [integral_mul_const, integral_sub hF hFh,
      integral_add_right_eq_self, sub_self, zero_mul]
  calc
    _ = (∫ z, (F z-F (z+h))*g (x-z)) -
        (∫ z, (F z-F (z+h))*g x) := by
      rw [hzero, sub_zero]
      congr 1
      funext z
      ring
    _ = _ := by
      have hint : Integrable (fun z => (F z-F (z+h))*g (x-z)) volume :=
        (hF.sub hFh).mul_bdd hgx (Filter.Eventually.of_forall fun z => hbound (x-z))
      rw [← integral_sub hint hsum]
      congr 1
      funext z
      ring

lemma kernel_measurable {K : Space m → 𝕜} (hK : KernelHypotheses K) : Measurable K :=
  measurable_of_continuousOn_compl_singleton 0 hK.smooth.continuousOn

lemma polar_mean_zero {K : Space m → 𝕜} (hK : KernelHypotheses K) :
    (∫ θ : sphere (0 : Space m) 1, K θ ∂(volume : Measure (Space m)).toSphere) = 0 := by
  have h := hK.mean_zero
  change (∫ z, K z ∂P201.unitSurface m) = 0 at h
  rw [unitSurface_eq_polar m] at h
  rw [integral_map (by fun_prop) (kernel_measurable hK).aestronglyMeasurable] at h
  exact h

/-- Homogeneity transfers the compact unit-sphere bound to every nonzero point. -/
lemma homogeneous_size {K : Space m → 𝕜} (hK : KernelHypotheses K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Space m, z ≠ 0 → ‖K z‖ ≤ M / ‖z‖ ^ m := by
  have hc : ContinuousOn K (sphere (0 : Space m) 1) :=
    hK.smooth.continuousOn.mono (by
      intro z hz
      change z ≠ 0
      intro he
      simp [he] at hz)
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space m) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Space m := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hz]
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hzu : ‖z‖ • u = z := by simp [u, smul_smul, hn.ne']
  have heq := hK.homogeneous ‖z‖ hn u hu0
  rw [hzu] at heq
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (‖z‖ ^ m)⁻¹ * ‖K u‖ ≤ (‖z‖ ^ m)⁻¹ * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC u (by simpa using hu)).trans (le_max_left _ _))
        (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

lemma size_of_sphere_bound {K : Space m → 𝕜} (hK : KernelHypotheses K)
    {A : ℝ} (hA : ∀ u : Space m, ‖u‖ = 1 → ‖K u‖ ≤ A)
    {z : Space m} (hz : z ≠ 0) : ‖K z‖ ≤ A / ‖z‖ ^ m := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Space m := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hz]
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hzu : ‖z‖ • u = z := by simp [u, smul_smul, hn.ne']
  have heq := hK.homogeneous ‖z‖ hn u hu0
  rw [hzu] at heq
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (‖z‖ ^ m)⁻¹ * ‖K u‖ ≤ (‖z‖ ^ m)⁻¹ * A :=
      mul_le_mul_of_nonneg_left (hA u hu) (by positivity)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

lemma kernel_differentiableAt {K : Space m → 𝕜} (hK : KernelHypotheses K)
    {z : Space m} (hz : z ≠ 0) : DifferentiableAt ℝ K z :=
  (hK.smooth.differentiableOn (by simp)).differentiableAt
    (isOpen_compl_singleton.mem_nhds hz)

/-- Differentiating the dilation identity supplies the extra inverse radius
in the derivative bound; no derivative estimate away from the sphere is assumed. -/
lemma derivative_of_sphere_bound {K : Space m → 𝕜} (hK : KernelHypotheses K)
    {B : ℝ} (hB : ∀ u : Space m, ‖u‖ = 1 → ‖fderiv ℝ K u‖ ≤ B)
    {z : Space m} (hz : z ≠ 0) : ‖fderiv ℝ K z‖ ≤ B / ‖z‖ ^ (m + 1) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Space m := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hz]
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hzu : ‖z‖ • u = z := by simp [u, smul_smul, hn.ne']
  have he : (fun y : Space m => K (‖z‖ • y)) =ᶠ[𝓝 u]
      (fun y => ((‖z‖ ^ m)⁻¹ : ℝ) • K y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hu0] with y hy
    exact hK.homogeneous ‖z‖ hn y hy
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hds : fderiv ℝ (fun y : Space m => ‖z‖ • y) u =
      ‖z‖ • ContinuousLinearMap.id ℝ (Space m) :=
    ((hasFDerivAt_id u).const_smul ‖z‖).fderiv
  rw [fderiv_fun_comp u
      (show DifferentiableAt ℝ K (‖z‖ • u) by rw [hzu]; exact kernel_differentiableAt hK hz)
      (differentiableAt_id.const_smul ‖z‖),
    hds,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    fderiv_fun_const_smul (kernel_differentiableAt hK hu0), hzu] at hd
  have hdn := congrArg norm hd
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hn,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le m))] at hdn
  have hb : ‖z‖ * ‖fderiv ℝ K z‖ ≤ (‖z‖ ^ m)⁻¹ * B := by
    rw [hdn]
    exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)
  apply (le_div_iff₀ (pow_pos hn (m + 1))).mpr
  have hmpos : 0 < ‖z‖ ^ m := pow_pos hn m
  calc
    ‖fderiv ℝ K z‖ * ‖z‖ ^ (m + 1) = ‖z‖ ^ m * (‖z‖ * ‖fderiv ℝ K z‖) := by
      rw [pow_succ]; ring
    _ ≤ ‖z‖ ^ m * ((‖z‖ ^ m)⁻¹ * B) := mul_le_mul_of_nonneg_left hb hmpos.le
    _ = B := by rw [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]

lemma integral_polar_product (hm : 1 ≤ m) (f : Space m → 𝕜) :
    (∫ z, f z) =
      ∫ p : sphere (0 : Space m) 1 × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂(volume : Measure (Space m)).toSphere.prod (Measure.volumeIoiPow (m - 1)) := by
  let : NeZero m := ⟨by omega⟩
  calc
    (∫ z, f z) = ∫ z : ({0}ᶜ : Set (Space m)), f z.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure (Space m)).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd (Space m)).symm p).1))
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace, Fintype.card_fin] using h

lemma annular_integrable {K : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m))) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    IntegrableOn K {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R} volume := by
  let S := closedBall (0 : Space m) R ∩ {z : Space m | ε ≤ ‖z‖}
  have hS : IsCompact S := (isCompact_closedBall (0 : Space m) R).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hc : ContinuousOn K S := hK.mono (by
    intro z hz
    change z ≠ 0
    exact norm_pos_iff.mp (hε.trans_le hz.2))
  exact (hc.integrableOn_compact hS).mono_set (by
    intro z hz
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz.2.le, hz.1.le⟩)

lemma annular_cancellation (hm : 1 ≤ m) {K : Space m → 𝕜}
    (hK : KernelHypotheses K) (ε R : ℝ) :
    (∫ z in {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0 := by
  rw [← integral_indicator (by measurability :
    MeasurableSet {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}), integral_polar_product hm]
  have he (p : sphere (0 : Space m) 1 × Ioi (0 : ℝ)) :
      {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}.indicator K (p.2.1 • p.1.1) =
        K p.1.1 * (if ε < p.2.1 ∧ p.2.1 < R then ((p.2.1 ^ m)⁻¹ : ℝ) else 0) := by
    have hn : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hz : p.1.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    have hr : 0 < p.2.1 := p.2.2
    by_cases h : ε < p.2.1 ∧ p.2.1 < R
    · have hmem : p.2.1 • p.1.1 ∈ {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R} := by
        simpa [norm_smul, abs_of_pos hr, hn] using h
      rw [indicator_of_mem hmem, ite_eq_left h, hK.homogeneous _ hr _ hz,
        RCLike.real_smul_eq_coe_mul, mul_comm]
    · simp [indicator, norm_smul, abs_of_pos hr, hn, h]
  simp_rw [he, apply_ite (algebraMap ℝ 𝕜), map_zero]
  exact (integral_prod_mul (μ := (volume : Measure (Space m)).toSphere)
    (ν := Measure.volumeIoiPow (m - 1)) (fun θ : sphere (0 : Space m) 1 => K θ.1)
    (fun r : Ioi (0 : ℝ) => ((if ε < r.1 ∧ r.1 < R then ((r.1 ^ m)⁻¹ : ℝ) else 0) : 𝕜))).trans
      (by rw [polar_mean_zero hK, zero_mul])

theorem annularCancellation : P201Specs.Elliptic.HolderCancellation.annularCancellationStatement := by
  intro m hm 𝕜 _ K hK ε R hε
  exact ⟨annular_integrable hK.smooth.continuousOn hε R, annular_cancellation hm hK ε R⟩

lemma holder_continuous {α : ℝ} (hα : 0 < α) {g : Space m → 𝕜}
    (hg : IsHolder α g) : Continuous g := by
  obtain ⟨M, H, hM, hH, hsup, hhol⟩ := hg
  let C : ℝ≥0 := ⟨H, hH⟩
  let a : ℝ≥0 := ⟨α, hα.le⟩
  have hh : HolderWith C a g := by
    intro x y
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (g x) (g y)) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ α
    rw [← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    change ENNReal.ofReal (dist (g x) (g y)) ≤
      ENNReal.ofReal H * ENNReal.ofReal (dist x y ^ α)
    rw [← ENNReal.ofReal_mul hH]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hhol x y)
  exact hh.continuous hα

/-- Continuity of the input and compact support suffice for each positive
truncation to be an absolutely defined Lebesgue integral. -/
lemma truncated_integrable {K g : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : Space m) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y => K (x - y) * g y) {y | ε < ‖x - y‖} volume := by
  let S := tsupport g ∩ {y : Space m | ε ≤ ‖x - y‖}
  have hS : IsCompact S := hgc.inter_right
    (isClosed_le continuous_const (continuous_const.sub continuous_id).norm)
  have hc : ContinuousOn (fun y => K (x - y)) S := by
    apply hK.comp (continuous_const.sub continuous_id).continuousOn
    intro y hy
    change x - y ≠ 0
    exact norm_pos_iff.mp (hε.trans_le hy.2)
  have hi : IntegrableOn (fun y => K (x - y) * g y) S volume :=
    IntegrableOn.continuousOn_mul hc
      (hg.integrable_of_hasCompactSupport hgc).integrableOn hS
  apply (hi.integrable_indicator hS.measurableSet).integrableOn.congr
  have hA : MeasurableSet {y : Space m | ε < ‖x - y‖} := by measurability
  filter_upwards [ae_restrict_mem hA] with y hy
  by_cases hs : y ∈ tsupport g
  · have : y ∈ S := ⟨hs, hy.le⟩
    simp [this]
  · have hz : g y = 0 := image_eq_zero_of_notMem_tsupport hs
    simp [hz]

/-- The compensated singularity has order α-m, which is locally integrable
for every α>0. The upper restriction α<1 is unnecessary for existence. -/
lemma compensated_integrable (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    {K g : Space m → 𝕜} (hK : KernelHypotheses K)
    (hgc : HasCompactSupport g) (hg : IsHolder α g) (x : Space m) :
    Integrable (compensatedIntegrand K g x) volume := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨M, hM, hsize⟩ := homogeneous_size hK
  obtain ⟨N, H, hN, hH, hsup, hhol⟩ := hg
  have hcont : Continuous g := holder_continuous hα ⟨N, H, hN, hH, hsup, hhol⟩
  have hmeas : AEStronglyMeasurable (fun z : Space m => K z * (g (x - z) - g x)) volume :=
    ((kernel_measurable hK).mul
      ((hcont.comp (continuous_const.sub continuous_id)).measurable.sub
        measurable_const)).aestronglyMeasurable
  have hi : IntegrableOn (fun z : Space m => K z * (g (x - z) - g x)) (ball 0 1) volume := by
    apply integrableOn_ball_of_norm_le_rpow
      (by simpa [P201Specs.Space] using hm : 1 ≤ Module.finrank ℝ (Space m))
      (α := (m : ℝ) - α) (C := M * H)
      (by simpa [P201Specs.Space] using sub_lt_self (m : ℝ) hα) _ hmeas
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Space m))] with z hz
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hl : ‖g (x - z) - g x‖ ≤ H * ‖z‖ ^ α := by
      simpa [dist_eq_norm, sub_sub_cancel_left] using hhol (x - z) x
    calc
      ‖K z * (g (x - z) - g x)‖ = ‖K z‖ * ‖g (x - z) - g x‖ := norm_mul _ _
      _ ≤ (M / ‖z‖ ^ m) * (H * ‖z‖ ^ α) :=
        mul_le_mul (hsize z hz) hl (norm_nonneg _) (by positivity)
      _ = M * H * ‖z‖ ^ (-((m : ℝ) - α)) := by
        rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp.le,
          show -((m : ℝ) - α) = -(m : ℝ) + α by ring, Real.rpow_add hp]
        ring
  have ht := truncated_integrable hK.smooth.continuousOn hcont hgc x
    (by norm_num : (0 : ℝ) < 1 / 2)
  have ht' : IntegrableOn (fun z : Space m => K z * g (x - z)) {z | 1 / 2 < ‖z‖} volume := by
    rw [← integrable_indicator_iff (by measurability)] at ht ⊢
    have hh := (volume.measurePreserving_sub_left x).integrable_comp_emb
      (Homeomorph.subLeft x).measurableEmbedding
      (g := {z : Space m | 1 / 2 < ‖z‖}.indicator (fun z => K z * g (x - z)))
    apply hh.mp
    convert ht using 1
    ext y
    simp [indicator, sub_sub_cancel]
  have hc : IntegrableOn (fun z : Space m => K z * g (x - z)) (ball (0 : Space m) 1)ᶜ volume :=
    ht'.mono_set (by
      intro z hz
      simp only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hz
      dsimp
      linarith)
  have htotal := (hi.integrable_indicator measurableSet_ball).add
    (hc.integrable_indicator measurableSet_ball.compl)
  apply htotal.congr
  exact ae_of_all _ fun z => by
    by_cases hz : z ∈ ball (0 : Space m) 1 <;> simp [compensatedIntegrand, hz]

lemma truncated_eq_reflected (K g : Space m → 𝕜) (ε : ℝ) (x : Space m) :
    truncated K g ε x = ∫ z in {z : Space m | ε < ‖z‖}, K z * g (x - z) := by
  rw [truncated, ← integral_indicator (by measurability :
    MeasurableSet {y : Space m | ε < ‖x - y‖}),
    ← integral_indicator (by measurability : MeasurableSet {z : Space m | ε < ‖z‖})]
  have h := (volume.measurePreserving_sub_left x).integral_comp
    (Homeomorph.subLeft x).measurableEmbedding
    ({z : Space m | ε < ‖z‖}.indicator (fun z => K z * g (x - z)))
  rw [← h]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp [indicator, sub_sub_cancel]

lemma truncated_compensated (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    {K g : Space m → 𝕜} (hK : KernelHypotheses K)
    (hgc : HasCompactSupport g) (hg : IsHolder α g) (x : Space m)
    {ε : ℝ} (hε : 0 < ε) :
    truncated K g ε x = ∫ z in {z : Space m | ε < ‖z‖}, compensatedIntegrand K g x z := by
  let A := {z : Space m | ε < ‖z‖}
  let D := {z : Space m | ε < ‖z‖ ∧ ‖z‖ < 1}
  let F := compensatedIntegrand K g x
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hF := compensated_integrable hm hα hK hgc hg x
  have hDK : IntegrableOn (fun z => K z * g x) D volume :=
    (annular_integrable hK.smooth.continuousOn hε 1).mul_const (g x)
  have hG : IntegrableOn (D.indicator (fun z => K z * g x)) A volume :=
    (hDK.integrable_indicator hD).integrableOn
  rw [truncated_eq_reflected]
  calc
    _ = ∫ z in A, F z + D.indicator (fun z => K z * g x) z := by
      apply setIntegral_congr_fun hA
      intro z hz
      by_cases hb : z ∈ ball (0 : Space m) 1
      · have hzD : z ∈ D := ⟨hz, by simpa using hb⟩
        simp [F, compensatedIntegrand, hb, hzD, mul_sub]
      · have hzD : z ∉ D := by
          intro hzD
          exact hb (by simpa using hzD.2)
        simp [F, compensatedIntegrand, hb, hzD]
    _ = (∫ z in A, F z) + ∫ z in A, D.indicator (fun z => K z * g x) z :=
      integral_add hF.integrableOn hG
    _ = ∫ z in A, F z := by
      have hh : (∫ z in A, D.indicator (fun z => K z * g x) z) = 0 := by
        rw [setIntegral_indicator hD, inter_eq_right.mpr (show D ⊆ A from fun _ h => h.1),
          integral_mul_const, annular_cancellation hm hK ε 1, zero_mul]
      rw [hh, add_zero]

theorem principalValueExists : P201Specs.Elliptic.HolderCancellation.principalValueStatement := by
  intro m hm 𝕜 _ α hα _ K g hK hgc hg x
  let : NeZero m := ⟨by omega⟩
  refine ⟨fun ε hε => truncated_integrable hK.smooth.continuousOn
    (holder_continuous hα hg) hgc x hε, compensated_integrable hm hα hK hgc hg x, ?_⟩
  let F := compensatedIntegrand K g x
  have hi : Integrable F volume := compensated_integrable hm hα hK hgc hg x
  have ht : Tendsto (fun ε : ℝ => ∫ z in {z : Space m | ε < ‖z‖}, F z)
      (𝓝[>] 0) (𝓝 (∫ z, F z)) := by
    have hmE (ε : ℝ) : MeasurableSet {z : Space m | ε < ‖z‖} := by measurability
    simp_rw [← integral_indicator (hmE _)]
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall fun ε =>
        (hi.indicator (by measurability)).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => ae_of_all _ fun z => norm_indicator_le_norm_self _ _
    · exact hi.norm
    · filter_upwards [volume.ae_ne (0 : Space m)] with z hz
      have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds] with ε hε
      simp [hε]
  have he : (fun ε => truncated K g ε x) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ z in {z : Space m | ε < ‖z‖}, F z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact truncated_compensated hm hα hK hgc hg x hε
  have ht' := ht.congr' he.symm
  have hv : principalValue K g x = ∫ z, F z := ht'.limUnder_eq
  exact ⟨by rw [hv]; exact ht', hv⟩

lemma ae_norm_ne {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ z : Space m ∂volume, ‖z‖ ≠ r := by
  rw [ae_iff]
  simpa [sphere, dist_zero_right] using
    (Measure.addHaar_sphere_of_ne_zero (volume : Measure (Space m)) 0 hr)

lemma indicator_radius_difference {K : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hcancel : ∀ ε R : ℝ, 0 < ε →
      (∫ z in {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0)
    (c : 𝕜) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    Integrable (fun z => K z * ((ball (0 : Space m) s).indicator (fun _ => c) z -
      (ball (0 : Space m) r).indicator (fun _ => c) z)) volume ∧
    (∫ z, K z * ((ball (0 : Space m) s).indicator (fun _ => c) z -
      (ball (0 : Space m) r).indicator (fun _ => c) z)) = 0 := by
  let D := {z : Space m | r < ‖z‖ ∧ ‖z‖ < s}
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hiD : IntegrableOn (fun z => K z*c) D volume :=
    (annular_integrable hK hr s).mul_const c
  have hi : Integrable (D.indicator (fun z => K z*c)) volume :=
    hiD.integrable_indicator hD
  have he : (fun z => K z * ((ball (0 : Space m) s).indicator (fun _ => c) z -
      (ball (0 : Space m) r).indicator (fun _ => c) z)) =ᵐ[volume]
      D.indicator (fun z => K z*c) := by
    filter_upwards [ae_norm_ne hr.ne'] with z hz
    by_cases hzr : ‖z‖ < r
    · have hzs : ‖z‖ < s := hzr.trans_le hrs
      have hn : z ∉ D := by dsimp [D]; simp only [mem_ofPred_eq, not_and]; intro h; linarith
      simp [mem_ball_zero_iff, hzr, hzs, hn]
    · have hrz : r < ‖z‖ := lt_of_le_of_ne (not_lt.mp hzr) (Ne.symm hz)
      by_cases hzs : ‖z‖ < s
      · have hzd : z ∈ D := ⟨hrz, hzs⟩
        simp [mem_ball_zero_iff, hzr, hzs, hzd]
      · have hn : z ∉ D := by intro h; exact hzs h.2
        simp [mem_ball_zero_iff, hzr, hzs, hn]
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_indicator hD, integral_mul_const, hcancel r s hr, zero_mul]

lemma change_compensation_radius {K g : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hcancel : ∀ ε R : ℝ, 0 < ε →
      (∫ z in {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0)
    (x : Space m) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (compensatedIntegrand K g x) volume) :
    Integrable (fun z => K z*(g (x-z)-(ball (0 : Space m) r).indicator (fun _ => g x) z)) volume ∧
    (∫ z, K z*(g (x-z)-(ball (0 : Space m) r).indicator (fun _ => g x) z)) =
      ∫ z, compensatedIntegrand K g x z := by
  let D := fun z => K z*((ball (0 : Space m) 1).indicator (fun _ => g x) z -
    (ball (0 : Space m) r).indicator (fun _ => g x) z)
  have hD : Integrable D volume ∧ (∫ z, D z) = 0 := by
    by_cases h : r ≤ 1
    · exact indicator_radius_difference hK hcancel (g x) hr h
    · have ht := indicator_radius_difference hK hcancel (g x) (by norm_num : (0:ℝ)<1) (le_of_not_ge h)
      have he : D = fun z => -(K z*((ball (0 : Space m) r).indicator (fun _ => g x) z -
          (ball (0 : Space m) 1).indicator (fun _ => g x) z)) := by
        funext z; dsimp [D]; ring
      rw [he]
      refine ⟨ht.1.neg, ?_⟩
      rw [integral_neg, ht.2, neg_zero]
  have he : (fun z => K z*(g (x-z)-(ball (0 : Space m) r).indicator (fun _ => g x) z)) =
      fun z => compensatedIntegrand K g x z + D z := by
    funext z; dsimp [compensatedIntegrand, D]; ring
  rw [he]
  exact ⟨hi.add hD.1, by rw [integral_add hi hD.1, hD.2, add_zero]⟩

lemma integral_near_add_truncated {K g : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hcancel : ∀ ε R : ℝ, 0 < ε →
      (∫ z in {z : Space m | ε < ‖z‖ ∧ ‖z‖ < R}, K z) = 0)
    (x : Space m) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (compensatedIntegrand K g x) volume) :
    (∫ z, compensatedIntegrand K g x z) =
      (∫ z in ball (0 : Space m) r, K z*(g (x-z)-g x)) + truncated K g r x := by
  let F := fun z => K z*(g (x-z)-(ball (0 : Space m) r).indicator (fun _ => g x) z)
  have hF := change_compensation_radius hK hcancel x hr hi
  change Integrable F volume ∧ (∫ z, F z) = _ at hF
  rw [← hF.2, ← integral_add_compl measurableSet_ball hF.1]
  congr 1
  · apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    simp [F, hz]
  · rw [truncated_eq_reflected]
    have hset : (ball (0 : Space m) r)ᶜ =ᵐ[volume] {z : Space m | r < ‖z‖} := by
      filter_upwards [ae_norm_ne hr.ne'] with z hz
      simp only [mem_compl_iff, mem_ball, dist_zero_right, mem_ofPred_eq]
      exact propext ⟨fun h => lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz), fun h => not_lt.mpr h.le⟩
    rw [setIntegral_congr_set hset]
    apply setIntegral_congr_fun (by measurability)
    intro z hz
    have hb : z ∉ ball (0 : Space m) r := by simp; exact hz.le
    simp [F, hb]

lemma truncated_eq_annular_kernel (K g : Space m → 𝕜) (x : Space m) (r R : ℝ)
    (hsupp : ∀ z : Space m, R ≤ ‖z‖ → g (x-z) = 0) :
    truncated K g r x = ∫ z,
      {z : Space m | r < ‖z‖ ∧ ‖z‖ < R}.indicator K z * g (x-z) := by
  rw [truncated_eq_reflected, ← integral_indicator (by measurability :
    MeasurableSet {z : Space m | r < ‖z‖})]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases hr : r < ‖z‖
  · by_cases hR : ‖z‖ < R
    · simp [hr, hR]
    · simp [hr, hR, hsupp z (not_lt.mp hR)]
  · have hD : z ∉ {z : Space m | r < ‖z‖ ∧ ‖z‖ < R} := by simp [hr]
    simp [hr, hD]

lemma principalValue_eq_near_annular (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) {K g : Space m → 𝕜} (hK : KernelHypotheses K)
    (hgc : HasCompactSupport g) (hg : IsHolder α g)
    (x : Space m) {r R : ℝ} (hr : 0 < r)
    (hsupp : ∀ z : Space m, R ≤ ‖z‖ → g (x-z) = 0) :
    principalValue K g x =
      (∫ z in ball (0 : Space m) r, K z*(g (x-z)-g x)) +
      ∫ z, {z : Space m | r < ‖z‖ ∧ ‖z‖ < R}.indicator K z * g (x-z) := by
  rw [(principalValueExists hm α hα hα1 K g hK hgc hg x).2.2.2]
  rw [integral_near_add_truncated hK.smooth.continuousOn
    (fun ε R hε => annular_cancellation hm hK ε R) x hr
    (compensated_integrable hm hα hK hgc hg x)]
  rw [truncated_eq_annular_kernel K g x r R hsupp]

lemma exists_outer_cutoff {E F : Type*} [NormedAddCommGroup E] [Zero F]
    {g : E → F} (hgc : HasCompactSupport g) (x y : E) (T : ℝ) :
    ∃ R : ℝ, 0 < R ∧ T ≤ R ∧
      (∀ z : E, R ≤ ‖z‖ → g (x-z) = 0) ∧
      (∀ z : E, R ≤ ‖z‖ → g (y-z) = 0) := by
  obtain ⟨C, hC, hsupp⟩ := hgc.isBounded.exists_pos_norm_le
  refine ⟨max T (‖x‖+‖y‖+C+1), ?_, le_max_left _ _, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith [norm_nonneg x, norm_nonneg y]) (le_max_right _ _)
  · intro z hz
    by_contra hne
    have hc := hsupp (x-z) (subset_closure (show x-z ∈ Function.support g from hne))
    have hn : ‖z‖ ≤ ‖x‖+C := by
      calc
        ‖z‖ = ‖x-(x-z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖+‖x-z‖ := norm_sub_le _ _
        _ ≤ ‖x‖+C := by linarith
    have hh := le_max_right T (‖x‖+‖y‖+C+1)
    linarith [norm_nonneg y]
  · intro z hz
    by_contra hne
    have hc := hsupp (y-z) (subset_closure (show y-z ∈ Function.support g from hne))
    have hn : ‖z‖ ≤ ‖y‖+C := by
      calc
        ‖z‖ = ‖y-(y-z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y‖+‖y-z‖ := norm_sub_le _ _
        _ ≤ ‖y‖+C := by linarith
    have hh := le_max_right T (‖x‖+‖y‖+C+1)
    linarith [norm_nonneg x]


/-- The scalar radial majorant used in the local estimate is integrable. -/
lemma radial_majorant_integrable (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) (r : ℝ) :
    IntegrableOn (fun z : Space m => ‖z‖ ^ (α - (m : ℝ))) (ball 0 r) volume := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simpa [P201Specs.Space] using hm : 1 ≤ Module.finrank ℝ (Space m))
    (α := (m : ℝ) - α) (C := 1)
    (by simpa [P201Specs.Space] using sub_lt_self (m : ℝ) hα)
  · exact Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        one_mul, neg_sub]
      exact le_rfl
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma local_compensated_norm_bound {α A M H : ℝ}
    {K g : Space m → 𝕜}
    (hsize : ∀ z : Space m, z ≠ 0 → ‖K z‖ ≤ A / ‖z‖ ^ m)
    (hg : HolderBounds α g M H) (x : Space m) {z : Space m} (hz : z ≠ 0) :
    ‖K z * (g (x - z) - g x)‖ ≤ A * H * ‖z‖ ^ (α - (m : ℝ)) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hl : ‖g (x - z) - g x‖ ≤ H * ‖z‖ ^ α := by
    simpa [dist_eq_norm, sub_sub_cancel_left] using hg.2.2.2 (x - z) x
  calc
    _ = ‖K z‖ * ‖g (x - z) - g x‖ := norm_mul _ _
    _ ≤ (A / ‖z‖ ^ m) * (H * ‖z‖ ^ α) :=
      mul_le_mul (hsize z hz) hl (norm_nonneg _) (norm_nonneg _ |>.trans (hsize z hz))
    _ = _ := by
      rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp.le,
        sub_eq_add_neg, Real.rpow_add hp]
      ring

lemma local_compensated_integrable (hm : 1 ≤ m) {α A M H : ℝ} (hα : 0 < α)
    {K g : Space m → 𝕜}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hsize : ∀ z : Space m, z ≠ 0 → ‖K z‖ ≤ A / ‖z‖ ^ m)
    (hg : HolderBounds α g M H) (x : Space m) (r : ℝ) :
    IntegrableOn (fun z : Space m => K z * (g (x - z) - g x)) (ball 0 r) volume := by
  let : NeZero m := ⟨by omega⟩
  have hcont := holder_continuous hα (g := g) ⟨M, H, hg⟩
  have hmeas : AEStronglyMeasurable (fun z : Space m => K z * (g (x - z) - g x)) volume :=
    ((measurable_of_continuousOn_compl_singleton 0 hK).mul
      ((hcont.comp (continuous_const.sub continuous_id)).measurable.sub
        measurable_const)).aestronglyMeasurable
  apply ((radial_majorant_integrable hm hα r).const_mul (A * H)).mono' hmeas.restrict
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Space m))] with z hz
  exact local_compensated_norm_bound hsize hg x hz

lemma local_compensated_integral_bound (hm : 1 ≤ m) {α A M H : ℝ} (hα : 0 < α)
    {K g : Space m → 𝕜}
    (hsize : ∀ z : Space m, z ≠ 0 → ‖K z‖ ≤ A / ‖z‖ ^ m)
    (hg : HolderBounds α g M H) (x : Space m) {r : ℝ} (hr : 0 < r) :
    ‖∫ z in ball (0 : Space m) r, K z * (g (x - z) - g x)‖ ≤
      A * H * (∫ z in ball (0 : Space m) 1, ‖z‖ ^ (α - (m : ℝ))) * r ^ α := by
  let : NeZero m := ⟨by omega⟩
  have hi := (radial_majorant_integrable hm hα r).const_mul (A * H)
  calc
    _ ≤ ∫ z in ball (0 : Space m) r, A * H * ‖z‖ ^ (α - (m : ℝ)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Space m))] with z hz
      exact local_compensated_norm_bound hsize hg x hz
    _ = _ := by
      rw [integral_const_mul, radial_ball_scale _ hr]
      simp only [P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin, sub_add_cancel]
      ring


lemma far_bulk_norm_bound {α D M H : ℝ} {K g : Space m → 𝕜}
    (hg : HolderBounds α g M H) (x h : Space m) {z : Space m} (hz : z ≠ 0)
    (hdiff : ‖K (z + h) - K z‖ ≤ D * ‖h‖ / ‖z‖ ^ (m + 1)) :
    ‖(K (z + h) - K z) * (g (x - z) - g x)‖ ≤
      D * H * ‖h‖ * ‖z‖ ^ (α - (m : ℝ) - 1) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hl : ‖g (x - z) - g x‖ ≤ H * ‖z‖ ^ α := by
    simpa [dist_eq_norm, sub_sub_cancel_left] using hg.2.2.2 (x - z) x
  calc
    _ = ‖K (z + h) - K z‖ * ‖g (x - z) - g x‖ := norm_mul _ _
    _ ≤ (D * ‖h‖ / ‖z‖ ^ (m + 1)) * (H * ‖z‖ ^ α) :=
      mul_le_mul hdiff hl (norm_nonneg _) (norm_nonneg _ |>.trans hdiff)
    _ = _ := by
      rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp.le]
      rw [show α - (m : ℝ) - 1 = -(↑(m + 1) : ℝ) + α by push_cast; ring,
        Real.rpow_add hp]
      ring

lemma tail_majorant_integrable (hm : 1 ≤ m) {α r : ℝ} (hα1 : α < 1) (hr : 0 < r) :
    IntegrableOn (fun z : Space m => ‖z‖ ^ (α - (m : ℝ) - 1)) {z : Space m | r < ‖z‖} volume := by
  let : NeZero m := ⟨by omega⟩
  apply radial_exterior_integrable (E := Space m) _ hr
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  linarith

lemma far_bulk_integral_bound (hm : 1 ≤ m) {α D M H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K g : Space m → 𝕜} (hK : ContinuousOn K ({0}ᶜ : Set (Space m)))
    (hg : HolderBounds α g M H) (x h : Space m) {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ z : Space m, r < ‖z‖ → ‖K (z + h) - K z‖ ≤ D * ‖h‖ / ‖z‖ ^ (m + 1)) :
    IntegrableOn (fun z => (K (z + h) - K z) * (g (x - z) - g x))
      {z : Space m | r < ‖z‖} volume ∧
    ‖∫ z in {z : Space m | r < ‖z‖}, (K (z + h) - K z) * (g (x - z) - g x)‖ ≤
      D * H * ‖h‖ * (∫ z in {z : Space m | 1 < ‖z‖}, ‖z‖ ^ (α - (m : ℝ) - 1)) * r ^ (α - 1) := by
  let : NeZero m := ⟨by omega⟩
  have hcont := holder_continuous hα (g := g) ⟨M, H, hg⟩
  have hKm := measurable_of_continuousOn_compl_singleton 0 hK
  have hmeas : AEStronglyMeasurable (fun z : Space m =>
      (K (z + h) - K z) * (g (x - z) - g x)) volume :=
    ((hKm.comp (measurable_id.add measurable_const)).sub hKm |>.mul
      ((hcont.comp (continuous_const.sub continuous_id)).measurable.sub
        measurable_const)).aestronglyMeasurable
  have hi := (tail_majorant_integrable hm hα1 hr).const_mul (D * H * ‖h‖)
  have hb : ∀ᵐ z ∂volume.restrict {z : Space m | r < ‖z‖},
      ‖(K (z + h) - K z) * (g (x - z) - g x)‖ ≤ D * H * ‖h‖ * ‖z‖ ^ (α - (m : ℝ) - 1) := by
    filter_upwards [ae_restrict_mem (by measurability : MeasurableSet {z : Space m | r < ‖z‖})] with z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz)
    exact far_bulk_norm_bound hg x h hz0 (hdiff z hz)
  refine ⟨hi.mono' hmeas.restrict hb, ?_⟩
  calc
    _ ≤ ∫ z in {z : Space m | r < ‖z‖}, D * H * ‖h‖ * ‖z‖ ^ (α - (m : ℝ) - 1) :=
      norm_integral_le_of_norm_le hi hb
    _ = _ := by
      rw [integral_const_mul, radial_exterior_scale _ hr]
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      rw [show α - (m : ℝ) - 1 + m = α - 1 by ring]
      ring

lemma compensated_norm_bound {α A M H : ℝ} (hA : 0 ≤ A)
    {K g : Space m → 𝕜} (hK : KernelHypotheses K)
    (hsize : ∀ u : Space m, ‖u‖ = 1 → ‖K u‖ ≤ A)
    (hg : HolderBounds α g M H) (x : Space m) {z : Space m} (hz : z ≠ 0) :
    ‖compensatedIntegrand K g x z‖ ≤
      (ball (0 : Space m) 1).indicator
        (fun z => (A * H) * ‖z‖ ^ (α - (m : ℝ))) z + A * ‖g (x - z)‖ := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases hb : z ∈ ball (0 : Space m) 1
  · rw [compensatedIntegrand, indicator_of_mem hb, indicator_of_mem hb]
    have hl : ‖g (x - z) - g x‖ ≤ H * ‖z‖ ^ α := by
      simpa [dist_eq_norm, sub_sub_cancel_left] using hg.2.2.2 (x - z) x
    have hprod : ‖K z * (g (x - z) - g x)‖ ≤ A * H * ‖z‖ ^ (α - (m : ℝ)) := by
      calc
        _ = ‖K z‖ * ‖g (x - z) - g x‖ := norm_mul _ _
        _ ≤ (A / ‖z‖ ^ m) * (H * ‖z‖ ^ α) :=
          mul_le_mul (size_of_sphere_bound hK hsize hz) hl (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hp.le,
            sub_eq_add_neg, Real.rpow_add hp]
          ring
    exact hprod.trans (le_add_of_nonneg_right (mul_nonneg hA (norm_nonneg _)))
  · rw [compensatedIntegrand, indicator_of_notMem hb, sub_zero, norm_mul,
      indicator_of_notMem hb, zero_add]
    have hnorm : 1 ≤ ‖z‖ := by simpa using hb
    have hk : ‖K z‖ ≤ A := (size_of_sphere_bound hK hsize hz).trans
      (div_le_self hA (one_le_pow₀ hnorm))
    exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)

lemma principalValue_seminorm_of_far {m : ℕ} (hm : 1 ≤ m)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfar : ∃ Cfar : ℝ, 0 ≤ Cfar ∧
      ∀ {𝕜 : Type} [RCLike 𝕜] (K g : Space m → 𝕜) (M H : ℝ),
        KernelHypotheses K → SphereBounds K A B → HasCompactSupport g →
        HolderBounds α g M H → ∀ (x h : Space m) (R : ℝ), h ≠ 0 → 4*‖h‖ ≤ R →
        ‖∫ z, (annularCutoff K (2*‖h‖) R z - annularCutoff K (2*‖h‖) R (z+h)) *
          (g (x-z)-g x)‖ ≤ Cfar*H*‖h‖^α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {𝕜 : Type} [RCLike 𝕜] (K g : Space m → 𝕜) (M H : ℝ),
        KernelHypotheses K → SphereBounds K A B → HasCompactSupport g →
        HolderBounds α g M H → ∀ x y : Space m,
          ‖principalValue K g x-principalValue K g y‖ ≤ C*H*dist x y^α := by
  obtain ⟨Cfar, hCfar, hfar⟩ := hfar
  let J := ∫ z : Space m in ball 0 1, ‖z‖^(α-(m:ℝ))
  let C := 2*(A*J*(2:ℝ)^α)+Cfar
  have hJ : 0 ≤ J := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ K g M H hK hKB hgc hg x y
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow hα.ne']
  let h := y-x
  have hh0 : h ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hh : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  have hr : 0 < 2*‖h‖ := by positivity
  obtain ⟨R, hR, h4R, hsx, hsy⟩ := exists_outer_cutoff hgc x y (4*‖h‖)
  let L := annularCutoff K (2*‖h‖) R
  let Nx := ∫ z in ball (0 : Space m) (2*‖h‖), K z*(g (x-z)-g x)
  let Ny := ∫ z in ball (0 : Space m) (2*‖h‖), K z*(g (y-z)-g y)
  let Fx := ∫ z, L z*g (x-z)
  let Fy := ∫ z, L z*g (y-z)
  have hx : principalValue K g x = Nx+Fx := by
    simpa only [Nx, Fx, L, annularCutoff_eq_indicator] using
      principalValue_eq_near_annular hm hα hα1 hK hgc ⟨M,H,hg⟩ x hr hsx
  have hy : principalValue K g y = Ny+Fy := by
    simpa only [Ny, Fy, L, annularCutoff_eq_indicator] using
      principalValue_eq_near_annular hm hα hα1 hK hgc ⟨M,H,hg⟩ y hr hsy
  have hL : Integrable L volume := by
    have hi := (annular_integrable hK.smooth.continuousOn hr R).integrable_indicator
      (by measurability : MeasurableSet {z : Space m | 2*‖h‖ < ‖z‖ ∧ ‖z‖ < R})
    exact hi.congr (ae_of_all _ fun z => by simp [L, annularCutoff, indicator])
  have hmeas : AEStronglyMeasurable g volume := (holder_continuous hα (g := g) ⟨M,H,hg⟩).aestronglyMeasurable
  have hdiff : Fx-Fy = ∫ z, (L z-L (z+h))*(g (x-z)-g x) :=
    finite_kernel_translation_identity hL hmeas hg.2.2.1 x y
  have hfarbound : ‖Fx-Fy‖ ≤ Cfar*H*‖h‖^α := by
    rw [hdiff]
    exact hfar K g M H hK hKB hgc hg x h R hh0 h4R
  have hsize : ∀ z : Space m, z ≠ 0 → ‖K z‖ ≤ A/‖z‖^m :=
    fun z hz => size_of_sphere_bound hK (fun u hu => (hKB.2.2 u hu).1) hz
  have hnx : ‖Nx‖ ≤ (A*J*(2:ℝ)^α)*H*‖h‖^α := by
    calc
      _ ≤ A*H*J*(2*‖h‖)^α := local_compensated_integral_bound hm hα hsize hg x hr
      _ = _ := normalized_near_majorant_eq α A H J 2 (by norm_num) hh
  have hny : ‖Ny‖ ≤ (A*J*(2:ℝ)^α)*H*‖h‖^α := by
    calc
      _ ≤ A*H*J*(2*‖h‖)^α := local_compensated_integral_bound hm hα hsize hg y hr
      _ = _ := normalized_near_majorant_eq α A H J 2 (by norm_num) hh
  have hdist : dist x y = ‖h‖ := by simp [h, dist_eq_norm, norm_sub_rev]
  rw [hx, hy, hdist]
  calc
    _ = ‖(Nx-Ny)+(Fx-Fy)‖ := by congr 1; ring
    _ ≤ ‖Nx-Ny‖+‖Fx-Fy‖ := norm_add_le _ _
    _ ≤ (‖Nx‖+‖Ny‖)+‖Fx-Fy‖ := add_le_add (norm_sub_le Nx Ny) le_rfl
    _ ≤ ((A*J*(2:ℝ)^α)*H*‖h‖^α+(A*J*(2:ℝ)^α)*H*‖h‖^α)+Cfar*H*‖h‖^α :=
      add_le_add (add_le_add hnx hny) hfarbound
    _ = _ := by dsimp [C]; ring

theorem principalValueSeminorm : P201Specs.Elliptic.HolderCancellation.principalValueSeminormStatement := by
  intro m hm α hα hα1 A B hA hB
  apply principalValue_seminorm_of_far hm α hα hα1 A B hA hB
  let : NeZero m := ⟨by omega⟩
  obtain ⟨Cfar, hCfar, hfar⟩ := annular_difference_integral_bound (E := Space m) hα hα1 hA hB
  refine ⟨Cfar, hCfar, ?_⟩
  intro 𝕜 _ K g M H hK hKB hgc hg x h R hh hR
  apply hfar K g H hg.2.1 (hK.smooth.of_le (by simp)) _ _ hg.2.2.2 x h hh R hR
  · intro z hz
    simpa only [P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin] using
      size_of_sphere_bound hK (fun u hu => (hKB.2.2 u hu).1) hz
  · intro z hz
    simpa only [P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin] using
      derivative_of_sphere_bound hK (fun u hu => (hKB.2.2 u hu).2) hz


/-- Uniform supremum control, retaining the L¹ input term until a support ball
is prescribed. The local moment depends only on m and α. -/
lemma principalValue_supremum_bound (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K g : Space m → 𝕜}
    (hK : KernelHypotheses K) (hgc : HasCompactSupport g)
    {A M H : ℝ} (hA : 0 ≤ A)
    (hsize : ∀ u : Space m, ‖u‖ = 1 → ‖K u‖ ≤ A)
    (hg : HolderBounds α g M H) (x : Space m) :
    ‖principalValue K g x‖ ≤
      (A * H) * (∫ z : Space m in ball 0 1, ‖z‖ ^ (α - (m : ℝ))) +
        A * ∫ z : Space m, ‖g z‖ := by
  let : NeZero m := ⟨by omega⟩
  have hcont := holder_continuous hα (g := g) ⟨M, H, hg⟩
  have hgi : Integrable g volume := hcont.integrable_of_hasCompactSupport hgc
  have hni0 : IntegrableOn (fun z : Space m => (A * H) * ‖z‖ ^ (α - (m : ℝ)))
      (ball 0 1) volume := (radial_majorant_integrable hm hα 1).const_mul (A * H)
  have hni := hni0.integrable_indicator measurableSet_ball
  have hti := (hgi.comp_sub_left x).norm.const_mul A
  rw [(principalValueExists hm α hα hα1 K g hK hgc ⟨M, H, hg⟩ x).2.2.2]
  calc
    _ ≤ ∫ z : Space m,
        (ball (0 : Space m) 1).indicator
          (fun z => (A * H) * ‖z‖ ^ (α - (m : ℝ))) z + A * ‖g (x - z)‖ := by
      apply norm_integral_le_of_norm_le (hni.add hti)
      filter_upwards [volume.ae_ne (0 : Space m)] with z hz
      exact compensated_norm_bound hA hK hsize hg x hz
    _ = _ := by
      rw [integral_add hni hti, integral_indicator measurableSet_ball,
        integral_const_mul, integral_const_mul]
      congr 1
      congr 1
      exact (volume.measurePreserving_sub_left x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding (fun z : Space m => ‖g z‖)

lemma input_integral_norm_bound {g : Space m → 𝕜} {M : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) {a : Space m} {R : ℝ}
    (hsupp : tsupport g ⊆ closedBall a R) :
    (∫ z : Space m, ‖g z‖) ≤ M * volume.real (closedBall a R) := by
  have he : (∫ z in closedBall a R, ‖g z‖) = ∫ z : Space m, ‖g z‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsupp h)), norm_zero]
  rw [← he]
  have hn : 0 ≤ ∫ z in closedBall a R, ‖g z‖ := integral_nonneg fun _ => norm_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using
    (norm_setIntegral_le_of_norm_le_const (f := fun z : Space m => ‖g z‖)
      (measure_closedBall_lt_top (μ := (volume : Measure (Space m))) (x := a) (r := R))
      (fun z _ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hM z))

private lemma quotient_set_nonempty (hm : 1 ≤ m) (α : ℝ) (g : Space m → 𝕜) :
    {q : ℝ | ∃ x y : Space m, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α}.Nonempty := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Space m)
  exact ⟨_, 0, y, hy.symm, rfl⟩

private lemma quotient_set_bddAbove {α M H : ℝ} {g : Space m → 𝕜}
    (hg : HolderBounds α g M H) :
    BddAbove {q : ℝ | ∃ x y : Space m, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α} := by
  refine ⟨H, ?_⟩
  rintro q ⟨x, y, hxy, rfl⟩
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hg.2.2.2 x y)

/-- For a bounded Hölder function these are the actual finite suprema, so the
source norm is bounded by any separately supplied supremum and seminorm bounds. -/
lemma holderNorm_le (hm : 1 ≤ m) {α M H : ℝ} {g : Space m → 𝕜}
    (hg : HolderBounds α g M H) : holderNorm α g ≤ M + H := by
  unfold holderNorm
  apply add_le_add
  · exact csSup_le (Set.range_nonempty (fun x : Space m => ‖g x‖))
      (by rintro _ ⟨x, rfl⟩; exact hg.2.2.1 x)
  · apply csSup_le (quotient_set_nonempty hm α g)
    rintro q ⟨x, y, hxy, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hg.2.2.2 x y)

/-- Conversely, the ordinary sum norm controls both defining quantities. -/
lemma bounds_by_holderNorm (hm : 1 ≤ m) {α : ℝ} {g : Space m → 𝕜}
    (hg : IsHolder α g) : HolderBounds α g (holderNorm α g) (holderNorm α g) := by
  obtain ⟨M, H, hg⟩ := hg
  let S : Set ℝ := Set.range (fun x : Space m => ‖g x‖)
  let Q : Set ℝ := {q : ℝ | ∃ x y : Space m, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α}
  have hS : BddAbove S := ⟨M, by rintro _ ⟨x, rfl⟩; exact hg.2.2.1 x⟩
  have hQ : BddAbove Q := quotient_set_bddAbove hg
  have hS0 : 0 ≤ sSup S := (norm_nonneg (g 0)).trans (le_csSup hS ⟨0, rfl⟩)
  have hQ0 : 0 ≤ sSup Q := by
    obtain ⟨q, x, y, hxy, rfl⟩ := quotient_set_nonempty hm α g
    exact (div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)).trans
      (le_csSup hQ ⟨x, y, hxy, rfl⟩)
  have hN0 : 0 ≤ holderNorm α g := add_nonneg hS0 hQ0
  refine ⟨hN0, hN0, ?_, ?_⟩
  · intro x
    exact (le_csSup hS ⟨x, rfl⟩).trans (le_add_of_nonneg_right hQ0)
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, dist_self]
      exact mul_nonneg hN0 (Real.rpow_nonneg (by norm_num) _)
    · have hp : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
      have hq : ‖g x - g y‖ / dist x y ^ α ≤ sSup Q := le_csSup hQ ⟨x, y, hxy, rfl⟩
      apply (div_le_iff₀ hp).mp
      exact hq.trans (le_add_of_nonneg_left hS0)

/-- The uniform seminorm estimate and the support-dependent supremum bound
control the manuscript's ordinary Hölder norm. -/
lemma quantitativeHolder_of_sourceSeminorm
    (hestimate : P201Specs.Elliptic.HolderCancellation.principalValueSeminormStatement) :
    P201Specs.Elliptic.HolderCancellation.quantitativeHolderStatement := by
  intro m hm 𝕜 _ α hα hα1 a R A B hR hA hB
  obtain ⟨C, hC, hestimate⟩ := hestimate hm α hα hα1 A B hA hB
  let J : ℝ := ∫ z : Space m in ball 0 1, ‖z‖ ^ (α - (m : ℝ))
  let V : ℝ := volume.real (closedBall a R)
  let D : ℝ := A * J + A * V
  have hJ : 0 ≤ J := integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg _) _)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := add_nonneg (mul_nonneg hA hJ) (mul_nonneg hA hV)
  refine ⟨D + C, add_nonneg hD hC, ?_⟩
  intro K g hK hKB hgc hsupp hg
  let N := holderNorm α g
  have hgb : HolderBounds α g N N := bounds_by_holderNorm hm hg
  have hsize := fun u hu => (hKB.2.2 u hu).1
  have hderiv := fun u hu => (hKB.2.2 u hu).2
  have hsup (x : Space m) : ‖principalValue K g x‖ ≤ D * N := by
    calc
      _ ≤ (A * N) * J + A * ∫ z : Space m, ‖g z‖ :=
        principalValue_supremum_bound hm hα hα1 hK hgc hA hsize hgb x
      _ ≤ (A * N) * J + A * (N * V) := by
        gcongr
        exact input_integral_norm_bound hgb.2.2.1 hsupp
      _ = D * N := by dsimp [D]; ring
  have hhol (x y : Space m) :
      ‖principalValue K g x - principalValue K g y‖ ≤ (C * N) * dist x y ^ α := by
    exact hestimate K g N N hK hKB hgc hgb x y
  have houtput : HolderBounds α (principalValue K g) (D * N) (C * N) :=
    ⟨mul_nonneg hD hgb.1, mul_nonneg hC hgb.1, hsup, hhol⟩
  refine ⟨⟨D * N, C * N, houtput⟩, ?_⟩
  calc
    _ ≤ D * N + C * N := holderNorm_le hm houtput
    _ = _ := by change D * N + C * N = (D + C) * N; ring


lemma sphere_bounds_exist {K : Space m → 𝕜} (hK : KernelHypotheses K) :
    ∃ A B : ℝ, SphereBounds K A B := by
  have hsub : sphere (0 : Space m) 1 ⊆ ({0}ᶜ : Set (Space m)) := by
    intro z hz
    change z ≠ 0
    intro he
    simp [he] at hz
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : Space m) 1).exists_bound_of_continuousOn
    (hK.smooth.continuousOn.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Space m) 1).exists_bound_of_continuousOn
    ((hK.smooth.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by simp)).mono hsub)
  refine ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro z hz
  have hzs : z ∈ sphere (0 : Space m) 1 := mem_sphere_zero_iff_norm.mpr hz
  exact ⟨(hA z hzs).trans (le_max_left _ _), (hB z hzs).trans (le_max_left _ _)⟩

lemma globalHolder_of_quantitativeHolder
    (hestimate : P201Specs.Elliptic.HolderCancellation.quantitativeHolderStatement) :
    P201Specs.Elliptic.HolderCancellation.globalHolderStatement := by
  intro m hm 𝕜 _ α hα hα1 K g hK hgc hg
  obtain ⟨R, hR, hsupp⟩ := hgc.isBounded.exists_pos_norm_le
  obtain ⟨A, B, hKB⟩ := sphere_bounds_exist hK
  obtain ⟨C, _, hC⟩ := hestimate (𝕜 := 𝕜) hm α hα hα1
    (0 : Space m) R A B hR hKB.1 hKB.2.1
  exact (hC K g hK hKB hgc (fun z hz => by simpa using hsupp z hz) hg).1

theorem quantitativeHolder :
    P201Specs.Elliptic.HolderCancellation.quantitativeHolderStatement :=
  quantitativeHolder_of_sourceSeminorm principalValueSeminorm

theorem globalHolder : P201Specs.Elliptic.HolderCancellation.globalHolderStatement :=
  globalHolder_of_quantitativeHolder quantitativeHolder

end P201.Elliptic.HolderCancellation
