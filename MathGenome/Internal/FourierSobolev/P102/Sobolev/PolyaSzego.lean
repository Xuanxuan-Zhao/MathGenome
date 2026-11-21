import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.PolyaSzego
import MathGenome.Internal.FourierSobolev.P102.Sobolev.Polarization
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.Rat.Encodable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SupportedCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorLpReflexive
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev
open P102.U4 Polarization Rearrangement

namespace Polarization.Halfspace

theorem reflection_formula {d : ℕ} (H : Halfspace d) (x : Space d) :
    H.reflection x = x + (2 * (H.offset - inner ℝ H.normal x)) • H.normal :=
  H.reflection_apply x

theorem reflection_involutive {d : ℕ} (H : Halfspace d) :
    Function.Involutive H.reflection :=
  H.reflection_reflection

theorem reflection_norm_gt {d : ℕ} (H : Halfspace d) {x : Space d}
    (hx : x ∈ H.nearSide) : ‖x‖ < ‖H.reflection x‖ := by
  have hs := reflection_norm_sq H x
  have hpos : 0 < 4 * H.offset * (H.offset - inner ℝ H.normal x) :=
    mul_pos (mul_pos (by norm_num) H.offset_pos) (sub_pos.mpr hx)
  nlinarith [norm_nonneg x, norm_nonneg (H.reflection x)]

theorem gaussian_reflection_lt {d : ℕ} (H : Halfspace d) {x : Space d}
    (hx : x ∈ H.nearSide) :
    Real.exp (-‖H.reflection x‖ ^ 2) < Real.exp (-‖x‖ ^ 2) := by
  apply Real.exp_lt_exp.mpr
  have hs := reflection_norm_sq H x
  have hpos : 0 < 4 * H.offset * (H.offset - inner ℝ H.normal x) :=
    mul_pos (mul_pos (by norm_num) H.offset_pos) (sub_pos.mpr hx)
  linarith

theorem nearSide_measurableSet {d : ℕ} (H : Halfspace d) :
    MeasurableSet H.nearSide :=
  (isOpen_lt (continuous_const.inner continuous_id) continuous_const).measurableSet

def reflectionIsometryEquiv {d : ℕ} (H : Halfspace d) : Space d ≃ᵢ Space d where
  toEquiv := H.reflection_involutive.toPerm
  isometry_toFun := H.reflection_isometry

@[simp] theorem reflectionIsometryEquiv_apply {d : ℕ} (H : Halfspace d) (x : Space d) :
    H.reflectionIsometryEquiv x = H.reflection x := rfl

theorem reflection_preimage_closedBall {d : ℕ} (H : Halfspace d) (x : Space d) (r : ℝ) :
    H.reflection ⁻¹' Metric.closedBall (H.reflection x) r = Metric.closedBall x r :=
  H.reflection_isometry.preimage_closedBall x r

theorem reflection_image_closedBall {d : ℕ} (H : Halfspace d) (x : Space d) (r : ℝ) :
    H.reflection '' Metric.closedBall x r = Metric.closedBall (H.reflection x) r :=
  H.reflectionIsometryEquiv.image_closedBall x r

theorem nearSide_isOpen {d : ℕ} (H : Halfspace d) : IsOpen H.nearSide :=
  isOpen_lt (continuous_const.inner continuous_id) continuous_const

/-- Any two points at strictly increasing distance from the origin are paired
by an allowed polarization plane, with the nearer point in its open near side. -/
theorem exists_reflection_pair {d : ℕ} (x y : Space d) (hxy : ‖x‖ < ‖y‖) :
    ∃ H : Halfspace d, H.reflection x = y ∧ x ∈ H.nearSide := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (by intro h; subst y; exact lt_irrefl _ hxy)
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr hyx
  let e : Space d := ‖y - x‖⁻¹ • (y - x)
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hi : inner ℝ e x + inner ℝ e y = ‖y - x‖⁻¹ * (‖y‖ ^ 2 - ‖x‖ ^ 2) := by
    simp only [e, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq,
      real_inner_comm y x]
    ring
  have hc : 0 < (inner ℝ e x + inner ℝ e y) / 2 := by
    rw [hi]
    apply div_pos _ (by norm_num)
    apply mul_pos (inv_pos.mpr hn)
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hd : inner ℝ e y - inner ℝ e x = ‖y - x‖ := by
    rw [← inner_sub_right]
    dsimp [e]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  let H : Halfspace d := ⟨e, he, (inner ℝ e x + inner ℝ e y) / 2, hc⟩
  refine ⟨H, ?_, ?_⟩
  · rw [reflection_formula]
    change x + (2 * ((inner ℝ e x + inner ℝ e y) / 2 - inner ℝ e x)) • e = y
    have hcoef : 2 * ((inner ℝ e x + inner ℝ e y) / 2 - inner ℝ e x) = ‖y - x‖ := by
      linarith
    rw [hcoef]
    dsimp [e]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    abel
  · change inner ℝ e x < (inner ℝ e x + inner ℝ e y) / 2
    linarith

end Polarization.Halfspace

namespace Polarization.Halfspace

theorem reflection_mem_nearSide_iff {d : ℕ} (H : Halfspace d) (x : Space d) :
    H.reflection x ∈ H.nearSide ↔ H.offset < inner ℝ H.normal x := by
  change inner ℝ H.normal (H.reflection x) < H.offset ↔ _
  rw [inner_reflection]
  constructor <;> intro h <;> linarith

theorem reflection_fixed_of_boundary {d : ℕ} (H : Halfspace d) {x : Space d}
    (hx : inner ℝ H.normal x = H.offset) : H.reflection x = x := by
  rw [reflection_formula, hx, sub_self, mul_zero, zero_smul, add_zero]

theorem polarize_reflection_of_nearSide {d : ℕ} (H : Halfspace d)
    (g : Space d → ℝ) {x : Space d} (hx : x ∈ H.nearSide) :
    H.polarize g (H.reflection x) = min (g x) (g (H.reflection x)) := by
  have hr : H.reflection x ∉ H.nearSide := by
    rw [reflection_mem_nearSide_iff]
    exact not_lt.mpr (le_of_lt hx)
  simp only [polarize, ite_eq_right hr, H.reflection_involutive x, min_comm]

theorem gaussian_polarization_pair_gain_of_nearSide {d : ℕ} (H : Halfspace d)
    (g : Space d → ℝ) {x : Space d} (hx : x ∈ H.nearSide) :
    (H.polarize g x - g x) * Real.exp (-‖x‖ ^ 2) +
      (H.polarize g (H.reflection x) - g (H.reflection x)) *
        Real.exp (-‖H.reflection x‖ ^ 2) =
      (Real.exp (-‖x‖ ^ 2) - Real.exp (-‖H.reflection x‖ ^ 2)) *
        max (g (H.reflection x) - g x) 0 := by
  rw [polarize_reflection_of_nearSide H g hx]
  simp only [polarize, ite_eq_left hx]
  by_cases hg : g x ≤ g (H.reflection x)
  · rw [max_eq_right hg, min_eq_left hg, max_eq_left (sub_nonneg.mpr hg)]
    ring
  · have hrg := le_of_not_ge hg
    rw [max_eq_left hrg, min_eq_right hrg, max_eq_right (sub_nonpos.mpr hrg)]
    ring

theorem gaussian_polarization_pair_nonneg {d : ℕ} (H : Halfspace d)
    (g : Space d → ℝ) (x : Space d) :
    0 ≤ (H.polarize g x - g x) * Real.exp (-‖x‖ ^ 2) +
      (H.polarize g (H.reflection x) - g (H.reflection x)) *
        Real.exp (-‖H.reflection x‖ ^ 2) := by
  by_cases hx : x ∈ H.nearSide
  · rw [gaussian_polarization_pair_gain_of_nearSide H g hx]
    exact mul_nonneg (sub_nonneg.mpr (H.gaussian_reflection_lt hx).le) (le_max_right _ _)
  · by_cases hr : H.reflection x ∈ H.nearSide
    · have h := gaussian_polarization_pair_gain_of_nearSide H g hr
      rw [H.reflection_involutive x] at h
      rw [add_comm, h]
      apply mul_nonneg _ (le_max_right _ _)
      apply sub_nonneg.mpr
      simpa only [H.reflection_involutive x] using (H.gaussian_reflection_lt hr).le
    · have hb : inner ℝ H.normal x = H.offset := by
        rw [reflection_mem_nearSide_iff] at hr
        exact le_antisymm (not_lt.mp hr) (not_lt.mp hx)
      rw [reflection_fixed_of_boundary H hb]
      simp [polarize, reflection_fixed_of_boundary H hb]

theorem gaussian_polarization_pair_zero_iff {d : ℕ} (H : Halfspace d)
    (g : Space d → ℝ) {x : Space d} (hx : x ∈ H.nearSide) :
    (H.polarize g x - g x) * Real.exp (-‖x‖ ^ 2) +
      (H.polarize g (H.reflection x) - g (H.reflection x)) *
        Real.exp (-‖H.reflection x‖ ^ 2) = 0 ↔ g (H.reflection x) ≤ g x := by
  rw [gaussian_polarization_pair_gain_of_nearSide H g hx, mul_eq_zero]
  have hw : Real.exp (-‖x‖ ^ 2) - Real.exp (-‖H.reflection x‖ ^ 2) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (H.gaussian_reflection_lt hx))
  simp only [hw, false_or, max_eq_right_iff, sub_nonpos]

end Polarization.Halfspace

/-- Nested centered balls of the same finite measure agree almost everywhere.
This avoids a choice of an inverse for the volume-of-balls formula. -/
theorem centered_balls_ae_eq_of_volume_eq {d : ℕ} (r t : ℝ)
    (h : volume (Metric.ball (0 : Space d) r) =
      volume (Metric.ball (0 : Space d) t)) :
    Metric.ball (0 : Space d) r =ᵐ[volume] Metric.ball (0 : Space d) t := by
  rcases le_total r t with hrt | htr
  · exact ae_eq_of_subset_of_measure_ge (Metric.ball_subset_ball hrt) h.ge
      measurableSet_ball.nullMeasurableSet measure_ball_ne_top
  · exact (ae_eq_of_subset_of_measure_ge (Metric.ball_subset_ball htr) h.le
      measurableSet_ball.nullMeasurableSet measure_ball_ne_top).symm

/-- Countably many positive rational superlevels determine a nonnegative
real-valued function, on a single set of full measure. -/
theorem ae_eq_of_positive_rat_superlevels {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ}
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x) (hh : ∀ᵐ x ∂μ, 0 ≤ h x)
    (hlevel : ∀ q : ℚ, 0 < q → ∀ᵐ x ∂μ, ((q : ℝ) < g x ↔ (q : ℝ) < h x)) :
    g =ᵐ[μ] h := by
  have hall : ∀ᵐ x ∂μ, ∀ q : ℚ, 0 < q → ((q : ℝ) < g x ↔ (q : ℝ) < h x) :=
    (ae_all_iff).2 fun q => by
      by_cases hq : 0 < q
      · exact (hlevel q hq).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hg, hh, hall] with x hgx hhx hx
  apply le_antisymm
  · by_contra hle
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_of_not_ge hle)
    have hq : (0 : ℚ) < q := by exact_mod_cast (lt_of_le_of_lt hhx hq₁)
    exact (not_lt_of_ge (hx q hq |>.mp hq₂).le) hq₁
  · by_contra hle
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_of_not_ge hle)
    have hq : (0 : ℚ) < q := by exact_mod_cast (lt_of_le_of_lt hgx hq₁)
    exact (not_lt_of_ge (hx q hq |>.mpr hq₂).le) hq₁

/-- Centered superlevels of the prescribed measures determine the nonnegative
function up to equality almost everywhere. -/
theorem rearrangement_unique : PolyaSzegoExpected.Uniqueness := by
  intro d _ f g h hg hh
  apply ae_eq_of_positive_rat_superlevels hg.1 hh.1
  intro q hq
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨r, _, hgr⟩ := hg.2.1 q hq'
  obtain ⟨t, _, hht⟩ := hh.2.1 q hq'
  have hvol : volume (Metric.ball (0 : Space d) r) =
      volume (Metric.ball (0 : Space d) t) :=
    (measure_congr hgr).symm.trans ((hg.2.2 q hq').trans
      ((hh.2.2 q hq').symm.trans (measure_congr hht)))
  have heq := hgr.trans ((centered_balls_ae_eq_of_volume_eq r t hvol).trans hht.symm)
  filter_upwards [heq] with x hx
  exact iff_of_eq hx


namespace Rearrangement

/-- Centered superlevels give a finite antitone profile on every positive
radius. Countably many rational levels suffice for a common full-measure set. -/
theorem hasCenteredSuperlevels_radial {d : ℕ} (hd : 0 < d)
    {g : Space d → ℝ} (hg : ∀ᵐ x ∂volume, 0 ≤ g x)
    (hcenter : HasCenteredSuperlevels g) : IsRadiallyNonincreasing g := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let Q := {q : ℚ // 0 < q}
  have hq : ∀ q : Q, 0 < ((q.val : ℚ) : ℝ) := fun q => by exact_mod_cast q.property
  choose r hr hre using fun q : Q => hcenter (q.val : ℝ) (hq q)
  have hall : ∀ᵐ x ∂volume, ∀ q : Q, ((q.val : ℚ) : ℝ) < g x ↔ ‖x‖ < r q := by
    apply ae_all_iff.mpr
    intro q
    filter_upwards [hre q] with x hx
    simpa only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using iff_of_eq hx
  let S : ℝ → Set ℝ := fun t => {a | a = 0 ∨ ∃ q : Q, t < r q ∧ a = (q.val : ℝ)}
  have hzero : ∀ t, (0 : ℝ) ∈ S t := fun _ => Or.inl rfl
  have hbound : ∀ t > 0, BddAbove (S t) := by
    intro t ht
    obtain ⟨x, hxt, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.isOpen_ball.measure_ne_zero volume ⟨0, Metric.mem_ball_self ht⟩)
      (ae_restrict_of_ae (hg.and hall))
    refine ⟨g x, ?_⟩
    rintro a (rfl | ⟨q, htq, rfl⟩)
    · exact hx.1
    · have hnorm : ‖x‖ < t := by simpa only [Metric.mem_ball, dist_zero_right] using hxt
      exact ((hx.2 q).mpr (hnorm.trans htq)).le
  let φ : ℝ → ℝ := fun t => sSup (S t)
  have hφ0 : ∀ t > 0, 0 ≤ φ t := fun t ht => le_csSup (hbound t ht) (hzero t)
  refine ⟨φ, ?_, hφ0, ?_⟩
  · intro t ht u hu htu
    apply csSup_le ⟨0, hzero u⟩
    intro a ha
    apply le_csSup (hbound t ht)
    rcases ha with rfl | ⟨q, hq, rfl⟩
    · exact hzero t
    · exact Or.inr ⟨q, htu.trans_lt hq, rfl⟩
  · have hne : ∀ᵐ x : Space d ∂volume, x ≠ 0 := by
      simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (0 : Space d))
    filter_upwards [hg, hall, hne] with x hgx hx hnx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hnx
    apply le_antisymm
    · by_contra h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_of_not_ge h)
      have hqpos : (0 : ℚ) < q := by exact_mod_cast (hφ0 _ hnorm).trans_lt hq1
      have hmem : (q : ℝ) ∈ S ‖x‖ := Or.inr ⟨⟨q, hqpos⟩, (hx ⟨q, hqpos⟩).mp hq2, rfl⟩
      exact (not_lt_of_ge (le_csSup (hbound _ hnorm) hmem)) hq1
    · apply csSup_le ⟨0, hzero _⟩
      rintro a (rfl | ⟨q, hq, rfl⟩)
      · exact hgx
      · exact ((hx q).mpr hq).le

/-- A radial antitone profile with bounded essential support has centered-ball
superlevels. Open versus closed endpoint choices differ only on a sphere. -/
theorem radial_hasCenteredSuperlevels {d : ℕ} (hd : 0 < d)
    {g : Space d → ℝ} {R : ℝ} (hR : 0 < R)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → g x = 0)
    (hrad : IsRadiallyNonincreasing g) : HasCenteredSuperlevels g := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨φ, hanti, _, heq⟩ := hrad
  have hU : IsOpen {x : Space d | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hUne : {x : Space d | R < ‖x‖}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_norm_eq (Space d) (show 0 ≤ R + 1 by linarith)
    exact ⟨x, by simp only [Set.mem_ofPred_eq, hx]; linarith⟩
  obtain ⟨v, hv, hveq, hvs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero volume hUne) (ae_restrict_of_ae (heq.and hsupport))
  have hvpos : 0 < ‖v‖ := hR.trans hv
  have hvzero : φ ‖v‖ = 0 := by
    change g v = φ ‖v‖ at hveq
    rw [← hveq]
    apply hvs
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le, Set.mem_ofPred_eq] using hv
  intro s hs
  let S : Set ℝ := {t | t = 0 ∨ (0 < t ∧ s < φ t)}
  have hzero : (0 : ℝ) ∈ S := Or.inl rfl
  have hbound : BddAbove S := by
    refine ⟨‖v‖, ?_⟩
    rintro t (rfl | ⟨ht, hst⟩)
    · exact hvpos.le
    · by_contra h
      have hvt : ‖v‖ ≤ t := (lt_of_not_ge h).le
      have hp := hanti hvpos ht hvt
      rw [hvzero] at hp
      exact (not_lt_of_ge (hp.trans (by linarith : (0 : ℝ) ≤ s))) hst
  have hr : 0 ≤ sSup S := le_csSup hbound hzero
  refine ⟨sSup S, hr, ?_⟩
  have hn : ∀ᵐ x : Space d ∂volume, x ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (0 : Space d))
  have hsp : ∀ᵐ x : Space d ∂volume, x ∉ Metric.sphere (0 : Space d) (sSup S) :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 (sSup S))
  filter_upwards [heq, hn, hsp] with x hx hnx hxr
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hnx
  have hnr : ‖x‖ ≠ sSup S := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hxr
  simp only [Metric.mem_ball, dist_zero_right, hx]
  apply propext
  constructor
  · intro hsx
    have hle : ‖x‖ ≤ sSup S := le_csSup hbound (Or.inr ⟨hnorm, hsx⟩)
    exact lt_of_le_of_ne hle hnr
  · intro hlt
    obtain ⟨t, ht, hxt⟩ := exists_lt_of_lt_csSup ⟨0, hzero⟩ hlt
    rcases ht with rfl | ⟨htpos, hst⟩
    · exact (not_lt_of_ge hnorm.le hxt).elim
    · exact hst.trans_le (hanti hnorm htpos hxt.le)



/-- A full-measure set of values ordered by radius determines centered superlevels. -/
theorem centeredSuperlevels_of_ae_norm_order {d : ℕ} (hd : 0 < d)
    {g : Space d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (D : Set (Space d)) (hD : ∀ᵐ x ∂volume, x ∈ D)
    (hsupport : ∀ x ∈ D, x ∉ Metric.closedBall (0 : Space d) R → g x = 0)
    (horder : ∀ x ∈ D, ∀ y ∈ D, ‖x‖ < ‖y‖ → g y ≤ g x) :
    HasCenteredSuperlevels g := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro s hs
  let S : Set ℝ := {t | t = 0 ∨ ∃ y ∈ D, s < g y ∧ t = ‖y‖}
  have hzero : (0 : ℝ) ∈ S := Or.inl rfl
  have hbound : BddAbove S := by
    refine ⟨R, ?_⟩
    rintro t (rfl | ⟨y, hy, hsy, rfl⟩)
    · exact hR
    · by_contra h
      have hny : y ∉ Metric.closedBall (0 : Space d) R := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using lt_of_not_ge h
      rw [hsupport y hy hny] at hsy
      exact (not_lt_of_ge hs.le) hsy
  have hr : 0 ≤ sSup S := le_csSup hbound hzero
  refine ⟨sSup S, hr, ?_⟩
  have hsphere : ∀ᵐ x : Space d ∂volume, x ∉ Metric.sphere (0 : Space d) (sSup S) :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 (sSup S))
  filter_upwards [hD, hsphere] with x hx hxr
  have hnr : ‖x‖ ≠ sSup S := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hxr
  simp only [Metric.mem_ball, dist_zero_right]
  apply propext
  constructor
  · intro hsx
    exact lt_of_le_of_ne (le_csSup hbound (Or.inr ⟨x, hx, hsx, rfl⟩)) hnr
  · intro hlt
    obtain ⟨t, ht, hxt⟩ := exists_lt_of_lt_csSup ⟨0, hzero⟩ hlt
    rcases ht with rfl | ⟨y, hy, hsy, rfl⟩
    · exact (not_lt_of_ge (norm_nonneg x) hxt).elim
    · exact hsy.trans_le (horder x hx y hy hxt)

/-- Standard ball-average differentiation on the canonical volume measure. -/
theorem ae_tendsto_closedBall_average {d : ℕ} {g : Space d → ℝ}
    (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂volume, Tendsto (fun r => ⨍ y in Metric.closedBall x r, g y)
      (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hg 1] with x hx
  apply hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Metric.mem_closedBall_self (by simpa only [one_mul] using (show 0 ≤ r from le_of_lt hr))

/-- Reflection preserves the normalized integral over corresponding balls. -/
theorem reflection_closedBall_average {d : ℕ} (H : Halfspace d)
    (g : Space d → ℝ) (x : Space d) (r : ℝ) :
    (⨍ z in Metric.closedBall x r, g (H.reflection z)) =
      ⨍ z in Metric.closedBall (H.reflection x) r, g z := by
  have hemb : MeasurableEmbedding H.reflection :=
    H.reflectionIsometryEquiv.toHomeomorph.measurableEmbedding
  have hvol : volume (Metric.closedBall x r) =
      volume (Metric.closedBall (H.reflection x) r) := by
    rw [← H.reflection_preimage_closedBall x r]
    exact H.reflection_measurePreserving.measure_preimage_emb hemb _
  simp only [setAverage_eq, measureReal_def, hvol]
  congr 1
  rw [← H.reflection_preimage_closedBall x r]
  exact H.reflection_measurePreserving.setIntegral_preimage_emb hemb g _

/-- Ordering on a neighborhood gives ordering of corresponding ball averages. -/
theorem reflection_closedBall_average_le {d : ℕ} {g : Space d → ℝ}
    (hg : LocallyIntegrable g volume) (H : Halfspace d) (x : Space d) (r : ℝ)
    (hsub : Metric.closedBall x r ⊆ H.nearSide)
    (horder : ∀ᵐ z ∂volume, z ∈ H.nearSide → g (H.reflection z) ≤ g z) :
    (⨍ z in Metric.closedBall (H.reflection x) r, g z) ≤
      ⨍ z in Metric.closedBall x r, g z := by
  have hemb : MeasurableEmbedding H.reflection :=
    H.reflectionIsometryEquiv.toHomeomorph.measurableEmbedding
  have hint : IntegrableOn g (Metric.closedBall x r) volume :=
    hg.integrableOn_isCompact (isCompact_closedBall x r)
  have hint' : IntegrableOn (fun z => g (H.reflection z)) (Metric.closedBall x r) volume := by
    rw [← H.reflection_preimage_closedBall x r]
    exact (H.reflection_measurePreserving.integrableOn_comp_preimage hemb).mpr
      (hg.integrableOn_isCompact (isCompact_closedBall _ _))
  rw [← reflection_closedBall_average H g x r]
  simp only [setAverage_eq, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr measureReal_nonneg)
  apply integral_mono_ae hint' hint
  filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae horder] with z hz hord
  exact hord (hsub hz)

/-- At two Lebesgue points, all reflected a.e. orders force order by radius. -/
theorem le_of_closedBall_average_limits {d : ℕ} {g : Space d → ℝ}
    (hg : LocallyIntegrable g volume)
    (horder : ∀ H : Halfspace d, ∀ᵐ z ∂volume,
      z ∈ H.nearSide → g (H.reflection z) ≤ g z)
    (x y : Space d) (hxy : ‖x‖ < ‖y‖)
    (hx : Tendsto (fun r => ⨍ z in Metric.closedBall x r, g z)
      (𝓝[>] (0 : ℝ)) (𝓝 (g x)))
    (hy : Tendsto (fun r => ⨍ z in Metric.closedBall y r, g z)
      (𝓝[>] (0 : ℝ)) (𝓝 (g y))) : g y ≤ g x := by
  obtain ⟨H, Hxy, Hx⟩ := Halfspace.exists_reflection_pair x y hxy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp H.nearSide_isOpen x Hx
  apply le_of_tendsto_of_tendsto hy hx
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have hsub : Metric.closedBall x r ⊆ H.nearSide := by
    intro z hz
    apply hball
    exact (Metric.closedBall_subset_ball hr.2) hz
  simpa only [Hxy] using reflection_closedBall_average_le hg H x r hsub (horder H)

/-- Halfspace reflection order identifies every supported locally integrable
function by centered superlevels, using ball differentiation at a single common
full-measure set, without interchanging uncountably many exceptional sets. -/
theorem centeredSuperlevels_of_reflection_order {d : ℕ} (hd : 0 < d)
    {g : Space d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hg : LocallyIntegrable g volume)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → g x = 0)
    (horder : ∀ H : Halfspace d, ∀ᵐ z ∂volume,
      z ∈ H.nearSide → g (H.reflection z) ≤ g z) :
    HasCenteredSuperlevels g := by
  let D : Set (Space d) := {x | (x ∉ Metric.closedBall (0 : Space d) R → g x = 0) ∧
      Tendsto (fun r => ⨍ z in Metric.closedBall x r, g z) (𝓝[>] (0 : ℝ)) (𝓝 (g x))}
  have hD : ∀ᵐ x ∂volume, x ∈ D := hsupport.and (ae_tendsto_closedBall_average hg)
  apply centeredSuperlevels_of_ae_norm_order hd hR D hD
  · intro x hx
    exact hx.1
  · intro x hx y hy hxy
    exact le_of_closedBall_average_limits hg horder x y hxy hx.2 hy.2

theorem supportedSobolev_centeredSuperlevels_of_reflection_order {d : ℕ} (hd : 0 < d)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ} (hR : 0 ≤ R)
    (g : Polarization.WholeSobolev d p) (hg : SupportedNonnegative R g)
    (horder : ∀ H : Halfspace d, ∀ᵐ z ∂volume,
      z ∈ H.nearSide → sobolevUnderlying g (H.reflection z) ≤ sobolevUnderlying g z) :
    HasCenteredSuperlevels (sobolevUnderlying g) := by
  apply centeredSuperlevels_of_reflection_order hd hR _ hg.2 horder
  have hm : MemLp (sobolevUnderlying g) p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevUnderlying g)
  exact hm.locallyIntegrable Fact.out


/-- Sobolev classes with the fixed common support and sign conditions. -/
abbrev SupportedClass (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : ℝ) :=
  {g : Polarization.WholeSobolev d p // SupportedNonnegative R g}

section Orbit
variable (properties : PolarizationExpected.Properties)
variable {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)

/-- Choose the genuine weak-derivative tuple provided by the
polarization theorem. Its underlying function is the reflected max/min formula. -/
def choosePolarization (H : Halfspace d) (g : SupportedClass d p R) :
    SupportedClass d p R :=
  ⟨Classical.choose (properties d hd p hp hptop H R hR g.val g.property),
    (Classical.choose_spec (properties d hd p hp hptop H R hR g.val g.property)).2.1⟩

theorem choosePolarization_spec (H : Halfspace d) (g : SupportedClass d p R) :
    let w := choosePolarization properties hd hp hptop hR H g
    (sobolevUnderlying w.val =ᵐ[volume] H.polarize (sobolevUnderlying g.val)) ∧
    (∀ s : ℝ, 0 < s → volume {x | s < sobolevUnderlying w.val x} =
      volume {x | s < sobolevUnderlying g.val x}) ∧
    eLpNorm (sobolevUnderlying w.val) p volume =
      eLpNorm (sobolevUnderlying g.val) p volume ∧
    eLpNorm (gradient w.val) p volume ≤ eLpNorm (gradient g.val) p volume := by
  have h := Classical.choose_spec (properties d hd p hp hptop H R hR g.val g.property)
  exact ⟨h.1, h.2.2⟩

/-- Every finite string of polarizations, including the empty string. -/
def finitePolarization (L : List (Halfspace d)) (g : SupportedClass d p R) :
    SupportedClass d p R :=
  L.foldr (choosePolarization properties hd hp hptop hR) g

theorem finitePolarization_invariants (L : List (Halfspace d)) (g : SupportedClass d p R) :
    let w := finitePolarization properties hd hp hptop hR L g
    (∀ s : ℝ, 0 < s → volume {x | s < sobolevUnderlying w.val x} =
      volume {x | s < sobolevUnderlying g.val x}) ∧
    eLpNorm (sobolevUnderlying w.val) p volume =
      eLpNorm (sobolevUnderlying g.val) p volume ∧
    eLpNorm (gradient w.val) p volume ≤ eLpNorm (gradient g.val) p volume := by
  induction L with
  | nil => exact ⟨fun _ _ => rfl, rfl, le_rfl⟩
  | cons H L ih =>
    have h := (choosePolarization_spec properties hd hp hptop hR H
      (finitePolarization properties hd hp hptop hR L g)).2
    exact ⟨fun s hs => (h.1 s hs).trans (ih.1 s hs),
      h.2.1.trans ih.2.1, h.2.2.trans ih.2.2⟩

/-- The actual Sobolev orbit, before taking its Lp closure. -/
def finitePolarizationOrbit (g : SupportedClass d p R) :
    Set (Polarization.WholeSobolev d p) :=
  Set.range fun L => (finitePolarization properties hd hp hptop hR L g).val

end Orbit

/-- The gradients in the two frozen upstream interfaces represent the same
Euclidean vector. Only the change from volume restricted to the whole space
to volume itself can change their pointwise representatives. -/
theorem gradientFunction_ae_gradient {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Polarization.WholeSobolev d p) :
    gradientFunction u =ᵐ[volume] gradient u := by
  have hcoords : ∀ᵐ x ∂volume, ∀ j : Fin d,
      wholeLp (sobolevDerivative u (supportedFirstIndex j)) x =
        firstWeakDerivative u j x := by
    apply ae_all_iff.mpr
    intro j
    exact wholeLp_ae (firstWeakDerivative u j)
  filter_upwards [hcoords] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem gradientNorm_eq_eLpNorm_toReal {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Polarization.WholeSobolev d p) :
    gradientNorm u = (eLpNorm (gradient u) p volume).toReal := by
  rw [gradientNorm, gradientLp, Lp.norm_toLp,
    eLpNorm_congr_ae (gradientFunction_ae_gradient u)]

/-- The common energy bound from finite polarization is a bound for the
canonical Sobolev graph norm, not merely for an unrelated vector norm. -/
theorem finitePolarizationOrbit_bounded
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) :
    Bornology.IsBounded (finitePolarizationOrbit properties hd hp hptop hR g) := by
  apply (isBounded_iff_euclidean_gradient_bound _).mpr
  refine ⟨‖wholeLp (sobolevUnderlying g.val)‖ + gradientNorm g.val, ?_⟩
  rintro u ⟨L, rfl⟩
  have hi := finitePolarization_invariants properties hd hp hptop hR L g
  have hn : ‖wholeLp (sobolevUnderlying
      (finitePolarization properties hd hp hptop hR L g).val)‖ =
      ‖wholeLp (sobolevUnderlying g.val)‖ := by
    rw [wholeLp, Lp.norm_toLp, wholeLp, Lp.norm_toLp, hi.2.1]
  rw [hn, gradientNorm_eq_eLpNorm_toReal, gradientNorm_eq_eLpNorm_toReal]
  apply add_le_add le_rfl
  apply ENNReal.toReal_mono _ hi.2.2
  have hm := gradientFunction_memLp g.val
  exact (eLpNorm_congr_ae (gradientFunction_ae_gradient g.val)) ▸ hm.eLpNorm_ne_top

/-- Relative compactness of the finite orbit follows from the supplied actual
bounded-support compactness theorem and the explicitly verified norm bridge. -/
theorem finitePolarizationOrbit_compact_closure
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) :
    IsCompact (closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g)) := by
  apply supported_compactness hd p hptop _
    (finitePolarizationOrbit_bounded properties hd hp hptop hR g)
    (Metric.closedBall (0 : Space d) R) Metric.isBounded_closedBall
  rintro u ⟨L, rfl⟩
  have hs := (finitePolarization properties hd hp hptop hR L g).property.2
  filter_upwards [hs, wholeLp_ae (sobolevUnderlying
      (finitePolarization properties hd hp hptop hR L g).val)] with x hx heq houtside
  exact heq.trans (hx houtside)


/-- Sign and essential support are closed conditions in the Lp topology.
The subsequence argument works on an arbitrary measure space and support set. -/
theorem isClosed_nonnegative_supportedLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ≥0∞) [Fact (1 ≤ p)] (B : Set α) :
    IsClosed {u : Lp ℝ p μ | (∀ᵐ x ∂μ, 0 ≤ u x) ∧
      (∀ᵐ x ∂μ, x ∉ B → u x = 0)} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f u hf hfu
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfu).exists_seq_tendsto_ae
  have hn : ∀ᵐ x ∂μ, ∀ n : ℕ, 0 ≤ f n x :=
    ae_all_iff.mpr fun n => (hf n).1
  have hs : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∉ B → f n x = 0 :=
    ae_all_iff.mpr fun n => (hf n).2
  constructor
  · filter_upwards [hns, hn] with x hx hnx
    exact ge_of_tendsto' hx fun n => hnx (ns n)
  · filter_upwards [hns, hs] with x hx hsx houtside
    have heq : (fun n => f (ns n) x) = fun _ => (0 : ℝ) :=
      funext fun n => hsx (ns n) houtside
    rw [heq] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds

/-- The common sign and support conditions persist at every point of the
compact orbit closure, in particular at a Gaussian maximizer. -/
theorem finitePolarizationOrbit_closure_supported
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) :
    closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g) ⊆
    {u : Lp ℝ p (volume : Measure (Space d)) |
      (∀ᵐ x ∂volume, 0 ≤ u x) ∧
      (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → u x = 0)} := by
  apply closure_minimal _ (isClosed_nonnegative_supportedLp volume p _)
  rintro v ⟨u, ⟨L, rfl⟩, rfl⟩
  have hs := (finitePolarization properties hd hp hptop hR L g).property
  have heq := wholeLp_ae (sobolevUnderlying
    (finitePolarization properties hd hp hptop hR L g).val)
  constructor
  · filter_upwards [heq, hs.1] with x hx hnx
    simpa only [hx] using hnx
  · filter_upwards [heq, hs.2] with x hx hsx houtside
    exact hx.trans (hsx houtside)

open ExpandedFA.P1.C04CanonicalMap.Spec
open ExpandedFA.PartIV.VectorLpReflexive

/-- Reflexivity of a finite product, using its actual canonical evaluation. -/
theorem finite_pi_reflexive {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (hE : ∀ i, IsReflexiveValue ℝ (E i)) : IsReflexiveValue ℝ (∀ i, E i) := by
  classical
  intro Φ
  let L : (i : ι) → (E i →L[ℝ] ℝ) →L[ℝ] ((∀ i, E i) →L[ℝ] ℝ) := fun i =>
    (ContinuousLinearMap.compL ℝ (∀ i, E i) (E i) ℝ).flip (ContinuousLinearMap.proj i)
  choose x hx using fun i => hE i (Φ.comp (L i))
  refine ⟨x, ?_⟩
  ext f
  let g : (i : ι) → E i →L[ℝ] ℝ := fun i => f.comp (ContinuousLinearMap.single ℝ E i)
  have he : f = ∑ i, L i (g i) := by
    ext v
    simpa only [sum_apply, L, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, g] using (ContinuousLinearMap.sum_comp_single ℝ E f v).symm
  change f x = Φ f
  calc
    f x = ∑ i, g i (x i) := (ContinuousLinearMap.sum_comp_single ℝ E f x).symm
    _ = ∑ i, Φ (L i (g i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => z (g i)) (hx i)
    _ = Φ (∑ i, L i (g i)) := (map_sum Φ _ _).symm
    _ = Φ f := congrArg Φ he.symm

/-- The canonical first-order Sobolev graph is a closed subspace of a finite
product of reflexive Lp spaces for the source's exponent range. -/
theorem wholeSobolev_reflexive {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) : IsReflexiveValue ℝ (Polarization.WholeSobolev d p) := by
  have hscalar : IsReflexiveValue ℝ ℝ := (endpoint_counterexamples ℝ).1
  have hLp : IsReflexiveValue ℝ (DomainLp ℝ (⊤ : Opens (Space d)) p) :=
    lp_reflexive ℝ hscalar _ p hp hptop
  have hPi := finite_pi_reflexive
    (fun _ : SobolevIndex d 1 => DomainLp ℝ (⊤ : Opens (Space d)) p) (fun _ => hLp)
  have htuple : IsReflexiveValue ℝ (SobolevTuple ℝ (⊤ : Opens (Space d)) 1 p) :=
    reflexive_of_equiv (PiLp.continuousLinearEquiv 1 ℝ _).symm hPi
  exact closed_subspace_reflexive _ (sobolevSubmodule_isClosed _ 1 p) htuple

/-- A bounded, closed, convex subset of a reflexive space has closed image
under every continuous linear map, in the norm topology of the codomain. -/
theorem isClosed_linear_image_of_reflexive {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hX : IsReflexiveValue ℝ X) (L : X →L[ℝ] Y)
    {C : Set X} (hC : IsClosed C) (hb : Bornology.IsBounded C) (hc : Convex ℝ C) :
    IsClosed (L '' C) := by
  let S : Set (WeakSpace ℝ X) := toWeakSpace ℝ X '' C
  have hSc : IsClosed S := by
    apply closure_eq_iff_isClosed.mp
    rw [← hc.toWeakSpace_closure ℝ, hC.closure_eq]
  have hSk : IsCompact S := by
    rw [← hSc.closure_eq]
    apply NormedSpace.isCompact_closure_of_isBounded ℝ X S
    · simpa only [S, Set.preimage_image_eq _ (toWeakSpace ℝ X).injective] using hb
    · intro z _
      obtain ⟨x, hx⟩ := hX (WeakDual.toStrongDual z)
      exact ⟨toWeakSpace ℝ X x, hx⟩
  have himage : IsClosed ((WeakSpace.map L) '' S) :=
    (hSk.image (WeakSpace.map L).continuous).isClosed
  have hpre := himage.preimage (toWeakSpaceCLM ℝ Y).continuous
  convert hpre using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨toWeakSpace ℝ X x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
    exact ⟨x, hx, hxy⟩

/-- Every Lp closure point of the finite orbit has a genuine weak-derivative
tuple with the original sharp Euclidean gradient bound. -/
theorem finitePolarizationOrbit_closure_sobolev
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R)
    {v : Lp ℝ p (volume : Measure (Space d))}
    (hv : v ∈ closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g)) :
    ∃ w : Polarization.WholeSobolev d p,
      wholeLp (sobolevUnderlying w) = v ∧ SupportedNonnegative R w ∧
      eLpNorm (gradient w) p volume ≤ eLpNorm (gradient g.val) p volume := by
  let U : Polarization.WholeSobolev d p →L[ℝ] Lp ℝ p (volume : Measure (Space d)) :=
    wholeLpCLM.comp (sobolevUnderlyingCLM (⊤ : Opens (Space d)) 1 p)
  let G : Polarization.WholeSobolev d p →L[ℝ] Lp (Space d) p volume := gradientCLM
  let F : ℝ := ‖wholeLp (sobolevUnderlying g.val)‖
  let E : ℝ := gradientNorm g.val
  let C : Set (Polarization.WholeSobolev d p) :=
    U ⁻¹' Metric.closedBall 0 F ∩ G ⁻¹' Metric.closedBall 0 E
  have hc : IsClosed C :=
    (Metric.isClosed_closedBall.preimage U.continuous).inter
      (Metric.isClosed_closedBall.preimage G.continuous)
  have hvC : Convex ℝ C :=
    ((convex_closedBall _ _).linear_preimage U.toLinearMap).inter
      ((convex_closedBall _ _).linear_preimage G.toLinearMap)
  have hb : Bornology.IsBounded C := by
    apply (isBounded_iff_euclidean_gradient_bound C).mpr
    refine ⟨F + E, ?_⟩
    intro u hu
    have huf : ‖U u‖ ≤ F := by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hu.1
    have hue : ‖G u‖ ≤ E := by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hu.2
    change ‖wholeLp (sobolevUnderlying u)‖ ≤ F at huf
    have hue' : gradientNorm u ≤ E := by
      simpa only [G, gradientCLM_eq, gradientNorm] using hue
    exact add_le_add huf hue'
  have him := isClosed_linear_image_of_reflexive (wholeSobolev_reflexive hp hptop) U hc hb hvC
  have hsub : ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g) ⊆ U '' C := by
    rintro _ ⟨u, ⟨L, rfl⟩, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have hi := finitePolarization_invariants properties hd hp hptop hR L g
    constructor
    · change U _ ∈ Metric.closedBall 0 F
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖wholeLp (sobolevUnderlying
        (finitePolarization properties hd hp hptop hR L g).val)‖ ≤ F
      dsimp only [F]
      rw [wholeLp, Lp.norm_toLp, wholeLp, Lp.norm_toLp, hi.2.1]
    · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, G,
        gradientCLM_eq]
      change gradientNorm _ ≤ gradientNorm g.val
      rw [gradientNorm_eq_eLpNorm_toReal, gradientNorm_eq_eLpNorm_toReal]
      apply ENNReal.toReal_mono _ hi.2.2
      exact (eLpNorm_congr_ae (gradientFunction_ae_gradient g.val)) ▸
        (gradientFunction_memLp g.val).eLpNorm_ne_top
  obtain ⟨w, hw, hwv⟩ := closure_minimal hsub him hv
  refine ⟨w, hwv, ?_, ?_⟩
  · have hsign := finitePolarizationOrbit_closure_supported properties hd hp hptop hR g hv
    have heq : sobolevUnderlying w =ᵐ[volume] v := by
      have heq := (wholeLp_ae (sobolevUnderlying w)).symm
      change wholeLp (sobolevUnderlying w) = v at hwv
      rwa [hwv] at heq
    constructor
    · filter_upwards [heq, hsign.1] with x hx hnx
      exact hx.symm ▸ hnx
    · filter_upwards [heq, hsign.2] with x hx hs hout
      exact hx.trans (hs hout)
  · have he : gradientNorm w ≤ gradientNorm g.val := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, G,
        gradientCLM_eq, E, gradientNorm] using hw.2
    rw [gradientNorm_eq_eLpNorm_toReal, gradientNorm_eq_eLpNorm_toReal] at he
    apply (ENNReal.toReal_le_toReal ?_ ?_).mp he
    · exact (eLpNorm_congr_ae (gradientFunction_ae_gradient w)) ▸
        (gradientFunction_memLp w).eLpNorm_ne_top
    · exact (eLpNorm_congr_ae (gradientFunction_ae_gradient g.val)) ▸
        (gradientFunction_memLp g.val).eLpNorm_ne_top


/-- The bounded ramps used in the source to retain *every* positive level
under passage to the orbit closure. -/
def levelRamp (n : ℕ) (s t : ℝ) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal ((n : ℝ) * max (t - s) 0))

theorem levelRamp_monotone (s t : ℝ) : Monotone (fun n => levelRamp n s t) := by
  intro i j hij
  unfold levelRamp
  apply min_le_min_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (le_max_right _ _)

theorem iSup_levelRamp (s t : ℝ) :
    (⨆ n : ℕ, levelRamp n s t) = if s < t then 1 else 0 := by
  by_cases hst : s < t
  · rw [ite_eq_left hst]
    have hpos : 0 < t - s := sub_pos.mpr hst
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t - s))
    have hprod : 1 ≤ (n : ℝ) * max (t - s) 0 := by
      rw [max_eq_left hpos.le]
      exact ((div_lt_iff₀ hpos).mp hn).le
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) * max (t - s) 0) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hprod
    apply le_antisymm
    · exact iSup_le fun _ => min_le_left _ _
    · exact le_iSup_of_le n (le_min le_rfl hone)
  · simp [hst, levelRamp, max_eq_right (sub_nonpos.mpr (le_of_not_gt hst))]

/-- Monotone convergence recovers a strict superlevel measure at the exact
specified level; no zero-measure assumption on the equality level is used. -/
theorem superlevel_measure_eq_iSup_ramps {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : AEMeasurable g μ) (s : ℝ) :
    μ {x | s < g x} = ⨆ n : ℕ, ∫⁻ x, levelRamp n s (g x) ∂μ := by
  have hm : ∀ n : ℕ, AEMeasurable (fun x => levelRamp n s (g x)) μ := by
    intro n
    unfold levelRamp
    fun_prop
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n : ℕ => levelRamp n s (g x)) :=
    Filter.Eventually.of_forall fun x => levelRamp_monotone s (g x)
  rw [← lintegral_iSup' hm hmono,
    ← lintegral_indicator_one₀ (nullMeasurableSet_lt aemeasurable_const hg)]
  apply lintegral_congr
  intro x
  rw [iSup_levelRamp]
  by_cases hx : s < g x <;> simp [Set.indicator, hx]

/-- Equality of all ramp integrals implies equality of all strict level
measures, including levels of positive measure. -/
theorem superlevel_measure_eq_of_ramps {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) (s : ℝ)
    (hramp : ∀ n : ℕ, (∫⁻ x, levelRamp n s (g x) ∂μ) =
      ∫⁻ x, levelRamp n s (h x) ∂μ) :
    μ {x | s < g x} = μ {x | s < h x} := by
  rw [superlevel_measure_eq_iSup_ramps hg s, superlevel_measure_eq_iSup_ramps hh s]
  exact iSup_congr hramp

/-- A real-valued version of the ramp, used with the layer-cake formula. -/
def realLevelRamp (n : ℕ) (s t : ℝ) : ℝ :=
  min 1 ((n : ℝ) * max (t - s) 0)

theorem levelRamp_eq_ofReal (n : ℕ) (s t : ℝ) :
    levelRamp n s t = ENNReal.ofReal (realLevelRamp n s t) := by
  simp only [levelRamp, realLevelRamp, ENNReal.ofReal_min, ENNReal.ofReal_one]

theorem realLevelRamp_nonneg (n : ℕ) (s t : ℝ) : 0 ≤ realLevelRamp n s t := by
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))

theorem continuous_levelRamp (n : ℕ) (s : ℝ) : Continuous (levelRamp n s) := by
  unfold levelRamp
  exact continuous_const.min (ENNReal.continuous_ofReal.comp (by fun_prop))

/-- The strict superlevels of a nonzero ramp are strict superlevels of the
original function. This identity is valid at every level, including atoms. -/
theorem realLevelRamp_lt_iff {n : ℕ} (hn : n ≠ 0) (s t a : ℝ) (ht : 0 < t) :
    t < realLevelRamp n s a ↔ t < 1 ∧ s + t / n < a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [realLevelRamp, lt_min_iff]
  constructor
  · rintro ⟨ht1, hta⟩
    refine ⟨ht1, ?_⟩
    have hma : t / n < max (a - s) 0 := (div_lt_iff₀ hn').mpr (by nlinarith)
    have hts : 0 < t / n := div_pos ht hn'
    have ha : 0 < a - s := by
      by_contra h
      rw [max_eq_right (le_of_not_gt h)] at hma
      exact (not_lt_of_ge hts.le) hma
    rw [max_eq_left ha.le] at hma
    linarith
  · rintro ⟨ht1, hta⟩
    refine ⟨ht1, ?_⟩
    have hma : t / n < a - s := by linarith
    have hmul : t < (a - s) * n := (div_lt_iff₀ hn').mp hma
    calc t < (n : ℝ) * (a - s) := by nlinarith
         _ ≤ (n : ℝ) * max (a - s) 0 :=
           mul_le_mul_of_nonneg_left (le_max_left _ _) hn'.le

/-- Equality of the original positive tails gives equality of every ramp
integral by Cavalieri's principle. No regularity of the distribution is used. -/
theorem lintegral_levelRamp_eq_of_superlevels {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    (heq : ∀ t : ℝ, 0 < t → μ {x | t < g x} = μ {x | t < h x})
    (n : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, levelRamp n s (g x) ∂μ) = ∫⁻ x, levelRamp n s (h x) ∂μ := by
  by_cases hn : n = 0
  · simp [hn, levelRamp]
  simp_rw [levelRamp_eq_ofReal]
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun x => realLevelRamp_nonneg n s (g x))
    (by unfold realLevelRamp; fun_prop),
    lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun x => realLevelRamp_nonneg n s (h x))
    (by unfold realLevelRamp; fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  simp_rw [realLevelRamp_lt_iff hn s t _ ht]
  by_cases ht1 : t < 1
  · simp only [ht1, true_and]
    apply heq
    exact add_pos_of_pos_of_nonneg hs (div_nonneg ht.le (Nat.cast_nonneg _))
  · simp only [ht1, false_and, Set.ofPred_false]

/-- Along an almost everywhere convergent sequence with common support of
finite measure, all bounded ramp integrals converge. -/
theorem tendsto_lintegral_levelRamp_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} (hB : MeasurableSet B) (hBfin : μ B ≠ ∞)
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ k, AEMeasurable (f k) μ)
    (hsupport : ∀ k, ∀ᵐ x ∂μ, x ∉ B → f k x = 0)
    (hfg : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => f k x) Filter.atTop (𝓝 (g x)))
    (n : ℕ) (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun k => ∫⁻ x, levelRamp n s (f k x) ∂μ) Filter.atTop
      (𝓝 (∫⁻ x, levelRamp n s (g x) ∂μ)) := by
  apply tendsto_lintegral_of_dominated_convergence' (B.indicator (fun _ => (1 : ℝ≥0∞)))
  · intro k
    exact (continuous_levelRamp n s).measurable.comp_aemeasurable (hf k)
  · intro k
    filter_upwards [hsupport k] with x hx
    by_cases hxB : x ∈ B
    · simpa only [Set.indicator_of_mem hxB, levelRamp] using min_le_left (1 : ℝ≥0∞) _
    · simp [Set.indicator_of_notMem hxB, hx hxB, levelRamp,
        hs.le]
  · simpa only [lintegral_indicator hB, setLIntegral_const, one_mul] using hBfin
  · filter_upwards [hfg] with x hx
    exact ((continuous_levelRamp n s).tendsto (g x)).comp hx

/-- Equidistribution at every positive level is closed in Lp when all
functions vanish outside a common finite-measure measurable set. -/
theorem isClosed_supported_equidistributedLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {B : Set α} (hB : MeasurableSet B) (hBfin : μ B ≠ ∞)
    {g : α → ℝ} (hg : AEMeasurable g μ) :
    IsClosed {u : Lp ℝ p μ |
      (∀ᵐ x ∂μ, x ∉ B → u x = 0) ∧
      ∀ s : ℝ, 0 < s → μ {x | s < u x} = μ {x | s < g x}} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f u hf hfu
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfu).exists_seq_tendsto_ae
  have hs : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∉ B → f k x = 0 :=
    ae_all_iff.mpr fun k => (hf k).1
  refine ⟨?_, ?_⟩
  · filter_upwards [hns, hs] with x hx hsx hout
    have heq : (fun k => f (ns k) x) = fun _ => (0 : ℝ) :=
      funext fun k => hsx (ns k) hout
    rw [heq] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds
  · intro s hs
    apply superlevel_measure_eq_of_ramps (Lp.aestronglyMeasurable u).aemeasurable hg s
    intro n
    have ht := tendsto_lintegral_levelRamp_of_ae hB hBfin
      (fun k => (Lp.aestronglyMeasurable (f (ns k))).aemeasurable) (fun k => (hf (ns k)).1) hns n s hs
    have heq : (fun k => ∫⁻ x, levelRamp n s (f (ns k) x) ∂μ) =
        fun _ : ℕ => ∫⁻ x, levelRamp n s (g x) ∂μ := by
      funext k
      exact lintegral_levelRamp_eq_of_superlevels (Lp.aestronglyMeasurable _).aemeasurable hg (hf (ns k)).2 n s hs
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds

/-- All points of the compact orbit closure retain every positive level
measure, without excluding atoms of the initial distribution. -/
theorem finitePolarizationOrbit_closure_superlevels
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) :
    closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g) ⊆
    {u : Lp ℝ p (volume : Measure (Space d)) |
      ∀ s : ℝ, 0 < s → volume {x | s < u x} =
        volume {x | s < sobolevUnderlying g.val x}} := by
  have hclosed := isClosed_supported_equidistributedLp volume p
    (B := Metric.closedBall (0 : Space d) R) measurableSet_closedBall
    measure_closedBall_lt_top.ne
    (show AEMeasurable (sobolevUnderlying g.val) volume by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (Lp.aestronglyMeasurable (sobolevUnderlying g.val)).aemeasurable)
  have hsub : (fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g ⊆
      {u : Lp ℝ p (volume : Measure (Space d)) |
        (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → u x = 0) ∧
        ∀ s : ℝ, 0 < s → volume {x | s < u x} =
          volume {x | s < sobolevUnderlying g.val x}} := by
    rintro u ⟨v, ⟨L, rfl⟩, rfl⟩
    have heq := wholeLp_ae (sobolevUnderlying
      (finitePolarization properties hd hp hptop hR L g).val)
    constructor
    · filter_upwards [heq, (finitePolarization properties hd hp hptop hR L g).property.2]
        with x hx hs hout
      exact hx.trans (hs hout)
    · intro s hs
      calc volume {x | s < wholeLp (sobolevUnderlying
              (finitePolarization properties hd hp hptop hR L g).val) x} =
            volume {x | s < sobolevUnderlying
              (finitePolarization properties hd hp hptop hR L g).val x} := by
                apply measure_congr
                filter_upwards [heq] with x hx
                simp only [hx]
           _ = _ := (finitePolarization_invariants properties hd hp hptop hR L g).1 s hs
  intro u hu
  exact (closure_minimal hsub hclosed hu).2

/-- The source's Gaussian weight, cut off only outside the common support.
On every member of the orbit its integral is the full Gaussian moment. -/
def supportedGaussian {d : ℕ} (R : ℝ) : Space d → ℝ :=
  (Metric.closedBall (0 : Space d) R).indicator (fun x => Real.exp (-‖x‖ ^ 2))

theorem supportedGaussian_memLp {d : ℕ} (R : ℝ) (q : ℝ≥0∞) :
    MemLp (supportedGaussian (d := d) R) q volume := by
  have hs : HasCompactSupport (supportedGaussian (d := d) R) := by
    apply (isCompact_closedBall (0 : Space d) R).of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal Set.support_indicator_subset Metric.isClosed_closedBall
  have hm : AEStronglyMeasurable (supportedGaussian (d := d) R) volume :=
    (by fun_prop : Continuous (fun x : Space d => Real.exp (-‖x‖ ^ 2))).aestronglyMeasurable.indicator
      measurableSet_closedBall
  apply hs.memLp_of_bound hm 1
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : Space d) R
  · simp only [supportedGaussian, Set.indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  · simp [supportedGaussian, Set.indicator_of_notMem hx]

/-- A continuous linear realization of the Gaussian moment on the fixed ball. -/
def gaussianMoment {d : ℕ} (R : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (volume : Measure (Space d)) →L[ℝ] ℝ := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing volume p (ENNReal.conjExponent p)).flip
    ((supportedGaussian_memLp R (ENNReal.conjExponent p)).toLp (supportedGaussian R))

theorem gaussianMoment_eq_integral {d : ℕ} (R : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (volume : Measure (Space d))) :
    gaussianMoment R p u = ∫ x, u x * supportedGaussian R x := by
  have : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  rw [gaussianMoment, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(supportedGaussian_memLp (d := d) R (ENNReal.conjExponent p)).coeFn_toLp] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx]

/-- The compact orbit closure contains a maximizer of the actual weighted
integral. No radiality or Sobolev regularity of this maximizer is assumed. -/
theorem exists_gaussian_maximizer
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) :
    let K := closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g)
    ∃ v ∈ K, IsMaxOn (gaussianMoment R p) K v := by
  apply (finitePolarizationOrbit_compact_closure properties hd hp hptop hR g).exists_isMaxOn
  · apply Set.Nonempty.closure
    refine ⟨wholeLp (sobolevUnderlying g.val), ?_⟩
    exact ⟨g.val, ⟨[], rfl⟩, rfl⟩
  · exact (gaussianMoment R p).continuous.continuousOn

/-- The exact scalar gain obtained by sorting a reflected pair. -/
theorem polarization_pair_gain (a b w z : ℝ) :
    max a b * w + min a b * z - (a * w + b * z) =
      (w - z) * max (b - a) 0 := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, min_eq_left hab, max_eq_left (sub_nonneg.mpr hab)]
    ring
  · have hba := le_of_not_ge hab
    rw [max_eq_left hba, min_eq_right hba, max_eq_right (sub_nonpos.mpr hba)]
    ring

/-- Strictly greater weight at the near point forces the sorted order whenever
the polarization has zero gain. -/
theorem polarization_pair_zero_gain_iff (a b w z : ℝ) (hzw : z < w) :
    max a b * w + min a b * z = a * w + b * z ↔ b ≤ a := by
  rw [← sub_eq_zero, polarization_pair_gain, mul_eq_zero]
  have hwz : w - z ≠ 0 := ne_of_gt (sub_pos.mpr hzw)
  simp only [hwz, false_or, max_eq_right_iff, sub_nonpos]


lemma edist_wholeLp_eq_eLpNorm_sub {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g h : Polarization.WholeSobolev d p) :
    edist (wholeLp (sobolevUnderlying g)) (wholeLp (sobolevUnderlying h)) =
      eLpNorm (fun x => sobolevUnderlying g x - sobolevUnderlying h x) p volume := by
  rw [Lp.edist_def]
  exact eLpNorm_congr_ae ((wholeLp_ae (sobolevUnderlying g)).sub
    (wholeLp_ae (sobolevUnderlying h)))

lemma choosePolarization_edist_le
    (continuity : PolarizationExpected.Continuity)
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (H : Halfspace d) (g h : SupportedClass d p R) :
    edist (wholeLp (sobolevUnderlying
      (choosePolarization properties hd hp hptop hR H g).val))
      (wholeLp (sobolevUnderlying
      (choosePolarization properties hd hp hptop hR H h).val)) ≤
      (2 : ℝ≥0∞) ^ p.toReal⁻¹ *
      edist (wholeLp (sobolevUnderlying g.val)) (wholeLp (sobolevUnderlying h.val)) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) hptop
  have hc := continuity d hd p hp hptop H R hR g.val h.val g.property h.property
  rw [edist_wholeLp_eq_eLpNorm_sub, edist_wholeLp_eq_eLpNorm_sub]
  have hg := (choosePolarization_spec properties hd hp hptop hR H g).1
  have hh := (choosePolarization_spec properties hd hp hptop hR H h).1
  have heq : eLpNorm (fun x =>
      sobolevUnderlying (choosePolarization properties hd hp hptop hR H g).val x -
      sobolevUnderlying (choosePolarization properties hd hp hptop hR H h).val x) p volume =
      eLpNorm (fun x => H.polarize (sobolevUnderlying g.val) x -
        H.polarize (sobolevUnderlying h.val) x) p volume :=
    eLpNorm_congr_ae (hg.sub hh)
  rw [heq]
  have h' := ENNReal.rpow_le_rpow hc (inv_nonneg.mpr hq.le)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one] using h'


/-- The Lp closure of the finite orbit is stable under every allowed polarization. -/
lemma finitePolarizationOrbit_closure_polarization
    (continuity : PolarizationExpected.Continuity)
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g : SupportedClass d p R) (H : Halfspace d) (w : SupportedClass d p R)
    (hw : wholeLp (sobolevUnderlying w.val) ∈
      closure ((fun u => wholeLp (sobolevUnderlying u)) ''
        finitePolarizationOrbit properties hd hp hptop hR g)) :
    wholeLp (sobolevUnderlying (choosePolarization properties hd hp hptop hR H w).val) ∈
      closure ((fun u => wholeLp (sobolevUnderlying u)) ''
        finitePolarizationOrbit properties hd hp hptop hR g) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  have hLists : ∀ n, ∃ L : List (Halfspace d),
      wholeLp (sobolevUnderlying (finitePolarization properties hd hp hptop hR L g).val) =
        v n := by
    intro n
    rcases hv n with ⟨u, ⟨L, rfl⟩, hu⟩
    exact ⟨L, hu⟩
  choose L hL using hLists
  let wseq : ℕ → SupportedClass d p R :=
    fun n => finitePolarization properties hd hp hptop hR (L n) g
  let vseq : ℕ → Lp ℝ p (volume : Measure (Space d)) := fun n =>
    wholeLp (sobolevUnderlying (choosePolarization properties hd hp hptop hR H (wseq n)).val)
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨vseq, ?_, ?_⟩
  · intro n
    exact ⟨_, ⟨H :: L n, rfl⟩, rfl⟩
  · apply tendsto_iff_edist_tendsto_0.mpr
    have hbound : ∀ n,
        edist (vseq n)
          (wholeLp (sobolevUnderlying (choosePolarization properties hd hp hptop hR H w).val)) ≤
        (2 : ℝ≥0∞) ^ p.toReal⁻¹ * edist (v n) (wholeLp (sobolevUnderlying w.val)) := by
      intro n
      have hb := choosePolarization_edist_le continuity properties hd hp hptop hR H (wseq n) w
      change edist (vseq n) _ ≤ _ at hb
      rw [show wholeLp (sobolevUnderlying (wseq n).val) = v n from hL n] at hb
      exact hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => bot_le) hbound
    simpa using ENNReal.Tendsto.const_mul (tendsto_iff_edist_tendsto_0.mp hlim)
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg
        (inv_nonneg.mpr ENNReal.toReal_nonneg) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))



/-- The full Gaussian product is integrable on the common finite support. -/
theorem gaussianProduct_integrable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {R : ℝ} {f : Space d → ℝ} (hf : MemLp f p volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → f x = 0) :
    Integrable (fun x => f x * Real.exp (-‖x‖ ^ 2)) volume := by
  have hi := hf.integrable_mul (supportedGaussian_memLp (d := d) R (ENNReal.conjExponent p))
  apply hi.congr
  filter_upwards [hs] with x hx
  by_cases hxB : x ∈ Metric.closedBall (0 : Space d) R
  · simp only [Pi.mul_apply, supportedGaussian, Set.indicator_of_mem hxB]
  · simp only [Pi.mul_apply, hx hxB, zero_mul]

/-- On a supported Lp class the continuous cutoff moment is the full moment. -/
theorem gaussianMoment_eq_full_integral {d : ℕ} (R : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp ℝ p (volume : Measure (Space d)))
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → u x = 0) :
    gaussianMoment R p u = ∫ x, u x * Real.exp (-‖x‖ ^ 2) := by
  rw [gaussianMoment_eq_integral]
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  by_cases hxB : x ∈ Metric.closedBall (0 : Space d) R
  · simp only [supportedGaussian, Set.indicator_of_mem hxB]
  · simp only [hx hxB, zero_mul]

/-- A maximizer of the full Gaussian moment is ordered on each reflected pair.
The proof integrates a nonnegative symmetrized gain over the whole space. -/
theorem gaussian_reflection_order_of_integral_le {d : ℕ}
    (H : Halfspace d) (f : Space d → ℝ)
    (hfi : Integrable (fun x => f x * Real.exp (-‖x‖ ^ 2)) volume)
    (hpi : Integrable (fun x => H.polarize f x * Real.exp (-‖x‖ ^ 2)) volume)
    (hle : (∫ x, H.polarize f x * Real.exp (-‖x‖ ^ 2)) ≤
      ∫ x, f x * Real.exp (-‖x‖ ^ 2)) :
    ∀ᵐ x ∂volume, x ∈ H.nearSide → f (H.reflection x) ≤ f x := by
  let D : Space d → ℝ := fun x => (H.polarize f x - f x) * Real.exp (-‖x‖ ^ 2)
  have hD : Integrable D volume := by
    convert hpi.sub hfi using 1
    ext x
    dsimp [D]
    ring
  have hDr : Integrable (fun x => D (H.reflection x)) volume :=
    H.reflection_measurePreserving.integrable_comp_of_integrable hD
  have hDn : ∀ x, 0 ≤ D x + D (H.reflection x) :=
    H.gaussian_polarization_pair_nonneg f
  have hDint : (∫ x, D x) =
      (∫ x, H.polarize f x * Real.exp (-‖x‖ ^ 2)) -
        ∫ x, f x * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_sub hpi hfi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp [D]; ring
  have hzero : (∫ x, D x + D (H.reflection x)) = 0 := by
    apply le_antisymm
    · rw [integral_add hD hDr,
        H.reflection_measurePreserving.integral_comp
          H.reflectionIsometryEquiv.toHomeomorph.measurableEmbedding D, hDint]
      linarith
    · exact integral_nonneg hDn
  have heq : (fun x => D x + D (H.reflection x)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hDn (hD.add hDr)).mp hzero
  filter_upwards [heq] with x hx hxs
  exact (H.gaussian_polarization_pair_zero_iff f hxs).mp hx

/-- The moment of the whole-space Lp class uses the original Sobolev representative. -/
theorem gaussianMoment_wholeLp_eq_full_integral {d : ℕ} (R : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Polarization.WholeSobolev d p)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : Space d) R → sobolevUnderlying u x = 0) :
    gaussianMoment R p (wholeLp (sobolevUnderlying u)) =
      ∫ x, sobolevUnderlying u x * Real.exp (-‖x‖ ^ 2) := by
  rw [gaussianMoment_eq_integral]
  apply integral_congr_ae
  filter_upwards [wholeLp_ae (sobolevUnderlying u), hs] with x hx hsx
  rw [hx]
  by_cases hxB : x ∈ Metric.closedBall (0 : Space d) R
  · simp only [supportedGaussian, Set.indicator_of_mem hxB]
  · simp only [hsx hxB, zero_mul]

/-- Maximality in the orbit closure forces ordering for each allowed reflection. -/
theorem gaussian_maximizer_reflection_order
    (continuity : PolarizationExpected.Continuity)
    (properties : PolarizationExpected.Properties)
    {d : ℕ} (hd : 0 < d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ∞) {R : ℝ} (hR : 0 < R)
    (g w : SupportedClass d p R) :
    let K := closure ((fun u => wholeLp (sobolevUnderlying u)) ''
      finitePolarizationOrbit properties hd hp hptop hR g)
    wholeLp (sobolevUnderlying w.val) ∈ K →
    IsMaxOn (gaussianMoment R p) K (wholeLp (sobolevUnderlying w.val)) →
    ∀ H : Halfspace d, ∀ᵐ x ∂volume, x ∈ H.nearSide →
      sobolevUnderlying w.val (H.reflection x) ≤ sobolevUnderlying w.val x := by
  intro K hw hmax H
  let z := choosePolarization properties hd hp hptop hR H w
  have hz := (choosePolarization_spec properties hd hp hptop hR H w).1
  have hzK : wholeLp (sobolevUnderlying z.val) ∈ K :=
    finitePolarizationOrbit_closure_polarization continuity properties hd hp hptop hR g H w hw
  have hwm : MemLp (sobolevUnderlying w.val) p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevUnderlying w.val)
  have hzm : MemLp (sobolevUnderlying z.val) p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevUnderlying z.val)
  have hfi := gaussianProduct_integrable hwm w.property.2
  have hzi := gaussianProduct_integrable hzm z.property.2
  have heq : (fun x => sobolevUnderlying z.val x * Real.exp (-‖x‖ ^ 2)) =ᵐ[volume]
      (fun x => H.polarize (sobolevUnderlying w.val) x * Real.exp (-‖x‖ ^ 2)) := by
    filter_upwards [hz] with x hx
    rw [hx]
  apply gaussian_reflection_order_of_integral_le H (sobolevUnderlying w.val) hfi (hzi.congr heq)
  calc
    (∫ x, H.polarize (sobolevUnderlying w.val) x * Real.exp (-‖x‖ ^ 2)) =
        ∫ x, sobolevUnderlying z.val x * Real.exp (-‖x‖ ^ 2) :=
      integral_congr_ae heq.symm
    _ = gaussianMoment R p (wholeLp (sobolevUnderlying z.val)) :=
      (gaussianMoment_wholeLp_eq_full_integral R p z.val z.property.2).symm
    _ ≤ gaussianMoment R p (wholeLp (sobolevUnderlying w.val)) := hmax hzK
    _ = ∫ x, sobolevUnderlying w.val x * Real.exp (-‖x‖ ^ 2) :=
      gaussianMoment_wholeLp_eq_full_integral R p w.val w.property.2


end Rearrangement

/-- Centered positive superlevels are equivalent to a radial nonincreasing
representative for the supported nonnegative Sobolev class. -/
theorem rearrangement_radial_characterization : PolyaSzegoExpected.RadialCharacterization := by
  intro d hd p _ hp hptop R hR g hg
  exact ⟨hasCenteredSuperlevels_radial hd hg.1,
    radial_hasCenteredSuperlevels hd hR hg.2⟩

/-- Bounded-support Pólya–Szegő, with preservation of every positive
superlevel measure and the sharp Euclidean gradient bound. -/
theorem polya_szego : PolyaSzegoExpected.Existence := by
  have continuity : PolarizationExpected.Continuity := polarization_continuity
  have properties : PolarizationExpected.Properties := polarization_properties
  intro d hd p _ hp hptop R hR f hf
  let g : SupportedClass d p R := ⟨f, hf⟩
  obtain ⟨v, hv, hmax⟩ := exists_gaussian_maximizer properties hd hp hptop hR g
  obtain ⟨w, hwv, hw, hgrad⟩ :=
    finitePolarizationOrbit_closure_sobolev properties hd hp hptop hR g hv
  rw [← hwv] at hv hmax
  have horder := gaussian_maximizer_reflection_order continuity properties hd hp hptop hR
    g ⟨w, hw⟩ hv hmax
  have hcenter := supportedSobolev_centeredSuperlevels_of_reflection_order hd hR.le w hw horder
  refine ⟨w, hw, ⟨hw.1, hcenter, ?_⟩,
    hasCenteredSuperlevels_radial hd hw.1 hcenter, hgrad⟩
  have hlevels := finitePolarizationOrbit_closure_superlevels properties hd hp hptop hR g hv
  intro s hs
  calc
    volume {x | s < sobolevUnderlying w x} =
        volume {x | s < wholeLp (sobolevUnderlying w) x} := by
      apply measure_congr
      filter_upwards [wholeLp_ae (sobolevUnderlying w)] with x hx
      simp only [hx]
    _ = volume {x | s < sobolevUnderlying f x} := hlevels s hs


end P102.Sobolev
