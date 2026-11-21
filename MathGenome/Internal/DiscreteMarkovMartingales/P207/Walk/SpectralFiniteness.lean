import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.SpectralFiniteness
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.LatticeLocalBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators

namespace P207.Walk.SpectralFiniteness

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem continuous_phi {d : ℕ} : Continuous (phi (d := d)) := by
  unfold phi
  exact continuous_const.mul (continuous_finsetSum _ fun j _ =>
    Real.Angle.continuous_cos.comp (continuous_apply j))

theorem abs_phi_le_one {d : ℕ} [NeZero d] (t : Torus d) : |phi t| ≤ 1 := by
  calc
    |phi t| = (d : ℝ)⁻¹ * |∑ j : Fin d, Real.Angle.cos (t j)| := by
      rw [phi, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d : ℝ)⁻¹)]
    _ ≤ (d : ℝ)⁻¹ * ∑ j : Fin d, |Real.Angle.cos (t j)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ _j : Fin d, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => abs_le.mpr
        ⟨LatticeLocalBounds.neg_one_le_angle_cos (t j), LatticeLocalBounds.angle_cos_le_one (t j)⟩)
    _ = 1 := by simp [NeZero.ne d]

/-- A fundamental cube in Euclidean coordinates, with the half-open convention
used by the measure-preserving circle quotient. -/
def angularCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {u | ∀ j, u j ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)}

theorem torus_volume_eq (d : ℕ) :
    (volume : Measure (Torus d)) =
      ENNReal.ofReal (2 * Real.pi) ^ d • torusMeasure d := by
  change Measure.pi (fun _ : Fin d => (volume : Measure (AddCircle (2 * Real.pi)))) = _
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, torusMeasure, Measure.pi_pi]
  simp only [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

theorem angularLift_measurePreserving {d : ℕ} (center : Torus d) :
    MeasurePreserving (angularLift center)
      (volume.restrict (angularCube d)) (volume : Measure (Torus d)) := by
  have hp := measurePreserving_pi
    (fun _ : Fin d => volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
    (fun _ : Fin d => (volume : Measure (AddCircle (2 * Real.pi))))
    (fun _ => AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi))
  rw [← Measure.restrict_pi_pi] at hp
  have he := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.univ.pi (fun _ : Fin d => Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  have hm := (measurePreserving_add_left (volume : Measure (Torus d)) center).comp (hp.comp he)
  have hc : (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) ⁻¹'
      (Set.univ.pi (fun _ : Fin d => Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) =
      angularCube d := by
    ext u
    simp [angularCube]
  rw [hc] at hm
  exact hm

theorem angularLift_injOn {d : ℕ} (center : Torus d) :
    InjOn (angularLift center) (angularCube d) := by
  intro u hu v hv h
  apply PiLp.ext
  intro j
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hu j) (hv j)).mp
    (add_left_cancel (congrFun h j))

theorem ball_subset_cube {d : ℕ} {r : ℝ} (hr : r < Real.pi) :
    ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ angularCube d := by
  intro u hu j
  have hn : ‖u‖ < r := by simpa using hu
  have hj := (PiLp.norm_apply_le u j).trans_lt (hn.trans hr)
  rw [Real.norm_eq_abs] at hj
  rcases abs_lt.mp hj with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- Change of variables on a measurable subset of the fundamental cube. -/
theorem lintegral_angularLift {d : ℕ} (center : Torus d)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : s ⊆ angularCube d)
    (hi : MeasurableSet (angularLift center '' s))
    {f : Torus d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t in angularLift center '' s, f t ∂(volume : Measure (Torus d)) =
      ∫⁻ u in s, f (angularLift center u) := by
  have hm := (angularLift_measurePreserving center).setLIntegral_comp_preimage hi hf
  rw [Measure.restrict_restrict
    ((angularLift_measurePreserving center).measurable hi)] at hm
  have he : angularLift center ⁻¹' (angularLift center '' s) ∩ angularCube d = s := by
    ext u
    constructor
    · rintro ⟨⟨v, hv, hvu⟩, hu⟩
      have := angularLift_injOn center (hs hv) hu hvu
      exact this ▸ hv
    · intro hu
      exact ⟨⟨u, hu, rfl⟩, hs hu⟩
  rw [he] at hm
  exact hm.symm

/-- The denominator controls the squared Euclidean distance in either peak chart. -/
theorem denominator_lower {d : ℕ} [NeZero d] {a : ℝ} {t : Torus d}
    {u : EuclideanSpace ℝ (Fin d)} (h : a * ‖u‖ ^ 2 ≤ 1 - |phi t|) :
    a * ‖u‖ ^ 2 ≤ 1 - phi t ^ 2 := by
  have hp := abs_phi_le_one t
  have hn := abs_nonneg (phi t)
  have hs := sq_abs (phi t)
  nlinarith

/-- The real reciprocal is integrable in a peak chart in dimension greater than two.
Its value at the origin will be handled separately when passing to ENNReal. -/
theorem integrable_chart {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (center : Torus d) {a r : ℝ} (ha : 0 < a)
    (hbound : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ < r →
      a * ‖u‖ ^ 2 ≤ 1 - |phi (angularLift center u)|) :
    IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      (1 - phi (angularLift center u) ^ 2)⁻¹) (ball 0 r) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hm : Measurable (angularLift center) := (angularLift_measurePreserving center).measurable
  apply integrableOn_ball_of_norm_le_rpow (μ := volume)
    (C := a⁻¹) (α := 2) (by omega) (by rw [hdim]; exact_mod_cast (by omega : 2 < d))
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))),
      ae_restrict_mem measurableSet_ball] with u hu hur
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hlow := denominator_lower (hbound u (by simpa using hur))
    have hpos : 0 < a * ‖u‖ ^ 2 := mul_pos ha (sq_pos_of_pos hn)
    have hp : 0 < 1 - phi (angularLift center u) ^ 2 := hpos.trans_le hlow
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    calc
      _ ≤ (a * ‖u‖ ^ 2)⁻¹ := inv_anti₀ hpos hlow
      _ = a⁻¹ * ‖u‖ ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (norm_nonneg u), Real.rpow_two, mul_inv_rev, mul_comm]
  · exact ((measurable_const.sub ((continuous_phi.measurable.comp hm).pow_const 2)).inv).aestronglyMeasurable

/-- The extended reciprocal also has a finite integral in each coordinate ball.
Lebesgue measure has no atom at the coordinate origin. -/
theorem finite_chart {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (center : Torus d) {a r : ℝ} (ha : 0 < a)
    (hbound : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ < r →
      a * ‖u‖ ^ 2 ≤ 1 - |phi (angularLift center u)|) :
    (∫⁻ u in ball (0 : EuclideanSpace ℝ (Fin d)) r,
      (ENNReal.ofReal (1 - phi (angularLift center u) ^ 2))⁻¹) < ⊤ := by
  have hi := integrable_chart hd center ha hbound
  have he : (fun u : EuclideanSpace ℝ (Fin d) =>
      (ENNReal.ofReal (1 - phi (angularLift center u) ^ 2))⁻¹) =ᵐ[volume.restrict (ball 0 r)]
      (fun u => ENNReal.ofReal ‖(1 - phi (angularLift center u) ^ 2)⁻¹‖) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))),
      ae_restrict_mem measurableSet_ball] with u hu hur
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hlow := denominator_lower (hbound u (by simpa using hur))
    have hp : 0 < 1 - phi (angularLift center u) ^ 2 :=
      (mul_pos ha (sq_pos_of_pos hn)).trans_le hlow
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), ENNReal.ofReal_inv_of_pos hp]
  rw [lintegral_congr_ae he]
  exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

theorem measurable_reciprocal {d : ℕ} :
    Measurable (fun t : Torus d => (ENNReal.ofReal (1 - phi t ^ 2))⁻¹) :=
  (ENNReal.measurable_ofReal.comp (continuous_const.sub (continuous_phi.pow 2)).measurable).inv

/-- Both actual peaks possess open neighborhoods of finite integral. -/
theorem finite_peak_neighborhood {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (center : Torus d) (hc : center = 0 ∨ center = piPoint d) :
    ∃ U : Set (Torus d), IsOpen U ∧ center ∈ U ∧
      (∫⁻ t in U, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹
        ∂(volume : Measure (Torus d))) < ⊤ := by
  obtain ⟨e, a, b, η, ha, hb, hη, he, he0, hes, hq⟩ :=
    LatticeLocalBounds.local_quadratic d center hc
  let r : ℝ := min η (Real.pi / 2)
  have hr : 0 < r := lt_min hη (by positivity)
  have hrη : r ≤ η := min_le_left _ _
  have hrpi : r < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hsub : ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ e.source := by
    apply Subset.trans _ hes
    intro u hu
    simp only [mem_closedBall, dist_zero_right]
    exact (show ‖u‖ < r by simpa using hu).le.trans hrη
  have himage : e '' ball (0 : EuclideanSpace ℝ (Fin d)) r =
      angularLift center '' ball 0 r := by
    congr 1
    exact funext he
  have hopen : IsOpen (angularLift center '' ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [← himage]
    exact e.isOpen_image_of_subset_source isOpen_ball hsub
  refine ⟨angularLift center '' ball (0 : EuclideanSpace ℝ (Fin d)) r, hopen, ?_, ?_⟩
  · refine ⟨0, by simpa using hr, ?_⟩
    rw [← he, he0]
  · rw [lintegral_angularLift center (ball_subset_cube hrpi) hopen.measurableSet measurable_reciprocal]
    apply finite_chart hd center ha
    intro u hu
    rw [← he]
    exact (hq u (hu.le.trans hrη)).1

/-- The reciprocal is continuous and integrable on a compact set avoiding the peaks. -/
theorem finite_compact_complement {d : ℕ} [NeZero d] (K : Set (Torus d))
    (hK : IsCompact K) (hno : ∀ t ∈ K, t ≠ 0 ∧ t ≠ piPoint d) :
    (∫⁻ t in K, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹
      ∂(volume : Measure (Torus d))) < ⊤ := by
  have hpos : ∀ t ∈ K, 0 < 1 - phi t ^ 2 := by
    intro t ht
    have hne : |phi t| ≠ 1 := by
      intro h
      rcases (LatticeLocalBounds.peaks d t).mp h with h | h
      · exact (hno t ht).1 h
      · exact (hno t ht).2 h
    have hlt : |phi t| < 1 := lt_of_le_of_ne (abs_phi_le_one t) hne
    nlinarith [sq_abs (phi t), abs_nonneg (phi t)]
  have hi : IntegrableOn (fun t : Torus d => (1 - phi t ^ 2)⁻¹) K volume :=
    ((continuous_const.sub (continuous_phi.pow 2)).continuousOn.inv₀
      (fun t ht => (hpos t ht).ne')).integrableOn_compact hK
  have he : (fun t : Torus d => (ENNReal.ofReal (1 - phi t ^ 2))⁻¹) =ᵐ[volume.restrict K]
      (fun t => ENNReal.ofReal ‖(1 - phi t ^ 2)⁻¹‖) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos t ht)),
      ENNReal.ofReal_inv_of_pos (hpos t ht)]
  rw [lintegral_congr_ae he]
  exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

/-- Finiteness of the spectral integral for all positive dimensions at least three,
with the literal normalized Haar measure of the shared interface. -/
theorem spectral_finiteness : SpectralFinitenessSpec.spectral_finiteness := by
  intro d _ hd
  obtain ⟨U, hU, h0, hiU⟩ := finite_peak_neighborhood hd 0 (Or.inl rfl)
  obtain ⟨V, hV, hπ, hiV⟩ := finite_peak_neighborhood hd (piPoint d) (Or.inr rfl)
  have hK : IsCompact ((U ∪ V)ᶜ) := (hU.union hV).isClosed_compl.isCompact
  have hiK := finite_compact_complement ((U ∪ V)ᶜ) hK (by
    intro t ht
    constructor
    · intro h
      subst t
      exact ht (Or.inl h0)
    · intro h
      subst t
      exact ht (Or.inr hπ))
  have hiUV : (∫⁻ t in U ∪ V, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹
      ∂(volume : Measure (Torus d))) < ⊤ :=
    (lintegral_union_le _ U V).trans_lt (ENNReal.add_lt_top.mpr ⟨hiU, hiV⟩)
  have hi : (∫⁻ t : Torus d, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹
      ∂(volume : Measure (Torus d))) < ⊤ := by
    rw [← lintegral_add_compl _ (hU.union hV).measurableSet]
    exact ENNReal.add_lt_top.mpr ⟨hiUV, hiK⟩
  rw [torus_volume_eq, lintegral_smul_measure] at hi
  have hC : ENNReal.ofReal (2 * Real.pi) ^ d ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  by_contra h
  have ht : (∫⁻ t : Torus d, (ENNReal.ofReal (1 - phi t ^ 2))⁻¹
      ∂torusMeasure d) = ⊤ := top_unique (le_of_not_gt h)
  rw [ht, smul_eq_mul, ENNReal.mul_top hC] at hi
  exact (lt_irrefl ⊤) hi

end
end P207.Walk.SpectralFiniteness
