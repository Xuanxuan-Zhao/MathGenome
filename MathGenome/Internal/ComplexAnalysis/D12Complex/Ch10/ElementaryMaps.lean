import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ElementaryMaps
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set
open scoped Topology
namespace D12Complex.ElementaryMaps

/- Definition exports are aliases of the canonical objects in the independent Spec. -/
namespace Definitions
abbrev upperHalfPlane : Set ℂ :=
  _root_.D12Complex.upperHalfPlane

abbrev unitDisk : Set ℂ :=
  _root_.D12Complex.unitDisk

abbrev cayley : ℂ → ℂ :=
  _root_.D12Complex.cayley

abbrev cayleyInverse : ℂ → ℂ :=
  _root_.D12Complex.cayleyInverse

abbrev horizontalStrip : ℝ → ℝ → Set ℂ :=
  _root_.D12Complex.horizontalStrip

abbrev sector : ℝ → ℝ → Set ℂ :=
  _root_.D12Complex.sector

abbrev sectorArg : ℝ → ℝ → ℂ → ℝ :=
  _root_.D12Complex.sectorArg

abbrev sectorLog : ℝ → ℝ → ℂ → ℂ :=
  _root_.D12Complex.sectorLog

abbrev sectorPower : ℝ → ℝ → ℂ → ℂ :=
  _root_.D12Complex.sectorPower

abbrev sectorPowerInverse : ℝ → ℝ → ℂ → ℂ :=
  _root_.D12Complex.sectorPowerInverse

end Definitions

theorem isOpen_horizontalStrip (a θ : ℝ) : IsOpen (horizontalStrip a θ) :=
  isOpen_Ioo.preimage Complex.continuous_im

theorem sector_eq_exp_image (a θ : ℝ) :
    sector a θ = Complex.exp '' horizontalStrip a θ := by
  ext w
  constructor
  · rintro ⟨r, hr, t, ht, ht', rfl⟩
    refine ⟨(Real.log r : ℂ) + (t : ℂ) * Complex.I, ?_, ?_⟩
    · simpa [horizontalStrip] using And.intro ht ht'
    · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Real.exp z.re, Real.exp_pos _, z.im, hz.1, hz.2, ?_⟩
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]

theorem isOpen_sector (a θ : ℝ) : IsOpen (sector a θ) := by
  rw [sector_eq_exp_image]
  exact Complex.isOpenMap_exp _ (isOpen_horizontalStrip a θ)

theorem centered_strip (a θ : ℝ) (hθ : θ ≤ 2 * Real.pi)
    {z : ℂ} (hz : z ∈ horizontalStrip a θ) :
    -Real.pi < (z - ((a + θ / 2 : ℝ) : ℂ) * Complex.I).im ∧
    (z - ((a + θ / 2 : ℝ) : ℂ) * Complex.I).im < Real.pi := by
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  rcases hz with ⟨h1, h2⟩
  constructor <;> linarith

theorem sectorLog_exp (a θ : ℝ) (hθ : θ ≤ 2 * Real.pi)
    {z : ℂ} (hz : z ∈ horizontalStrip a θ) :
    sectorLog a θ (Complex.exp z) = z := by
  unfold sectorLog
  rw [← Complex.exp_add]
  have hc := centered_strip a θ hθ hz
  rw [show z + -((a + θ / 2 : ℝ) : ℂ) * Complex.I =
      z - ((a + θ / 2 : ℝ) : ℂ) * Complex.I by ring,
    Complex.log_exp hc.1 hc.2.le]
  ring

theorem rotated_mem_slitPlane (a θ : ℝ) (hθ : θ ≤ 2 * Real.pi)
    {w : ℂ} (hw : w ∈ sector a θ) :
    w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [sector_eq_exp_image] at hw
  rcases hw with ⟨z, hz, rfl⟩
  rw [← Complex.exp_add]
  apply Complex.expOpenPartialHomeomorph.map_source
  change -Real.pi < (z + -((a + θ / 2 : ℝ) : ℂ) * Complex.I).im ∧
    (z + -((a + θ / 2 : ℝ) : ℂ) * Complex.I).im < Real.pi
  simpa only [sub_eq_add_neg, neg_mul] using centered_strip a θ hθ hz

theorem exponential_biholomorphicPair :
    Specs.D12Complex.Ch10.ElementaryMaps.exponential_biholomorphicPair_type := by
  intro a θ hpos hθ
  refine ⟨⟨isOpen_horizontalStrip a θ, fun z _ => ?_⟩,
    ⟨isOpen_sector a θ, fun w hw => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Exponential.E_eq_exp]; exact Complex.differentiableAt_exp
  · change DifferentiableAt ℂ (fun w => Complex.log
      (w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I)) +
      ((a + θ / 2 : ℝ) : ℂ) * Complex.I) w
    exact ((Complex.differentiableAt_log (rotated_mem_slitPlane a θ hθ hw)).comp w
      ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) w).mul_const _)).add_const _
  · rw [Exponential.E_eq_exp, sector_eq_exp_image]
    exact mapsTo_image _ _
  · intro w hw
    rw [sector_eq_exp_image] at hw
    rcases hw with ⟨z, hz, rfl⟩
    rwa [sectorLog_exp a θ hθ hz]
  · intro z hz
    rw [Exponential.E_eq_exp]
    exact sectorLog_exp a θ hθ hz
  · intro w hw
    rw [Exponential.E_eq_exp, sector_eq_exp_image] at *
    rcases hw with ⟨z, hz, rfl⟩
    rw [sectorLog_exp a θ hθ hz]

theorem sectorLog_polar :
    Specs.D12Complex.Ch10.ElementaryMaps.sectorLog_polar_type := by
  intro a θ w
  unfold sectorLog sectorArg Complex.log
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.I_im,
    sub_self, Real.exp_zero, mul_one]
  push_cast
  ring

theorem sectorArg_bounds :
    Specs.D12Complex.Ch10.ElementaryMaps.sectorArg_bounds_type := by
  intro a θ hpos hθ w hw
  have h := (exponential_biholomorphicPair a θ hpos hθ).2.2.2.1 hw
  rw [sectorLog_polar] at h
  simpa [horizontalStrip] using h

theorem sector_zero_pi :
    Specs.D12Complex.Ch10.ElementaryMaps.sector_zero_pi_type := by
  ext w
  constructor
  · rintro ⟨r, hr, t, ht, ht', rfl⟩
    change 0 < ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, Complex.mul_re, sub_zero, Real.exp_zero, one_mul]
    exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht (by simpa using ht'))
  · intro hw
    change 0 < w.im at hw
    have hn : w ≠ 0 := by rintro rfl; simp at hw
    have ha : 0 < w.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hw.le)
      (by intro h; have := Complex.arg_eq_zero_iff.mp h.symm; simp_all)
    refine ⟨‖w‖, norm_pos_iff.mpr hn, w.arg, ha,
      by simpa using Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne'), ?_⟩
    rw [Complex.exp_mul_I, Complex.norm_mul_cos_add_sin_mul_I]

theorem cayley_denominator {z : ℂ} (hz : z ∈ upperHalfPlane) : z + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  change 0 < z.im at hz
  linarith

theorem cayley_mapsTo : MapsTo cayley upperHalfPlane unitDisk := by
  intro z hz
  have hd := cayley_denominator hz
  change ‖(z - Complex.I) / (z + Complex.I)‖ < 1
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have hn : Complex.normSq (z - Complex.I) < Complex.normSq (z + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
      Complex.sub_im, Complex.I_im, Complex.add_re, add_zero, Complex.add_im]
    change 0 < z.im at hz
    nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]

theorem cayleyInverse_denominator {w : ℂ} (hw : w ∈ unitDisk) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.mp h).symm
  subst w
  simp [unitDisk] at hw

theorem cayleyInverse_im (w : ℂ) :
    (cayleyInverse w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  simp [cayleyInverse, Complex.div_im, Complex.normSq_apply]
  ring

theorem cayleyInverse_mapsTo : MapsTo cayleyInverse unitDisk upperHalfPlane := by
  intro w hw
  change 0 < (cayleyInverse w).im
  rw [cayleyInverse_im]
  apply div_pos
  · have h : ‖w‖ < 1 := hw
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  · exact Complex.normSq_pos.mpr (cayleyInverse_denominator hw)

theorem cayley_left_inverse : LeftInvOn cayleyInverse cayley upperHalfPlane := by
  intro z hz
  have hd := cayley_denominator hz
  have hi := cayleyInverse_denominator (cayley_mapsTo hz)
  unfold cayleyInverse cayley at *
  field_simp
  ring

theorem cayley_right_inverse : RightInvOn cayleyInverse cayley unitDisk := by
  intro w hw
  have hd := cayleyInverse_denominator hw
  have hi := cayley_denominator (cayleyInverse_mapsTo hw)
  unfold cayleyInverse cayley at *
  field_simp
  ring

theorem cayley_biholomorphicPair :
    Specs.D12Complex.Ch10.ElementaryMaps.cayley_biholomorphicPair_type := by
  refine ⟨⟨isOpen_lt continuous_const Complex.continuous_im, ?_⟩,
    ⟨isOpen_lt continuous_norm continuous_const, ?_⟩,
    cayley_mapsTo, cayleyInverse_mapsTo, cayley_left_inverse, cayley_right_inverse⟩
  · intro z hz
    exact (differentiableAt_id.sub_const _).div (differentiableAt_id.add_const _)
      (cayley_denominator hz)
  · intro w hw
    exact ((differentiableAt_const _).mul (differentiableAt_const _ |>.add
      differentiableAt_id)).div ((differentiableAt_const _).sub differentiableAt_id)
      (cayleyInverse_denominator hw)

theorem scale_strip (a θ : ℝ) (hθ : 0 < θ) {z : ℂ}
    (hz : z ∈ horizontalStrip a θ) :
    ((Real.pi / θ : ℝ) : ℂ) * (z - (a : ℂ) * Complex.I) ∈ horizontalStrip 0 Real.pi := by
  have hs : 0 < Real.pi / θ := div_pos Real.pi_pos hθ
  have h1 : 0 < (Real.pi / θ) * (z.im - a) := mul_pos hs (sub_pos.mpr hz.1)
  have ht : z.im - a < θ := by linarith [hz.2]
  have h2 := mul_lt_mul_of_pos_left ht hs
  rw [div_mul_cancel₀ _ hθ.ne'] at h2
  simpa [horizontalStrip] using And.intro h1 h2

theorem unscale_strip (a θ : ℝ) (hθ : 0 < θ) {z : ℂ}
    (hz : z ∈ horizontalStrip 0 Real.pi) :
    (a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) * z ∈ horizontalStrip a θ := by
  have hs : 0 < θ / Real.pi := div_pos hθ Real.pi_pos
  have h1 : 0 < (θ / Real.pi) * z.im := mul_pos hs hz.1
  have h2 := mul_lt_mul_of_pos_left hz.2 hs
  rw [zero_add, div_mul_cancel₀ _ Real.pi_ne_zero] at h2
  simpa [horizontalStrip] using
    And.intro (show a < a + (θ / Real.pi) * z.im by linarith)
      (show a + (θ / Real.pi) * z.im < a + θ by linarith)

theorem scale_unscale (a θ : ℝ) (hθ : θ ≠ 0) (z : ℂ) :
    ((Real.pi / θ : ℝ) : ℂ) *
      ((a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) * z - (a : ℂ) * Complex.I) = z := by
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hθ]
  ring

theorem unscale_scale (a θ : ℝ) (hθ : θ ≠ 0) (z : ℂ) :
    (a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) *
      (((Real.pi / θ : ℝ) : ℂ) * (z - (a : ℂ) * Complex.I)) = z := by
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hθ]
  ring

theorem sectorPower_mapsTo (a θ : ℝ) (hpos : 0 < θ) (hθ : θ < 2 * Real.pi) :
    MapsTo (sectorPower a θ) (sector a θ) upperHalfPlane := by
  intro z hz
  rw [← sector_zero_pi]
  exact (exponential_biholomorphicPair 0 Real.pi Real.pi_pos (by linarith [Real.pi_pos])).2.2.1
    (scale_strip a θ hpos ((exponential_biholomorphicPair a θ hpos hθ.le).2.2.2.1 hz))

theorem sectorPowerInverse_mapsTo (a θ : ℝ) (hpos : 0 < θ) (hθ : θ < 2 * Real.pi) :
    MapsTo (sectorPowerInverse a θ) upperHalfPlane (sector a θ) := by
  intro w hw
  rw [← sector_zero_pi] at hw
  exact (exponential_biholomorphicPair a θ hpos hθ.le).2.2.1
    (unscale_strip a θ hpos
      ((exponential_biholomorphicPair 0 Real.pi Real.pi_pos (by linarith [Real.pi_pos])).2.2.2.1 hw))

theorem sectorPower_left_inverse (a θ : ℝ) (hpos : 0 < θ) (hθ : θ < 2 * Real.pi) :
    LeftInvOn (sectorPowerInverse a θ) (sectorPower a θ) (sector a θ) := by
  intro z hz
  have hb := exponential_biholomorphicPair a θ hpos hθ.le
  have hp := exponential_biholomorphicPair 0 Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  unfold sectorPowerInverse sectorPower powerWithLog
  dsimp only
  rw [hp.2.2.2.2.1 (scale_strip a θ hpos (hb.2.2.2.1 hz)),
    unscale_scale a θ hpos.ne']
  exact hb.2.2.2.2.2 hz

theorem sectorPower_right_inverse (a θ : ℝ) (hpos : 0 < θ) (hθ : θ < 2 * Real.pi) :
    RightInvOn (sectorPowerInverse a θ) (sectorPower a θ) upperHalfPlane := by
  intro w hw
  rw [← sector_zero_pi] at hw
  have hb := exponential_biholomorphicPair a θ hpos hθ.le
  have hp := exponential_biholomorphicPair 0 Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  unfold sectorPowerInverse sectorPower powerWithLog
  dsimp only
  rw [hb.2.2.2.2.1 (unscale_strip a θ hpos (hp.2.2.2.1 hw)),
    scale_unscale a θ hpos.ne']
  exact hp.2.2.2.2.2 hw

theorem sectorPower_rotation :
    Specs.D12Complex.Ch10.ElementaryMaps.sectorPower_rotation_type := by
  intro a θ z
  unfold sectorPower powerWithLog
  rw [← Exponential.E_add]
  congr 1
  ring

theorem sectorPower_biholomorphicPair :
    Specs.D12Complex.Ch10.ElementaryMaps.sectorPower_biholomorphicPair_type := by
  intro a θ hpos hθ
  have hb := exponential_biholomorphicPair a θ hpos hθ.le
  have hp := exponential_biholomorphicPair 0 Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  refine ⟨⟨isOpen_sector a θ, ?_⟩, ⟨isOpen_lt continuous_const Complex.continuous_im, ?_⟩,
    sectorPower_mapsTo a θ hpos hθ, sectorPowerInverse_mapsTo a θ hpos hθ,
    sectorPower_left_inverse a θ hpos hθ, sectorPower_right_inverse a θ hpos hθ⟩
  · intro z hz
    change DifferentiableAt ℂ (fun z => E (_ * (sectorLog a θ z - _))) z
    rw [Exponential.E_eq_exp]
    exact Complex.differentiableAt_exp.comp z ((hb.2.1.2 z hz).sub_const _ |>.const_mul _)
  · intro w hw
    rw [← sector_zero_pi] at hw
    change DifferentiableAt ℂ (fun w => E (_ + _ * sectorLog 0 Real.pi w)) w
    rw [Exponential.E_eq_exp]
    exact Complex.differentiableAt_exp.comp w ((hp.2.1.2 w hw).const_mul _ |>.const_add _)

/-- The only exponential period smaller in modulus than 2π in imaginary part is zero. -/
theorem exp_injective_of_im_difference {x y : ℂ}
    (hlo : -(2 * Real.pi) < x.im - y.im)
    (hhi : x.im - y.im < 2 * Real.pi) (he : Complex.exp x = Complex.exp y) : x = y := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hn
  simp at him
  have hn0 : n = 0 := by
    by_contra hn0
    rcases lt_or_gt_of_ne hn0 with hneg | hpos
    · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [Real.pi_pos]
    · have hle : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [Real.pi_pos]
  simpa [hn0] using hn

theorem sector_boundary_excluded :
    Specs.D12Complex.Ch10.ElementaryMaps.sector_boundary_excluded_type := by
  intro a θ hpos hθ r hr
  have hb : ∀ b : ℝ, (b = a ∨ b = a + θ) →
      (r : ℂ) * Complex.exp ((b : ℂ) * Complex.I) ∉ sector a θ := by
    intro b hb hw
    rw [sector_eq_exp_image] at hw
    rcases hw with ⟨z, hz, he⟩
    have hp : Complex.exp ((Real.log r : ℂ) + (b : ℂ) * Complex.I) =
        (r : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    have him : ((Real.log r : ℂ) + (b : ℂ) * Complex.I).im = b := by simp
    have heq := exp_injective_of_im_difference (x := z)
      (y := (Real.log r : ℂ) + (b : ℂ) * Complex.I) (by
        rw [him]; rcases hb with rfl | rfl <;> linarith [hz.1, hz.2, Real.pi_pos]) (by
        rw [him]; rcases hb with rfl | rfl <;> linarith [hz.1, hz.2, Real.pi_pos])
      (he.trans hp.symm)
    have hi : z.im = b := (congrArg Complex.im heq).trans him
    rcases hb with rfl | rfl <;> linarith [hz.1, hz.2]
  exact ⟨hb a (Or.inl rfl), hb (a + θ) (Or.inr rfl)⟩

end D12Complex.ElementaryMaps
