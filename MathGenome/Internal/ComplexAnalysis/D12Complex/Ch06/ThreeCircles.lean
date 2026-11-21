import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.ThreeCircles
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Hadamard three circles (paper.tex:1528–1559). Apply the zero-inclusive
three-lines theorem to `w ↦ f (exp w)`. The exponential maps the closed
strip between log radii into a compact subannulus, supplying its bound.
A maximum point on the intermediate circle can be lifted using any
complex logarithm value; no logarithm branch on the annulus is assumed.
Positivity follows by propagating a hypothetical vanishing circle using
the multiplicative inequality. Finally take logarithms and prove Jensen
convexity in the logarithmic radius variable.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.ThreeCircles

abbrev circleMaximum := maximumModulus

private lemma sphere_subset {r₀ r₃ t : ℝ} (h₀ : r₀ < t) (h₃ : t < r₃) :
    sphere (0 : ℂ) t ⊆ {z : ℂ | r₀ < ‖z‖ ∧ ‖z‖ < r₃} := by
  intro z hz
  have : ‖z‖ = t := by simpa [mem_sphere, dist_zero_right] using hz
  simpa [this] using And.intro h₀ h₃

private lemma continuousOn_sphere {f : ℂ → ℂ} {r₀ r₃ t : ℝ}
    (hf : HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f)
    (h₀ : r₀ < t) (h₃ : t < r₃) : ContinuousOn (fun z => ‖f z‖) (sphere 0 t) :=
  fun z hz => (hf.2 z (sphere_subset h₀ h₃ hz)).continuousAt.norm.continuousWithinAt

private lemma maximum_bound {f : ℂ → ℂ} {r₀ r₃ t : ℝ}
    (hf : HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f)
    (h₀ : r₀ < t) (h₃ : t < r₃) {z : ℂ} (hz : ‖z‖ = t) :
    ‖f z‖ ≤ maximumModulus f t := by
  apply le_csSup ((isCompact_sphere 0 t).bddAbove_image (continuousOn_sphere hf h₀ h₃))
  exact mem_image_of_mem _ (by simpa [mem_sphere, dist_zero_right] using hz)

theorem maximum_attained :
    Specs.D12Complex.Ch06.ThreeCircles.maximum_attained_type := by
  intro f r₀ r₃ t hf ht h₀ h₃
  have hne : (sphere (0 : ℂ) t).Nonempty :=
    ⟨(t : ℂ), by simp [abs_of_pos ht]⟩
  obtain ⟨z, hz, hm⟩ := (isCompact_sphere 0 t).exists_isMaxOn hne
    (continuousOn_sphere hf h₀ h₃)
  have hzt : ‖z‖ = t := by simpa [mem_sphere, dist_zero_right] using hz
  refine ⟨z, hzt, le_antisymm (maximum_bound hf h₀ h₃ hzt) ?_, ?_⟩
  · exact csSup_le (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hm hw)
  · intro w hw
    exact hm (by simpa [mem_sphere, dist_zero_right] using hw)

theorem maximum_zero :
    Specs.D12Complex.Ch06.ThreeCircles.maximum_zero_type := by
  intro f r₀ r₃ t hf hz ht h₀ h₃
  obtain ⟨z, hzt, hm, _⟩ := maximum_attained f r₀ r₃ t hf ht h₀ h₃
  rw [← hm, hz (by simpa [hzt] using And.intro h₀ h₃), norm_zero]

private lemma three_circles_powers {f : ℂ → ℂ} {r₀ r₁ r r₂ r₃ : ℝ}
    (hf : HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f)
    (hpos : 0 < r₁) (h₀ : r₀ < r₁) (h₁ : r₁ < r) (h₂ : r < r₂) (h₃ : r₂ < r₃) :
    maximumModulus f r ≤
      (maximumModulus f r₁) ^ (1 - (Real.log r - Real.log r₁) /
        (Real.log r₂ - Real.log r₁)) *
      (maximumModulus f r₂) ^ ((Real.log r - Real.log r₁) /
        (Real.log r₂ - Real.log r₁)) := by
  have hr : 0 < r := hpos.trans h₁
  have hr₂ : 0 < r₂ := hr.trans h₂
  let S := Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₂)
  let C := Complex.HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₂)
  have hC : IsClosed C := isClosed_Icc.preimage Complex.continuous_re
  have hSC : S ⊆ C := fun _ hw => ⟨hw.1.le, hw.2.le⟩
  have hexp : ∀ w ∈ C, r₁ ≤ ‖Complex.exp w‖ ∧ ‖Complex.exp w‖ ≤ r₂ := by
    intro w hw
    rw [Complex.norm_exp]
    exact ⟨by simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hw.1,
      by simpa [Real.exp_log hr₂] using Real.exp_le_exp.mpr hw.2⟩
  have hd : ∀ w ∈ C, DifferentiableAt ℂ (fun w => f (Complex.exp w)) w := by
    intro w hw
    have he := hexp w hw
    exact (hf.2 _ ⟨h₀.trans_le he.1, he.2.trans_lt h₃⟩).comp w
      Complex.differentiable_exp.differentiableAt
  have hdc : DiffContOnCl ℂ (fun w => f (Complex.exp w)) S := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact (hd w (closure_minimal hSC hC hw)).differentiableWithinAt
  let K : Set ℂ := {z | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ) r₂).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      simpa [mem_closedBall, dist_zero_right] using hz.2
  have hcont : ContinuousOn (fun z => ‖f z‖) K := fun z hz =>
    (hf.2 z ⟨h₀.trans_le hz.1, hz.2.trans_lt h₃⟩).continuousAt.norm.continuousWithinAt
  have hB : BddAbove ((norm ∘ (fun w => f (Complex.exp w))) '' C) := by
    apply (hK.bddAbove_image hcont).mono
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨Complex.exp w, hexp w hw, rfl⟩
  obtain ⟨z, hz, hm, _⟩ := maximum_attained f r₀ r₃ r hf hr (h₀.trans h₁) (h₂.trans h₃)
  have hzn : z ≠ 0 := by intro he; simp [he] at hz; linarith
  have hlog : (Complex.log z).re = Real.log r := by rw [Complex.log_re, hz]
  have hbound := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := fun w => f (Complex.exp w))
    (Real.log_lt_log hpos (h₁.trans h₂))
    (z := Complex.log z) (by
      change Real.log r₁ ≤ (Complex.log z).re ∧ (Complex.log z).re ≤ Real.log r₂
      rw [hlog]
      exact ⟨(Real.log_lt_log hpos h₁).le,
        (Real.log_lt_log hr h₂).le⟩)
    hdc hB
    (a := maximumModulus f r₁) (b := maximumModulus f r₂)
    (by
      intro w hw
      apply maximum_bound hf h₀ ((h₁.trans h₂).trans h₃)
      rw [Complex.norm_exp, show w.re = Real.log r₁ from hw, Real.exp_log hpos])
    (by
      intro w hw
      apply maximum_bound hf (h₀.trans (h₁.trans h₂)) h₃
      rw [Complex.norm_exp, show w.re = Real.log r₂ from hw, Real.exp_log hr₂])
  simpa only [Complex.exp_log hzn, hm, hlog] using hbound

private lemma weights {r₁ r r₂ : ℝ} (hpos : 0 < r₁) (h₁ : r₁ < r) (h₂ : r < r₂) :
    Real.log (r₂ / r) / Real.log (r₂ / r₁) =
      1 - (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) ∧
    1 - Real.log (r₂ / r) / Real.log (r₂ / r₁) =
      (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) ∧
    Real.log (r / r₁) / Real.log (r₂ / r₁) =
      (Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁) := by
  have hr := hpos.trans h₁
  have hr₂ := hr.trans h₂
  have hn : Real.log r₂ - Real.log r₁ ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.log_lt_log hpos (h₁.trans h₂)))
  rw [Real.log_div hr₂.ne' hr.ne', Real.log_div hr₂.ne' hpos.ne',
    Real.log_div hr.ne' hpos.ne']
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · rfl

theorem three_circles_multiplicative :
    Specs.D12Complex.Ch06.ThreeCircles.three_circles_multiplicative_type := by
  intro f r₀ r₁ r r₂ r₃ hf hpos h₀ h₁ h₂ h₃
  rw [(weights hpos h₁ h₂).2.1, (weights hpos h₁ h₂).1]
  exact three_circles_powers hf hpos h₀ h₁ h₂ h₃

/-- A vanishing circle forces vanishing at every nonzero point of the annulus.
The zero-inclusive three-lines estimate proves this directly. -/
private lemma zero_of_maximum_zero {f : ℂ → ℂ} {r₀ r₃ t : ℝ}
    (hf : HolomorphicOn {z | r₀ < ‖z‖ ∧ ‖z‖ < r₃} f)
    (ht : 0 < t) (h₀ : r₀ < t) (h₃ : t < r₃)
    (hm : maximumModulus f t = 0) {z : ℂ}
    (hz : r₀ < ‖z‖ ∧ ‖z‖ < r₃) (hzn : z ≠ 0) : f z = 0 := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hzn
  have hle : ‖f z‖ ≤ 0 := by
    rcases lt_trichotomy ‖z‖ t with hzt | hzt | hzt
    · obtain ⟨s, hs, hsz⟩ := exists_between (max_lt hz.1 hp)
      have hspos : 0 < s := (le_max_right _ _).trans_lt hs
      have hs₀ : r₀ < s := (le_max_left _ _).trans_lt hs
      have h := three_circles_powers hf hspos hs₀ hsz hzt h₃
      have he : 0 < (Real.log ‖z‖ - Real.log s) / (Real.log t - Real.log s) :=
        div_pos (sub_pos.mpr (Real.log_lt_log hspos hsz))
          (sub_pos.mpr (Real.log_lt_log hspos (hsz.trans hzt)))
      rw [hm, Real.zero_rpow he.ne', mul_zero] at h
      exact (maximum_bound hf hz.1 hz.2 rfl).trans h
    · simpa [hm, hzt] using maximum_bound hf hz.1 hz.2 (z := z) rfl
    · obtain ⟨s, hzs, hs⟩ := exists_between hz.2
      have h := three_circles_powers hf ht h₀ hzt hzs hs
      have he : 0 < 1 - (Real.log ‖z‖ - Real.log t) / (Real.log s - Real.log t) := by
        have hd : 0 < Real.log s - Real.log t :=
          sub_pos.mpr (Real.log_lt_log ht (hzt.trans hzs))
        have hn : Real.log ‖z‖ - Real.log t < Real.log s - Real.log t := by
          linarith [Real.log_lt_log hp hzs]
        exact sub_pos.mpr ((div_lt_one hd).mpr hn)
      rw [hm, Real.zero_rpow he.ne', zero_mul] at h
      exact (maximum_bound hf hz.1 hz.2 rfl).trans h
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

theorem maximum_positive :
    Specs.D12Complex.Ch06.ThreeCircles.maximum_positive_type := by
  intro f r₀ r₃ t hf hn ht h₀ h₃
  obtain ⟨a, ha, hfa⟩ := hn
  have hnonneg : 0 ≤ maximumModulus f t := by
    obtain ⟨z, _, hm, _⟩ := maximum_attained f r₀ r₃ t hf ht h₀ h₃
    rw [← hm]; exact norm_nonneg _
  apply lt_of_le_of_ne hnonneg
  intro he
  have hm := he.symm
  by_cases han : a ≠ 0
  · exact hfa (zero_of_maximum_zero hf ht h₀ h₃ hm ha han)
  · have ha0 : a = 0 := not_ne_iff.mp han
    subst a
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        (r₀ < ‖z‖ ∧ ‖z‖ < r₃) ∧ f z ≠ 0 := by
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      exact Filter.Eventually.and (hf.1.mem_nhds ha)
        ((hf.2 0 ha).continuousAt.eventually_ne hfa)
    obtain ⟨z, hz, hne⟩ := (hev.and self_mem_nhdsWithin).exists
    exact hz.2 (zero_of_maximum_zero hf ht h₀ h₃ hm hz.1 (by simpa using hne))

theorem three_circles_log :
    Specs.D12Complex.Ch06.ThreeCircles.three_circles_log_type := by
  intro f r₀ r₁ r r₂ r₃ hf hn hpos h₀ h₁ h₂ h₃
  have hp₁ := maximum_positive f r₀ r₃ r₁ hf hn hpos h₀ ((h₁.trans h₂).trans h₃)
  have hpr := maximum_positive f r₀ r₃ r hf hn (hpos.trans h₁) (h₀.trans h₁) (h₂.trans h₃)
  have hp₂ := maximum_positive f r₀ r₃ r₂ hf hn ((hpos.trans h₁).trans h₂)
    (h₀.trans (h₁.trans h₂)) h₃
  have h := Real.log_le_log hpr (three_circles_powers hf hpos h₀ h₁ h₂ h₃)
  rw [Real.log_mul (Real.rpow_pos_of_pos hp₁ _).ne' (Real.rpow_pos_of_pos hp₂ _).ne',
    Real.log_rpow hp₁, Real.log_rpow hp₂] at h
  rw [(weights hpos h₁ h₂).1, (weights hpos h₁ h₂).2.2]
  exact h

theorem logMaximum_convex :
    Specs.D12Complex.Ch06.ThreeCircles.logMaximum_convex_type := by
  intro f r₀ r₃ hf hn
  have hc : Convex ℝ {x : ℝ | r₀ < Real.exp x ∧ Real.exp x < r₃} :=
    convex_iff_ordConnected.mpr (ordConnected_Ioo.preimage_mono Real.exp_monotone)
  apply LinearOrder.convexOn_of_lt hc
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul]
  have hxv : x < a * x + b * y := by linear_combination b * hxy - x * hab
  have hvy : a * x + b * y < y := by linear_combination a * hxy + y * hab
  have h := three_circles_log f r₀ (Real.exp x) (Real.exp (a*x+b*y))
    (Real.exp y) r₃ hf hn (Real.exp_pos x) hx.1
    (Real.exp_lt_exp.mpr hxv) (Real.exp_lt_exp.mpr hvy) hy.2
  rw [Real.log_div (Real.exp_pos y).ne' (Real.exp_pos (a*x+b*y)).ne',
    Real.log_div (Real.exp_pos y).ne' (Real.exp_pos x).ne',
    Real.log_div (Real.exp_pos (a*x+b*y)).ne' (Real.exp_pos x).ne'] at h
  simp only [Real.log_exp] at h
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  have hwa : (y - (a*x+b*y)) / (y-x) = a := by
    apply (div_eq_iff hyx).mpr
    linear_combination -y * hab
  have hwb : (a*x+b*y-x) / (y-x) = b := by
    apply (div_eq_iff hyx).mpr
    linear_combination x * hab
  simpa only [hwa, hwb] using h

end D12Complex.ThreeCircles
