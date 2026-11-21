import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.RadialCriterion
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ExpandedFA.HilbertCharacterization

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_convex_combination_le {u v : X} {c p q : ℝ}
    (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) : ‖p • u + q • v‖ ≤ c := by
  calc
    ‖p • u + q • v‖ ≤ ‖p • u‖ + ‖q • v‖ := norm_add_le _ _
    _ = p * ‖u‖ + q * ‖v‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ p * c + q * c := add_le_add (mul_le_mul_of_nonneg_left hu hp)
      (mul_le_mul_of_nonneg_left hv hq)
    _ = c := by rw [← add_mul, hpq, one_mul]

lemma norm_line_between_le (x y : X) {a b t c : ℝ} (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) (ha : ‖x - a • y‖ ≤ c)
    (hb : ‖x - b • y‖ ≤ c) : ‖x - t • y‖ ≤ c := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hid : x - t • y = ((b-t)/(b-a)) • (x-a • y) +
      ((t-a)/(b-a)) • (x-b • y) := by
    have h₁ : (b-t)/(b-a) + (t-a)/(b-a) = 1 := by field_simp; ring
    have h₂ : (b-t)/(b-a)*a + (t-a)/(b-a)*b = t := by field_simp; ring
    rw [smul_sub, smul_sub, smul_smul, smul_smul]
    rw [sub_add_sub_comm, ← add_smul, ← add_smul, h₁, h₂, one_smul]
  rw [hid]
  apply norm_convex_combination_le ha hb
  · exact div_nonneg (sub_nonneg.mpr htb) hd.le
  · exact div_nonneg (sub_nonneg.mpr hat) hd.le
  · field_simp; ring

lemma radialRetraction_of_norm_le_one {x : X} (hx : ‖x‖ ≤ 1) :
    radialRetraction x = x := by simp [radialRetraction, max_eq_left hx]

lemma radialRetraction_smul_unit {x : X} (hx : ‖x‖ = 1) {t : ℝ} (ht : 1 ≤ t) :
    radialRetraction (t • x) = x := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  simp [radialRetraction, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hx,
    max_eq_right ht, smul_smul, ne_of_gt ht0]

lemma unit_ray_inequality
    (hR : ∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖)
    {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖x-y‖ ≤ ‖x-t • y‖ := by
  simpa [radialRetraction_of_norm_le_one hx.le, radialRetraction_smul_unit hy ht]
    using hR x (t • y)

/-- Flat minima beyond one contradict radial nonexpansion, even in a nonsmooth norm. -/
lemma unit_minimizer_le_one
    (hR : ∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖)
    {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {b : ℝ}
    (hbmin : ∀ t : ℝ, ‖x-b • y‖ ≤ ‖x-t • y‖) : b ≤ 1 := by
  by_contra hb
  have hb : 1 < b := lt_of_not_ge hb
  let a : ℝ := (b-1)/(4*b)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hab : a * (4*b) = b-1 := by dsimp [a]; field_simp
  have haquarter : a < 1/4 := by nlinarith
  let z : X := a • x + (1-a) • y
  let n : ℝ := ‖z‖
  have hnupper : n ≤ 1 := by
    exact norm_convex_combination_le hx.le hy.le ha.le (by linarith) (by ring)
  have hnlower : 1 - 2*a ≤ n := by
    have hid : y = z + a • (y-x) := by dsimp [z]; module
    have hn := norm_add_le z (a • (y-x))
    have hnxy : ‖y-x‖ ≤ 2 := by
      calc
        ‖y-x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ = 2 := by rw [hx, hy]; norm_num
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hn
    have := mul_le_mul_of_nonneg_left hnxy ha.le
    rw [← hid, hy] at hn
    dsimp [n]
    linarith
  have hn : 0 < n := by linarith
  have hna : 0 < n-a := by linarith
  have hsmall : a*(3*b-1) < b-1 := by nlinarith
  let d : ℝ := 1+a*(b-1)
  have hd : 0 < d := by dsimp [d]; positivity
  let k : ℝ := b/d
  have hk : 0 < k := div_pos (by linarith) hd
  have hkd : k*d = b := by dsimp [k]; field_simp
  have hkn : 1 < k*n := by
    have hb0 : 0 < b := by linarith
    have := mul_le_mul_of_nonneg_left hnlower hb0.le
    have hdn : d < b*n := by dsimp [d]; nlinarith
    simpa [k, div_mul_eq_mul_div] using (lt_div_iff₀ hd).mpr (show 1*d < b*n by simpa using hdn)
  have hka : k*a < 1 := by
    have hbd : b*a < d := by dsimp [d]; nlinarith
    simpa [k, div_mul_eq_mul_div] using (div_lt_one hd).mpr hbd
  let t : ℝ := (1-a)/(n-a)
  have ht1 : 1 ≤ t := (le_div_iff₀ hna).mpr (by linarith)
  have htb : t ≤ b := by
    apply (div_le_iff₀ hna).mpr
    have := mul_le_mul_of_nonneg_left hnlower (show 0 ≤ b by linarith)
    nlinarith
  let c : ℝ := ‖x-b • y‖
  have hc : 0 < c := by
    apply norm_pos_iff.mpr
    intro heq
    have heq' : x = b • y := sub_eq_zero.mp heq
    have hnorm := congrArg norm heq'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < b by linarith), hx, hy] at hnorm
    nlinarith
  have hc1 : ‖x-(1 : ℝ) • y‖ ≤ c := by
    simpa [c] using unit_ray_inequality hR hx hy hb.le
  have hct : ‖x-t • y‖ = c := le_antisymm
    (norm_line_between_le x y hb ht1 htb hc1 le_rfl) (hbmin t)
  have hrz : radialRetraction (k • z) = n⁻¹ • z := by
    have hnorm : ‖k • z‖ = k*n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    simp only [radialRetraction, hnorm, max_eq_right hkn.le, smul_smul]
    congr 1
    field_simp
  have hfact₁ : x - n⁻¹ • z = (1-a/n) • (x-t • y) := by
    have htcoef : (1-a/n)*t = (1-a)/n := by dsimp [t]; field_simp
    dsimp [z]
    rw [smul_add, smul_smul, smul_smul, smul_sub, smul_smul, htcoef]
    have : 1-a/n = 1-n⁻¹*a := by ring
    rw [this]
    module
  have hfact₂ : x - k • z = (1-k*a) • (x-b • y) := by
    have hkcoef : (1-k*a)*b = k*(1-a) := by dsimp [d] at hkd; nlinarith [hkd]
    dsimp [z]
    rw [smul_add, smul_smul, smul_smul, smul_sub, smul_smul, hkcoef]
    module
  have hineq := hR x (k • z)
  rw [radialRetraction_of_norm_le_one hx.le, hrz, hfact₁, hfact₂,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 1-a/n by apply sub_nonneg.mpr; apply (div_le_one hn).mpr; linarith),
    abs_of_nonneg (show 0 ≤ 1-k*a by linarith), hct] at hineq
  have hkinv : a/n < k*a := by
    apply (div_lt_iff₀ hn).mpr
    nlinarith
  nlinarith

lemma norm_normalized_line (x y : X) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖r⁻¹ • x - t • (r⁻¹ • y)‖ = r⁻¹ * ‖x-t • y‖ := by
  have hid : r⁻¹ • x - t • (r⁻¹ • y) = r⁻¹ • (x-t • y) := by module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]

lemma norm_normalize {x : X} (hx : 0 < ‖x‖) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']

lemma minimizer_bound_of_nonexpansive
    (hR : ∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖) :
    EqualNormMinimizerBound X := by
  intro x y hxy hx a hmin
  let u : X := ‖x‖⁻¹ • x
  let v : X := ‖x‖⁻¹ • y
  have hu : ‖u‖ = 1 := norm_normalize hx
  have hv : ‖v‖ = 1 := by dsimp [v]; rw [hxy]; exact norm_normalize (hxy ▸ hx)
  have hmin' : ∀ t : ℝ, ‖u-a • v‖ ≤ ‖u-t • v‖ := by
    intro t
    dsimp [u, v]
    rw [norm_normalized_line x y hx a, norm_normalized_line x y hx t]
    exact mul_le_mul_of_nonneg_left (hmin t) (inv_nonneg.mpr hx.le)
  have hpos : a ≤ 1 := unit_minimizer_le_one hR hu hv hmin'
  have hneg : -a ≤ 1 := by
    apply unit_minimizer_le_one hR hu (by simpa using hv) (y := -v)
    intro t
    simpa using hmin' (-t)
  exact abs_le.mpr ⟨by linarith, hpos⟩

/-- A scalar norm on a line with nonzero direction attains its minimum.
For unit pairs it is enough to minimize on [-3,3]. -/
lemma exists_unit_line_minimizer {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ m : ℝ, ∀ t : ℝ, ‖x-m • y‖ ≤ ‖x-t • y‖ := by
  have hcont : Continuous (fun t : ℝ => ‖x-t • y‖) := by fun_prop
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn
    (f := fun t : ℝ => ‖x-t • y‖) (show (Set.Icc (-3 : ℝ) 3).Nonempty from
      ⟨0, by norm_num⟩) hcont.continuousOn
  refine ⟨m, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-3 : ℝ) 3
  · exact hmin ht
  · have hm0 : ‖x-m • y‖ ≤ 1 := by
      simpa [hx] using hmin (show (0 : ℝ) ∈ Set.Icc (-3 : ℝ) 3 by norm_num)
    have habst : 3 < |t| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · rw [abs_of_neg (show t < 0 by linarith)]; linarith
      · rw [abs_of_pos (show 0 < t by linarith)]; exact ht
    have hrev := norm_sub_norm_le (t • y) x
    rw [norm_smul, Real.norm_eq_abs, hy, hx, norm_sub_rev (t • y) x] at hrev
    linarith

lemma unit_ray_monotone_of_minimizer_bound (h : EqualNormMinimizerBound X)
    {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ‖x-a • y‖ ≤ ‖x-b • y‖ := by
  obtain ⟨m, hm⟩ := exists_unit_line_minimizer hx hy
  have hm1 : m ≤ 1 := (abs_le.mp (h x y (hx.trans hy.symm) (by rw [hx]; norm_num) m hm)).2
  by_cases heq : a = b
  · rw [heq]
  · apply norm_line_between_le x y (a := m) (lt_of_le_of_lt (hm1.trans ha) (lt_of_le_of_ne hab heq))
      (hm1.trans ha) hab (hm b) le_rfl

lemma norm_scaled_line (u v : X) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ‖s • u - t • v‖ = s * ‖u-(t/s) • v‖ := by
  have hcoef : s*(t/s) = t := by field_simp
  have hid : s • u - t • v = s • (u-(t/s) • v) := by
    rw [smul_sub, smul_smul, hcoef]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hs]

lemma radialRetraction_of_one_le_norm {x : X} (hx : 1 ≤ ‖x‖) :
    radialRetraction x = ‖x‖⁻¹ • x := by rw [radialRetraction, max_eq_right hx]

lemma nonexpansive_of_minimizer_bound_ordered (h : EqualNormMinimizerBound X)
    (x y : X) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖radialRetraction x - radialRetraction y‖ ≤ ‖x-y‖ := by
  by_cases hyball : ‖y‖ ≤ 1
  · rw [radialRetraction_of_norm_le_one (hxy.trans hyball),
      radialRetraction_of_norm_le_one hyball]
  have hyr : 1 < ‖y‖ := lt_of_not_ge hyball
  by_cases hxzero : x = 0
  · subst x
    rw [radialRetraction_of_norm_le_one (by simp : ‖(0 : X)‖ ≤ 1),
      radialRetraction_of_one_le_norm hyr.le]
    simpa [norm_normalize (lt_trans zero_lt_one hyr)] using hyr.le
  have hs : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
  let s := ‖x‖
  let r := ‖y‖
  let u : X := s⁻¹ • x
  let v : X := r⁻¹ • y
  have hu : ‖u‖ = 1 := norm_normalize hs
  have hv : ‖v‖ = 1 := norm_normalize (lt_trans zero_lt_one hyr)
  have hxu : s • u = x := by dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hyv : r • v = y := by
    dsimp [v]; rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one hyr)), one_smul]
  have hRy : radialRetraction y = v := radialRetraction_of_one_le_norm hyr.le
  by_cases hxball : s ≤ 1
  · have hRx : radialRetraction x = x := radialRetraction_of_norm_le_one hxball
    rw [hRx, hRy, ← hxu, ← hyv]
    have hmono := unit_ray_monotone_of_minimizer_bound h hu hv
      (a := 1/s) (b := r/s) ((le_div_iff₀ hs).mpr (by simpa using hxball))
      ((div_le_div_iff_of_pos_right hs).mpr hyr.le)
    have hmul := mul_le_mul_of_nonneg_left hmono hs.le
    have hleft : ‖s • u-v‖ = s * ‖u-(1/s) • v‖ := by
      simpa only [one_smul] using norm_scaled_line u v hs 1
    rw [hleft, norm_scaled_line u v hs r]
    exact hmul
  · have hs1 : 1 ≤ s := (lt_of_not_ge hxball).le
    have hRx : radialRetraction x = u := radialRetraction_of_one_le_norm hs1
    rw [hRx, hRy, ← hxu, ← hyv]
    have hmono := unit_ray_monotone_of_minimizer_bound h hu hv
      (a := 1) (b := r/s) le_rfl ((le_div_iff₀ hs).mpr (by simpa using hxy))
    rw [one_smul] at hmono
    calc
      ‖u-v‖ ≤ ‖u-(r/s) • v‖ := hmono
      _ ≤ s * ‖u-(r/s) • v‖ := le_mul_of_one_le_left (norm_nonneg _) hs1
      _ = ‖s • u-r • v‖ := by
        rw [norm_scaled_line u v hs r]

/-- The radial nonexpansion criterion of de Figueiredo--Karlovitz.
No dimension or completeness assumption is imposed. -/
theorem radial_nonexpansive_iff : RadialCriterionStatement := by
  intro X _ _
  constructor
  · exact minimizer_bound_of_nonexpansive
  · intro h x y
    rcases le_total ‖x‖ ‖y‖ with hxy | hyx
    · exact nonexpansive_of_minimizer_bound_ordered h x y hxy
    · simpa only [norm_sub_rev] using nonexpansive_of_minimizer_bound_ordered h y x hyx

end ExpandedFA.HilbertCharacterization
