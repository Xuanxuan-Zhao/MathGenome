import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.RadialPlaneException
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.HilbertCharacterization.RadialCriterion
import Mathlib.Analysis.InnerProductSpace.Basic

namespace ExpandedFA.HilbertCharacterization

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma unit_ray_strict_of_minimizer_bound (h : EqualNormMinimizerBound X)
    {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {b : ℝ} (hb : 1 < b) :
    ‖x-y‖ < ‖x-b • y‖ := by
  obtain ⟨m, hm⟩ := exists_unit_line_minimizer hx hy
  have hm1 : m ≤ 1 := (abs_le.mp (h x y (hx.trans hy.symm)
    (by rw [hx]; norm_num) m hm)).2
  have hmb : ‖x-m • y‖ < ‖x-b • y‖ := by
    apply lt_of_le_of_ne (hm b)
    intro heq
    have hbmin : ∀ t : ℝ, ‖x-b • y‖ ≤ ‖x-t • y‖ := by
      intro t
      rw [← heq]
      exact hm t
    have := (abs_le.mp (h x y (hx.trans hy.symm)
      (by rw [hx]; norm_num) b hbmin)).2
    linarith
  let p : ℝ := (b-1)/(b-m)
  let q : ℝ := (1-m)/(b-m)
  have hd : 0 < b-m := by linarith
  have hp : 0 < p := div_pos (by linarith) hd
  have hq : 0 ≤ q := div_nonneg (by linarith) hd.le
  have hpq : p+q = 1 := by dsimp [p,q]; field_simp; ring
  have hcoef : p*m+q*b = 1 := by dsimp [p,q]; field_simp; ring
  have hid : x-y = p • (x-m • y) + q • (x-b • y) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, sub_add_sub_comm,
      ← add_smul, ← add_smul, hpq, hcoef, one_smul, one_smul]
  calc
    ‖x-y‖ ≤ p*‖x-m • y‖ + q*‖x-b • y‖ := by
      rw [hid]
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hp, abs_of_nonneg hq]
        using norm_add_le (p • (x-m • y)) (q • (x-b • y))
    _ < p*‖x-b • y‖ + q*‖x-b • y‖ :=
      by linarith only [mul_lt_mul_of_pos_left hmb hp]
    _ = ‖x-b • y‖ := by rw [← add_mul, hpq, one_mul]

lemma equal_norm_ray_strict (h : EqualNormMinimizerBound X)
    {x y : X} (hxy : ‖x‖ = ‖y‖) (hx : 0 < ‖x‖) {b : ℝ} (hb : 1 < b) :
    ‖x-y‖ < ‖x-b • y‖ := by
  have hu := norm_normalize hx
  have hv : ‖‖x‖⁻¹ • y‖ = 1 := by rw [hxy]; exact norm_normalize (hxy ▸ hx)
  have hh := unit_ray_strict_of_minimizer_bound h hu hv hb
  have hh' : ‖‖x‖⁻¹ • x - (1:ℝ) • (‖x‖⁻¹ • y)‖ <
      ‖‖x‖⁻¹ • x - b • (‖x‖⁻¹ • y)‖ := by simpa using hh
  rw [norm_normalized_line x y hx 1, norm_normalized_line x y hx b, one_smul] at hh'
  exact (mul_lt_mul_iff_right₀ (inv_pos.mpr hx)).mp hh'

lemma BirkhoffOrthogonal.smul_left {x y : X} (h : BirkhoffOrthogonal x y) (a : ℝ) :
    BirkhoffOrthogonal (a • x) y := by
  intro t
  by_cases ha : a = 0
  · subst a; simp
  have hid : a • x + t • y = a • (x + (t/a) • y) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ ha]
  rw [hid, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (h (t/a)) (norm_nonneg a)

lemma symmetric_birkhoff_of_minimizer_bound (h : EqualNormMinimizerBound X) :
    ∀ x y : X, BirkhoffOrthogonal x y → BirkhoffOrthogonal y x := by
  intro x y hxy t
  by_contra hbad
  have hlt : ‖y+t • x‖ < ‖y‖ := lt_of_not_ge hbad
  have hy : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have ht : t ≠ 0 := by intro ht; simp [ht] at hlt
  have hz : 0 < ‖y+t • x‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hyx : y = -t • x := by
      have : y = -(t • x) := eq_neg_of_add_eq_zero_left hz
      simpa using this
    have hh := hxy (t⁻¹)
    have hid : x + t⁻¹ • y = 0 := by rw [hyx, smul_smul]; field_simp; module
    rw [hid, norm_zero] at hh
    have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    simp [hx0] at hlt
  let m : ℝ := ‖y+t • x‖/‖y‖
  have hm : 0 < m := div_pos hz hy
  have hm1 : m < 1 := (div_lt_one hy).mpr hlt
  have heq : ‖y+t • x‖ = ‖m • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
    dsimp [m]
    rw [div_mul_cancel₀ _ hy.ne']
  have hstrict := equal_norm_ray_strict h heq hz
    ((one_lt_inv₀ hm).mpr hm1)
  have hid₁ : y+t • x - m • y = t • x + (1-m) • y := by module
  have hid₂ : y+t • x - m⁻¹ • (m • y) = t • x := by
    rw [smul_smul, inv_mul_cancel₀ hm.ne', one_smul]; module
  rw [hid₁, hid₂] at hstrict
  exact (not_lt_of_ge (hxy.smul_left t (1-m))) hstrict

lemma minimizer_bound_of_symmetric_birkhoff
    (h : ∀ x y : X, BirkhoffOrthogonal x y → BirkhoffOrthogonal y x) :
    EqualNormMinimizerBound X := by
  intro x y hxy hx a hmin
  by_cases ha : a = 0
  · simp [ha]
  have hres : BirkhoffOrthogonal (x-a • y) y := by
    intro t
    have hid : x-a • y+t • y = x-(a-t) • y := by module
    rw [hid]
    exact hmin (a-t)
  have hh := h (x-a • y) y hres
  have hid : y+a⁻¹ • (x-a • y) = a⁻¹ • x := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]; module
  have hh' := hh a⁻¹
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv, hxy] at hh'
  have habs : 0 < |a| := abs_pos.mpr ha
  have := (le_inv_mul_iff₀ habs).mp hh'
  nlinarith

/-- Radial nonexpansion is equivalent to symmetry of Birkhoff orthogonality. -/
theorem birkhoff_radial_iff : BirkhoffRadialStatement := by
  intro X _ _
  rw [radial_nonexpansive_iff X]
  exact ⟨symmetric_birkhoff_of_minimizer_bound, minimizer_bound_of_symmetric_birkhoff⟩

namespace HexPlane

@[simp] lemma coords_zero : coords 0 = (0,0) := rfl
@[simp] lemma coords_add (x y : HexPlane) : coords (x+y) = coords x + coords y := rfl
@[simp] lemma coords_sub (x y : HexPlane) : coords (x-y) = coords x - coords y := rfl
@[simp] lemma coords_neg (x : HexPlane) : coords (-x) = -coords x := rfl
@[simp] lemma coords_smul (a : ℝ) (x : HexPlane) : coords (a • x) = a • coords x := rfl
@[simp] lemma coords_ofCoords (s t : ℝ) : coords (ofCoords s t) = (s,t) := rfl

lemma norm_eq (x : HexPlane) :
    ‖x‖ = max (max |(coords x).1| |(coords x).2|) |(coords x).1+(coords x).2| := by
  change max (max ‖(coords x).1‖ ‖(coords x).2‖) ‖(coords x).1+(coords x).2‖ = _
  simp only [Real.norm_eq_abs]

lemma abs_fst_le (x : HexPlane) : |(coords x).1| ≤ ‖x‖ := by
  rw [norm_eq]
  exact (le_max_left _ _).trans (le_max_left _ _)

lemma abs_snd_le (x : HexPlane) : |(coords x).2| ≤ ‖x‖ := by
  rw [norm_eq]
  exact (le_max_right _ _).trans (le_max_left _ _)

lemma abs_sum_le (x : HexPlane) : |(coords x).1+(coords x).2| ≤ ‖x‖ := by
  rw [norm_eq]
  exact le_max_right _ _

lemma abs_positive_combination_le {p q u v B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hu : |u| ≤ B) (hv : |v| ≤ B) : |p*u+q*v| ≤ (p+q)*B := by
  calc
    |p*u+q*v| ≤ |p*u|+|q*v| := abs_add_le _ _
    _ = p*|u|+q*|v| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    _ ≤ p*B+q*B := add_le_add (mul_le_mul_of_nonneg_left hu hp)
      (mul_le_mul_of_nonneg_left hv hq)
    _ = (p+q)*B := by ring

lemma area_bound_nonneg {a b c d A B : ℝ} (ha : 0 ≤ a)
    (haA : |a| ≤ A) (hbA : |b| ≤ A) (habA : |a+b| ≤ A)
    (hc : |c| ≤ B) (hd : |d| ≤ B) (hcd : |c+d| ≤ B) (hB : 0 ≤ B) :
    |a*d-b*c| ≤ A*B := by
  by_cases hb : 0 ≤ b
  · calc
      |a*d-b*c| = |a*d+b*(-c)| := by congr 1; ring
      _ ≤ (a+b)*B := abs_positive_combination_le ha hb hd (by simpa using hc)
      _ ≤ A*B := mul_le_mul_of_nonneg_right (abs_le.mp habA).2 hB
  by_cases hab : 0 ≤ a+b
  · calc
      |a*d-b*c| = |(a+b)*d+(-b)*(c+d)| := by congr 1; ring
      _ ≤ ((a+b)+(-b))*B := abs_positive_combination_le hab (by linarith) hd hcd
      _ = a*B := by ring
      _ ≤ A*B := mul_le_mul_of_nonneg_right (abs_le.mp haA).2 hB
  · calc
      |a*d-b*c| = |a*(c+d)+(-(a+b))*c| := by congr 1; ring
      _ ≤ (a+(-(a+b)))*B := abs_positive_combination_le ha (by linarith) hcd hc
      _ = (-b)*B := by ring
      _ ≤ A*B := mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hbA).1]) hB

/-- The area bound for the hexagonal norm. -/
lemma abs_det_le (x y : HexPlane) : |det x y| ≤ ‖x‖*‖y‖ := by
  by_cases hx : 0 ≤ (coords x).1
  · exact area_bound_nonneg hx (abs_fst_le x) (abs_snd_le x) (abs_sum_le x)
      (abs_fst_le y) (abs_snd_le y) (abs_sum_le y) (norm_nonneg y)
  · have hh := area_bound_nonneg (by linarith : 0 ≤ -(coords x).1)
      (show |-(coords x).1| ≤ ‖x‖ by simpa using abs_fst_le x)
      (show |-(coords x).2| ≤ ‖x‖ by simpa using abs_snd_le x)
      (show |-(coords x).1 + -(coords x).2| ≤ ‖x‖ by
        simpa only [← neg_add, abs_neg] using abs_sum_le x)
      (abs_fst_le y) (abs_snd_le y) (abs_sum_le y) (norm_nonneg y)
    have hid : -(coords x).1 * (coords y).2 - -(coords x).2 * (coords y).1 = -det x y := by
      unfold det; ring
    simpa only [hid, abs_neg] using hh

lemma det_swap (x y : HexPlane) : det y x = -det x y := by unfold det; ring

@[simp] lemma det_zero_left (y : HexPlane) : det 0 y = 0 := by simp [det]

lemma det_smul_left (a : ℝ) (x y : HexPlane) : det (a • x) y = a*det x y := by
  simp [det]; ring

lemma det_add_smul (x y : HexPlane) (t : ℝ) : det (x+t • y) y = det x y := by
  simp [det]; ring

/-- A vertex of the hexagon attains the area supremum. -/
lemma exists_area_vertex (y : HexPlane) : ∃ u : HexPlane, ‖u‖ = 1 ∧ |det u y| = ‖y‖ := by
  rcases le_total |(coords y).1| |(coords y).2| with h | h
  · rcases le_total |(coords y).2| |(coords y).1+(coords y).2| with h' | h'
    · refine ⟨ofCoords 1 (-1), ?_, ?_⟩
      · norm_num [norm_eq]
      · simp only [det, coords_ofCoords, norm_eq]
        rw [max_eq_right h, max_eq_right h']
        congr 1; ring
    · refine ⟨ofCoords 1 0, ?_, ?_⟩
      · norm_num [norm_eq]
      · simp [det, norm_eq, max_eq_right h, max_eq_left h']
  · rcases le_total |(coords y).1| |(coords y).1+(coords y).2| with h' | h'
    · refine ⟨ofCoords 1 (-1), ?_, ?_⟩
      · norm_num [norm_eq]
      · simp only [det, coords_ofCoords, norm_eq]
        rw [max_eq_left h, max_eq_right h']
        congr 1; ring
    · refine ⟨ofCoords 0 1, ?_, ?_⟩
      · norm_num [norm_eq]
      · simp [det, norm_eq, max_eq_left h, max_eq_left h']

/-- The antinorm for standard determinant area equals the hexagonal norm exactly. -/
lemma antinorm_eq (y : HexPlane) : antinorm y = ‖y‖ := by
  obtain ⟨u, hu, huy⟩ := exists_area_vertex y
  have hbound : ∀ r ∈ {r : ℝ | ∃ x : HexPlane, ‖x‖ ≤ 1 ∧ r = |det x y|}, r ≤ ‖y‖ := by
    rintro r ⟨x,hx,rfl⟩
    exact (abs_det_le x y).trans (by nlinarith [norm_nonneg y])
  have hmem : ‖y‖ ∈ {r : ℝ | ∃ x : HexPlane, ‖x‖ ≤ 1 ∧ r = |det x y|} :=
    ⟨u, hu.le, huy.symm⟩
  exact le_antisymm (csSup_le ⟨_,hmem⟩ hbound) (le_csSup ⟨_,hbound⟩ hmem)

lemma det_sub_left (x z y : HexPlane) : det (x-z) y = det x y - det z y := by
  simp [det]; ring

lemma exists_smul_of_det_zero {z y : HexPlane} (hy : y ≠ 0) (hz : det z y = 0) :
    ∃ t : ℝ, z = t • y := by
  by_cases hy1 : (coords y).1 = 0
  · have hy2 : (coords y).2 ≠ 0 := by
      intro hy2
      apply hy
      apply Prod.ext <;> assumption
    have hz1 : (coords z).1 = 0 := by
      have hh : (coords z).1 * (coords y).2 = 0 := by simpa [det, hy1] using hz
      exact (mul_eq_zero.mp hh).resolve_right hy2
    refine ⟨(coords z).2/(coords y).2, ?_⟩
    apply Prod.ext
    · change (coords z).1 = ((coords z).2/(coords y).2)*(coords y).1
      simp [hz1,hy1]
    · change (coords z).2 = ((coords z).2/(coords y).2)*(coords y).2
      rw [div_mul_cancel₀ _ hy2]
  · refine ⟨(coords z).1/(coords y).1, ?_⟩
    apply Prod.ext
    · change (coords z).1 = ((coords z).1/(coords y).1)*(coords y).1
      rw [div_mul_cancel₀ _ hy1]
    · change (coords z).2 = ((coords z).1/(coords y).1)*(coords y).2
      field_simp
      unfold det at hz
      nlinarith

/-- For this plane, Birkhoff orthogonality is equality in the area bound. -/
lemma birkhoff_iff_area (x y : HexPlane) :
    BirkhoffOrthogonal x y ↔ |det x y| = ‖x‖*‖y‖ := by
  by_cases hy : y = 0
  · subst y
    simp [BirkhoffOrthogonal, det]
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  constructor
  · intro h
    obtain ⟨u,hu,huy⟩ := exists_area_vertex y
    have hdu : det u y ≠ 0 := by
      intro hh
      rw [hh,abs_zero] at huy
      linarith
    let a : ℝ := det x y / det u y
    have hd : det (x-a • u) y = 0 := by
      rw [det_sub_left, det_smul_left]
      dsimp [a]
      rw [div_mul_cancel₀ _ hdu, sub_self]
    obtain ⟨t,ht⟩ := exists_smul_of_det_zero hy hd
    have hid : x+(-t) • y = a • u := by
      calc
        x+(-t) • y = (x-a • u) - t • y + a • u := by module
        _ = a • u := by rw [ht, sub_self, zero_add]
    have hh := h (-t)
    rw [hid, norm_smul, Real.norm_eq_abs, hu, mul_one] at hh
    have ha : |a| = |det x y|/‖y‖ := by dsimp [a]; rw [abs_div,huy]
    rw [ha] at hh
    exact le_antisymm (abs_det_le x y) ((le_div_iff₀ hny).mp hh)
  · intro h t
    have hh := abs_det_le (x+t • y) y
    rw [det_add_smul,h] at hh
    exact (mul_le_mul_iff_left₀ hny).mp hh

lemma birkhoff_symmetric :
    ∀ x y : HexPlane, BirkhoffOrthogonal x y → BirkhoffOrthogonal y x := by
  intro x y h
  rw [birkhoff_iff_area] at h ⊢
  rw [det_swap,abs_neg,h,mul_comm]

lemma radial_nonexpansive :
    ∀ x y : HexPlane, ‖radialRetraction x-radialRetraction y‖ ≤ ‖x-y‖ :=
  (birkhoff_radial_iff HexPlane).mpr birkhoff_symmetric

/-- The coordinate unit vectors violate the parallelogram identity: 5 ≠ 4. -/
lemma not_parallelogram : ∃ x y : HexPlane,
    ‖x+y‖^2 + ‖x-y‖^2 ≠ 2*‖x‖^2 + 2*‖y‖^2 := by
  refine ⟨ofCoords 1 0, ofCoords 0 1, ?_⟩
  norm_num [norm_eq]

lemma finrank_eq_two : Module.finrank ℝ HexPlane = 2 := by
  change Module.finrank ℝ (ℝ × ℝ) = 2
  simp [Module.finrank_prod]

/-- No real inner product can induce the given hexagonal norm. -/
lemma not_innerProductSpace : ¬ Nonempty (InnerProductSpace ℝ HexPlane) := by
  rintro ⟨inst⟩
  letI := inst
  obtain ⟨x,y,hxy⟩ := not_parallelogram
  apply hxy
  simpa only [mul_add] using parallelogram_law_with_norm ℝ x y

end HexPlane

/-- A norm with a hexagonal unit ball gives the genuine two-dimensional exception. -/
theorem hexPlane_exception : HexPlaneExceptionStatement := by
  refine ⟨?_, HexPlane.antinorm_eq, HexPlane.birkhoff_symmetric,
    HexPlane.radial_nonexpansive, HexPlane.not_parallelogram,
    HexPlane.finrank_eq_two, HexPlane.not_innerProductSpace⟩
  intro s t
  exact HexPlane.norm_eq _

end ExpandedFA.HilbertCharacterization
