import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Products
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Analysis.Normed.Field.Basic

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- The Darboux gap is the sum of the cell oscillations times their lengths. -/
theorem sum_cell_oscillation (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) :
    (∑ i : Fin P.n, (cellSupremum f P hf i - cellInfimum f P hf i) *
      cellLength P i) = upperSum f P hf - lowerSum f P hf := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  rfl

/-- An arbitrarily small additive error plus a Lipschitz bound suffices.
This form expresses the good-cell/bad-cell argument without choosing extrema. -/
theorem realIntegrable_of_approximate_lipschitz {f h : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hh : BoundedOnInterval h a b)
    (hd : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        h x - h y ≤ η + C * |f x - f y|) : RealIntegrable h a b := by
  apply (realIntegrable_iff_small_gap h (RealIntegrable.ordered hf) hh).mpr
  intro ε hε
  have hlen : 0 ≤ b - a := sub_nonneg.mpr (RealIntegrable.ordered hf)
  let η := ε / (2 * (b - a + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hdiff⟩ := hd η hη
  obtain ⟨P, hP⟩ := (realIntegrable_iff_small_gap f (RealIntegrable.ordered hf) (RealIntegrable.bounded hf)).mp hf
    (ε / (2 * (C + 1))) (by positivity)
  have hcell (i : Fin P.n) :
      cellSupremum h P hh i - cellInfimum h P hh i ≤
        η + C * (cellSupremum f P (RealIntegrable.bounded hf) i - cellInfimum f P (RealIntegrable.bounded hf) i) := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    exact (hdiff x (cell_subset_interval P i hx) y (cell_subset_interval P i hy)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (abs_sub_le_cell_oscillation f P (RealIntegrable.bounded hf) i hx hy) hC))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_cellLength, sum_cell_oscillation] at hs
  refine ⟨P, hs.trans_lt ?_⟩
  have hη' : η * (2 * (b - a + 1)) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  have hP' := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hP
  have hgap := sub_nonneg.mpr (lowerSum_le_upperSum f P (RealIntegrable.bounded hf))
  nlinarith [mul_nonneg hη.le hlen]

/-- Weighted component estimates transfer Darboux integrability. -/
theorem realIntegrable_of_two_weighted_bound {f g h : ℝ → ℝ} {a b A B : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (hh : BoundedOnInterval h a b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      h x - h y ≤ A * |f x - f y| + B * |g x - g y|) :
    RealIntegrable h a b := by
  apply realIntegrable_of_two_component_bound (real_mul_value hf A).choose
    (real_mul_value hg B).choose hh
  intro x hx y hy
  simpa only [← mul_sub, abs_mul, abs_of_nonneg hA, abs_of_nonneg hB] using hd x hx y hy

theorem real_product : Specs.SingleVariableAnalysis.Ch08.Products.realProduct := by
  intro f g a b hf hg
  obtain ⟨A, hA⟩ := (RealIntegrable.bounded hf).abs_bound
  obtain ⟨B, hB⟩ := (RealIntegrable.bounded hg).abs_bound
  have hA0 : 0 ≤ A := (abs_nonneg (f a)).trans (hA a ⟨le_rfl, (RealIntegrable.ordered hf)⟩)
  have hB0 : 0 ≤ B := (abs_nonneg (g a)).trans (hB a ⟨le_rfl, (RealIntegrable.ordered hf)⟩)
  have hh : BoundedOnInterval (fun x => f x * g x) a b := by
    apply boundedOnInterval_of_abs (M := A * B)
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hA x hx) (hB x hx) (abs_nonneg _) hA0
  apply realIntegrable_of_two_weighted_bound hf hg hh hB0 hA0
  intro x hx y hy
  calc
    _ ≤ |f x * g x - f y * g y| := le_abs_self _
    _ = |g x * (f x - f y) + f y * (g x - g y)| := by congr 1; ring
    _ ≤ |g x| * |f x - f y| + |f y| * |g x - g y| := by
      simpa only [abs_mul] using abs_add_le (g x * (f x - f y)) (f y * (g x - g y))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hB x hx) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (hA y hy) (abs_nonneg _))

theorem RealIntegrable.sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    RealIntegrable (fun x => f x - g x) a b := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    (real_add_value hf (real_mul_value hg (-1)).choose).choose

theorem complex_product : Specs.SingleVariableAnalysis.Ch08.Products.complexProduct := by
  intro f g a b hf hg
  constructor
  · simpa only [Complex.mul_re] using
      RealIntegrable.sub (real_product hf.1 hg.1) (real_product hf.2 hg.2)
  · simpa only [Complex.mul_im] using
      (real_add_value (real_product hf.1 hg.2) (real_product hf.2 hg.1)).choose

theorem real_composition : Specs.SingleVariableAnalysis.Ch08.Products.realComposition := by
  intro f a b c d Φ hf hΦ hrange
  have hbΦ : BoundedOnInterval Φ c d :=
    ⟨(isCompact_Icc.image_of_continuousOn hΦ).bddBelow, (isCompact_Icc.image_of_continuousOn hΦ).bddAbove⟩
  obtain ⟨H, hH⟩ := hbΦ.abs_bound
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH _ (hrange a ⟨le_rfl, (RealIntegrable.ordered hf)⟩))
  have hh : BoundedOnInterval (fun x => Φ (f x)) a b :=
    boundedOnInterval_of_abs (fun x hx => hH _ (hrange x hx))
  apply realIntegrable_of_approximate_lipschitz hf hh
  intro η hη
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hΦ) η hη
  refine ⟨2 * H / δ, by positivity, ?_⟩
  intro x hx y hy
  by_cases hxy : |f x - f y| < δ
  · have hsmall : |Φ (f x) - Φ (f y)| < η := by
      simpa only [Real.dist_eq] using huc (f x) (hrange x hx) (f y) (hrange y hy)
        (by simpa only [Real.dist_eq] using hxy)
    exact (le_abs_self _).trans (hsmall.le.trans
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (abs_nonneg _))))
  · have hlarge : δ ≤ |f x - f y| := le_of_not_gt hxy
    have hbound : Φ (f x) - Φ (f y) ≤ 2 * H := by
      have hx' := abs_le.mp (hH _ (hrange x hx))
      have hy' := abs_le.mp (hH _ (hrange y hy))
      linarith
    have hcoef : 2 * H ≤ (2 * H / δ) * |f x - f y| := by
      calc
        _ = (2 * H / δ) * δ := (div_mul_cancel₀ _ hδ.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (by positivity)
    exact hbound.trans (hcoef.trans (le_add_of_nonneg_left hη.le))

theorem complex_composition : Specs.SingleVariableAnalysis.Ch08.Products.complexComposition := by
  intro f a b c d Φ hf hΦ hrange
  exact ⟨real_composition hf (Complex.continuous_re.comp_continuousOn hΦ) hrange,
    real_composition hf (Complex.continuous_im.comp_continuousOn hΦ) hrange⟩

/-- Inversion is Lipschitz on every subset bounded away from zero;
the subset need not be an interval or have a fixed real sign. -/
theorem norm_inv_sub_inv_le_of_lower_bound {K : Type*} [NormedField K]
    {u v : K} {d : ℝ} (hd : 0 < d) (hu : d ≤ ‖u‖) (hv : d ≤ ‖v‖) :
    ‖u⁻¹ - v⁻¹‖ ≤ (1 / (d * d)) * ‖u - v‖ := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hd.trans_le hu)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (hd.trans_le hv)
  calc
    _ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
      simpa only [dist_eq_norm] using dist_inv_inv₀ hu0 hv0
    _ ≤ ‖u - v‖ / (d * d) := div_le_div_of_nonneg_left (norm_nonneg _)
      (mul_pos hd hd) (mul_le_mul hu hv hd.le (norm_nonneg _))
    _ = _ := by ring

theorem norm_inv_le_of_lower_bound {K : Type*} [NormedField K]
    {u : K} {d : ℝ} (hd : 0 < d) (hu : d ≤ ‖u‖) : ‖u⁻¹‖ ≤ 1 / d := by
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hd hu

theorem real_reciprocal : Specs.SingleVariableAnalysis.Ch08.Products.realReciprocal := by
  intro f a b d hf hd hlower
  have hh : BoundedOnInterval (fun x => 1 / f x) a b := by
    apply boundedOnInterval_of_abs (M := 1 / d)
    intro x hx
    simpa only [one_div, Real.norm_eq_abs] using
      norm_inv_le_of_lower_bound (u := f x) hd (by simpa only [Real.norm_eq_abs] using hlower x hx)
  apply realIntegrable_of_approximate_lipschitz hf hh
  intro η hη
  refine ⟨1 / (d * d), by positivity, ?_⟩
  intro x hx y hy
  have h := norm_inv_sub_inv_le_of_lower_bound hd
    (show d ≤ ‖f x‖ by simpa only [Real.norm_eq_abs] using hlower x hx)
    (show d ≤ ‖f y‖ by simpa only [Real.norm_eq_abs] using hlower y hy)
  simp only [Real.norm_eq_abs] at h
  simpa only [one_div] using (le_abs_self ((f x)⁻¹ - (f y)⁻¹)).trans
    (h.trans (le_add_of_nonneg_left hη.le))

theorem complex_reciprocal : Specs.SingleVariableAnalysis.Ch08.Products.complexReciprocal := by
  intro f a b d hf hd hlower
  have hb : ∀ x ∈ Set.Icc a b, ‖(f x)⁻¹‖ ≤ 1 / d :=
    fun x hx => norm_inv_le_of_lower_bound hd (hlower x hx)
  have hbr : BoundedOnInterval (fun x => ((f x)⁻¹).re) a b :=
    boundedOnInterval_of_abs (fun x hx => (Complex.abs_re_le_norm _).trans (hb x hx))
  have hbi : BoundedOnInterval (fun x => ((f x)⁻¹).im) a b :=
    boundedOnInterval_of_abs (fun x hx => (Complex.abs_im_le_norm _).trans (hb x hx))
  have hdiff (x : ℝ) (hx : x ∈ Set.Icc a b) (y : ℝ) (hy : y ∈ Set.Icc a b) :
      ‖(f x)⁻¹ - (f y)⁻¹‖ ≤
        (1 / (d * d)) * |(f x).re - (f y).re| +
        (1 / (d * d)) * |(f x).im - (f y).im| := by
    calc
      _ ≤ (1 / (d * d)) * ‖f x - f y‖ :=
        norm_inv_sub_inv_le_of_lower_bound hd (hlower x hx) (hlower y hy)
      _ ≤ (1 / (d * d)) * (|(f x).re - (f y).re| + |(f x).im - (f y).im|) :=
        mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (by positivity)
      _ = _ := by ring
  constructor
  · simp only [one_div]
    apply realIntegrable_of_two_weighted_bound (A := 1 / (d * d)) (B := 1 / (d * d)) hf.1 hf.2 hbr (by positivity) (by positivity)
    intro x hx y hy
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm ((f x)⁻¹ - (f y)⁻¹)).trans
      (hdiff x hx y hy))
  · simp only [one_div]
    apply realIntegrable_of_two_weighted_bound (A := 1 / (d * d)) (B := 1 / (d * d)) hf.1 hf.2 hbi (by positivity) (by positivity)
    intro x hx y hy
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm ((f x)⁻¹ - (f y)⁻¹)).trans
      (hdiff x hx y hy))

end SingleVariableAnalysis.Riemann
