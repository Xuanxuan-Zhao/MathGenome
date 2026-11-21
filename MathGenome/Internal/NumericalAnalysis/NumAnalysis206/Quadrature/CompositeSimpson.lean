import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.CompositeSimpson
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.PeanoKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace NumAnalysis206.Quadrature
open Set
open scoped BigOperators
open NumAnalysis206.Approximation

noncomputable abbrev simpsonStep := CompositeSimpsonSpec.stepValue
noncomputable abbrev simpsonNode := CompositeSimpsonSpec.nodeValue
noncomputable abbrev compositeSimpson := CompositeSimpsonSpec.ruleValue

/-- The three-node Simpson error is a bounded functional on the full space of
continuous functions on the panel. -/
private theorem exists_simpsonError (c h : ℝ) (hh : 0 < h) :
    ∃ E : IntervalSpace c (c+2*h) →L[ℝ] ℝ,
      ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c (c+2*h))),
        E ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩ =
          (∫ x in c..c+2*h, g x) - h/3 * (g c + 4*g (c+h) + g (c+2*h)) := by
  let nodes : Fin 3 → Icc c (c+2*h) := fun i =>
    ⟨c + (i : ℕ)*h, by have hi := i.isLt; constructor <;> fin_cases i <;> norm_num <;> linarith⟩
  let weights : Fin 3 → ℝ := fun i => if i = 1 then 4*h/3 else h/3
  obtain ⟨E, hE, _⟩ := exists_quadratureError (by linarith : c ≤ c+2*h)
    Finset.univ nodes weights
  refine ⟨E, ?_⟩
  intro g hg
  rw [hE]
  change (∫ t in c..c+2*h, g (projIcc c (c+2*h) _ t)) -
    ∑ i : Fin 3, weights i * g (nodes i) = _
  have hi : (∫ t in c..c+2*h,
      g (projIcc c (c+2*h) (by linarith) t)) = ∫ t in c..c+2*h, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith : c ≤ c+2*h)] at ht
    change g (projIcc c (c+2*h) _ t) = g t
    simp only [projIcc_of_mem _ ht]
  rw [hi]
  simp [Fin.sum_univ_succ, nodes, weights]
  ring

private theorem simpson_pow_exact (c h : ℝ) (k : ℕ) (hk : k < 4) :
    (∫ x in c..c+2*h, x^k) =
      h/3 * (c^k + 4*(c+h)^k + (c+2*h)^k) := by
  rw [integral_pow]
  interval_cases k <;> norm_num <;> ring

private theorem simpson_annihilates {c h : ℝ}
    (E : IntervalSpace c (c+2*h) →L[ℝ] ℝ)
    (hE : ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c (c+2*h))),
      E ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩ =
        (∫ x in c..c+2*h, g x) - h/3 * (g c + 4*g (c+h) + g (c+2*h))) :
    AnnihilatesPolynomials E 4 := by
  intro p hp
  have hn : p.natDegree < 4 := by
    by_cases hp0 : p = 0
    · subst p; norm_num
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  have hpoly : intervalPolynomial (a := c) (b := c+2*h) p =
      ∑ k ∈ Finset.range 4, p.coeff k • intervalPolynomial (Polynomial.X^k) := by
    ext x
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hn]
    simp [intervalPolynomial, PeanoKernelSpec.polynomialValue, Polynomial.eval_finsetSum]
  change E (intervalPolynomial p) = 0
  rw [hpoly, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_smul]
  have hzero : E (intervalPolynomial (Polynomial.X^k)) = 0 := by
    have heq := hE (fun x => x^k) (by fun_prop)
    have hm : intervalPolynomial (a := c) (b := c+2*h) (Polynomial.X^k) =
        ⟨fun x => (x : ℝ)^k, (continuous_subtype_val.pow k)⟩ := by
      ext x; simp [intervalPolynomial, PeanoKernelSpec.polynomialValue]
    rw [hm, heq, simpson_pow_exact c h k (Finset.mem_range.mp hk), sub_self]
  rw [hzero, smul_zero]

/-- Integrating a truncated cubic on an interval, including either endpoint. -/
private theorem integral_positive_cube {c d t : ℝ} (ht : t ∈ Icc c d) :
    (∫ x in c..d, max (x-t) 0 ^ 3 / 6) = (d-t)^4 / 24 := by
  let g : ℝ → ℝ := fun x => max (x-t) 0 ^ 3 / 6
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hleft : (∫ x in c..t, g x) = 0 := by
    calc
      _ = ∫ x in c..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ht.1] at hx
        simp [g, max_eq_right (sub_nonpos.mpr hx.2)]
      _ = 0 := intervalIntegral.integral_zero
  have hright : (∫ x in t..d, g x) = (d-t)^4 / 24 := by
    calc
      _ = ∫ x in t..d, (x-t)^3 / 6 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ht.2] at hx
        simp [g, max_eq_left (sub_nonneg.mpr hx.1)]
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right
          (fun x : ℝ => x^3) t, integral_pow]
        norm_num
        ring
  calc
    _ = (∫ x in c..t, g x) + ∫ x in t..d, g x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable c t) (hg.intervalIntegrable t d)).symm
    _ = _ := by rw [hleft, hright, zero_add]

private theorem simpson_kernel_formula {c h : ℝ} (_hh : 0 < h)
    (E : IntervalSpace c (c+2*h) →L[ℝ] ℝ)
    (hE : ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c (c+2*h))),
      E ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩ =
        (∫ x in c..c+2*h, g x) - h/3 * (g c + 4*g (c+h) + g (c+2*h)))
    {t : ℝ} (ht : t ∈ Icc c (c+2*h)) :
    peanoKernel E 4 t =
      if t ≤ c+h then (t-c)^3 * (3*(t-c)-4*h) / 72
      else (c+2*h-t)^3 * (3*(c+2*h-t)-4*h) / 72 := by
  have heq := hE (fun x => max (x-t) 0 ^ 3 / 6) (by fun_prop)
  have hm : peanoSlice (a := c) (b := c+2*h) 4 t =
      ⟨fun x => max ((x : ℝ)-t) 0 ^ 3 / 6,
        continuousOn_iff_continuous_domRestrict.mp
          (show ContinuousOn (fun x : ℝ => max (x-t) 0 ^ 3 / 6) (Icc c (c+2*h)) from by fun_prop)⟩ := by
    ext x
    norm_num [peanoSlice, PeanoKernelSpec.sliceValue]
    rfl
  change E (peanoSlice 4 t) = _
  rw [hm, heq, integral_positive_cube ht,
    max_eq_right (sub_nonpos.mpr ht.1), max_eq_left (sub_nonneg.mpr ht.2)]
  by_cases hmid : t ≤ c+h
  · rw [ite_eq_left hmid, max_eq_left (by linarith : 0 ≤ c+h-t)]
    ring
  · rw [ite_eq_right hmid, max_eq_right (by linarith : c+h-t ≤ 0)]
    ring

private theorem simpson_kernel_nonpos {c h : ℝ} (hh : 0 < h)
    (E : IntervalSpace c (c+2*h) →L[ℝ] ℝ)
    (hE : ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c (c+2*h))),
      E ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩ =
        (∫ x in c..c+2*h, g x) - h/3 * (g c + 4*g (c+h) + g (c+2*h))) :
    ∀ t ∈ Icc c (c+2*h), peanoKernel E 4 t ≤ 0 := by
  intro t ht
  rw [simpson_kernel_formula hh E hE ht]
  split_ifs with hmid
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sub_nonneg.mpr ht.1) _) (by linarith))
      (by norm_num)
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sub_nonneg.mpr ht.2) _) (by linarith))
      (by norm_num)

private theorem simpson_kernel_mass {c h : ℝ} (hh : 0 < h)
    (E : IntervalSpace c (c+2*h) →L[ℝ] ℝ)
    (hE : ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc c (c+2*h))),
      E ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩ =
        (∫ x in c..c+2*h, g x) - h/3 * (g c + 4*g (c+h) + g (c+2*h))) :
    (∫ t in c..c+2*h, |peanoKernel E 4 t|) = h^5 / 90 := by
  rw [peano_mass E (by linarith) (by decide) (simpson_annihilates E hE)
    (Or.inr (simpson_kernel_nonpos hh E hE))]
  have hm : intervalPolynomial (a := c) (b := c+2*h)
      (Polynomial.C ((Nat.factorial 4 : ℝ)⁻¹) * Polynomial.X^4) =
      ⟨fun x => (x : ℝ)^4 / 24, (continuous_subtype_val.pow 4).div_const 24⟩ := by
    ext x
    norm_num [intervalPolynomial, PeanoKernelSpec.polynomialValue]
    ring
  rw [hm, hE (fun x => x^4 / 24) (by fun_prop),
    intervalIntegral.integral_div, integral_pow]
  have halg : ((c+2*h)^5-c^5)/5/24 -
      h/3*(c^4/24 + 4*((c+h)^4/24) + (c+2*h)^4/24) = -(h^5/90) := by ring
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [halg, abs_neg, abs_of_nonneg (by positivity)]

/-- The sharp bound on one panel of length `2*h`, with any uniform bound on
its fourth derivative. No extension of the jet off the panel is assumed. -/
theorem simpson_panel_bound {c h M : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (hh : 0 < h) (hD : IntervalJet c (c+2*h) 4 f D)
    (hM : ∀ t ∈ Icc c (c+2*h), |D 4 t| ≤ M) :
    |(∫ t in c..c+2*h, f t) - h/3*(f c + 4*f (c+h) + f (c+2*h))| ≤
      h^5 / 90 * M := by
  obtain ⟨E, hE⟩ := exists_simpsonError c h hh
  have hf : ContinuousOn f (Icc c (c+2*h)) :=
    (hD.2.1 0 (by omega)).congr hD.1.symm
  have heq : E (PeanoKernelSpec.functionValue hD) =
      (∫ t in c..c+2*h, f t) - h/3*(f c + 4*f (c+h) + f (c+2*h)) := hE f hf
  have hb := peano_bound E (by linarith) (by decide) (simpson_annihilates E hE) hD
  rw [heq, simpson_kernel_mass hh E hE] at hb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c ⟨le_rfl, by linarith⟩)
  have hn : ‖PeanoKernelSpec.derivativeValue hD‖ ≤ M := by
    apply (ContinuousMap.norm_le _ hM0).mpr
    intro t
    exact hM t t.property
  calc
    _ ≤ ‖PeanoKernelSpec.derivativeValue hD‖ * (h^5/90) := hb
    _ ≤ h^5/90 * M := by nlinarith [show 0 ≤ h^5/90 by positivity]

/-- Composite Simpson's error with `n` small grid steps, grouped in pairs.
The final derivative norm is the uniform norm on the original interval. -/
theorem composite_simpson_error {a b : ℝ} {n : ℕ} {f : ℝ → ℝ}
    {D : ℕ → ℝ → ℝ} (hab : a < b) (hn : 2 ≤ n) (heven : Even n)
    (hD : IntervalJet a b 4 f D) :
    |(∫ t in a..b, f t) - compositeSimpson a b n f| ≤
      (b-a) * (simpsonStep a b n)^4 / 180 * ‖PeanoKernelSpec.derivativeValue hD‖ := by
  let h := simpsonStep a b n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : 0 < h := div_pos (sub_pos.mpr hab) hnpos
  have hstep : (n : ℝ) * h = b-a := by
    dsimp [h, simpsonStep, CompositeSimpsonSpec.stepValue]
    field_simp
  have htwo : (2 : ℝ) * (n / 2 : ℕ) = n := by
    exact_mod_cast Nat.two_mul_div_two_of_even heven
  have hspan : (n / 2 : ℕ) * (2*h) = b-a := by
    calc
      _ = (2 * (n / 2 : ℕ)) * h := by ring
      _ = _ := by rw [htwo, hstep]
  let c : ℕ → ℝ := fun j => a + (j : ℝ)*(2*h)
  have hc0 : c 0 = a := by simp [c]
  have hcm : c (n/2) = b := by dsimp [c]; linarith
  have hcs (j : ℕ) : c (j+1) = c j + 2*h := by
    simp only [c, Nat.cast_add, Nat.cast_one]; ring
  have hcl (j : ℕ) : a ≤ c j := by
    dsimp [c]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) (by positivity))
  have hcr (j : ℕ) (hj : j ≤ n/2) : c j ≤ b := by
    rw [← hcm]
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (show (j : ℝ) ≤ (n/2 : ℕ) by exact_mod_cast hj) (by positivity : 0 ≤ 2*h)) a
  have hcle (j : ℕ) : c j ≤ c (j+1) := by rw [hcs]; linarith
  have hsub (j : ℕ) (hj : j < n/2) : Icc (c j) (c (j+1)) ⊆ Icc a b :=
    Icc_subset_Icc (hcl j) (hcr (j+1) (by omega))
  have hf : ContinuousOn f (Icc a b) := (hD.2.1 0 (by omega)).congr hD.1.symm
  have hInt (j : ℕ) (hj : j < n/2) :
      IntervalIntegrable f MeasureTheory.volume (c j) (c (j+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hcle j)]
    exact hf.mono (hsub j hj)
  have hsum : (∑ j ∈ Finset.range (n/2), ∫ t in c j..c (j+1), f t) =
      ∫ t in a..b, f t := by
    simpa only [hc0, hcm] using intervalIntegral.sum_integral_adjacent_intervals hInt
  have hloc (j : ℕ) (hj : j ∈ Finset.range (n/2)) :
      |(∫ t in c j..c (j+1), f t) -
        h/3*(f (c j) + 4*f (c j+h) + f (c (j+1)))| ≤
        h^5/90 * ‖PeanoKernelSpec.derivativeValue hD‖ := by
    have hJ : IntervalJet (c j) (c j+2*h) 4 f D := by
      rw [← hcs]
      exact jet_restrict (hcl j) (hcr (j+1) (by have := Finset.mem_range.mp hj; omega)) hD
    have hM : ∀ t ∈ Icc (c j) (c j+2*h),
        |D 4 t| ≤ ‖PeanoKernelSpec.derivativeValue hD‖ := by
      intro t ht
      rw [← hcs] at ht
      exact (PeanoKernelSpec.derivativeValue hD).norm_coe_le_norm
        ⟨t, hsub j (Finset.mem_range.mp hj) ht⟩
    simpa only [hcs] using simpson_panel_bound hh hJ hM
  have hsim : compositeSimpson a b n f =
      ∑ j ∈ Finset.range (n/2), h/3*(f (c j) + 4*f (c j+h) + f (c (j+1))) := by
    unfold compositeSimpson CompositeSimpsonSpec.ruleValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have hj0 : simpsonNode a b n (2*j) = c j := by
      dsimp [simpsonNode, CompositeSimpsonSpec.nodeValue, c, h]
      push_cast; ring
    have hj1 : simpsonNode a b n (2*j+1) = c j+h := by
      dsimp [simpsonNode, CompositeSimpsonSpec.nodeValue, c, h]
      push_cast; ring
    have hj2 : simpsonNode a b n (2*j+2) = c (j+1) := by
      dsimp [simpsonNode, CompositeSimpsonSpec.nodeValue, c, h]
      push_cast; ring
    change f (simpsonNode a b n (2*j)) + 4*f (simpsonNode a b n (2*j+1)) +
      f (simpsonNode a b n (2*j+2)) = _
    rw [hj0, hj1, hj2]
  calc
    _ = |∑ j ∈ Finset.range (n/2), ((∫ t in c j..c (j+1), f t) -
          h/3*(f (c j) + 4*f (c j+h) + f (c (j+1))))| := by
      rw [Finset.sum_sub_distrib, hsum, ← hsim]
    _ ≤ ∑ j ∈ Finset.range (n/2), |(∫ t in c j..c (j+1), f t) -
          h/3*(f (c j) + 4*f (c j+h) + f (c (j+1)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (n/2), h^5/90 * ‖PeanoKernelSpec.derivativeValue hD‖ :=
      Finset.sum_le_sum hloc
    _ = (b-a) * (simpsonStep a b n)^4 / 180 * ‖PeanoKernelSpec.derivativeValue hD‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      change (n/2 : ℕ) * (h^5/90 * _) = (b-a)*h^4/180 * _
      rw [← hspan]
      ring

end NumAnalysis206.Quadrature
