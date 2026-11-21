import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.StrictnessPersistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.FactorFourRate
import Mathlib.Analysis.SpecificLimits.Basic

/-! Persistence of strict convexity in Asplund's iteration.

For a fixed pair of points and weights, multiply the Jensen gap of φₙ by 2ⁿ.
The arithmetic recurrence and convexity of ψₙ make these scaled gaps increasing.
If the limit had a zero gap, the factor-four estimate would bound the scaled
gaps by a constant times (1/2)ⁿ, forcing every one of them to be zero.
Strictness of either initial function makes the first arithmetic mean's gap
positive, giving the contradiction. No minimizing splitting, continuity, or
completeness is used. -/
namespace ExpandedFA.Asplund.StrictnessPersistence

open Iteration OrderLimit FactorFourRate Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The defect in the convexity inequality at two points and two weights. -/
def jensenGap (f : E → ℝ) (x y : E) (a b : ℝ) : ℝ :=
  a * f x + b * f y - f (a • x + b • y)

theorem jensenGap_nonneg {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    0 ≤ jensenGap f x y a b := by
  have h := hf.2 (mem_univ x) (mem_univ y) ha hb hab
  change f (a • x + b • y) ≤ a * f x + b * f y at h
  exact sub_nonneg.mpr h

/-- The scaled convexity defects cannot decrease under arithmetic averaging
with the convex lower iterates. -/
theorem scaled_jensenGap_monotone (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀)
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Monotone (fun n => (2 : ℝ) ^ n * jensenGap (phi E φ₀ ψ₀ n) x y a b) := by
  apply monotone_nat_of_le_succ
  intro n
  have hq := jensenGap_nonneg (iterates_properties E φ₀ ψ₀ h n).2.1 x y ha hb hab
  change 0 ≤ jensenGap (psi E φ₀ ψ₀ n) x y a b at hq
  have heq : jensenGap (phi E φ₀ ψ₀ (n + 1)) x y a b =
      (jensenGap (phi E φ₀ ψ₀ n) x y a b +
        jensenGap (psi E φ₀ ψ₀ n) x y a b) / 2 := by
    simp only [jensenGap, phi_succ]
    ring
  rw [pow_succ, heq]
  have hn : 0 ≤ (2 : ℝ) ^ n := by positivity
  nlinarith [mul_nonneg hn hq]

/-- The first arithmetic mean is strictly convex if either input is. -/
theorem first_arithmeticMean_strict (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀)
    (hs : StrictConvexOn ℝ univ φ₀ ∨ StrictConvexOn ℝ univ ψ₀) :
    StrictConvexOn ℝ univ (phi E φ₀ ψ₀ 1) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hp := h.1.2 hx hy ha.le hb.le hab
  have hq := h.2.1.2 hx hy ha.le hb.le hab
  change φ₀ (a • x + b • y) ≤ a * φ₀ x + b * φ₀ y at hp
  change ψ₀ (a • x + b • y) ≤ a * ψ₀ x + b * ψ₀ y at hq
  change (φ₀ (a • x + b • y) + ψ₀ (a • x + b • y)) / 2 <
    a * ((φ₀ x + ψ₀ x) / 2) + b * ((φ₀ y + ψ₀ y) / 2)
  rcases hs with hs | hs
  · have hp' := hs.2 hx hy hxy ha hb hab
    change φ₀ (a • x + b • y) < a * φ₀ x + b * φ₀ y at hp'
    linarith
  · have hq' := hs.2 hx hy hxy ha hb hab
    change ψ₀ (a • x + b • y) < a * ψ₀ x + b * ψ₀ y at hq'
    linarith

/-- Replace the lower iterate in the factor-four bound by the common limit. -/
theorem phi_le_scaled_theta (φ₀ ψ₀ : E → ℝ) (h : InitialData E φ₀ ψ₀)
    (hφh : ∀ (a : ℝ) (x : E), φ₀ (a • x) = a ^ 2 * φ₀ x)
    (hψh : ∀ (a : ℝ) (x : E), ψ₀ (a • x) = a ^ 2 * ψ₀ x)
    (C : ℝ) (hC : 0 ≤ C) (hcomp : ∀ x, φ₀ x ≤ (1 + C) * ψ₀ x)
    (n : ℕ) (x : E) :
    phi E φ₀ ψ₀ n x ≤ (1 + C / (4 : ℝ) ^ n) * theta E φ₀ ψ₀ x := by
  exact (factor_four_bound E φ₀ ψ₀ h hφh hψh C hC hcomp n x).trans
    (mul_le_mul_of_nonneg_left (theta_bounds φ₀ ψ₀ h n x).1 (by positivity))

theorem strictness_persistence : Spec.ThetaStrictConvex := by
  intro E _ _ φ₀ ψ₀ h hφh hψh C hC hcomp hs
  change StrictConvexOn ℝ univ (theta E φ₀ ψ₀)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  change theta E φ₀ ψ₀ (a • x + b • y) <
    a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y
  by_contra hbad
  have hgap : jensenGap (theta E φ₀ ψ₀) x y a b ≤ 0 := by
    dsimp [jensenGap]
    exact sub_nonpos.mpr (le_of_not_gt hbad)
  let d : ℕ → ℝ := fun n => (2 : ℝ) ^ n * jensenGap (phi E φ₀ ψ₀ n) x y a b
  have hdmono : Monotone d := scaled_jensenGap_monotone φ₀ ψ₀ h x y ha.le hb.le hab
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    mul_nonneg (by positivity)
      (jensenGap_nonneg (iterates_properties E φ₀ ψ₀ h n).1 x y ha.le hb.le hab)
  have hupper : ∀ n, d n ≤
      (C * (a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y)) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hp := mul_le_mul_of_nonneg_left
      (phi_le_scaled_theta φ₀ ψ₀ h hφh hψh C hC hcomp n x) ha.le
    have hq := mul_le_mul_of_nonneg_left
      (phi_le_scaled_theta φ₀ ψ₀ h hφh hψh C hC hcomp n y) hb.le
    have hz := (theta_bounds φ₀ ψ₀ h n (a • x + b • y)).2
    have hg : jensenGap (phi E φ₀ ψ₀ n) x y a b ≤
        C / (4 : ℝ) ^ n * (a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y) := by
      dsimp [jensenGap] at hgap ⊢
      nlinarith
    have hratio : (2 : ℝ) ^ n / (4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← div_pow]
      norm_num
    calc d n ≤ (2 : ℝ) ^ n *
          (C / (4 : ℝ) ^ n * (a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by rw [← hratio]; ring
  have ht : Tendsto (fun n =>
      (C * (a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y)) * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (C * (a * theta E φ₀ ψ₀ x + b * theta E φ₀ ψ₀ y))
  have hdlim : Tendsto d atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hd0 hupper
  have hd1 := hdmono.ge_of_tendsto hdlim 1
  have hs1 := (first_arithmeticMean_strict φ₀ ψ₀ h hs).2 hx hy hxy ha hb hab
  change phi E φ₀ ψ₀ 1 (a • x + b • y) <
    a * phi E φ₀ ψ₀ 1 x + b * phi E φ₀ ψ₀ 1 y at hs1
  dsimp [d, jensenGap] at hd1
  norm_num at hd1
  linarith

end ExpandedFA.Asplund.StrictnessPersistence
