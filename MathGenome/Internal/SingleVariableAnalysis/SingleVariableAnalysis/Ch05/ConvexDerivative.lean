import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.ConvexDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Monotonicity
import Mathlib.Analysis.Convex.Deriv

/-!
# Convexity and derivatives

K03.05.convex_derivative, paper.tex:931–941. All domains are open real
intervals, including unbounded ones. Derivatives need not be continuous.
The secant bounds use Mathlib's limit-of-secants results. The tangent
criterion follows from the upstream mean value theorem in each ordering
of the two points; its converse is the weighted cancellation argument.
The second derivative criterion uses the upstream monotonicity theorem
and its necessity direction, applied to the first derivative.
-/

namespace SingleVariableAnalysis

open Set

/-- The derivative bounds the secant from either endpoint. -/
theorem convex_derivative_secant_bounds (I : Set ℝ) (_hopen : IsOpen I)
    (hI : I.OrdConnected) (f : ℝ → ℝ)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ f x) (hf : ConvexFunctionOn I f)
    (x : ℝ) (hx : x ∈ I) (y : ℝ) (hy : y ∈ I) (hxy : x < y) :
    deriv f x ≤ (f y - f x) / (y - x) ∧
      (f y - f x) / (y - x) ≤ deriv f y := by
  have hc := (convexFunctionOn_iff_convexOn I hI f).mp hf
  simpa only [slope_def_field] using
    And.intro (hc.deriv_le_slope hx hy hxy (hd x hx))
      (hc.slope_le_deriv hx hy hxy (hd y hy))

/-- Convexity is exactly monotonicity of the first derivative. -/
theorem convex_iff_monotone_derivative (I : Set ℝ) (hopen : IsOpen I)
    (hI : I.OrdConnected) (f : ℝ → ℝ)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ f x) :
    ConvexFunctionOn I f ↔ MonotoneOn (deriv f) I := by
  constructor
  · intro hf x hx y hy hxy
    rcases hxy.eq_or_lt with heq | hlt
    · exact heq ▸ le_rfl
    have hb := convex_derivative_secant_bounds I hopen hI f hd hf x hx y hy hlt
    exact hb.1.trans hb.2
  · intro hm
    apply (convexFunctionOn_iff_convexOn I hI f).mpr
    apply MonotoneOn.convexOn_of_deriv hI.convex
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · simpa only [hopen.interior_eq] using
        (show DifferentiableOn ℝ f I from fun x hx => (hd x hx).differentiableWithinAt)
    · simpa only [hopen.interior_eq] using hm

/-- A monotone derivative supplies a supporting tangent in both point orders. -/
theorem tangent_support_of_monotone_derivative (I : Set ℝ) (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hd : ∀ x ∈ I, DifferentiableAt ℝ f x)
    (hm : MonotoneOn (deriv f) I) (x : ℝ) (hx : x ∈ I)
    (y : ℝ) (hy : y ∈ I) : f x + deriv f x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | heq | hyx
  · have hseg : Icc x y ⊆ I := hI.out hx hy
    obtain ⟨c, hc, heq⟩ := lagrange_deriv f x y hxy
      (fun t ht => (hd t (hseg ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hseg (Ioo_subset_Icc_self ht)))
    have hle := hm hx (hseg (Ioo_subset_Icc_self hc)) hc.1.le
    have hmul := mul_le_mul_of_nonneg_right hle (sub_nonneg.mpr hxy.le)
    linarith
  · subst y
    simp
  · have hseg : Icc y x ⊆ I := hI.out hy hx
    obtain ⟨c, hc, heq⟩ := lagrange_deriv f y x hyx
      (fun t ht => (hd t (hseg ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hseg (Ioo_subset_Icc_self ht)))
    have hle := hm (hseg (Ioo_subset_Icc_self hc)) hx hc.2.le
    have hmul := mul_le_mul_of_nonneg_right hle (sub_nonneg.mpr hyx.le)
    linarith

/-- Every tangent supports the graph if and only if the function is convex. -/
theorem convex_iff_tangent_support (I : Set ℝ) (hopen : IsOpen I)
    (hI : I.OrdConnected) (f : ℝ → ℝ)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ f x) :
    ConvexFunctionOn I f ↔
      ∀ x ∈ I, ∀ y ∈ I, f x + deriv f x * (y - x) ≤ f y := by
  constructor
  · intro hf
    exact tangent_support_of_monotone_derivative I hI f hd
      ((convex_iff_monotone_derivative I hopen hI f hd).mp hf)
  · intro hs x hx y hy t ht ht1
    let z := (1 - t) * x + t * y
    have hz : z ∈ I := by
      simpa only [z, smul_eq_mul] using
        hI.convex hx hy (sub_nonneg.mpr ht1) ht (sub_add_cancel 1 t)
    have hleft := mul_le_mul_of_nonneg_left (hs z hz x hx) (sub_nonneg.mpr ht1)
    have hright := mul_le_mul_of_nonneg_left (hs z hz y hy) ht
    have hsum := add_le_add hleft hright
    have hcancel :
        (1 - t) * (f z + deriv f z * (x - z)) +
          t * (f z + deriv f z * (y - z)) = f z := by
      dsimp only [z]
      ring
    rw [hcancel] at hsum
    exact hsum

/-- Twice differentiability suffices; continuity of the second derivative
is not a hypothesis. -/
theorem convex_iff_second_derivative_nonnegative (I : Set ℝ) (hopen : IsOpen I)
    (hI : I.OrdConnected) (f : ℝ → ℝ)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ f x)
    (hdd : ∀ x ∈ I, DifferentiableAt ℝ (deriv f) x) :
    ConvexFunctionOn I f ↔ ∀ x ∈ I, 0 ≤ deriv (deriv f) x := by
  rw [convex_iff_monotone_derivative I hopen hI f hd]
  constructor
  · intro hm x hx
    exact monotone_derivative_nonnegative (deriv f) I x (deriv (deriv f) x)
      hm (by simpa only [hopen.interior_eq] using hx) (hdd x hx).hasDerivAt
  · intro hnonneg
    apply nonnegative_derivative_monotone (deriv f) I hI
      (fun x hx => (hdd x hx).continuousAt.continuousWithinAt)
    · simpa only [hopen.interior_eq] using hdd
    · simpa only [hopen.interior_eq] using hnonneg

end SingleVariableAnalysis
