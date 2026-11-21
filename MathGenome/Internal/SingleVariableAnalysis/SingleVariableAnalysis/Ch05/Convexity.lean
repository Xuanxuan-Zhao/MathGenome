import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Scalar
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith

/-!
# Convexity and secant slopes

K03.05.convexity (paper.tex:917–929). The predicates retain exactly the
one-parameter formulas of the manuscript. The bridges identify them with
Mathlib's two-weight predicates on real intervals. The secant characterization
then uses the two long-secant inequalities, not just the adjacent-slope bound.
-/

namespace SingleVariableAnalysis

/-- The manuscript's definition of convexity on a real domain. -/
def ConvexFunctionOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f ((1 - t) * x + t * y) ≤ (1 - t) * f x + t * f y

/-- Strict convexity uses distinct points and strictly interior weights. -/
def StrictConvexFunctionOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    f ((1 - t) * x + t * y) < (1 - t) * f x + t * f y

/-- Concavity means convexity of the negative function. -/
def ConcaveFunctionOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ConvexFunctionOn I (fun x => -f x)

/-- The two ordered secant inequalities of the manuscript. -/
def OrderedSecantSlopes (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, x ∈ I → y ∈ I → z ∈ I → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) ∧
      (f z - f x) / (z - x) ≤ (f z - f y) / (z - y)

/-- On an interval, the literal one-weight formula is Mathlib convexity. -/
theorem convexFunctionOn_iff_convexOn (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) :
    ConvexFunctionOn I f ↔ ConvexOn ℝ I f := by
  constructor
  · intro h
    refine ⟨hI.convex, ?_⟩
    intro x hx y hy a b ha hb hab
    have ha' : 1 - b = a := by linarith
    simpa only [ha', smul_eq_mul] using h x hx y hy b hb (by linarith)
  · intro h x hx y hy t ht ht'
    simpa only [smul_eq_mul] using
      h.2 hx hy (sub_nonneg.mpr ht') ht (sub_add_cancel 1 t)

/-- Strict interior weights correspond exactly to positive normalized weights. -/
theorem strictConvexFunctionOn_iff_strictConvexOn
    (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) :
    StrictConvexFunctionOn I f ↔ StrictConvexOn ℝ I f := by
  constructor
  · intro h
    refine ⟨hI.convex, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have ha' : 1 - b = a := by linarith
    simpa only [ha', smul_eq_mul] using h x hx y hy hxy b hb (by linarith)
  · intro h x hx y hy hxy t ht ht'
    simpa only [smul_eq_mul] using
      h.2 hx hy hxy (sub_pos.mpr ht') ht (sub_add_cancel 1 t)

/-- Negation gives the canonical library concavity predicate. -/
theorem concaveFunctionOn_iff_concaveOn (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) :
    ConcaveFunctionOn I f ↔ ConcaveOn ℝ I f := by
  exact (convexFunctionOn_iff_convexOn I hI (fun x => -f x)).trans neg_convexOn_iff

/-- Convexity is equivalent to the full chain of ordered secant slopes.
In the reverse direction interval membership supplies the middle point, so the
chain implies the adjacent-slope criterion. No regularity of `f` is assumed. -/
theorem convexFunctionOn_iff_orderedSecantSlopes
    (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ) :
    ConvexFunctionOn I f ↔ OrderedSecantSlopes I f := by
  rw [convexFunctionOn_iff_convexOn I hI f]
  constructor
  · intro h x y z hx _hy hz hxy hyz
    exact ⟨h.secant_mono_aux2 hx hz hxy hyz, h.secant_mono_aux3 hx hz hxy hyz⟩
  · intro h
    apply convexOn_of_slope_mono_adjacent hI.convex
    intro x y z hx hz hxy hyz
    have hy : y ∈ I := hI.out hx hz ⟨hxy.le, hyz.le⟩
    exact (h x y z hx hy hz hxy hyz).1.trans (h x y z hx hy hz hxy hyz).2

end SingleVariableAnalysis
