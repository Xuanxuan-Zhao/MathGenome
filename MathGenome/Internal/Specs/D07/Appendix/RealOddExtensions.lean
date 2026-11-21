import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Independent specification of `lem:real-no-odd-extension`, paper.tex:7572–7590.
Odd natural degree excludes the zero polynomial and degree-zero polynomials.
An extension is given by its specified `Algebra ℝ E` structure, without any
order or topology on E. Finiteness means vector-space dimension, not a finite
underlying field. The conclusion concerns this same structure map.
-/

universe u

namespace Specs.D07.Appendix.RealOddExtensions

/-- Every odd-degree real polynomial has a real zero. -/
def OddPolynomialHasRealZero : Prop :=
  ∀ f : Polynomial ℝ, Odd f.natDegree → ∃ x : ℝ, f.eval x = 0

/-- Every finite odd-degree extension of ℝ consists of its specified real scalars. -/
def OddExtensionSurjective : Prop :=
  ∀ (E : Type u) [Field E] [Algebra ℝ E] [FiniteDimensional ℝ E],
    Odd (Module.finrank ℝ E) → Function.Surjective (algebraMap ℝ E)

end Specs.D07.Appendix.RealOddExtensions
