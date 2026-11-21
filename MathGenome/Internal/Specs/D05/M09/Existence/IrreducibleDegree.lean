import MathGenome.Internal.Specs.D05.M09.Existence.QuotientFieldBasis
import Mathlib.Basic.Real.Basic

/-! Independent statements for the degree-divisibility obstruction and its
real quadratic consequence in paper.tex:1320–1326. Kernels carry their
inherited scalar structures; no nonzero-space or splitting assumption is made. -/

namespace Specs.D05.M09.Existence.IrreducibleDegree

/-- The degree of an irreducible polynomial divides the dimension of the
kernel of its value at the original operator. -/
def degree_dvd_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K),
    Irreducible p →
      p.natDegree ∣ Module.finrank K (LinearMap.ker (Polynomial.aeval T p))

/-- Completing the square, with the original coefficients. -/
def quadratic_complete_square : Prop :=
  ∀ (b c x : ℝ),
    x ^ 2 + b * x + c = (x + b / 2) ^ 2 + c - b ^ 2 / 4

/-- Negative discriminant excludes every real root. -/
def quadratic_no_real_root : Prop :=
  ∀ (b c : ℝ), b ^ 2 < 4 * c →
    ∀ x : ℝ, Polynomial.eval x
      (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠ 0

/-- The same formal quadratic is irreducible over the real field. -/
def quadratic_irreducible : Prop :=
  ∀ (b c : ℝ), b ^ 2 < 4 * c →
    Irreducible (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c)

/-- Evenness concerns this particular kernel, including the zero kernel. -/
def quadratic_kernel_even : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (b c : ℝ), b ^ 2 < 4 * c →
      Even (Module.finrank ℝ (LinearMap.ker (T ^ 2 + b • T + c • 1)))

end Specs.D05.M09.Existence.IrreducibleDegree
