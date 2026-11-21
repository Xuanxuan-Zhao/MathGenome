import MathGenome.Internal.Specs.D05.M09.Diagonalizable
import MathGenome.Internal.Specs.D05.M08.Minpoly
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Nilpotent.Defs

/-! Independent statement of K05.10.additive_decomposition, paper.tex:1579–1587.
All eigenvalues and polynomial coefficients are in the original field. Uniqueness
is among all commuting diagonalizable–nilpotent pairs, without a polynomial
hypothesis on the competing pair. Finite dimension includes the zero space. -/

namespace Specs.D05.M10.AdditiveDecomposition

noncomputable def decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    (Specs.D05.M08.Minpoly.minimalPolynomial_value K V T).Splits →
    ∃ D N : Module.End K V,
      T = D + N ∧
      Specs.D05.M09.Diagonalizable.diagonalizable_value K V D ∧
      IsNilpotent N ∧ Commute D N ∧
      (∃ p : Polynomial K, Polynomial.aeval T p = D) ∧
      (∃ q : Polynomial K, Polynomial.aeval T q = N) ∧
      ∀ D' N' : Module.End K V,
        T = D' + N' →
        Specs.D05.M09.Diagonalizable.diagonalizable_value K V D' →
        IsNilpotent N' → Commute D' N' → D' = D ∧ N' = N

end Specs.D05.M10.AdditiveDecomposition
