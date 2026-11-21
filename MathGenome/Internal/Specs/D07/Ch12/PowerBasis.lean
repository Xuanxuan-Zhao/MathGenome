import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition
import MathGenome.Internal.Specs.D07.Ch12.MinpolyDivisibility
import Mathlib.LinearAlgebra.Basis.Defs

/-!
Independent specification for K07.12.power_basis, paper.tex:3607–3613.
The chosen `Algebra K L` is the specified embedding. Only α is assumed
algebraic, with no finiteness or algebraicity premise on the ambient extension.
The generated field and minimal polynomial are the same canonical objects as
in the upstream specifications. `degree` includes the bottom value for zero;
thus the representative assertion includes the zero element and polynomial.
-/

universe u v

namespace Specs.D07.Ch12.PowerBasis

/-- The positive degree indexes a basis consisting of the first powers of α,
as elements of the generated intermediate field with its inherited scalars. -/
def PowerBasisExists : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      0 < (minpoly K α).natDegree ∧
      ∃ b : Module.Basis (Fin (minpoly K α).natDegree) K
          (IntermediateField.adjoin K {α}),
        ∀ i, (b i : L) = α ^ (i : ℕ)

/-- Existence and uniqueness range over all formal polynomials of degree
strictly below that of the minimal polynomial, evaluated using the chosen map. -/
def UniquePolynomialRepresentative : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α → ∀ x : IntermediateField.adjoin K {α},
      ∃! p : Polynomial K,
        p.degree < (minpoly K α).degree ∧ Polynomial.aeval α p = (x : L)

end Specs.D07.Ch12.PowerBasis
