import MathGenome.Internal.Specs.D07.Ch12.DerivativeCriterion

/-!
Independent statements for K07.12.characteristic_zero_separability,
paper.tex:3752–3759 (chapters/M07.12.tex:211–218).

The separability predicates are the canonical upstream predicates, already
identified with simple roots and separable minimal polynomials. The extension
has its specified embedding and may have infinite algebraic degree. Neither
finite dimensionality nor an algebraically closed ambient field is assumed.
-/

universe u v

namespace Specs.D07.Ch12.CharacteristicZeroSeparability

def IrreduciblePolynomialSeparable : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : Polynomial K),
    Irreducible f → SeparableDefinition.polynomialSeparableValue K f

def AlgebraicExtensionSeparable : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [CharZero K],
    Algebra.IsAlgebraic K L → SeparableDefinition.extensionSeparableValue K L

end Specs.D07.Ch12.CharacteristicZeroSeparability
