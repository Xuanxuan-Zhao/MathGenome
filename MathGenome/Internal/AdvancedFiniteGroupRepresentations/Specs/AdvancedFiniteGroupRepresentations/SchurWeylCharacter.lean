import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.MultiplicityTraceAverage
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.LengthBound

/-! FR-D08, character assertion, lines 1585–1615. A basis indexed by `Fin d`
expresses dimension d without excluding d = 0. The operator on L is the
postcomposition operator on the original equivariant Hom space. Evaluation
of the canonical Schur polynomial is defined for every complex alphabet;
the trace comparison only requires an invertible diagonal operator. -/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The Frobenius polynomial formula at every complex alphabet, including
coordinates equal to zero. Together with the diagonal trace formula this
is the polynomial extension of the diagonal character. -/
def schur_character_polynomialType : Prop :=
  ∀ {n : ℕ} (p : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    InheritedSpechtAction p ρ → ∀ (d : ℕ) (x : Fin d → ℂ),
    MvPolynomial.eval x (schurPolynomial p d) =
      ∑ ν : Partition n, (representationClassFunction ρ (cycleClass ν) / (zFactor ν : ℂ)) *
        MvPolynomial.eval x (partitionPowerSum d ν)

/-- Weyl's diagonal character formula in any chosen basis. -/
def schurWeyl_diagonal_characterType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n d : ℕ} (p : Partition n) (b : Module.Basis (Fin d) ℂ V)
    (x : Fin d → ℂ), (∀ i, x i ≠ 0) → ∀ g : LinearGroup V,
    (∀ i, g (b i) = x i • b i) →
    LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) =
      MvPolynomial.eval x (schurPolynomial p d)

/-- Both the character and its polynomial extension vanish above the length
cutoff. No diagonalizability assumption is needed for the trace vanishing. -/
def schurWeyl_character_length_cutoffType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n d : ℕ} (p : Partition n) (_b : Module.Basis (Fin d) ℂ V), d < length p →
    ∀ (g : LinearGroup V) (x : Fin d → ℂ),
    LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) = 0 ∧
      MvPolynomial.eval x (schurPolynomial p d) = 0

/-- The empty shape has character one, including the zero-dimensional
vector space and empty alphabet. -/
def schurWeyl_empty_characterType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (g : LinearGroup V) (x : Fin d → ℂ),
    LinearMap.trace ℂ (TensorMultiplicity V emptyPartition)
      (tensorMultiplicityOperator V emptyPartition g) = 1 ∧
    MvPolynomial.eval x (schurPolynomial emptyPartition d) = 1

end Specs.AdvancedFiniteGroupRepresentations
