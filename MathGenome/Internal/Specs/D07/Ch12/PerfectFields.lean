import MathGenome.Internal.Specs.D07.Ch12.SeparableDefinition
import Mathlib.FieldTheory.Perfect

/-!
Independent statements for K07.12.perfect_fields, paper.tex:3768–3776.

The canonical perfect-field predicate means that every irreducible polynomial
is separable. The equivalence below quantifies over all algebraic extensions,
including ones of infinite algebraic degree, with their specified embeddings.
The extension universe is `max u v`, with arbitrary `v`; thus it includes every
universe at least as large as that of the base. The separate extension theorem
also permits an arbitrary pair of universes without this convention.

Positive characteristic is stated as `CharP K p` and `0 < p`. Primality follows
from the field hypothesis and is not an extra assumption. The finite-field
statement means a finite underlying set, not merely finite extension degree.
-/

universe u v

namespace Specs.D07.Ch12.PerfectFields

def PerfectPredicateType := ∀ (K : Type u) [Field K], Prop

def perfectPredicateValue : PerfectPredicateType.{u} :=
  fun K _ => PerfectField K

/-- The defining polynomial characterization, including nonmonic irreducibles. -/
def PerfectIffIrreducibleSeparable : Prop :=
  ∀ (K : Type u) [Field K],
    perfectPredicateValue K ↔
      ∀ f : Polynomial K, Irreducible f →
        SeparableDefinition.polynomialSeparableValue K f

/-- The two conditions in the source's equivalence. -/
def EquivalentCriteria : Prop :=
  ∀ (K : Type u) [Field K],
    (∀ f : Polynomial K, Irreducible f →
      SeparableDefinition.polynomialSeparableValue K f) ↔
    ∀ (L : Type (max u v)) [Field L] [Algebra K L],
      Algebra.IsAlgebraic K L → SeparableDefinition.extensionSeparableValue K L

def AlgebraicExtensionSeparable : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    perfectPredicateValue K → Algebra.IsAlgebraic K L →
      SeparableDefinition.extensionSeparableValue K L

def CharacteristicZeroPerfect : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K], perfectPredicateValue K

def FiniteFieldPerfect : Prop :=
  ∀ (K : Type u) [Field K] [Finite K], perfectPredicateValue K

def PerfectIffFrobeniusSurjective : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p], 0 < p →
    (perfectPredicateValue K ↔ Function.Surjective (fun a : K => a ^ p))

/-- The Frobenius properties used in the source proof do not need perfection. -/
def FrobeniusProperties : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p], 0 < p →
    (∀ a b : K, (a + b) ^ p = a ^ p + b ^ p) ∧
    (∀ a b : K, (a * b) ^ p = a ^ p * b ^ p) ∧
    Function.Injective (fun a : K => a ^ p)

end Specs.D07.Ch12.PerfectFields
