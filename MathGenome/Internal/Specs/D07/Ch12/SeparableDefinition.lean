import MathGenome.Internal.Specs.D07.Ch12.SplittingDefinition
import Mathlib.FieldTheory.Separable

/-!
Independent specification of K07.12.separable_definition,
paper.tex:3733–3746 (chapters/M07.12.tex:192–205).

All fields are arbitrary, with their specified embeddings `Algebra K L`.
The canonical library predicates are fixed below, and their agreement with
the source definitions is an explicit proof obligation: simple roots means
root multiplicity exactly one in a field where the polynomial splits.
The polynomial must be nonzero in that characterization. Nonzero constants
are included. Element and extension separability imply algebraicity; no
finite-degree, characteristic or algebraically-closedness assumption is used.
-/

universe u v w

namespace Specs.D07.Ch12.SeparableDefinition

open Polynomial

def PolynomialPredicateType :=
  ∀ (K : Type u) [Field K], Polynomial K → Prop

def polynomialSeparableValue : PolynomialPredicateType.{u} :=
  fun _ _ f => f.Separable

def ElementPredicateType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], L → Prop

def elementSeparableValue : ElementPredicateType.{u, v} :=
  fun K _ _ _ _ α => IsSeparable K α

def ExtensionPredicateType :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Prop

def extensionSeparableValue : ExtensionPredicateType.{u, v} :=
  fun K L _ _ _ => Algebra.IsSeparable K L

/-- Zero is excluded by the canonical predicate itself. -/
def PolynomialNonzero : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K),
    polynomialSeparableValue K f → f ≠ 0

/-- This applies to every splitting field, and even to any larger field in
which f splits. The embedding used for evaluation and coefficients is the
same. Only actual roots are required to have multiplicity exactly one. -/
def SimpleRootsCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), f ≠ 0 → (f.map (algebraMap K L)).Splits →
    (polynomialSeparableValue K f ↔
      ∀ a : L, aeval a f = 0 → (f.map (algebraMap K L)).rootMultiplicity a = 1)

/-- Every base-preserving isomorphism preserves each root's multiplicity,
including multiplicity zero at nonroots. -/
def MultiplicityTransport : Prop :=
  ∀ (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L ≃ₐ[K] E) (f : Polynomial K) (a : L),
    (f.map (algebraMap K L)).rootMultiplicity a =
      (f.map (algebraMap K E)).rootMultiplicity (e a)

/-- The full source splitting-field predicate includes splitting and
generation by roots. Neither realization is a chosen canonical field. -/
def SplittingFieldIndependence : Prop :=
  ∀ (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (f : Polynomial K),
    SplittingDefinition.splittingFieldValue K L f →
    SplittingDefinition.splittingFieldValue K E f →
    ((∀ a : L, aeval a f = 0 → (f.map (algebraMap K L)).rootMultiplicity a = 1) ↔
      ∀ a : E, aeval a f = 0 → (f.map (algebraMap K E)).rootMultiplicity a = 1)

/-- Algebraicity is explicit, and the minimal polynomial is the canonical
one from the upstream minimal-polynomial specifications. -/
def ElementCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    elementSeparableValue K L α ↔
      IsAlgebraic K α ∧ polynomialSeparableValue K (minpoly K α)

/-- This is algebraic extension separability, including extensions of
infinite algebraic degree. -/
def ExtensionCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    extensionSeparableValue K L ↔
      Algebra.IsAlgebraic K L ∧ ∀ α : L, elementSeparableValue K L α

/-- A separable annihilator already forces algebraicity. This formulation
therefore includes the source's equivalence for every algebraic element. -/
def SeparableAnnihilator : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    elementSeparableValue K L α ↔
      ∃ f : Polynomial K, polynomialSeparableValue K f ∧ aeval α f = 0

end Specs.D07.Ch12.SeparableDefinition
