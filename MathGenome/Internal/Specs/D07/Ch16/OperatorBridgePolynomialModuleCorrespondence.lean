import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.Equiv.Basic

/-!
Independent specification of the polynomial-module correspondence in
paper.tex:3330–3337 and 3368–3371. All additive and field-module structures
are fixed. A polynomial-module structure is allowed precisely when its
constant polynomials induce the given field action. No finite-dimensionality,
nonzero-vector-space, basis, or algebraicity assumption is imposed.

The two unique-existence statements specify the correspondence in both
directions; the action formula identifies the entire polynomial action,
not merely the generator. The last statement compares the same underlying
functions: polynomial-linear equivalences are exactly field-linear
equivalences intertwining the two given operators, even on different spaces.
-/

universe u v w

namespace Specs.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence

open Polynomial

/-- Extending the *given* scalar action means equality on every constant. -/
def CompatibleAction (F : Type u) [Field F] (V : Type v)
    [AddCommGroup V] [Module F V] (m : Module (Polynomial F) V) : Prop :=
  ∀ (a : F) (x : V), m.smul (C a) x = a • x

/-- Every operator gives exactly one compatible polynomial-module structure. -/
def OperatorToModule : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V),
    ∃! m : Module (Polynomial F) V,
      CompatibleAction F V m ∧ ∀ x : V, m.smul X x = T x

/-- Acting by X in any compatible module recovers exactly one linear operator. -/
def ModuleToOperator : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (m : Module (Polynomial F) V), CompatibleAction F V m →
      ∃! T : Module.End F V, ∀ x : V, T x = m.smul X x

/-- The recovered action is precisely f(T), on every vector and polynomial. -/
def ActionFormula : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V) (m : Module (Polynomial F) V),
    CompatibleAction F V m → (∀ x : V, m.smul X x = T x) →
      ∀ (f : Polynomial F) (x : V), m.smul f x = (aeval T f) x

/-- Equality of the sets of underlying invertible maps, with explicit
intertwining. Both implications retain the actual function on vectors. -/
def EquivalenceCharacterization : Prop :=
  ∀ (F : Type u) [Field F]
    (V : Type v) [AddCommGroup V] [Module F V]
    (W : Type w) [AddCommGroup W] [Module F W]
    (T : Module.End F V) (S : Module.End F W)
    (m : Module (Polynomial F) V) (n : Module (Polynomial F) W),
    CompatibleAction F V m → CompatibleAction F W n →
    (∀ x : V, m.smul X x = T x) → (∀ y : W, n.smul X y = S y) →
    ∀ h : V → W,
      (letI : Module (Polynomial F) V := m
       letI : Module (Polynomial F) W := n
       ∃ e : V ≃ₗ[Polynomial F] W, (e : V → W) = h) ↔
      ∃ e : V ≃ₗ[F] W, (e : V → W) = h ∧ ∀ x : V, e (T x) = S (e x)

end Specs.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
