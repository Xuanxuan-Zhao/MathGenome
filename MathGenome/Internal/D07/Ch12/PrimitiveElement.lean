import MathGenome.Internal.Specs.D07.Ch12.PrimitiveElement
import MathGenome.Internal.D07.Ch12.PerfectFields
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import MathGenome.Internal.D07.Ch12.PrimitiveElementInseparableNonsimpleExample
import MathGenome.Internal.D07.Ch12.FiniteAlgebraicAlgebraicClosureInfiniteDegree
import Mathlib.FieldTheory.PrimitiveElement

/-!
The primitive element theorem and its boundaries, K07.12.primitive_element.

Mathlib's theorem has exactly the finite-dimensional, separable hypotheses.
Its finite-base branch uses cyclicity of the finite multiplicative group; its
infinite-base branch combines pairs of separable generators by avoiding
finitely many coefficients and then inducts on finite field generation.
Perfectness supplies separability in both special cases in the source.

The two counterexamples are assembled from the allocated upstream proofs,
using their actual rational-function model and arbitrary rational closures.
No separability is added to either counterexample and no complex closedness
assumption is used.
-/

universe u v

namespace D07.Ch12.PrimitiveElement

open Specs.D07.Ch12.PrimitiveElement

theorem finite_separable_simple : FiniteSeparableSimple.{u, v} := by
  intro K E _ _ _ _ hsep
  let : Algebra.IsSeparable K E := hsep
  exact Field.exists_primitive_element K E

theorem cardinal_finite_separable_simple : CardinalFiniteSeparableSimple.{u, v} := by
  intro K E _ _ _ hfinite hsep
  let : FiniteDimensional K E :=
    (DegreeDefinition.finite_iff_finiteDimensional K E).mp hfinite
  exact finite_separable_simple K E hsep

theorem characteristic_zero_simple : CharacteristicZeroSimple.{u, v} := by
  intro K E _ _ _ _ _
  have hsep := PerfectFields.algebraic_extension_separable K E
    (PerfectFields.characteristic_zero_perfect K) (Algebra.IsAlgebraic.of_finite K E)
  exact finite_separable_simple K E hsep

theorem finite_base_simple : FiniteBaseSimple.{u, v} := by
  intro K E _ _ _ _ _
  have hsep := PerfectFields.algebraic_extension_separable K E
    (PerfectFields.finite_field_perfect K) (Algebra.IsAlgebraic.of_finite K E)
  exact finite_separable_simple K E hsep

theorem inseparable_counterexample : InseparableCounterexample := by
  intro p _
  obtain ⟨hind, hgen⟩ := PrimitiveElementInseparableNonsimpleExample.rational_function_model p
  obtain ⟨hfinite, halg, hnat, hcard⟩ :=
    PrimitiveElementInseparableNonsimpleExample.degree_and_algebraicity p
  exact ⟨hind, hgen, PrimitiveElementInseparableNonsimpleExample.monomial_basis p,
    hfinite, halg, hnat, hcard, PrimitiveElementInseparableNonsimpleExample.powers_in_base p,
    PrimitiveElementInseparableNonsimpleExample.simple_degree_bound p,
    PrimitiveElementInseparableNonsimpleExample.not_simple p⟩

theorem algebraic_closure_counterexample : AlgebraicClosureCounterexample.{u} := by
  intro Ω _ _ _ _
  obtain ⟨halg, hinfinite, hrank, hnonsimple⟩ :=
    FiniteAlgebraicAlgebraicClosureInfiniteDegree.closure_infinite_and_not_simple Ω
  exact ⟨halg, hinfinite, hrank,
    FiniteAlgebraicAlgebraicClosureInfiniteDegree.roots_of_every_degree Ω, hnonsimple⟩

end D07.Ch12.PrimitiveElement
