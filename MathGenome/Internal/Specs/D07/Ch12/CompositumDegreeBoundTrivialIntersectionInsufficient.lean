import MathGenome.Internal.Specs.D07.Ch14.CubicSplittingExample
import Mathlib.FieldTheory.LinearDisjoint

/-!
The counterexample in K07.12.compositum_degree_bound (paper.tex:3676),
using the concrete fields of K07.14.cubic_splitting_example. The ambient
field is Q(a, ζ), with a the positive real cube root of 2. All scalar
maps and subfields are the canonical compatible ones of that upstream
specification. The infimum is intersection and the supremum is compositum.
-/
namespace Specs.D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient

open IntermediateField
open Specs.D07.Ch14.CubicSplittingExample

/-- Full data for the two displayed cubic fields, including their actual
failure of linear disjointness and the strict degree inequality 6 < 3 * 3. -/
def CounterexampleAt (ζ : ℂ) : Prop :=
  FiniteDimensional ℚ (L ζ) ∧
  Polynomial.IsSplittingField ℚ (L ζ) cubic ∧
  IsGalois ℚ (L ζ) ∧
  Nonempty ((L ζ ≃ₐ[ℚ] L ζ) ≃* Equiv.Perm (Fin 3)) ∧
  cubicField ζ 0 ≠ cubicField ζ 1 ∧
  FiniteDimensional ℚ (cubicField ζ 0) ∧
  FiniteDimensional ℚ (cubicField ζ 1) ∧
  Module.finrank ℚ (cubicField ζ 0) = 3 ∧
  Module.finrank ℚ (cubicField ζ 1) = 3 ∧
  cubicField ζ 0 ⊓ cubicField ζ 1 = ⊥ ∧
  cubicField ζ 0 ⊔ cubicField ζ 1 = ⊤ ∧
  Module.finrank ℚ (L ζ) = 6 ∧
  Module.finrank ℚ ↥(cubicField ζ 0 ⊔ cubicField ζ 1) = 6 ∧
  Module.finrank ℚ ↥(cubicField ζ 0 ⊔ cubicField ζ 1) <
    Module.finrank ℚ (cubicField ζ 0) * Module.finrank ℚ (cubicField ζ 1) ∧
  ¬ (cubicField ζ 0).LinearDisjoint (cubicField ζ 1)

/-- Either primitive cube root gives the source's example. -/
def CubicCounterexample : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → CounterexampleAt ζ

/-- A witness exists; the primitive-root premise is not vacuous. -/
def ExistsCubicCounterexample : Prop :=
  ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 ∧ CounterexampleAt ζ

end Specs.D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient
