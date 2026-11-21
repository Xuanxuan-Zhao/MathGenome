import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LinearJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import Mathlib.Algebra.Lie.BaseChange

/-!
LA-B03 (source lines 729–782; the finite-dimensional convention is at
lines 597–600). The Jordan components below are the original endomorphisms
and use the shared, geometric definition of Jordan decomposition. The
bracket inclusion is valid without a splitting assumption; in particular
it applies over every splitting field. Descent uses the actual Lie bracket
on the scalar extension, not an assumed certificate for the components.
-/

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.JordanDerivations

open _root_.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
open scoped TensorProduct

/-- The generalized eigenspace bracket inclusion, in particular over a splitting field. -/
def generalized_eigenspace_bracket_type : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (D : LieDerivation k G G) (a b : k) (x y : G),
    x ∈ Module.End.maxGenEigenspace D.toLinearMap a →
    y ∈ Module.End.maxGenEigenspace D.toLinearMap b →
    ⁅x, y⁆ ∈ Module.End.maxGenEigenspace D.toLinearMap (a + b)

/-- The derivation identity extends and descends along any field extension. -/
def derivation_baseChange_iff_type : Prop :=
  ∀ {k : Type u} [Field k] {K : Type w} [Field K] [Algebra k K]
    {G : Type v} [LieRing G] [LieAlgebra k G] (f : Module.End k G),
    (∀ x y : K ⊗[k] G,
      f.baseChange K ⁅x, y⁆ = ⁅f.baseChange K x, y⁆ + ⁅x, f.baseChange K y⁆) ↔
    (∀ x y : G, f ⁅x, y⁆ = ⁅f x, y⁆ + ⁅x, f y⁆)

/-- Both components of every Jordan decomposition of a derivation are derivations. -/
def jordan_components_are_derivations_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
    (D : LieDerivation k G G) (s n : Module.End k G),
    IsJordanDecomposition D.toLinearMap s n →
    s ∈ derivations_subalgebra_value k G ∧ n ∈ derivations_subalgebra_value k G

/-- The polynomial Jordan decomposition can be formed inside the derivations. -/
def jordan_decomposition_derivations_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
    (D : LieDerivation k G G),
    ∃ s n : LieDerivation k G G,
      IsJordanDecomposition D.toLinearMap s.toLinearMap n.toLinearMap ∧
      (∃ p q : Polynomial k,
        Polynomial.aeval D.toLinearMap p = s.toLinearMap ∧
        Polynomial.aeval D.toLinearMap q = n.toLinearMap) ∧
      (∀ W : Submodule k G, (∀ x ∈ W, D x ∈ W) →
        (∀ x ∈ W, s x ∈ W) ∧ (∀ x ∈ W, n x ∈ W)) ∧
      (∀ s' n' : Module.End k G, IsJordanDecomposition D.toLinearMap s' n' →
        s' = s.toLinearMap ∧ n' = n.toLinearMap)

end Specs.LieAlgebrasAndRepresentations.JordanDerivations
