import MathGenome.Internal.Specs.D07.Ch12.CompositumDegreeBound
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Degrees of finite composita and the basis criterion for equality. -/

universe u v w s

namespace D07.Ch12.CompositumDegreeBound

open Specs.D07.Ch12.CompositumDegreeBound

theorem finite_compositum : FiniteCompositum.{u, v} := by
  intro K Ω _ _ _ E F _ _
  exact IntermediateField.finiteDimensional_sup E F

theorem cardinal_degree_bound : CardinalDegreeBound.{u, v} := by
  intro K Ω _ _ _ E F _ _
  exact IntermediateField.rank_sup_le_of_isAlgebraic E F (Or.inl inferInstance)

theorem degree_bound : DegreeBound.{u, v} := by
  intro K Ω _ _ _ E F _ _
  exact IntermediateField.finrank_sup_le E F

theorem equality_iff_linearDisjoint : EqualityIffLinearDisjoint.{u, v} := by
  intro K Ω _ _ _ E F _ _
  exact ⟨IntermediateField.LinearDisjoint.of_finrank_sup,
    IntermediateField.LinearDisjoint.finrank_sup⟩

theorem equality_iff_basis_independent : EqualityIffBasisIndependent.{u, v, w} := by
  intro K Ω _ _ _ E F _ _ I b
  constructor
  · intro h
    exact (IntermediateField.LinearDisjoint.of_finrank_sup h).linearIndependent_left
      b.linearIndependent
  · intro h
    exact (IntermediateField.LinearDisjoint.of_basis_left b h).finrank_sup

theorem basis_independence_invariant : BasisIndependenceInvariant.{u, v, w, s} := by
  intro K Ω _ _ _ E F _ _ I J b c
  exact (equality_iff_basis_independent K Ω E F I b).symm.trans
    (equality_iff_basis_independent K Ω E F J c)

end D07.Ch12.CompositumDegreeBound
