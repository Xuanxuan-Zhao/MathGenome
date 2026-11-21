import MathGenome.Internal.Specs.D05.M08.RestrictionMinpoly
import MathGenome.Internal.Specs.D05.M09.MinpolyCriterion
import MathGenome.Internal.Specs.D05.M10.Triangularization

/-! Independent specifications for paper.tex:1236, K05.08.restriction_minpoly.
The subspace and quotient operators are the canonical upstream constructions.
All splitting and eigenbasis assertions use the original field. Zero spaces,
zero subspaces and the whole subspace are included. -/

noncomputable section

namespace Specs.D05.M08.RestrictionMinpoly.Inheritance

open Polynomial
open Specs.D05.M06.Invariant
open Specs.D05.M09.Diagonalizable
open Specs.D05.M10.Triangularization

/-- A divisor of a nonzero split polynomial splits over the same field. -/
def divisor_splits : Prop :=
  ∀ {K : Type*} [Field K] (p q : Polynomial K),
    p ≠ 0 → p.Splits → q ∣ p → q.Splits

/-- Every divisor has distinct linear factors, up to its leading coefficient.
No monicity assumption is imposed on the divisor; `t ⊆ s` also records that
no new roots appear. The empty set handles nonzero constants. -/
def divisor_distinct_linear_factors : Prop :=
  ∀ {K : Type*} [Field K] (s : Finset K) (q : Polynomial K),
    q ∣ ∏ a ∈ s, (X - C a) →
    ∃ t : Finset K, t ⊆ s ∧ q = C q.leadingCoeff * ∏ a ∈ t, (X - C a)

def restriction_triangularizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    HasUpperTriangularBasis T →
      HasUpperTriangularBasis (restriction_value K V U T h)

def quotient_triangularizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    HasUpperTriangularBasis T →
      HasUpperTriangularBasis (inducedMap_value K V U T h)

def restriction_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    diagonalizable_value K V T →
      diagonalizable_value K U (restriction_value K V U T h)

def quotient_diagonalizable : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : Submodule K V) (T : Module.End K V) (h : invariant_value K V U T),
    diagonalizable_value K V T →
      diagonalizable_value K (V ⧸ U) (inducedMap_value K V U T h)

end Specs.D05.M08.RestrictionMinpoly.Inheritance
