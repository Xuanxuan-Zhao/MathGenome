import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
Independent specification of `K07.05.class_equation`, paper.tex:899–909.
`ConjClasses` is the quotient by conjugacy, and its carrier is the actual
set of conjugates. The noncenter predicate means the carrier has at least
two elements; the first obligation identifies it with noncentrality in G.
The equations allow every finite group, including the trivial group.
Representatives are indexed by the distinct noncentral classes, with an
arbitrary member chosen from each; no preferred choice is imposed.
-/

namespace Specs.D07.Ch05.ClassEquation

universe u

/-- Exactly the conjugacy classes of elements outside the center are nontrivial. -/
def NoncentralClassCriterion : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    ConjClasses.mk x ∈ ConjClasses.noncenter G ↔ x ∉ Subgroup.center G

/-- The representative-free form: each distinct noncentral class is counted once. -/
def ClassEquationCardinalities : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    letI := Fintype.ofFinite ↥(ConjClasses.noncenter G)
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ c : ↥(ConjClasses.noncenter G), Nat.card ↥c.val.carrier

/-- The displayed source formula, for any choice of one member of each class. -/
def ClassEquationIndices : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (x : ↥(ConjClasses.noncenter G) → G),
    (∀ c, x c ∈ c.val.carrier) →
    letI := Fintype.ofFinite ↥(ConjClasses.noncenter G)
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ c : ↥(ConjClasses.noncenter G), (Subgroup.centralizer {x c}).index

/-- The same formula with an arbitrary finite set of representatives.
Bijectivity on the set says precisely that it meets each noncentral class
once and meets no central class. -/
def ClassEquationRepresentativeSet : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (R : Finset G),
    Set.BijOn ConjClasses.mk (R : Set G) (ConjClasses.noncenter G) →
    Nat.card G = Nat.card (Subgroup.center G) +
      ∑ x ∈ R, (Subgroup.centralizer {x}).index

end Specs.D07.Ch05.ClassEquation
