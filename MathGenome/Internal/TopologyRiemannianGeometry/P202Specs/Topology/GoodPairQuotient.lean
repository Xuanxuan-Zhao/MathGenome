import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Excision
import Mathlib.Topology.Homotopy.Basic

/-! The quotient of a good pair, paper.tex 1340–1372.

`Data` records exactly a nonempty closed subspace and a strong deformation
retraction of an open neighborhood onto it. No separation or CW hypothesis
is imposed on the ambient space. The quotient is the topological quotient
identifying precisely the points of the subspace.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v

namespace P202Specs.GoodPairQuotient
open P202Specs.SingularChains P202Specs.RelativeSingularChains

/-- Equivalence relation for collapsing a subspace to one point. -/
def collapseSetoid (P : Pair.{v}) : Setoid P.space where
  r x y := x = y ∨ (x ∈ P.subspace ∧ y ∈ P.subspace)
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm), by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩⟩

/-- This uses the coinduced quotient topology, not a topology chosen afterwards. -/
def quotientSpace (P : Pair.{v}) : TopCat.{v} :=
  TopCat.of (Quotient (collapseSetoid P))

def quotientProjection (P : Pair.{v}) : P.space ⟶ quotientSpace P :=
  TopCat.ofHom ⟨Quotient.mk (collapseSetoid P), continuous_quot_mk⟩

/-- For nonempty `A`, the second term is precisely the singleton `q(A)`. -/
def quotientPair (P : Pair.{v}) : Pair.{v} :=
  ⟨quotientSpace P, quotientProjection P '' P.subspace⟩

def quotientPairMap (P : Pair.{v}) : P ⟶ quotientPair P :=
  ⟨quotientProjection P, fun x hx => ⟨x, hx, rfl⟩⟩

structure Data where
  pair : Pair.{v}
  nonempty : pair.subspace.Nonempty
  closed : IsClosed pair.subspace
  neighborhood : Set pair.space
  open_neighborhood : IsOpen neighborhood
  subset_neighborhood : pair.subspace ⊆ neighborhood
  deformation : C(unitInterval × neighborhood, neighborhood)
  at_zero : ∀ x, deformation (0, x) = x
  at_one : ∀ x, (deformation (1, x)).val ∈ pair.subspace
  fixes : ∀ (t : unitInterval) (x : neighborhood),
    x.val ∈ pair.subspace → deformation (t, x) = x

/-- The canonical degree identifications specify the ordinary/reduced relative
comparison; an arbitrary abstract isomorphism would not specify the induced map. -/
def IsRelativeComparison (R : Type u) [CommRing R] (P : Pair.{v})
    (c : reduced R R P ≅ ordinary R R P) : Prop :=
  ∀ n : ℕ, c.hom.f (n : ℤ) ≫ (ordinaryDegreeIso R R P n).hom =
    (reducedDegreeIso R R P n).hom

/-- The quotient-induced ordinary-relative to reduced-absolute isomorphism.
The displayed identity says that its composite with the reduced projection
is exactly the map induced by `q : (X,A) → (X/A,q(A))`. It fixes the meaning
of "induces", including degree zero. The projection at the quotient is itself
an isomorphism on reduced homology since its subspace is a point. -/
def isomorphism_type : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Data.{v}),
    ∃ c : reduced R R D.pair ≅ ordinary R R D.pair,
      IsRelativeComparison R D.pair c ∧
      ∀ n : ℕ,
        IsIso (homologyMap (projection (reducedFunctor R R) (quotientPair D.pair))
          (n : ℤ)) ∧
        ∃ e : relativeHomology R R D.pair (n : ℤ) ≅
            reducedHomology R R (quotientSpace D.pair) (n : ℤ),
          homologyMap c.hom (n : ℤ) ≫ e.hom ≫
            homologyMap (projection (reducedFunctor R R) (quotientPair D.pair)) (n : ℤ) =
          homologyMap (relativeMap (reducedFunctor R R) (quotientPairMap D.pair)) (n : ℤ)

/-- Empty second term, with no nonemptiness condition on `X`. -/
def emptyPair (X : TopCat.{v}) : Pair.{v} := ⟨X, ∅⟩

/-- For `A = ∅`, relative chains are ordinary chains through the actual quotient
projection. In particular this statement makes no reduced-quotient assertion. -/
def empty_type : Prop :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{v}),
    ∃ e : ordinary R R (emptyPair X) ≅ ordinaryComplex R R X,
      projection (ordinaryFunctor R R) (emptyPair X) ≫ e.hom = 𝟙 _

end P202Specs.GoodPairQuotient
