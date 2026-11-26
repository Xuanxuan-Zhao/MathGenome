import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import Mathlib.LinearAlgebra.TensorProduct.Tower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.AdjointCocharacters

open CentralTorus (IsSchemeCentre)
open CharacterDescent (Cocharacter GeometricCharacters)
open DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)
open GeometricRadicals (IsMaximalTorus IsReductive IsSemisimple IsTorus)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (RepresentsQuotient)
open SmoothnessAndIsogenies (pullbackCharacter)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable {k : Type u} [Field k]

/-- The affine adjoint quotient represents right cosets by the full scheme centre. -/
def IsAdjointQuotient {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val) : Prop :=
  IsSchemeCentre Z ∧ IsSchemeKernel q Z ∧ RepresentsQuotient Z q ∧
    Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
    LocallyOfFinitePresentation q.hom.hom.left

/-- The full inverse image is a torus, witnessed on the underlying schemes by a pullback. -/
def IsMaximalTorusPreimage {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    (T' : ClosedSubgroup Q.val) (T : ClosedSubgroup G.val) (p : T.group ⟶ T'.group) : Prop :=
  IsPullback T.inclusion.hom.hom p.hom.hom q.hom.hom T'.inclusion.hom.hom ∧
    IsMaximalTorus T ∧ IsGeometricallyMaximal T ∧
    Flat p.hom.hom.left ∧ Surjective p.hom.hom.left

/-- Precomposition with this endomorphism multiplies a cocharacter by `n`. -/
def powerOnGm (k : Type u) [Field k] (n : ℕ) :
    Cocharacter (specGroup (groupAlgebra k IntegerCharacters.{u})) :=
  specGroupMap (groupAlgebraMap k (powMonoidHom n))

private theorem existsHopfPresentation (G : AffineAlgebraicGroup k) :
    ∃ A : (HopfAlgebraCategory k)ᵒᵖ,
      Nonempty ((hopfSpec (CommRingCat.of k)).obj A ≅ G.val) :=
  essImage_hopfSpec.mpr G.property.1

/-- A Hopf algebra presenting the coordinate algebra and group operations of an affine group. -/
def coordinateHopf (G : AffineAlgebraicGroup k) : HopfAlgebraCategory k :=
  (existsHopfPresentation G).choose.unop

/-- The spectrum comparison for the chosen presentation. -/
def coordinateHopfIso (G : AffineAlgebraicGroup k) : specGroup (coordinateHopf G) ≅ G.val :=
  Classical.choice (existsHopfPresentation G).choose_spec

/-- Pullback on the presented coordinate Hopf algebras. -/
def coordinateHopfMap {G H : AffineAlgebraicGroup k} (f : G.val ⟶ H.val) :
    coordinateHopf H ⟶ coordinateHopf G :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((coordinateHopfIso G).hom ≫ f ≫ (coordinateHopfIso H).inv)).unop

variable (K : Type u) [Field K] [Algebra k K]

/-- The geometric character group with scalars extended from the integers to the rationals. -/
abbrev RationalCharacters (A : HopfAlgebraCategory k) :=
  ℚ ⊗[ℤ] Additive (GeometricCharacters K A)

/-- For a torus split over `K`, this dual of the rational character space is
the rationalization of its cocharacter lattice. -/
abbrev RationalCocharacters (A : HopfAlgebraCategory k) :=
  RationalCharacters K A →ₗ[ℚ] ℚ

/-- Fixed cocharacters for the dual Galois action, tested on the geometric characters
that span the rational character space. -/
def rationalCocharacterInvariants (A : HopfAlgebraCategory k) :
    Submodule ℚ (RationalCocharacters K A) where
  carrier := {v | ∀ (σ : Gal(K/k)) (χ ψ : GeometricCharacters K A),
    (Descent.SemilinearAction.scalarExtension (K := K) A).act σ χ.val = ψ.val →
      v (1 ⊗ₜ[ℤ] Additive.ofMul ψ) = v (1 ⊗ₜ[ℤ] Additive.ofMul χ)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw σ χ ψ h
    change v _ + w _ = v _ + w _
    rw [hv σ χ ψ h, hw σ χ ψ h]
  smul_mem' := by
    intro a v hv σ χ ψ h
    change a • v _ = a • v _
    rw [hv σ χ ψ h]

/-- The rational cocharacter map is dual to pullback of geometric characters. -/
def rationalCocharacterMap {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    RationalCocharacters K B →ₗ[ℚ] RationalCocharacters K A where
  toFun v := v.comp (((pullbackCharacter K f).toAdditive.toIntLinearMap).baseChange ℚ)
  map_add' v w := by ext x; rfl
  map_smul' a v := by ext x; rfl

/-- For every connected reductive group the adjoint quotient is an affine connected
reductive group, with the full centre as kernel. -/
def AdjointQuotientExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsAdjointQuotient Z q ∧ IsReductive Q

/-- The scheme inverse image of a torus maximal over the algebraic closure is
again a torus maximal over the algebraic closure. -/
def MaximalTorusPreimage : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), IsReductive G → IsAdjointQuotient Z q →
      ∀ (T' : ClosedSubgroup Q.val), IsTorus T'.group → IsGeometricallyMaximal T' →
        ∃ (T : ClosedSubgroup G.val) (p : T.group ⟶ T'.group),
          IsMaximalTorusPreimage q T' T p

/-- The actual map on rational cocharacters is surjective, also on Galois invariants. -/
def RationalCocharacterSurjectivity : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), IsReductive G → IsAdjointQuotient Z q →
      ∀ (T' : ClosedSubgroup Q.val), IsTorus T'.group → IsGeometricallyMaximal T' →
        ∀ (T : ClosedSubgroup G.val) (p : T.group ⟶ T'.group), IsMaximalTorusPreimage q T' T p →
          let A := coordinateHopf (closedSubgroupAlgebraicGroup T)
          let B := coordinateHopf (closedSubgroupAlgebraicGroup T')
          let K := SeparableClosure k
          let m := rationalCocharacterMap K (coordinateHopfMap
            (G := closedSubgroupAlgebraicGroup T) (H := closedSubgroupAlgebraicGroup T') p)
          Function.Surjective m ∧
            (rationalCocharacterInvariants K A).map m = rationalCocharacterInvariants K B

/-- Each cocharacter over the ground field has a positive multiple that lifts
through the adjoint quotient. -/
def AdjointCocharacterLift : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), IsReductive G → IsAdjointQuotient Z q →
      ∀ cochar : Cocharacter Q.val,
        ∃ (n : ℕ), 0 < n ∧ ∃ lift : Cocharacter G.val, lift ≫ q = powerOnGm k n ≫ cochar

/-- For a semisimple group the same map is an isomorphism on geometric rational
cocharacters, and its restriction is an isomorphism on the invariant subspaces. -/
def SemisimpleRationalCocharacterIso : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), IsReductive G → IsSemisimple G → IsAdjointQuotient Z q →
      ∀ (T' : ClosedSubgroup Q.val), IsTorus T'.group → IsGeometricallyMaximal T' →
        ∀ (T : ClosedSubgroup G.val) (p : T.group ⟶ T'.group), IsMaximalTorusPreimage q T' T p →
          let A := coordinateHopf (closedSubgroupAlgebraicGroup T)
          let B := coordinateHopf (closedSubgroupAlgebraicGroup T')
          let K := SeparableClosure k
          let m := rationalCocharacterMap K (coordinateHopfMap
            (G := closedSubgroupAlgebraicGroup T) (H := closedSubgroupAlgebraicGroup T') p)
          Function.Bijective m ∧
            (rationalCocharacterInvariants K A).map m = rationalCocharacterInvariants K B

end

end LinearAlgebraicGroups.Specs.AdjointCocharacters
