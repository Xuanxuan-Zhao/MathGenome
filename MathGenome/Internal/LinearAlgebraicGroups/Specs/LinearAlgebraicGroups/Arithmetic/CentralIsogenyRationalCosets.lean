import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped RestrictedProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

universe u v

namespace LinearAlgebraicGroups.Specs.CentralIsogenyRationalCosets

open Arithmetic Arithmetic.AdelicGroups
open IntegralModels (MatrixRealization RationalPoints)
open GeometricRadicals (IsSemisimple)
open CentralIsogenies (IsCentralIsogeny)

/-- The map of groups of points induced by a homomorphism of group schemes. -/
def pointMap {K : Type u} [Field K] {G Q : GroupScheme K}
    (q : G ⟶ Q) (R : Type u) [CommRing R] [Algebra K R] :
    ((groupPointsFunctor K).obj G).obj (CommAlgCat.of K R) →*
      ((groupPointsFunctor K).obj Q).obj (CommAlgCat.of K R) :=
  (((groupPointsFunctor K).map q).app (CommAlgCat.of K R)).hom

/-- The finite-coset conclusion for the given local points and full adelic topology. -/
def FiniteCosetsFor {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {G Q : AffineAlgebraicGroup K} (q : G.val ⟶ Q.val) (j : MatrixRealization Q) : Prop :=
  ∀ (C : Set (Adeles D j ∅)), IsCompact C →
    ∃ F : Finset (RationalPoints Q),
      ∀ d : RationalPoints Q,
        (∃ c ∈ C, ∀ w : Outside D ∅,
          ∃ x : ((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K (D.Completion w.1)),
            c w = (show LocalPoints D j w.1 from pointMap q (D.Completion w.1) x) *
              localPoint D j w.1 d) →
        ∃ r ∈ F, ∃ γ : RationalPoints G, d = pointMap q K γ * r

/-- Rational points lying in the local lift classes of a compact set of full adeles
belong to finitely many cosets of the rational image of the central isogeny. -/
def FiniteRationalCosets : Prop :=
  ∀ {K : Type u} [Field K] [hK : NumberField K] (G Q : AffineAlgebraicGroup K),
    IsSemisimple G → IsSemisimple Q →
    ∀ (q : G.val ⟶ Q.val), IsCentralIsogeny q →
      ∀ (j : MatrixRealization Q), FiniteCosetsFor (GlobalFieldData.number.{u, v} hK) q j

end LinearAlgebraicGroups.Specs.CentralIsogenyRationalCosets
