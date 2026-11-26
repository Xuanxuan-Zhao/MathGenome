import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SmoothOrbit

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.QuotientEmbedding

noncomputable section

/-- A quasi-projective scheme over a field admits a locally closed immersion into
a finite-dimensional projective space over that field. -/
def IsQuasiProjective {k : Type u} [Field k] (X : SchemeOver k) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
    (j : X ⟶ ProjectiveSpaces.projectiveSpace k V), IsImmersion j.left

/-- A representing scheme for the right-coset sheaf, with an fppf morphism
corresponding to the quotient projection. -/
structure Presentation {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G) where
  scheme : SchemeOver k
  quasiProjective : IsQuasiProjective scheme
  projection : G.X ⟶ scheme
  flat : Flat projection.left
  surjective : Surjective projection.left
  finitePresentation : LocallyOfFinitePresentation projection.left
  quotientIso : rightQuotientSheaf H ≅ schemeFppfSheaf scheme
  quotientProjection : rightQuotientProjection H ≫ quotientIso.hom =
    (fppfOver k).uliftYoneda.map projection

/-- For smooth groups the representing scheme is the open orbit in the schematic
closure of the translates of a rational line whose scheme stabilizer is H. -/
def SmoothQuotientEmbedding : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    Smooth G.val.X.hom →
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
      (a : ModObj G.val.X (ProjectiveSpaces.projectiveSpace k V))
      (x : 𝟙_ (SchemeOver k) ⟶ ProjectiveSpaces.projectiveSpace k V)
      (P : SmoothOrbit.Presentation a x) (Q : Presentation H),
      RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) ∧
      (∃ e : Q.scheme ≅ P.orbit, Q.projection ≫ e.hom = P.projection) ∧
      ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (b : Module.Basis I k V)
        (M : GroupScheme k)
        (E : (groupPointsFunctor k).obj M ≅ StandardGroups.generalLinearPoints k I)
        (f : G.val ⟶ M) (ρ : ProjectiveSpaces.LineRepresentation k V),
        ∀ (R : TestAlgebra k) (g : Points G.val.X R)
          (p : Points (ProjectiveSpaces.projectiveSpace k V) R),
          ((ρ.points _ (lift g p ≫ a.smul)).line R (𝟙 _)).submodule =
            ((ρ.points _ p).line R (𝟙 _)).submodule.map
              (PluckerEmbedding.matrixTransport b R (E.hom.app R (g ≫ f.hom.hom))).toLinearMap

/-- The right fppf quotient of any finite-type affine group by a closed subgroup
scheme is represented by a quasi-projective scheme. -/
def RightQuotientRepresentable : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    Nonempty (Presentation H)

end

end LinearAlgebraicGroups.Specs.QuotientEmbedding
