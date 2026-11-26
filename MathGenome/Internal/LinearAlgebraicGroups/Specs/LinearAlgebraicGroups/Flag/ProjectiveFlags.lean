import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ProjectiveFlags

open BorelProper (IsParabolic)
open ProjectiveSpaces (LineRepresentation projectiveSpace)

/-- A parabolic quotient over any field is represented by a smooth projective
scheme. Its closed projective orbit embedding uses a representation line with
scheme stabilizer equal to the given parabolic. -/
def SmoothProjectiveQuotient : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    Nonempty (QuotientEmbedding.Presentation P) ∧
    ∀ Q : QuotientEmbedding.Presentation P,
      Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
        (a : ModObj G.val.X (projectiveSpace k V))
        (x : 𝟙_ (SchemeOver k) ⟶ projectiveSpace k V)
        (b : ModObj G.val.X Q.scheme) (j : Q.scheme ⟶ projectiveSpace k V),
        IsClosedImmersion j.left ∧
        Q.projection ≫ j = SmoothOrbit.orbitMap a x ∧
        μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ b.smul ∧
        b.smul ≫ j = (𝟙 G.val.X ⊗ₘ j) ≫ a.smul ∧
        RepresentsSubgroup P (fun _ g ↦ Stabilizes a.smul x g) ∧
        ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (v : Module.Basis I k V)
          (M : GroupScheme k)
          (E : (groupPointsFunctor k).obj M ≅ StandardGroups.generalLinearPoints k I)
          (f : G.val ⟶ M) (ρ : LineRepresentation k V),
          ∀ (R : TestAlgebra k) (g : Points G.val.X R)
            (p : Points (projectiveSpace k V) R),
            ((ρ.points _ (lift g p ≫ a.smul)).line R (𝟙 _)).submodule =
              ((ρ.points _ p).line R (𝟙 _)).submodule.map
                (PluckerEmbedding.matrixTransport v R (E.hom.app R (g ≫ f.hom.hom))).toLinearMap

end LinearAlgebraicGroups.Specs.ProjectiveFlags
