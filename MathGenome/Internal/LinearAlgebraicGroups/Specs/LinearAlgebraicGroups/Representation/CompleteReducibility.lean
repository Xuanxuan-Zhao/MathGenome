import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.BaseChange
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry CategoryTheory Opposite WithConv

universe u

namespace LinearAlgebraicGroups.Specs.CompleteReducibility

/-- The scheme representation associated to the coaction in a finite basis is a
closed immersion into a group scheme representing the general linear functor. -/
def IsFaithful {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (G : AffineAlgebraicGroup k) {A : HopfAlgebraCategory k} (ρ : RightComodule k A V)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) k V)
    (L : AffineAlgebraicGroup k)
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left ∧
    LinearAlgebraicGroups.RationalRepresentations.coefficients A b ρ =
      LinearAlgebraicGroups.RationalRepresentations.universalMatrix A
        (⟨G.val, G.property.1⟩ : AffineGroupCategory k) L.val e l f

/-- The point comparison furnished by a coordinate Hopf presentation. -/
noncomputable def pointPresentation {k : Type u} [Field k] {A : HopfAlgebraCategory k}
    {G : GroupScheme k} (a : specGroup A ≅ G) :
    convolutionPoints A ≅ (groupPointsFunctor k).obj G :=
  (NatIso.ofComponents (fun R : TestAlgebra k =>
    (Spec.mapMulEquiv (R := k) (S := A) (T := R)).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro g
      apply Over.OverMorphism.ext
      exact Spec.map_comp (CommRingCat.ofHom g.ofConv.toRingHom)
        (CommRingCat.ofHom f.hom.toRingHom))) ≪≫ (groupPointsFunctor k).mapIso a

/-- Complete reducibility for connected affine algebraic groups in characteristic zero
(LAG E07), in the right-comodule model of rational representations. -/
def CharacteristicZeroCompleteReducibility : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] (A : HopfAlgebraCategory k) (a : specGroup A ≅ G.val),
    let e := pointPresentation a
    let allSemisimple := ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (ρ : RightComodule k A V), LinearAlgebraicGroups.RationalRepresentations.IsSemisimple A ρ
    let hasFaithfulSemisimple := ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V)
      (_ : FiniteDimensional k V) (ρ : RightComodule k A V),
      IsFaithful G ρ e ∧ LinearAlgebraicGroups.RationalRepresentations.IsSemisimple A ρ
    (GeometricRadicals.IsReductive G ↔ allSemisimple) ∧
      (allSemisimple ↔ hasFaithfulSemisimple)

end LinearAlgebraicGroups.Specs.CompleteReducibility
