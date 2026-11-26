import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralSmoothness

/-! Representability and descent for the quadratic automorphism group of an Albert algebra. -/

namespace LinearAlgebraicGroups.Albert.AutomorphismDescentSpecification

open AlgebraicGeometry CategoryTheory Opposite
open SplitSpecification IntegralSmoothnessSpecification
open ShortDirectionSpecification (IntegralPresentation)
open SpinSpecification (GroupScheme SchemePoints)
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

/-- Base change of groups in schemes over a commutative base ring. -/
abbrev groupChange (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    GroupScheme R ⥤ GroupScheme S :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp

/-- Triviality of the scheme centre, tested also on nonreduced schemes. -/
def IsCenterless {R : Type} [CommRing R] (G : GroupScheme R) : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) (z : X ⟶ G.X),
    (∀ (Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X) (g : Y ⟶ G.X),
      (f ≫ z) * g = g * (f ≫ z)) → z = 1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- Representation of the actual automorphisms of the base point and operator law.
The action is natural on all commutative scalar algebras. -/
def RepresentsAutomorphisms (J : ParaQuadratic R M) (G : GroupScheme R) : Prop :=
  ∃ a : ∀ S : CommAlgCat R,
    SchemePoints G S →* (S ⊗[R] M ≃ₗ[S] S ⊗[R] M),
    (∀ S, Function.Injective (a S) ∧ Set.range (a S) =
      {g | g (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit ∧
        ∀ x y, g (J.op S x y) = J.op S (g x) (g y)}) ∧
    ∀ {S T : CommAlgCat R} (f : S ⟶ T) (p : SchemePoints G S) (x : S ⊗[R] M),
      let m := f.hom.toLinearMap.rTensor M
      m (a S p x) = a T ((algSpec (CommRingCat.of R)).map f.op ≫ p) (m x)

/-- The automorphism functor is represented by an affine finitely presented group
scheme, and its representing action extends to every scalar algebra. -/
def RepresentationType : Prop :=
  ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsAlbert J →
    ∃ G : GroupScheme R, IsAffine G.X.left ∧ LocallyOfFinitePresentation G.X.hom ∧
      RepresentsAutomorphisms J G ∧
      ∀ (S : Type) [CommRing S] [Algebra R S],
        RepresentsAutomorphisms (J.baseChange S) ((groupChange R S).obj G)

/-- Comparison for any affine group representing the automorphisms of an Albert form.
The integral model and the geometric and centre hypotheses concern the same group. -/
def DescentType : Prop :=
  ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsAlbert J →
    ∀ (G : GroupScheme R), IsAffine G.X.left → RepresentsAutomorphisms J G →
    ∀ {P : IntegralPresentation} (L : SplitGroup P),
      (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
        Nonempty (((groupChange R K).obj G) ≅ geometricFiber L K)) ∧
      (IsSplitModel J .octonion → Nonempty (G ≅ (groupChange ℤ R).obj L.group)) ∧
      ((Smooth L.group.X.hom → Smooth G.X.hom) ∧
        (GeometricallyConnected L.group.X.hom → GeometricallyConnected G.X.hom)) ∧
      ((∀ (S : Type) [CommRing S], IsCenterless ((groupChange ℤ S).obj L.group)) →
        IsCenterless G)

end
end LinearAlgebraicGroups.Albert.AutomorphismDescentSpecification
