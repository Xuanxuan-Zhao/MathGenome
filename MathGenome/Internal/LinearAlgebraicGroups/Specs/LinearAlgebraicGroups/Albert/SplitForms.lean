import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.RemoveParameters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.PeirceFrames
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Separable

/-! The isomorphism torsor and separable splitting in NA13-C04.04. -/

namespace LinearAlgebraicGroups.Albert.SplitFormsSpecification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SplitSpecification
open scoped TensorProduct CategoryTheory.MonObj

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Isomorphisms on a test algebra preserve the unit and quadratic operator. -/
def IsomorphismPoints (K : ParaQuadratic R N) (J : ParaQuadratic R M)
    (S : Type u) [CommRing S] [Algebra R S] :=
  {e : S ⊗[R] N ≃ₗ[S] S ⊗[R] M //
    e (1 ⊗ₜ[R] K.unit) = 1 ⊗ₜ[R] J.unit ∧
      ∀ x y, e (K.op S x y) = J.op S (e x) (e y)}

noncomputable abbrev TestScheme (S : CommAlgCat.{u} R) :=
  (algSpec (CommRingCat.of R)).obj (op S)

abbrev Points (X : Over (Spec (CommRingCat.of R))) (S : CommAlgCat.{u} R) :=
  TestScheme S ⟶ X

/-- Representation of isomorphisms with their scalar-extension maps. -/
structure IsomorphismRepresentation (K : ParaQuadratic R N) (J : ParaQuadratic R M)
    (X : Over (Spec (CommRingCat.of R))) where
  points (S : CommAlgCat.{u} R) : Points X S ≃ IsomorphismPoints K J S
  natural {S T : CommAlgCat.{u} R} (f : S ⟶ T) (p : Points X S) (x : S ⊗[R] N) :
    (points T ((algSpec (CommRingCat.of R)).map f.op ≫ p)).val
        (f.hom.toLinearMap.rTensor N x) =
      f.hom.toLinearMap.rTensor M ((points S p).val x)

/-- An affine finite-type scheme representing the relative isomorphism functor. -/
def AffineRepresentability : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (K : ParaQuadratic R N) (J : ParaQuadratic R M)
    {ι₀ : Type u} [Fintype ι₀] (_b : Module.Basis ι₀ R N) (_c : Module.Basis ι₀ R M),
    ∃ X : Over (Spec (CommRingCat.of R)),
      IsAffine X.left ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
        Nonempty (IsomorphismRepresentation K J X)

/-- The explicit isomorphism from a reduced model with split octonion input
to the untwisted split model, over its original base. -/
def SplitReducedModel : Prop :=
  ∀ {R : Type u} [CommRing R]
    (h : Composition.Specification.OctonionNormConditions (LowerRankSpecification.zornNorm R))
    (weights : Fin 3 → Rˣ) (J : ParaQuadratic R (SplitRank.octonion.Model R)),
    IsReducedModel h weights J →
    ∃ K : ParaQuadratic R (SplitRank.octonion.Model R),
      IsSplitModel K .octonion ∧ J.IsIso K (RemoveParametersSpecification.removeZornWeights weights)

/-- Weight removal for any split octonion algebra, using its Zorn coordinates. -/
def SplitReducedModelOfSplitOctonion : Prop :=
  ∀ {R : Type u} [CommRing R] {A : Type v} [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : Composition.Specification.OctonionNormConditions n) (weights : Fin 3 → Rˣ)
    (J : ParaQuadratic R (HermitianSpecification.Coordinates R A)),
    Composition.Specification.splitOctonion n → IsReducedModel h weights J →
    ∃ (K : ParaQuadratic R (SplitRank.octonion.Model R))
      (f : Composition.PeirceSpecification.ZornIsomorphism n),
      IsSplitModel K .octonion ∧
      let coordinates := (LinearEquiv.refl R (Fin 3 → R)).prodCongr
        (LinearEquiv.piCongrRight fun _ : Fin 3 => f.toLinearEquiv)
      J.IsIso K (coordinates.symm.trans (RemoveParametersSpecification.removeZornWeights weights))

/-- Right action diagrams for a group object on the isomorphism scheme. -/
def IsRightAction {k : Type} [Field k] (G : SpinSpecification.GroupScheme k)
    {X : Over (Spec (CommRingCat.of k))} (act : X ⨯ G.X ⟶ X) : Prop :=
  prod.lift (𝟙 X) (1 : X ⟶ G.X) ≫ act = 𝟙 X ∧
    let Y := (X ⨯ G.X) ⨯ G.X
    let q : Y ⟶ X ⨯ G.X := prod.fst
    prod.lift (q ≫ act) (prod.snd : Y ⟶ G.X) ≫ act =
      prod.lift (q ≫ prod.fst) ((q ≫ prod.snd) * prod.snd) ≫ act

/-- The orbit of a point induces the indicated isomorphism after base change. -/
def TrivializesAt {k : Type} [Field k] {G X U : Over (Spec (CommRingCat.of k))}
    (act : X ⨯ G ⟶ X) (p : U ⟶ X) : Prop :=
  let change := Over.pullback U.hom
  let adj := Over.mapPullbackAdj U.hom
  let cover : (Over.map U.hom).obj (change.obj G) ⟶ U :=
    Over.homMk (change.obj G).hom rfl
  ∃ e : change.obj G ≅ change.obj X,
    (adj.homEquiv _ _).symm e.hom =
      prod.lift (cover ≫ p) (adj.counit.app G) ≫ act

/-- The isomorphism torsor from the split Albert algebra and its separable point. -/
def SeparableSplitting : Prop :=
  ∀ {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M), IsAlbert J →
    ∃ (K : ParaQuadratic k (SplitRank.octonion.Model k))
      (G : SpinSpecification.GroupScheme k) (X : Over (Spec (CommRingCat.of k)))
      (I : IsomorphismRepresentation K J X),
      IsSplitModel K .octonion ∧ IsAffine G.X.left ∧ Smooth G.X.hom ∧
      IsAffine X.left ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      Flat X.hom ∧ Surjective X.hom ∧ Smooth X.hom ∧
      ∃ a : ∀ S : CommAlgCat k, Points G.X S →*
          (S ⊗[k] SplitRank.octonion.Model k ≃ₗ[S] S ⊗[k] SplitRank.octonion.Model k),
        (∀ S, Function.Injective (a S) ∧ Set.range (a S) =
          {g | g (1 ⊗ₜ[k] K.unit) = 1 ⊗ₜ[k] K.unit ∧
              ∀ x y, g (K.op S x y) = K.op S (g x) (g y)}) ∧
        (∀ {S T : CommAlgCat k} (f : S ⟶ T) (g : Points G.X S) (x),
          let m := f.hom.toLinearMap.rTensor (SplitRank.octonion.Model k)
          m (a S g x) = a T ((algSpec (CommRingCat.of k)).map f.op ≫ g) (m x)) ∧
        (∃ act : X ⨯ G.X ⟶ X,
          IsRightAction G act ∧
          (∀ (S : CommAlgCat k) (p : Points X S) (g : Points G.X S) (x),
            (I.points S (prod.lift p g ≫ act)).val x = (I.points S p).val (a S g x)) ∧
          IsIso (prod.lift (prod.fst : X ⨯ G.X ⟶ X) act : X ⨯ G.X ⟶ X ⨯ X) ∧
          ∀ (S : CommAlgCat k) (p : Points X S),
            TrivializesAt act p ∧
            (K.baseChange S).IsIso (J.baseChange S) (I.points S p).val) ∧
        (∃ (S : Type) (_ : CommRing S) (_ : Algebra k S),
          Module.FaithfullyFlat k S ∧ Nonempty (Points X (CommAlgCat.of k S))) ∧
        ∃ (L : Type) (_ : Field L) (_ : Algebra k L),
          FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
            Nonempty (Points X (CommAlgCat.of k L)) ∧ IsSplitModel (J.baseChange L) .octonion

end LinearAlgebraicGroups.Albert.SplitFormsSpecification
