import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FlagIncidence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.PluckerEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Projection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.FlagSchemes
noncomputable section

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- A (d)-plane on an affine test scheme is encoded by the kernel of a locally free
quotient of corank (d). In finite dimension the complementary rank is (d). -/
abbrev Plane (d : ℕ) (R : TestAlgebra k) :=
  GrassmannianCharts.Plane k V d R

abbrev planeFunctor (d : ℕ) : TestAlgebra k ⥤ Type u :=
  GrassmannianCharts.planeFunctor k V d

/-- The entries of a flag are submodules, ordered by inclusion. -/
structure Flag {m : ℕ} (ranks : Fin m → ℕ) (R : TestAlgebra k) where
  plane : ∀ i, Plane k V (ranks i) R
  nested : ∀ ⦃i j : Fin m⦄, i ≤ j → (plane i).toSubmodule ≤ (plane j).toSubmodule

@[ext] theorem Flag.ext {m : ℕ} {ranks : Fin m → ℕ} {R : TestAlgebra k}
    {x y : Flag k V ranks R} (h : ∀ i, x.plane i = y.plane i) : x = y := by
  cases x
  cases y
  cases funext h
  rfl

def BaseChangePreservesInclusion : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    {R S : TestAlgebra k} (a : R ⟶ S) {d e : ℕ}
    (L : Plane k V d R) (M : Plane k V e R),
    L.toSubmodule ≤ M.toSubmodule →
      (Module.Grassmannian.map a.hom L).toSubmodule ≤
        (Module.Grassmannian.map a.hom M).toSubmodule

def FlagFunctorType :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    {m : ℕ}, (Fin m → ℕ) → TestAlgebra k ⥤ Type u

/-- The map on flags applies the canonical Grassmannian base change to each entry. -/
def FlagFunctorMaps (F : FlagFunctorType.{u}) : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] {m : ℕ}
    (ranks : Fin m → ℕ), ∃ e : ∀ R, (F k V ranks).obj R ≃ Flag k V ranks R,
      ∀ (R S : TestAlgebra k) (a : R ⟶ S) (x : (F k V ranks).obj R) (i : Fin m),
        (e S ((F k V ranks).map a x)).plane i =
          Module.Grassmannian.map a.hom ((e R x).plane i)

def FlagFunctorExists : Prop := ∃ F : FlagFunctorType.{u}, FlagFunctorMaps F

def PlaneSplitAndRank : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (d : ℕ) (_hd : d ≤ Module.finrank k V) (R : TestAlgebra k) (L : Plane k V d R),
    (∃ C : Submodule R (R ⊗[k] V), IsCompl L.toSubmodule C) ∧
      Module.Finite R L.toSubmodule ∧ Module.Projective R L.toSubmodule ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk L.toSubmodule p = d

def PlaneEndpointSubmodules : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (R : TestAlgebra k),
    (∀ L : Plane k V 0 R, L.toSubmodule = ⊥) ∧
      (∀ L : Plane k V (Module.finrank k V) R, L.toSubmodule = ⊤)

def PlaneEndpointsUnique : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (R : TestAlgebra k),
    Nonempty (Unique (Plane k V 0 R)) ∧ Nonempty (Unique (Plane k V (Module.finrank k V) R))

def EmptyFlagUnique : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] (R : TestAlgebra k)
    (ranks : Fin 0 → ℕ), Nonempty (Unique (Flag k V ranks R))

abbrev pointScheme (k : Type u) [Field k] : SchemeOver k :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

def PlaneEndpointsRepresentedByPoint : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V],
    Nonempty (pointsFunctor (pointScheme k) ≅ planeFunctor k V 0) ∧
    Nonempty (pointsFunctor (pointScheme k) ≅ planeFunctor k V (Module.finrank k V))

def EmptyFlagRepresentedByPoint : Prop :=
  ∃ F : FlagFunctorType.{u}, FlagFunctorMaps F ∧
    ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] (ranks : Fin 0 → ℕ),
      Nonempty (pointsFunctor (pointScheme k) ≅ F k V ranks)

section GraphCharts

variable (R : Type u) [CommRing R] (I J : Type u) [Fintype I] [Fintype J]

/-- A pivot chart on the decomposition (R^{I}\oplus R^{J}) is the locus
where projection to the first factor trivializes the submodule. -/
abbrev GraphChart :=
  { L : Module.Grassmannian R ((I → R) × (J → R)) (Fintype.card J) //
    Function.Bijective (Prod.fst ∘ L.toSubmodule.subtype) }

def GraphChartCoordinates : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Type u) [Fintype I] [Fintype J],
    ∃ e : ((I → R) →ₗ[R] (J → R)) ≃ GraphChart R I J,
      ∀ f, (e f).val.toSubmodule = f.graph

/-- The affine parameter scheme of a pivot chart, with one variable per free entry. -/
abbrev graphChartScheme (k : Type u) [Field k] (I J : Type u) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial (J × I) k)))

def GraphChartRepresentedOnAffines : Prop :=
  ∀ (k : Type u) [Field k] (I J : Type u) [Fintype I] [Fintype J] [DecidableEq I]
    (R : TestAlgebra k),
    ∃ e : Points (graphChartScheme k I J) R ≃ GraphChart R I J,
      ∀ f : MvPolynomial (J × I) k →ₐ[k] R,
        (e ((testSpec k).map (CommAlgCat.ofHom f).op)).val.toSubmodule =
          (Matrix.toLin' (Matrix.of fun j i ↦ f (MvPolynomial.X (j, i)))).graph

end GraphCharts

section Coordinate

variable (R : Type u) [CommRing R]

/-- The coordinate summand spanned by the standard vectors in a given set. -/
def coordinateSubmodule {ι : Type*} (selected : Set ι) : Submodule R (ι → R) :=
  LinearMap.ker (LinearMap.funLeft R R (Subtype.val : {i : ι // i ∉ selected} → ι))

def CoordinateFlagStabilizer : Prop :=
  ∀ (R : Type u) (ι : Type v) [CommRing R] [Fintype ι] [DecidableEq ι]
    {m : ℕ} (cuts : Fin m → Set ι) (g : Matrix.GeneralLinearGroup ι R),
    (∀ a, (coordinateSubmodule R (cuts a)).map (Matrix.mulVecLin (g : Matrix ι ι R)) =
        coordinateSubmodule R (cuts a)) ↔
      ∀ a (i j : ι), j ∈ cuts a → i ∉ cuts a → g i j = 0

def CoordinateFullFlagStabilizer : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R),
    (∀ a : Fin n,
      (coordinateSubmodule R {i : Fin n | i < a}).map
          (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) R)) =
        coordinateSubmodule R {i : Fin n | i < a}) ↔
    ∀ i j : Fin n, j < i → g i j = 0

section ClosedLocus

open StandardGroups

variable (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] {m : ℕ} (cuts : Fin m → Set ι)

/-- The matrix entries crossing a cut from an earlier column to a later row
generate the ideal of the block upper triangular locus. -/
def coordinateFlagIdeal : Ideal (GLCoordinates k ι) :=
  Ideal.span {x | ∃ (a : Fin m) (i j : ι),
    j ∈ cuts a ∧ i ∉ cuts a ∧ x = universalMatrix k ι i j}

abbrev coordinateFlagLocus : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (GLCoordinates k ι ⧸ coordinateFlagIdeal k ι cuts)))

abbrev matrixScheme : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (GLCoordinates k ι)))

def coordinateFlagInclusion : coordinateFlagLocus k ι cuts ⟶ matrixScheme k ι :=
  (testSpec k).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k (coordinateFlagIdeal k ι cuts))).op

def CoordinateFlagClosedLocus : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] {m : ℕ} (cuts : Fin m → Set ι),
    IsClosedImmersion (coordinateFlagInclusion k ι cuts).left ∧
    ∀ (R : TestAlgebra k) (f : GLCoordinates k ι →ₐ[k] R),
      let p : Points (matrixScheme k ι) R := (testSpec k).map (CommAlgCat.ofHom f).op
      (∃ q : Points (coordinateFlagLocus k ι cuts) R,
        q ≫ coordinateFlagInclusion k ι cuts = p) ↔
      ∀ a (i j : ι), j ∈ cuts a → i ∉ cuts a → f (universalMatrix k ι i j) = 0

def CoordinateFlagSchemeStabilizer : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] {m : ℕ} (cuts : Fin m → Set ι)
    (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup ι R),
    ∃! f : GLCoordinates k ι →ₐ[k] R,
      (∀ i j, f (universalMatrix k ι i j) = g i j) ∧
      ((∃ q : Points (coordinateFlagLocus k ι cuts) R,
        q ≫ coordinateFlagInclusion k ι cuts = (testSpec k).map (CommAlgCat.ofHom f).op) ↔
      ∀ a, (coordinateSubmodule R (cuts a)).map (Matrix.mulVecLin (g : Matrix ι ι R)) =
        coordinateSubmodule R (cuts a))

end ClosedLocus

end Coordinate

section Geometry

set_option maxHeartbeats 800000

open FlagIncidence (Action GrassmannianProduct Presentation)
open PluckerEmbedding (PluckerMorphism SchemeAction Wedge exteriorTransport matrixTransport)
open ProjectiveSpaces (LineRepresentation projectiveProduct projectiveSpace tensorSpace)

variable {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype ι] [DecidableEq ι] {m : ℕ} (b : Module.Basis ι k V) (ranks : Fin m → ℕ)

/-- The exterior powers used for the Plücker embeddings of the entries of the flag. -/
abbrev flagWedges (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    {m : ℕ} (ranks : Fin m → ℕ) (i : ULift.{u} (Fin m)) : Type u :=
  Wedge k (ranks i.down) V

abbrev flagRepresentation := tensorSpace (k := k) (flagWedges k V ranks)

variable (P : ∀ i : Fin m, PluckerMorphism b (ranks i))

/-- Take the Plücker line of each entry. -/
def productPlucker :
    GrassmannianProduct ranks b (fun i ↦ (P i).charts) ⟶
      projectiveProduct (k := k) (flagWedges k V ranks) :=
  Pi.lift fun i ↦ Pi.π _ i.down ≫ (P i.down).morphism

variable (D : Presentation ranks b (fun i ↦ (P i).charts) (fun i ↦ (P i).families))

/-- The incidence immersion followed by the Plücker and Segre maps. -/
def flagEmbedding
    (σ : projectiveProduct (k := k) (flagWedges k V ranks) ⟶
      projectiveSpace k (flagRepresentation (k := k) (V := V) ranks)) :
    D.scheme ⟶ projectiveSpace k (flagRepresentation (k := k) (V := V) ranks) :=
  D.inclusion ≫ productPlucker b ranks P ≫ σ

/-- On a test algebra the representation is the tensor product of the exterior actions. -/
def tensorExteriorTransport (R : TestAlgebra k)
    (c : (⨂[R] i, R ⊗[k] flagWedges k V ranks i) ≃ₗ[R]
      R ⊗[k] flagRepresentation (k := k) (V := V) ranks)
    (g : Matrix.GeneralLinearGroup ι R) :
    Module.End R (R ⊗[k] flagRepresentation (k := k) (V := V) ranks) :=
  let f (i : ULift.{u} (Fin m)) : Module.End R (R ⊗[k] flagWedges k V ranks i) :=
    exteriorTransport ((P i.down).exteriorLines.compare R) (matrixTransport b R g)
  c.toLinearMap.comp ((PiTensorProduct.map f).comp c.symm.toLinearMap)

variable (G : GroupScheme k)
  (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k ι)
  (A : Action ranks b (fun i ↦ (P i).charts) D.inclusion G E)

/-- The projective realization uses the same incidence presentation and linear action. -/
structure ProjectivePresentation where
  lines : LineRepresentation k (flagRepresentation (k := k) (V := V) ranks)
  segre : projectiveProduct (k := k) (flagWedges k V ranks) ⟶
    projectiveSpace k (flagRepresentation (k := k) (V := V) ranks)
  tensorCompare : ∀ R : TestAlgebra k,
    (⨂[R] i, R ⊗[k] flagWedges k V ranks i) ≃ₗ[R]
      R ⊗[k] flagRepresentation (k := k) (V := V) ranks
  tensorCompare_pure : ∀ (R : TestAlgebra k) (v : ∀ i, flagWedges k V ranks i),
    tensorCompare R (PiTensorProduct.tprod R (fun i ↦ (1 : R) ⊗ₜ[k] v i)) =
      (1 : R) ⊗ₜ[k] PiTensorProduct.tprod k v
  segre_formula : ∀ (S : SchemeOver k)
    (p : S ⟶ projectiveProduct (k := k) (flagWedges k V ranks))
    (R : TestAlgebra k) (a : Points S R),
    let L (i : ULift.{u} (Fin m)) : Submodule R (R ⊗[k] flagWedges k V ranks i) :=
      (((P i.down).lines.points S (p ≫ Pi.π _ i)).line R a).submodule
    ((lines.points S (p ≫ segre)).line R a).submodule =
      (LinearMap.range (PiTensorProduct.mapIncl L)).map (tensorCompare R).toLinearMap
  segre_closed : IsClosedImmersion segre.left
  embedding_closed : IsClosedImmersion (flagEmbedding b ranks P D segre).left
  proper : IsProper D.scheme.hom
  linearRepresentation : ∀ R : TestAlgebra k,
    ((groupPointsFunctor k).obj G).obj R →* Module.End R (R ⊗[k] flagRepresentation (k := k) (V := V) ranks)
  linear_formula : ∀ (R : TestAlgebra k) (g : Points G.X R),
    linearRepresentation R g = tensorExteriorTransport b ranks P R (tensorCompare R) (E.hom.app R g)
  linear_baseChange : ∀ {R T : TestAlgebra k} (a : R ⟶ T) (g : Points G.X R),
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T
      (flagRepresentation (k := k) (V := V) ranks)
    (linearRepresentation T (mapPoints a g)).comp c.toLinearMap =
      c.toLinearMap.comp ((linearRepresentation R g).baseChange (↥T))
  action : SchemeAction G (projectiveSpace k (flagRepresentation (k := k) (V := V) ranks))
  action_on_points : ∀ (R : TestAlgebra k) (g : Points G.X R)
    (p : Points (projectiveSpace k (flagRepresentation (k := k) (V := V) ranks)) R),
    ((lines.points _ (CartesianMonoidalCategory.lift g p ≫ action.act)).line R (𝟙 _)).submodule =
      ((lines.points _ p).line R (𝟙 _)).submodule.map
        (tensorExteriorTransport b ranks P R (tensorCompare R) (E.hom.app R g))
  equivariant : ∀ (S : SchemeOver k) (g : S ⟶ G.X) (p : S ⟶ D.scheme),
    (prod.lift g p ≫ A.onFlags) ≫ flagEmbedding b ranks P D segre =
      CartesianMonoidalCategory.lift g (p ≫ flagEmbedding b ranks P D segre) ≫ action.act

/-- The affine restrictions of the incidence presentation agree with the flags of
projective quotients and their canonical base change. -/
def AffineFlagPoints : Prop :=
  ∃ e : ∀ R : TestAlgebra k, Points D.scheme R ≃ Flag k V ranks R,
    (∀ (R : TestAlgebra k) (p : Points D.scheme R) (i : Fin m),
      (e R p).plane i =
        FlagIncidence.productPlanes ranks b (fun i ↦ (P i).charts) (p ≫ D.inclusion) i) ∧
    ∀ (R T : TestAlgebra k) (a : R ⟶ T) (p : Points D.scheme R) (i : Fin m),
      (e T (mapPoints a p)).plane i = Module.Grassmannian.map a.hom ((e R p).plane i)

end Geometry

section CoordinateGeometry

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {m n : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)

abbrev liftedBasis := β.reindex (Equiv.ulift.{u}.symm)

def prefixCuts : Fin m → Set (ULift.{u} (Fin n)) :=
  fun a ↦ {i | i.down.val < ranks a}

/-- The structure map to the base regarded as the spectrum of the test algebra k. -/
def toBasePoint (X : SchemeOver k) : X ⟶ (testSpec k).obj (op (CommAlgCat.of k k)) :=
  Over.homMk X.hom (by
    change X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = X.hom
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl,
      Spec.map_id, Category.comp_id])

variable (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (liftedBasis β) (ranks i))
  (D : FlagIncidence.Presentation ranks (liftedBasis β)
    (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
  (G : GroupScheme k)
  (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
  (A : FlagIncidence.Action ranks (liftedBasis β) (fun i ↦ (P i).charts) D.inclusion G E)

/-- The stabilizer is the scheme fibre of the orbit map at the coordinate flag. -/
structure CoordinateStabilizer where
  point : Points D.scheme (CommAlgCat.of k k)
  point_formula : ∀ i : Fin m,
    (FlagIncidence.productPlanes ranks (liftedBasis β) (fun i ↦ (P i).charts)
      (point ≫ D.inclusion) i).toSubmodule =
        FlagIncidence.prefixSubmodule β (CommAlgCat.of k k) (ranks i)
  matrixIso : matrixScheme k (ULift.{u} (Fin n)) ≅ G.X
  matrix_entries : ∀ (R : TestAlgebra k)
    (f : StandardGroups.GLCoordinates k (ULift.{u} (Fin n)) →ₐ[k] R) (i j : ULift.{u} (Fin n)),
    (E.hom.app R ((testSpec k).map (CommAlgCat.ofHom f).op ≫ matrixIso.hom) :
      Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j =
      f (StandardGroups.universalMatrix k (ULift.{u} (Fin n)) i j)
  stabilizer_pullback :
    IsPullback (coordinateFlagInclusion k (ULift.{u} (Fin n)) (prefixCuts ranks) ≫ matrixIso.hom)
      (toBasePoint _)
      (prod.lift (𝟙 G.X) (toBasePoint G.X ≫ point) ≫ A.onFlags) point
  closed : IsClosedImmersion
    (coordinateFlagInclusion k (ULift.{u} (Fin n)) (prefixCuts ranks) ≫ matrixIso.hom).left
  subgroup : ∃ (H : GroupScheme k) (j : H ⟶ G)
      (e : H.X ≅ coordinateFlagLocus k (ULift.{u} (Fin n)) (prefixCuts ranks)),
    j.hom.hom = e.hom ≫ coordinateFlagInclusion k (ULift.{u} (Fin n)) (prefixCuts ranks) ≫ matrixIso.hom
  equations : ∀ (R : TestAlgebra k) (g : Points G.X R),
    (∃ q : Points (coordinateFlagLocus k (ULift.{u} (Fin n)) (prefixCuts ranks)) R,
      q ≫ (coordinateFlagInclusion k (ULift.{u} (Fin n)) (prefixCuts ranks) ≫ matrixIso.hom) = g) ↔
      ∀ (a : Fin m) (i j : ULift.{u} (Fin n)), j.down.val < ranks a → ranks a ≤ i.down.val →
        (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0
  full_upper_triangular : (∀ a : Fin n, 0 < a.val → ∃ i : Fin m, ranks i = a.val) →
    ∀ (R : TestAlgebra k) (g : Points G.X R),
    (∃ q : Points (coordinateFlagLocus k (ULift.{u} (Fin n)) (prefixCuts ranks)) R,
      q ≫ (coordinateFlagInclusion k (ULift.{u} (Fin n)) (prefixCuts ranks) ≫ matrixIso.hom) = g) ↔
      ∀ i j : ULift.{u} (Fin n), j.down < i.down →
        (E.hom.app R g : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val i j = 0

end CoordinateGeometry

/-- The standard flag scheme and its projective realization for every rank sequence. -/
def FlagSchemeGeometry : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (n : ℕ) (β : Module.Basis (Fin n) k V) (m : ℕ) (ranks : Fin m → ℕ),
    StrictMono ranks → (∀ i, ranks i ≤ Module.finrank k V) →
    ∃ (P : ∀ i : Fin m, PluckerEmbedding.PluckerMorphism (liftedBasis β) (ranks i))
      (D : FlagIncidence.Presentation ranks (liftedBasis β)
        (fun i ↦ (P i).charts) (fun i ↦ (P i).families))
      (G : GroupScheme k)
      (E : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
      (A : FlagIncidence.Action ranks (liftedBasis β) (fun i ↦ (P i).charts) D.inclusion G E),
      (∀ i, IsClosedImmersion (P i).morphism.left ∧ PluckerEmbedding.IsEquivariant (liftedBasis β) (P i) ∧
        ((ranks i = 0 ∨ ranks i = Module.finrank k V) → Nonempty (IsTerminal (P i).charts.scheme))) ∧
      AffineFlagPoints (liftedBasis β) ranks P D ∧
      FlagIncidence.HasLocalAdaptedBases ranks (liftedBasis β) (fun i ↦ (P i).charts) D.inclusion ∧
      FlagIncidence.HasLocalTransitivity ranks (liftedBasis β) (fun i ↦ (P i).charts) D.inclusion G E A ∧
      Nonempty (ProjectivePresentation (liftedBasis β) ranks P D G E A) ∧
      Nonempty (CoordinateStabilizer β ranks P D G E A)

end

end LinearAlgebraicGroups.Specs.FlagSchemes
