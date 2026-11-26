import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.F4RealCompletion
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.F4RealCompletionBorelPair
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.F4RealCompletionCartan
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RealAlbertGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Topology WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.F4RealCompletion

open LinearAlgebraicGroups.Specs hiding coordinateMap
open Specs.Arithmetic.F4RealCompletion (PositiveRankNoncompact RealCompletionPointComparison
  SmallRealCoordinates SmallRealGroupPresentation liftTestAlgebra realRationalTestAlgebraIso
  RadicalPointComparison)
open AdelicGroups (PointsIn asMatrix)
open CompactProductIsolation (Contracted)
open Specs.RealAlbertGroups (HasAbsoluteTypeF4 NoncompactRealParabolicGeneration RealPointsConnected)
open Specs.Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints cocharacterRadicalPoints)
open IntegralModels (MatrixRealization)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition lieImage)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (HasLimit cocharacterPoint unitPoint)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open private gm unitEquiv unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open Unipotent (Index closedSubgroupAlgebraicGroup)

open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private coordinateMap coordinateMap_spec specMap_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private asMatrix_isClosedEmbedding coordinateMap_of_map matrixPresentation continuous_glEvaluation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private contracted_eq_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
open private limitIsParabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- A nonzero tangent direction in a contracting subgroup gives a nonidentity
rational point of the same subgroup, using its affine-space coordinates. -/
private theorem exists_nonidentity_contracting_point
    {F : Type u} [Field F] (G : AffineAlgebraicGroup F) (hG : Specs.GeometricRadicals.IsReductive G)
    (i : MatrixRealization G) (c : Cocharacter G.val) (D : LimitDecomposition c)
    {v : Lie F G.val} (hv : v ∈ lieImage D.contracting) (hv₀ : v ≠ 0) :
    ∃ g : PointsIn i F, g ≠ 1 ∧
      g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app
        (CommAlgCat.of F F)).hom).range := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup D.contracting)
  obtain ⟨n, _, q, _, _, _, _⟩ :=
    Relative.SplitContractingRadical.contractingPolynomialCoordinates G hG c D A e
  let iso := hopfSpecPointIso A ≪≫ (groupPointsFunctor F).mapIso e
  have hn : n ≠ 0 := by
    rintro rfl
    let C := (MvPolynomial.isEmptyAlgEquiv F (Fin 0)).symm.trans q
    let R := CommAlgCat.of F (DualNumber F)
    let f := (iso.app R).groupIsoToMulEquiv
    obtain ⟨z, rfl⟩ := hv
    have hz : z = 0 := by
      apply Subtype.ext
      apply f.symm.injective
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro b
      obtain ⟨a, rfl⟩ := C.surjective b
      have ha : C a = algebraMap F A a := C.commutes a
      rw [ha]
      exact ((f.symm z.toMul.val).ofConv.commutes a).trans
        ((f.symm (0 : Lie F D.contracting.group).toMul.val).ofConv.commutes a).symm
    exact hv₀ (hz ▸ map_zero (mapPointKernel D.contracting.inclusion))
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let R := CommAlgCat.of F F
  let f := (iso.app R).groupIsoToMulEquiv
  let p : A →ₐ[F] R := (MvPolynomial.aeval (fun _ : Fin n => (1 : R))).comp q.symm.toAlgHom
  let r : A →ₐ[F] R := (MvPolynomial.aeval (fun _ : Fin n => (0 : R))).comp q.symm.toAlgHom
  have hpr : p ≠ r := by
    intro h
    have he := DFunLike.congr_fun h (q (MvPolynomial.X j))
    simp [p, r] at he
  let inc := (((groupPointsFunctor F).map D.contracting.inclusion).app R).hom
  have hinc : Function.Injective inc := by
    letI : IsClosedImmersion D.contracting.inclusion.hom.hom.left := D.contracting.isClosedImmersion
    intro a b hab
    apply Over.OverMorphism.ext
    apply (cancel_mono D.contracting.inclusion.hom.hom.left).mp
    exact congrArg (fun x : Points G.val.X R => x.left) hab
  have hdiff : inc (f (toConv p)) ≠ inc (f (toConv r)) :=
    fun h => hpr (congrArg WithConv.ofConv (f.injective (hinc h)))
  by_cases hp : inc (f (toConv p)) = 1
  · exact ⟨inc (f (toConv r)), fun hr => hdiff (hp.trans hr.symm), _, rfl⟩
  · exact ⟨inc (f (toConv p)), hp, _, rfl⟩

/-- A compact Hausdorff group has trivial contraction groups, whereas positive
relative rank produces a nontrivial contracting point. -/
theorem positiveRankNoncompact : PositiveRankNoncompact.{u} := by
  intro F _ G i hG hr hcompact
  obtain ⟨S, _, c, D, v, hv, hv₀⟩ := LocalCocharacterEvaluation.isotropicContractingLie G hG hr
  obtain ⟨g, hg, hgD⟩ :=
    exists_nonidentity_contracting_point G (reductive_of_semisimple G hG) i _ D hv hv₀
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := F)
  have hscalar : Continuous (algebraMap F F) := by
    simpa using (continuous_id : Continuous (fun x : F => x))
  have h : Contracted g := ⟨_, LocalCocharacterEvaluation.contractingEvaluation
    G i (c ≫ S.inclusion) D hscalar t ht g hgD⟩
  letI : T2Space (PointsIn i F) := (asMatrix_isClosedEmbedding i F).isEmbedding.t2Space
  exact hg (contracted_eq_one h)


/-- An isomorphism of test algebras transports the matrix point topology by
entrywise application of the coefficient isomorphism. -/
private def pointsHomeomorphOfAlgEquiv
    {F R S : Type u} [Field F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    {G : AffineAlgebraicGroup F} (i : MatrixRealization G) (e : R ≃ₐ[F] S)
    (he : Continuous e) (he' : Continuous e.symm) : PointsIn i R ≃ₜ* PointsIn i S := by
  let A := CommAlgCat.of F R
  let B := CommAlgCat.of F S
  let P := (groupPointsFunctor F).obj G.val
  let E : A ≅ B := CommAlgCat.isoMk e
  let p : PointsIn i R ≃* PointsIn i S := (P.mapIso E).groupIsoToMulEquiv
  let m := (groupPointsFunctor F).map i.embedding ≫ i.matrix.hom
  have h₁ (x : PointsIn i R) :
      asMatrix i S (p x) = Matrix.GeneralLinearGroup.map e.toRingHom (asMatrix i R x) :=
    NatTrans.naturality_apply m E.hom x
  have h₂ (x : PointsIn i S) :
      asMatrix i R (p.symm x) = Matrix.GeneralLinearGroup.map e.symm.toRingHom (asMatrix i S x) :=
    NatTrans.naturality_apply m E.inv x
  refine { p with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (IsInducing.induced (asMatrix i S)).continuous_iff.mpr
    change Continuous (fun x : PointsIn i R => asMatrix i S (p x))
    simp_rw [h₁]
    exact
      ((Continuous.generalLinearGroup_map (f := e.toRingHom) he).comp (continuous_induced_dom :
        Continuous (asMatrix i R)))
  · apply (IsInducing.induced (asMatrix i R)).continuous_iff.mpr
    change Continuous (fun x : PointsIn i S => asMatrix i R (p.symm x))
    simp_rw [h₂]
    exact
      ((Continuous.generalLinearGroup_map (f := e.symm.toRingHom) he').comp (continuous_induced_dom :
        Continuous (asMatrix i S)))

/-- The coefficient isometry extends to a multiplicative homeomorphism of the
original matrix point group with the scalar-extended points. -/
theorem realCompletionPointComparison : RealCompletionPointComparison.{u} := by
  intro F _ e he G i
  let q : F ≃+* ULift.{u} ℝ := e.trans ULift.ringEquiv.symm
  letI : Algebra F (ULift.{u} ℝ) := q.toRingHom.toAlgebra
  let a : F ≃ₐ[F] ULift.{u} ℝ := AlgEquiv.ofRingEquiv (f := q) (fun _ => rfl)
  have hf : Continuous q := continuous_uliftUp.comp he.continuous
  let ei : F ≃ᵢ ℝ := ⟨e.toEquiv, he⟩
  have hq : Continuous q.symm := ei.symm.continuous.comp continuous_uliftDown
  obtain ⟨h, j, _, f, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison F (ULift.{u} ℝ) G i
  exact ⟨h, j, ⟨f.trans (pointsHomeomorphOfAlgEquiv i a hf hq).symm⟩⟩

private theorem smallCoordinates {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G : AffineAlgebraicGroup F) :
    ∃ (A : HopfAlgebraCategory F) (_ : Algebra.FiniteType F A),
      Nonempty (specGroup A ≅ G.val) ∧
      ∃ (P : FGAlgCatSkeleton K) (r : P.eval.obj ≃+* A),
        r.toRingHom.comp (algebraMap K P.eval.obj) =
          (algebraMap F A).comp e.symm.toRingHom := by
  obtain ⟨A, hA, hG⟩ := groupPresentation G
  have hF : (algebraMap F A).FiniteType :=
    RingHom.finiteType_algebraMap.mpr hA
  have hK : ((algebraMap F A).comp e.symm.toRingHom).FiniteType :=
    hF.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective)
  obtain ⟨P, r, hr⟩ := hK.exists_smallRepr
  exact ⟨A, hA, hG, P, r, hr.symm⟩

/-- Finitely many coordinate generators over a real completion make its
coordinate algebra a quotient of a polynomial ring over the actual reals. -/
theorem smallRealCoordinates : SmallRealCoordinates.{u} :=
  fun e G => smallCoordinates e G

private def coordinateHomEquiv {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K)
    {B : TestAlgebra K} {A : TestAlgebra F} (r : B ≃+* A)
    (hr : r.toRingHom.comp (algebraMap K B) = (algebraMap F A).comp e.symm.toRingHom)
    (R : TestAlgebra K) : (B ⟶ R) ≃ (A ⟶ (liftTestAlgebra e).obj R) where
  toFun f := ConcreteCategory.ofHom (C := TestAlgebra F)
    { toRingHom := (ULift.ringEquiv.symm.toRingHom.comp f.hom.toRingHom).comp r.symm.toRingHom
      commutes' := by
        intro x
        have h := DFunLike.congr_fun hr (e x)
        change r (algebraMap K B (e x)) = algebraMap F A (e.symm (e x)) at h
        rw [e.symm_apply_apply] at h
        change ULift.up (f.hom (r.symm (algebraMap F A x))) = ULift.up (algebraMap K R (e x))
        rw [← h, r.symm_apply_apply, f.hom.commutes] }
  invFun g := ConcreteCategory.ofHom (C := TestAlgebra K)
    { toRingHom := (ULift.ringEquiv.toRingHom.comp g.hom.toRingHom).comp r.toRingHom
      commutes' := by
        intro x
        have h := DFunLike.congr_fun hr x
        change r (algebraMap K B x) = algebraMap F A (e.symm x) at h
        change (g.hom (r (algebraMap K B x))).down = algebraMap K R x
        rw [h, g.hom.commutes]
        change algebraMap K R (e (e.symm x)) = algebraMap K R x
        rw [e.apply_symm_apply] }
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change f.hom (r.symm (r x)) = f.hom x
    rw [r.symm_apply_apply]
  right_inv g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change ULift.up ((g.hom (r (r.symm x))).down) = g.hom x
    rw [r.apply_symm_apply]
    rfl

private theorem coordinateHomEquiv_natural {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K)
    {B : TestAlgebra K} {A : TestAlgebra F} (r : B ≃+* A)
    (hr : r.toRingHom.comp (algebraMap K B) = (algebraMap F A).comp e.symm.toRingHom)
    {R S : TestAlgebra K} (f : R ⟶ S) (p : B ⟶ R) :
    coordinateHomEquiv e r hr S (p ≫ f) =
      coordinateHomEquiv e r hr R p ≫ (liftTestAlgebra e).map f := by
  apply CommAlgCat.hom_ext
  exact AlgHom.ext fun x => rfl

private def coordinatePointEquiv {k : Type u} [Field k] (A R : TestAlgebra k) :
    Points ((testSpec k).obj (op A)) R ≃ (A ⟶ R) where
  toFun := coordinateMap
  invFun f := (testSpec k).map f.op
  left_inv := coordinateMap_spec
  right_inv := coordinateMap_of_map

private theorem coordinatePointEquiv_natural {k : Type u} [Field k] (A : TestAlgebra k)
    {R S : TestAlgebra k} (f : R ⟶ S) (x : Points ((testSpec k).obj (op A)) R) :
    coordinatePointEquiv A S (mapPoints f x) = coordinatePointEquiv A R x ≫ f := by
  change coordinateMap (A := S) (B := A) (mapPoints f x) =
    coordinateMap (A := R) (B := A) x ≫ f
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec]


private theorem continuous_of_matrixEntries
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] [TopologicalSpace R] [IsTopologicalRing R]
    {K S : Type v} [Field K] [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]
    {G : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    (i : MatrixRealization G) (j : MatrixRealization H) (f : PointsIn i R →* PointsIn j S)
    (hf : ∀ a b, Continuous (fun x : PointsIn i R => (asMatrix j S (f x)).val a b)) :
    Continuous f := by
  apply (IsInducing.induced (asMatrix j S)).continuous_iff.mpr
  apply Units.continuous_iff.mpr
  have hmat : Continuous (fun x : PointsIn i R => (asMatrix j S (f x)).val) :=
    continuous_matrix hf
  refine ⟨hmat, ?_⟩
  change Continuous (fun x : PointsIn i R => (asMatrix j S (f x))⁻¹.val)
  have h (x : PointsIn i R) : (asMatrix j S (f x))⁻¹ = asMatrix j S (f x⁻¹) := by
    rw [map_inv, map_inv]
  simp_rw [h]
  exact hmat.comp continuous_inv

private theorem continuous_coordinateEvaluation
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] [TopologicalSpace R]
    [IsTopologicalRing R] {G : AffineAlgebraicGroup k}
    {A : TestAlgebra k} (z : (testSpec k).obj (op A) ≅ G.val.X)
    (i : MatrixRealization G) (a : A) :
    Continuous (fun g : PointsIn i R => (coordinateMap (g ≫ z.inv)).hom a) := by
  obtain ⟨c, hc, h⟩ := matrixPresentation A z i
  obtain ⟨p, rfl⟩ := hc a
  have hp (g : PointsIn i R) :
      (coordinateMap (g ≫ z.inv)).hom (c.hom p) = glEvaluation (asMatrix i R g) p :=
    (DFunLike.congr_fun (h R g) p).symm
  simp_rw [hp]
  exact (continuous_glEvaluation p).comp continuous_induced_dom

private theorem matrixEntry_eq_coordinateEvaluation
    {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {A : TestAlgebra k} (z : (testSpec k).obj (op A) ≅ G.val.X)
    (i : MatrixRealization G) (a b : Index.{u} i.size) :
    ∃ p : A, ∀ (R : Type u) [CommRing R] [Algebra k R] (g : PointsIn i R),
      (asMatrix i R g).val a b = (coordinateMap (g ≫ z.inv)).hom p := by
  obtain ⟨c, _, h⟩ := matrixPresentation A z i
  let p := Specs.StandardGroups.universalMatrix k (Index.{u} i.size) a b
  refine ⟨c.hom p, fun R _ _ g => ?_⟩
  exact (glEvaluation_entry (asMatrix i R g) a b).symm.trans
    (DFunLike.congr_fun (h R g) p)

/-- Restriction along a field isomorphism and universe lift is fully faithful
on test algebras. -/
private def liftTestAlgebraFullyFaithful {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) : (liftTestAlgebra e).FullyFaithful where
  preimage {R S} f := CommAlgCat.ofHom
    { toRingHom := (ULift.ringEquiv.toRingHom.comp f.hom.toRingHom).comp ULift.ringEquiv.symm.toRingHom
      commutes' := fun x => by
        have h := congrArg ULift.down (f.hom.commutes (e.symm x))
        change (f.hom (ULift.up (algebraMap K R (e (e.symm x))))).down =
          algebraMap K S (e (e.symm x)) at h
        rwa [e.apply_symm_apply] at h }
  map_preimage f := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  preimage_map f := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

/-- Every finite-type test algebra over the larger field is isomorphic
to one lifted from the smaller universe. -/
private theorem liftTestAlgebraEssentialImage {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (A : TestAlgebra F) (hA : Algebra.FiniteType F A) :
    ∃ R : TestAlgebra K, Nonempty ((liftTestAlgebra e).obj R ≅ A) := by
  have hF : (algebraMap F A).FiniteType := RingHom.finiteType_algebraMap.mpr hA
  have hK : ((algebraMap F A).comp e.symm.toRingHom).FiniteType :=
    hF.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective)
  obtain ⟨P, r, hr⟩ := hK.exists_smallRepr
  let R := P.eval.obj
  let L := (liftTestAlgebra e).obj R
  let b : L ≃+* A := ULift.ringEquiv.trans r
  let a : L ≃ₐ[F] A := AlgEquiv.ofRingEquiv (f := b) (fun x => by
    have h := DFunLike.congr_fun hr (e x)
    change algebraMap F A (e.symm (e x)) = r (algebraMap K R (e x)) at h
    rw [e.symm_apply_apply] at h
    exact h.symm)
  exact ⟨R, ⟨CommAlgCat.isoMk a⟩⟩

private theorem liftedSpectrumPresentation {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (X : SchemeOver F) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ R : TestAlgebra K, Nonempty ((testSpec F).obj (op ((liftTestAlgebra e).obj R)) ≅ X) := by
  obtain ⟨A, ⟨z⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  have hf : LocallyOfFiniteType ((testSpec F).obj A).hom := by
    rw [← Over.w z.hom]
    have : IsIso z.hom.left := (Over.forget _).map_isIso z.hom
    infer_instance
  have hA : Algebra.FiniteType F A.unop := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap F A.unop))).mp hf
  obtain ⟨R, ⟨j⟩⟩ := liftTestAlgebraEssentialImage e A.unop hA
  exact ⟨R, ⟨(testSpec F).mapIso j.op.symm ≪≫ z⟩⟩

private theorem hom_ext_of_liftedPoints {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) {X Y : SchemeOver F} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {f g : X ⟶ Y} (h : ∀ R : TestAlgebra K, ∀ p : Points X ((liftTestAlgebra e).obj R),
      p ≫ f = p ≫ g) : f = g := by
  obtain ⟨R, ⟨z⟩⟩ := liftedSpectrumPresentation e X
  exact (cancel_epi z.hom).mp (h R z.hom)

set_option maxHeartbeats 900000 in
private theorem liftGroupHom {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G H : AffineAlgebraicGroup F)
    (α : liftTestAlgebra e ⋙ (groupPointsFunctor F).obj G.val ⟶
      liftTestAlgebra e ⋙ (groupPointsFunctor F).obj H.val) :
    ∃ f : G.val ⟶ H.val, ∀ (R : TestAlgebra K) (p : Points G.val.X ((liftTestAlgebra e).obj R)),
      (((groupPointsFunctor F).map f).app ((liftTestAlgebra e).obj R)).hom p = α.app R p := by
  letI := G.prop.1
  letI := G.prop.2.1
  obtain ⟨R₀, ⟨z⟩⟩ := liftedSpectrumPresentation e G.val.X
  let t : Points H.val.X ((liftTestAlgebra e).obj R₀) := α.app R₀ z.hom
  let f := z.inv ≫ t
  have hf (R : TestAlgebra K) (p : Points G.val.X ((liftTestAlgebra e).obj R)) :
      α.app R p = p ≫ f := by
    let a := coordinateMap (p ≫ z.inv)
    let b := (liftTestAlgebraFullyFaithful e).preimage a
    have ha : (liftTestAlgebra e).map b = a := (liftTestAlgebraFullyFaithful e).map_preimage a
    have hb : (testSpec F).map ((liftTestAlgebra e).map b).op = p ≫ z.inv := by
      rw [ha, coordinateMap_spec]
    have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality b)) z.hom
    change α.app R (mapPoints ((liftTestAlgebra e).map b) z.hom) =
      mapPoints ((liftTestAlgebra e).map b) t at hn
    change α.app R ((testSpec F).map ((liftTestAlgebra e).map b).op ≫ z.hom) =
      (testSpec F).map ((liftTestAlgebra e).map b).op ≫ t at hn
    simpa [hb, f, Category.assoc] using hn
  have hmul (R : TestAlgebra K) (p q : Points G.val.X ((liftTestAlgebra e).obj R)) :
      (p * q) ≫ f = (p ≫ f) * (q ≫ f) := by
    rw [← hf, ← hf, ← hf]
    exact (α.app R).hom.map_mul p q
  haveI : IsMonHom f := by
    constructor
    · haveI : IsAffine ((𝟙_ (SchemeOver F)).left) :=
        inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
      haveI : LocallyOfFiniteType ((𝟙_ (SchemeOver F)).hom) :=
        inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of F))))
      apply hom_ext_of_liftedPoints e
      intro R p
      rw [show p = toUnit _ from toUnit_unique _ _]
      change (1 : Points G.val.X ((liftTestAlgebra e).obj R)) ≫ f = 1
      rw [← hf]
      exact (α.app R).hom.map_one
    · haveI : IsAffine (G.val.X ⊗ G.val.X).left := by
        change IsAffine (Limits.pullback G.val.X.hom G.val.X.hom)
        infer_instance
      haveI : LocallyOfFiniteType (G.val.X ⊗ G.val.X).hom := by
        change LocallyOfFiniteType (Limits.pullback.fst G.val.X.hom G.val.X.hom ≫ G.val.X.hom)
        infer_instance
      apply hom_ext_of_liftedPoints e
      intro R p
      let x := p ≫ fst G.val.X G.val.X
      let y := p ≫ snd G.val.X G.val.X
      calc
        p ≫ μ[G.val.X] ≫ f = (x * y) ≫ f := by
          simp only [x, y, Hom.mul_def, lift_comp_fst_snd, Category.assoc]
        _ = (x ≫ f) * (y ≫ f) := hmul R x y
        _ = p ≫ (f ⊗ₘ f) ≫ μ[H.val.X] := by
          have h : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
            apply CartesianMonoidalCategory.hom_ext
            · simp only [x, lift_fst, Category.assoc, tensorHom_fst]
            · simp only [y, lift_snd, Category.assoc, tensorHom_snd]
          simp only [Hom.mul_def, h, Category.assoc]
  exact ⟨Grp.homMk f, fun R p => (hf R p).symm⟩

private def liftedUnitEquiv {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (R : TestAlgebra K) : ((liftTestAlgebra e).obj R)ˣ ≃* Rˣ :=
  Units.mapEquiv (ULift.ringEquiv : ((liftTestAlgebra e).obj R) ≃+* R).toMulEquiv

private theorem liftedUnitEquiv_natural {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) {R S : TestAlgebra K} (a : R ⟶ S) (x : ((liftTestAlgebra e).obj R)ˣ) :
    liftedUnitEquiv e S (Units.map ((liftTestAlgebra e).map a).hom.toMonoidHom x) =
      Units.map a.hom.toMonoidHom (liftedUnitEquiv e R x) := by
  apply Units.ext
  rfl

private theorem liftCocharacter {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup K)
    (p : ∀ R : TestAlgebra K, GroupPoints H.val R ≃*
      GroupPoints G.val ((liftTestAlgebra e).obj R))
    (hp : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : GroupPoints H.val R),
      p S (mapPoints f x) = mapPoints ((liftTestAlgebra e).map f) (p R x))
    (c : Cocharacter H.val) :
    ∃ d : Cocharacter G.val, ∀ (R : TestAlgebra K) (s : ((liftTestAlgebra e).obj R)ˣ),
      cocharacterPoint d ((liftTestAlgebra e).obj R) s =
        p R (cocharacterPoint c R (liftedUnitEquiv e R s)) := by
  let T := liftTestAlgebra e
  let A := groupAlgebra F IntegerCharacters.{u}
  letI : Algebra.FiniteType F A :=
    inferInstanceAs (Algebra.FiniteType F (MonoidAlgebra F IntegerCharacters.{u}))
  let M : AffineAlgebraicGroup F := (finiteTypeHopfSpec F).obj (op ⟨A, inferInstance⟩)
  let q (R : TestAlgebra K) : GroupPoints M.val (T.obj R) ≃* GroupPoints (gm K) R :=
    (unitEquiv (T.obj R)).trans ((liftedUnitEquiv e R).trans (unitEquiv R).symm)
  have hq (R : TestAlgebra K) (s : (T.obj R)ˣ) :
      q R (unitPoint (T.obj R) s) = unitPoint R (liftedUnitEquiv e R s) := by
    apply (unitEquiv R).injective
    change (unitEquiv R) ((unitEquiv R).symm
      (liftedUnitEquiv e R (unitEquiv (T.obj R) (unitPoint (T.obj R) s)))) = _
    rw [(unitEquiv R).apply_symm_apply, unitEquiv_unitPoint, unitEquiv_unitPoint]
  have hn {R S : TestAlgebra K} (a : R ⟶ S) (x : GroupPoints M.val (T.obj R)) :
      q S (mapPoints (T.map a) x) = mapPoints a (q R x) := by
    obtain ⟨s, rfl⟩ : ∃ s : (T.obj R)ˣ, unitPoint (T.obj R) s = x :=
      ⟨unitEquiv (T.obj R) x, (unitEquiv (T.obj R)).injective
        (unitEquiv_unitPoint _ _)⟩
    rw [CocharacterDynamics.mapPoints_unitPoint, hq, hq,
      CocharacterDynamics.mapPoints_unitPoint, liftedUnitEquiv_natural]
  let α : T ⋙ (groupPointsFunctor F).obj M.val ⟶ T ⋙ (groupPointsFunctor F).obj G.val :=
    { app := fun R => GrpCat.ofHom ((p R).toMonoidHom.comp
        ((((groupPointsFunctor K).map c).app R).hom.comp (q R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        change p S (q S (mapPoints (T.map a) x) ≫ c.hom.hom) =
          mapPoints (T.map a) (p R (q R x ≫ c.hom.hom))
        rw [← hp a, hn]
        exact congrArg (p S) (Category.assoc ..) }
  obtain ⟨d, hd⟩ := liftGroupHom e M G α
  refine ⟨d, fun R s => ?_⟩
  have hx := hd R (unitPoint (T.obj R) s)
  change cocharacterPoint d (T.obj R) s = p R (q R (unitPoint (T.obj R) s) ≫ c.hom.hom) at hx
  rw [hq] at hx
  exact hx

open CocharacterDynamics (polynomialAlgebra laurentAlgebra polynomialToLaurent
  polynomialEvaluate laurentConstants laurentParameter orbit mapPoints_comp mapPoints_cocharacterPoint)

private abbrev groundTest (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private def liftRealPolynomial {F : Type u} [Field F] (e : F ≃+* ℝ) :
    polynomialAlgebra (groundTest F) ≅ (liftTestAlgebra e).obj (polynomialAlgebra (groundTest ℝ)) := by
  let b := (Polynomial.mapEquiv e).trans ULift.ringEquiv.symm
  let a : polynomialAlgebra (groundTest F) ≃ₐ[F]
      (liftTestAlgebra e).obj (polynomialAlgebra (groundTest ℝ)) :=
    AlgEquiv.ofRingEquiv (f := b) (fun x => by
      change ULift.up ((Polynomial.C x).map e.toRingHom) = ULift.up (Polynomial.C (e x))
      rw [Polynomial.map_C]
      rfl)
  exact CommAlgCat.isoMk a

private def liftRealLaurent {F : Type u} [Field F] (e : F ≃+* ℝ) :
    laurentAlgebra (groundTest F) ≅ (liftTestAlgebra e).obj (laurentAlgebra (groundTest ℝ)) := by
  let b := (AddMonoidAlgebra.mapRingEquiv ℤ e).trans ULift.ringEquiv.symm
  let a : laurentAlgebra (groundTest F) ≃ₐ[F]
      (liftTestAlgebra e).obj (laurentAlgebra (groundTest ℝ)) :=
    AlgEquiv.ofRingEquiv (f := b) (fun x => by
      change ULift.up (AddMonoidAlgebra.mapRingEquiv ℤ e (LaurentPolynomial.C x)) =
        ULift.up (LaurentPolynomial.C (e x))
      simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingEquiv_single])
  exact CommAlgCat.isoMk a

private theorem liftRealPolynomial_toLaurent {F : Type u} [Field F] (e : F ≃+* ℝ) :
    polynomialToLaurent (groundTest F) ≫ (liftRealLaurent e).hom =
      (liftRealPolynomial e).hom ≫ (liftTestAlgebra e).map (polynomialToLaurent (groundTest ℝ)) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.toRingHom_injective
  apply Polynomial.ringHom_ext
  · intro x
    change ULift.up (AddMonoidAlgebra.mapRingEquiv ℤ e (Polynomial.toLaurent (Polynomial.C x))) =
      ULift.up (Polynomial.toLaurent ((Polynomial.C x).map e.toRingHom))
    simp only [Polynomial.toLaurent_C, Polynomial.map_C, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.mapRingEquiv_single]
    rfl
  · change ULift.up (AddMonoidAlgebra.mapRingEquiv ℤ e (Polynomial.toLaurent Polynomial.X)) =
      ULift.up (Polynomial.toLaurent (Polynomial.X.map e.toRingHom))
    simp only [Polynomial.toLaurent_X, Polynomial.map_X, LaurentPolynomial.T,
      AddMonoidAlgebra.mapRingEquiv_single, map_one]

private theorem liftRealPolynomial_evaluate_zero {F : Type u} [Field F] (e : F ≃+* ℝ) :
    polynomialEvaluate (groundTest F) 0 ≫ (realRationalTestAlgebraIso e).hom =
      (liftRealPolynomial e).hom ≫
        (liftTestAlgebra e).map (polynomialEvaluate (groundTest ℝ) 0) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.toRingHom_injective
  apply Polynomial.ringHom_ext
  · intro x
    change ULift.up (e ((Polynomial.aeval (0 : F)) (Polynomial.C x))) =
      ULift.up ((Polynomial.aeval (0 : ℝ)) ((Polynomial.C x).map e.toRingHom))
    simp only [Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Polynomial.map_C]
    rfl
  · change ULift.up (e ((Polynomial.aeval (0 : F)) Polynomial.X)) =
      ULift.up ((Polynomial.aeval (0 : ℝ)) (Polynomial.X.map e.toRingHom))
    simp only [Polynomial.aeval_X, Polynomial.map_X, map_zero]

private theorem liftRealLaurent_constants {F : Type u} [Field F] (e : F ≃+* ℝ) :
    laurentConstants (groundTest F) ≫ (liftRealLaurent e).hom =
      (realRationalTestAlgebraIso e).hom ≫
        (liftTestAlgebra e).map (laurentConstants (groundTest ℝ)) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change ULift.up (AddMonoidAlgebra.mapRingEquiv ℤ e (LaurentPolynomial.C x)) =
    ULift.up (LaurentPolynomial.C (e x))
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingEquiv_single]

private theorem liftRealLaurent_parameter {F : Type u} [Field F] (e : F ≃+* ℝ) :
    liftedUnitEquiv e (laurentAlgebra (groundTest ℝ))
      (Units.map (liftRealLaurent e).hom.hom.toMonoidHom (laurentParameter (groundTest F))) =
        laurentParameter (groundTest ℝ) := by
  apply Units.ext
  change AddMonoidAlgebra.mapRingEquiv ℤ e (LaurentPolynomial.T 1) = LaurentPolynomial.T 1
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingEquiv_single, map_one]

private theorem mapPoints_injective_of_iso {k : Type u} [Field k] {X : SchemeOver k}
    {R S : TestAlgebra k} (f : R ≅ S) : Function.Injective (mapPoints (X := X) f.hom) := by
  intro x y h
  exact (cancel_epi ((testSpec k).map f.hom.op)).mp h

private theorem liftRealCocharacterLimit {F : Type u} [Field F]
    (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup ℝ)
    (p : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃*
      GroupPoints G.val ((liftTestAlgebra e).obj R))
    (hp : ∀ {R S : TestAlgebra ℝ} (f : R ⟶ S) (x : GroupPoints H.val R),
      p S (mapPoints f x) = mapPoints ((liftTestAlgebra e).map f) (p R x))
    (c : Cocharacter H.val) :
    ∃ d : Cocharacter G.val, ∀ (x : GroupPoints H.val (groundTest ℝ))
      (y : GroupPoints G.val (groundTest F)),
      mapPoints (realRationalTestAlgebraIso e).hom y = p (groundTest ℝ) x →
      HasLimit c x 1 → HasLimit d y 1 := by
  obtain ⟨d, hd⟩ := liftCocharacter e G H p hp c
  refine ⟨d, fun x y hy hx => ?_⟩
  let R := groundTest ℝ
  let S := groundTest F
  let a := liftRealPolynomial e
  let b := liftRealLaurent e
  let r := realRationalTestAlgebraIso e
  let points := (groupPointsFunctor F).obj G.val
  obtain ⟨z, hzL, hz₀⟩ := hx
  let ζ : GroupPoints G.val (polynomialAlgebra S) := mapPoints a.inv (p (polynomialAlgebra R) z)
  have hζ : mapPoints a.hom ζ = p (polynomialAlgebra R) z := by
    change mapPoints a.hom (mapPoints a.inv (p (polynomialAlgebra R) z)) = _
    rw [← mapPoints_comp, Iso.inv_hom_id]
    change (testSpec F).map (𝟙 _).op ≫ _ = _
    simp
  have horb : mapPoints b.hom (orbit d y) = p (laurentAlgebra R) (orbit c x) := by
    let t := cocharacterPoint d (laurentAlgebra S) (laurentParameter S)
    let s := cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
    change (points.map b.hom) (t * (points.map (laurentConstants S)) y * t⁻¹) =
      p (laurentAlgebra R) (s * (show GroupPoints H.val (laurentAlgebra R) from
        mapPoints (laurentConstants R) x) * s⁻¹)
    have ht : points.map b.hom t = p (laurentAlgebra R) s := by
      change mapPoints b.hom (cocharacterPoint d (laurentAlgebra S) (laurentParameter S)) = _
      rw [mapPoints_cocharacterPoint, hd, liftRealLaurent_parameter]
    have hconst : points.map b.hom (points.map (laurentConstants S) y) =
        p (laurentAlgebra R) (mapPoints (laurentConstants R) x) := by
      change mapPoints b.hom (mapPoints (laurentConstants S) y) = _
      rw [← mapPoints_comp, liftRealLaurent_constants, mapPoints_comp, hy, hp]
    change (points.map b.hom).hom (t * (points.map (laurentConstants S)) y * t⁻¹) = _
    rw [map_mul, map_mul, map_inv, show (points.map b.hom).hom t = _ from ht,
      show (points.map b.hom).hom (points.map (laurentConstants S) y) = _ from hconst,
      map_mul, map_mul, map_inv]
  refine ⟨ζ, ?_, ?_⟩
  · apply mapPoints_injective_of_iso b
    rw [← mapPoints_comp, liftRealPolynomial_toLaurent, mapPoints_comp, hζ, ← hp, hzL, horb]
  · apply mapPoints_injective_of_iso r
    rw [← mapPoints_comp, liftRealPolynomial_evaluate_zero, mapPoints_comp, hζ, ← hp, hz₀, map_one]
    exact ((points.map r.hom).hom.map_one).symm

/-- A finite-type presentation and its coordinate comparison across universes. -/
private structure SmallGroupModel {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup K) where
  A : TestAlgebra F
  B : TestAlgebra K
  originalSpec : (testSpec F).obj (op A) ≅ G.val.X
  modelSpec : (testSpec K).obj (op B) ≅ H.val.X
  coordinates : B ≃+* A
  scalar : coordinates.toRingHom.comp (algebraMap K B) =
    (algebraMap F A).comp e.symm.toRingHom
  pointEquiv : ∀ R : TestAlgebra K,
    ((groupPointsFunctor K).obj H.val).obj R ≃*
      ((groupPointsFunctor F).obj G.val).obj ((liftTestAlgebra e).obj R)
  natural : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : ((groupPointsFunctor K).obj H.val).obj R),
    pointEquiv S (((groupPointsFunctor K).obj H.val).map f x) =
      ((groupPointsFunctor F).obj G.val).map ((liftTestAlgebra e).map f) (pointEquiv R x)
  evaluate : ∀ (R : TestAlgebra K) (x : ((groupPointsFunctor K).obj H.val).obj R) (b : B),
    (coordinateMap (pointEquiv R x ≫ originalSpec.inv)).hom (coordinates b) =
      ULift.up ((coordinateMap (x ≫ modelSpec.inv)).hom b)

/-- Descend the full multiplication law by transporting the point functor
and applying affine Yoneda in the smaller universe. -/
private theorem smallGroupModel {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G : AffineAlgebraicGroup F) :
    ∃ H : AffineAlgebraicGroup K, Nonempty (SmallGroupModel e G H) := by
  obtain ⟨A, _, ⟨g⟩, P, r, hr⟩ := smallCoordinates e G
  let B := P.eval.obj
  let X := (testSpec K).obj (op B)
  let Y := (testSpec F).obj (op ((forgetHopfAlgebra (k := F)).obj A))
  let T := liftTestAlgebra e
  let z : Y ≅ G.val.X := (Grp.forget (SchemeOver F)).mapIso g
  let p (R : TestAlgebra K) :
      Points X R ≃ ((groupPointsFunctor F).obj G.val).obj (T.obj R) :=
    (coordinatePointEquiv B R).trans
      ((coordinateHomEquiv e r hr R).trans
        ((coordinatePointEquiv _ (T.obj R)).symm.trans
          { toFun := (· ≫ z.hom)
            invFun := (· ≫ z.inv)
            left_inv := by intro x; simp
            right_inv := by intro x; simp }))
  have hn {R S : TestAlgebra K} (f : R ⟶ S) (x : Points X R) :
      p S (mapPoints f x) = ((groupPointsFunctor F).obj G.val).map (T.map f) (p R x) := by
    change (testSpec F).map (coordinateHomEquiv e r hr S (coordinatePointEquiv B S (mapPoints f x))).op
        ≫ z.hom =
      (testSpec F).map (T.map f).op ≫
        (testSpec F).map (coordinateHomEquiv e r hr R (coordinatePointEquiv B R x)).op ≫ z.hom
    rw [coordinatePointEquiv_natural, coordinateHomEquiv_natural,
      op_comp, Functor.map_comp, Category.assoc]
  let L : NaturalGroupLaw X :=
    { group := fun R => (p R).group
      map_one := by
        intro R S f
        apply (p S).injective
        rw [hn]
        change ((groupPointsFunctor F).obj G.val).map (T.map f) (p R ((p R).symm 1)) =
          p S ((p S).symm 1)
        simp
      map_mul := by
        intro R S f x y
        apply (p S).injective
        rw [hn]
        change ((groupPointsFunctor F).obj G.val).map (T.map f)
          (p R ((p R).symm (p R x * p R y))) =
            p S ((p S).symm (p S (mapPoints f x) * p S (mapPoints f y)))
        simp only [Equiv.apply_symm_apply, hn, map_mul] }
  have hX : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  let s := (groupLawEquiv X hX).symm L
  have hs : inducedGroupLaw X s = L := (groupLawEquiv X hX).apply_symm_apply L
  letI := s
  let H : AffineAlgebraicGroup K := ⟨Grp.mk X, hX, by
    change LocallyOfFiniteType (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))
    infer_instance, by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K B)))
    infer_instance⟩
  let q (R : TestAlgebra K) :
      ((groupPointsFunctor K).obj H.val).obj R ≃*
        ((groupPointsFunctor F).obj G.val).obj (T.obj R) :=
    { p R with
      map_mul' := fun x y => by
        have h := congrArg (fun laws : NaturalGroupLaw X => (laws.group R).mul x y) hs
        change (x * y : Points X R) = (p R).symm (p R x * p R y) at h
        exact (congrArg (p R) h).trans ((p R).apply_symm_apply _) }
  refine ⟨H, ⟨⟨(forgetHopfAlgebra (k := F)).obj A, B, z, Iso.refl _, r, hr, q, hn, ?_⟩⟩⟩
  intro R x b
  let p₀ := coordinateHomEquiv (B := B) (A := (forgetHopfAlgebra (k := F)).obj A) e r hr R
    (coordinateMap x)
  change (coordinateMap ((((testSpec F).map p₀.op) ≫ z.hom) ≫ z.inv)).hom (r b) =
    ULift.up ((coordinateMap (x ≫ 𝟙 X)).hom b)
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, coordinateMap_of_map, Category.comp_id]
  change ULift.up ((coordinateMap x).hom (r.symm (r b))) = _
  rw [r.symm_apply_apply]

open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (GeometricGroup)
open private affineGroupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private geometricallyConnectedOfSepClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

private theorem SmallGroupModel.natural_mapPoints {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) {R S : TestAlgebra K} (a : R ⟶ S) (x : GroupPoints H.val R) :
    D.pointEquiv S (mapPoints a x) = mapPoints ((liftTestAlgebra e).map a) (D.pointEquiv R x) :=
  D.natural a x

private def rationalGroupMap {k : Type u} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) (R : TestAlgebra k) : GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem SmallGroupModel.descendHom {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G G' : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (E : SmallGroupModel e G' H') (f : G.val ⟶ G'.val) :
    ∃ g : H.val ⟶ H'.val, ∀ (R : TestAlgebra K) (x : GroupPoints H.val R),
      E.pointEquiv R (rationalGroupMap g R x) =
        rationalGroupMap f ((liftTestAlgebra e).obj R) (D.pointEquiv R x) := by
  let T := liftTestAlgebra e
  let α : (groupPointsFunctor K).obj H.val ⟶ (groupPointsFunctor K).obj H'.val :=
    { app := fun R => GrpCat.ofHom ((E.pointEquiv R).symm.toMonoidHom.comp
        ((rationalGroupMap f (T.obj R)).comp (D.pointEquiv R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        apply (E.pointEquiv S).injective
        change E.pointEquiv S ((E.pointEquiv S).symm
          (rationalGroupMap f (T.obj S) (D.pointEquiv S (mapPoints a x)))) =
            E.pointEquiv S (mapPoints a ((E.pointEquiv R).symm
              (rationalGroupMap f (T.obj R) (D.pointEquiv R x))))
        rw [MulEquiv.apply_symm_apply, D.natural_mapPoints, E.natural_mapPoints,
          MulEquiv.apply_symm_apply]
        change (((testSpec F).map (T.map a).op ≫ D.pointEquiv R x) ≫ f.hom.hom) =
          (testSpec F).map (T.map a).op ≫ D.pointEquiv R x ≫ f.hom.hom
        exact Category.assoc .. }
  let g := (groupHomEquiv H.val H'.val H.prop.1).symm α
  have hg := (groupHomEquiv H.val H'.val H.prop.1).apply_symm_apply α
  change (groupPointsFunctor K).map g = α at hg
  refine ⟨g, fun R x => ?_⟩
  have hx := congrArg (fun β : (groupPointsFunctor K).obj H.val ⟶ (groupPointsFunctor K).obj H'.val =>
    (β.app R).hom x) hg
  change rationalGroupMap g R x = (E.pointEquiv R).symm
    (rationalGroupMap f (T.obj R) (D.pointEquiv R x)) at hx
  rw [hx, MulEquiv.apply_symm_apply]

private theorem SmallGroupModel.liftHom {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G G' : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (E : SmallGroupModel e G' H') (g : H.val ⟶ H'.val) :
    ∃ f : G.val ⟶ G'.val, ∀ (R : TestAlgebra K) (x : GroupPoints H.val R),
      E.pointEquiv R (rationalGroupMap g R x) =
        rationalGroupMap f ((liftTestAlgebra e).obj R) (D.pointEquiv R x) := by
  let T := liftTestAlgebra e
  let α : T ⋙ (groupPointsFunctor F).obj G.val ⟶ T ⋙ (groupPointsFunctor F).obj G'.val :=
    { app := fun R => GrpCat.ofHom ((E.pointEquiv R).toMonoidHom.comp
        ((rationalGroupMap g R).comp (D.pointEquiv R).symm.toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        have h : (D.pointEquiv S).symm (mapPoints (T.map a) x) =
            mapPoints a ((D.pointEquiv R).symm x) := by
          apply (D.pointEquiv S).injective
          rw [MulEquiv.apply_symm_apply, D.natural_mapPoints, MulEquiv.apply_symm_apply]
        change E.pointEquiv S (rationalGroupMap g S ((D.pointEquiv S).symm (mapPoints (T.map a) x))) =
          mapPoints (T.map a) (E.pointEquiv R (rationalGroupMap g R ((D.pointEquiv R).symm x)))
        rw [h, ← E.natural_mapPoints]
        congr 1 }
  obtain ⟨f, hf⟩ := liftGroupHom e G G' α
  refine ⟨f, fun R x => ?_⟩
  have hx := hf R (D.pointEquiv R x)
  change rationalGroupMap f (T.obj R) (D.pointEquiv R x) = E.pointEquiv R
    (rationalGroupMap g R ((D.pointEquiv R).symm (D.pointEquiv R x))) at hx
  rw [MulEquiv.symm_apply_apply] at hx
  exact hx.symm

private theorem coordinateMap_comp {k : Type u} [Field k] {A B C : TestAlgebra k}
    (f : (testSpec k).obj (op A) ⟶ (testSpec k).obj (op B))
    (g : (testSpec k).obj (op B) ⟶ (testSpec k).obj (op C)) :
    coordinateMap (f ≫ g) = coordinateMap g ≫ coordinateMap f := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec, coordinateMap_spec]

private theorem SmallGroupModel.coordinateMap_eq {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G G' : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (E : SmallGroupModel e G' H')
    (f : G.val ⟶ G'.val) (g : H.val ⟶ H'.val)
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints H.val R),
      E.pointEquiv R (rationalGroupMap g R x) =
        rationalGroupMap f ((liftTestAlgebra e).obj R) (D.pointEquiv R x))
    (b : E.B) :
    (coordinateMap (D.originalSpec.hom ≫ f.hom.hom ≫ E.originalSpec.inv)).hom (E.coordinates b) =
      D.coordinates ((coordinateMap (D.modelSpec.hom ≫ g.hom.hom ≫ E.modelSpec.inv)).hom b) := by
  let X := D.B
  let x : GroupPoints H.val X := D.modelSpec.hom
  let k := coordinateMap (D.originalSpec.hom ≫ f.hom.hom ≫ E.originalSpec.inv)
  let l := coordinateMap (D.modelSpec.hom ≫ g.hom.hom ≫ E.modelSpec.inv)
  have hl : coordinateMap (rationalGroupMap g X x ≫ E.modelSpec.inv) = l := by
    change coordinateMap ((D.modelSpec.hom ≫ g.hom.hom) ≫ E.modelSpec.inv) = _
    rw [Category.assoc]
  have hk := E.evaluate X (rationalGroupMap g X x) b
  rw [h, hl] at hk
  change (coordinateMap ((D.pointEquiv X x ≫ f.hom.hom) ≫ E.originalSpec.inv)).hom (E.coordinates b) =
    ULift.up (l.hom b) at hk
  have hu : (D.pointEquiv X x ≫ D.originalSpec.inv) ≫
      (D.originalSpec.hom ≫ f.hom.hom ≫ E.originalSpec.inv) =
      (D.pointEquiv X x ≫ f.hom.hom) ≫ E.originalSpec.inv := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hu, coordinateMap_comp] at hk
  change (coordinateMap (D.pointEquiv X x ≫ D.originalSpec.inv)).hom
      (k.hom (E.coordinates b)) = ULift.up (l.hom b) at hk
  obtain ⟨y, hy⟩ := D.coordinates.surjective (k.hom (E.coordinates b))
  rw [← hy, D.evaluate] at hk
  have hi : coordinateMap (x ≫ D.modelSpec.inv) = 𝟙 X := by
    change coordinateMap (D.modelSpec.hom ≫ D.modelSpec.inv) = _
    have h₀ : (testSpec K).map (𝟙 X).op = 𝟙 ((testSpec K).obj (op X)) := by
      rw [op_id]
      exact (testSpec K).map_id _
    rw [Iso.hom_inv_id, ← h₀, coordinateMap_of_map]
  rw [hi] at hk
  exact hy.symm.trans (congrArg D.coordinates (ULift.up.inj hk))

private theorem closedImmersion_iff_coordinateSurjective {k : Type u} [Field k]
    {A B : TestAlgebra k} {X Y : SchemeOver k} (z : (testSpec k).obj (op A) ≅ X)
    (w : (testSpec k).obj (op B) ≅ Y) (f : X ⟶ Y) :
    Function.Surjective (coordinateMap (z.hom ≫ f ≫ w.inv)).hom ↔ IsClosedImmersion f.left := by
  let a := coordinateMap (z.hom ≫ f ≫ w.inv)
  let b := CommRingCat.ofHom a.hom.toRingHom
  have he : Spec.map b = z.hom.left ≫ f.left ≫ w.inv.left := by
    have hh := congrArg Over.Hom.left (coordinateMap_spec (z.hom ≫ f ≫ w.inv))
    rw [algSpec_map_left, Over.comp_left, Over.comp_left] at hh
    exact hh
  letI : IsIso z.hom.left := (Over.forget _).map_isIso z.hom
  letI : IsIso w.inv.left := (Over.forget _).map_isIso w.inv
  have hi : IsClosedImmersion (Spec.map b) ↔ IsClosedImmersion f.left := by
    rw [he, ← Category.assoc,
      MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)
        (z.hom.left ≫ f.left) w.inv.left,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) z.hom.left f.left]
  exact ⟨fun h => hi.mp (IsClosedImmersion.spec_of_surjective b h),
    fun h => specMap_surjective b (hi.mpr h)⟩

private theorem SmallGroupModel.closedImmersion_iff {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G G' : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (E : SmallGroupModel e G' H')
    (f : G.val ⟶ G'.val) (g : H.val ⟶ H'.val)
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints H.val R),
      E.pointEquiv R (rationalGroupMap g R x) =
        rationalGroupMap f ((liftTestAlgebra e).obj R) (D.pointEquiv R x)) :
    IsClosedImmersion f.hom.hom.left ↔ IsClosedImmersion g.hom.hom.left := by
  let a := coordinateMap (D.originalSpec.hom ≫ f.hom.hom ≫ E.originalSpec.inv)
  let b := coordinateMap (D.modelSpec.hom ≫ g.hom.hom ≫ E.modelSpec.inv)
  have ha : Function.Surjective a.hom ↔ IsClosedImmersion f.hom.hom.left :=
    closedImmersion_iff_coordinateSurjective D.originalSpec E.originalSpec f.hom.hom
  have hb : Function.Surjective b.hom ↔ IsClosedImmersion g.hom.hom.left :=
    closedImmersion_iff_coordinateSurjective D.modelSpec E.modelSpec g.hom.hom
  have eq (x : E.B) : a.hom (E.coordinates x) = D.coordinates (b.hom x) :=
    D.coordinateMap_eq E f g h x
  rw [← ha, ← hb]
  constructor
  · intro hs x
    obtain ⟨y, hy⟩ := hs (D.coordinates x)
    obtain ⟨z, rfl⟩ := E.coordinates.surjective y
    exact ⟨z, D.coordinates.injective ((eq z).symm.trans hy)⟩
  · intro hs x
    obtain ⟨y, rfl⟩ := D.coordinates.surjective x
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨E.coordinates z, eq z⟩

private def restrictLargeTest {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K)
    (R : TestAlgebra F) : CommAlgCat.{u} K :=
  letI : Algebra K R := ((algebraMap F R).comp e.symm.toRingHom).toAlgebra
  CommAlgCat.of K R

private def restrictLargeTestMap {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K)
    {R S : TestAlgebra F} (a : R ⟶ S) :
    restrictLargeTest e R →ₐ[K] restrictLargeTest e S :=
  ⟨a.hom.toRingHom, fun x => a.hom.commutes (e.symm x)⟩

private def liftedCoordinateEquiv {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (B : TestAlgebra K) (R : TestAlgebra F) :
    (((liftTestAlgebra e).obj B) ⟶ R) ≃ WithConv (B →ₐ[K] restrictLargeTest e R) where
  toFun f := toConv
    { toRingHom := f.hom.toRingHom.comp ULift.ringEquiv.symm.toRingHom
      commutes' := fun x => by
        have h := f.hom.commutes (e.symm x)
        change f.hom (ULift.up (algebraMap K B (e (e.symm x)))) = algebraMap F R (e.symm x) at h
        rw [e.apply_symm_apply] at h
        exact h }
  invFun f :=
    let A := (liftTestAlgebra e).obj B
    ConcreteCategory.ofHom (C := TestAlgebra F) (X := A) (Y := R)
      (@AlgHom.mk F A R _ _ _ A.algebra R.algebra
        (f.ofConv.toRingHom.comp ULift.ringEquiv.toRingHom)
        (fun x => by
          have h := f.ofConv.commutes (e x)
          change f.ofConv (algebraMap K B (e x)) = algebraMap F R (e.symm (e x)) at h
          rw [e.symm_apply_apply] at h
          exact h))
  left_inv _ := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
  right_inv _ := WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

private theorem liftedCoordinateEquiv_natural {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (B : TestAlgebra K) {R S : TestAlgebra F} (a : R ⟶ S)
    (f : (liftTestAlgebra e).obj B ⟶ R) :
    (liftedCoordinateEquiv e B S (f ≫ a)).ofConv =
      (restrictLargeTestMap e a).comp (liftedCoordinateEquiv e B R f).ofConv := by
  apply AlgHom.ext
  intro x
  rfl

/-- Convolution is a group also when the coefficient algebra is in a
different universe from the Hopf algebra. -/
@[instance_reducible]
private def coordinateConvolutionGroup {K : Type} [Field K] (C : HopfAlgebraCategory K)
    (R : CommAlgCat.{u} K) : Group (WithConv (C →ₐ[K] R)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom K C))
  inv_mul_cancel f := by
    let s : WithConv (C →ₐ[K] C) := toConv (HopfAlgebra.antipodeAlgHom K C)
    let i : WithConv (C →ₐ[K] C) := toConv (AlgHom.id K C)
    have hi : s * i = 1 := AlgHom.antipode_id_cancel
    have h := AlgHom.comp_convMul_distrib f.ofConv s i
    rw [hi] at h
    apply WithConv.ofConv_injective
    refine h.symm.trans ?_
    apply AlgHom.ext
    intro a
    exact f.ofConv.commutes (Coalgebra.counit a)

private def coerceSmallCoordinates {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (R : TestAlgebra K) :
    R ≃ₐ[K] restrictLargeTest e ((liftTestAlgebra e).obj R) :=
  AlgEquiv.ofRingEquiv (f := ULift.ringEquiv.symm) (fun x => by
    change ULift.up (algebraMap K R x) = ULift.up (algebraMap K R (e (e.symm x)))
    rw [e.apply_symm_apply])

set_option maxHeartbeats 1000000 in
/-- A finite-type group in the smaller universe has a group model in the
larger universe by extending its convolution law to all test algebras. -/
private theorem largeGroupModel {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (H : AffineAlgebraicGroup K) :
    ∃ G : AffineAlgebraicGroup F, Nonempty (SmallGroupModel e G H) := by
  obtain ⟨C, hC, ⟨c⟩⟩ := groupPresentation H
  let B := (forgetHopfAlgebra (k := K)).obj C
  let b : (testSpec K).obj (op B) ≅ H.val.X := (Grp.forget (SchemeOver K)).mapIso c
  let A := (liftTestAlgebra e).obj B
  let X := (testSpec F).obj (op A)
  let Q (R : TestAlgebra F) := WithConv (C →ₐ[K] restrictLargeTest e R)
  letI (R : TestAlgebra F) : Group (Q R) := coordinateConvolutionGroup C (restrictLargeTest e R)
  let p (R : TestAlgebra F) : Points X R ≃ Q R :=
    (coordinatePointEquiv A R).trans (liftedCoordinateEquiv e B R)
  have hn {R S : TestAlgebra F} (a : R ⟶ S) (x : Points X R) :
      (p S (mapPoints a x)).ofConv = (restrictLargeTestMap e a).comp (p R x).ofConv := by
    change (liftedCoordinateEquiv e B S (coordinatePointEquiv A S (mapPoints a x))).ofConv = _
    rw [coordinatePointEquiv_natural, liftedCoordinateEquiv_natural]
    rfl
  let L : NaturalGroupLaw X :=
    { group := fun R => (p R).group
      map_one := by
        intro R S a
        apply (p S).injective
        apply WithConv.ofConv_injective
        rw [hn]
        change (restrictLargeTestMap e a).comp (p R ((p R).symm 1)).ofConv =
          (p S ((p S).symm 1)).ofConv
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        apply AlgHom.ext
        intro x
        exact (restrictLargeTestMap e a).commutes (Coalgebra.counit x)
      map_mul := by
        intro R S a x y
        apply (p S).injective
        apply WithConv.ofConv_injective
        rw [hn]
        change (restrictLargeTestMap e a).comp (p R ((p R).symm (p R x * p R y))).ofConv =
          (p S ((p S).symm (p S (mapPoints a x) * p S (mapPoints a y)))).ofConv
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, AlgHom.comp_convMul_distrib,
          ← hn a x, ← hn a y] }
  have hX : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let s := (groupLawEquiv X hX).symm L
  have hs : inducedGroupLaw X s = L := (groupLawEquiv X hX).apply_symm_apply L
  letI := s
  have hf : (algebraMap F A).FiniteType := by
    change (ULift.ringEquiv.symm.toRingHom.comp ((algebraMap K B).comp e.toRingHom)).FiniteType
    exact ((RingHom.finiteType_algebraMap.mpr hC).comp
      (RingHom.FiniteType.of_surjective _ e.surjective)).comp_surjective ULift.ringEquiv.symm.surjective
  let G : AffineAlgebraicGroup F := ⟨Grp.mk X, hX, by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap F A)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hf, by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F A)))
    infer_instance⟩
  let q (R : TestAlgebra F) : GroupPoints G.val R ≃* Q R :=
    { p R with
      map_mul' := fun x y => by
        have h := congrArg (fun laws : NaturalGroupLaw X => (laws.group R).mul x y) hs
        change (x * y : Points X R) = (p R).symm (p R x * p R y) at h
        exact (congrArg (p R) h).trans ((p R).apply_symm_apply _) }
  let u (R : TestAlgebra K) : (convolutionPoints C).obj R ≃* Q ((liftTestAlgebra e).obj R) :=
    { toEquiv :=
        { toFun := fun f => toConv ((coerceSmallCoordinates e R).toAlgHom.comp f.ofConv)
          invFun := fun f => toConv ((coerceSmallCoordinates e R).symm.toAlgHom.comp f.ofConv)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_mul' := fun f g => WithConv.ofConv_injective
        (AlgHom.comp_convMul_distrib (coerceSmallCoordinates e R).toAlgHom f g) }
  let r (R : TestAlgebra K) :=
    ((hopfSpecPointIso C ≪≫ (groupPointsFunctor K).mapIso c).app R).groupIsoToMulEquiv
  let v (R : TestAlgebra K) : GroupPoints H.val R ≃*
      GroupPoints G.val ((liftTestAlgebra e).obj R) :=
    (r R).symm.trans ((u R).trans (q _).symm)
  have hcoord (R : TestAlgebra K) (x : GroupPoints H.val R) :
      ((r R).symm x).ofConv = (coordinateMap (x ≫ b.inv)).hom := by
    have h := (r R).apply_symm_apply x
    change (testSpec K).map (CommAlgCat.ofHom ((r R).symm x).ofConv).op ≫ b.hom = x at h
    let w : Points ((testSpec K).obj (op B)) R :=
      (testSpec K).map (CommAlgCat.ofHom ((r R).symm x).ofConv).op
    have hw : w ≫ b.hom = x := h
    have hx : x ≫ b.inv = w := by
      change (show Points H.val.X R from x) ≫ b.inv = w
      rw [← hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hx]
    change _ = (coordinateMap ((testSpec K).map (CommAlgCat.ofHom ((r R).symm x).ofConv).op)).hom
    rw [coordinateMap_of_map]
    rfl
  have heval (R : TestAlgebra K) (x : GroupPoints H.val R) (z : B) :
      (coordinateMap (v R x)).hom (ULift.up z) = ULift.up ((coordinateMap (x ≫ b.inv)).hom z) := by
    have h :
        q ((liftTestAlgebra e).obj R) (v R x) = u R ((r R).symm x) :=
      (q ((liftTestAlgebra e).obj R)).apply_symm_apply _
    have hh := DFunLike.congr_fun (congrArg WithConv.ofConv h) z
    change (coordinateMap (v R x)).hom (ULift.up z) = ULift.up (((r R).symm x).ofConv z) at hh
    rw [hcoord] at hh
    exact hh
  refine ⟨G, ⟨⟨A, B, Iso.refl _, b, ULift.ringEquiv.symm, ?_, v, ?_, ?_⟩⟩⟩
  · ext x : 1
    change ULift.up (algebraMap K B x) = ULift.up (algebraMap K B (e (e.symm x)))
    rw [e.apply_symm_apply]
  · intro R S a x
    change v S (mapPoints a x) = mapPoints ((liftTestAlgebra e).map a) (v R x)
    apply (coordinatePointEquiv A ((liftTestAlgebra e).obj S)).injective
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨z, rfl⟩ := ULift.up_surjective z
    change (coordinateMap (v S (mapPoints a x))).hom (ULift.up z) =
      (coordinateMap (mapPoints ((liftTestAlgebra e).map a) (v R x))).hom (ULift.up z)
    have h1 : coordinateMap (mapPoints ((liftTestAlgebra e).map a) (v R x)) =
        coordinateMap (v R x) ≫ (liftTestAlgebra e).map a :=
      coordinatePointEquiv_natural A (liftTestAlgebra e |>.map a) (v R x)
    have h2 : coordinateMap (mapPoints a (show Points H.val.X R from x) ≫ b.inv) =
        coordinateMap ((show Points H.val.X R from x) ≫ b.inv) ≫ a := by
      have h := coordinatePointEquiv_natural B a (x ≫ b.inv)
      change coordinateMap ((testSpec K).map a.op ≫ x ≫ b.inv) = _
      exact h
    rw [heval, h1, h2]
    change ULift.up (a.hom ((coordinateMap (x ≫ b.inv)).hom z)) =
      ULift.up (a.hom ((coordinateMap (v R x)).hom (ULift.up z)).down)
    rw [heval]
  · intro R x z
    change (coordinateMap (v R x ≫ 𝟙 X)).hom (ULift.up z) = _
    rw [Category.comp_id, heval]

private def restrictLiftIso {F E : Type u} [Field F] [Field E] [Algebra F E]
    {K L : Type} [Field K] [Field L] [Algebra K L] (e : F ≃+* K) (e' : E ≃+* L)
    (he : ∀ x, e' (algebraMap F E x) = algebraMap K L (e x)) (R : TestAlgebra L) :
    (liftTestAlgebra e).obj ((restrictTestAlgebra K L).obj R) ≅
      (restrictTestAlgebra F E).obj ((liftTestAlgebra e').obj R) := by
  let A := (liftTestAlgebra e).obj ((restrictTestAlgebra K L).obj R)
  let B := (restrictTestAlgebra F E).obj ((liftTestAlgebra e').obj R)
  let a : A ≃ₐ[F] B := AlgEquiv.ofRingEquiv (f := RingEquiv.refl (ULift.{u} R)) (fun x => by
    change ULift.up (algebraMap L R (algebraMap K L (e x))) =
      ULift.up (algebraMap L R (e' (algebraMap F E x)))
    rw [he])
  exact CommAlgCat.isoMk a

private theorem restrictLiftIso_natural {F E : Type u} [Field F] [Field E] [Algebra F E]
    {K L : Type} [Field K] [Field L] [Algebra K L] (e : F ≃+* K) (e' : E ≃+* L)
    (he : ∀ x, e' (algebraMap F E x) = algebraMap K L (e x))
    {R S : TestAlgebra L} (a : R ⟶ S) :
    (liftTestAlgebra e).map ((restrictTestAlgebra K L).map a) ≫ (restrictLiftIso e e' he S).hom =
      (restrictLiftIso e e' he R).hom ≫
        (restrictTestAlgebra F E).map ((liftTestAlgebra e').map a) := by
  exact CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

private theorem baseChangeGroupPoints_natural {F E : Type u} [Field F] [Field E] [Algebra F E]
    (G : GroupScheme F) {R S : TestAlgebra E} (a : R ⟶ S)
    (x : GroupPoints ((groupBaseChange F E).obj G) R) :
    baseChangePointGroupEquiv E G S (mapPoints a x) =
      mapPoints ((restrictTestAlgebra F E).map a) (baseChangePointGroupEquiv E G R x) :=
  baseChangePointsNaturality F E G.X a x

private def baseChangeModelPointEquiv {F E : Type u} [Field F] [Field E] [Algebra F E]
    {K L : Type} [Field K] [Field L] [Algebra K L] (e : F ≃+* K) (e' : E ≃+* L)
    (he : ∀ x, e' (algebraMap F E x) = algebraMap K L (e x))
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (R : TestAlgebra L) :
    GroupPoints (baseChangedAlgebraicGroup L H).val R ≃*
      GroupPoints (baseChangedAlgebraicGroup E G).val ((liftTestAlgebra e').obj R) :=
  (baseChangePointGroupEquiv L H.val R).trans <|
    (D.pointEquiv ((restrictTestAlgebra K L).obj R)).trans <|
      ((((groupPointsFunctor F).obj G.val).mapIso (restrictLiftIso e e' he R)).groupIsoToMulEquiv).trans
        (baseChangePointGroupEquiv E G.val ((liftTestAlgebra e').obj R)).symm

private theorem baseChangeModelPointEquiv_natural {F E : Type u} [Field F] [Field E] [Algebra F E]
    {K L : Type} [Field K] [Field L] [Algebra K L] (e : F ≃+* K) (e' : E ≃+* L)
    (he : ∀ x, e' (algebraMap F E x) = algebraMap K L (e x))
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) {R S : TestAlgebra L} (a : R ⟶ S)
    (x : GroupPoints (baseChangedAlgebraicGroup L H).val R) :
    baseChangeModelPointEquiv e e' he D S (mapPoints a x) =
      mapPoints ((liftTestAlgebra e').map a) (baseChangeModelPointEquiv e e' he D R x) := by
  let T := liftTestAlgebra e'
  let r := restrictTestAlgebra K L
  let q := restrictTestAlgebra F E
  let v (R : TestAlgebra L) := restrictLiftIso e e' he R
  let p (R : TestAlgebra L) := baseChangePointGroupEquiv L H.val R
  let p' (R : TestAlgebra L) := baseChangePointGroupEquiv E G.val (T.obj R)
  apply (p' S).injective
  change p' S ((p' S).symm (mapPoints (v S).hom (D.pointEquiv (r.obj S) (p S (mapPoints a x))))) =
    p' S (mapPoints (T.map a) ((p' R).symm (mapPoints (v R).hom (D.pointEquiv (r.obj R) (p R x)))))
  have h₀ : p S (mapPoints a x) = mapPoints (r.map a) (p R x) :=
    baseChangeGroupPoints_natural H.val a x
  rw [MulEquiv.apply_symm_apply, h₀, D.natural_mapPoints]
  rw [show p' S (mapPoints (T.map a) _) = mapPoints (q.map (T.map a)) (p' R _) from
    baseChangeGroupPoints_natural G.val _ _]
  rw [MulEquiv.apply_symm_apply, ← mapPoints_comp, ← mapPoints_comp, restrictLiftIso_natural]

private theorem SmallGroupModel.connected {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (hG : ConnectedSpace G.val.X.left) :
    ConnectedSpace H.val.X.left := by
  letI := hG
  let t : H.val.X.left ≃ₜ G.val.X.left :=
    D.modelSpec.inv.left.homeomorph.trans
      ((PrimeSpectrum.homeomorphOfRingEquiv D.coordinates).trans D.originalSpec.hom.left.homeomorph)
  exact t.symm.surjective.connectedSpace t.symm.continuous

/-- The smaller geometric group has the same point functor as the model of
the original geometric group. -/
private theorem geometricModelComparison {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) :
    let e' := IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure K) e
    ∃ (J : AffineAlgebraicGroup (AlgebraicClosure K))
      (_ : SmallGroupModel e' (GeometricGroup G) J), Nonempty (J.val ≅ (GeometricGroup H).val) := by
  let L := AlgebraicClosure K
  let E := AlgebraicClosure F
  let e' := IsAlgClosure.equivOfEquiv E L e
  have he := IsAlgClosure.equivOfEquiv_algebraMap E L e
  obtain ⟨J, ⟨B⟩⟩ := smallGroupModel e' (GeometricGroup G)
  let p := baseChangeModelPointEquiv e e' he D
  let q (R : TestAlgebra L) :
      GroupPoints J.val R ≃* GroupPoints (GeometricGroup H).val R :=
    (B.pointEquiv R).trans (p R).symm
  let n : (groupPointsFunctor L).obj J.val ≅ (groupPointsFunctor L).obj (GeometricGroup H).val :=
    NatIso.ofComponents (fun R => (q R).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro x
      change q S (mapPoints a x) = mapPoints a (q R x)
      apply (p S).injective
      rw [show (p S) (mapPoints a (q R x)) = mapPoints ((liftTestAlgebra e').map a) (p R (q R x)) from
        baseChangeModelPointEquiv_natural e e' he D a _]
      change p S ((p S).symm (B.pointEquiv S (mapPoints a x))) =
        mapPoints ((liftTestAlgebra e').map a) (p R ((p R).symm (B.pointEquiv R x)))
      simp only [MulEquiv.apply_symm_apply, B.natural_mapPoints])
  exact ⟨J, B, ⟨affineGroupIsoOfPoints J.prop.1 (GeometricGroup H).prop.1 n⟩⟩

private theorem SmallGroupModel.geometricallyConnected {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (hG : GeometricallyConnected G.val.X.hom) :
    GeometricallyConnected H.val.X.hom := by
  obtain ⟨J, B, ⟨j⟩⟩ := geometricModelComparison D
  letI := hG
  let E := AlgebraicClosure F
  let L := AlgebraicClosure K
  letI : GeometricallyConnected (GeometricGroup G).val.X.hom :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd G.val.X.hom (fieldSpecMap F E)))
  have hconn : ConnectedSpace (GeometricGroup G).val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (GeometricGroup G).val.X.hom
  letI : ConnectedSpace J.val.X.left := B.connected hconn
  let jX := ((Grp.forget (SchemeOver L)) ⋙ Over.forget _).mapIso j
  let jT : J.val.X.left ≃ₜ (GeometricGroup H).val.X.left := jX.hom.homeomorph
  letI : ConnectedSpace (GeometricGroup H).val.X.left :=
    jT.surjective.connectedSpace jT.continuous
  letI : IsAffine (GeometricGroup H).val.X.left := (GeometricGroup H).prop.1
  letI : GeometricallyConnected (GeometricGroup H).val.X.hom :=
    geometricallyConnectedOfSepClosed (GeometricGroup H).val.X.hom
  let a := fieldSpecMap K L
  letI : GeometricallyConnected (Limits.pullback.snd H.val.X.hom a) :=
    inferInstanceAs (GeometricallyConnected (GeometricGroup H).val.X.hom)
  letI : Surjective a := ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact LinearAlgebraicGroups.geometricallyConnectedOfSurjectiveBaseChange H.val.X.hom a

open Specs.GeometricRadicals (IsSemisimple geometricSolvableRadical)
open Specs.SchemeDerivedGroup (IsSolvable)
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private solvable_iff_sections rationalSections trivial_of_subsingleton_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem SmallGroupModel.replaceModel {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (j : H.val ≅ H'.val) : Nonempty (SmallGroupModel e G H') := by
  let t := (groupPointsFunctor K).mapIso j.symm
  let q (R : TestAlgebra K) := (t.app R).groupIsoToMulEquiv
  let j₀ := (Grp.forget (SchemeOver K)).mapIso j
  refine ⟨⟨D.A, D.B, D.originalSpec, D.modelSpec ≪≫ j₀, D.coordinates, D.scalar,
    fun R => (q R).trans (D.pointEquiv R), ?_, ?_⟩⟩
  · intro R S a x
    have h : q S (mapPoints a x) = mapPoints a (q R x) := by
      change ((testSpec K).map a.op ≫ x) ≫ j.inv.hom.hom =
        (testSpec K).map a.op ≫ x ≫ j.inv.hom.hom
      rw [Category.assoc]
    change D.pointEquiv S (q S (mapPoints a x)) =
      mapPoints ((liftTestAlgebra e).map a) (D.pointEquiv R (q R x))
    rw [h, D.natural_mapPoints]
  · intro R x b
    change (coordinateMap (D.pointEquiv R (q R x) ≫ D.originalSpec.inv)).hom (D.coordinates b) =
      ULift.up ((coordinateMap (x ≫ j.inv.hom.hom ≫ D.modelSpec.inv)).hom b)
    rw [D.evaluate]
    change ULift.up ((coordinateMap ((x ≫ j.inv.hom.hom) ≫ D.modelSpec.inv)).hom b) = _
    rw [Category.assoc]

private theorem SmallGroupModel.geometric {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) :
    Nonempty (SmallGroupModel (IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure K) e)
      (GeometricGroup G) (GeometricGroup H)) := by
  obtain ⟨J, B, ⟨j⟩⟩ := geometricModelComparison D
  exact B.replaceModel j

private def groundLiftIso {F : Type u} [Field F] {K : Type} [Field K] (e : F ≃+* K) :
    groundTest F ≅ (liftTestAlgebra e).obj (groundTest K) := by
  let A := (liftTestAlgebra e).obj (groundTest K)
  let a : F ≃+* A := e.trans ULift.ringEquiv.symm
  let b : F ≃ₐ[F] A := AlgEquiv.ofRingEquiv (f := a) (fun _ => rfl)
  exact CommAlgCat.isoMk b

private def groundSpecIso (k : Type u) [Field k] :
    𝟙_ (SchemeOver k) ≅ (testSpec k).obj (op (groundTest k)) :=
  (isTerminalTensorUnit (C := SchemeOver k)).uniqueUpToIso (affineBaseTerminal k)

private def groundPointsToSections {k : Type u} [Field k] (G : GroupScheme k) :
    GroupPoints G (groundTest k) ≃* rationalSections G :=
  ((yonedaGrp.obj G).mapIso (groundSpecIso k).op).groupIsoToMulEquiv

private def SmallGroupModel.rationalEquiv {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) : rationalSections H.val ≃* rationalSections G.val :=
  (groundPointsToSections H.val).symm.trans <|
    (D.pointEquiv (groundTest K)).trans <|
      ((((groupPointsFunctor F).obj G.val).mapIso (groundLiftIso e)).groupIsoToMulEquiv).symm.trans
        (groundPointsToSections G.val)

private theorem isNormalSubgroup_of_liftedPoints {F : Type u} [Field F] {K : Type} [Field K]
    (e : F ≃+* K) (G H : AffineAlgebraicGroup F)
    (i : H.val ⟶ G.val)
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints G.val ((liftTestAlgebra e).obj R))
      (y : GroupPoints H.val ((liftTestAlgebra e).obj R)),
      ∃ z : GroupPoints H.val ((liftTestAlgebra e).obj R),
        rationalGroupMap i _ z = x * rationalGroupMap i _ y * x⁻¹) :
    IsNormalSubgroup i := by
  let X := G.val.X ⊗ H.val.X
  letI : IsAffine G.val.X.left := G.prop.1
  letI : IsAffine H.val.X.left := H.prop.1
  letI : LocallyOfFiniteType G.val.X.hom := G.prop.2.1
  letI : LocallyOfFiniteType H.val.X.hom := H.prop.2.1
  letI : IsAffine X.left := inferInstanceAs (IsAffine (Limits.pullback G.val.X.hom H.val.X.hom))
  letI : LocallyOfFiniteType X.hom := inferInstanceAs
    (LocallyOfFiniteType (Limits.pullback.fst G.val.X.hom H.val.X.hom ≫ G.val.X.hom))
  obtain ⟨R, ⟨p⟩⟩ := liftedSpectrumPresentation e X
  obtain ⟨z, hz⟩ := h R (p.hom ≫ fst G.val.X H.val.X) (p.hom ≫ snd G.val.X H.val.X)
  let z₀ : Points H.val.X ((liftTestAlgebra e).obj R) := z
  refine ⟨p.inv ≫ z₀, ?_⟩
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc p.hom (p.inv ≫ z₀), Iso.hom_inv_id_assoc]
  change z₀ ≫ i.hom.hom = p.hom ≫ subgroupConjugation i
  rw [show z₀ ≫ i.hom.hom = (p.hom ≫ fst G.val.X H.val.X) *
      ((p.hom ≫ snd G.val.X H.val.X) ≫ i.hom.hom) *
      (p.hom ≫ fst G.val.X H.val.X)⁻¹ from hz]
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

private theorem SmallGroupModel.liftNormal {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G G' : AffineAlgebraicGroup F} {H H' : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (E : SmallGroupModel e G' H')
    (f : G.val ⟶ G'.val) (g : H.val ⟶ H'.val)
    (h : ∀ (R : TestAlgebra K) (x : GroupPoints H.val R),
      E.pointEquiv R (rationalGroupMap g R x) =
        rationalGroupMap f ((liftTestAlgebra e).obj R) (D.pointEquiv R x))
    (hn : IsNormalSubgroup g) : IsNormalSubgroup f := by
  apply isNormalSubgroup_of_liftedPoints e G' G f
  intro R x y
  obtain ⟨x, rfl⟩ := (E.pointEquiv R).surjective x
  obtain ⟨y, rfl⟩ := (D.pointEquiv R).surjective y
  obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections hn x y
  refine ⟨D.pointEquiv R z, ?_⟩
  rw [← h R z, ← h R y]
  change E.pointEquiv R (z ≫ g.hom.hom) = _
  rw [hz, map_mul, map_mul, map_inv]
  rfl

private theorem SmallGroupModel.connected_iff {F : Type u} [Field F] {K : Type} [Field K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) :
    ConnectedSpace G.val.X.left ↔ ConnectedSpace H.val.X.left :=
  (D.modelSpec.inv.left.homeomorph.trans
    ((PrimeSpectrum.homeomorphOfRingEquiv D.coordinates).trans
      D.originalSpec.hom.left.homeomorph)).connectedSpace_iff.symm

private theorem SmallGroupModel.liftSolvable {F : Type u} [Field F] [IsAlgClosed F]
    {K : Type} [Field K] [IsAlgClosed K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (sG : Smooth G.val.X.hom)
    (sH : Smooth H.val.X.hom) (cH : ConnectedSpace H.val.X.left) (h : IsSolvable H.val) :
    IsSolvable G.val := by
  letI : Group.IsSolvable (rationalSections H.val) := (solvable_iff_sections H sH cH).mp h
  have hs : Group.IsSolvable (rationalSections G.val) :=
    Group.isSolvable_of_surjective (f := D.rationalEquiv.toMonoidHom) D.rationalEquiv.surjective
  exact (solvable_iff_sections G sG (D.connected_iff.mpr cH)).mpr hs

private theorem rationalSections_subsingleton_of_trivial {k : Type u} [Field k]
    (G : GroupScheme k) (e : G ≅ Grp.trivial (SchemeOver k)) :
    Subsingleton (rationalSections G) := by
  let f := e.hom.hom.hom
  letI : IsIso f := (Grp.forget (SchemeOver k)).map_isIso e.hom
  exact ⟨fun x y => (cancel_mono f).mp ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)⟩

/-- Smoothness in characteristic zero and the transported geometric
solvable radical show that the real model is semisimple. -/
private theorem SmallGroupModel.semisimple {F : Type u} [Field F] [CharZero F]
    {K : Type} [Field K] [CharZero K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (D : SmallGroupModel e G H) (hG : IsSemisimple G) : IsSemisimple H := by
  refine ⟨characteristicZeroSmoothness K H, D.geometricallyConnected hG.2.1, ?_⟩
  let E := AlgebraicClosure F
  let L := AlgebraicClosure K
  let e' := IsAlgClosure.equivOfEquiv E L e
  let N := geometricSolvableRadical H
  let N₀ := closedSubgroupAlgebraicGroup N
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest H
  obtain ⟨D'⟩ := D.geometric
  obtain ⟨M, ⟨U⟩⟩ := largeGroupModel e' N₀
  obtain ⟨i, hi⟩ := U.liftHom D' N.inclusion
  let M₀ : Specs.ClosedSubgroup (GeometricGroup G).val :=
    ⟨M.val, i, (U.closedImmersion_iff D' i N.inclusion hi).mpr N.isClosedImmersion⟩
  have hMs : Smooth M.val.X.hom := characteristicZeroSmoothness E M
  have hMc : ConnectedSpace M.val.X.left := U.connected_iff.mpr hN.1.2.1
  have hMn : IsNormalSubgroup i := U.liftNormal D' i N.inclusion hi hN.1.2.2
  have hMsolv : IsSolvable M.val := U.liftSolvable hMs hN.1.1 hN.1.2.1 hN.2.1
  have hrad := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  obtain ⟨j, hj⟩ := hrad.2.2 M₀ ⟨hMs, hMc, hMn⟩ hMsolv
  obtain ⟨b⟩ := hG.2.2
  letI : Subsingleton (rationalSections (geometricSolvableRadical G).group) :=
    rationalSections_subsingleton_of_trivial _ b
  letI : IsClosedImmersion i.hom.hom.left := M₀.isClosedImmersion
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hm : Subsingleton (rationalSections M.val) := by
    constructor
    intro x y
    apply (cancel_mono i.hom.hom).mp
    have hj' : j.hom.hom ≫ (geometricSolvableRadical G).inclusion.hom.hom = i.hom.hom :=
      congrArg (Grp.forget (SchemeOver E)).map hj
    rw [← hj', ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (geometricSolvableRadical G).inclusion.hom.hom)
      (Subsingleton.elim (x ≫ j.hom.hom) (y ≫ j.hom.hom))
  letI : Subsingleton (rationalSections N₀.val) :=
    U.rationalEquiv.injective.subsingleton
  exact trivial_of_subsingleton_sections N₀ hN.1.1

/-- The split Borel pair on the geometric group and its Cartan type
are preserved by the comparison on test algebras. -/
private theorem SmallGroupModel.absoluteTypeF4 {F : Type u} [Field F] [CharZero F]
    {K : Type} [Field K] [CharZero K]
    {e : F ≃+* K} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (M : SmallGroupModel e G H) (hG : HasAbsoluteTypeF4 G) : HasAbsoluteTypeF4 H := by
  obtain ⟨hs, P, hP, D, htype⟩ := hG
  have hsH := M.semisimple hs
  have hsGeom : IsSemisimple (GeometricGroup H) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := AlgebraicClosure K)
      H hsH.1 hsH.2.1).mpr hsH
  obtain ⟨M'⟩ := M.geometric
  let e' := IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure K) e
  let L := liftTestAlgebra e'
  let r (R : TestAlgebra (AlgebraicClosure K)) : L.obj R ≃+* R := ULift.ringEquiv
  have hr : Specs.Arithmetic.F4RealCompletionCartan.AlgebraCompatible e' L r :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  let p : Specs.Arithmetic.F4RealCompletionBorelPair.PointComparison L P.G.val
      (GeometricGroup H).val := by
    rw [hP]
    exact ⟨M'.pointEquiv, M'.natural_mapPoints⟩
  obtain ⟨Q, hQ, qG, qT, qB, ht, hb⟩ :=
    F4RealCompletionBorelPair.transportSplitBorelPair (AlgebraicClosure F) (AlgebraicClosure K)
      e' L r hr.1 hr.2 P (GeometricGroup H) (reductive_of_semisimple _ hsGeom) p
  obtain ⟨E⟩ := Classification.Pinning.datumExists Q
  exact ⟨hsH, Q, hQ, E, F4RealCompletionCartan.cartanType e' L r hr P Q
    qG.equiv qT.equiv qB.equiv qG.natural qT.natural qB.natural ht hb D E htype⟩

/-- The scheme-theoretic parabolic radical description can be compared
on point groups using algebraic conjugation limits. -/
theorem radicalPointComparison : RadicalPointComparison.{u} := by
  intro F _ G hG
  obtain ⟨n, M, ⟨m⟩, i₀, hi₀⟩ := faithfulLinearization F G
  let i : MatrixRealization G := ⟨n, M, m, i₀, hi₀⟩
  let R := CommAlgCat.of F F
  ext x
  constructor
  · rintro ⟨P, hP, U, hU, p, hp⟩
    obtain ⟨c, D, _, _, hD, _⟩ :=
      LocalCocharacterEvaluation.parabolicRadicalEvaluation.{u, u} G i P hP
    obtain ⟨f, hf⟩ := hD U hU
    refine ⟨c, D, (((groupPointsFunctor F).map f.hom).app R).hom p, ?_⟩
    rw [← hp, ← hf, Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  · rintro ⟨c, D, p, hp⟩
    have hr := Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c D
    refine ⟨D.parabolic, limitIsParabolic G hG c D,
      Specs.BorelsAndChambers.contractingSubgroup D, hr.1, p, ?_⟩
    change (((groupPointsFunctor F).map
      (D.contractingToParabolic ≫ D.parabolic.inclusion)).app R).hom p = x
    rw [D.contracting_in_G]
    exact hp

/-- Compare the parabolic radical points through the same rational point map
used for the matrix topology. -/
private theorem realModelRadicalImage {F : Type u} [NontriviallyNormedField F]
    (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup ℝ)
    (hG : Specs.GeometricRadicals.IsReductive G) (hH : Specs.GeometricRadicals.IsReductive H)
    (i : MatrixRealization G) (j : MatrixRealization H)
    (p : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃*
      GroupPoints G.val ((liftTestAlgebra e).obj R))
    (hp : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (x : GroupPoints H.val R),
      p S (mapPoints a x) = mapPoints ((liftTestAlgebra e).map a) (p R x))
    (f : PointsIn j ℝ → PointsIn i F)
    (hf : ∀ x, mapPoints (realRationalTestAlgebraIso e).hom (f x) = p (groundTest ℝ) x) :
    f '' (parabolicRadicalPoints H : Set (PointsIn j ℝ)) ⊆ parabolicRadicalPoints G := by
  rw [radicalPointComparison H hH, radicalPointComparison G hG]
  rintro _ ⟨x, ⟨c, D, z, hz⟩, rfl⟩
  have hx : HasLimit c x 1 := (D.contracting_points _ x).mpr ⟨z, hz⟩
  obtain ⟨d, hd⟩ := liftRealCocharacterLimit e G H p hp c
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G d
  have hy : HasLimit d (f x) 1 := hd x (f x) (hf x) hx
  obtain ⟨w, hw⟩ := (E.contracting_points _ (f x)).mp hy
  exact ⟨d, E, w, hw⟩

/-- Compare the matrix topology and radical points of the specified real model. -/
private theorem SmallGroupModel.realMatrixComparison {F : Type u} [NontriviallyNormedField F]
    {e : F ≃+* ℝ} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup ℝ}
    (D : SmallGroupModel e G H) (he : Isometry e) (i : MatrixRealization G) :
    ∃ (j : MatrixRealization H) (f : PointsIn j ℝ ≃ₜ* PointsIn i F),
      (∀ x, mapPoints (realRationalTestAlgebraIso e).hom (f x) = D.pointEquiv (groundTest ℝ) x) ∧
      (Specs.GeometricRadicals.IsReductive G → Specs.GeometricRadicals.IsReductive H →
        f '' (parabolicRadicalPoints H : Set (PointsIn j ℝ)) ⊆ parabolicRadicalPoints G) := by
  let q := D.pointEquiv
  let r := D.coordinates
  let z := D.originalSpec
  let zH := D.modelSpec
  obtain ⟨n, M, ⟨m⟩, j₀, hj₀⟩ := faithfulLinearization ℝ H
  let j : MatrixRealization H := ⟨n, M, m, j₀, hj₀⟩
  let E := ULift.{u} ℝ
  let R₀ := CommAlgCat.of ℝ ℝ
  let a : F ≃+* ULift.{u} ℝ := e.trans ULift.ringEquiv.symm
  letI : Algebra F (ULift.{u} ℝ) := a.toRingHom.toAlgebra
  let t : PointsIn j ℝ ≃* PointsIn i E := q R₀
  have heval (x : PointsIn j ℝ) (b : D.B) :
      (coordinateMap (t x ≫ z.inv)).hom (r b) =
        ULift.up ((coordinateMap (x ≫ zH.inv)).hom b) :=
    D.evaluate R₀ x b
  have ht : Continuous t := by
    apply continuous_of_matrixEntries (R := ℝ) (S := ULift.{u} ℝ) j i t.toMonoidHom
    intro l m
    obtain ⟨p, hp⟩ := matrixEntry_eq_coordinateEvaluation z i l m
    obtain ⟨b, rfl⟩ := r.surjective p
    change Continuous (fun x : PointsIn j ℝ => (asMatrix i E (t x)).val l m)
    simp_rw [hp E, heval]
    exact continuous_uliftUp.comp (continuous_coordinateEvaluation zH j b)
  have ht' : Continuous t.symm := by
    apply continuous_of_matrixEntries (R := ULift.{u} ℝ) (S := ℝ) i j t.symm.toMonoidHom
    intro l m
    obtain ⟨b, hb⟩ := matrixEntry_eq_coordinateEvaluation zH j l m
    change Continuous (fun x : PointsIn i E => (asMatrix j ℝ (t.symm x)).val l m)
    simp_rw [hb ℝ]
    have hh (x : PointsIn i E) :
        (coordinateMap (t.symm x ≫ zH.inv)).hom b =
          ((coordinateMap (x ≫ z.inv)).hom (r b)).down := by
      simpa only [t.apply_symm_apply] using (congrArg ULift.down (heval (t.symm x) b)).symm
    simp_rw [hh]
    exact continuous_uliftDown.comp (continuous_coordinateEvaluation z i (r b))
  let tHomeo : PointsIn j ℝ ≃ₜ* PointsIn i E :=
    { t with continuous_toFun := ht, continuous_invFun := ht' }
  let alg : F ≃ₐ[F] ULift.{u} ℝ := AlgEquiv.ofRingEquiv (f := a) (fun _ => rfl)
  let ei : F ≃ᵢ ℝ := ⟨e.toEquiv, he⟩
  let aHomeo := pointsHomeomorphOfAlgEquiv i alg (continuous_uliftUp.comp he.continuous)
    (ei.symm.continuous.comp continuous_uliftDown)
  let f := tHomeo.trans aHomeo.symm
  have hf (x : PointsIn j ℝ) :
      mapPoints (realRationalTestAlgebraIso e).hom (f x) = q R₀ x := by
    change aHomeo (aHomeo.symm (tHomeo x)) = tHomeo x
    exact aHomeo.apply_symm_apply _
  exact ⟨j, f, hf,
    fun hG hH => realModelRadicalImage e G H hG hH i j q D.natural f hf⟩

/-- The small real model preserves the actual points and their matrix topology. -/
theorem smallRealGroupPresentation : SmallRealGroupPresentation.{u} := by
  intro F _ e he G i
  obtain ⟨H, ⟨D⟩⟩ := smallGroupModel e G
  obtain ⟨j, f, hf, hr⟩ := D.realMatrixComparison he i
  letI : CharZero F :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  exact ⟨H, D.semisimple, D.pointEquiv, D.natural, j, f, hf, hr⟩

/-- Once the geometric type and the radical-point images have been compared,
the two frozen real propositions give the original local conclusions. -/
private theorem localConclusionsOfRealModel
    (hgen : NoncompactRealParabolicGeneration) (hconn : RealPointsConnected)
    {F : Type u} [NontriviallyNormedField F] (G : AffineAlgebraicGroup F)
    (i : MatrixRealization G) (hG : HasAbsoluteTypeF4 G)
    (H : AffineAlgebraicGroup ℝ) (j : MatrixRealization H) (hH : HasAbsoluteTypeF4 H)
    (f : PointsIn j ℝ ≃ₜ* PointsIn i F)
    (hr : f '' (parabolicRadicalPoints H : Set (PointsIn j ℝ)) ⊆ parabolicRadicalPoints G) :
    ConnectedSpace (PointsIn i F) ∧
      (0 < Specs.RelativeRank.relativeRank G → ¬ CompactSpace (PointsIn i F)) ∧
      (¬ CompactSpace (PointsIn i F) →
        Dense (Subgroup.closure (G := PointsIn i F) (parabolicRadicalPoints G) :
          Set (PointsIn i F))) := by
  letI := hconn H j hH
  refine ⟨f.surjective.connectedSpace f.continuous, positiveRankNoncompact G i hG.1, ?_⟩
  intro hnc
  have hnc' : ¬ CompactSpace (PointsIn j ℝ) := by
    intro hc
    exact hnc (f.surjective.compactSpace f.continuous)
  have hd := f.surjective.denseRange.dense_image f.continuous (hgen H j hH hnc').2
  apply hd.mono
  change ((Subgroup.closure (G := PointsIn j ℝ) (parabolicRadicalPoints H)).map
    f.toMulEquiv.toMonoidHom : Set (PointsIn i F)) ⊆ _
  rw [MonoidHom.map_closure]
  exact Subgroup.closure_mono hr

/-- Transfer the real connectedness and generation results to the given
completion, retaining its matrix topology and rational parabolic radicals. -/
theorem realCompletion_conditional : Specs.Arithmetic.F4RealCompletion.ConditionalStatement.{u} := by
  intro hgen hconn F _ e he G i hG
  letI : CharZero F :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  obtain ⟨H, ⟨M⟩⟩ := smallGroupModel e G
  have hH := M.absoluteTypeF4 hG
  obtain ⟨j, f, _, hr⟩ := M.realMatrixComparison he i
  exact localConclusionsOfRealModel hgen hconn G i hG H j hH f
    (hr (reductive_of_semisimple G hG.1) (reductive_of_semisimple H hH.1))

/-- The local conclusions for all real completions of a group of absolute type F₄. -/
theorem realCompletion : Specs.Arithmetic.F4RealCompletion.Statement.{u} :=
  realCompletion_conditional RealAlbertGroups.noncompactRealParabolicGeneration
    RealAlbertGroups.realPointsConnected

end

end LinearAlgebraicGroups.Arithmetic.F4RealCompletion
