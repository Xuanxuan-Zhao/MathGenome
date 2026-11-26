import Specs.LinearAlgebraicGroups.Flag.FlagSchemes
import LinearAlgebraicGroups.Flag.FlagIncidence
import LinearAlgebraicGroups.Flag.PluckerEmbedding
import Mathlib.RingTheory.OrzechProperty
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.FlagSchemes

open Specs.FlagSchemes

noncomputable section

theorem baseChangePreservesInclusion : BaseChangePreservesInclusion.{u} := by
  intro k V _ _ _ R S a d e L M h
  let : Algebra R S := a.hom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq k R S
  rw [Module.Grassmannian.map_toSubmodule, Module.Grassmannian.map_toSubmodule]
  have hcomp : Module.Grassmannian.baseChangeMkQ S M.toSubmodule =
      (Submodule.factor h).baseChange S ∘ₗ
        Module.Grassmannian.baseChangeMkQ S L.toSubmodule := by
    simp only [Module.Grassmannian.baseChangeMkQ, ← LinearMap.comp_assoc,
      ← LinearMap.baseChange_comp, Submodule.factor_comp_mk]
  rw [hcomp]
  exact LinearMap.ker_le_ker_comp _ _

def flagFunctor : FlagFunctorType.{u} := by
  intro k V _ _ _ m ranks
  exact
    { obj := Flag k V ranks
      map := fun a ↦ ↾fun x ↦
        { plane := fun i ↦ Module.Grassmannian.map a.hom (x.plane i)
          nested := fun {i j} h ↦ baseChangePreservesInclusion k V a (x.plane i) (x.plane j) (x.nested h) }
      map_id := by
        intro R
        apply ConcreteCategory.hom_ext
        intro x
        apply Specs.FlagSchemes.Flag.ext
        intro i
        exact Module.Grassmannian.map_id _ R (x.plane i)
      map_comp := by
        intro R S T a b
        apply ConcreteCategory.hom_ext
        intro x
        apply Specs.FlagSchemes.Flag.ext
        intro i
        exact Module.Grassmannian.map_comp _ a.hom b.hom (x.plane i) }

theorem flagFunctorMaps : FlagFunctorMaps flagFunctor := by
  intro k V _ _ _ m ranks
  exact ⟨fun R ↦ Equiv.refl _, fun _ _ _ _ _ ↦ rfl⟩

theorem flagFunctorExists : FlagFunctorExists.{u} := ⟨flagFunctor, flagFunctorMaps⟩

theorem planeSplitAndRank : PlaneSplitAndRank.{u} :=
  GrassmannianCharts.planeSplitAndRank

theorem planeEndpointSubmodules : PlaneEndpointSubmodules.{u} :=
  GrassmannianCharts.planeEndpointSubmodules

theorem planeEndpointsUnique : PlaneEndpointsUnique.{u} :=
  GrassmannianCharts.planeEndpointsUnique

private theorem rankAtStalk_functions {R J : Type u} [CommRing R] [Fintype J]
    (p : PrimeSpectrum R) : Module.rankAtStalk (J → R) p = Fintype.card J := by
  have : Nontrivial R := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free]
  simp

theorem graphChartCoordinates : GraphChartCoordinates.{u} := by
  intro R _ I J _ _
  let chart : ((I → R) →ₗ[R] (J → R)) → GraphChart R I J := fun f ↦ by
    let q := (-f).coprod (LinearMap.id : (J → R) →ₗ[R] (J → R))
    have hq : Function.Surjective q := fun y ↦ ⟨(0, y), by simp [q]⟩
    let e : (((I → R) × (J → R)) ⧸ f.graph) ≃ₗ[R] (J → R) :=
      f.graph.quotEquivOfEq _ (LinearMap.graph_eq_ker_coprod f) ≪≫ₗ
        q.quotKerEquivOfSurjective hq
    refine ⟨⟨f.graph, Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, ?_⟩, ?_⟩
    · intro p
      rw [Module.rankAtStalk_eq_of_equiv e, rankAtStalk_functions]
    · constructor
      · intro x y h
        apply Subtype.ext
        exact Prod.ext h (by
          change x.val.1 = y.val.1 at h
          rw [(f.mem_graph_iff _).mp x.property, (f.mem_graph_iff _).mp y.property, h])
      · intro x
        exact ⟨⟨(x, f x), (f.mem_graph_iff _).mpr rfl⟩, rfl⟩
  refine ⟨Equiv.ofBijective chart ⟨?_, ?_⟩, fun f ↦ rfl⟩
  · intro f g h
    have hgraphs := congrArg (fun z : GraphChart R I J ↦ z.val.toSubmodule) h
    change f.graph = g.graph at hgraphs
    apply LinearMap.ext
    intro x
    have hx : (x, f x) ∈ g.graph := by
      rw [← hgraphs]
      exact (f.mem_graph_iff _).mpr rfl
    exact (g.mem_graph_iff _).mp hx
  · intro L
    obtain ⟨f, hf⟩ := Submodule.exists_eq_graph L.property
    exact ⟨f, Subtype.ext (Module.Grassmannian.ext hf.symm)⟩

theorem graphChartRepresentedOnAffines : GraphChartRepresentedOnAffines.{u} := by
  intro k _ I J _ _ _ R
  obtain ⟨e, he⟩ := graphChartCoordinates R I J
  let A := CommAlgCat.of k (MvPolynomial (J × I) k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let affine : Points (graphChartScheme k I J) R ≃ (A ⟶ R) :=
    ff.homEquiv.symm.trans Quiver.Hom.opEquiv.symm
  let matrix : (A ⟶ R) ≃ Matrix J I R :=
    { toFun := fun f ↦ Matrix.of fun j i ↦ f.hom (MvPolynomial.X (j, i))
      invFun := fun M ↦ CommAlgCat.ofHom (MvPolynomial.aeval fun ji ↦ M ji.1 ji.2)
      left_inv := fun f ↦ by
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        rintro ⟨j, i⟩
        exact MvPolynomial.aeval_X _ (j, i)
      right_inv := fun M ↦ by
        ext j i
        exact MvPolynomial.aeval_X _ (j, i) }
  refine ⟨affine.trans (matrix.trans (Matrix.toLin'.toEquiv.trans e)), ?_⟩
  intro f
  have hf : affine ((testSpec k).map (CommAlgCat.ofHom f).op) = CommAlgCat.ofHom f :=
    affine.apply_symm_apply (CommAlgCat.ofHom f)
  change (e (Matrix.toLin' (matrix (affine ((testSpec k).map (CommAlgCat.ofHom f).op))))).val.toSubmodule =
    (Matrix.toLin' (Matrix.of fun j i ↦ f (MvPolynomial.X (j, i)))).graph
  rw [hf, he]
  rfl

private theorem submodule_map_eq_of_le {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (P : Submodule R M) [Module.Finite R (M ⧸ P)] (e : M ≃ₗ[R] M)
    (h : P.map e.toLinearMap ≤ P) : P.map e.toLinearMap = P := by
  let f := P.mapQ P e.toLinearMap (Submodule.map_le_iff_le_comap.mp h)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    refine ⟨P.mkQ (e.symm x), ?_⟩
    simp [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
  have hinj := OrzechProperty.injective_of_surjective_endomorphism f hsurj
  refine le_antisymm h fun x hx ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hinj
  rw [map_zero, Submodule.mapQ_apply, LinearEquiv.coe_coe, e.apply_symm_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hx

private theorem mem_coordinateSubmodule {R : Type u} {ι : Type v} [CommRing R]
    {selected : Set ι} {x : ι → R} :
    x ∈ coordinateSubmodule R selected ↔ ∀ i, i ∉ selected → x i = 0 := by
  change (fun i : {i : ι // i ∉ selected} ↦ x i.val) = 0 ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.property

theorem coordinateFlagStabilizer : CoordinateFlagStabilizer.{u, v} := by
  classical
  intro R ι _ _ _ m cuts g
  let matrix : Matrix ι ι R := g
  let e := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have he : e.toLinearMap = matrix.mulVecLin := Matrix.GeneralLinearGroup.coe_toLin g
  constructor
  · intro h a i j hj hi
    let w : ι → R := Pi.single j 1
    have hw : w ∈ coordinateSubmodule R (cuts a) := mem_coordinateSubmodule.mpr (by
      intro l hl
      have hlj : l ≠ j := fun heq ↦ hl (heq ▸ hj)
      simp [w, Pi.single_eq_of_ne hlj])
    have hw' := Submodule.mem_map_of_mem (f := matrix.mulVecLin) hw
    rw [h a] at hw'
    simpa [Matrix.mulVecLin_apply, w, Matrix.mulVec_single_one, matrix] using
      (mem_coordinateSubmodule.mp hw') i hi
  · intro h a
    rw [← he]
    apply submodule_map_eq_of_le
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    apply mem_coordinateSubmodule.mpr
    intro i hi
    change (e.toLinearMap x) i = 0
    rw [he, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ cuts a
    · have hz : matrix i j = 0 := h a i j hj hi
      rw [hz, zero_mul]
    · rw [mem_coordinateSubmodule.mp hx j hj, mul_zero]

theorem coordinateFullFlagStabilizer : CoordinateFullFlagStabilizer.{u} := by
  intro R _ n g
  let cuts : Fin n → Set (Fin n) := fun a ↦ {i | i < a}
  rw [show (∀ a : Fin n, (coordinateSubmodule R (cuts a)).map
      (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) R)) = coordinateSubmodule R (cuts a)) ↔
      (∀ a i j, j ∈ cuts a → i ∉ cuts a → g i j = 0) from
    coordinateFlagStabilizer R (Fin n) cuts g]
  constructor
  · intro h i j hji
    exact h i i j hji (lt_irrefl i)
  · intro h a i j hj hi
    exact h i j (lt_of_lt_of_le hj (le_of_not_gt hi))

theorem coordinateFlagClosedLocus : CoordinateFlagClosedLocus.{u} := by
  intro k ι _ _ _ m cuts
  let A := Specs.StandardGroups.GLCoordinates k ι
  let I := coordinateFlagIdeal k ι cuts
  constructor
  · change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  intro R f p
  let qAlg : CommAlgCat.of k A ⟶ CommAlgCat.of k (A ⧸ I) :=
    CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  constructor
  · rintro ⟨q, hq⟩
    let g := (ff.preimage q).unop
    have he := ff.map_preimage q
    change (testSpec k).map g.op = q at he
    change q ≫ (testSpec k).map qAlg.op = (testSpec k).map (CommAlgCat.ofHom f).op at hq
    rw [← he, ← Functor.map_comp] at hq
    have hf := congrArg (fun a ↦ a.unop.hom) (ff.map_injective hq)
    change g.hom.comp (Ideal.Quotient.mkₐ k I) = f at hf
    intro a i j hj hi
    have hmem : Specs.StandardGroups.universalMatrix k ι i j ∈ I :=
      Ideal.subset_span ⟨a, i, j, hj, hi, rfl⟩
    rw [← hf]
    simp only [AlgHom.comp_apply]
    change g.hom (Ideal.Quotient.mk I _) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hmem, map_zero]
  · intro h
    have hI : I ≤ RingHom.ker f.toRingHom := by
      apply Ideal.span_le.mpr
      rintro x ⟨a, i, j, hj, hi, rfl⟩
      exact h a i j hj hi
    let g := Ideal.Quotient.liftₐ I f (fun x hx ↦ hI hx)
    refine ⟨(testSpec k).map (CommAlgCat.ofHom g).op, ?_⟩
    change (testSpec k).map (CommAlgCat.ofHom g).op ≫ (testSpec k).map qAlg.op =
      (testSpec k).map (CommAlgCat.ofHom f).op
    rw [← Functor.map_comp]
    congr 2

open private glEvaluation glEvaluation_entry glCoordinates_ext
  from LinearAlgebraicGroups.Affine.StandardGroups

theorem coordinateFlagSchemeStabilizer : CoordinateFlagSchemeStabilizer.{u} := by
  intro k ι _ _ _ m cuts R g
  let f := glEvaluation (k := k) g
  have he i j : f (Specs.StandardGroups.universalMatrix k ι i j) = g i j :=
    glEvaluation_entry g i j
  refine ⟨f, ⟨he, ?_⟩, ?_⟩
  · have hClosed := (coordinateFlagClosedLocus k ι cuts).2 R f
    have hStab := coordinateFlagStabilizer R ι cuts g
    simp only [he] at hClosed
    exact hClosed.trans hStab.symm
  · intro a ha
    apply glCoordinates_ext
    intro i j
    rw [ha.1 i j, he i j]

theorem emptyFlagUnique : EmptyFlagUnique.{u} := by
  intro k V _ _ _ R ranks
  exact ⟨{ default := ⟨fun i ↦ Fin.elim0 i, fun {i j} _ ↦ Fin.elim0 i⟩
           uniq := by
             rintro ⟨planes, nested⟩
             congr
             funext i
             exact Fin.elim0 i }⟩

private def terminalPointComparison {k : Type u} [Field k] (F : TestAlgebra k ⥤ Type u)
    (h : ∀ R, Unique (F.obj R)) : pointsFunctor (pointScheme k) ≅ F := by
  let T := Over.mkIdTerminal (X := Spec (CommRingCat.of k))
  refine NatIso.ofComponents (fun R ↦ Equiv.toIso
    { toFun := fun _ ↦ (h R).default
      invFun := fun _ ↦ T.from ((testSpec k).obj (op R))
      left_inv := fun _ ↦ T.hom_ext _ _
      right_inv := fun _ ↦ ((h R).uniq _).symm }) ?_
  intro R S a
  apply ConcreteCategory.hom_ext
  intro x
  let := h S
  exact Subsingleton.elim _ _

theorem planeEndpointsRepresentedByPoint : PlaneEndpointsRepresentedByPoint.{u} := by
  intro k V _ _ _ _
  exact ⟨⟨terminalPointComparison _ (fun R ↦ Classical.choice (planeEndpointsUnique k V R).1)⟩,
    ⟨terminalPointComparison _ (fun R ↦ Classical.choice (planeEndpointsUnique k V R).2)⟩⟩

theorem emptyFlagRepresentedByPoint : EmptyFlagRepresentedByPoint.{u} := by
  refine ⟨flagFunctor, flagFunctorMaps, ?_⟩
  intro k V _ _ _ ranks
  exact ⟨terminalPointComparison _ (fun R ↦ Classical.choice (emptyFlagUnique k V R ranks))⟩

set_option autoImplicit false

section FlagGeometry

open scoped CategoryTheory.MonObj

set_option maxRecDepth 1400

open Specs.FlagIncidence (productPlanes GrassmannianProduct Presentation)
open Specs.PluckerEmbedding (PluckerMorphism SchemeAction exteriorTransport matrixTransport)
open Specs.ProjectiveSpaces (projectiveProduct projectiveSpace LineRepresentation LineFamily
  AffineLine changeLineSubmodule)
open GrassmannianCharts (affineProbesEquiv affineProbesEquiv_apply hom_ext_on_affines)
open ProjectiveSpaces (lineRepresentation projectiveSpaceProper segreMorphism segreClosedImmersion)

open private productPlanes_naturality from LinearAlgebraicGroups.Flag.FlagIncidence
open private proper_of_overIso product_proper from LinearAlgebraicGroups.Flag.ProjectiveSpaces

variable {k V Idx : Type u} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Fintype Idx] [DecidableEq Idx] {m : ℕ} (b : Module.Basis Idx k V) (ranks : Fin m → ℕ)
  (P : ∀ i : Fin m, PluckerMorphism b (ranks i))

local notation "C" => (fun i : Fin m ↦ PluckerMorphism.charts (P i))
local notation "ExteriorFactors" => flagWedges k V ranks
local notation "Tens" => flagRepresentation (k := k) (V := V) ranks

section AffineComparison

private def flagAt (D : Presentation ranks b C (fun i ↦ (P i).families))
    (R : TestAlgebra k) (p : Points D.scheme R) : Flag k V ranks R := by
  refine ⟨productPlanes ranks b C (p ≫ D.inclusion), ?_⟩
  intro i j h
  have hn := (D.factor_affine R (p ≫ D.inclusion)).mp ⟨p, rfl⟩
  rcases eq_or_lt_of_le h with he | hlt
  · subst j
    exact le_rfl
  · exact hn hlt

private theorem affineFlagPoints (D : Presentation ranks b C (fun i ↦ (P i).families)) :
    AffineFlagPoints b ranks P D := by
  let : IsClosedImmersion D.inclusion.left := D.closed
  let : Mono D.inclusion := Over.mono_of_mono_left _
  have he (R : TestAlgebra k) : Function.Bijective (flagAt b ranks P D R) := by
    constructor
    · intro p q hpq
      apply (cancel_mono D.inclusion).mp
      apply Pi.hom_ext
      intro i
      apply ((P i).charts.affinePoints.app R).toEquiv.injective
      exact congrArg (fun L : Flag k V ranks R ↦ L.plane i) hpq
    · intro L
      let a (i : Fin m) : Points (P i).charts.scheme R :=
        (P i).charts.affinePoints.inv.app R (L.plane i)
      let p := Pi.lift a
      have hp (i : Fin m) : productPlanes ranks b C p i = L.plane i := by
        change (P i).charts.affinePoints.hom.app R (Pi.lift a ≫ Pi.π _ i) = L.plane i
        rw [Pi.lift_comp_π]
        exact ((P i).charts.affinePoints.app R).toEquiv.apply_symm_apply _
      have hn ⦃i j : Fin m⦄ (hij : i < j) :
          (productPlanes ranks b C p i).toSubmodule ≤ (productPlanes ranks b C p j).toSubmodule := by
        rw [hp, hp]
        exact L.nested hij.le
      obtain ⟨q, hq⟩ := (D.factor_affine R p).mpr @hn
      refine ⟨q, ?_⟩
      apply Specs.FlagSchemes.Flag.ext
      intro i
      change productPlanes ranks b C (q ≫ D.inclusion) i = _
      rw [hq, hp]
  refine ⟨fun R ↦ Equiv.ofBijective (flagAt b ranks P D R) (he R), fun _ _ _ ↦ rfl, ?_⟩
  intro R T a p i
  change productPlanes ranks b C (((testSpec k).map a.op ≫ p) ≫ D.inclusion) i = _
  rw [Category.assoc]
  exact productPlanes_naturality b ranks C a (p ≫ D.inclusion) i

end AffineComparison

section ClosedEmbedding

@[reassoc]
private theorem productPlucker_π (i : ULift.{u} (Fin m)) :
    productPlucker b ranks P ≫ Pi.π (fun j ↦ projectiveSpace k (ExteriorFactors j)) i =
      Pi.π (fun j ↦ (P j).charts.scheme) i.down ≫ (P i.down).morphism :=
  Pi.lift_comp_π _ i

private theorem productPlucker_closed (hP : ∀ i, IsClosedImmersion (P i).morphism.left) :
    IsClosedImmersion (productPlucker b ranks P).left := by
  let X (i : Fin m) := (P i).charts.scheme
  let Y (i : ULift.{u} (Fin m)) := projectiveSpace k (ExteriorFactors i)
  let e : (∏ᶜ (X ∘ Equiv.ulift)) ≅ ∏ᶜ X := Pi.reindex Equiv.ulift X
  have hproper (i : Fin m) : IsProper (X i).hom := by
    have : IsClosedImmersion (P i).morphism.left := hP i
    have : IsProper (projectiveSpace k (Specs.PluckerEmbedding.Wedge k (ranks i) V)).hom :=
      projectiveSpaceProper k _
    rw [← Over.w (P i).morphism]
    infer_instance
  have hp : IsProper (∏ᶜ X).hom :=
    proper_of_overIso e.symm (product_proper _ (fun i ↦ hproper i.down))
  have hy : IsProper (∏ᶜ Y).hom := product_proper Y (fun _ ↦ projectiveSpaceProper k _)
  let p := productPlucker b ranks P
  have : Mono p := by
    constructor
    intro S f g h
    apply Limits.Pi.hom_ext
    intro i
    have : IsClosedImmersion (P i).morphism.left := hP i
    have : Mono (P i).morphism := Over.mono_of_mono_left _
    apply (cancel_mono (P i).morphism).mp
    have hh := congrArg (fun h ↦ h ≫ Pi.π Y (ULift.up i)) h
    change (f ≫ productPlucker b ranks P) ≫ Pi.π _ (ULift.up i) =
      (g ≫ productPlucker b ranks P) ≫ Pi.π _ (ULift.up i) at hh
    simpa only [Category.assoc, productPlucker_π] using hh
  have : IsProper (p.left ≫ (∏ᶜ Y).hom) := Over.w p ▸ hp
  exact (IsClosedImmersion.iff_isProper_and_mono (f := p.left)).mpr
    ⟨IsProper.of_comp p.left (∏ᶜ Y).hom, inferInstance⟩

private theorem flagEmbedding_closed (D : Presentation ranks b C (fun i ↦ (P i).families))
    (hP : ∀ i, IsClosedImmersion (P i).morphism.left) :
    IsClosedImmersion (flagEmbedding b ranks P D (segreMorphism ExteriorFactors)).left := by
  have : IsClosedImmersion D.inclusion.left := D.closed
  have : IsClosedImmersion (productPlucker b ranks P).left := productPlucker_closed b ranks P hP
  have : IsClosedImmersion (segreMorphism (k := k) ExteriorFactors).left := segreClosedImmersion ExteriorFactors
  change IsClosedImmersion (D.inclusion.left ≫ (productPlucker b ranks P).left ≫
    (segreMorphism ExteriorFactors).left)
  infer_instance

end ClosedEmbedding

section TensorAction

open private projectiveBasis tensorBasis tensorChangeEquiv tensorVector tensorVector_tmul
  tensorVector_baseChange extendVector extendVector_tmul tensorLineSubmodule
  from LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private extendedWedgeEquiv matrixExteriorTransport_natural changeSubmodule_map
  matrixPoint_natural exteriorTransportHom matrixPointEquivHom lineAt lineAt_change transportLine
  schemeActionOfSubmodules lineRepresentation_affine_ext affinePlucker_formula matrixTransport_apply_basis
  from LinearAlgebraicGroups.Flag.PluckerEmbedding
open private coordinates_transport from LinearAlgebraicGroups.Flag.FlagIncidence
open private coordinates_basis from LinearAlgebraicGroups.Flag.GrassmannianCharts

set_option maxHeartbeats 1000000

private theorem tensorComparison_pure (R : TestAlgebra k) (v : ∀ i, ExteriorFactors i) :
    tensorChangeEquiv ExteriorFactors R (PiTensorProduct.tprod R (fun i ↦ (1 : R) ⊗ₜ[k] v i)) =
      (1 : R) ⊗ₜ[k] PiTensorProduct.tprod k v := by
  simpa only [Finset.prod_const_one, tensorVector] using tensorVector_tmul ExteriorFactors R (fun _ ↦ 1) v

private theorem tensorComparison_unique (R : TestAlgebra k)
    (c : (⨂[R] i, R ⊗[k] ExteriorFactors i) ≃ₗ[R] R ⊗[k] Tens)
    (hc : ∀ v : ∀ i, ExteriorFactors i,
      c (PiTensorProduct.tprod R (fun i ↦ (1 : R) ⊗ₜ[k] v i)) =
        (1 : R) ⊗ₜ[k] PiTensorProduct.tprod k v) :
    c = tensorChangeEquiv ExteriorFactors R := by
  apply LinearEquiv.toLinearMap_injective
  apply (Basis.piTensorProduct (fun i ↦ (projectiveBasis k (ExteriorFactors i)).baseChange R)).ext
  intro p
  simp only [Basis.piTensorProduct_apply, Module.Basis.baseChange_apply, LinearEquiv.coe_coe]
  exact (hc _).trans (tensorComparison_pure (k := k) (V := V) ranks R _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem cancelBaseChange_one {M : Type u} [AddCommGroup M] [Module k M]
    {R T : TestAlgebra k} (a : R ⟶ T) (x : R ⊗[k] M) :
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T M ((1 : T) ⊗ₜ[R] x) =
      extendVector a x := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T M
  change c ((1 : T) ⊗ₜ[R] x) = extendVector a x
  refine TensorProduct.inductionOn (motive := fun x ↦ c ((1 : T) ⊗ₜ[R] x) = extendVector a x) x ?_ ?_
  · intro r x
    dsimp only [c]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, extendVector_tmul]
    change (a.hom r * 1) ⊗ₜ[k] x = a.hom r ⊗ₜ[k] x
    rw [mul_one]
  · intro x y hx hy
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

local notation "tensorEnd" => fun R g ↦ tensorExteriorTransport b ranks P R (tensorChangeEquiv ExteriorFactors R) g

private theorem tensorTransport_tprod {R : TestAlgebra k} (g : Matrix.GeneralLinearGroup Idx R)
    (v : ∀ i, R ⊗[k] ExteriorFactors i) :
    tensorEnd R g (tensorVector ExteriorFactors R v) =
      tensorVector ExteriorFactors R (fun i ↦
        exteriorTransport ((P i.down).exteriorLines.compare R) (matrixTransport b R g) (v i)) := by
  simp only [tensorExteriorTransport, tensorVector, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, PiTensorProduct.map_tprod]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorTransport_natural {R T : TestAlgebra k} (a : R ⟶ T)
    (g : Matrix.GeneralLinearGroup Idx R) :
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T Tens
    (tensorEnd T (Matrix.GeneralLinearGroup.map a.hom.toRingHom g)).comp c.toLinearMap =
      c.toLinearMap.comp ((tensorEnd R g).baseChange (↥T)) := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let gT := Matrix.GeneralLinearGroup.map a.hom.toRingHom g
  let B := (tensorBasis (k := k) ExteriorFactors).baseChange R
  apply (B.baseChange T).ext
  intro p
  change (tensorEnd T gT).comp _ ((B.baseChange T) p) = _
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul]
  have hleft := cancelBaseChange_one (M := Tens) a (B p)
  have hright := cancelBaseChange_one (M := Tens) a ((tensorEnd R g) (B p))
  rw [hleft, hright]
  let v (i : ULift.{u} (Fin m)) : R ⊗[k] ExteriorFactors i := (1 : R) ⊗ₜ[k] projectiveBasis k (ExteriorFactors i) (p i)
  have hb : B p = tensorVector ExteriorFactors R v := by
    dsimp only [B]
    rw [Module.Basis.baseChange_apply, tensorBasis, Basis.piTensorProduct_apply]
    exact (tensorComparison_pure (k := k) (V := V) ranks R _).symm
  rw [hb, tensorVector_baseChange, tensorTransport_tprod, tensorTransport_tprod, tensorVector_baseChange]
  congr 1
  funext i
  have h := LinearMap.congr_fun
    (matrixExteriorTransport_natural b a g ((P i.down).exteriorLines.compare R)
      ((P i.down).exteriorLines.compare T)) ((1 : T) ⊗ₜ[R] v i)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    cancelBaseChange_one a, gT] using h

variable {G : Specs.GroupScheme k}
  (E : (groupPointsFunctor k).obj G ≅ Specs.StandardGroups.generalLinearPoints k Idx)

private def tensorTransportHom (R : TestAlgebra k) :
    Points G.X R →* Module.End R (R ⊗[k] Tens) :=
  ((tensorChangeEquiv ExteriorFactors R).conjRingEquiv.toMonoidHom.comp PiTensorProduct.mapMonoidHom).comp
    (MonoidHom.pi fun i : ULift.{u} (Fin m) ↦
      (exteriorTransportHom R ((P i.down).exteriorLines.compare R)).comp
        (matrixPointEquivHom b E R))

private theorem tensorTransportHom_natural {R T : TestAlgebra k} (a : R ⟶ T) (g : Points G.X R) :
    letI : Algebra R T := a.hom.toAlgebra
    letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T Tens
    (tensorTransportHom b ranks P E T (mapPoints a g)).comp c.toLinearMap =
      c.toLinearMap.comp ((tensorTransportHom b ranks P E R g).baseChange (↥T)) := by
  let _ : Algebra R T := a.hom.toAlgebra
  let _ : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T Tens
  change (tensorEnd T (E.hom.app T (mapPoints a g))).comp c.toLinearMap =
    c.toLinearMap.comp ((tensorEnd R (E.hom.app R g)).baseChange (↥T))
  rw [matrixPoint_natural E]
  exact tensorTransport_natural b ranks P a (E.hom.app R g)

private def tensorTransportEquiv (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup Idx R) :
    (R ⊗[k] Tens) ≃ₗ[R] (R ⊗[k] Tens) :=
  (tensorChangeEquiv ExteriorFactors R).symm ≪≫ₗ
    PiTensorProduct.congr (fun i : ULift.{u} (Fin m) ↦
      extendedWedgeEquiv ((P i.down).exteriorLines.compare R) (matrixTransport b R g)) ≪≫ₗ
    tensorChangeEquiv ExteriorFactors R

private def projectiveActionOfLinearRepresentation {M : Type u}
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    (ρ : LineRepresentation k M)
    (e : ∀ (R : TestAlgebra k), Points G.X R → (R ⊗[k] M) ≃ₗ[R] (R ⊗[k] M))
    (r : ∀ (R : TestAlgebra k), Points G.X R →* Module.End R (R ⊗[k] M))
    (he : ∀ R g, (e R g).toLinearMap = r R g)
    (hn : ∀ {R T : TestAlgebra k} (a : R ⟶ T) (g : Points G.X R),
      letI : Algebra R T := a.hom.toAlgebra
      letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (a.hom.comp_algebraMap).symm
      let c := TensorProduct.AlgebraTensorModule.cancelBaseChange k R T T M
      (r T (mapPoints a g)).comp c.toLinearMap = c.toLinearMap.comp ((r R g).baseChange (↥T))) :
    { F : SchemeAction G (projectiveSpace k M) //
      ∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points (projectiveSpace k M) R),
        (lineAt ρ (lift g p ≫ F.act)).submodule = (lineAt ρ p).submodule.map (r R g) } := by
  let Y := projectiveSpace k M
  let s (R : TestAlgebra k) (p : Points Y R) := (lineAt ρ p).submodule
  let F : LineFamily k M (G.X ⊗ Y) :=
    { line := fun R q ↦ transportLine (e R (q ≫ fst G.X Y)) (lineAt ρ (q ≫ snd G.X Y))
      compatible := by
        intro R T a q
        let p := q ≫ snd G.X Y
        let g := q ≫ fst G.X Y
        change (lineAt ρ (mapPoints a q ≫ snd G.X Y)).submodule.map
            (e T (mapPoints a q ≫ fst G.X Y)).toLinearMap =
          changeLineSubmodule k M a ((lineAt ρ p).submodule.map (e R g).toLinearMap)
        simp only [he]
        rw [show mapPoints a q ≫ snd G.X Y = mapPoints a p from Category.assoc _ _ _,
          show mapPoints a q ≫ fst G.X Y = mapPoints a g from Category.assoc _ _ _,
          lineAt_change]
        exact (changeSubmodule_map a _ _ (hn a g) (s R p)).symm }
  let act := (ρ.points (G.X ⊗ Y)).symm F
  have hact (R : TestAlgebra k) (g : Points G.X R) (p : Points Y R) :
      s R (lift g p ≫ act) = (s R p).map (r R g) := by
    change ((ρ.points _ (lift g p ≫ act)).line R (𝟙 _)).submodule = _
    rw [ρ.naturality, show ρ.points _ act = F from Equiv.apply_symm_apply _ _]
    change (F.line R (𝟙 _ ≫ lift g p)).submodule = _
    rw [Category.id_comp]
    change (s R (lift g p ≫ snd G.X Y)).map
      (e R (lift g p ≫ fst G.X Y)).toLinearMap = _
    rw [lift_fst, lift_snd, he]
  exact ⟨schemeActionOfSubmodules s (fun _ _ _ h ↦ lineRepresentation_affine_ext ρ h) r act hact, hact⟩

private def tensorProjectiveAction (ρ : LineRepresentation k Tens) :
    { F : SchemeAction G (projectiveSpace k Tens) //
      ∀ (R : TestAlgebra k) (g : Points G.X R) (p : Points (projectiveSpace k Tens) R),
        (lineAt ρ (lift g p ≫ F.act)).submodule =
          (lineAt ρ p).submodule.map (tensorEnd R (E.hom.app R g)) } := by
  exact projectiveActionOfLinearRepresentation ρ
    (fun R g ↦ tensorTransportEquiv b ranks P R (E.hom.app R g))
    (tensorTransportHom b ranks P E) (fun _ _ ↦ rfl) (fun a g ↦ tensorTransportHom_natural b ranks P E a g)

private theorem tensorLineSubmodule_map {R : TestAlgebra k} (g : Matrix.GeneralLinearGroup Idx R)
    (L : ∀ i, Submodule R (R ⊗[k] ExteriorFactors i)) :
    tensorLineSubmodule ExteriorFactors R (fun i ↦ (L i).map
      (exteriorTransport ((P i.down).exteriorLines.compare R) (matrixTransport b R g))) =
      (tensorLineSubmodule ExteriorFactors R L).map (tensorEnd R g) := by
  let e (i : ULift.{u} (Fin m)) :=
    extendedWedgeEquiv ((P i.down).exteriorLines.compare R) (matrixTransport b R g)
  let L' (i : ULift.{u} (Fin m)) := (L i).map (e i).toLinearMap
  let c := tensorChangeEquiv ExteriorFactors R
  let h := PiTensorProduct.congr fun i ↦ (e i).submoduleMap (L i)
  let f := PiTensorProduct.map fun i ↦ (e i).toLinearMap
  have hsquare : (PiTensorProduct.mapIncl L').comp h.toLinearMap =
      f.comp (PiTensorProduct.mapIncl L) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      h, PiTensorProduct.congr_tprod, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod, f]
    rfl
  change ((PiTensorProduct.mapIncl L').range).map c.toLinearMap =
    ((PiTensorProduct.mapIncl L).range.map c.toLinearMap).map
      (c.toLinearMap.comp (f.comp c.symm.toLinearMap))
  rw [← LinearMap.range_comp_of_range_eq_top (PiTensorProduct.mapIncl L')
    (LinearMap.range_eq_top.mpr h.surjective), hsquare, LinearMap.range_comp]
  have hc : (c.toLinearMap.comp (f.comp c.symm.toLinearMap)).comp c.toLinearMap =
      c.toLinearMap.comp f := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp only [← Submodule.map_comp, hc]

omit [Module.Finite k V] in
private theorem matrixTransport_agrees (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup Idx R) :
    Specs.FlagIncidence.matrixTransport b R g = matrixTransport b R g := by
  apply LinearEquiv.toLinearMap_injective
  apply (b.baseChange R).ext
  intro j
  apply (Specs.GrassmannianCharts.coordinates b R).injective
  change Specs.GrassmannianCharts.coordinates b R
      (Specs.FlagIncidence.matrixTransport b R g (b.baseChange R j)) =
    Specs.GrassmannianCharts.coordinates b R (matrixTransport b R g (b.baseChange R j))
  rw [coordinates_transport, matrixTransport_apply_basis, map_sum]
  have hsingle (l : Idx) :
      Specs.GrassmannianCharts.coordinates b R (b.baseChange R l) = Pi.single l 1 := by
    funext i
    rw [Module.Basis.baseChange_apply, coordinates_basis]
    simp [Pi.single_apply, eq_comm]
  simp only [hsingle, Matrix.mulVec_single_one, map_smul]
  funext i
  simp [Pi.single_apply]

private theorem flagSegre_formula
    (hL : ∀ i : Fin m, (P i).lines = lineRepresentation k (ExteriorFactors ⟨i⟩))
    (S : SchemeOver k) (p : S ⟶ projectiveProduct (k := k) ExteriorFactors)
    (R : TestAlgebra k) (a : Points S R) :
    (((lineRepresentation k Tens).points S (p ≫ segreMorphism ExteriorFactors)).line R a).submodule =
      tensorLineSubmodule ExteriorFactors R (fun i ↦ (((P i.down).lines.points S (p ≫ Pi.π _ i)).line R a).submodule) := by
  obtain ⟨c, hc, hf⟩ := ProjectiveSpaces.segrePointFormula (k := k) ExteriorFactors
  have h := hf S p R a
  change _ = _ at h
  rw [tensorComparison_unique (k := k) (V := V) ranks R (c R) (hc R)] at h
  refine h.trans (congrArg (tensorLineSubmodule (k := k) ExteriorFactors R) ?_)
  funext i
  rw [hL i.down]

private theorem flagEmbedding_line (D : Presentation ranks b C (fun i ↦ (P i).families))
    (hL : ∀ i : Fin m, (P i).lines = lineRepresentation k (ExteriorFactors ⟨i⟩))
    {R : TestAlgebra k} (p : Points D.scheme R) :
    (lineAt (lineRepresentation k Tens) (p ≫ flagEmbedding b ranks P D (segreMorphism ExteriorFactors))).submodule =
      tensorLineSubmodule ExteriorFactors R (fun i ↦
        Specs.PluckerEmbedding.lineSubmodule ((P i.down).exteriorLines.compare R)
          (productPlanes ranks b C (p ≫ D.inclusion) i.down)) := by
  let y : Points (projectiveProduct (k := k) ExteriorFactors) R :=
    (p ≫ D.inclusion) ≫ productPlucker b ranks P
  have he : p ≫ flagEmbedding b ranks P D (segreMorphism ExteriorFactors) =
      y ≫ segreMorphism ExteriorFactors := by
    simp only [flagEmbedding, y, Category.assoc]
  unfold lineAt
  rw [he, flagSegre_formula b ranks P hL _ y R (𝟙 _)]
  congr 1
  funext i
  have hπ : y ≫ Pi.π _ i =
      ((p ≫ D.inclusion) ≫ Pi.π _ i.down) ≫ (P i.down).morphism := by
    simp only [y, Category.assoc, productPlucker_π]
  rw [hπ]
  exact affinePlucker_formula b (P i.down) _

private theorem flagEmbedding_equivariant (D : Presentation ranks b C (fun i ↦ (P i).families))
    (A : Specs.FlagIncidence.Action ranks b C D.inclusion G E)
    (hL : ∀ i : Fin m, (P i).lines = lineRepresentation k (ExteriorFactors ⟨i⟩))
    (S : SchemeOver k) (g : S ⟶ G.X) (p : S ⟶ D.scheme) :
    (prod.lift g p ≫ A.onFlags) ≫ flagEmbedding b ranks P D (segreMorphism ExteriorFactors) =
      lift g (p ≫ flagEmbedding b ranks P D (segreMorphism ExteriorFactors)) ≫
        (tensorProjectiveAction b ranks P E (lineRepresentation k Tens)).val.act := by
  let j := flagEmbedding b ranks P D (segreMorphism ExteriorFactors)
  let F := tensorProjectiveAction b ranks P E (lineRepresentation k Tens)
  have hAffine (R : TestAlgebra k) (gR : Points G.X R) (pR : Points D.scheme R) :
      (prod.lift gR pR ≫ A.onFlags) ≫ j = lift gR (pR ≫ j) ≫ F.val.act := by
    apply lineRepresentation_affine_ext (lineRepresentation k Tens)
    change (lineAt (lineRepresentation k Tens) ((prod.lift gR pR ≫ A.onFlags) ≫ j)).submodule =
      (lineAt (lineRepresentation k Tens) (lift gR (pR ≫ j) ≫ F.val.act)).submodule
    rw [F.property, flagEmbedding_line b ranks P D hL, flagEmbedding_line b ranks P D hL]
    let M : Matrix.GeneralLinearGroup Idx R := E.hom.app R gR
    let L (i : ULift.{u} (Fin m)) := Specs.PluckerEmbedding.lineSubmodule
      ((P i.down).exteriorLines.compare R) (productPlanes ranks b C (pR ≫ D.inclusion) i.down)
    change _ = (tensorLineSubmodule ExteriorFactors R L).map (tensorEnd R M)
    rw [← tensorLineSubmodule_map b ranks P M L]
    congr 1
    funext i
    apply PluckerEmbedding.affineExteriorEquivariance k V (ranks i.down) R
    have hrestrict :
        (prod.lift gR pR ≫ A.onFlags) ≫ D.inclusion =
          prod.lift gR (pR ≫ D.inclusion) ≫ A.onProduct := by
      rw [Category.assoc, A.restricts, prod.lift_map_assoc, Category.comp_id]
    rw [hrestrict, A.transport, prod.lift_fst, prod.lift_snd]
    exact congrArg (fun e ↦ (productPlanes ranks b C (pR ≫ D.inclusion) i.down).toSubmodule.map
      e.toLinearMap) (matrixTransport_agrees b R M)
  apply hom_ext_on_affines
  intro R a
  simpa only [Category.assoc, prod.comp_lift_assoc, comp_lift_assoc] using
    hAffine R (a ≫ g) (a ≫ p)

private def projectivePresentation (D : Presentation ranks b C (fun i ↦ (P i).families))
    (A : Specs.FlagIncidence.Action ranks b C D.inclusion G E)
    (hP : ∀ i, IsClosedImmersion (P i).morphism.left)
    (hL : ∀ i : Fin m, (P i).lines = lineRepresentation k (ExteriorFactors ⟨i⟩)) :
    ProjectivePresentation b ranks P D G E A where
  lines := lineRepresentation k Tens
  segre := segreMorphism ExteriorFactors
  tensorCompare := tensorChangeEquiv ExteriorFactors
  tensorCompare_pure := tensorComparison_pure ranks
  segre_formula := flagSegre_formula b ranks P hL
  segre_closed := segreClosedImmersion ExteriorFactors
  embedding_closed := flagEmbedding_closed b ranks P D hP
  proper := by
    let j := flagEmbedding b ranks P D (segreMorphism ExteriorFactors)
    have : IsClosedImmersion j.left := flagEmbedding_closed b ranks P D hP
    have : IsProper (projectiveSpace k Tens).hom := projectiveSpaceProper k Tens
    rw [← Over.w j]
    infer_instance
  linearRepresentation := tensorTransportHom b ranks P E
  linear_formula := fun _ _ ↦ rfl
  linear_baseChange := fun a g ↦ tensorTransportHom_natural b ranks P E a g
  action := (tensorProjectiveAction b ranks P E (lineRepresentation k Tens)).val
  action_on_points := (tensorProjectiveAction b ranks P E (lineRepresentation k Tens)).property
  equivariant := flagEmbedding_equivariant b ranks P E D A hL

end TensorAction

end FlagGeometry

section Stabilizer

open GrassmannianCharts (affineProbesEquiv affineProbesEquiv_apply hom_ext_on_affines)
open Specs.FlagIncidence (productPlanes prefixSubmodule)

open private productPlanes_naturality prefixPlane prefixPlane_map prefixPlane_submodule
  flags_eq_of_planes flagAction_plane coordinates_transport
  from LinearAlgebraicGroups.Flag.FlagIncidence
open private coordinates_basis from LinearAlgebraicGroups.Flag.GrassmannianCharts
open private generalLinearRepresentation Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups

set_option maxRecDepth 1400
set_option maxHeartbeats 1000000

variable {k : Type u} [Field k]

local notation "Base" => Functor.obj (testSpec k) (op (CommAlgCat.of k k))

private theorem hom_toBase_eq {X : SchemeOver k} (f : X ⟶ Base) :
    f = toBasePoint X := by
  apply Over.OverMorphism.ext
  have h : (Base).hom = 𝟙 (Spec (CommRingCat.of k)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    exact Spec.map_id (CommRingCat.of k)
  change f.left = X.hom
  exact (Category.comp_id _).symm.trans ((congrArg (f.left ≫ ·) h).symm.trans (Over.w f))

@[reassoc]
private theorem comp_toBasePoint {X Y : SchemeOver k} (f : X ⟶ Y) :
    f ≫ toBasePoint Y = toBasePoint X := hom_toBase_eq _

private theorem isPullback_of_affine_fibres {H X F : SchemeOver k} (j : H ⟶ X) [Mono j]
    (f : X ⟶ F) (z : Base ⟶ F)
    (h : ∀ (R : TestAlgebra k) (a : Points X R),
      (∃ q : Points H R, q ≫ j = a) ↔ a ≫ f = toBasePoint _ ≫ z) :
    IsPullback j (toBasePoint H) f z := by
  refine IsPullback.mk' ?_ (fun _ _ _ hj _ ↦ (cancel_mono j).mp hj) ?_
  · apply hom_ext_on_affines
    intro R a
    simpa only [Category.assoc, comp_toBasePoint_assoc] using (h R (a ≫ j)).mp ⟨a, rfl⟩
  · intro S a b hab
    have hlocal (R : TestAlgebra k) (p : Points S R) :
        ∃ q : Points H R, q ≫ j = p ≫ a := by
      apply (h R (p ≫ a)).mpr
      rw [Category.assoc, hab, hom_toBase_eq b, comp_toBasePoint_assoc]
    choose q hq using hlocal
    have hq_natural {R T : TestAlgebra k} (α : R ⟶ T) (p : Points S R) :
        q T (mapPoints α p) = mapPoints α (q R p) := by
      apply (cancel_mono j).mp
      calc
        q T (mapPoints α p) ≫ j = mapPoints α p ≫ a := hq _ _
        _ = mapPoints α (p ≫ a) := Category.assoc _ _ _
        _ = mapPoints α (q R p ≫ j) := congrArg (mapPoints α) (hq R p).symm
        _ = mapPoints α (q R p) ≫ j := (Category.assoc _ _ _).symm
    let τ : pointsFunctor S ⟶ pointsFunctor H :=
      { app := fun R ↦ ↾q R
        naturality := by
          intro R T α
          apply ConcreteCategory.hom_ext
          exact hq_natural α }
    let l := (affineProbesEquiv S H).symm τ
    refine ⟨l, ?_, (hom_toBase_eq (l ≫ toBasePoint H)).trans (hom_toBase_eq b).symm⟩
    apply hom_ext_on_affines
    intro R p
    have hp : p ≫ l = q R p :=
      congrArg (fun t : pointsFunctor S ⟶ pointsFunctor H ↦ t.app R p)
        ((affineProbesEquiv S H).apply_symm_apply τ)
    rw [← Category.assoc, hp]
    exact hq R p

section GroupStabilizer

open scoped CategoryTheory.MonObj

private theorem orbit_apply {G F S : SchemeOver k} (act : G ⨯ F ⟶ F) (z : Base ⟶ F)
    (g : S ⟶ G) :
    g ≫ (prod.lift (𝟙 G) (toBasePoint G ≫ z) ≫ act) =
      prod.lift g (toBasePoint S ≫ z) ≫ act := by
  simp only [prod.comp_lift_assoc, Category.comp_id, comp_toBasePoint_assoc]

private theorem stabilizer_subgroup {G : Specs.GroupScheme k} {H F : SchemeOver k}
    (act : G.X ⨯ F ⟶ F) (z : Base ⟶ F) (j : H ⟶ G.X) [Mono j]
    (hOne : ∀ (S : SchemeOver k) (q : S ⟶ F), prod.lift (1 : S ⟶ G.X) q ≫ act = q)
    (hMul : ∀ (S : SchemeOver k) (g h : S ⟶ G.X) (q : S ⟶ F),
      prod.lift (g * h) q ≫ act = prod.lift g (prod.lift h q ≫ act) ≫ act)
    (pb : IsPullback j (toBasePoint H) (prod.lift (𝟙 G.X) (toBasePoint G.X ≫ z) ≫ act) z) :
    ∃ (H' : Specs.GroupScheme k) (i : H' ⟶ G) (e : H'.X ≅ H), i.hom.hom = e.hom ≫ j := by
  let o := prod.lift (𝟙 G.X) (toBasePoint G.X ≫ z) ≫ act
  let K (S : SchemeOver k) : Subgroup (S ⟶ G.X) :=
    { carrier := {g | g ≫ o = toBasePoint S ≫ z}
      one_mem' := (orbit_apply act z (1 : S ⟶ G.X)).trans (hOne S _)
      mul_mem' := by
        intro g h hg hh
        change g ≫ o = _ at hg
        change h ≫ o = _ at hh
        change (g * h) ≫ o = _
        rw [orbit_apply act z g] at hg
        rw [orbit_apply act z h] at hh
        rw [orbit_apply act z (g * h), hMul, hh, hg]
      inv_mem' := by
        intro g hg
        change g ≫ o = _ at hg
        change g⁻¹ ≫ o = _
        rw [orbit_apply act z g] at hg
        have h := hMul S g⁻¹ g (toBasePoint S ≫ z)
        rw [inv_mul_cancel, hOne, hg] at h
        exact (orbit_apply act z g⁻¹).trans h.symm }
  let T : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u} :=
    { obj := fun S ↦ GrpCat.of (K S.unop)
      map := fun {S U} f ↦ GrpCat.ofHom
        { toFun := fun g ↦ ⟨f.unop ≫ g.val, by
            have hg : g.val ≫ o = toBasePoint S.unop ≫ z := g.property
            change (f.unop ≫ g.val) ≫ o = _
            rw [Category.assoc, hg, comp_toBasePoint_assoc]⟩
          map_one' := Subtype.ext (MonObj.comp_one _)
          map_mul' := fun _ _ ↦ Subtype.ext (MonObj.comp_mul _ _ _) }
      map_id := by
        intro S
        apply GrpCat.ext
        intro g
        exact Subtype.ext (Category.id_comp _)
      map_comp := by
        intro S U V a b
        apply GrpCat.ext
        intro g
        exact Subtype.ext (Category.assoc _ _ _) }
  let rep : (T ⋙ forget _).RepresentableBy H :=
    { homEquiv := fun {S} ↦
        { toFun := fun p ↦ ⟨p ≫ j, by
            change (p ≫ j) ≫ o = _
            rw [Category.assoc, pb.w, comp_toBasePoint_assoc]⟩
          invFun := fun g ↦ pb.lift g.val (toBasePoint S) g.property
          left_inv := fun p ↦ (cancel_mono j).mp (pb.lift_fst _ _ _)
          right_inv := fun g ↦ Subtype.ext (pb.lift_fst _ _ _) }
      homEquiv_comp := fun f p ↦ Subtype.ext (Category.assoc f p j) }
  let inclusion : T ⟶ yonedaGrp.obj G :=
    { app := fun S ↦ GrpCat.ofHom (K S.unop).subtype
      naturality := by
        intro S U a
        apply GrpCat.ext
        intro p
        rfl }
  let := GrpObj.ofRepresentableBy H T rep
  let H' : Specs.GroupScheme k := ⟨H⟩
  let e := yonedaGrpObjIsoOfRepresentableBy H T rep
  let i : H' ⟶ G := yonedaGrpFullyFaithful.preimage (e.hom ≫ inclusion)
  refine ⟨H', i, Iso.refl _, ?_⟩
  have h := congrArg (fun α : yonedaGrp.obj H' ⟶ yonedaGrp.obj G ↦ α.app (op H) (𝟙 H))
    (yonedaGrpFullyFaithful.map_preimage (e.hom ≫ inclusion))
  change (𝟙 H) ≫ i.hom.hom = (𝟙 H) ≫ j at h
  simpa only [Category.id_comp, Iso.refl_hom] using h

end GroupStabilizer

private theorem span_coordinateSingles (R Idx : Type u) [CommRing R] [Fintype Idx]
    [DecidableEq Idx] (s : Set Idx) :
    Submodule.span R ((fun i : Idx ↦ Pi.single i (1 : R)) '' s) = coordinateSubmodule R s := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    apply mem_coordinateSubmodule.mpr
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hj hi
    simp [Pi.single_eq_of_ne hji]
  · intro x hx
    let B := Pi.basisFun R Idx
    rw [← B.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ s
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, hi, (Pi.basisFun_apply R Idx i).symm⟩
    · have hzero : B.repr x i = 0 := by simpa [B] using (mem_coordinateSubmodule.mp hx) i hi
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  {n m : ℕ} (β : Module.Basis (Fin n) k V) (ranks : Fin m → ℕ)

private abbrev BasisIndex (_k : Type u) (n : ℕ) : Type u := ULift.{u} (Fin n)

local notation "Idx" => BasisIndex k n
local notation "B" => liftedBasis β
local notation "GLgroup" => Subtype.val (StandardGroups.generalLinearGroup k Idx)
local notation "glPoints" => StandardGroups.generalLinearGroupPointsIso k Idx

omit [Module.Finite k V] in
private theorem prefixSubmodule_coordinates (R : TestAlgebra k) (d : ℕ) :
    (prefixSubmodule β R d).map (Specs.GrassmannianCharts.coordinates B R).toLinearMap =
      coordinateSubmodule R {i : Idx | i.down.val < d} := by
  rw [prefixSubmodule, Submodule.map_span, Set.image_image, ← span_coordinateSingles]
  congr 1
  have h (j : Fin n) :
      Specs.GrassmannianCharts.coordinates B R (β.baseChange R j) = Pi.single (ULift.up j) 1 := by
    funext i
    rw [show β.baseChange R j = (1 : R) ⊗ₜ[k] B (ULift.up j) from by
      rw [Module.Basis.baseChange_apply, Module.Basis.reindex_apply]; rfl, coordinates_basis]
    simp [Pi.single_apply, eq_comm]
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j⟩, hj, (h j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.down, hj, h j.down⟩

omit [Module.Finite k V] in
private theorem prefixTransport_iff (R : TestAlgebra k) (d : ℕ)
    (g : Matrix.GeneralLinearGroup Idx R) :
    (prefixSubmodule β R d).map (Specs.FlagIncidence.matrixTransport B R g).toLinearMap =
      prefixSubmodule β R d ↔
    (coordinateSubmodule R {i : Idx | i.down.val < d}).map
        (Matrix.mulVecLin (g : Matrix Idx Idx R)) =
      coordinateSubmodule R {i : Idx | i.down.val < d} := by
  let c := Specs.GrassmannianCharts.coordinates B R
  have h : c.toLinearMap.comp (Specs.FlagIncidence.matrixTransport B R g).toLinearMap =
      (Matrix.mulVecLin (g : Matrix Idx Idx R)).comp c.toLinearMap := by
    apply LinearMap.ext
    exact coordinates_transport B g
  rw [← (Submodule.map_injective_of_injective (f := c.toLinearMap) c.injective).eq_iff,
    ← Submodule.map_comp, h, Submodule.map_comp]
  exact iff_of_eq (by rw [show c = Specs.GrassmannianCharts.coordinates B R from rfl,
    prefixSubmodule_coordinates])

private def generalLinearMatrixIso : matrixScheme k Idx ≅ (GLgroup).X := Iso.refl _

private theorem generalLinear_entries (R : TestAlgebra k)
    (f : Specs.StandardGroups.GLCoordinates k Idx →ₐ[k] R) (i j : Idx) :
    ((glPoints).hom.app R ((testSpec k).map (CommAlgCat.ofHom f).op ≫
      (generalLinearMatrixIso (k := k) (n := n)).hom) : Matrix.GeneralLinearGroup Idx R).val i j =
        f (Specs.StandardGroups.universalMatrix k Idx i j) := by
  let := StandardGroups.generalLinearHopf k Idx
  let e := hopfSpecPointIso (CommHopfAlgCat.of k (Specs.StandardGroups.GLCoordinates k Idx))
  have he : e ≪≫ glPoints = Representation.convolutionIso
      (generalLinearRepresentation (k := k) (ι := Idx)) := by
    change e ≪≫ (e.symm ≪≫ _) = _
    simp
  have h := congrArg (fun c ↦ c.hom.app R (WithConv.toConv f)) he
  have hf : (e.hom.app R (WithConv.toConv f) : Points (GLgroup).X R) =
      (testSpec k).map (CommAlgCat.ofHom f).op ≫
        (generalLinearMatrixIso (k := k) (n := n)).hom := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ 𝟙 _
    rw [Category.comp_id]
  rw [← hf]
  exact congrArg (fun g : Matrix.GeneralLinearGroup Idx R ↦ g.val i j) h

private theorem coordinateInclusion_equations (R : TestAlgebra k) (g : Points (GLgroup).X R) :
    (∃ q : Points (coordinateFlagLocus k Idx (prefixCuts ranks)) R,
      q ≫ (coordinateFlagInclusion k Idx (prefixCuts ranks) ≫
        (generalLinearMatrixIso (k := k) (n := n)).hom) = g) ↔
      ∀ (a : Fin m) (i j : Idx), j.down.val < ranks a → ranks a ≤ i.down.val →
        ((glPoints).hom.app R g : Matrix.GeneralLinearGroup Idx R).val i j = 0 := by
  let e := generalLinearMatrixIso (k := k) (n := n)
  obtain ⟨a, ha⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective (g ≫ e.inv)
  let f := a.unop.hom
  have hg : (testSpec k).map (CommAlgCat.ofHom f).op ≫ e.hom = g := by
    change (testSpec k).map a ≫ e.hom = _
    rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let j := coordinateFlagInclusion k Idx (prefixCuts ranks)
  change (∃ q, q ≫ (j ≫ e.hom) = g) ↔ _
  rw [← hg]
  simp only [← Category.assoc, cancel_mono, e, generalLinear_entries]
  simpa only [prefixCuts, Set.mem_ofPred_eq, not_lt] using
    (coordinateFlagClosedLocus k Idx (prefixCuts ranks)).2 R f

omit [Module.Finite k V] in
private theorem coordinateFlag_baseChange
    (C : ∀ i : Fin m, Specs.GrassmannianCharts.ChartSystem V B (ranks i))
    (hr : ∀ i, ranks i ≤ Module.finrank k V)
    (z : Points (FlagIncidence.flagScheme B ranks C) (CommAlgCat.of k k))
    (hz : ∀ i, (productPlanes ranks B C (z ≫ FlagIncidence.flagInclusion B ranks C) i).toSubmodule =
      prefixSubmodule β (CommAlgCat.of k k) (ranks i)) (R : TestAlgebra k) (i : Fin m) :
    (productPlanes ranks B C ((toBasePoint ((testSpec k).obj (op R)) ≫ z) ≫
      FlagIncidence.flagInclusion B ranks C) i).toSubmodule =
      prefixSubmodule β R (ranks i) := by
  let jF := FlagIncidence.flagInclusion B ranks C
  have hdim : Module.finrank k V = n := by simp [Module.finrank_eq_card_basis β]
  have hn : ranks i ≤ n := (hr i).trans_eq hdim
  have hplane : productPlanes ranks B C (z ≫ jF) i = prefixPlane β hn (CommAlgCat.of k k) :=
    Module.Grassmannian.ext ((hz i).trans (prefixPlane_submodule β hn _).symm)
  let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  rw [← hom_toBase_eq ((testSpec k).map a.op), Category.assoc]
  change (productPlanes ranks B C (mapPoints a (z ≫ jF)) i).toSubmodule = _
  rw [productPlanes_naturality, hplane, prefixPlane_map, prefixPlane_submodule]

omit [Module.Finite k V] in
private theorem coordinateFlag_fixed
    (C : ∀ i : Fin m, Specs.GrassmannianCharts.ChartSystem V B (ranks i))
    (hr : ∀ i, ranks i ≤ Module.finrank k V)
    (z : Points (FlagIncidence.flagScheme B ranks C) (CommAlgCat.of k k))
    (hz : ∀ i, (productPlanes ranks B C (z ≫ FlagIncidence.flagInclusion B ranks C) i).toSubmodule =
      prefixSubmodule β (CommAlgCat.of k k) (ranks i)) (R : TestAlgebra k) (g : Points (GLgroup).X R) :
    g ≫ (prod.lift (𝟙 (GLgroup).X) (toBasePoint (GLgroup).X ≫ z) ≫
      FlagIncidence.flagAction B ranks C) =
        toBasePoint ((testSpec k).obj (op R)) ≫ z ↔
      ∀ a (i j : Idx), j.down.val < ranks a → ranks a ≤ i.down.val →
        ((glPoints).hom.app R g : Matrix.GeneralLinearGroup Idx R).val i j = 0 := by
  let jF := FlagIncidence.flagInclusion B ranks C
  let actF := FlagIncidence.flagAction B ranks C
  let zR : Points (FlagIncidence.flagScheme B ranks C) R :=
    toBasePoint ((testSpec k).obj (op R)) ≫ z
  let M : Matrix.GeneralLinearGroup Idx R := (glPoints).hom.app R g
  have hOrbit : g ≫ (prod.lift (𝟙 (GLgroup).X) (toBasePoint (GLgroup).X ≫ z) ≫ actF) =
      prod.lift g zR ≫ actF := by
    simp only [zR, prod.comp_lift_assoc, Category.comp_id, comp_toBasePoint_assoc]
  rw [hOrbit]
  have hPlanes : prod.lift g zR ≫ actF = zR ↔
      ∀ i, (prefixSubmodule β R (ranks i)).map (Specs.FlagIncidence.matrixTransport B R M).toLinearMap =
        prefixSubmodule β R (ranks i) := by
    have hImage (i : Fin m) :
        (productPlanes ranks B C ((prod.lift g zR ≫ actF) ≫ jF) i).toSubmodule =
          (prefixSubmodule β R (ranks i)).map (Specs.FlagIncidence.matrixTransport B R M).toLinearMap := by
      rw [flagAction_plane, coordinateFlag_baseChange β ranks C hr z hz R i]
    constructor
    · intro h i
      rw [← hImage, h]
      exact coordinateFlag_baseChange β ranks C hr z hz R i
    · intro h
      apply flags_eq_of_planes B ranks C
      intro i
      rw [hImage, h i, coordinateFlag_baseChange β ranks C hr z hz R i]
  change (prod.lift g zR ≫ actF = zR) ↔ _
  rw [hPlanes]
  simp_rw [prefixTransport_iff]
  simpa only [prefixCuts, Set.mem_ofPred_eq, not_lt] using
    (coordinateFlagStabilizer R Idx (prefixCuts ranks) M)

private def coordinateStabilizer
    (P : ∀ i : Fin m, Specs.PluckerEmbedding.PluckerMorphism B (ranks i))
    (hc : ∀ (i : Fin m) (R : TestAlgebra k) (p : Points (P i).charts.scheme R),
      Specs.GrassmannianCharts.IsTildePlane V B R ((P i).charts.affinePoints.hom.app R p)
        ((P i).families.subbundle _ ((P i).families.family _ p)))
    (hr : ∀ i, ranks i ≤ Module.finrank k V)
    (z : Points (FlagIncidence.flagScheme B ranks (fun i ↦ (P i).charts)) (CommAlgCat.of k k))
    (hz : ∀ i, (productPlanes ranks B (fun j ↦ (P j).charts)
      (z ≫ FlagIncidence.flagInclusion B ranks (fun j ↦ (P j).charts)) i).toSubmodule =
        prefixSubmodule β (CommAlgCat.of k k) (ranks i)) :
    CoordinateStabilizer β ranks P
      (FlagIncidence.flagPresentation B ranks (fun i ↦ (P i).charts) (fun i ↦ (P i).families) hc)
      GLgroup glPoints (FlagIncidence.intrinsicFlagAction B ranks (fun i ↦ (P i).charts)) := by
  let C := fun i : Fin m ↦ (P i).charts
  let A := FlagIncidence.intrinsicFlagAction B ranks C
  let H := coordinateFlagLocus k Idx (prefixCuts ranks)
  let e := generalLinearMatrixIso (k := k) (n := n)
  let j : H ⟶ (GLgroup).X := coordinateFlagInclusion k Idx (prefixCuts ranks) ≫ e.hom
  have hClosed : IsClosedImmersion j.left := (coordinateFlagClosedLocus k Idx (prefixCuts ranks)).1
  letI : Mono j := Over.mono_of_mono_left _
  have hPB : IsPullback j (toBasePoint H)
      (prod.lift (𝟙 (GLgroup).X) (toBasePoint (GLgroup).X ≫ z) ≫ A.onFlags) z := by
    apply isPullback_of_affine_fibres j
    intro R g
    exact (coordinateInclusion_equations ranks R g).trans (coordinateFlag_fixed β ranks C hr z hz R g).symm
  refine
    { point := z
      point_formula := hz
      matrixIso := e
      matrix_entries := generalLinear_entries
      stabilizer_pullback := hPB
      closed := hClosed
      subgroup := stabilizer_subgroup A.onFlags z j A.one A.mul hPB
      equations := coordinateInclusion_equations ranks
      full_upper_triangular := ?_ }
  intro hs R g
  rw [coordinateInclusion_equations]
  constructor
  · intro h i j hj
    obtain ⟨a, ha⟩ := hs i.down (lt_of_le_of_lt (Nat.zero_le j.down.val) hj)
    exact h a i j (by rwa [ha]) (by rw [ha])
  · intro h a i j hj hi
    exact h i j (hj.trans_le hi)

end Stabilizer

open private pluckerMorphism pluckerEquivariance from LinearAlgebraicGroups.Flag.PluckerEmbedding

private theorem pluckerClosedForOrderedIndex {k V Idx : Type u} [Field k] [AddCommGroup V]
    [Module k V] [Module.Finite k V] [Fintype Idx] [order : LinearOrder Idx]
    [dec : DecidableEq Idx] (b : Module.Basis Idx k V) (d : ℕ)
    (P : Specs.PluckerEmbedding.PluckerMorphism b d) :
    IsClosedImmersion P.morphism.left := by
  have h : dec = order.toDecidableEq := Subsingleton.elim _ _
  subst dec
  exact PluckerEmbedding.pluckerClosedImmersion k V Idx b d P

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1600 in
/-- The incidence scheme of flags, with its Plücker–Segre realization and coordinate stabilizer. -/
theorem flagSchemeGeometry : FlagSchemeGeometry.{u} := by
  intro k V _ _ _ _ n β m ranks hmono hr
  let Idx := ULift.{u} (Fin n)
  let b : Module.Basis Idx k V := liftedBasis β
  choose C F hF using fun i : Fin m ↦ GrassmannianCharts.construction k V Idx b (ranks i) (hr i)
  let P (i : Fin m) : Specs.PluckerEmbedding.PluckerMorphism b (ranks i) :=
    pluckerMorphism b (C i) (F i) (hF i)
      (ProjectiveSpaces.lineRepresentation k (Specs.PluckerEmbedding.Wedge k (ranks i) V))
      (ProjectiveSpaces.basisPointFormula k _)
      (Classical.choice (PluckerEmbedding.affineExteriorLineGeometry k V (ranks i) (hr i)))
  let hc (i : Fin m) := (P i).affineComparison
  let D := FlagIncidence.flagPresentation b ranks C F hc
  let G := (StandardGroups.generalLinearGroup k Idx).val
  let E := StandardGroups.generalLinearGroupPointsIso k Idx
  let A := FlagIncidence.intrinsicFlagAction b ranks C
  have hclosed (i : Fin m) : IsClosedImmersion (P i).morphism.left :=
    pluckerClosedForOrderedIndex b (ranks i) (P i)
  have hlocal := FlagIncidence.localFlagTransitivity b ranks C hmono.monotone hr
  obtain ⟨z, hz, _⟩ := hlocal n β
  refine ⟨P, D, G, E, A, ?_, affineFlagPoints b ranks P D,
    FlagIncidence.localFlagAdaptedBases b ranks C hmono.monotone hr, hlocal,
    ⟨projectivePresentation b ranks P E D A hclosed (fun _ ↦ rfl)⟩,
    ⟨coordinateStabilizer β ranks P hc hr z hz⟩⟩
  intro i
  rcases (GrassmannianCharts.endpoints k V Idx b) with ⟨hzero, htop⟩
  have hterminal (d : ℕ) (Q : Specs.GrassmannianCharts.ChartSystem V b d)
      (hi : d = 0 ∨ d = Module.finrank k V) : Nonempty (IsTerminal Q.scheme) := by
    rcases hi with rfl | rfl
    · exact hzero Q
    · exact htop Q
  exact ⟨hclosed i, pluckerEquivariance b E (P i), hterminal _ _⟩

end

end LinearAlgebraicGroups.FlagSchemes
