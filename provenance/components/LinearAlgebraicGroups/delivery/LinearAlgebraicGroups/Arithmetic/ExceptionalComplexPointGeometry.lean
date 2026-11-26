import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Flag.BruhatCells
import Mathlib.Analysis.Complex.Convex
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.Polynomial
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology
open LinearAlgebraicGroups.Specs hiding coordinateMap
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry

open AdelicGroups
open IntegralModels (MatrixRealization)
open Specs.ExceptionalComplexPointGeometry
open Specs.StandardGroups (GLCoordinates universalMatrix)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsSplitAdditive)
open Unipotent (Index baseChangedAlgebraicGroup)
open CartesianMonoidalCategory

open private matrixPresentation continuous_glEvaluation asMatrix_isClosedEmbedding glVal_isEmbedding
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels

universe u

set_option backward.isDefEq.respectTransparency false

private theorem coordinateMap_comp {k : Type u} [Field k] {A B C : TestAlgebra k}
    (f : (testSpec k).obj (op A) ⟶ (testSpec k).obj (op B))
    (g : (testSpec k).obj (op B) ⟶ (testSpec k).obj (op C)) :
    coordinateMap (f ≫ g) = coordinateMap g ≫ coordinateMap f := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [coordinateMap_spec, op_comp, Functor.map_comp, coordinateMap_spec, coordinateMap_spec]

/-- Pulling a coordinate back along an affine scheme morphism preserves
continuity in any family in which evaluation of all source coordinates is continuous. -/
private theorem continuous_of_coordinates {k : Type} [Field k] [Algebra k ℂ]
    {H : AffineAlgebraicGroup k} (j : MatrixRealization H)
    (A : TestAlgebra k) (f : (testSpec k).obj (op A) ⟶ H.val.X)
    {P : Type*} [TopologicalSpace P]
    (x : P → Points ((testSpec k).obj (op A)) (CommAlgCat.of k ℂ))
    (hc : ∀ a : A, Continuous (fun t => (coordinateMap (x t)).hom a)) :
    Continuous (fun t => (show PointsIn j ℂ from x t ≫ f)) := by
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr H.prop.1
  obtain ⟨b, _, hb⟩ := matrixPresentation B.unop e j
  refine ((glVal_isEmbedding.comp (asMatrix_isClosedEmbedding j ℂ).isEmbedding).isInducing
    ).continuous_iff.mpr ?_
  refine continuous_matrix fun l m => ?_
  let c := (coordinateMap (f ≫ e.inv)).hom (b.hom (universalMatrix k _ l m))
  apply (hc c).congr
  intro t
  change _ = (asMatrix j ℂ (x t ≫ f)).val l m
  rw [← glEvaluation_entry (k := k), hb ℂ, Category.assoc, coordinateMap_comp]
  rfl

theorem continuousPointMap : ContinuousPointMap := by
  intro k _ _ G H i j f
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, he⟩ := matrixPresentation A.unop e i
  have h := continuous_of_coordinates j A.unop (e.hom ≫ f.hom.hom)
    (fun x : PointsIn i ℂ => x ≫ e.inv) (by
      intro b
      obtain ⟨c, rfl⟩ := ha b
      have he' (x : PointsIn i ℂ) :
          (coordinateMap (x ≫ e.inv)).hom (a.hom c) = glEvaluation (asMatrix i ℂ x) c :=
        congrFun (congrArg DFunLike.coe (he ℂ x).symm) c
      simp_rw [he']
      exact (continuous_glEvaluation c).comp continuous_induced_dom)
  apply h.congr
  intro x
  change (x ≫ e.inv) ≫ e.hom ≫ f.hom.hom = x ≫ f.hom.hom
  simp

theorem continuousComplexifiedPointMap : ContinuousComplexifiedPointMap := by
  intro G H i j f
  obtain ⟨hG, iC, _, ei, hei, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  obtain ⟨hH, jC, _, ej, hej, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ H j
  let q := pointMap iC jC f
  refine ⟨ej.toMonoidHom.comp (q.comp ei.symm.toMonoidHom),
    ej.continuous.comp ((continuousPointMap iC jC f).comp ei.symm.continuous), ?_⟩
  intro z
  have hz : (show PointsIn i ℂ from baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ ℂ) z) =
      ei z := (Over.OverMorphism.ext (hei z)).symm
  refine (congrArg (fun x : PointsIn i ℂ =>
    (show Points H.val.X (CommAlgCat.of ℝ ℂ) from ej (q (ei.symm x))).left) hz).trans ?_
  exact (congrArg (fun x : PointsIn iC ℂ =>
    (show Points H.val.X (CommAlgCat.of ℝ ℂ) from ej (q x)).left) (ei.symm_apply_apply z)).trans
      (hej (q z))

private def pointFiberEquivSections {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : SchemeOver k} (f : X ⟶ Y) (y : Points Y (CommAlgCat.of k K)) :
    {x : Points X (CommAlgCat.of k K) // x ≫ f = y} ≃
      {s : Spec (CommRingCat.of K) ⟶ pullback f.left y.left //
        s ≫ pullback.snd f.left y.left = 𝟙 _} where
  toFun x :=
    ⟨pullback.lift x.val.left (𝟙 _) (by
        have h := congrArg (fun p : Points Y (CommAlgCat.of k K) => p.left) x.prop
        change x.val.left ≫ f.left = y.left at h
        simpa only [Category.id_comp] using h),
      pullback.lift_snd ..⟩
  invFun s := by
    let x := s.val ≫ pullback.fst f.left y.left
    have he : x ≫ f.left = y.left := by
      dsimp only [x]
      rw [Category.assoc, pullback.condition, ← Category.assoc, s.prop, Category.id_comp]
    have hx : x ≫ X.hom = ((testSpec k).obj (op (CommAlgCat.of k K))).hom := by
      rw [← Over.w f, ← Category.assoc, he, Over.w y]
    exact ⟨Over.homMk x hx, Over.OverMorphism.ext he⟩
  left_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst ..
  right_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst ..
    · exact (pullback.lift_snd ..).trans s.prop.symm

/-- A finite surjection lifts every point over an algebraically closed test field. -/
private theorem surjective_points_of_finite {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed K] {X Y : SchemeOver k} (f : X ⟶ Y)
    (hfin : IsFinite f.left) (hsurj : AlgebraicGeometry.Surjective f.left) :
    Function.Surjective (fun x : Points X (CommAlgCat.of k K) => x ≫ f) := by
  intro y
  let π : pullback f.left y.left ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
  have hpb := IsPullback.of_hasPullback f.left y.left
  have : IsFinite π := MorphismProperty.of_isPullback hpb hfin
  have hπ : AlgebraicGeometry.Surjective π := MorphismProperty.of_isPullback hpb hsurj
  have hne : (Set.univ : Set (pullback f.left y.left : Scheme)).Nonempty :=
    ⟨(hπ.surj (IsLocalRing.closedPoint K)).choose, Set.mem_univ _⟩
  have : JacobsonSpace (pullback f.left y.left : Scheme) :=
    LocallyOfFiniteType.jacobsonSpace π
  obtain ⟨a, _, ha⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  let x := (pointFiberEquivSections f y).symm
    ⟨pointOfClosedPoint π a ha, pointOfClosedPoint_comp π a ha⟩
  exact ⟨x.val, x.prop⟩

private theorem finite_points_of_finite {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOver k) (hfin : IsFinite X.hom) :
    Finite (Points X (CommAlgCat.of k K)) := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨A, ⟨e⟩⟩ := (AlgebraicGeometry.essImage_algSpec (G := X)).mpr ‹IsAffine X.left›
  have he : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hA : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A.unop))) := by
    change IsFinite ((testSpec k).obj A).hom
    rw [← Over.w e.hom]
    infer_instance
  have : Module.Finite k A.unop :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hA)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let eval (x : Points X (CommAlgCat.of k K)) : A.unop →ₐ[k] K :=
    ((ff.preimage (x ≫ e.inv)).unop).hom
  apply Finite.of_injective eval
  intro x y h
  have hs : ff.preimage (x ≫ e.inv) = ff.preimage (y ≫ e.inv) := by
    apply Quiver.Hom.unop_inj
    exact CommAlgCat.hom_ext h
  apply (cancel_mono e.inv).mp
  rw [← ff.map_preimage (x ≫ e.inv), ← ff.map_preimage (y ≫ e.inv), hs]

/-- Each geometric point fiber of a finite morphism is finite on actual points. -/
private theorem finite_pointFiber_of_finite {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : SchemeOver k} (f : X ⟶ Y) (hfin : IsFinite f.left)
    (y : Points Y (CommAlgCat.of k K)) :
    Finite {x : Points X (CommAlgCat.of k K) // x ≫ f = y} := by
  let π : pullback f.left y.left ⟶ Spec (CommRingCat.of K) := pullback.snd _ _
  have hπ : IsFinite π := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hfin
  have : Finite (Points (Over.mk π) (CommAlgCat.of K K)) := finite_points_of_finite _ hπ
  let g (x : {x : Points X (CommAlgCat.of k K) // x ≫ f = y}) :
      Points (Over.mk π) (CommAlgCat.of K K) :=
    Over.homMk ((pointFiberEquivSections f y) x).val (by
      simpa using ((pointFiberEquivSections f y) x).prop)
  apply Finite.of_injective g
  intro x₁ x₂ hx
  apply (pointFiberEquivSections f y).injective
  exact Subtype.ext (congrArg Over.Hom.left hx)


private theorem glLocallyCompact (n : ℕ) : LocallyCompactSpace (Matrix.GeneralLinearGroup (Index.{0} n) ℂ) := by
  have h : IsEmbedding (Units.val : Matrix.GeneralLinearGroup (Index.{0} n) ℂ → _) :=
    glVal_isEmbedding
  have ho : IsOpen (Set.range (Units.val : Matrix.GeneralLinearGroup (Index.{0} n) ℂ → _)) := by
    change IsOpen {M : Matrix (Index.{0} n) (Index.{0} n) ℂ | IsUnit M}
    simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact isOpen_ne_fun continuous_id.matrix_det continuous_const
  letI : LocallyCompactSpace (Matrix (Index.{0} n) (Index.{0} n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Index.{0} n → Index.{0} n → ℂ))
  exact (show IsOpenEmbedding (Units.val : Matrix.GeneralLinearGroup (Index.{0} n) ℂ → _) from
    ⟨h, ho⟩).locallyCompactSpace

private theorem glSigmaCompact (n : ℕ) : SigmaCompactSpace (Matrix.GeneralLinearGroup (Index.{0} n) ℂ) := by
  letI := glLocallyCompact n
  have h : IsEmbedding (Units.val : Matrix.GeneralLinearGroup (Index.{0} n) ℂ → _) :=
    glVal_isEmbedding
  letI : SecondCountableTopology (Matrix (Index.{0} n) (Index.{0} n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Index.{0} n → Index.{0} n → ℂ))
  letI := h.secondCountableTopology
  infer_instance

theorem finiteSurjectiveCovering : FiniteSurjectiveCovering := by
  intro G H i j f hf hs
  let p := pointMap i j f
  have hp : Continuous p := continuousPointMap i j f
  have hsurj : Function.Surjective p := surjective_points_of_finite f.hom.hom hf hs
  letI : Finite p.ker := finite_pointFiber_of_finite (K := ℂ) f.hom.hom hf (1 : PointsIn j ℂ)
  letI : T2Space (PointsIn i ℂ) := (asMatrix_isClosedEmbedding i ℂ).isEmbedding.t2Space
  letI : T2Space (PointsIn j ℂ) := (asMatrix_isClosedEmbedding j ℂ).isEmbedding.t2Space
  letI := glSigmaCompact (n := i.size)
  letI := glLocallyCompact (n := j.size)
  letI : SigmaCompactSpace (PointsIn i ℂ) := (asMatrix_isClosedEmbedding i ℂ).sigmaCompactSpace
  letI : LocallyCompactSpace (PointsIn j ℂ) := (asMatrix_isClosedEmbedding j ℂ).locallyCompactSpace
  have hq : IsQuotientMap p := (p.isOpenMap_of_sigmaCompact hsurj hp).isQuotientMap hp hsurj
  exact ⟨hp, hsurj, ‹Finite p.ker›,
    (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (Set.toFinite (p.ker : Set (PointsIn i ℂ))).isDiscrete).isCoveringMap⟩


theorem centralIsogenyCovering : CentralIsogenyCovering := by
  intro G H i j f hf
  exact finiteSurjectiveCovering i j f hf.1 hf.2.2.1

section LineImages

open private coordinateMap_of_map from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private exponentEvaluation exponentsEquiv from LinearAlgebraicGroups.Affine.StandardGroups

/-- Evaluation in the affine presentation gives a continuous parametrization of
the whole image when the coordinate homomorphisms are parametrized continuously. -/
private theorem pathConnected_of_evaluations {H : AffineAlgebraicGroup ℂ}
    (j : MatrixRealization H) (A : TestAlgebra ℂ)
    (f : (testSpec ℂ).obj (op A) ⟶ H.val.X) {P : Type*} [TopologicalSpace P]
    [PathConnectedSpace P] (v : P → (A →ₐ[ℂ] ℂ)) (hs : Function.Surjective v)
    (hc : ∀ a : A, Continuous (fun t => v t a)) :
    IsPathConnected (Set.range (fun z : Points ((testSpec ℂ).obj (op A)) (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn j ℂ from z ≫ f))) := by
  let p (t : P) : Points ((testSpec ℂ).obj (op A)) (CommAlgCat.of ℂ ℂ) :=
    (testSpec ℂ).map (CommAlgCat.ofHom (v t)).op
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨t, ht⟩ := hs (coordinateMap z).hom
    refine ⟨t, ?_⟩
    change (testSpec ℂ).map (CommAlgCat.ofHom (v t)).op = z
    rw [show CommAlgCat.ofHom (v t) = coordinateMap z from CommAlgCat.hom_ext ht,
      coordinateMap_spec]
  have h := continuous_of_coordinates j A f p (fun a => by
    simp only [p, coordinateMap_of_map]
    exact hc a)
  let F := fun z : Points ((testSpec ℂ).obj (op A)) (CommAlgCat.of ℂ ℂ) =>
    (show PointsIn j ℂ from z ≫ f)
  have hr : IsPathConnected (Set.range (F ∘ p)) := isPathConnected_range h
  rwa [hp.range_comp F] at hr

private theorem pathConnected_additiveImage {H : AffineAlgebraicGroup ℂ}
    (j : MatrixRealization H) {S : GroupScheme ℂ} (f : S ⟶ H.val)
    (h : IsSplitAdditive S) :
    IsPathConnected (Set.range (fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn j ℂ from z ≫ f.hom.hom))) := by
  obtain ⟨ops, _, _, _, ⟨e⟩⟩ := h
  letI := ops.hopf
  let A := CommAlgCat.of ℂ (Polynomial ℂ)
  let g : (testSpec ℂ).obj (op A) ⟶ H.val.X := e.inv.hom.hom ≫ f.hom.hom
  have hg := pathConnected_of_evaluations j A g (Polynomial.aeval (R := ℂ) (A := ℂ))
    (Polynomial.aevalEquiv (R := ℂ) (A := ℂ)).surjective (fun a => a.continuous_aeval)
  let E := (Grp.forget (SchemeOver ℂ)).mapIso e
  let p := fun z : Points ((testSpec ℂ).obj (op A)) (CommAlgCat.of ℂ ℂ) => z ≫ E.inv
  have he : Function.Surjective p := by
    intro z
    refine ⟨z ≫ E.hom, ?_⟩
    change (z ≫ E.hom) ≫ E.inv = z
    rw [Category.assoc, E.hom_inv_id, Category.comp_id]
  let F := fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
    (show PointsIn j ℂ from z ≫ f.hom.hom)
  have hr : Set.range (F ∘ p) = Set.range (fun z : Points ((testSpec ℂ).obj (op A))
      (CommAlgCat.of ℂ ℂ) => (show PointsIn j ℂ from z ≫ g)) :=
    congrArg Set.range (funext fun z => Category.assoc z E.inv f.hom.hom)
  rwa [← he.range_comp F, hr]

private theorem continuous_laurentEvaluation {I : Type} [Fintype I] [DecidableEq I]
    (a : Specs.StandardGroups.LaurentPowerCoordinates ℂ I) :
    Continuous (fun v : I → ℂˣ =>
      AddMonoidAlgebra.lift ℂ ℂ (I → ℤ)
        ((Units.coeHom ℂ).comp (exponentEvaluation v)) a) := by
  classical
  simp only [AddMonoidAlgebra.lift_apply', RingHom.id_apply, Algebra.algebraMap_self]
  apply continuous_finsetSum
  intro m _
  apply continuous_const.mul
  exact Units.continuous_val.comp
    (continuous_finsetProd Finset.univ (fun i _ => (continuous_apply i).zpow (m i)))

private theorem pathConnected_torusImage {H : AffineAlgebraicGroup ℂ}
    (j : MatrixRealization H) {S : GroupScheme ℂ} (f : S ⟶ H.val)
    (h : IsSplitTorus S) :
    IsPathConnected (Set.range (fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn j ℂ from z ≫ f.hom.hom))) := by
  obtain ⟨r, ⟨e⟩⟩ := h
  let I := ULift.{0} (Fin r)
  let A := CommAlgCat.of ℂ (Specs.StandardGroups.LaurentPowerCoordinates ℂ I)
  let g : (testSpec ℂ).obj (op A) ⟶ H.val.X := e.inv.hom.hom ≫ f.hom.hom
  let v : (I → ℂˣ) ≃ (A →ₐ[ℂ] ℂ) :=
    (show (Multiplicative (I → ℤ) →* ℂˣ) ≃* (I → ℂˣ) from
      exponentsEquiv ℂ).symm.toEquiv.trans
      (MonoidHom.toHomUnitsMulEquiv (G := Multiplicative (I → ℤ)) (M := ℂ)).symm.toEquiv |>.trans
        (AddMonoidAlgebra.lift ℂ ℂ (I → ℤ))
  have hg := pathConnected_of_evaluations j A g v v.surjective continuous_laurentEvaluation
  let E := (Grp.forget (SchemeOver ℂ)).mapIso e
  let p := fun z : Points ((testSpec ℂ).obj (op A)) (CommAlgCat.of ℂ ℂ) => z ≫ E.inv
  have he : Function.Surjective p := by
    intro z
    refine ⟨z ≫ E.hom, ?_⟩
    change (z ≫ E.hom) ≫ E.inv = z
    rw [Category.assoc, E.hom_inv_id, Category.comp_id]
  let F := fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
    (show PointsIn j ℂ from z ≫ f.hom.hom)
  have hr : Set.range (F ∘ p) = Set.range (fun z : Points ((testSpec ℂ).obj (op A))
      (CommAlgCat.of ℂ ℂ) => (show PointsIn j ℂ from z ≫ g)) :=
    congrArg Set.range (funext fun z => Category.assoc z E.inv f.hom.hom)
  rwa [← he.range_comp F, hr]

theorem pathConnectedLineImages : PathConnectedLineImages := by
  intro H j S f h
  exact h.elim (pathConnected_torusImage j f) (pathConnected_additiveImage j f)

theorem pathConnectedComplexifiedLineImages : PathConnectedComplexifiedLineImages := by
  intro H j S f h
  obtain ⟨hH, jC, _, e, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ H j
  have hp := (pathConnectedLineImages jC f h).image e.continuous
  rw [← Set.range_comp] at hp
  have heq (z : Points S.X (CommAlgCat.of ℂ ℂ)) :
      e (z ≫ f.hom.hom) = (show PointsIn j ℂ from
        baseChangePoint ℝ ℂ H.val.X (CommAlgCat.of ℂ ℂ) (z ≫ f.hom.hom)) :=
    Over.OverMorphism.ext (he (z ≫ f.hom.hom))
  exact (congrArg IsPathConnected (congrArg Set.range (funext heq))).mp hp

end LineImages

section ConnectedComplexGroups

open AbstractPairing (Root)
open OrderedRootProducts (RootSubgroupFamily rootProduct rootCellMap)
open CocharacterDynamics (oppositeCocharacter)
open BorelsAndChambers (positiveRoots)
open private groundPointIso subgroup_eq_top_of_denseOpen
  from LinearAlgebraicGroups.Flag.BruhatCells
open private existsEnumeration from LinearAlgebraicGroups.Flag.OpenCell
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private split_of_torus from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private exists_regular_cocharacter from LinearAlgebraicGroups.RootData.BorelsAndChambers

private def terminalPointMap (G : AffineAlgebraicGroup ℂ) (i : MatrixRealization G) :
    (𝟙_ (SchemeOver ℂ) ⟶ G.val.X) →* PointsIn i ℂ where
  toFun g := (groundPointIso ℂ).inv ≫ g
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private def terminalPathSubgroup (G : AffineAlgebraicGroup ℂ) (i : MatrixRealization G) :
    Subgroup (𝟙_ (SchemeOver ℂ) ⟶ G.val.X) :=
  (Subgroup.pathComponentOne (PointsIn i ℂ)).comap (terminalPointMap G i)

private theorem terminalPoint_mem_pathSubgroup {G : AffineAlgebraicGroup ℂ} (i : MatrixRealization G)
    {S : GroupScheme ℂ} (f : S ⟶ G.val) (h : IsSplitTorus S ∨ IsSplitAdditive S)
    (x : 𝟙_ (SchemeOver ℂ) ⟶ S.X) :
    x ≫ f.hom.hom ∈ terminalPathSubgroup G i := by
  have hp := pathConnectedLineImages i f h
  let y : Points S.X (CommAlgCat.of ℂ ℂ) := (groundPointIso ℂ).inv ≫ x
  change Joined (1 : PointsIn i ℂ) (terminalPointMap G i (x ≫ f.hom.hom))
  have h1 : (1 : PointsIn i ℂ) ∈ Set.range (fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn i ℂ from z ≫ f.hom.hom)) :=
    ⟨1, map_one (((groupPointsFunctor ℂ).map f).app (CommAlgCat.of ℂ ℂ)).hom⟩
  exact (hp.joinedIn _ h1 _ ⟨y, Category.assoc ..⟩).joined

private theorem rootProduct_mem_pathSubgroup {G : AffineAlgebraicGroup ℂ} (i : MatrixRealization G)
    {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) (l : List (Root T))
    (p : 𝟙_ (SchemeOver ℂ) ⟶
      OrderedRootProducts.product (fun α => (U α).val.group.X) l) :
    p ≫ rootProduct U l ∈ terminalPathSubgroup G i := by
  induction l with
  | nil =>
    rw [rootProduct, MonObj.comp_one]
    exact (terminalPathSubgroup G i).one_mem
  | cons α l ih =>
    rw [rootProduct, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    exact (terminalPathSubgroup G i).mul_mem
      (terminalPoint_mem_pathSubgroup i (U α).val.inclusion (Or.inr (U α).property.2.1) _)
      (ih _)

private def rootProductIdentity {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) :
    (l : List (Root T)) →
      (𝟙_ (SchemeOver ℂ) ⟶ OrderedRootProducts.product (fun α => (U α).val.group.X) l)
  | [] => 𝟙 _
  | _ :: l => CartesianMonoidalCategory.lift 1 (rootProductIdentity U l)

private theorem rootCell_nonempty_range {G : AffineAlgebraicGroup ℂ} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) (ln lp : List (Root T)) :
    (Set.range (rootCellMap T U ln lp).left).Nonempty := by
  let p : 𝟙_ (SchemeOver ℂ) ⟶ _ :=
    CartesianMonoidalCategory.lift (rootProductIdentity U ln)
      (CartesianMonoidalCategory.lift (1 : 𝟙_ (SchemeOver ℂ) ⟶ T.group.X)
        (rootProductIdentity U lp))
  exact ⟨_, p.left (IsLocalRing.closedPoint ℂ), rfl⟩

/-- The usual root product cell is dense, since it is nonempty and open in
the irreducible underlying scheme of the connected reductive group. -/
private theorem exists_denseRootCell (G : AffineAlgebraicGroup ℂ) (hG : IsReductive G) :
    ∃ (T : ClosedSubgroup G.val) (U : RootSubgroupFamily T) (ln lp : List (Root T)),
      IsSplitTorus T.group ∧ IsOpenImmersion (rootCellMap T U ln lp).left ∧
      DenseRange (rootCellMap T U ln lp).left := by
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  letI := hG.2.1
  letI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  letI : IrreducibleSpace G.val.X.left := irreducible_of_geometricallyConnected G.val
  obtain ⟨T, htorus, hmax⟩ := LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
    G hG.1 ‹ConnectedSpace G.val.X.left›
  have hT : IsSplitTorus T.group :=
    split_of_torus (D := Unipotent.closedSubgroupAlgebraicGroup T)
      ((isTorus_iff_coordinates _).mp htorus)
  obtain ⟨c, hc⟩ := exists_regular_cocharacter G T hT
  obtain ⟨hfin, ⟨U⟩, _⟩ := LinearAlgebraicGroups.RootData.OrderedRootProducts.contractingProduct
    G hG T hT hmax
  letI : Finite (Root T) := hfin.to_subtype
  obtain ⟨ln, hn⟩ := existsEnumeration (positiveRoots T (oppositeCocharacter c))
  obtain ⟨lp, hp⟩ := existsEnumeration (positiveRoots T c)
  let m := rootCellMap T U ln lp
  letI : IsOpenImmersion m.left :=
    LinearAlgebraicGroups.RootData.OrderedRootProducts.regularRootCell G hG T hT hmax c hc U ln lp hn hp
  exact ⟨T, U, ln, lp, hT, ‹IsOpenImmersion m.left›,
    (IsOpenImmersion.isOpen_range m.left).dense (rootCell_nonempty_range U ln lp)⟩

private theorem rootCell_mem_pathSubgroup {G : AffineAlgebraicGroup ℂ} (i : MatrixRealization G)
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group)
    (U : RootSubgroupFamily T) (ln lp : List (Root T))
    (p : 𝟙_ (SchemeOver ℂ) ⟶ _) :
    p ≫ rootCellMap T U ln lp ∈ terminalPathSubgroup G i := by
  let Xn := OrderedRootProducts.product (fun α => (U α).val.group.X) ln
  let Xp := OrderedRootProducts.product (fun α => (U α).val.group.X) lp
  let Y : SchemeOver ℂ := T.group.X ⊗ Xp
  let n : 𝟙_ (SchemeOver ℂ) ⟶ Xn := p ≫ fst Xn Y
  let y : 𝟙_ (SchemeOver ℂ) ⟶ Y := p ≫ snd Xn Y
  let t : 𝟙_ (SchemeOver ℂ) ⟶ T.group.X := y ≫ fst T.group.X Xp
  let x : 𝟙_ (SchemeOver ℂ) ⟶ Xp := y ≫ snd T.group.X Xp
  have he : p ≫ rootCellMap T U ln lp =
      (n ≫ rootProduct U ln) * ((t ≫ T.inclusion.hom.hom) * (x ≫ rootProduct U lp)) := by
    change p ≫ ((fst Xn Y ≫ rootProduct U ln) *
      (snd Xn Y ≫ ((fst T.group.X Xp ≫ T.inclusion.hom.hom) *
        (snd T.group.X Xp ≫ rootProduct U lp)))) = _
    rw [MonObj.comp_mul, ← Category.assoc p (fst Xn Y), ← Category.assoc p (snd Xn Y)]
    change (n ≫ rootProduct U ln) *
      (y ≫ ((fst T.group.X Xp ≫ T.inclusion.hom.hom) *
        (snd T.group.X Xp ≫ rootProduct U lp))) = _
    rw [MonObj.comp_mul, ← Category.assoc y (fst T.group.X Xp),
      ← Category.assoc y (snd T.group.X Xp)]
  rw [he]
  exact (terminalPathSubgroup G i).mul_mem (rootProduct_mem_pathSubgroup i U ln n)
    ((terminalPathSubgroup G i).mul_mem
      (terminalPoint_mem_pathSubgroup i T.inclusion (Or.inl hT) t)
      (rootProduct_mem_pathSubgroup i U lp x))

private theorem terminalPointMap_surjective (G : AffineAlgebraicGroup ℂ)
    (i : MatrixRealization G) : Function.Surjective (terminalPointMap G i) := by
  intro x
  refine ⟨(groundPointIso ℂ).hom ≫ x, ?_⟩
  change (groundPointIso ℂ).inv ≫ (groundPointIso ℂ).hom ≫ x = x
  exact Iso.inv_hom_id_assoc _ _

private theorem pathConnectedSpace_of_comap_eq_top {M X : Type*} [Group M] [Group X]
    [TopologicalSpace X] [IsTopologicalGroup X]
    (p : M →* X) (hp : Function.Surjective p)
    (h : (Subgroup.pathComponentOne X).comap p = ⊤) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_eq.mpr
  refine ⟨1, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨a, rfl⟩ := hp x
  change a ∈ (Subgroup.pathComponentOne X).comap p
  rw [h]
  exact Subgroup.mem_top _

private theorem terminalPathSubgroup_eq_top (G : AffineAlgebraicGroup ℂ)
    (i : MatrixRealization G) (hG : IsReductive G) : terminalPathSubgroup G i = ⊤ := by
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  obtain ⟨T, U, ln, lp, hT, hOpen, hDense⟩ := exists_denseRootCell G hG
  letI := hOpen
  exact subgroup_eq_top_of_denseOpen G.val (rootCellMap T U ln lp) hDense
    (terminalPathSubgroup G i) (rootCell_mem_pathSubgroup i hT U ln lp)

theorem complexPointsPathConnected : ComplexPointsPathConnected := by
  intro G i hG
  exact pathConnectedSpace_of_comap_eq_top (terminalPointMap G i)
    (terminalPointMap_surjective G i) (terminalPathSubgroup_eq_top G i hG)

theorem realGroupComplexPointsPathConnected : RealGroupComplexPointsPathConnected := by
  intro G i h
  obtain ⟨hA, iC, _, e, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison ℝ ℂ G i
  letI : PathConnectedSpace (PointsIn iC ℂ) := complexPointsPathConnected ⟨_, hA⟩ iC h
  exact e.surjective.pathConnectedSpace e.continuous

theorem reductiveRealGroupComplexPointsPathConnected :
    ReductiveRealGroupComplexPointsPathConnected := by
  intro G i h
  exact realGroupComplexPointsPathConnected G i
    ((Reductive.RadicalBaseChange.reductiveFieldExtension G h.1 h.2.1).mpr h)

end ConnectedComplexGroups

end LinearAlgebraicGroups.Arithmetic.ExceptionalComplexPointGeometry
