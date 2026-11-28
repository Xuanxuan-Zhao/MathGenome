import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Contraction

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
namespace RepTheorySurvey.Geometric.ConvolutionSurface

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints testSpec)
open LinearAlgebraicGroups.GrassmannianCharts (hom_ext_on_affines)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs
open ConvolutionSurfaceSpecs
open scoped TensorProduct
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Pivot chartScheme chartAlgebra Inside Outside coordinates pivotProjection IsPivot graphInclusion graphColumns matrixOfPoint)

open private planeMap_eq_span tensorExtension tensorExtension_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts

open private windowClass windowClass_surjective windowCoordinates_class windowClass_mem
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinates

set_option linter.unusedVariables false in
theorem surfaceIdentification_conditional
    (_minusculeOrbit : MinusculeOrbit)
    (_minusculeProjective : MinusculeProjective)
    (_smallSchubertSchemes : SmallSchubertSchemes)
    (_twoStepOrbits : TwoStepOrbits)
    (_twoStepStableModel : TwoStepStableModel)
    (firstLatticeQuotient : FirstLatticeQuotient)
    (_flagJetAction : FlagJetAction)
    (latticeIncidence : LatticeIncidence)
    (projectiveBundle : ProjectiveBundle)
    (surfaceGeometry : SurfaceGeometry)
    (twistedFlags : TwistedFlags) : SurfaceIdentification :=
  ⟨twistedFlags, latticeIncidence, firstLatticeQuotient, projectiveBundle, surfaceGeometry⟩

private theorem scalarLatticeCoordinates (x : Fin 2 → O) :
    shiftedInclusion 2 0 x ∈ scalarPoint.val ↔ (∀ i, PowerSeries.coeff 0 (x i) = 0) := by
  have hs (y : Fin 2 → O) := shiftedInclusion_add_nat 2 (0 : ℤ) 1 y
  simp only [Nat.cast_one, zero_add, pow_one] at hs
  rw [scalarLattice_val]
  constructor
  · rintro ⟨y, hy⟩ i
    rw [hs] at hy
    rw [← (shiftedInclusion_injective 2 0 hy), Pi.smul_apply, smul_eq_mul]
    simp [t, PowerSeries.coeff_zero_eq_constantCoeff]
  · intro hx
    have hd (i : Fin 2) : t ∣ x i :=
      PowerSeries.X_dvd_iff.mpr (by simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hx i)
    choose y hy using hd
    refine ⟨y, ?_⟩
    rw [hs]
    congr 1
    funext i
    exact (hy i).symm

private theorem scalarPlane :
    (latticeSubspace 0 2 scalarPoint).map twoStepCoordinates.toLinearMap =
      (⊥ : Submodule ℂ V).prod ⊤ := by
  have hlo : (scalarLattice 2 (2 : ℤ)).val ≤ scalarPoint.val := by
    exact scalarLattice_add_nat_le 2 1 1
  ext z
  obtain ⟨x, hx⟩ := windowClass_surjective 2 0 2 (twoStepCoordinates.symm z)
  have hz : twoStepCoordinates (windowClass 2 0 2 x) = z := by
    rw [hx, LinearEquiv.apply_symm_apply]
  rw [← hz, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, windowClass_mem scalarPoint (show (scalarLattice 2 (0 + (2 : ℕ))).val ≤ scalarPoint.val from hlo)]
  rw [scalarLatticeCoordinates]
  simp only [Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top, and_true]
  exact ⟨fun h ↦ funext fun i ↦ (windowCoordinates_class 2 0 2 x i 0).trans (h i),
    fun h i ↦ (windowCoordinates_class 2 0 2 x i 0).symm.trans (congrFun h i)⟩

private theorem complexPoint_comp (Y : SchemeOver ℂ)
    (x : Points Y complexAlgebra) : x.left ≫ Y.hom = 𝟙 _ := by
  rw [Over.w x, AlgebraicGeometry.algSpec_obj_hom]
  change Spec.map (𝟙 (CommRingCat.of ℂ)) = _
  exact AlgebraicGeometry.Spec.map_id _

private theorem scalarTerminalPoint_exists :
    ∃ x : Points twoStepScheme complexAlgebra, ScalarTerminalPoint x := by
  let P := (⊥ : Submodule ℂ V).prod (⊤ : Submodule ℂ V)
  have hd : Module.finrank ℂ P = 2 := by
    rw [(Submodule.prodEquiv (⊥ : Submodule ℂ V) (⊤ : Submodule ℂ V)).finrank_eq,
      Module.finrank_prod, finrank_bot, finrank_top, zero_add]
    simp [V]
  let p := subspacePoint twoStepBasis twoStepRank P hd
  have hp : grassmannianSubspace twoStepBasis twoStepRank p = P :=
    subspacePoint_subspace _ _ _ _
  have hstable : StablePlane twoStepBasis twoStepRank shift p := by
    rw [StablePlane, hp]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨rfl, Submodule.mem_top⟩
  let e := LatticeModels.stableSchemePoints twoStepBasis twoStepRank shift
  let x := e.symm ⟨p, hstable⟩
  have he : x ≫ twoStepSchemeInGrassmannian = p :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p, hstable⟩)
  have hx : secondPlane x = P := by
    change grassmannianSubspace twoStepBasis twoStepRank (x ≫ twoStepSchemeInGrassmannian) = P
    rw [he, hp]
  have : Subsingleton complexPointScheme.left := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  exact ⟨x, isClosedImmersion_of_comp_eq_id _ _ (complexPoint_comp _ x),
    hx.trans scalarPlane.symm, hx⟩

private def grassmannianCover {W ι : Type} [AddCommGroup W] [Module ℂ W]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ W) : (grassmannianCharts b hd).scheme.left.OpenCover :=
  let X := grassmannianCharts b hd
  Scheme.Cover.mkOfCovers (Pivot ι d)
    (fun I ↦ (chartScheme (k := ℂ) I).left) (fun I ↦ (X.chart I).left)
    X.cover X.openChart

private def projectiveCover : projectiveScheme.left.OpenCover :=
  grassmannianCover projectiveBasis projectiveRank

private theorem projectiveReduced : IsReduced projectiveScheme.left := by
  have (I : projectiveCover.I₀) : IsReduced (projectiveCover.X I) := by
    change IsReduced (Spec (CommRingCat.of (chartAlgebra (k := ℂ) I)))
    infer_instance
  exact IsReduced.of_openCover _ projectiveCover

private theorem grassmannianLocallyFiniteType {W ι : Type} [AddCommGroup W] [Module ℂ W]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ W) :
    LocallyOfFiniteType (grassmannianCharts b hd).scheme.hom := by
  let C := grassmannianCover b hd
  have (I : C.I₀) : IsAffine (C.X I) := by
    change IsAffine (Spec (CommRingCat.of (chartAlgebra (k := ℂ) I)))
    infer_instance
  refine HasRingHomProperty.of_source_openCover (P := @LocallyOfFiniteType)
    C (fun I ↦ ?_)
  change Pivot ι d at I
  let i := (grassmannianCharts b hd).chart I
  change (i.left ≫ (grassmannianCharts b hd).scheme.hom).appTop.hom.FiniteType
  rw [Over.w i]
  let f := CommRingCat.ofHom (algebraMap ℂ (chartAlgebra (k := ℂ) I))
  change (Spec.map f).appTop.hom.FiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := Spec.map f)).mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance))

private theorem projectiveLocallyFiniteType : LocallyOfFiniteType projectiveScheme.hom :=
  grassmannianLocallyFiniteType projectiveBasis projectiveRank

private theorem twoStepLocallyFiniteType : LocallyOfFiniteType twoStepScheme.hom := by
  have : LocallyOfFiniteType (grassmannianCharts twoStepBasis twoStepRank).scheme.hom :=
    grassmannianLocallyFiniteType twoStepBasis twoStepRank
  have : IsClosedImmersion twoStepSchemeInGrassmannian.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  rw [← Over.w twoStepSchemeInGrassmannian]
  infer_instance

private theorem complexPointStructure :
    complexPointScheme.hom = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  rw [AlgebraicGeometry.algSpec_obj_hom]
  change Spec.map (𝟙 (CommRingCat.of ℂ)) = _
  exact AlgebraicGeometry.Spec.map_id _

private theorem toComplexPoint_unique (Y : SchemeOver ℂ) (p : Y ⟶ complexPointScheme) :
    p = toComplexPoint Y := by
  apply Over.OverMorphism.ext
  change p.left = Y.hom
  have h : p.left ≫ complexPointScheme.hom = Y.hom := Over.w p
  rw [complexPointStructure] at h
  exact (Category.comp_id p.left).symm.trans h

private theorem secondPlane_injective : Function.Injective secondPlane := by
  intro p q hpq
  have h : IsClosedImmersion twoStepSchemeInGrassmannian.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  apply Over.OverMorphism.ext
  apply (cancel_mono twoStepSchemeInGrassmannian.left).mp
  exact congrArg (fun r ↦ r.left)
    (grassmannianSubspace_injective twoStepBasis twoStepRank hpq)

private theorem firstPlane_finrank (p : ProjectivePoints) : Module.finrank ℂ (firstPlane p) = 1 :=
  grassmannianSubspace_finrank projectiveBasis projectiveRank p

private theorem complexPoints_dense (X : SchemeOver ℂ) [LocallyOfFiniteType X.hom] :
    Dense (Set.range (pointLocation : Points X complexAlgebra → X.left)) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [dense_iff_closure_eq, ← closure_closedPoints (X := X.left)]
  apply le_antisymm
  · rw [closure_closedPoints]
    exact Set.subset_univ _
  · apply closure_mono
    intro z hz
    let p : Points X complexAlgebra :=
      Over.homMk (pointOfClosedPoint X.hom z hz)
        ((pointOfClosedPoint_comp X.hom z hz).trans complexPointStructure.symm)
    exact ⟨p, pointOfClosedPoint_apply X.hom z hz _⟩

private theorem liftIntoReducedClosure {X Y : SchemeOver ℂ} (j : X ⟶ Y)
    (S : Set (Points Y complexAlgebra)) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (hj : ∀ p : Points X complexAlgebra, p ≫ j ∈ S) :
    ∃ s : X ⟶ reducedClosureScheme Y S, s ≫ reducedClosureInclusion Y S = j := by
  let i := reducedClosureInclusion Y S
  have hi : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal Y S).subschemeι
    infer_instance
  have hImage : j.left '' (Set.univ : Set X.left) ⊆ closure (pointLocation '' S) := by
    rw [← (complexPoints_dense X).closure_eq]
    apply Set.image_subset_iff.mpr
    apply closure_minimal _ (isClosed_closure.preimage j.left.continuous)
    rintro _ ⟨p, rfl⟩
    exact subset_closure ⟨p ≫ j, hj p, pointLocation_comp p j⟩
  have hk : i.left.ker ≤ j.left.ker := by
    rw [show i.left.ker = reducedClosureIdeal Y S from Scheme.IdealSheafData.ker_subschemeι _]
    have hmap := Scheme.IdealSheafData.map_vanishingIdeal j.left (⊤ : Closeds X.left)
    rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot] at hmap
    rw [hmap]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.mpr hImage)
  let l := IsClosedImmersion.lift i.left j.left hk
  have hl : l ≫ i.left = j.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w i, ← Category.assoc, hl, Over.w j]

private theorem exceptionalSection_square (x : Points twoStepScheme complexAlgebra)
    (hx : ScalarTerminalPoint x) :
    ∃ s : projectiveScheme ⟶ incidenceScheme, s ≫ firstProjection = 𝟙 _ ∧
      s ≫ terminalProjection = toComplexPoint projectiveScheme ≫ x ∧
      IsPullback s (toComplexPoint projectiveScheme) terminalProjection x ∧
      IsClosedImmersion s.left := by
  let j : projectiveScheme ⟶ IncidenceAmbient :=
    prod.lift (𝟙 projectiveScheme) (toComplexPoint projectiveScheme ≫ x)
  have : IsReduced projectiveScheme.left := projectiveReduced
  have : LocallyOfFiniteType projectiveScheme.hom := projectiveLocallyFiniteType
  have hj (p : Points projectiveScheme complexAlgebra) : p ≫ j ∈ incidenceLocus := by
    have hu : p ≫ toComplexPoint projectiveScheme = 𝟙 complexPointScheme :=
      (toComplexPoint_unique _ _).trans (toComplexPoint_unique _ (𝟙 _)).symm
    have hp₁ : (p ≫ j) ≫ (prod.fst : IncidenceAmbient ⟶ projectiveScheme) = p := by
      simp [j]
    have hp₂ : (p ≫ j) ≫ (prod.snd : IncidenceAmbient ⟶ twoStepScheme) = x := by
      simp only [Category.assoc, j, prod.lift_snd]
      rw [← Category.assoc, hu, Category.id_comp]
    have hcond : IncidenceCondition (firstPlane p) (secondPlane x) := by
      rw [hx.2.2]
      exact ⟨Submodule.prod_mono le_rfl le_top, Submodule.prod_mono bot_le le_rfl⟩
    change IncidenceCondition (firstPlane ((p ≫ j) ≫ prod.fst))
      (secondPlane ((p ≫ j) ≫ prod.snd))
    exact hp₁.symm ▸ hp₂.symm ▸ hcond
  obtain ⟨s, hs⟩ := liftIntoReducedClosure j incidenceLocus hj
  change projectiveScheme ⟶ incidenceScheme at s
  change s ≫ incidenceInclusion = j at hs
  have hs₁ : s ≫ firstProjection = 𝟙 projectiveScheme :=
    (Category.assoc s incidenceInclusion prod.fst).symm.trans
      ((congrArg (fun f ↦ f ≫ prod.fst) hs).trans (prod.lift_fst _ _))
  have hs₂ : s ≫ terminalProjection = toComplexPoint projectiveScheme ≫ x :=
    (Category.assoc s incidenceInclusion prod.snd).symm.trans
      ((congrArg (fun f ↦ f ≫ prod.snd) hs).trans (prod.lift_snd _ _))
  have hinc : IsClosedImmersion incidenceInclusion.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have : Mono incidenceInclusion :=
    Functor.mono_of_mono_map (Over.forget _) (show Mono incidenceInclusion.left by infer_instance)
  have hpb : IsPullback s (toComplexPoint projectiveScheme) terminalProjection x := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk s (toComplexPoint projectiveScheme) hs₂)
      (PullbackCone.IsLimit.mk hs₂ (fun c ↦ c.fst ≫ firstProjection) ?_ ?_ ?_)
    · intro c
      apply (cancel_mono incidenceInclusion).mp
      apply prod.hom_ext
      · change ((c.fst ≫ firstProjection) ≫ s) ≫ firstProjection = c.fst ≫ firstProjection
        rw [Category.assoc, hs₁, Category.comp_id]
      · have hq := toComplexPoint_unique _ ((c.fst ≫ firstProjection) ≫
          toComplexPoint projectiveScheme)
        have hc := toComplexPoint_unique _ c.snd
        change ((c.fst ≫ firstProjection) ≫ s) ≫ incidenceInclusion ≫ prod.snd =
          c.fst ≫ incidenceInclusion ≫ prod.snd
        rw [← show terminalProjection = incidenceInclusion ≫ prod.snd from rfl,
          Category.assoc, hs₂, ← Category.assoc, hq.trans hc.symm, c.condition]
    · intro c
      exact (toComplexPoint_unique _ _).trans (toComplexPoint_unique _ c.snd).symm
    · intro c m hm _
      rw [← hm, Category.assoc, hs₁, Category.comp_id]
  have hsclosed : IsClosedImmersion s.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hpb.map (Over.forget _)).flip hx.1
  exact ⟨s, hs₁, hs₂, hpb, hsclosed⟩

private theorem incidencePoints_ext {R : TestAlgebra ℂ} {p q : Points incidenceScheme R}
    (h₁ : p ≫ firstProjection = q ≫ firstProjection)
    (h₂ : p ≫ terminalProjection = q ≫ terminalProjection) : p = q := by
  have : IsClosedImmersion incidenceInclusion.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have : Mono incidenceInclusion :=
    Functor.mono_of_mono_map (Over.forget _) (show Mono incidenceInclusion.left by infer_instance)
  apply (cancel_mono incidenceInclusion).mp
  apply prod.hom_ext
  · simpa only [Category.assoc, ConvolutionBundleSpecs.firstProjection] using h₁
  · simpa only [Category.assoc, terminalProjection] using h₂

private theorem exceptionalFibre_homeomorph
    {x : Points twoStepScheme complexAlgebra} {s : projectiveScheme ⟶ incidenceScheme}
    (h₁ : s ≫ firstProjection = 𝟙 _) (h₂ : s ≫ terminalProjection =
      toComplexPoint projectiveScheme ≫ x) :
    ∃ e : ProjectivePoints ≃ₜ {q : Points incidenceScheme complexAlgebra //
      q ≫ terminalProjection = x}, ∀ p, (e p).val = p ≫ s := by
  let ptx := x ≫ twoStepSchemeInGrassmannian
  have hterm (p : ProjectivePoints) : (p ≫ s) ≫ terminalProjection = x := by
    rw [Category.assoc, h₂, ← Category.assoc]
    have hu : p ≫ toComplexPoint projectiveScheme = 𝟙 complexPointScheme :=
      (toComplexPoint_unique _ _).trans (toComplexPoint_unique _ (𝟙 _)).symm
    rw [hu, Category.id_comp]
  have hfirst (p : ProjectivePoints) : (p ≫ s) ≫ firstProjection = p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f : projectiveScheme ⟶ projectiveScheme ↦ p ≫ f) h₁).trans
        (Category.comp_id p))
  let e : ProjectivePoints ≃ {q : Points incidenceScheme complexAlgebra //
      q ≫ terminalProjection = x} :=
    { toFun := fun p ↦ ⟨p ≫ s, hterm p⟩
      invFun := fun q ↦ q.val ≫ firstProjection
      left_inv := hfirst
      right_inv := fun q ↦ Subtype.ext (incidencePoints_ext (hfirst _) ((hterm _).trans q.2.symm)) }
  refine ⟨⟨e, ?_, ?_⟩, fun _ ↦ rfl⟩
  · apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    have he (p : ProjectivePoints) : incidenceCoordinates (p ≫ s) = (p, ptx) := by
      refine Prod.ext (hfirst p) ?_
      change ((p ≫ s) ≫ terminalProjection ≫ twoStepSchemeInGrassmannian) = _
      rw [← Category.assoc, hterm]
    exact (continuous_id.prodMk continuous_const).congr (fun p ↦ (he p).symm)
  · exact (continuous_fst.comp
      (continuous_induced_dom : Continuous (incidenceCoordinates))).comp continuous_subtype_val

private def firstCoefficient (R : TestAlgebra ℂ) :
    (R ⊗[ℂ] (V × V)) →ₗ[R] Coefficients R :=
  (LinearMap.fst R (Coefficients R) (Coefficients R)).comp
    (TensorProduct.prodRight ℂ R R V V).toLinearMap

private theorem firstCoefficient_surjective (R : TestAlgebra ℂ) :
    Function.Surjective (firstCoefficient R) := by
  intro v
  exact ⟨(TensorProduct.prodRight ℂ R R V V).symm (v, 0), by simp [firstCoefficient]⟩

private theorem baseChangeKer_congr {W A B : Type} [AddCommGroup W] [Module ℂ W]
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (N : Submodule A (A ⊗[ℂ] W)) (a₁ a₂ : Algebra A B) (h : a₁ = a₂)
    (t₁ : @IsScalarTower ℂ A B _ a₁.toSMul _)
    (t₂ : @IsScalarTower ℂ A B _ a₂.toSMul _) :
    (letI := a₁; letI := t₁; (Module.Grassmannian.baseChangeMkQ B N).ker) =
      (letI := a₂; letI := t₂; (Module.Grassmannian.baseChangeMkQ B N).ker) := by
  subst a₂
  rfl

private theorem scalarAffinePlane (x : Points twoStepScheme complexAlgebra)
    (hx : ScalarTerminalPoint x) (R : TestAlgebra ℂ) :
    twoStepAffinePlane R (toComplexPoint ((testSpec ℂ).obj (op R)) ≫ x) =
      (⊥ : Submodule R (Coefficients R)).prod ⊤ := by
  let a : complexAlgebra ⟶ R := CommAlgCat.ofHom (Algebra.ofId ℂ R)
  let X := grassmannianCharts twoStepBasis twoStepRank
  let p := x ≫ twoStepSchemeInGrassmannian
  let N := X.affinePoints.hom.app complexAlgebra p
  have ha : (testSpec ℂ).map a.op = toComplexPoint ((testSpec ℂ).obj (op R)) :=
    toComplexPoint_unique _ _
  have hN : N.toSubmodule = (firstCoefficient complexAlgebra).ker := by
    have hc : (LinearMap.fst ℂ V V).comp (TensorProduct.lid ℂ (V × V)).toLinearMap =
        (TensorProduct.lid ℂ V).toLinearMap.comp (firstCoefficient complexAlgebra) := by
      apply TensorProduct.ext'
      intro c v
      simp [firstCoefficient]
    ext v
    have hn : (TensorProduct.lid ℂ (V × V)) v ∈ secondPlane x ↔ v ∈ N.toSubmodule := by
      change (TensorProduct.lid ℂ (V × V)) v ∈
        N.toSubmodule.map (TensorProduct.lid ℂ (V × V)).toLinearMap ↔ _
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    have hcv := LinearMap.congr_fun hc v
    change ((TensorProduct.lid ℂ (V × V)) v).1 =
      (TensorProduct.lid ℂ V) (firstCoefficient complexAlgebra v) at hcv
    rw [← hn, hx.2.2, Submodule.mem_prod, Submodule.mem_bot, LinearMap.mem_ker, hcv]
    simp
  have hnat : X.affinePoints.hom.app R (mapPoints a p) = Module.Grassmannian.map a.hom N :=
    congrArg (fun f ↦ f p) (X.affinePoints.hom.naturality a)
  let f := firstCoefficient complexAlgebra
  let eq : ((complexAlgebra ⊗[ℂ] (V × V)) ⧸ N.toSubmodule) ≃ₗ[ℂ] Coefficients complexAlgebra :=
    Submodule.quotEquivOfEq _ _ hN ≪≫ₗ f.quotKerEquivOfSurjective (firstCoefficient_surjective _)
  let e := eq.baseChange ℂ R ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange
    ℂ ℂ R R V
  have he : e.toLinearMap.comp (Module.Grassmannian.baseChangeMkQ R N.toSubmodule) =
      firstCoefficient R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r v
    simp only [e, eq, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk, Submodule.mkQ_apply,
      f, firstCoefficient, TensorProduct.prodRight_tmul, LinearMap.fst_apply]
    simp
  have hker : (Module.Grassmannian.map a.hom N).toSubmodule = (firstCoefficient R).ker := by
    have hA : a.hom.toAlgebra = (inferInstance : Algebra complexAlgebra R) :=
      Algebra.algebra_ext _ _ (fun _ ↦ rfl)
    rw [Module.Grassmannian.map_toSubmodule, ← he, LinearEquiv.ker_comp]
    exact baseChangeKer_congr N.toSubmodule _ _ hA _ _
  unfold twoStepAffinePlane
  rw [← ha, Category.assoc]
  change ((X.affinePoints.hom.app R (mapPoints a p)).toSubmodule.map _) = _
  rw [hnat, hker]
  ext v
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, Submodule.mem_prod, Submodule.mem_bot]
  simp [firstCoefficient]

private theorem bundleQuotient_surjective (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :
    Function.Surjective (bundleQuotient R S) := by
  rintro ⟨x, y⟩
  obtain ⟨z, hz⟩ := S.mkQ_surjective y
  exact ⟨⟨(x, z), x.property, Submodule.mem_top⟩, Prod.ext rfl hz⟩

private theorem scalarBundleLine_iff {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (B : BundleLine R p) :
    let S := tautological R p
    (⊥ : Submodule R (Coefficients R)).prod ⊤ =
      ((B.toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype) ↔
      B.toSubmodule = (⊥ : Submodule R S).prod ⊤ := by
  let S := tautological R p
  have hplane :
      ((((⊥ : Submodule R S).prod ⊤).comap (bundleQuotient R S)).map
        (S.prod ⊤).subtype) = (⊥ : Submodule R (Coefficients R)).prod ⊤ := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨congrArg Subtype.val hz.1, Submodule.mem_top⟩
    · intro hv
      have h0 : v.1 = 0 := hv.1
      have hv' : v ∈ S.prod (⊤ : Submodule R (Coefficients R)) :=
        ⟨h0.symm ▸ S.zero_mem, Submodule.mem_top⟩
      exact ⟨⟨v, hv'⟩, ⟨Subtype.ext h0, Submodule.mem_top⟩, rfl⟩
  change _ = (B.toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype ↔ _
  rw [← hplane, Submodule.map_injective_of_injective (S.prod ⊤).subtype_injective |>.eq_iff,
    Submodule.comap_injective_of_surjective (bundleQuotient_surjective R S) |>.eq_iff, eq_comm]

private theorem exceptionalSection_exists :
    ∃ (x : Points twoStepScheme complexAlgebra) (s : projectiveScheme ⟶ incidenceScheme),
      ExceptionalSection x s := by
  obtain ⟨x, hx⟩ := scalarTerminalPoint_exists
  obtain ⟨s, h₁, h₂, hpb, hs⟩ := exceptionalSection_square x hx
  refine ⟨x, s, hx, hs, h₁, hpb, ?_⟩
  intro R p B
  rw [h₂, ← Category.assoc, toComplexPoint_unique _ (p ≫ toComplexPoint projectiveScheme),
    scalarAffinePlane x hx R]
  exact scalarBundleLine_iff B

private theorem projectiveChart_dim (I : Pivot (Fin 2 × Fin 1) 1) :
    topologicalKrullDim (chartScheme (k := ℂ) I).left = 1 := by
  change topologicalKrullDim (PrimeSpectrum (chartAlgebra (k := ℂ) I)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  have hI : Fintype.card (Inside I) = 1 := (Fintype.card_coe I.val).trans I.prop
  have hO : Fintype.card (Outside I) = 1 := by
    change Fintype.card {i // i ∉ I.val} = 1
    rw [Fintype.card_subtype_compl (fun i ↦ i ∈ I.val), hI]
    decide
  simp [Nat.card_eq_fintype_card, hI, hO]

private theorem projective_dim : topologicalKrullDim projectiveScheme.left = 1 := by
  let X := grassmannianCharts projectiveBasis projectiveRank
  let I₀ : Pivot (Fin 2 × Fin 1) 1 := ⟨{(0, 0)}, Finset.card_singleton _⟩
  have hlower : 1 ≤ topologicalKrullDim projectiveScheme.left := by
    rw [← projectiveChart_dim I₀]
    have h := X.openChart I₀
    exact (X.chart I₀).left.isOpenEmbedding.isInducing.topologicalKrullDim_le
  refine le_antisymm ?_ hlower
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := projectiveScheme.left)), Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨I, y, hxy⟩ := X.cover x
  have h := X.openChart I
  change (X.chart I).left y = x at hxy
  rw [← hxy, coheight_eq_of_isOpenImmersion (X.chart I).left]
  rw [← projectiveChart_dim I, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := (chartScheme (k := ℂ) I).left))]
  exact Order.coheight_le_krullDim y

private theorem submodule_ret {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) [Module.Projective R (M ⧸ S)] :
    ∃ f : M →ₗ[R] S, f.comp S.subtype = LinearMap.id := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property S.mkQ
    (LinearMap.id : (M ⧸ S) →ₗ[R] M ⧸ S) S.mkQ_surjective
  have h (v : M) : v - g (S.mkQ v) ∈ S := by
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (v - g (S.mkQ v)) = 0
    rw [map_sub]
    rw [show S.mkQ (g (S.mkQ v)) = S.mkQ v from LinearMap.congr_fun hg (S.mkQ v), sub_self]
  refine ⟨(LinearMap.id - g.comp S.mkQ).codRestrict S h, ?_⟩
  ext v
  change v.val - g (S.mkQ v.val) = v.val
  have hv : S.mkQ v.val = 0 := (Submodule.Quotient.mk_eq_zero S).mpr v.property
  rw [hv, map_zero, sub_zero]

private theorem normalLinearMaps_tensor (h : ProjectiveBundle) (R : TestAlgebra ℂ)
    (p : Points projectiveScheme R) :
    let S := tautological R p
    ∃ e : (S ⊗[R] S) ≃ₗ[R] NormalLinearMaps R p,
      ∀ (u v : S) (w : Coefficients R),
        e (u ⊗ₜ[R] v) (S.mkQ w) = volume R v.val w • u := by
  let S := tautological R p
  let Q := Coefficients R ⧸ S
  have : Module.Finite R Q := by
    change Module.Finite R ((R ⊗[ℂ] V) ⧸
      ((grassmannianCharts projectiveBasis projectiveRank).affinePoints.hom.app R p).toSubmodule)
    infer_instance
  have : Module.Projective R Q := by
    change Module.Projective R ((R ⊗[ℂ] V) ⧸
      ((grassmannianCharts projectiveBasis projectiveRank).affinePoints.hom.app R p).toSubmodule)
    infer_instance
  have : Module.Free R (Coefficients R) := Module.Free.of_basis (projectiveBasis.baseChange R)
  have : Module.Finite R (Coefficients R) := Module.Finite.of_basis (projectiveBasis.baseChange R)
  obtain ⟨r, hr⟩ := submodule_ret S
  have : Module.Finite R S := Module.Finite.of_surjective r
    (LinearMap.surjective_of_comp_eq_id S.subtype r hr)
  have : Module.Projective R S := Module.Projective.of_split S.subtype r hr
  obtain ⟨d, hd⟩ := h.1 R p
  let b : S ≃ₗ[R] Module.Dual R Q := Module.evalEquiv R S ≪≫ₗ d.dualMap
  let e : S ⊗[R] S ≃ₗ[R] NormalLinearMaps R p :=
    TensorProduct.comm R S S ≪≫ₗ
      TensorProduct.congr b (LinearEquiv.refl R S) ≪≫ₗ
      dualTensorHomEquiv R Q S
  refine ⟨e, ?_⟩
  intro u v w
  change (e (u ⊗ₜ[R] v)) (S.mkQ w) = _
  simp only [e, b, LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, Module.evalEquiv_apply]
  exact congrArg (· • u) (hd v w)

private theorem complexFirstCoefficient (x : Points twoStepScheme complexAlgebra) :
    ((twoStepAffinePlane complexAlgebra x).map
      (LinearMap.fst ℂ (Coefficients complexAlgebra) (Coefficients complexAlgebra))).map
        (TensorProduct.lid ℂ V).toLinearMap =
    (secondPlane x).map (LinearMap.fst ℂ V V) := by
  unfold twoStepAffinePlane secondPlane grassmannianSubspace
  simp only [← Submodule.map_comp]
  congr 1
  apply TensorProduct.ext'
  intro c v
  simp

private theorem lattice_sum_of_firstPlane {F : Flags}
    (h₁ : scalarPoint.val ≤ F.val.1.val)
    (h₂ : (scalarLattice 2 2).val ≤ F.val.2.val)
    (hplane : (latticeSubspace 0 1 F.val.1).map constantCoordinates.toLinearMap =
      ((latticeSubspace 0 2 F.val.2).map twoStepCoordinates.toLinearMap).map
        (LinearMap.fst ℂ V V)) :
    F.val.1.val = F.val.2.val ⊔ scalarPoint.val := by
  apply le_antisymm _ (sup_le F.property.2.1 h₁)
  intro z hz
  have hz₀ : z ∈ (scalarLattice 2 0).val := F.property.1.1 hz
  obtain ⟨x, hzx⟩ := (shiftedCoordinates 2 0).surjective ⟨z, hz₀⟩
  have hxz : shiftedInclusion 2 0 x = z :=
    (shiftedCoordinates_coe 2 0 x).symm.trans (congrArg Subtype.val hzx)
  have hx : windowClass 2 0 1 x ∈ latticeSubspace 0 1 F.val.1 :=
    (windowClass_mem F.val.1
      (show (scalarLattice 2 (0 + (1 : ℕ))).val ≤ F.val.1.val from h₁) x).mpr (hxz.symm ▸ hz)
  have hv : constantCoordinates (windowClass 2 0 1 x) ∈
      ((latticeSubspace 0 2 F.val.2).map twoStepCoordinates.toLinearMap).map
        (LinearMap.fst ℂ V V) :=
    hplane ▸ Submodule.mem_map_of_mem hx
  obtain ⟨_, ⟨v, hv', rfl⟩, heq⟩ := hv
  obtain ⟨y, rfl⟩ := windowClass_surjective 2 0 2 v
  have hy := (windowClass_mem F.val.2
    (show (scalarLattice 2 (0 + (2 : ℕ))).val ≤ F.val.2.val from h₂) y).mp hv'
  have hcoef (i : Fin 2) : PowerSeries.coeff 0 (y i) = PowerSeries.coeff 0 (x i) := by
    have he := congrFun heq i
    change windowCoordinates 2 0 2 (windowClass 2 0 2 y) (i, 0) =
      windowCoordinates 2 0 1 (windowClass 2 0 1 x) (i, 0) at he
    rwa [windowCoordinates_class, windowCoordinates_class] at he
  have hd : shiftedInclusion 2 0 x - shiftedInclusion 2 0 y ∈ scalarPoint.val := by
    rw [← map_sub, scalarLatticeCoordinates]
    intro i
    rw [Pi.sub_apply, map_sub, hcoef, sub_self]
  exact Submodule.mem_sup.mpr ⟨_, hy, _, hd, by rw [← hxz]; abel⟩

private theorem twoStepPoints_location_injective :
    Function.Injective (pointLocation : Points twoStepScheme complexAlgebra → twoStepScheme.left) := by
  intro p q hpq
  have : LocallyOfFiniteType twoStepScheme.hom := twoStepLocallyFiniteType
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq twoStepScheme.hom (complexPoint_comp _ p)
    (complexPoint_comp _ q) hpq

private theorem terminal_lattice_injective (ho : TwoStepOrbits) :
    Function.Injective (fun L : Colength 2 ↦
      (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap) := by
  intro L M h
  obtain ⟨e, he, _⟩ := BoundedLattices.windowLatticeComparison 2 0 2
  let L' : WindowLattice 2 0 2 := ⟨L.val, ho.1 L, L.property.1⟩
  let M' : WindowLattice 2 0 2 := ⟨M.val, ho.1 M, M.property.1⟩
  have hsub : latticeSubspace 0 2 L.val = latticeSubspace 0 2 M.val :=
    (Submodule.map_injective_of_injective twoStepCoordinates.injective) h
  have hem : (e L').val = (e M').val := (he L').trans (hsub.trans (he M').symm)
  exact Subtype.ext (congrArg (fun N : WindowLattice 2 0 2 ↦ N.val) (e.injective (Subtype.ext hem)))

private theorem scalarComplement (ho : TwoStepOrbits)
    (x : Points twoStepScheme complexAlgebra) (hx : ScalarTerminalPoint x) :
    ∃ U : twoStepScheme.left.Opens,
      (U : Set twoStepScheme.left) = {pointLocation x}ᶜ ∧
      ∀ (p : Points twoStepScheme complexAlgebra) (L : Colength 2),
        secondPlane p = (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap →
        (pointLocation p ∈ U ↔ L.val ∈ gl2Orbit twoStepPair) := by
  have : IsClosedImmersion x.left := hx.1
  have hclosed : IsClosed ({pointLocation x} : Set twoStepScheme.left) := by
    rw [← pointLocation_range]
    exact x.left.isClosedEmbedding.isClosed_range
  let U : twoStepScheme.left.Opens := ⟨_, hclosed.isOpen_compl⟩
  refine ⟨U, rfl, ?_⟩
  intro p L h
  have heq : pointLocation p = pointLocation x ↔ L.val = scalarPoint := by
    let D : Colength 2 := ⟨scalarPoint, ho.2.2.2.1⟩
    constructor
    · intro hp
      have hpx : p = x := twoStepPoints_location_injective hp
      have hL := h.symm.trans ((congrArg secondPlane hpx).trans hx.2.1)
      exact congrArg Subtype.val (terminal_lattice_injective ho (a₁ := L) (a₂ := D) hL)
    · intro hL
      apply congrArg pointLocation
      apply secondPlane_injective
      rw [h, hL, hx.2.1]
  change pointLocation p ∉ ({pointLocation x} : Set twoStepScheme.left) ↔
    L.val ∈ gl2Orbit twoStepPair
  rw [ho.2.2.1, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_singleton_iff, heq]
  exact ⟨fun hn ↦ ⟨L.property, hn⟩, And.right⟩

private theorem stablePlane_incidence (P : Submodule ℂ (V × V))
    (hd : Module.finrank ℂ P = 2) (hP : P.map shift ≤ P)
    (hne : P ≠ (⊥ : Submodule ℂ V).prod ⊤) :
    let S := P.map (LinearMap.fst ℂ V V)
    Module.finrank ℂ S = 1 ∧ IncidenceCondition S P := by
  let S := P.map (LinearMap.fst ℂ V V)
  have hdV : Module.finrank ℂ V = 2 := by simp [V]
  have hs : IncidenceCondition S P := by
    refine ⟨?_, fun v hv ↦ ⟨Submodule.mem_map_of_mem hv, Submodule.mem_top⟩⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨v, hv, rfl⟩ := hb
    have ha₀ : a = 0 := ha
    rw [ha₀]
    exact (show shift v ∈ P from hP (Submodule.mem_map_of_mem (f := shift) hv))
  have hSn : S ≠ ⊥ := by
    intro h
    apply hne
    apply Submodule.eq_of_le_of_finrank_le (h ▸ hs.2)
    rw [hd, (Submodule.prodEquiv (⊥ : Submodule ℂ V) (⊤ : Submodule ℂ V)).finrank_eq,
      Module.finrank_prod, finrank_bot, finrank_top, zero_add, hdV]
  have hSt : S ≠ ⊤ := by
    intro h
    apply hne
    symm
    apply Submodule.eq_of_le_of_finrank_le (h ▸ hs.1)
    rw [hd, (Submodule.prodEquiv (⊥ : Submodule ℂ V) (⊤ : Submodule ℂ V)).finrank_eq,
      Module.finrank_prod, finrank_bot, finrank_top, zero_add, hdV]
  have hmin : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero
    (fun H ↦ hSn (Submodule.finrank_eq_zero.mp H))
  have hmax : Module.finrank ℂ S < 2 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hSt)
    have htop : Module.finrank ℂ (⊤ : Submodule ℂ V) = 2 := (finrank_top ℂ V).trans hdV
    exact hlt.trans_le htop.le
  change Module.finrank ℂ S = 1 ∧ IncidenceCondition S P
  exact ⟨by omega, hs⟩

private theorem terminalProjection_surjective_complex (x : Points twoStepScheme complexAlgebra)
    (hx : ScalarTerminalPoint x) :
    Function.Surjective (fun q : Points incidenceScheme complexAlgebra ↦
      q ≫ terminalProjection) := by
  intro p
  by_cases he : p = x
  · subst p
    obtain ⟨s, h₁, h₂, _, _⟩ := exceptionalSection_square x hx
    obtain ⟨e, _⟩ := exceptionalFibre_homeomorph h₁ h₂
    let I : Pivot (Fin 2 × Fin 1) 1 := ⟨{(0, 0)}, Finset.card_singleton _⟩
    let q := grassmannianChartPoint projectiveBasis projectiveRank I 0
    exact ⟨(e q).val, (e q).property⟩
  · let P := secondPlane p
    have hd := grassmannianSubspace_finrank twoStepBasis twoStepRank
      (p ≫ twoStepSchemeInGrassmannian)
    have hP : P.map shift ≤ P :=
      (LatticeModels.stableSchemePoints twoStepBasis twoStepRank shift p).property
    have hn : P ≠ (⊥ : Submodule ℂ V).prod ⊤ := fun h ↦ he
      (secondPlane_injective (h.trans hx.2.2.symm))
    obtain ⟨ds, hs⟩ := stablePlane_incidence P hd hP hn
    let S := P.map (LinearMap.fst ℂ V V)
    let q := subspacePoint projectiveBasis projectiveRank S ds
    let r : Points IncidenceAmbient complexAlgebra := prod.lift q p
    have hr : r ∈ incidenceLocus := by
      change IncidenceCondition (firstPlane (r ≫ prod.fst)) (secondPlane (r ≫ prod.snd))
      have hf : r ≫ (prod.fst : IncidenceAmbient ⟶ projectiveScheme) = q := prod.lift_fst _ _
      have hg : r ≫ (prod.snd : IncidenceAmbient ⟶ twoStepScheme) = p := prod.lift_snd _ _
      have hq : firstPlane q = S := subspacePoint_subspace _ _ _ _
      exact hf.symm ▸ hg.symm ▸ hq.symm ▸ hs
    obtain ⟨a, ha⟩ :=
      (LatticeModels.pointLocation_in_closure_iff incidenceLocus r).mp
        (subset_closure ⟨r, hr, rfl⟩)
    have ha' : a ≫ incidenceInclusion = r := ha
    exact ⟨a, (Category.assoc a incidenceInclusion prod.snd).symm.trans
      ((congrArg (fun f ↦ f ≫ prod.snd) ha').trans (prod.lift_snd _ _))⟩

private theorem bundlePlane_bounds {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (B : BundleLine R p) :
    let S := tautological R p
    let P := (B.toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype
    (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤ := by
  let S := tautological R p
  constructor
  · rintro v ⟨h₁, h₂⟩
    have ha : v.1 = 0 := h₁
    have hb : v ∈ S.prod (⊤ : Submodule R (Coefficients R)) :=
      ⟨ha.symm ▸ S.zero_mem, Submodule.mem_top⟩
    refine ⟨⟨v, hb⟩, ?_, rfl⟩
    have hq : S.mkQ v.2 = 0 := (Submodule.Quotient.mk_eq_zero S).mpr h₂
    change (⟨v.1, hb.1⟩, S.mkQ v.2) ∈ B.toSubmodule
    have hz : (⟨v.1, hb.1⟩ : S) = 0 := Subtype.ext ha
    rw [hz, hq]
    exact B.toSubmodule.zero_mem
  · rintro _ ⟨v, -, rfl⟩
    exact v.property

private theorem affineIncidence_bounds (h : ProjectiveBundle) {R : TestAlgebra ℂ}
    (q : Points incidenceScheme R) :
    let S := tautological R (q ≫ firstProjection)
    let P := twoStepAffinePlane R (q ≫ terminalProjection)
    (⊥ : Submodule R (Coefficients R)).prod S ≤ P ∧ P ≤ S.prod ⊤ := by
  obtain ⟨e, he, _⟩ := h.2
  obtain ⟨h₁, h₂⟩ := he R q
  dsimp only at h₂ ⊢
  rw [← h₁, h₂]
  exact bundlePlane_bounds (e R q).2

private theorem graphPlane_snd {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) :
    Function.Bijective (fun z : graphPlane f ↦ z.val.2) := by
  constructor
  · rintro ⟨v, y, rfl⟩ ⟨w, z, rfl⟩ h
    change y = z at h
    subst z
    rfl
  · intro y
    exact ⟨⟨_, y, rfl⟩, rfl⟩

private theorem graphPlane_injective {R : TestAlgebra ℂ} (p : Points projectiveScheme R) :
    Function.Injective (graphPlane (R := R) (p := p)) := by
  intro f g h
  apply LinearMap.ext
  intro u
  obtain ⟨w, rfl⟩ := (tautological R p).mkQ_surjective u
  have hmem : (graphEndomorphism f w, w) ∈ graphPlane g :=
    h ▸ (show (graphEndomorphism f w, w) ∈ graphPlane f from ⟨w, rfl⟩)
  obtain ⟨z, hz⟩ := hmem
  have hzw : z = w := congrArg Prod.snd hz
  subst z
  exact Subtype.ext (congrArg Prod.fst hz).symm

private def quotientFactor {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (S : Submodule R M) (b : M →ₗ[R] N)
    (hb : ∀ v ∈ S, b v = 0) : (M ⧸ S) →ₗ[R] N :=
  S.liftQ b (fun v hv ↦ LinearMap.mem_ker.mpr (hb v hv))

private theorem graphPlane_exists {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (P : Submodule R (Coefficients R × Coefficients R))
    (hlo : (⊥ : Submodule R (Coefficients R)).prod (tautological R p) ≤ P)
    (hhi : P ≤ (tautological R p).prod ⊤)
    (hsnd : Function.Bijective (fun z : P ↦ z.val.2)) :
    ∃ f : NormalLinearMaps R p, P = graphPlane f := by
  let S := tautological R p
  let d : P ≃ₗ[R] Coefficients R :=
    LinearEquiv.ofBijective ((LinearMap.snd R _ _).comp P.subtype) hsnd
  let a : Coefficients R →ₗ[R] Coefficients R :=
    (LinearMap.fst R _ _).comp (P.subtype.comp d.symm.toLinearMap)
  have h₂ (v : Coefficients R) : (d.symm v).val.2 = v := d.apply_symm_apply v
  have h₁ (v : Coefficients R) : a v ∈ S := (hhi (d.symm v).property).1
  let b : Coefficients R →ₗ[R] S := a.codRestrict S h₁
  have hun (v : Coefficients R) (hv : v ∈ S) : b v = 0 := by
    let z : P := ⟨(0, v), hlo ⟨Submodule.zero_mem _, hv⟩⟩
    have hz : d z = v := rfl
    apply Subtype.ext
    change (d.symm v).val.1 = 0
    rw [← hz, LinearEquiv.symm_apply_apply]
  let f₀ := quotientFactor (R := R) (M := Coefficients R) (N := ↥S) S b hun
  let f : NormalLinearMaps R p := f₀
  refine ⟨f, ?_⟩
  have hA (v : Coefficients R) : graphEndomorphism f v = a v := rfl
  ext v
  constructor
  · intro hv
    let z : P := ⟨v, hv⟩
    refine ⟨d z, Prod.ext ?_ rfl⟩
    change graphEndomorphism f (d z) = v.1
    rw [hA]
    change (d.symm (d z)).val.1 = _
    rw [LinearEquiv.symm_apply_apply]
  · rintro ⟨v, rfl⟩
    have he : (graphEndomorphism f v, v) = (d.symm v).val :=
      Prod.ext (hA v) (h₂ v).symm
    change (graphEndomorphism f v, v) ∈ P
    rw [he]
    exact (d.symm v).property

private theorem twoStepAffinePlane_injective (R : TestAlgebra ℂ) :
    Function.Injective (twoStepAffinePlane R) := by
  intro p q h
  have : IsClosedImmersion twoStepSchemeInGrassmannian.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have : Mono twoStepSchemeInGrassmannian :=
    Functor.mono_of_mono_map (Over.forget _)
      (show Mono twoStepSchemeInGrassmannian.left by infer_instance)
  apply (cancel_mono twoStepSchemeInGrassmannian).mp
  apply ((grassmannianCharts twoStepBasis twoStepRank).affinePoints.app R).toEquiv.injective
  apply Module.Grassmannian.ext
  exact Submodule.map_injective_of_injective
    (TensorProduct.prodRight ℂ R R V V).injective h

private def splitSubmoduleEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (r : M →ₗ[R] S) (hr : r.comp S.subtype = LinearMap.id) :
    M ≃ₗ[R] S × (M ⧸ S) := by
  have hr' (s : S) : r s.val = s := LinearMap.congr_fun hr s
  refine LinearEquiv.ofBijective (r.prod S.mkQ) ⟨?_, ?_⟩
  · refine (LinearMap.ker_eq_bot (f := r.prod S.mkQ)).mp ?_
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hx₁ : r x = 0 := congrArg Prod.fst hx
    have hx₂ : S.mkQ x = 0 := congrArg Prod.snd hx
    let sx : S := ⟨x, (Submodule.Quotient.mk_eq_zero S).mp hx₂⟩
    exact congrArg Subtype.val ((hr' sx).symm.trans hx₁)
  · rintro ⟨s, y⟩
    obtain ⟨w, hw⟩ := S.mkQ_surjective y
    refine ⟨w + (s - r w : S).val, Prod.ext ?_ ?_⟩
    · change r (w + _) = s
      rw [map_add, hr']
      abel
    · change S.mkQ (w + _) = y
      have hzero : S.mkQ (s - r w : S).val = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr (s - r w).property
      rw [map_add, hw, hzero, add_zero]

private theorem tautological_rank (R : TestAlgebra ℂ) (p : Points projectiveScheme R)
    (z : PrimeSpectrum R) : Module.rankAtStalk (R := R) (tautological R p) z = 1 := by
  let N := (grassmannianCharts projectiveBasis projectiveRank).affinePoints.hom.app R p
  let S := tautological R p
  let Q := Coefficients R ⧸ S
  have : Module.Finite R Q := N.finite_quotient
  have : Module.Projective R Q := N.projective_quotient
  have : Module.Free R (Coefficients R) := Module.Free.of_basis (projectiveBasis.baseChange R)
  have : Module.Finite R (Coefficients R) := Module.Finite.of_basis (projectiveBasis.baseChange R)
  obtain ⟨r, hr⟩ := submodule_ret S
  have : Module.Finite R S := Module.Finite.of_surjective r
    (LinearMap.surjective_of_comp_eq_id S.subtype r hr)
  have : Module.Projective R S := Module.Projective.of_split S.subtype r hr
  let e : Coefficients R ≃ₗ[R] (S × Q) := splitSubmoduleEquiv S r hr
  have he := congrFun (Module.rankAtStalk_eq_of_equiv (M := Coefficients R) (N := S × Q) e) z
  have hn : Module.rankAtStalk (R := R) Q z = 1 := by
    have h := N.rankAtStalk_eq z
    change Module.rankAtStalk (R := R) Q z = Module.finrank ℂ V - 1 at h
    simpa [V] using h
  have : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with hsub | hn
    · exact (z.isPrime.ne_top (Subsingleton.elim _ _)).elim
    · exact hn
  have hf : Module.finrank R (Coefficients R) = 2 := by
    rw [Module.finrank_eq_card_basis (projectiveBasis.baseChange R)]
    decide
  change Module.rankAtStalk (R := R) (Coefficients R) z =
    Module.rankAtStalk (R := R) (S × Q) z at he
  rw [Module.rankAtStalk_prod, Pi.add_apply, hn, Module.rankAtStalk_eq_finrank_of_free, hf] at he
  change Module.rankAtStalk (R := R) S z = 1
  exact Nat.add_right_cancel (show _ + 1 = 1 + 1 from he.symm)

private theorem tautological_finite_projective (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :
    Module.Finite R (tautological R p) ∧ Module.Projective R (tautological R p) := by
  let S := tautological R p
  let Q := Coefficients R ⧸ S
  let N := (grassmannianCharts projectiveBasis projectiveRank).affinePoints.hom.app R p
  have : Module.Projective R Q := N.projective_quotient
  have : Module.Free R (Coefficients R) := Module.Free.of_basis (projectiveBasis.baseChange R)
  have : Module.Finite R (Coefficients R) := Module.Finite.of_basis (projectiveBasis.baseChange R)
  obtain ⟨r, hr⟩ := submodule_ret S
  exact ⟨Module.Finite.of_surjective r (LinearMap.surjective_of_comp_eq_id S.subtype r hr),
    Module.Projective.of_split S.subtype r hr⟩

private def graphQuotient {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) : M × N →ₗ[R] M :=
  LinearMap.fst R M N - f.comp (LinearMap.snd R M N)

private def graphQuotientEquiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    ((M × N) ⧸ (graphQuotient f).ker) ≃ₗ[R] M :=
  (graphQuotient f).quotKerEquivOfSurjective fun s ↦
    ⟨(s, 0), by simp [graphQuotient]⟩

private def graphBundleLine {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) : BundleLine R p := by
  let S := tautological R p
  let Q := Coefficients R ⧸ S
  let f' : Q →ₗ[R] S := f
  let F : BundleFiber R S →ₗ[R] S := graphQuotient (R := R) (M := ↥S) (N := Q) f'
  let e := graphQuotientEquiv (R := R) (M := ↥S) (N := Q) f'
  have : Module.Finite R S := (tautological_finite_projective R p).1
  have : Module.Projective R S := (tautological_finite_projective R p).2
  exact ⟨F.ker, Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm,
    fun z ↦ (congrFun (Module.rankAtStalk_eq_of_equiv e) z).trans (tautological_rank R p z)⟩

private theorem graphBundleLine_plane {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) :
    let S := tautological R p
    (((graphBundleLine f).toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype) =
      graphPlane f := by
  let S := tautological R p
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.2, Prod.ext ?_ rfl⟩
    change (⟨z.val.1, z.property.1⟩ : S) - f (S.mkQ z.val.2) = 0 at hz
    have hh : (⟨z.val.1, z.property.1⟩ : S) = (f (S.mkQ z.val.2) : S) :=
      sub_eq_zero.mp hz
    exact congrArg (fun x : S ↦ x.val) hh.symm
  · rintro ⟨v, rfl⟩
    let z : S.prod (⊤ : Submodule R (Coefficients R)) :=
      ⟨(graphEndomorphism f v, v), (f (S.mkQ v)).property, Submodule.mem_top⟩
    refine ⟨z, ?_, rfl⟩
    change (⟨z.val.1, z.property.1⟩ : S) - f (S.mkQ v) = 0
    exact sub_self (f (S.mkQ v) : S)

/-- The graph formula for lines in the coefficient bundle over any affine test. -/
private theorem incidenceGraph_existsUnique (h : ProjectiveBundle) (R : TestAlgebra ℂ)
    (p : Points projectiveScheme R) (f : NormalLinearMaps R p) :
    ∃! q : Points incidenceScheme R, q ≫ firstProjection = p ∧
      twoStepAffinePlane R (q ≫ terminalProjection) = graphPlane f := by
  obtain ⟨e, he, _⟩ := h.2
  let q := (e R).symm ⟨p, graphBundleLine f⟩
  have hq : e R q = ⟨p, graphBundleLine f⟩ := (e R).apply_symm_apply _
  obtain ⟨h₁, h₂⟩ := he R q
  rw [hq] at h₁ h₂
  have hfg : twoStepAffinePlane R (q ≫ terminalProjection) = graphPlane f :=
    h₂.trans (graphBundleLine_plane f)
  exact ⟨q, ⟨h₁.symm, hfg⟩, fun r hr ↦
    incidencePoints_ext (hr.1.trans h₁) (twoStepAffinePlane_injective R (hr.2.trans hfg.symm))⟩

private def secondPivot : Pivot (Fin 2 × Fin 2) 2 :=
  ⟨{(0, 1), (1, 1)}, by decide⟩

private theorem secondPivot_mem (i : Fin 2 × Fin 2) :
    i ∈ secondPivot.val ↔ i.2 = 1 := by
  obtain ⟨i, j⟩ := i
  fin_cases i <;> fin_cases j <;> decide

private def secondPivotRows : Inside secondPivot ≃ Fin 2 where
  toFun i := i.val.1
  invFun i := ⟨(i, 1), (secondPivot_mem _).mpr rfl⟩
  left_inv i := Subtype.ext (Prod.ext rfl ((secondPivot_mem _).mp i.property).symm)
  right_inv _ := rfl

private theorem twoStepBasis_repr (v : V × V) (i j : Fin 2) :
    twoStepBasis.repr v (i, j) = if j = 0 then v.1 i else v.2 i := by
  rw [twoStepBasis, Module.Basis.map_repr, windowBasis, LinearEquiv.trans_apply, Module.Basis.ofEquivFun_repr_apply]
  let w : Fin 2 × Fin 2 → ℂ := fun ij ↦ if ij.2 = 0 then v.1 ij.1 else v.2 ij.1
  change windowCoordinates 2 0 2 ((windowCoordinates 2 0 2).symm w) (i, j) = _
  rw [LinearEquiv.apply_symm_apply]

private theorem secondPivot_coefficients (R : TestAlgebra ℂ) (v : R ⊗[ℂ] (V × V))
    (i : Inside secondPivot) :
    pivotProjection twoStepBasis secondPivot R v i =
      coordinates (Pi.basisFun ℂ (Fin 2)) R ((TensorProduct.prodRight ℂ R R V V) v).2
        (secondPivotRows i) := by
  refine TensorProduct.inductionOn
    (motive := fun v ↦ pivotProjection twoStepBasis secondPivot R v i =
      coordinates (Pi.basisFun ℂ (Fin 2)) R ((TensorProduct.prodRight ℂ R R V V) v).2
        (secondPivotRows i)) v ?_ ?_
  · intro r v
    change (twoStepBasis.baseChange R).repr (r ⊗ₜ[ℂ] v) i.val =
      coordinates (Pi.basisFun ℂ (Fin 2)) R ((TensorProduct.prodRight ℂ R R V V)
        (r ⊗ₜ[ℂ] v)).2 i.val.1
    rw [TensorProduct.prodRight_tmul]
    change (twoStepBasis.baseChange R).repr (r ⊗ₜ[ℂ] v) i.val =
      ((Pi.basisFun ℂ (Fin 2)).baseChange R).repr (r ⊗ₜ[ℂ] v.2) i.val.1
    rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul]
    have hi : i.val.2 = 1 := (secondPivot_mem _).mp i.property
    rw [show i.val = (i.val.1, i.val.2) from Prod.eta _, twoStepBasis_repr, hi]
    simp
  · intro x y hx hy
    simp only [map_add, Pi.add_apply, Prod.snd_add, hx, hy]

private theorem terminalPlane_secondPivot (R : TestAlgebra ℂ) (p : Points twoStepScheme R) :
    IsPivot twoStepBasis secondPivot R ((grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R
      (p ≫ twoStepSchemeInGrassmannian)) ↔
    Function.Bijective (fun v : twoStepAffinePlane R p ↦ v.val.2) := by
  let N := ((grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R
    (p ≫ twoStepSchemeInGrassmannian)).toSubmodule
  let e := TensorProduct.prodRight ℂ R R V V
  let en : N ≃ₗ[R] twoStepAffinePlane R p := N.equivMapOfInjective e.toLinearMap e.injective
  let s := fun v : twoStepAffinePlane R p ↦ v.val.2
  let c : Coefficients R ≃ (Inside secondPivot → R) :=
    (coordinates (Pi.basisFun ℂ (Fin 2)) R).toEquiv.trans
      (Equiv.arrowCongr secondPivotRows.symm (Equiv.refl R))
  have hc (v : Coefficients R) (i : Inside secondPivot) :
      c v i = coordinates (Pi.basisFun ℂ (Fin 2)) R v (secondPivotRows i) := by
    simp [c]
  have he : ((pivotProjection twoStepBasis secondPivot R).comp N.subtype : N → _) =
      c ∘ s ∘ en := by
    funext v i
    exact (secondPivot_coefficients R v.val i).trans (hc _ _).symm
  change Function.Bijective (⇑((pivotProjection twoStepBasis secondPivot R).comp N.subtype)) ↔
    Function.Bijective s
  rw [he, c.bijective.of_comp_iff', Function.Bijective.of_comp_iff s en.bijective]

private theorem openFactors_iff_range {X Y : SchemeOver ℂ} {R : TestAlgebra ℂ}
    (j : Y ⟶ X) [IsOpenImmersion j.left] (q : Points X R) :
    (∃ r : Points Y R, r ≫ j = q) ↔ Set.range q.left ⊆ Set.range j.left := by
  constructor
  · rintro ⟨r, rfl⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨r.left x, rfl⟩
  · intro h
    let r := IsOpenImmersion.lift j.left q.left h
    have hr : r ≫ j.left = q.left := IsOpenImmersion.lift_fac _ _ _
    exact ⟨Over.homMk r (by rw [← Over.w j, ← Category.assoc, hr, Over.w q]),
      Over.OverMorphism.ext hr⟩

private def graphChartOpen : incidenceScheme.left.Opens := by
  let G := grassmannianCharts twoStepBasis twoStepRank
  let j := G.chart secondPivot
  have : IsOpenImmersion j.left := G.openChart secondPivot
  exact (terminalProjection ≫ twoStepSchemeInGrassmannian).left ⁻¹ᵁ j.left.opensRange

private theorem graphChart_iff (R : TestAlgebra ℂ) (q : Points incidenceScheme R) :
    (∃ r : Points (openOver graphChartOpen) R, r ≫ openOverInclusion graphChartOpen = q) ↔
      Function.Bijective (fun z : twoStepAffinePlane R (q ≫ terminalProjection) ↦ z.val.2) := by
  let G := grassmannianCharts twoStepBasis twoStepRank
  let C := G.chart secondPivot
  have : IsOpenImmersion C.left := G.openChart secondPivot
  rw [← terminalPlane_secondPivot,
    ← G.factor_iff secondPivot R ((q ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian)]
  have : IsOpenImmersion (openOverInclusion graphChartOpen).left :=
    inferInstanceAs (IsOpenImmersion graphChartOpen.ι)
  rw [openFactors_iff_range, openFactors_iff_range]
  change Set.range q.left ⊆ Set.range graphChartOpen.ι ↔ _
  rw [Scheme.Opens.range_ι]
  change (∀ x, x ∈ Set.range q.left →
    (terminalProjection ≫ twoStepSchemeInGrassmannian).left x ∈ Set.range C.left) ↔ _
  constructor
  · rintro h _ ⟨z, rfl⟩
    exact h (q.left z) ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h ⟨z, rfl⟩

private theorem graphChart_points_injective (R : TestAlgebra ℂ) :
    Function.Injective (fun q : Points (openOver graphChartOpen) R ↦
      q ≫ openOverInclusion graphChartOpen) := by
  let j := openOverInclusion graphChartOpen
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion graphChartOpen.ι)
  have : Mono j := Functor.mono_of_mono_map (Over.forget _) (show Mono j.left by infer_instance)
  intro a b h
  exact (cancel_mono j).mp h

private def graphChartParameters (R : TestAlgebra ℂ) :=
  Σ p : Points projectiveScheme R, NormalLinearMaps R p

private theorem graphParameters_unique {R : TestAlgebra ℂ}
    {q : Points incidenceScheme R} {a b : graphChartParameters R}
    (ha : q ≫ firstProjection = a.1)
    (hb : q ≫ firstProjection = b.1)
    (h : graphPlane a.2 = graphPlane b.2) : a = b := by
  obtain ⟨p, f⟩ := a
  obtain ⟨r, g⟩ := b
  change q ≫ firstProjection = p at ha
  change q ≫ firstProjection = r at hb
  have hp := ha.symm.trans hb
  cases hp
  exact congrArg (fun m ↦ (⟨p, m⟩ : graphChartParameters R))
    (graphPlane_injective p (a₁ := f) (a₂ := g) h)

private theorem graphChart_equiv (h : ProjectiveBundle) :
    ∃ e : ∀ R : TestAlgebra ℂ, Points (openOver graphChartOpen) R ≃ graphChartParameters R,
      ∀ (R : TestAlgebra ℂ) (q : Points (openOver graphChartOpen) R),
        (e R q).1 = q ≫ openOverInclusion graphChartOpen ≫ firstProjection ∧
        twoStepAffinePlane R (q ≫ openOverInclusion graphChartOpen ≫ terminalProjection) =
          graphPlane (e R q).2 := by
  let j := openOverInclusion graphChartOpen
  have hex (R : TestAlgebra ℂ) (a : graphChartParameters R) :
      ∃ q : Points (openOver graphChartOpen) R, (q ≫ j) ≫ firstProjection = a.1 ∧
        twoStepAffinePlane R ((q ≫ j) ≫ terminalProjection) = graphPlane a.2 := by
    obtain ⟨q, ⟨h₁, h₂⟩, _⟩ := incidenceGraph_existsUnique h R a.1 a.2
    have hproj : Function.Bijective (fun z : twoStepAffinePlane R (q ≫ terminalProjection) ↦ z.val.2) :=
      h₂.symm ▸ graphPlane_snd a.2
    obtain ⟨r, hr⟩ := (graphChart_iff R q).mpr hproj
    exact ⟨r, hr.symm ▸ h₁, hr.symm ▸ h₂⟩
  let F (R : TestAlgebra ℂ) (a : graphChartParameters R) := (hex R a).choose
  have hF (R : TestAlgebra ℂ) (a : graphChartParameters R) := (hex R a).choose_spec
  have hb (R : TestAlgebra ℂ) : Function.Bijective (F R) := by
    constructor
    · intro a b hEq
      have h₁ : ((F R a) ≫ j) ≫ firstProjection = a.1 := (hF R a).1
      have h₂ : ((F R b) ≫ j) ≫ firstProjection = b.1 := (hF R b).1
      rw [← hEq] at h₂
      have ha : twoStepAffinePlane R (((F R a) ≫ j) ≫ terminalProjection) = graphPlane a.2 :=
        (hF R a).2
      have hb : twoStepAffinePlane R (((F R b) ≫ j) ≫ terminalProjection) = graphPlane b.2 :=
        (hF R b).2
      rw [← hEq] at hb
      exact graphParameters_unique h₁ h₂ (ha.symm.trans hb)
    · intro q
      let y := q ≫ j
      have hp : Function.Bijective (fun z : twoStepAffinePlane R (y ≫ terminalProjection) ↦ z.val.2) :=
        (graphChart_iff R y).mp ⟨q, rfl⟩
      obtain ⟨hlo, hhi⟩ := affineIncidence_bounds h y
      obtain ⟨f, hf⟩ := graphPlane_exists _ hlo hhi hp
      let a : graphChartParameters R := ⟨y ≫ firstProjection, f⟩
      refine ⟨a, graphChart_points_injective R ?_⟩
      exact incidencePoints_ext (hF R a).1
        (twoStepAffinePlane_injective R ((hF R a).2.trans hf.symm))
  let e (R : TestAlgebra ℂ) := (Equiv.ofBijective (F R) (hb R)).symm
  refine ⟨e, ?_⟩
  intro R q
  have hq : F R (e R q) = q := (e R).symm_apply_apply q
  have hr : (F R (e R q) ≫ j) ≫ firstProjection = (e R q).1 ∧
      twoStepAffinePlane R ((F R (e R q) ≫ j) ≫ terminalProjection) = graphPlane (e R q).2 :=
    hF R (e R q)
  rw [hq] at hr
  exact ⟨hr.1.symm.trans (Category.assoc _ _ _), by rw [← Category.assoc]; exact hr.2⟩

private theorem planeChange_span {W : Type} [AddCommGroup W] [Module ℂ W]
    {d : ℕ} {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (P : Module.Grassmannian R (R ⊗[ℂ] W) (Module.finrank ℂ W - d)) :
    (Module.Grassmannian.map a.hom P).toSubmodule =
      Submodule.span T ((TensorProduct.map a.hom.toLinearMap LinearMap.id) ''
        (P.toSubmodule : Set (R ⊗[ℂ] W))) := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (a.hom.commutes x).symm)
  have ha : IsScalarTower.toAlgHom ℂ R T = a.hom := AlgHom.ext (fun _ ↦ rfl)
  have h := planeMap_eq_span (k := ℂ) (V := W) (R := R) (S := T) (d := d) P
  rw [ha] at h
  have he : (tensorExtension (k := ℂ) (R := R) (S := T) : R ⊗[ℂ] W → T ⊗[ℂ] W) =
      TensorProduct.map a.hom.toLinearMap LinearMap.id := by
    funext v
    refine TensorProduct.inductionOn (motive := fun v ↦
      tensorExtension (k := ℂ) (R := R) (S := T) (V := W) v =
        TensorProduct.map a.hom.toLinearMap LinearMap.id v) v ?_ ?_
    · intro r w
      rw [tensorExtension_tmul]
      rfl
    · intro v w hv hw
      rw [map_add, map_add, hv, hw]
  exact h.trans (congrArg (fun f : R ⊗[ℂ] W → T ⊗[ℂ] W ↦
    Submodule.span T (f '' (P.toSubmodule : Set (R ⊗[ℂ] W)))) he)

private theorem tautological_change {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (p : Points projectiveScheme R) :
    tautological T (mapPoints a p) =
      Submodule.span T (coefficientChange a '' (tautological R p : Set (Coefficients R))) := by
  let C := (grassmannianCharts projectiveBasis projectiveRank).affinePoints
  have h := congrArg (fun f ↦ f p) (C.hom.naturality a)
  change C.hom.app T (mapPoints a p) =
    Module.Grassmannian.map a.hom (C.hom.app R p) at h
  change (C.hom.app T (mapPoints a p)).toSubmodule = _
  rw [h]
  exact planeChange_span (d := 1) a (C.hom.app R p)

private def pairCoefficientChange {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    (Coefficients R × Coefficients R) →ₗ[ℂ] Coefficients T × Coefficients T :=
  (coefficientChange a).prodMap (coefficientChange a)

private theorem pairCoefficientChange_comp {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    (TensorProduct.prodRight ℂ T T V V).toLinearMap.restrictScalars ℂ ∘ₗ
      TensorProduct.map a.hom.toLinearMap (LinearMap.id : V × V →ₗ[ℂ] V × V) =
    (pairCoefficientChange a).comp
      ((TensorProduct.prodRight ℂ R R V V).toLinearMap.restrictScalars ℂ) := by
  apply TensorProduct.ext'
  intro r v
  simp [pairCoefficientChange, coefficientChange]

private theorem twoStepAffinePlane_change {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (p : Points twoStepScheme R) :
    twoStepAffinePlane T (mapPoints a p) =
      Submodule.span T (pairCoefficientChange a ''
        (twoStepAffinePlane R p : Set (Coefficients R × Coefficients R))) := by
  let C := (grassmannianCharts twoStepBasis twoStepRank).affinePoints
  let r := p ≫ twoStepSchemeInGrassmannian
  have h := congrArg (fun f ↦ f r) (C.hom.naturality a)
  change C.hom.app T (mapPoints a r) = Module.Grassmannian.map a.hom (C.hom.app R r) at h
  have hp : mapPoints a p ≫ twoStepSchemeInGrassmannian = mapPoints a r :=
    Category.assoc _ _ _
  change ((C.hom.app T (mapPoints a p ≫ twoStepSchemeInGrassmannian)).toSubmodule.map
    (TensorProduct.prodRight ℂ T T V V).toLinearMap) = _
  rw [hp, h, planeChange_span (d := 2), Submodule.map_span]
  congr 1
  change (TensorProduct.prodRight ℂ T T V V) '' ((TensorProduct.map a.hom.toLinearMap LinearMap.id) ''
    ((C.hom.app R r).toSubmodule : Set _)) = pairCoefficientChange a '' _
  rw [twoStepAffinePlane, Submodule.map_coe, Set.image_image, Set.image_image]
  exact congrArg (fun f : R ⊗[ℂ] (V × V) → Coefficients T × Coefficients T ↦
    f '' ((C.hom.app R r).toSubmodule : Set _)) (congrArg DFunLike.coe (pairCoefficientChange_comp a))

private theorem graphChange {R T : TestAlgebra ℂ} (a : R ⟶ T)
    {p : Points twoStepScheme R} {r : Points projectiveScheme R} {s : Points projectiveScheme T}
    {f : NormalLinearMaps R r} {g : NormalLinearMaps T s}
    (hf : twoStepAffinePlane R p = graphPlane f)
    (hg : twoStepAffinePlane T (mapPoints a p) = graphPlane g)
    (v : Coefficients R) :
    graphEndomorphism g (coefficientChange a v) = coefficientChange a (graphEndomorphism f v) := by
  have h : (graphEndomorphism f v, v) ∈ twoStepAffinePlane R p :=
    hf.symm ▸ (show (graphEndomorphism f v, v) ∈ graphPlane f from ⟨v, rfl⟩)
  have h' : (coefficientChange a (graphEndomorphism f v), coefficientChange a v) ∈ graphPlane g := by
    rw [← hg, twoStepAffinePlane_change]
    exact Submodule.subset_span ⟨_, h, rfl⟩
  obtain ⟨w, hw⟩ := h'
  have hw' : w = coefficientChange a v := congrArg Prod.snd hw
  exact hw' ▸ congrArg Prod.fst hw

private theorem coefficientCoordinates_change {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (v : Coefficients R) (i : Fin 2) :
    coordinates (Pi.basisFun ℂ (Fin 2)) T (coefficientChange a v) i =
      a.hom (coordinates (Pi.basisFun ℂ (Fin 2)) R v i) := by
  refine TensorProduct.inductionOn (motive := fun v ↦
    coordinates (Pi.basisFun ℂ (Fin 2)) T (coefficientChange a v) i =
      a.hom (coordinates (Pi.basisFun ℂ (Fin 2)) R v i)) v ?_ ?_
  · intro r w
    simp only [coefficientChange, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply]
    change ((Pi.basisFun ℂ (Fin 2)).baseChange T).repr (a.hom r ⊗ₜ[ℂ] w) i =
      a.hom (((Pi.basisFun ℂ (Fin 2)).baseChange R).repr (r ⊗ₜ[ℂ] w) i)
    rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul, map_smul]
  · intro v w hv hw
    simp only [map_add, Pi.add_apply, hv, hw]

private theorem lineCoefficient_exchange (h : ProjectiveBundle)
    {R : TestAlgebra ℂ} {p : Points projectiveScheme R} {v w : Coefficients R}
    (hv : v ∈ tautological R p) (hw : w ∈ tautological R p) (i : Fin 2) :
    coordinates (Pi.basisFun ℂ (Fin 2)) R v i • w =
      coordinates (Pi.basisFun ℂ (Fin 2)) R w i • v := by
  let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
  let S := tautological R p
  obtain ⟨d, hd⟩ := h.1 R p
  have hz : S.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hw
  have hdet := hd ⟨v, hv⟩ w
  change d (S.mkQ w) ⟨v, hv⟩ = volume R v w at hdet
  rw [hz, map_zero, LinearMap.zero_apply] at hdet
  have hev : c v 0 * c w 1 = c v 1 * c w 0 := sub_eq_zero.mp hdet.symm
  apply c.injective
  funext j
  change c (c v i • w) j = c (c w i • v) j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · exact mul_comm _ _
  · exact hev.trans (mul_comm _ _)
  · exact hev.symm.trans (mul_comm _ _)
  · exact mul_comm _ _

private theorem secondAffinePlane_rank (K' : Type) [Field K'] [Algebra ℂ K']
    (p : Points twoStepScheme (CommAlgCat.of ℂ K')) :
    Module.finrank K' (twoStepAffinePlane (CommAlgCat.of ℂ K') p) = 2 := by
  let R := CommAlgCat.of ℂ K'
  let N := (grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R
    (p ≫ twoStepSchemeInGrassmannian)
  let b := twoStepBasis.baseChange K'
  have hdim : Module.finrank K' (K' ⊗[ℂ] (V × V)) = 4 := by
    rw [Module.finrank_eq_card_basis b]
    decide
  have : Module.Finite K' (K' ⊗[ℂ] (V × V)) := Module.Finite.of_basis b
  have hn := N.rankAtStalk_eq (default : PrimeSpectrum K')
  have hfin : Module.finrank K' (K' ⊗[ℂ] (V × V) ⧸ N.toSubmodule) = 2 := by
    change Module.rankAtStalk (R := K') (K' ⊗[ℂ] (V × V) ⧸ N.toSubmodule) _ =
      Module.finrank ℂ (V × V) - 2 at hn
    rw [Module.rankAtStalk_eq_finrank_of_free] at hn
    simpa [V, Module.finrank_prod] using hn
  have htotal := N.toSubmodule.finrank_quotient_add_finrank
  change Module.finrank K' (K' ⊗[ℂ] (V × V) ⧸ N.toSubmodule) +
    Module.finrank K' N.toSubmodule = Module.finrank K' (K' ⊗[ℂ] (V × V)) at htotal
  rw [hfin, hdim] at htotal
  have h := (N.toSubmodule.equivMapOfInjective _ (TensorProduct.prodRight ℂ K' K' V V).injective).finrank_eq
  change Module.finrank K' N.toSubmodule = Module.finrank K' (twoStepAffinePlane R p) at h
  change Module.finrank K' (twoStepAffinePlane R p) = 2
  omega

private theorem firstProjection_zero_plane (K' : Type) [Field K'] [Algebra ℂ K']
    (p : Points twoStepScheme (CommAlgCat.of ℂ K'))
    (h : ∀ v ∈ twoStepAffinePlane (CommAlgCat.of ℂ K') p, (v : (K' ⊗[ℂ] V) × (K' ⊗[ℂ] V)).1 = 0) :
    twoStepAffinePlane (CommAlgCat.of ℂ K') p = (⊥ : Submodule K' (K' ⊗[ℂ] V)).prod ⊤ := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    exact ⟨h v hv, Submodule.mem_top⟩
  · let E := K' ⊗[ℂ] V
    let N := (⊥ : Submodule K' E).prod (⊤ : Submodule K' E)
    let e : N ≃ₗ[K'] E :=
      { toFun := fun z ↦ z.val.2
        invFun := fun y ↦ ⟨(0, y), Submodule.zero_mem _, Submodule.mem_top⟩
        left_inv := fun z ↦ Subtype.ext (Prod.ext (show z.val.1 = 0 from z.property.1).symm rfl)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hf : Module.finrank K' E = 2 := by
      rw [Module.finrank_eq_card_basis (projectiveBasis.baseChange K')]
      decide
    exact (e.finrank_eq.trans (hf.trans (secondAffinePlane_rank K' p).symm)).le

private theorem firstPlane_is_image (h : ProjectiveBundle)
    {x : Points twoStepScheme complexAlgebra} (hx : ScalarTerminalPoint x)
    {R : TestAlgebra ℂ} (q : Points incidenceScheme R)
    (hq : pointLocation x ∉ Set.range (q ≫ terminalProjection).left) :
    tautological R (q ≫ firstProjection) =
      (twoStepAffinePlane R (q ≫ terminalProjection)).map
        (LinearMap.fst R (Coefficients R) (Coefficients R)) := by
  let S := tautological R (q ≫ firstProjection)
  let P := twoStepAffinePlane R (q ≫ terminalProjection)
  let L := P.map (LinearMap.fst R (Coefficients R) (Coefficients R))
  let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
  have hL : L ≤ S := by
    rintro v ⟨w, hw, rfl⟩
    exact ((affineIncidence_bounds h q).2 hw).1
  let I : Ideal R := Ideal.span {r | ∃ v ∈ L, ∃ i : Fin 2, c v i = r}
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    have : M.IsMaximal := hM
    let : Field (R ⧸ M) := Ideal.Quotient.field M
    let T : TestAlgebra ℂ := CommAlgCat.of ℂ (R ⧸ M)
    let a : R ⟶ T := CommAlgCat.ofHom (Ideal.Quotient.mkₐ ℂ M)
    have hz (v : Coefficients R) (hv : v ∈ L) : coefficientChange a v = 0 := by
      let c' := coordinates (Pi.basisFun ℂ (Fin 2)) T
      apply c'.injective
      funext i
      change c' (coefficientChange a v) i = c' 0 i
      rw [coefficientCoordinates_change, map_zero, Pi.zero_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hIM (Ideal.subset_span ⟨v, hv, i, rfl⟩))
    let p := q ≫ terminalProjection
    have hzero (v : Coefficients T × Coefficients T)
        (hv : v ∈ twoStepAffinePlane T (mapPoints a p)) : v.1 = 0 := by
      have hh : twoStepAffinePlane T (mapPoints a p) ≤
          (LinearMap.fst T (Coefficients T) (Coefficients T)).ker := by
        rw [twoStepAffinePlane_change, Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        exact hz w.1 (Submodule.mem_map_of_mem hw)
      exact hh hv
    have he := firstProjection_zero_plane (R ⧸ M) (mapPoints a p) hzero
    have heq : mapPoints a p = toComplexPoint ((testSpec ℂ).obj (op T)) ≫ x :=
      twoStepAffinePlane_injective T (he.trans (scalarAffinePlane x hx T).symm)
    have hne' : pointLocation x ∈ Set.range p.left := by
      let z : ((testSpec ℂ).obj (op T)).left := (default : PrimeSpectrum (R ⧸ M))
      have hcom : ((testSpec ℂ).map a.op ≫ p).left z =
          (toComplexPoint ((testSpec ℂ).obj (op T)) ≫ x).left z :=
        congrArg (fun f : Points twoStepScheme T ↦ f.left z) heq
      refine ⟨((testSpec ℂ).map a.op).left z, hcom.trans ?_⟩
      change x.left ((toComplexPoint ((testSpec ℂ).obj (op T))).left z) = pointLocation x
      have : Subsingleton complexPointScheme.left :=
        inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
      exact congrArg (fun t : complexPointScheme.left ↦ x.left t) (Subsingleton.elim _ _)
    exact hq hne'
  apply le_antisymm _ hL
  intro v hv
  have hspan : I ≤ L.comap (LinearMap.toSpanSingleton R (Coefficients R) v) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨w, hw, i, rfl⟩
    change c w i • v ∈ L
    rw [lineCoefficient_exchange h (hL hw) hv i]
    exact L.smul_mem _ hw
  have h1 : (1 : R) ∈ I := hI.symm ▸ Submodule.mem_top
  have hv' := hspan h1
  change (1 : R) • v ∈ L at hv'
  simpa only [one_smul] using hv'

private theorem terminalProjection_surjective {x : Points twoStepScheme complexAlgebra}
    (hx : ScalarTerminalPoint x) (hproper : IsProper terminalProjection.left) :
    Surjective terminalProjection.left := by
  have : LocallyOfFiniteType twoStepScheme.hom := twoStepLocallyFiniteType
  have hclosed : IsClosed (Set.range terminalProjection.left) :=
    terminalProjection.left.isClosedMap.isClosed_range
  have hd := complexPoints_dense twoStepScheme
  have hs : Set.range (pointLocation : Points twoStepScheme complexAlgebra → twoStepScheme.left) ⊆
      Set.range terminalProjection.left := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := terminalProjection_surjective_complex x hx p
    exact ⟨pointLocation q, rfl⟩
  have he : closure (Set.range (pointLocation : Points twoStepScheme complexAlgebra →
      twoStepScheme.left)) ⊆ Set.range terminalProjection.left := closure_minimal hs hclosed
  rw [hd.closure_eq] at he
  exact ⟨fun y ↦ he (Set.mem_univ y)⟩

private theorem tautological_injective (R : TestAlgebra ℂ) :
    Function.Injective (tautological R) := by
  intro p q h
  apply ((grassmannianCharts projectiveBasis projectiveRank).affinePoints.app R).toEquiv.injective
  exact Module.Grassmannian.ext h

private theorem factors_away_scalar {R : TestAlgebra ℂ} {U : twoStepScheme.left.Opens}
    {x : Points twoStepScheme complexAlgebra} (hU : (U : Set twoStepScheme.left) = {pointLocation x}ᶜ)
    (p : Points (openOver U) R) :
    pointLocation x ∉ Set.range (p ≫ openOverInclusion U).left := by
  rintro ⟨z, hz⟩
  have h := (p.left z).property
  change (p.left z).val = pointLocation x at hz
  change (p.left z).val ∈ (U : Set twoStepScheme.left) at h
  rw [hz, hU] at h
  exact h rfl

private theorem restrictedTerminal_mono (h : ProjectiveBundle)
    {x : Points twoStepScheme complexAlgebra} (hx : ScalarTerminalPoint x)
    {U : twoStepScheme.left.Opens} (hU : (U : Set twoStepScheme.left) = {pointLocation x}ᶜ) :
    Mono (pullback.snd terminalProjection (openOverInclusion U)) := by
  let j := openOverInclusion U
  let F := pullback.snd terminalProjection j
  let i := pullback.fst terminalProjection j
  have hp : i ≫ terminalProjection = F ≫ j := pullback.condition
  constructor
  intro Z a b hab
  apply hom_ext_on_affines
  intro R p
  let A := (p ≫ a) ≫ i
  let B := (p ≫ b) ≫ i
  let C := (p ≫ a) ≫ F
  have hA : A ≫ terminalProjection = C ≫ j :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ (p ≫ a) ≫ f) hp).trans (Category.assoc _ _ _).symm)
  have hab' : a ≫ F = b ≫ F := hab
  have hC : (p ≫ b) ≫ F = C :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ p ≫ f) hab'.symm).trans (Category.assoc _ _ _).symm)
  have hB : B ≫ terminalProjection = C ≫ j := by
    dsimp [B]
    rw [Category.assoc, hp, ← Category.assoc, hC]
  have hAn : pointLocation x ∉ Set.range (A ≫ terminalProjection).left :=
    hA.symm ▸ factors_away_scalar hU C
  have hBn : pointLocation x ∉ Set.range (B ≫ terminalProjection).left :=
    hB.symm ▸ factors_away_scalar hU C
  have hAB : A = B := by
    apply incidencePoints_ext _ (hA.trans hB.symm)
    apply tautological_injective R
    rw [firstPlane_is_image h hx A hAn, firstPlane_is_image h hx B hBn, hA, hB]
  exact pullback.hom_ext hAB hC.symm

private theorem restrictedTerminal_iso (h : ProjectiveBundle) (hg : SurfaceGeometry)
    {x : Points twoStepScheme complexAlgebra} (hx : ScalarTerminalPoint x)
    {U : twoStepScheme.left.Opens} (hU : (U : Set twoStepScheme.left) = {pointLocation x}ᶜ) :
    IsIso (pullback.snd terminalProjection (openOverInclusion U)) := by
  let j := openOverInclusion U
  let F := pullback.snd terminalProjection j
  have hpb := (IsPullback.of_hasPullback terminalProjection j).map (Over.forget _)
  have : Mono F := restrictedTerminal_mono h hx hU
  have : Mono F.left := Over.mono_left_of_mono F
  have : IsProper F.left := MorphismProperty.of_isPullback (P := @IsProper) hpb hg.2.2
  have : IsClosedImmersion F.left :=
    (IsClosedImmersion.iff_isProper_and_mono F.left).mpr ⟨inferInstance, inferInstance⟩
  have : Surjective F.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb (terminalProjection_surjective hx hg.2.2)
  have : IsReduced (openOver U).left := by
    have : IsReduced twoStepScheme.left := LatticeModels.reducedClosure_reduced _ _
    exact isReduced_of_isOpenImmersion U.ι
  have : IsIso F.left := isIso_of_isClosedImmersion_of_surjective F.left
  have : IsIso ((Over.forget _).map F) := ‹IsIso F.left›
  exact isIso_of_reflects_iso F (Over.forget _)

set_option linter.unusedVariables false in
theorem openOrbitIsomorphism_conditional
    (minusculeOrbit : MinusculeOrbit)
    (_minusculeProjective : MinusculeProjective)
    (_smallSchubertSchemes : SmallSchubertSchemes)
    (twoStepOrbits : TwoStepOrbits)
    (_twoStepStableModel : TwoStepStableModel)
    (_firstLatticeQuotient : FirstLatticeQuotient)
    (_flagJetAction : FlagJetAction)
    (_latticeIncidence : LatticeIncidence)
    (projectiveBundle : ProjectiveBundle)
    (surfaceGeometry : SurfaceGeometry)
    (twistedFlags : TwistedFlags) : OpenOrbitIsomorphism := by
  obtain ⟨x, hx⟩ := scalarTerminalPoint_exists
  obtain ⟨U, hU, horbit⟩ := scalarComplement twoStepOrbits x hx
  refine ⟨x, U, hx, hU, horbit, ?_⟩
  dsimp only
  let j := openOverInclusion U
  let F := pullback.snd terminalProjection j
  let i := pullback.fst terminalProjection j
  have : IsIso F := restrictedTerminal_iso projectiveBundle surfaceGeometry hx hU
  let e := asIso F
  have h (R : TestAlgebra ℂ) (p : Points (openOver U) R) :
      tautological R (p ≫ e.inv ≫ i ≫ firstProjection) =
        (twoStepAffinePlane R (p ≫ j)).map (LinearMap.fst R (Coefficients R) (Coefficients R)) := by
    let q := p ≫ e.inv ≫ i
    have hf : i ≫ terminalProjection = F ≫ j := pullback.condition
    have ht : q ≫ terminalProjection = p ≫ j := by
      change (p ≫ e.inv ≫ i) ≫ terminalProjection = _
      rw [Category.assoc, Category.assoc, hf]
      change p ≫ e.inv ≫ e.hom ≫ j = _
      simp
    have hn : pointLocation x ∉ Set.range (q ≫ terminalProjection).left :=
      ht.symm ▸ factors_away_scalar hU p
    rw [← Category.assoc, ← Category.assoc]
    change tautological R ((p ≫ e.inv) ≫ i ≫ firstProjection) = _ at *
    exact ht ▸ firstPlane_is_image projectiveBundle hx q hn
  refine ⟨e, rfl, h, ?_⟩
  intro p L h₁ h₂
  obtain ⟨_, _, _, hflags⟩ := twistedFlags
  apply lattice_sum_of_firstPlane (minusculeOrbit.2 ⟨L.val.1, L.property.1⟩) (hflags L).2.1
  have he := congrArg (fun S ↦ S.map (TensorProduct.lid ℂ V).toLinearMap) (h complexAlgebra p)
  change firstPlane (p ≫ e.inv ≫ i ≫ firstProjection) = _ at he
  rw [complexFirstCoefficient, h₁, h₂] at he
  exact he

private theorem graphPlane_zero (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :
    graphPlane (0 : NormalLinearMaps R p) = (⊥ : Submodule R (Coefficients R)).prod ⊤ := by
  have h (v : Coefficients R) : graphEndomorphism (0 : NormalLinearMaps R p) v = 0 := by
    unfold graphEndomorphism
    simp
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h y, Submodule.mem_top⟩
  · rintro ⟨hz, _⟩
    exact ⟨z.2, Prod.ext ((h z.2).trans (show z.1 = 0 from hz).symm) rfl⟩

private theorem graphSection_lifts {s : projectiveScheme ⟶ incidenceScheme}
    {x : Points twoStepScheme complexAlgebra} (hs : ExceptionalSection x s) :
    ∃ sU : projectiveScheme ⟶ openOver graphChartOpen, sU ≫ openOverInclusion graphChartOpen = s := by
  let G := grassmannianCharts twoStepBasis twoStepRank
  let C := G.chart secondPivot
  have : IsOpenImmersion C.left := G.openChart secondPivot
  have hconst : toComplexPoint complexPointScheme = 𝟙 complexPointScheme :=
    (toComplexPoint_unique _ (𝟙 _)).symm
  have hP := scalarAffinePlane x hs.1 complexAlgebra
  change twoStepAffinePlane complexAlgebra (toComplexPoint complexPointScheme ≫ x) = _ at hP
  rw [hconst, Category.id_comp] at hP
  let p := grassmannianChartPoint projectiveBasis projectiveRank
    ⟨{(0, 0)}, by simp⟩ 0
  have hG : twoStepAffinePlane complexAlgebra x = graphPlane (0 : NormalLinearMaps complexAlgebra p) :=
    hP.trans (graphPlane_zero _ p).symm
  have hpivot : IsPivot twoStepBasis secondPivot complexAlgebra
      (G.affinePoints.hom.app complexAlgebra (x ≫ twoStepSchemeInGrassmannian)) :=
    (terminalPlane_secondPivot complexAlgebra x).mpr
      (hG.symm ▸ graphPlane_snd (0 : NormalLinearMaps complexAlgebra p))
  obtain ⟨y, hy⟩ := (G.factor_iff secondPivot complexAlgebra
    (x ≫ twoStepSchemeInGrassmannian)).mpr hpivot
  change y ≫ C = x ≫ twoStepSchemeInGrassmannian at hy
  let j := openOverInclusion graphChartOpen
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion graphChartOpen.ι)
  have hsx : s ≫ terminalProjection = toComplexPoint projectiveScheme ≫ x := hs.2.2.2.1.w
  have hterm : s ≫ terminalProjection ≫ twoStepSchemeInGrassmannian =
      (toComplexPoint projectiveScheme ≫ y) ≫ C := by
    rw [← Category.assoc, hsx, Category.assoc, ← hy, Category.assoc]
  have hrange : Set.range s.left ⊆ Set.range j.left := by
    change Set.range s.left ⊆ Set.range graphChartOpen.ι
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    change (s ≫ terminalProjection ≫ twoStepSchemeInGrassmannian).left v ∈ Set.range C.left
    rw [hterm]
    exact ⟨(toComplexPoint projectiveScheme ≫ y).left v, rfl⟩
  let l := IsOpenImmersion.lift j.left s.left hrange
  have hl : l ≫ j.left = s.left := IsOpenImmersion.lift_fac _ _ _
  exact ⟨Over.homMk l (by rw [← Over.w j, ← Category.assoc, hl, Over.w s]),
    Over.OverMorphism.ext hl⟩

private theorem graphSection_zero {s : projectiveScheme ⟶ incidenceScheme}
    {x : Points twoStepScheme complexAlgebra} (hs : ExceptionalSection x s)
    (sU : projectiveScheme ⟶ openOver graphChartOpen)
    (hsU : sU ≫ openOverInclusion graphChartOpen = s)
    (e : ∀ R : TestAlgebra ℂ, Points (openOver graphChartOpen) R ≃ graphChartParameters R)
    (he : ∀ (R : TestAlgebra ℂ) (q : Points (openOver graphChartOpen) R),
      (e R q).1 = q ≫ openOverInclusion graphChartOpen ≫ firstProjection ∧
      twoStepAffinePlane R (q ≫ openOverInclusion graphChartOpen ≫ terminalProjection) =
        graphPlane (e R q).2) :
    ∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R), e R (p ≫ sU) = ⟨p, 0⟩ := by
  intro R p
  let q := p ≫ s
  obtain ⟨h₁, h₂⟩ := he R (p ≫ sU)
  rw [← Category.assoc (p ≫ sU), Category.assoc p sU, hsU] at h₁ h₂
  have hp : q ≫ firstProjection = p := by
    change (p ≫ s) ≫ firstProjection = p
    rw [Category.assoc, hs.2.2.1, Category.comp_id]
  have hx : q ≫ terminalProjection = toComplexPoint ((testSpec ℂ).obj (op R)) ≫ x := by
    change (p ≫ s) ≫ terminalProjection = _
    rw [Category.assoc, hs.2.2.2.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (toComplexPoint_unique _ _)
  apply graphParameters_unique (q := q) h₁.symm hp
  exact h₂.symm.trans (hx ▸ (scalarAffinePlane x hs.1 R).trans (graphPlane_zero R p).symm)

universe u

private def ringQuotient {A : CommRingCat.{u}} (I : Ideal A) : A ⟶ CommRingCat.of (A ⧸ I) :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)

private def quotientChange {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) :
    CommRingCat.of (A ⧸ I) ⟶ CommRingCat.of (B ⧸ I.map f.hom) :=
  CommRingCat.ofHom (Ideal.quotientMap _ f.hom Ideal.le_comap_map)

private theorem quotientChange_pushout {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) :
    IsPushout f (ringQuotient I) (ringQuotient (I.map f.hom)) (quotientChange f I) := by
  let g := ringQuotient I
  let u := ringQuotient (I.map f.hom)
  let v := quotientChange f I
  have w : f ≫ u = g ≫ v := by
    apply CommRingCat.hom_ext
    apply DFunLike.ext
    intro x
    rfl
  let desc (s : PushoutCocone f g) : CommRingCat.of (B ⧸ I.map f.hom) ⟶ s.pt :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (by
      have hl : I ≤ (RingHom.ker s.inl.hom).comap f.hom := by
        intro x hx
        change s.inl.hom (f.hom x) = 0
        have e := congrArg (fun k : A ⟶ s.pt ↦ k.hom x) s.condition
        change s.inl.hom (f.hom x) = s.inr.hom (Ideal.Quotient.mk I x) at e
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at e
        exact e
      exact fun _ h ↦ Ideal.map_le_iff_le_comap.mpr hl h))
  refine IsPushout.of_isColimit (c := PushoutCocone.mk u v w)
    (PushoutCocone.IsColimit.mk w desc ?_ ?_ ?_)
  · intro s
    apply CommRingCat.hom_ext
    apply DFunLike.ext
    intro x
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply DFunLike.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := congrArg (fun k : A ⟶ s.pt ↦ k.hom y) s.condition
    exact h
  · intro s m h _
    apply CommRingCat.hom_ext
    apply DFunLike.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun k : B ⟶ s.pt ↦ k.hom y) h

private theorem ringQuotient_pullback_ker {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) :
    (Spec.map (ringQuotient I)).ker.comap (Spec.map f) =
      (Spec.map (ringQuotient (I.map f.hom))).ker := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (quotientChange_pushout f I)
  have : IsClosedImmersion (Spec.map (ringQuotient I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _,
    ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

private theorem specMap_ker_top {A B : CommRingCat.{u}} (ψ : A ⟶ B) :
    (Spec.map ψ).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker ψ.hom).comap (Scheme.ΓSpecIso A).hom.hom := by
  rw [Scheme.ker_of_isAffine]
  have ht : (Scheme.IdealSheafData.ofIdealTop (RingHom.ker (Spec.map ψ).appTop.hom)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = RingHom.ker (Spec.map ψ).appTop.hom :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply _
  rw [ht]
  let e := (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv
  calc
    _ = RingHom.ker (e.toRingHom.comp (Spec.map ψ).appTop.hom) :=
      (RingHom.ker_equiv_comp _ e).symm
    _ = RingHom.ker (ψ.hom.comp (Scheme.ΓSpecIso A).hom.hom) :=
      congrArg (fun f ↦ RingHom.ker (CommRingCat.Hom.hom f)) (Scheme.ΓSpecIso_naturality ψ)
    _ = _ := RingHom.comap_ker _ _ |>.symm

private theorem ringQuotient_ker_idealTop {A : CommRingCat.{u}} (I : Ideal A) :
    (Spec.map (ringQuotient I)).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.comap (Scheme.ΓSpecIso A).hom.hom := by
  rw [specMap_ker_top, show RingHom.ker (ringQuotient I).hom = I from Ideal.mk_ker]

private theorem comapRingEquiv_pow {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal B) (n : ℕ) :
    (I ^ n).comap (e : A →+* B) = I.comap (e : A →+* B) ^ n := by
  have hc (J : Ideal B) : J.comap (e : A →+* B) = J.map (e.symm : B →+* A) :=
    Ideal.comap_symm e.symm
  rw [hc, hc, Ideal.map_pow]

private theorem openComap_pow {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  exact comapRingEquiv_pow e.symm _ n

private theorem idealSheaf_ext_on_affines {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, I.comap U.2.fromSpec = J.comap U.2.fromSpec) : I = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let W : (Spec Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have h' := congrArg (fun K : (Spec Γ(X, U.1)).IdealSheafData ↦ K.ideal W) (h U)
  change (I.comap f).ideal W = (J.comap f).ideal W at h'
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h'
  have hu : f ''ᵁ W.1 = U.1 :=
    (Scheme.Hom.image_top_eq_opensRange f).trans U.2.opensRange_fromSpec
  let e := (f.appIso W).commRingCatIsoToRingEquiv
  have he : Function.Surjective (f.appIso W).inv.hom := e.symm.surjective
  have hu' : (⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ : X.affineOpens) = U :=
    Subtype.ext hu
  exact hu' ▸ (Ideal.comap_injective_of_surjective _ he) h'

private theorem quotientComap_pow {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (I : Ideal A) (n : ℕ) :
    ((Spec.map (ringQuotient I)).ker.comap f) ^ n =
      (Spec.map (ringQuotient (I ^ n))).ker.comap f := by
  apply idealSheaf_ext_on_affines
  intro U
  let i := U.2.fromSpec
  have : IsOpenImmersion i := U.2.isOpenImmersion_fromSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  change (((Spec.map (ringQuotient I)).ker.comap f) ^ n).comap i =
    ((Spec.map (ringQuotient (I ^ n))).ker.comap f).comap i
  rw [openComap_pow, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hφ,
    ringQuotient_pullback_ker, ringQuotient_pullback_ker, Ideal.map_pow]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ringQuotient_ker_idealTop]
  let e := (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U.1))).commRingCatIsoToRingEquiv
  exact (comapRingEquiv_pow e _ n).symm

private theorem closedFactors_iff_ker {X Y : SchemeOver ℂ} {R : TestAlgebra ℂ}
    (i : Y ⟶ X) [IsClosedImmersion i.left] (q : Points X R) :
    (∃ r : Points Y R, r ≫ i = q) ↔ i.left.ker ≤ q.left.ker := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.left.le_ker_comp i.left
  · intro h
    let r := IsClosedImmersion.lift i.left q.left h
    have hr : r ≫ i.left = q.left := IsClosedImmersion.lift_fac _ _ _
    exact ⟨Over.homMk r (by rw [← Over.w i, ← Category.assoc, hr, Over.w q]),
      Over.OverMorphism.ext hr⟩

private theorem twoStepTensor_coefficients (R : TestAlgebra ℂ) (v : R ⊗[ℂ] (V × V))
    (i j : Fin 2) :
    coordinates twoStepBasis R v (i, j) =
      if j = 0 then
        coordinates (Pi.basisFun ℂ (Fin 2)) R ((TensorProduct.prodRight ℂ R R V V) v).1 i
      else coordinates (Pi.basisFun ℂ (Fin 2)) R ((TensorProduct.prodRight ℂ R R V V) v).2 i := by
  have h (j : Fin 2) : coordinates twoStepBasis R v (i, j) =
      coordinates (Pi.basisFun ℂ (Fin 2)) R
        (if j = 0 then ((TensorProduct.prodRight ℂ R R V V) v).1
         else ((TensorProduct.prodRight ℂ R R V V) v).2) i := by
    refine TensorProduct.inductionOn (motive := fun v ↦ coordinates twoStepBasis R v (i, j) =
      coordinates (Pi.basisFun ℂ (Fin 2)) R
        (if j = 0 then ((TensorProduct.prodRight ℂ R R V V) v).1
         else ((TensorProduct.prodRight ℂ R R V V) v).2) i) v ?_ ?_
    · intro r w
      simp only [TensorProduct.prodRight_tmul]
      split_ifs with hj
      · change (twoStepBasis.baseChange R).repr (r ⊗ₜ[ℂ] w) (i, j) =
          ((Pi.basisFun ℂ (Fin 2)).baseChange R).repr (r ⊗ₜ[ℂ] w.1) i
        rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul, twoStepBasis_repr]
        simp [hj]
      · change (twoStepBasis.baseChange R).repr (r ⊗ₜ[ℂ] w) (i, j) =
          ((Pi.basisFun ℂ (Fin 2)).baseChange R).repr (r ⊗ₜ[ℂ] w.2) i
        rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul, twoStepBasis_repr]
        simp [hj]
    · intro v w hv hw
      by_cases hj : j = 0 <;>
        simp only [hj, ite_true, ite_false, map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add] at hv hw ⊢ <;>
        rw [hv, hw]
  by_cases hj : j = 0 <;> simpa only [hj, ite_true, ite_false] using h j

private def firstPivotRows : Outside secondPivot ≃ Fin 2 where
  toFun i := i.val.1
  invFun i := ⟨(i, 0), by rw [secondPivot_mem]; change ¬(0 : Fin 2) = 1; decide⟩
  left_inv i := by
    apply Subtype.ext
    change (i.val.1, (0 : Fin 2)) = i.val
    have hi := i.property
    rw [secondPivot_mem] at hi
    have hz : i.val.2 = 0 := by
      have h : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
      exact (h i.val.2).resolve_right hi
    exact Prod.ext (by rfl) hz.symm
  right_inv _ := rfl

private theorem graphMatrixOfPoint_eq {R : TestAlgebra ℂ} {q : Points twoStepScheme R}
    {p : Points projectiveScheme R} (f : NormalLinearMaps R p)
    (y : Points (chartScheme (k := ℂ) secondPivot) R)
    (hy : y ≫ (grassmannianCharts twoStepBasis twoStepRank).chart secondPivot =
      q ≫ twoStepSchemeInGrassmannian)
    (hf : twoStepAffinePlane R q = graphPlane f) (i : Outside secondPivot)
    (j : Inside secondPivot) :
    let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
    matrixOfPoint secondPivot R y i j =
      c (graphEndomorphism f (c.symm (Pi.single (secondPivotRows j) 1))) (firstPivotRows i) := by
  let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
  let N := (grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R
    (q ≫ twoStepSchemeInGrassmannian)
  let A := matrixOfPoint secondPivot R y
  let u : Inside secondPivot → R := Pi.single j 1
  let z := graphInclusion twoStepBasis secondPivot R A u
  let z' := (TensorProduct.prodRight ℂ R R V V) z
  have hN : N.toSubmodule = (graphInclusion twoStepBasis secondPivot R A).range := by
    dsimp only [N]
    rw [← hy]
    exact (grassmannianCharts twoStepBasis twoStepRank).coordinates_eq secondPivot R y
  have hz' : z' ∈ graphPlane f := by
    rw [← hf]
    exact ⟨z, hN.symm ▸ (show z ∈ (graphInclusion twoStepBasis secondPivot R A).range from ⟨u, rfl⟩),
      rfl⟩
  have hgraph : graphEndomorphism f z'.2 = z'.1 := by
    obtain ⟨v, hv⟩ := hz'
    have h₁ : v = z'.2 := congrArg Prod.snd hv
    have h₂ : graphEndomorphism f v = z'.1 := congrArg Prod.fst hv
    exact h₁ ▸ h₂
  have H (a : Fin 2 × Fin 2) :
      coordinates twoStepBasis R z a = graphColumns secondPivot R A u a := by
    change coordinates twoStepBasis R ((coordinates twoStepBasis R).symm _) a = _
    rw [LinearEquiv.apply_symm_apply]
  have hsecond : z'.2 = c.symm (Pi.single (secondPivotRows j) 1) := by
    apply c.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    let j' := secondPivotRows.symm k
    have hcoord := H j'.val
    change coordinates twoStepBasis R z (k, 1) = graphColumns secondPivot R A u (k, 1) at hcoord
    rw [twoStepTensor_coefficients] at hcoord
    have hm : (k, (1 : Fin 2)) ∈ secondPivot.val := (secondPivot_mem _).mpr rfl
    have hjne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hjne, ite_false, graphColumns, LinearMap.pi_apply, dite_eq_left hm,
      LinearMap.proj_apply] at hcoord
    change c z'.2 k = u j' at hcoord
    refine hcoord.trans ?_
    simp only [u, Pi.single_apply]
    have hi : j' = j ↔ k = secondPivotRows j := by
      rw [← show secondPivotRows j' = k from secondPivotRows.apply_symm_apply k]
      exact secondPivotRows.injective.eq_iff.symm
    by_cases hk : j' = j
    · rw [ite_eq_left hk, ite_eq_left (hi.mp hk)]
    · rw [ite_eq_right hk, ite_eq_right (fun h ↦ hk (hi.mpr h))]
  have hfirst : c z'.1 (firstPivotRows i) = A i j := by
    have hi : i.val.2 = 0 := by
      have hh : (firstPivotRows.symm (firstPivotRows i)).val.2 = i.val.2 :=
        congrArg (fun k : Outside secondPivot ↦ k.val.2) (firstPivotRows.symm_apply_apply i)
      exact hh.symm
    have hcoord := H i.val
    rw [show i.val = (i.val.1, i.val.2) from Prod.eta _, twoStepTensor_coefficients, hi] at hcoord
    simp only [ite_true] at hcoord
    change c z'.1 (firstPivotRows i) = graphColumns secondPivot R A u (i.val.1, 0) at hcoord
    refine hcoord.trans ?_
    have hp : (i.val.1, (0 : Fin 2)) = i.val := Prod.ext rfl hi.symm
    rw [hp]
    simp [graphColumns, i.property, Matrix.toLin'_apply, u]
  change A i j = c (graphEndomorphism f (c.symm (Pi.single (secondPivotRows j) 1))) (firstPivotRows i)
  rw [← hsecond, hgraph]
  exact hfirst.symm

private abbrev graphAffineChart := chartScheme (k := ℂ) secondPivot

private def graphAffineChartInclusion :
    graphAffineChart ⟶ (grassmannianCharts twoStepBasis twoStepRank).scheme :=
  (grassmannianCharts twoStepBasis twoStepRank).chart secondPivot

private theorem graphChartTerminal_exists :
    ∃ g : openOver graphChartOpen ⟶ graphAffineChart,
      g ≫ graphAffineChartInclusion =
        openOverInclusion graphChartOpen ≫ terminalProjection ≫ twoStepSchemeInGrassmannian := by
  let j := openOverInclusion graphChartOpen
  let C := graphAffineChartInclusion
  have : IsOpenImmersion C.left := (grassmannianCharts twoStepBasis twoStepRank).openChart secondPivot
  let f := j ≫ terminalProjection ≫ twoStepSchemeInGrassmannian
  have hf : Set.range f.left ⊆ Set.range C.left := by
    rintro _ ⟨z, rfl⟩
    exact z.property
  let g := IsOpenImmersion.lift C.left f.left hf
  have hg : g ≫ C.left = f.left := IsOpenImmersion.lift_fac _ _ _
  exact ⟨Over.homMk g (by rw [← Over.w C, ← Category.assoc, hg, Over.w f]),
    Over.OverMorphism.ext hg⟩

private theorem scalarPoint_inChart {x : Points twoStepScheme complexAlgebra}
    (hx : ScalarTerminalPoint x) :
    ∃ y : Points graphAffineChart complexAlgebra,
      y ≫ graphAffineChartInclusion = x ≫ twoStepSchemeInGrassmannian ∧
      matrixOfPoint secondPivot complexAlgebra y = 0 := by
  let p := grassmannianChartPoint projectiveBasis projectiveRank
    ⟨{(0, 0)}, by simp⟩ 0
  have h := scalarAffinePlane x hx complexAlgebra
  change twoStepAffinePlane complexAlgebra (toComplexPoint complexPointScheme ≫ x) = _ at h
  rw [← toComplexPoint_unique _ (𝟙 _), Category.id_comp] at h
  have hs : twoStepAffinePlane complexAlgebra x = graphPlane (0 : NormalLinearMaps complexAlgebra p) :=
    h.trans (graphPlane_zero _ p).symm
  obtain ⟨y, hy⟩ := ((grassmannianCharts twoStepBasis twoStepRank).factor_iff secondPivot complexAlgebra
    (x ≫ twoStepSchemeInGrassmannian)).mpr
    ((terminalPlane_secondPivot _ x).mpr (hs.symm ▸ graphPlane_snd (0 : NormalLinearMaps complexAlgebra p)))
  refine ⟨y, hy, ?_⟩
  ext i j
  rw [graphMatrixOfPoint_eq 0 y hy hs i j]
  simp [graphEndomorphism]

private theorem graphSection_pullback {s : projectiveScheme ⟶ incidenceScheme}
    {x : Points twoStepScheme complexAlgebra} (hs : ExceptionalSection x s)
    (sU : projectiveScheme ⟶ openOver graphChartOpen)
    (hsU : sU ≫ openOverInclusion graphChartOpen = s)
    (g : openOver graphChartOpen ⟶ graphAffineChart)
    (hg : g ≫ graphAffineChartInclusion =
      openOverInclusion graphChartOpen ≫ terminalProjection ≫ twoStepSchemeInGrassmannian)
    (y : Points graphAffineChart complexAlgebra)
    (hy : y ≫ graphAffineChartInclusion = x ≫ twoStepSchemeInGrassmannian) :
    IsPullback sU (toComplexPoint projectiveScheme) g y := by
  let j := openOverInclusion graphChartOpen
  let C := graphAffineChartInclusion
  have : IsOpenImmersion C.left := (grassmannianCharts twoStepBasis twoStepRank).openChart secondPivot
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion graphChartOpen.ι)
  have : Mono C := Functor.mono_of_mono_map (Over.forget _) (show Mono C.left by infer_instance)
  have : Mono j := Functor.mono_of_mono_map (Over.forget _) (show Mono j.left by infer_instance)
  let i := twoStepSchemeInGrassmannian
  have : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have : Mono i := Functor.mono_of_mono_map (Over.forget _) (show Mono i.left by infer_instance)
  have hs' := hs.2.2.2.1
  have hg' : g ≫ C = j ≫ terminalProjection ≫ i := hg
  have hy' : y ≫ C = x ≫ i := hy
  have hsU' : sU ≫ j = s := hsU
  have w : sU ≫ g = toComplexPoint projectiveScheme ≫ y := by
    apply (cancel_mono C).mp
    simp only [Category.assoc, hg', hy']
    rw [← Category.assoc sU j, hsU', ← Category.assoc s terminalProjection, hs'.w, Category.assoc]
  have hl (D : PullbackCone g y) : (D.fst ≫ j) ≫ terminalProjection = D.snd ≫ x := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, ← hg', ← hy']
    rw [← Category.assoc, ← Category.assoc, D.condition]
  refine IsPullback.of_isLimit (c := PullbackCone.mk sU (toComplexPoint projectiveScheme) w)
    (PullbackCone.IsLimit.mk w (fun D ↦ hs'.lift (D.fst ≫ j) D.snd (hl D)) ?_ ?_ ?_)
  · intro D
    apply (cancel_mono j).mp
    simp only [Category.assoc, hsU']
    exact hs'.lift_fst _ _ _
  · intro D
    exact hs'.lift_snd _ _ _
  · intro D m h₁ h₂
    apply hs'.hom_ext
    · calc
        m ≫ s = m ≫ sU ≫ j := congrArg (m ≫ ·) hsU'.symm
        _ = D.fst ≫ j := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) h₁)
        _ = _ := (hs'.lift_fst _ _ _).symm
    · rw [h₂, hs'.lift_snd]

private abbrev graphVariables := Outside secondPivot × Inside secondPivot
private abbrev graphAlgebra := MvPolynomial graphVariables ℂ

private def chartPointAlgebra (R : TestAlgebra ℂ) (y : Points graphAffineChart R) :
    graphAlgebra →ₐ[ℂ] R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of ℂ)).preimage y).unop.hom

private theorem chartPoint_spec (R : TestAlgebra ℂ) (y : Points graphAffineChart R) :
    y.left = Spec.map (CommRingCat.ofHom (chartPointAlgebra R y).toRingHom) :=
  (congrArg (fun f : Points graphAffineChart R ↦ f.left)
    ((algSpec.fullyFaithful (R := CommRingCat.of ℂ)).map_preimage y)).symm

private theorem chartIdeal_ker (y : Points graphAffineChart complexAlgebra)
    (hy : matrixOfPoint secondPivot complexAlgebra y = 0) :
    RingHom.ker (chartPointAlgebra complexAlgebra y).toRingHom =
      MvPolynomial.idealOfVars graphVariables ℂ := by
  let f := chartPointAlgebra complexAlgebra y
  let I := MvPolynomial.idealOfVars graphVariables ℂ
  have hf (i : graphVariables) : f (MvPolynomial.X i) = 0 :=
    congrArg (fun M : Matrix (Outside secondPivot) (Inside secondPivot) ℂ ↦ M i.1 i.2) hy
  apply le_antisymm
  · have hq : Ideal.Quotient.mkₐ ℂ I = (Algebra.ofId ℂ (graphAlgebra ⧸ I)).comp f := by
      ext i
      change Ideal.Quotient.mk I (MvPolynomial.X i) = algebraMap ℂ (graphAlgebra ⧸ I) (f (MvPolynomial.X i))
      rw [hf, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ ℂ I z = 0
    rw [hq, AlgHom.comp_apply]
    change f z = 0 at hz
    rw [hz, map_zero]
  · exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i)

open scoped Pointwise in
private theorem chartEntries_square (R : TestAlgebra ℂ) (p : Points graphAffineChart R) :
    (MvPolynomial.idealOfVars graphVariables ℂ)^2 ≤ RingHom.ker (chartPointAlgebra R p).toRingHom ↔
    ∀ (i k : Outside secondPivot) (j l : Inside secondPivot),
      matrixOfPoint secondPivot R p i j * matrixOfPoint secondPivot R p k l = 0 := by
  classical
  let S : Set graphAlgebra := Set.range MvPolynomial.X
  change (Ideal.span S)^2 ≤ _ ↔ _
  rw [pow_two, Ideal.span_mul_span, Ideal.span_le]
  constructor
  · intro h i k j l
    have hh := h (show MvPolynomial.X (i, j) * MvPolynomial.X (k, l) ∈ S * S from
      ⟨_, ⟨(i, j), rfl⟩, _, ⟨(k, l), rfl⟩, rfl⟩)
    change chartPointAlgebra R p (MvPolynomial.X (i, j) * MvPolynomial.X (k, l)) = 0 at hh
    exact (map_mul (chartPointAlgebra R p) _ _).symm.trans hh
  · rintro h _ ⟨_, ⟨⟨i, j⟩, rfl⟩, _, ⟨⟨k, l⟩, rfl⟩, rfl⟩
    change chartPointAlgebra R p (MvPolynomial.X (i, j) * MvPolynomial.X (k, l)) = 0
    exact (map_mul (chartPointAlgebra R p) _ _).trans (h i k j l)

private theorem graphFirstNeighbourhood {s : projectiveScheme ⟶ incidenceScheme}
    {x : Points twoStepScheme complexAlgebra} (hs : ExceptionalSection x s)
    (sU : projectiveScheme ⟶ openOver graphChartOpen)
    (hsU : sU ≫ openOverInclusion graphChartOpen = s)
    (R : TestAlgebra ℂ) (q : Points (openOver graphChartOpen) R)
    {p : Points projectiveScheme R} (f : NormalLinearMaps R p)
    (hf : twoStepAffinePlane R (q ≫ openOverInclusion graphChartOpen ≫ terminalProjection) =
      graphPlane f) :
    (∃ r : Points (firstNeighbourhood sU) R, r ≫ firstNeighbourhoodInclusion sU = q) ↔
      GraphEntriesSquareZero f := by
  obtain ⟨g, hg⟩ := graphChartTerminal_exists
  obtain ⟨y, hy, hZero⟩ := scalarPoint_inChart hs.1
  let A := CommRingCat.of graphAlgebra
  let I := MvPolynomial.idealOfVars graphVariables ℂ
  have hycl : IsClosedImmersion y.left := by
    have : Subsingleton complexPointScheme.left := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    exact isClosedImmersion_of_comp_eq_id _ _ (complexPoint_comp _ y)
  have : IsAffine graphAffineChart.left := inferInstanceAs (IsAffine (Spec A))
  have hyker : y.left.ker = (Spec.map (ringQuotient I)).ker := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [chartPoint_spec, specMap_ker_top, ringQuotient_ker_idealTop]
    exact congrArg (Ideal.comap (Scheme.ΓSpecIso A).hom.hom) (chartIdeal_ker _ hZero)
  have hpb := (graphSection_pullback hs sU hsU g hg y hy).map (Over.forget _)
  change IsPullback sU.left (toComplexPoint projectiveScheme).left g.left y.left at hpb
  have hker : sU.left.ker = y.left.ker.comap g.left := by
    rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hpower : sU.left.ker ^ 2 = (Spec.map (ringQuotient (I^2))).ker.comap g.left := by
    rw [hker, hyker, quotientComap_pow]
  have : IsClosedImmersion (firstNeighbourhoodInclusion sU).left := by
    change IsClosedImmersion (sU.left.ker ^ 2).subschemeι
    infer_instance
  rw [closedFactors_iff_ker]
  change ((sU.left.ker ^ 2).subschemeι).ker ≤ q.left.ker ↔ _
  rw [Scheme.IdealSheafData.ker_subschemeι, hpower]
  let z := q ≫ g
  let J := (Spec.map (ringQuotient (A := A) (I ^ 2))).ker
  have hAdj : J.comap g.left ≤ q.left.ker ↔ J ≤ q.left.ker.map g.left :=
    Scheme.IdealSheafData.le_map_iff_comap_le.symm
  have hzker : q.left.ker.map g.left = z.left.ker := Scheme.IdealSheafData.map_ker _ _
  refine hAdj.trans ?_
  rw [hzker]
  have hEq : ((Spec.map (ringQuotient (I ^ 2))).ker ≤ z.left.ker) ↔
      I^2 ≤ RingHom.ker (chartPointAlgebra R z).toRingHom := by
    let U : (Spec A).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    have h : _ ↔ (Spec.map (ringQuotient (I^2))).ker.ideal U ≤ z.left.ker.ideal U :=
      ⟨fun H ↦ H U, fun H ↦ Scheme.IdealSheafData.le_of_isAffine H⟩
    rw [h, ringQuotient_ker_idealTop, chartPoint_spec, specMap_ker_top]
    exact Ideal.comap_le_comap_iff_of_surjective _ (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.surjective _ _
  change ((Spec.map (ringQuotient (I ^ 2))).ker ≤ z.left.ker) ↔ _
  rw [hEq, chartEntries_square]
  have hz : z ≫ (grassmannianCharts twoStepBasis twoStepRank).chart secondPivot =
      (q ≫ openOverInclusion graphChartOpen ≫ terminalProjection) ≫ twoStepSchemeInGrassmannian := by
    change (q ≫ g) ≫ graphAffineChartInclusion = _
    rw [Category.assoc, hg]
    simp only [Category.assoc]
  simp only [graphMatrixOfPoint_eq f z hz hf, GraphEntriesSquareZero]
  constructor
  · intro H i j k l
    simpa only [Equiv.apply_symm_apply] using
      H (firstPivotRows.symm i) (firstPivotRows.symm k)
        (secondPivotRows.symm j) (secondPivotRows.symm l)
  · intro H i k j l
    exact H (firstPivotRows i) (secondPivotRows j) (firstPivotRows k) (secondPivotRows l)

set_option linter.unusedVariables false in
theorem exceptionalNormalBundle_conditional
    (_minusculeOrbit : MinusculeOrbit)
    (_minusculeProjective : MinusculeProjective)
    (_smallSchubertSchemes : SmallSchubertSchemes)
    (_twoStepOrbits : TwoStepOrbits)
    (_twoStepStableModel : TwoStepStableModel)
    (_firstLatticeQuotient : FirstLatticeQuotient)
    (_flagJetAction : FlagJetAction)
    (_latticeIncidence : LatticeIncidence)
    (projectiveBundle : ProjectiveBundle)
    (_surfaceGeometry : SurfaceGeometry)
    (_twistedFlags : TwistedFlags) : ExceptionalNormalBundle := by
  obtain ⟨x, s, hs⟩ := exceptionalSection_exists
  obtain ⟨sU, hsU⟩ := graphSection_lifts hs
  obtain ⟨e, he⟩ := graphChart_equiv projectiveBundle
  refine ⟨x, s, hs, graphChartOpen, sU, hsU, graphChart_iff, e, he,
    graphSection_zero hs sU hsU e he, ?_, ?_, normalLinearMaps_tensor projectiveBundle⟩
  · intro R T a q v
    have hx := (he T (mapPoints a q)).2
    have hy : mapPoints a (q ≫ openOverInclusion graphChartOpen ≫ terminalProjection) =
        mapPoints a q ≫ openOverInclusion graphChartOpen ≫ terminalProjection :=
      (Category.assoc _ _ _).symm
    rw [← hy] at hx
    exact graphChange a (he R q).2 hx v
  · intro R q
    exact graphFirstNeighbourhood hs sU hsU R q (e R q).2 (he R q).2

section ScalarCodimension

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open scoped Matrix nonZeroDivisors

set_option maxRecDepth 1200 in
private theorem shiftCoordinates (i j k l : Fin 2) :
    operatorInCoordinates twoStepBasis shift (i, j) (k, l) =
      if j = 0 then 0 else (if (i, (0 : Fin 2)) = (k, l) then 1 else 0) := by
  let e : Fin 2 × Fin 2 → ℂ := Pi.single (k, l) 1
  let v := twoStepBasis.equivFun.symm e
  have hv : v.1 i = (if (i, (0 : Fin 2)) = (k, l) then 1 else 0) := by
    have h := congrFun (twoStepBasis.equivFun.apply_symm_apply e) (i, 0)
    change twoStepBasis.repr v (i, 0) = _ at h
    simpa only [twoStepBasis_repr, ite_true, e, Pi.single_apply] using h
  rw [operatorInCoordinates, LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply]
  change twoStepBasis.repr (shift v) (i, j) = _
  rw [twoStepBasis_repr]
  change (if j = 0 then 0 else v.1 i) = _
  rw [hv]

private theorem shiftMulGraphMatrix {R : Type} [CommRing R] (f : ℂ →+* R)
    (A : Matrix (Outside secondPivot) (Inside secondPivot) R) (i j : Fin 2)
    (k : Inside secondPivot) :
    ((operatorInCoordinates twoStepBasis shift).map f * graphMatrix secondPivot A) (i, j) k =
      if j = 0 then 0 else A (firstPivotRows.symm i) k := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  by_cases hj : j = 0
  · rw [ite_eq_left hj]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ -
    rw [shiftCoordinates, ite_eq_left hj, map_zero, zero_mul]
  · rw [ite_eq_right hj, Finset.sum_eq_single (i, (0 : Fin 2))]
    · rw [shiftCoordinates, ite_eq_right hj, ite_eq_left rfl, map_one, one_mul]
      exact dite_eq_right (firstPivotRows.symm i).property
    · rintro ⟨a, b⟩ - hn
      rw [shiftCoordinates, ite_eq_right hj, ite_eq_right hn.symm, map_zero, zero_mul]
    · simp

private def graphMatrixReindex {R : Type} (A : Matrix (Outside secondPivot) (Inside secondPivot) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j ↦ A (firstPivotRows.symm i) (secondPivotRows.symm j)

/-- The residual equations in the chart of graphs over the second coefficient. -/
private theorem graphResidual_shift {R : Type} [CommRing R] (f : ℂ →+* R)
    (A : Matrix (Outside secondPivot) (Inside secondPivot) R) (i j : Fin 2) :
    graphResidual secondPivot ((operatorInCoordinates twoStepBasis shift).map f) A
        (firstPivotRows.symm i) (secondPivotRows.symm j) =
      -(graphMatrixReindex A * graphMatrixReindex A) i j := by
  rw [graphResidual, Matrix.sub_apply]
  change ((operatorInCoordinates twoStepBasis shift).map f * graphMatrix secondPivot A) (i, 0)
      (secondPivotRows.symm j) - _ = _
  rw [shiftMulGraphMatrix, ite_eq_left rfl, zero_sub, neg_inj]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Fintype.sum_equiv secondPivotRows _ _ ?_
  intro k
  rw [Matrix.submatrix_apply]
  have hk : k.val = (secondPivotRows k, (1 : Fin 2)) := Prod.ext rfl
    ((secondPivot_mem _).mp k.property)
  rw [hk, shiftMulGraphMatrix, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  simp [graphMatrixReindex]

private def graphCoordinate (i j : Fin 2) : graphAlgebra :=
  MvPolynomial.X (firstPivotRows.symm i, secondPivotRows.symm j)

private def graphStabilityIdeal : Ideal graphAlgebra :=
  reducedStabilityIdeal secondPivot (operatorInCoordinates twoStepBasis shift)

private abbrev GraphCoordinateRing := graphAlgebra ⧸ graphStabilityIdeal

private def graphCoordinateQuotient : graphAlgebra →ₐ[ℂ] GraphCoordinateRing :=
  Ideal.Quotient.mkₐ ℂ graphStabilityIdeal

private theorem graphPolynomial_shift (i j : Fin 2) :
    graphPolynomial secondPivot (operatorInCoordinates twoStepBasis shift)
        (firstPivotRows.symm i) (secondPivotRows.symm j) =
      -((Matrix.of graphCoordinate) * (Matrix.of graphCoordinate)) i j := by
  unfold graphPolynomial
  exact graphResidual_shift MvPolynomial.C _ i j

private def graphClass (i j : Fin 2) : GraphCoordinateRing :=
  graphCoordinateQuotient (graphCoordinate i j)

private theorem graphClass_square :
    (Matrix.of graphClass) * (Matrix.of graphClass) = 0 := by
  ext i j
  have hm : graphPolynomial secondPivot (operatorInCoordinates twoStepBasis shift)
      (firstPivotRows.symm i) (secondPivotRows.symm j) ∈ graphStabilityIdeal :=
    Ideal.le_radical (Ideal.subset_span
      (Set.mem_range_self (firstPivotRows.symm i, secondPivotRows.symm j)))
  have h : graphCoordinateQuotient (graphPolynomial secondPivot (operatorInCoordinates twoStepBasis shift)
      (firstPivotRows.symm i) (secondPivotRows.symm j)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [graphPolynomial_shift, map_neg, neg_eq_zero] at h
  simpa only [Matrix.mul_apply, graphClass, Matrix.of_apply, Matrix.zero_apply, map_sum, map_mul]
    using h

private theorem graphClass_equations :
    graphClass 1 1 = -graphClass 0 0 ∧
      graphClass 0 0 ^ 2 + graphClass 0 1 * graphClass 1 0 = 0 := by
  let M := Matrix.of graphClass
  have : _root_.IsReduced GraphCoordinateRing :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have hdet : M.det = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [pow_two, ← Matrix.det_mul, graphClass_square, Matrix.det_zero]
  have h₀ : graphClass 0 0 ^ 2 + graphClass 0 1 * graphClass 1 0 = 0 := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.zero_apply, pow_two]
      using congrArg (fun A : Matrix (Fin 2) (Fin 2) GraphCoordinateRing ↦ A 0 0) graphClass_square
  have h₁ : graphClass 1 0 * graphClass 0 1 + graphClass 1 1 ^ 2 = 0 := by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.zero_apply, pow_two]
      using congrArg (fun A : Matrix (Fin 2) (Fin 2) GraphCoordinateRing ↦ A 1 1) graphClass_square
  have h₂ : graphClass 0 0 * graphClass 1 1 - graphClass 0 1 * graphClass 1 0 = 0 := by
    simpa only [M, Matrix.det_fin_two, Matrix.of_apply] using hdet
  have h : (graphClass 1 1 + graphClass 0 0) ^ 2 = 0 := by
    linear_combination h₀ + h₁ + 2 * h₂
  exact ⟨eq_neg_of_add_eq_zero_left (eq_zero_of_pow_eq_zero h), h₀⟩

/-- The reduced chart is generated by three coordinates with the indicated quadratic relation. -/
private theorem graphDimension_add_one_le :
    ringKrullDim GraphCoordinateRing + 1 ≤ 3 := by
  let f : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] GraphCoordinateRing :=
    MvPolynomial.aeval ![graphClass 0 0, graphClass 0 1, graphClass 1 0]
  have hpre (i j : Fin 2) : ∃ p, f p = graphClass i j := by
    fin_cases i <;> fin_cases j
    · exact ⟨MvPolynomial.X 0, by simp [f]⟩
    · exact ⟨MvPolynomial.X 1, by simp [f]⟩
    · exact ⟨MvPolynomial.X 2, by simp [f]⟩
    · exact ⟨-MvPolynomial.X 0, by simpa [f] using graphClass_equations.1.symm⟩
  have hgen (v : graphVariables) : graphCoordinateQuotient (MvPolynomial.X v) ∈ f.range := by
    obtain ⟨i, j⟩ := v
    change ∃ p, f p = graphCoordinateQuotient (MvPolynomial.X (i, j))
    simpa only [graphClass, graphCoordinate, Equiv.symm_apply_apply]
      using hpre (firstPivotRows i) (secondPivotRows j)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ graphStabilityIdeal z
    change graphCoordinateQuotient p ∈ f.range
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h := f.commutes r
      exact ⟨MvPolynomial.C r, h.trans (graphCoordinateQuotient.commutes r).symm⟩
    | add p q hp hq =>
      rw [map_add]
      exact f.range.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact f.range.mul_mem hp (hgen i)
  let rel : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 * MvPolynomial.X 2
  have hrel : rel ≠ 0 := by
    intro hz
    have t := congrArg (MvPolynomial.aeval (![1, 0, 0] : Fin 3 → ℂ)) hz
    simp [rel] at t
  have h := ringKrullDim_succ_le_of_surjective f.toRingHom hf
    (mem_nonZeroDivisors_iff_ne_zero.mpr hrel)
    (by simpa [f, rel] using graphClass_equations.2 : f.toRingHom rel = 0)
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card,
    ringKrullDim_eq_zero_of_field] using h

private abbrev ParameterRing := MvPolynomial (Fin 2) ℂ

private def graphParameters : Matrix (Fin 2) (Fin 2) ParameterRing :=
  let u : ParameterRing := MvPolynomial.X 0
  let v : ParameterRing := MvPolynomial.X 1
  !![u * v, -u ^ 2; v ^ 2, -(u * v)]

private def graphParametrization : graphAlgebra →ₐ[ℂ] ParameterRing :=
  MvPolynomial.aeval (fun ij ↦ graphParameters (firstPivotRows ij.1) (secondPivotRows ij.2))

private theorem graphParametrization_apply (i j : Fin 2) :
    graphParametrization (graphCoordinate i j) = graphParameters i j := by
  simp [graphParametrization, graphCoordinate]

private theorem graphParametrization_kills : graphStabilityIdeal ≤ RingHom.ker
    graphParametrization.toRingHom := by
  apply (RingHom.ker_isPrime graphParametrization.toRingHom).radical_le_iff.mpr
  rw [stabilityIdeal, Ideal.span_le]
  rintro p ⟨⟨i, j⟩, rfl⟩
  change graphParametrization (graphPolynomial secondPivot (operatorInCoordinates twoStepBasis shift) i j) = 0
  obtain ⟨i, rfl⟩ := firstPivotRows.symm.surjective i
  obtain ⟨j, rfl⟩ := secondPivotRows.symm.surjective j
  rw [graphPolynomial_shift, map_neg, neg_eq_zero]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [map_add, map_mul, Matrix.of_apply, graphParametrization_apply]
  fin_cases i <;> fin_cases j <;> simp [graphParameters] <;> ring

private def graphOrigin : PrimeSpectrum graphAlgebra :=
  let f := MvPolynomial.aeval (0 : graphVariables → ℂ)
  ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩

/-- The parametrization, its specialization at the first parameter, and evaluation at
the origin give a length-two prime chain. -/
private theorem graphOrigin_height_lower (z : PrimeSpectrum GraphCoordinateRing)
    (hz : PrimeSpectrum.comap (Ideal.Quotient.mk graphStabilityIdeal) z = graphOrigin) :
    2 ≤ Order.height z := by
  let f₀ := graphParametrization
  let g₁ : ParameterRing →ₐ[ℂ] ParameterRing := MvPolynomial.aeval ![0, MvPolynomial.X 1]
  let g₂ : ParameterRing →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin 2 → ℂ)
  let f₁ := g₁.comp f₀
  let f₂ := g₂.comp f₁
  let p₀ : PrimeSpectrum graphAlgebra := ⟨RingHom.ker f₀.toRingHom, RingHom.ker_isPrime f₀.toRingHom⟩
  let p₁ : PrimeSpectrum graphAlgebra := ⟨RingHom.ker f₁.toRingHom, RingHom.ker_isPrime f₁.toRingHom⟩
  have heval : f₂ = MvPolynomial.aeval (0 : graphVariables → ℂ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    obtain ⟨i, rfl⟩ := firstPivotRows.symm.surjective i
    obtain ⟨j, rfl⟩ := secondPivotRows.symm.surjective j
    change g₂ (g₁ (graphParametrization (graphCoordinate i j))) = _
    rw [graphParametrization_apply, MvPolynomial.aeval_X]
    fin_cases i <;> fin_cases j <;> simp [graphParameters, g₁, g₂]
  have h01 : p₀ < p₁ := by
    change RingHom.ker f₀.toRingHom < RingHom.ker f₁.toRingHom
    apply lt_of_le_not_ge
    · intro u hu
      change g₁ (f₀ u) = 0
      rw [show f₀ u = 0 from hu, map_zero]
    · intro h
      have hb : graphCoordinate 0 1 ∈ RingHom.ker f₁.toRingHom := by
        change g₁ (graphParametrization (graphCoordinate 0 1)) = 0
        simp [graphParametrization_apply, graphParameters, g₁]
      have hh : graphParametrization (graphCoordinate 0 1) = 0 := h hb
      simp [graphParametrization_apply, graphParameters] at hh
  have h12 : p₁ < graphOrigin := by
    change RingHom.ker f₁.toRingHom < RingHom.ker (MvPolynomial.aeval (0 : graphVariables → ℂ)).toRingHom
    rw [← heval]
    apply lt_of_le_not_ge
    · intro u hu
      change g₂ (f₁ u) = 0
      rw [show f₁ u = 0 from hu, map_zero]
    · intro h
      have hc : graphCoordinate 1 0 ∈ RingHom.ker f₂.toRingHom := by
        change g₂ (g₁ (graphParametrization (graphCoordinate 1 0))) = 0
        simp [graphParametrization_apply, graphParameters, g₁, g₂]
      have hh : g₁ (graphParametrization (graphCoordinate 1 0)) = 0 := h hc
      simp [graphParametrization_apply, graphParameters, g₁] at hh
  let E := graphStabilityIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let q₀ : PrimeSpectrum.zeroLocus (graphStabilityIdeal : Set graphAlgebra) :=
    ⟨p₀, graphParametrization_kills⟩
  let q₁ : PrimeSpectrum.zeroLocus (graphStabilityIdeal : Set graphAlgebra) :=
    ⟨p₁, graphParametrization_kills.trans h01.le⟩
  rw [← one_add_one_eq_two, ENat.add_one_le_iff ENat.one_ne_top]
  refine Order.one_lt_height_iff.mpr ⟨E.symm q₁, E.symm q₀, E.symm.strictMono h01, ?_⟩
  apply E.lt_iff_lt.mp
  rw [E.apply_symm_apply]
  change p₁ < PrimeSpectrum.comap (Ideal.Quotient.mk graphStabilityIdeal) z
  exact hz ▸ h12

private theorem graphOrigin_height (z : PrimeSpectrum GraphCoordinateRing)
    (hz : PrimeSpectrum.comap (Ideal.Quotient.mk graphStabilityIdeal) z = graphOrigin) :
    Order.height z = 2 := by
  refine le_antisymm ?_ (graphOrigin_height_lower z hz)
  have h := (add_le_add_left (Order.height_le_krullDim z) (1 : WithBot ℕ∞)).trans
    graphDimension_add_one_le
  have h' : Order.height z + 1 ≤ (2 : ℕ∞) + 1 := by
    apply WithBot.coe_le_coe.mp
    simpa only [WithBot.coe_add, WithBot.coe_one, WithBot.coe_ofNat,
      show (2 : WithBot ℕ∞) + 1 = 3 by norm_num] using h
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

private theorem chart_location_zero (y : Points graphAffineChart complexAlgebra)
    (hy : matrixOfPoint secondPivot complexAlgebra y = 0) :
    (pointLocation y : PrimeSpectrum graphAlgebra) = graphOrigin := by
  have ha : chartPointAlgebra complexAlgebra y =
      MvPolynomial.aeval (0 : graphVariables → ℂ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [MvPolynomial.aeval_X]
    exact congrFun (congrFun hy i) j
  rw [pointLocation, chartPoint_spec, ha]
  change PrimeSpectrum.comap (MvPolynomial.aeval (0 : graphVariables → ℂ)).toRingHom
    (default : PrimeSpectrum ℂ) = graphOrigin
  rw [show (default : PrimeSpectrum ℂ) = ⊥ from Subsingleton.elim _ _]
  exact PrimeSpectrum.ext (RingHom.ker_eq_comap_bot _).symm

set_option maxRecDepth 1200 in
set_option maxHeartbeats 600000 in
private theorem scalar_coheight {x : Points twoStepScheme complexAlgebra}
    (hx : ScalarTerminalPoint x) : Order.coheight (pointLocation x) = 2 := by
  obtain ⟨y, hy, hZero⟩ := scalarPoint_inChart hx
  let f : graphAffineChart.left ⟶ (grassmannianCharts twoStepBasis twoStepRank).scheme.left :=
    graphAffineChartInclusion.left
  let j : twoStepScheme.left ⟶ (grassmannianCharts twoStepBasis twoStepRank).scheme.left :=
    twoStepSchemeInGrassmannian.left
  have hf : IsOpenImmersion f :=
    (grassmannianCharts twoStepBasis twoStepRank).openChart secondPivot
  have heq : y.left ≫ f = x.left ≫ j := congrArg (fun g ↦ g.left) hy
  let P : Scheme := pullback f j
  let q : complexPointScheme.left ⟶ P := pullback.lift y.left x.left heq
  let w : P := q (default : PrimeSpectrum ℂ)
  let B : CommRingCat := CommRingCat.of GraphCoordinateRing
  let v : Spec B ⟶ graphAffineChart.left :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk graphStabilityIdeal))
  have hp : ∃ e : P ≅ Spec B, e.hom ≫ v = pullback.fst f j :=
    LatticeModels.stableAffinePresentation twoStepBasis twoStepRank shift secondPivot
  obtain ⟨e, he⟩ := hp
  let z : Spec B := e.hom w
  have hc : ((e.hom ≫ v) w : PrimeSpectrum graphAlgebra) =
      ((pullback.fst f j) w : PrimeSpectrum graphAlgebra) :=
    congrArg (fun g : P ⟶ graphAffineChart.left ↦ (g w : PrimeSpectrum graphAlgebra)) he
  have hy' : ((pullback.fst f j) w : PrimeSpectrum graphAlgebra) =
      (pointLocation y : PrimeSpectrum graphAlgebra) :=
    congrArg (fun g : complexPointScheme.left ⟶ graphAffineChart.left ↦
      (g (default : PrimeSpectrum ℂ) : PrimeSpectrum graphAlgebra))
      (pullback.lift_fst y.left x.left heq)
  have hz : PrimeSpectrum.comap (Ideal.Quotient.mk graphStabilityIdeal) z = graphOrigin :=
    hc.trans (hy'.trans (chart_location_zero y hZero))
  have hw : (pullback.snd f j) w = pointLocation x :=
    congrArg (fun g : complexPointScheme.left ⟶ twoStepScheme.left ↦
      g (default : PrimeSpectrum ℂ)) (pullback.lift_snd y.left x.left heq)
  calc
    Order.coheight (pointLocation x) = Order.coheight w := by
      rw [← hw, coheight_eq_of_isOpenImmersion (pullback.snd f j)]
    _ = Order.coheight z := (coheight_eq_of_isOpenImmersion e.hom).symm
    _ = Order.height (α := PrimeSpectrum GraphCoordinateRing) z :=
      (idealHeight_eq_coheight B z).symm.trans (PrimeSpectrum.height_eq_orderHeight
        (R := GraphCoordinateRing) z)
    _ = 2 := graphOrigin_height z hz

set_option linter.unusedVariables false in
theorem exceptionalFibre_conditional
    (_minusculeOrbit : MinusculeOrbit)
    (_minusculeProjective : MinusculeProjective)
    (_smallSchubertSchemes : SmallSchubertSchemes)
    (_twoStepOrbits : TwoStepOrbits)
    (_twoStepStableModel : TwoStepStableModel)
    (_firstLatticeQuotient : FirstLatticeQuotient)
    (_flagJetAction : FlagJetAction)
    (_latticeIncidence : LatticeIncidence)
    (_projectiveBundle : ProjectiveBundle)
    (_surfaceGeometry : SurfaceGeometry)
    (_twistedFlags : TwistedFlags) : ExceptionalFibre := by
  obtain ⟨x, s, hs⟩ := exceptionalSection_exists
  have h := scalar_coheight hs.1
  refine ⟨x, s, hs, exceptionalFibre_homeomorph hs.2.2.1 hs.2.2.2.1.w, projective_dim, h, ?_⟩
  rw [h, projective_dim]
  norm_num

end ScalarCodimension

end

end RepTheorySurvey.Geometric.ConvolutionSurface

theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurfaceSpecs».«ExceptionalFibre» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurfaceSpecs».«ExceptionalNormalBundle» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurfaceSpecs».«OpenOrbitIsomorphism» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags»)
theorem _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification» : _root_.«RepTheorySurvey».«Geometric».«ConvolutionSurfaceSpecs».«SurfaceIdentification» :=
  @_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeOrbit») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«minusculeProjective») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«smallSchubertSchemes») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepOrbits») (@_root_.«RepTheorySurvey».«Geometric».«MinusculeAndTwoStep».«twoStepStableModel») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«firstLatticeQuotient») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«flagJetAction») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«latticeIncidence») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«projectiveBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«surfaceGeometry») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionBundle».«twistedFlags»)
