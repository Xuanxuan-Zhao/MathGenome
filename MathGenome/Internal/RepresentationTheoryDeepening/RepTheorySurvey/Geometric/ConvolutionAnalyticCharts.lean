import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionAnalyticCharts
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Matrix.Normed
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.ConvolutionAnalyticCharts

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 1024

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module Set Topology
open LinearAlgebraicGroups (Points)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Pivot Inside Outside)
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs ConvolutionSurfaceSpecs
open ConvolutionAnalyticChartsSpecs ConvolutionAnalyticChartsSpecs.Expected

attribute [local instance] surfacePointTopology

open private grassmannianChart_isOpenEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
open private continuous_of_columnRange continuous_graphMatrix chartPlane_eq_range graphMatrix_range_iff
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
open private incidenceCoordinates_injective terminalPlane_stable
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
open private stablePlane_incidence secondPlane_injective terminalProjection_surjective_complex
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface

section Grassmannian

variable {M N ι κ : Type}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (b : Basis ι ℂ M) (c : Basis κ ℂ N)
  {d n : ℕ} (hd : d ≤ finrank ℂ M) (hn : n ≤ finrank ℂ N)

private theorem chartRanges_cover :
    (⋃ I : Pivot ι d, range (grassmannianChartPoint b hd I)) = univ := by
  rw [eq_univ_iff_forall]
  intro p
  obtain ⟨I, A, hA⟩ := grassmannianChartPoint_cover b hd p
  exact mem_iUnion.mpr ⟨I, A, hA⟩

/-- Taking the image under a continuous family of linear maps is continuous
when the images have the prescribed dimension. -/
private theorem continuous_grassmannian_image {X : Type} [TopologicalSpace X]
    (p : X → GrassmannianPoints b hd) (hp : Continuous p)
    (q : X → GrassmannianPoints c hn) (L : X → (M →ₗ[ℂ] N))
    (hL : Continuous (fun x ↦ LinearMap.toMatrix b c (L x)))
    (hq : ∀ x, grassmannianSubspace c hn (q x) =
      (grassmannianSubspace b hd (p x)).map (L x)) : Continuous q := by
  classical
  let S (I : Pivot ι d) := p ⁻¹' range (grassmannianChartPoint b hd I)
  have hS (I : Pivot ι d) : IsOpen (S I) :=
    (grassmannianChart_isOpenEmbedding b hd I).isOpen_range.preimage hp
  have hcover : (⋃ I, S I) = univ := by
    simp only [S, ← preimage_iUnion, chartRanges_cover b hd, preimage_univ]
  refine continuous_of_continuousOn_iUnion_of_isOpen (fun I ↦ ?_) hS hcover
  rw [continuousOn_iff_continuous_domRestrict]
  let e := (grassmannianChart_isOpenEmbedding b hd I).isEmbedding.toHomeomorph
  let a (x : S I) := e.symm ⟨p x.val, x.property⟩
  have ha : Continuous a :=
    e.symm.continuous.comp ((hp.comp continuous_subtype_val).subtype_mk _)
  have he (x : S I) : grassmannianChartPoint b hd I (a x) = p x.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p x.val, x.property⟩)
  let A (x : S I) := LinearMap.toMatrix b c (L x.val) * graphMatrix I (a x)
  have hA : Continuous A :=
    (hL.comp continuous_subtype_val).matrix_mul ((continuous_graphMatrix I).comp ha)
  apply continuous_of_columnRange c hn _ A hA
  intro x
  change (grassmannianSubspace c hn (q x.val)).map c.equivFun.toLinearMap = _
  dsimp only [A]
  rw [hq, ← he x, chartPlane_eq_range, LinearMap.range_comp, ← Submodule.map_comp,
    ← Submodule.map_comp, Matrix.mulVecLin_mul, LinearMap.range_comp]
  congr 1
  change _ = Matrix.toLin' (LinearMap.toMatrix b c (L x.val))
  rw [LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix']
  rfl

variable (hnd : d ≤ finrank ℂ N)

private def mapPlane (e : M ≃ₗ[ℂ] N) (p : GrassmannianPoints b hd) :
    GrassmannianPoints c hnd :=
  subspacePoint c hnd ((grassmannianSubspace b hd p).map e.toLinearMap) (by
    rw [LinearEquiv.finrank_map_eq, grassmannianSubspace_finrank])

private theorem mapPlane_subspace (e : M ≃ₗ[ℂ] N) (p : GrassmannianPoints b hd) :
    grassmannianSubspace c hnd (mapPlane b c hd hnd e p) =
      (grassmannianSubspace b hd p).map e.toLinearMap :=
  subspacePoint_subspace _ _ _ _

private theorem mapPlane_cancel (e : M ≃ₗ[ℂ] N) (p : GrassmannianPoints b hd) :
    mapPlane c b hnd hd e.symm (mapPlane b c hd hnd e p) = p := by
  apply grassmannianSubspace_injective b hd
  rw [mapPlane_subspace, mapPlane_subspace, ← Submodule.map_comp, LinearEquiv.symm_comp,
    Submodule.map_id]

private theorem mapPlane_continuous [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousSMul ℂ N] [T2Space N]
    {X : Type} [TopologicalSpace X] (e : X → M ≃ₗ[ℂ] N)
    (he : ∀ v, Continuous (fun x ↦ e x v))
    (p : X → GrassmannianPoints b hd) (hp : Continuous p) :
    Continuous (fun x ↦ mapPlane b c hd hnd (e x) (p x)) := by
  let : FiniteDimensional ℂ N := Module.Finite.of_basis c
  apply continuous_grassmannian_image b c hd hnd p hp _ (fun x ↦ (e x).toLinearMap)
  · apply continuous_matrix
    intro i j
    simp only [LinearMap.toMatrix_apply]
    exact (continuous_apply i).comp (c.equivFun.toLinearMap.continuous_of_finiteDimensional.comp
      (he (b j)))
  · exact fun x ↦ mapPlane_subspace b c hd hnd (e x) (p x)

omit [AddCommGroup N] [Module ℂ N] [Fintype κ] [DecidableEq κ] in
private theorem grassmannian_t2 : T2Space (GrassmannianPoints b hd) := by
  rw [t2_iff_isClosed_diagonal, ← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨p, q⟩ hpq
  obtain ⟨I, A, rfl⟩ := grassmannianChartPoint_cover b hd p
  obtain ⟨J, B, rfl⟩ := grassmannianChartPoint_cover b hd q
  let f := Prod.map (grassmannianChartPoint b hd I) (grassmannianChartPoint b hd J)
  have hf : IsOpenEmbedding f :=
    (grassmannianChart_isOpenEmbedding b hd I).prodMap (grassmannianChart_isOpenEmbedding b hd J)
  have hclosed : IsClosed (f ⁻¹' diagonal (GrassmannianPoints b hd)) := by
    let v (u : Inside I → ℂ) (z : Matrix (Outside I) (Inside I) ℂ ×
        Matrix (Outside J) (Inside J) ℂ) := graphMatrix I z.1 *ᵥ u
    have heq : (f ⁻¹' diagonal (GrassmannianPoints b hd)) =
        ⋂ u : Inside I → ℂ, {z | graphMatrix J z.2 *ᵥ
          (fun i : Inside J ↦ v u z i.val) = v u z} := by
      ext z
      change (f z).1 = (f z).2 ↔ _
      rw [mem_iInter]
      change (_ : GrassmannianPoints b hd) = _ ↔
        ∀ u : Inside I → ℂ, graphMatrix J z.2 *ᵥ (fun i : Inside J ↦ v u z i.val) = v u z
      have hle :
          (grassmannianSubspace b hd (grassmannianChartPoint b hd I z.1)).map
              b.equivFun.toLinearMap ≤
            (grassmannianSubspace b hd (grassmannianChartPoint b hd J z.2)).map
              b.equivFun.toLinearMap ↔
          ∀ u : Inside I → ℂ, graphMatrix J z.2 *ᵥ (fun i : Inside J ↦ v u z i.val) = v u z := by
        rw [grassmannianChartSubspace, grassmannianChartSubspace]
        constructor
        · intro h u
          exact (graphMatrix_range_iff J _ _).mp (h (LinearMap.mem_range_self _ u))
        · rintro h _ ⟨u, rfl⟩
          exact (graphMatrix_range_iff J _ _).mpr (h u)
      rw [← hle]
      constructor
      · intro h
        change grassmannianChartPoint b hd I z.1 = grassmannianChartPoint b hd J z.2 at h
        rw [h]
      · intro h
        apply grassmannianSubspace_injective b hd
        apply Submodule.map_injective_of_injective b.equivFun.injective
        apply Submodule.eq_of_le_of_finrank_le h
        rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq,
          grassmannianSubspace_finrank, grassmannianSubspace_finrank]
    rw [heq]
    apply isClosed_iInter
    intro u
    have hv : Continuous (v u) :=
      ((continuous_graphMatrix I).comp continuous_fst).matrix_mulVec continuous_const
    have hres : Continuous (fun z ↦ fun i : Inside J ↦ v u z i.val) :=
      continuous_pi (fun i ↦ (continuous_apply i.val).comp hv)
    exact isClosed_eq (((continuous_graphMatrix J).comp continuous_snd).matrix_mulVec hres) hv
  have ho : IsOpen (f ⁻¹' (diagonal (GrassmannianPoints b hd))ᶜ) := hclosed.isOpen_compl
  have him := hf.isOpenMap _ ho
  exact Filter.mem_of_superset (him.mem_nhds ⟨(A, B), hpq, rfl⟩) (image_preimage_subset _ _)

end Grassmannian

private theorem terminalContinuous : Continuous (fun q : ordered ↦ q ≫ terminalProjection) := by
  apply continuous_induced_rng.mpr
  exact continuous_snd.comp (show Continuous incidenceCoordinates from continuous_induced_dom)

attribute [local instance] incidenceAnalyticTopology

private theorem incidencePoint_exists (p : ProjectivePoints)
    (t : GrassmannianPoints twoStepBasis twoStepRank)
    (h : IncidenceCondition (firstPlane p) (grassmannianSubspace twoStepBasis twoStepRank t)) :
    ∃ q : ordered, incidenceCoordinates q = (p, t) := by
  obtain ⟨e, he⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  let T : TwoStepPoints := ⟨t, terminalPlane_stable h⟩
  let r : surface := e.symm T
  have hr : r ≫ twoStepSchemeInGrassmannian = t :=
    (he r).symm.trans (congrArg Subtype.val (e.apply_symm_apply T))
  let s : Points IncidenceAmbient complexAlgebra := prod.lift p r
  have h₁ : s ≫ (prod.fst : IncidenceAmbient ⟶ projectiveScheme) = p := prod.lift_fst _ _
  have h₂ : s ≫ (prod.snd : IncidenceAmbient ⟶ twoStepScheme) = r := prod.lift_snd _ _
  have hs : s ∈ incidenceLocus := by
    have h' : IncidenceCondition (firstPlane p) (secondPlane r) := by
      rw [secondPlane, hr]
      exact h
    change IncidenceCondition (firstPlane (s ≫ (prod.fst : IncidenceAmbient ⟶ projectiveScheme)))
      (secondPlane (s ≫ (prod.snd : IncidenceAmbient ⟶ twoStepScheme)))
    rw [h₁, h₂]
    exact h'
  obtain ⟨q, hq⟩ := (LatticeModels.pointLocation_in_closure_iff incidenceLocus s).mp
    (subset_closure ⟨s, hs, rfl⟩)
  change q ≫ incidenceInclusion = s at hq
  refine ⟨q, Prod.ext ?_ ?_⟩
  · change q ≫ incidenceInclusion ≫ prod.fst = p
    exact (Category.assoc q incidenceInclusion _).symm.trans
      ((congrArg (· ≫ prod.fst) hq).trans h₁)
  · change (q ≫ incidenceInclusion ≫ prod.snd) ≫ twoStepSchemeInGrassmannian = t
    rw [← Category.assoc q incidenceInclusion, hq, h₂, hr]

private theorem firstImage_of_nonscalar {x : surface} (hx : ScalarTerminalPoint x)
    (q : orderedComplement x) :
    firstPlane (q.val ≫ firstProjection) =
      (secondPlane (q.val ≫ terminalProjection)).map (LinearMap.fst ℂ V V) := by
  let p : surface := q.val ≫ terminalProjection
  have hp : p ≠ x := q.property
  have hp' : secondPlane p ≠ (⊥ : Submodule ℂ V).prod ⊤ :=
    fun h ↦ hp (secondPlane_injective (h.trans hx.2.2.symm))
  have hst : (secondPlane p).map shift ≤ secondPlane p :=
    (LatticeModels.stableSchemePoints twoStepBasis twoStepRank shift p).property
  have hdim : finrank ℂ (secondPlane p) = 2 := grassmannianSubspace_finrank _ _ _
  have hrank := (stablePlane_incidence _ hdim hst hp').1
  symm
  refine Submodule.eq_of_le_of_finrank_le ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    exact ((ConvolutionBundle.incidencePoint_condition q.val).2 hw).1
  · exact (grassmannianSubspace_finrank projectiveBasis projectiveRank _).trans hrank.symm |>.le

/-- Analytic inversion of the actual convolution projection off the scalar
terminal lattice. -/
theorem openOrbitHomeomorphism : OpenOrbitHomeomorphism := by
  intro x hx
  let f (q : orderedComplement x) : terminalComplement x :=
    ⟨q.val ≫ terminalProjection, q.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r h
      have ht : q.val ≫ terminalProjection = r.val ≫ terminalProjection :=
        congrArg Subtype.val h
      apply Subtype.ext
      apply incidenceCoordinates_injective
      apply Prod.ext
      · apply grassmannianSubspace_injective projectiveBasis projectiveRank
        change firstPlane (q.val ≫ firstProjection) = firstPlane (r.val ≫ firstProjection)
        rw [firstImage_of_nonscalar hx q, firstImage_of_nonscalar hx r, ht]
      · exact congrArg (· ≫ twoStepSchemeInGrassmannian) ht
    · intro p
      obtain ⟨q, hq⟩ := terminalProjection_surjective_complex x hx p.val
      change q ≫ terminalProjection = p.val at hq
      have hq' : q ≫ terminalProjection ∈ terminalComplement x := by
        rw [hq]
        exact p.property
      exact ⟨⟨q, hq'⟩, Subtype.ext hq⟩
  let e := Equiv.ofBijective f hf
  have ht (p : terminalComplement x) : (e.symm p).val ≫ terminalProjection = p.val :=
    congrArg Subtype.val (e.apply_symm_apply p)
  have hi (p : terminalComplement x) : firstPlane ((e.symm p).val ≫ firstProjection) =
      (secondPlane p.val).map (LinearMap.fst ℂ V V) := by
    rw [firstImage_of_nonscalar hx (e.symm p), ht]
  have hc : Continuous (fun p : terminalComplement x ↦ p.val ≫ twoStepSchemeInGrassmannian) :=
    (show Continuous (fun p : surface ↦ p ≫ twoStepSchemeInGrassmannian)
      from continuous_induced_dom).comp continuous_subtype_val
  have hinv : Continuous (fun p : terminalComplement x ↦
      ((e.symm p).val ≫ firstProjection : ProjectivePoints)) :=
    continuous_grassmannian_image twoStepBasis projectiveBasis twoStepRank projectiveRank
      _ hc _ (fun _ ↦ LinearMap.fst ℂ V V) continuous_const hi
  let h : orderedComplement x ≃ₜ terminalComplement x := {
    toEquiv := e
    continuous_toFun := (terminalContinuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_induced_rng.mpr
      change Continuous (fun p : terminalComplement x ↦ incidenceCoordinates (e.symm p).val)
      have heq : (fun p : terminalComplement x ↦ incidenceCoordinates (e.symm p).val) =
          fun p ↦ ((e.symm p).val ≫ firstProjection, p.val ≫ twoStepSchemeInGrassmannian) := by
        funext p
        exact Prod.ext rfl (congrArg (· ≫ twoStepSchemeInGrassmannian) (ht p))
      rw [heq]
      exact hinv.prodMk hc }
  exact ⟨h, fun _ ↦ rfl, hi⟩

section BundleCharts

private abbrev LinePivot := Pivot (Fin 2 × Fin 1) 1

private abbrev ChartMatrix (I : LinePivot) := Matrix (Outside I) (Inside I) ℂ
private abbrev PivotCoordinates (I : LinePivot) := Inside I → ℂ
private abbrev QuotientCoordinates (I : LinePivot) := Outside I → ℂ
private abbrev FibreAmbient (I : LinePivot) := V × (PivotCoordinates I × QuotientCoordinates I)

private def pivotSplit (I : LinePivot) :
    V ≃ₗ[ℂ] PivotCoordinates I × QuotientCoordinates I :=
  projectiveBasis.equivFun ≪≫ₗ
    { toEquiv := Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ I.val) (fun _ ↦ ℂ)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private def lineFrame (I : LinePivot) (A : ChartMatrix I) :
    V ≃ₗ[ℂ] PivotCoordinates I × QuotientCoordinates I :=
  pivotSplit I ≪≫ₗ (LinearEquiv.refl ℂ _).skewProd (LinearEquiv.refl ℂ _) (-A.mulVecLin)

private theorem lineFrame_apply (I : LinePivot) (A : ChartMatrix I) (v : V) :
    lineFrame I A v = ((pivotSplit I v).1, (pivotSplit I v).2 - A *ᵥ (pivotSplit I v).1) := by
  change (_, _ + (-A.mulVecLin) _) = _
  simp [sub_eq_add_neg]

private theorem lineFrame_symm_apply (I : LinePivot) (A : ChartMatrix I)
    (z : PivotCoordinates I × QuotientCoordinates I) :
    (lineFrame I A).symm z = (pivotSplit I).symm (z.1, z.2 + A *ᵥ z.1) := by
  change (pivotSplit I).symm (z.1, z.2 - (-A.mulVecLin) z.1) = _
  simp

private theorem lineFrame_mem (I : LinePivot) (A : ChartMatrix I) (v : V) :
    v ∈ firstPlane (grassmannianChartPoint projectiveBasis projectiveRank I A) ↔
      (lineFrame I A v).2 = 0 := by
  have hgraph (u : PivotCoordinates I) :
      lineFrame I A (projectiveBasis.equivFun.symm (graphMatrix I A *ᵥ u)) = (u, 0) := by
    have hp : pivotSplit I (projectiveBasis.equivFun.symm (graphMatrix I A *ᵥ u)) =
        (u, A *ᵥ u) := by
      apply Prod.ext
      · funext i
        change projectiveBasis.equivFun (projectiveBasis.equivFun.symm _) i.val = u i
        rw [LinearEquiv.apply_symm_apply, graphMatrix_inside]
      · funext j
        change projectiveBasis.equivFun (projectiveBasis.equivFun.symm _) j.val = (A *ᵥ u) j
        rw [LinearEquiv.apply_symm_apply, graphMatrix_outside]
    rw [lineFrame_apply, hp, sub_self]
  change v ∈ grassmannianSubspace projectiveBasis projectiveRank
    (grassmannianChartPoint projectiveBasis projectiveRank I A) ↔ _
  rw [chartPlane_eq_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact congrArg Prod.snd (hgraph u)
  · intro hv
    refine ⟨(lineFrame I A v).1, (lineFrame I A).injective ?_⟩
    change lineFrame I A (projectiveBasis.equivFun.symm (graphMatrix I A *ᵥ _)) = _
    rw [hgraph]
    exact Prod.ext rfl hv.symm

/-- The coordinates are the constant pivot, the first-order quotient, the
first-order pivot, and the constant quotient, in that order. -/
private def terminalFrame (I : LinePivot) (A : ChartMatrix I) :
    (V × V) ≃ₗ[ℂ] FibreAmbient I :=
  let S := PivotCoordinates I
  let Q := QuotientCoordinates I
  let swap : ((S × Q) × (S × Q)) ≃ₗ[ℂ] ((S × Q) × (S × Q)) :=
    { toFun := fun z ↦ ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun := fun z ↦ ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  (lineFrame I A).prodCongr (lineFrame I A) ≪≫ₗ swap ≪≫ₗ
    (pivotSplit I).symm.prodCongr (LinearEquiv.refl ℂ (S × Q))

private theorem terminalFrame_continuous (I : LinePivot) (v : V × V) :
    Continuous (fun A : ChartMatrix I ↦ terminalFrame I A v) := by
  have h (w : V) : Continuous (fun A : ChartMatrix I ↦ lineFrame I A w) := by
    simp only [lineFrame_apply]
    exact continuous_const.prodMk
      (continuous_const.sub (continuous_id.matrix_mulVec continuous_const))
  change Continuous (fun A : ChartMatrix I ↦
    ((pivotSplit I).symm ((lineFrame I A v.1).1, (lineFrame I A v.2).2),
      (lineFrame I A v.2).1, (lineFrame I A v.1).2))
  exact ((pivotSplit I).symm.toLinearMap.continuous_of_finiteDimensional.comp
    ((h v.1).fst.prodMk (h v.2).snd)).prodMk ((h v.2).fst.prodMk (h v.1).snd)

private theorem terminalFrame_symm_continuous (I : LinePivot) (z : FibreAmbient I) :
    Continuous (fun A : ChartMatrix I ↦ (terminalFrame I A).symm z) := by
  have h (w : PivotCoordinates I × QuotientCoordinates I) :
      Continuous (fun A : ChartMatrix I ↦ (lineFrame I A).symm w) := by
    simp only [lineFrame_symm_apply]
    exact (pivotSplit I).symm.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_const.prodMk (continuous_const.add
        (continuous_id.matrix_mulVec continuous_const)))
  change Continuous (fun A : ChartMatrix I ↦
    ((lineFrame I A).symm ((pivotSplit I z.1).1, z.2.2),
      (lineFrame I A).symm (z.2.1, (pivotSplit I z.1).2)))
  exact (h _).prodMk (h _)

private def fibreSummand (I : LinePivot) :
    Submodule ℂ (PivotCoordinates I × QuotientCoordinates I) :=
  (⊤ : Submodule ℂ (PivotCoordinates I)).prod ⊥

private theorem frame_incidence_iff (I : LinePivot) (A : ChartMatrix I)
    (P : Submodule ℂ (V × V)) :
    IncidenceCondition (firstPlane (grassmannianChartPoint projectiveBasis projectiveRank I A)) P ↔
      (⊥ : Submodule ℂ V).prod (fibreSummand I) ≤ P.map (terminalFrame I A).toLinearMap ∧
      P.map (terminalFrame I A).toLinearMap ≤ (⊤ : Submodule ℂ V).prod (fibreSummand I) := by
  let e := terminalFrame I A
  let S := firstPlane (grassmannianChartPoint projectiveBasis projectiveRank I A)
  have hlo : (⊥ : Submodule ℂ V).prod S =
      ((⊥ : Submodule ℂ V).prod (fibreSummand I)).comap e.toLinearMap := by
    ext v
    change v.1 = 0 ∧ v.2 ∈ S ↔
      (pivotSplit I).symm ((lineFrame I A v.1).1, (lineFrame I A v.2).2) = 0 ∧
      (lineFrame I A v.2).1 ∈ (⊤ : Submodule ℂ (PivotCoordinates I)) ∧
      (lineFrame I A v.1).2 = 0
    rw [lineFrame_mem, LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero]
    simp only [Submodule.mem_top, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      simp [h₁, h₂]
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨(lineFrame I A).map_eq_zero_iff.mp (Prod.mk_eq_zero.mpr ⟨h₁, h₃⟩), h₂⟩
  have hhi : S.prod (⊤ : Submodule ℂ V) =
      ((⊤ : Submodule ℂ V).prod (fibreSummand I)).comap e.toLinearMap := by
    ext v
    change v.1 ∈ S ∧ v.2 ∈ (⊤ : Submodule ℂ V) ↔
      (e v).1 ∈ (⊤ : Submodule ℂ V) ∧
      (lineFrame I A v.2).1 ∈ (⊤ : Submodule ℂ (PivotCoordinates I)) ∧
      (lineFrame I A v.1).2 = 0
    simpa only [Submodule.mem_top, and_true, true_and] using lineFrame_mem I A v.1
  change _ ≤ P ∧ P ≤ _ ↔ _ ≤ P.map e.toLinearMap ∧ P.map e.toLinearMap ≤ _
  rw [← Submodule.map_le_map_iff_of_injective e.injective ((⊥ : Submodule ℂ V).prod S) P,
    ← Submodule.map_le_map_iff_of_injective e.injective P (S.prod ⊤)]
  rw [hlo, hhi, Submodule.map_comap_eq_of_surjective e.surjective,
    Submodule.map_comap_eq_of_surjective e.surjective]

private theorem pivot_finrank (I : LinePivot) : finrank ℂ (PivotCoordinates I) = 1 := by
  rw [Module.finrank_pi, Fintype.card_coe]
  exact I.property

private theorem fibreAmbientRank (I : LinePivot) : 2 ≤ finrank ℂ (FibreAmbient I) := by
  rw [← (terminalFrame I 0).finrank_eq]
  exact twoStepRank

private abbrev fibreBasis (I : LinePivot) := Module.finBasis ℂ (FibreAmbient I)
private abbrev FibreGrassmannian (I : LinePivot) :=
  GrassmannianPoints (fibreBasis I) (fibreAmbientRank I)

private def fixedFibrePlane (I : LinePivot) (p : ProjectivePoints) : FibreGrassmannian I :=
  subspacePoint (fibreBasis I) (fibreAmbientRank I) ((firstPlane p).prod (fibreSummand I)) (by
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, firstPlane,
      (grassmannianSubspace_finrank projectiveBasis projectiveRank p)]
    change 1 + finrank ℂ ((⊤ : Submodule ℂ (PivotCoordinates I)).prod
      (⊥ : Submodule ℂ (QuotientCoordinates I))) = 2
    rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod,
      finrank_top, finrank_bot, pivot_finrank])

private theorem fixedFibreEmbedding (I : LinePivot) :
    IsClosedEmbedding (fixedFibrePlane I) ∧
      range (fixedFibrePlane I) = {q |
        (⊥ : Submodule ℂ V).prod (fibreSummand I) ≤ grassmannianSubspace
          (fibreBasis I) (fibreAmbientRank I) q ∧
        grassmannianSubspace (fibreBasis I) (fibreAmbientRank I) q ≤
          (⊤ : Submodule ℂ V).prod (fibreSummand I)} := by
  have hdim : 2 = 1 + finrank ℂ (PivotCoordinates I) := by rw [pivot_finrank]
  have hmem (p : ProjectivePoints) (w : FibreAmbient I) :
      w ∈ grassmannianSubspace (fibreBasis I) (fibreAmbientRank I) (fixedFibrePlane I p) ↔
        w.1 ∈ firstPlane p ∧ w.2.2 = 0 := by
    rw [fixedFibrePlane, subspacePoint_subspace]
    change (_ ∧ _ ∈ (⊤ : Submodule ℂ (PivotCoordinates I)) ∧ w.2.2 = 0) ↔ _
    simp
  simpa [fibreSummand] using GrassmannianIncidenceTopology.incidenceClosedEmbedding
    projectiveBasis (fibreBasis I) (LinearEquiv.refl ℂ (FibreAmbient I)) projectiveRank
    (fibreAmbientRank I) hdim (fixedFibrePlane I) hmem

private abbrev TerminalGrassmannian := GrassmannianPoints twoStepBasis twoStepRank

private def firstChart (I : LinePivot) : ChartMatrix I → ProjectivePoints :=
  grassmannianChartPoint projectiveBasis projectiveRank I

private theorem firstChart_open (I : LinePivot) : IsOpenEmbedding (firstChart I) :=
  grassmannianChart_isOpenEmbedding projectiveBasis projectiveRank I

private theorem incidenceCoordinates_continuous : Continuous incidenceCoordinates :=
  continuous_induced_dom

private def bundleChartRange (I : LinePivot) : Set ordered :=
  (Prod.fst ∘ incidenceCoordinates) ⁻¹' range (firstChart I)

private theorem bundleChartRange_open (I : LinePivot) : IsOpen (bundleChartRange I) :=
  (firstChart_open I).isOpen_range.preimage (continuous_fst.comp incidenceCoordinates_continuous)

/-- Analytic bundle trivialization over one graph chart of the first line. -/
private def bundleChart (I : LinePivot) :
    (ChartMatrix I × ProjectivePoints) ≃ₜ bundleChartRange I := by
  let B := (firstChart_open I).isEmbedding.toHomeomorph
  let F := (fixedFibreEmbedding I).1.isEmbedding.toHomeomorph
  let toPlane (A : ChartMatrix I) :=
    mapPlane (fibreBasis I) twoStepBasis (fibreAmbientRank I) twoStepRank (terminalFrame I A).symm
  let fromPlane (A : ChartMatrix I) :=
    mapPlane twoStepBasis (fibreBasis I) twoStepRank (fibreAmbientRank I) (terminalFrame I A)
  have from_to (A : ChartMatrix I) (p : FibreGrassmannian I) :
      fromPlane A (toPlane A p) = p :=
    mapPlane_cancel (fibreBasis I) twoStepBasis (fibreAmbientRank I) twoStepRank _ p
  have to_from (A : ChartMatrix I) (p : TerminalGrassmannian) :
      toPlane A (fromPlane A p) = p :=
    mapPlane_cancel twoStepBasis (fibreBasis I) twoStepRank (fibreAmbientRank I) _ p
  have hiff (A : ChartMatrix I) (p : TerminalGrassmannian) :
      IncidenceCondition (firstPlane (firstChart I A))
        (grassmannianSubspace twoStepBasis twoStepRank p) ↔
      fromPlane A p ∈ range (fixedFibrePlane I) := by
    rw [(fixedFibreEmbedding I).2]
    change _ ↔ (⊥ : Submodule ℂ V).prod (fibreSummand I) ≤
        grassmannianSubspace (fibreBasis I) (fibreAmbientRank I) (fromPlane A p) ∧
        grassmannianSubspace (fibreBasis I) (fibreAmbientRank I) (fromPlane A p) ≤
          (⊤ : Submodule ℂ V).prod (fibreSummand I)
    dsimp only [fromPlane]
    rw [mapPlane_subspace]
    exact frame_incidence_iff I A _
  have hpoint (z : ChartMatrix I × ProjectivePoints) :
      ∃ q : ordered, incidenceCoordinates q =
        (firstChart I z.1, toPlane z.1 (fixedFibrePlane I z.2)) := by
    apply incidencePoint_exists
    apply (hiff _ _).mpr
    rw [from_to]
    exact mem_range_self _
  let encode (z : ChartMatrix I × ProjectivePoints) : bundleChartRange I :=
    ⟨(hpoint z).choose, ⟨z.1, (congrArg Prod.fst (hpoint z).choose_spec).symm⟩⟩
  have hencode (z : ChartMatrix I × ProjectivePoints) :
      incidenceCoordinates (encode z).val =
        (firstChart I z.1, toPlane z.1 (fixedFibrePlane I z.2)) :=
    (hpoint z).choose_spec
  let param (q : bundleChartRange I) := B.symm ⟨(incidenceCoordinates q.val).1, q.property⟩
  have hparam (q : bundleChartRange I) : firstChart I (param q) = (incidenceCoordinates q.val).1 :=
    congrArg Subtype.val (B.apply_symm_apply ⟨_, q.property⟩)
  let unframe (q : bundleChartRange I) := fromPlane (param q) (incidenceCoordinates q.val).2
  have hunframe (q : bundleChartRange I) : unframe q ∈ range (fixedFibrePlane I) := by
    apply (hiff (param q) (incidenceCoordinates q.val).2).mp
    rw [hparam]
    exact ConvolutionBundle.incidencePoint_condition q.val
  let fibre (q : bundleChartRange I) := F.symm ⟨unframe q, hunframe q⟩
  have hfibre (q : bundleChartRange I) : fixedFibrePlane I (fibre q) = unframe q :=
    congrArg Subtype.val (F.apply_symm_apply ⟨_, hunframe q⟩)
  refine {
    toFun := encode
    invFun := fun q ↦ (param q, fibre q)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro z
    have h₁ : param (encode z) = z.1 :=
      (firstChart_open I).injective ((hparam _).trans (congrArg Prod.fst (hencode z)))
    refine Prod.ext h₁ ((fixedFibreEmbedding I).1.injective ?_)
    rw [hfibre]
    change fromPlane (param (encode z)) (incidenceCoordinates (encode z).val).2 = _
    rw [h₁, hencode, from_to]
  · intro q
    apply Subtype.ext
    apply incidenceCoordinates_injective
    change incidenceCoordinates (encode (param q, fibre q)).val = _
    rw [hencode]
    exact Prod.ext (hparam q) (by
      change toPlane (param q) (fixedFibrePlane I (fibre q)) = _
      rw [hfibre]
      exact to_from _ _)
  · apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    change Continuous (fun z ↦ incidenceCoordinates (encode z).val)
    simp only [hencode]
    exact ((firstChart_open I).continuous.comp continuous_fst).prodMk
      (mapPlane_continuous (fibreBasis I) twoStepBasis (fibreAmbientRank I) twoStepRank
        (fun z : ChartMatrix I × ProjectivePoints ↦ (terminalFrame I z.1).symm)
        (fun v ↦ (terminalFrame_symm_continuous I v).comp continuous_fst)
        _ ((fixedFibreEmbedding I).1.continuous.comp continuous_snd))
  · have hcoord : Continuous (fun q : bundleChartRange I ↦ incidenceCoordinates q.val) :=
      incidenceCoordinates_continuous.comp continuous_subtype_val
    have hc : Continuous param := B.symm.continuous.comp (hcoord.fst.subtype_mk _)
    have hu : Continuous unframe :=
      mapPlane_continuous twoStepBasis (fibreBasis I) twoStepRank (fibreAmbientRank I)
        (fun q ↦ terminalFrame I (param q))
        (fun w ↦ (terminalFrame_continuous I w).comp hc) _ hcoord.snd
    exact hc.prodMk (F.symm.continuous.comp (hu.subtype_mk _))

private def orderedChart (i : LinePivot × LinePivot) :
    ChartMatrix i.1 × ChartMatrix i.2 → ordered :=
  Subtype.val ∘ bundleChart i.1 ∘ Prod.map id (firstChart i.2)

private theorem orderedChart_open (i : LinePivot × LinePivot) : IsOpenEmbedding (orderedChart i) :=
  ((bundleChartRange_open i.1).isOpenEmbedding_subtypeVal.comp
    (bundleChart i.1).isOpenEmbedding).comp (IsOpenEmbedding.id.prodMap (firstChart_open i.2))

private theorem orderedChart_cover (q : ordered) : ∃ i, q ∈ range (orderedChart i) := by
  obtain ⟨I, A, hA⟩ := grassmannianChartPoint_cover projectiveBasis projectiveRank
    (incidenceCoordinates q).1
  let Q : bundleChartRange I := ⟨q, ⟨A, hA⟩⟩
  let z := (bundleChart I).symm Q
  obtain ⟨J, D, hD⟩ := grassmannianChartPoint_cover projectiveBasis projectiveRank z.2
  refine ⟨(I, J), (z.1, D), ?_⟩
  have hz : Prod.map id (firstChart J) (z.1, D) = z := Prod.ext rfl hD
  change ((bundleChart I) (Prod.map id (firstChart J) (z.1, D))).val = q
  rw [hz]
  exact congrArg Subtype.val ((bundleChart I).apply_symm_apply Q)

open scoped Matrix.Norms.Elementwise

/-- The analytic convolution space satisfies the hypotheses for the singular
cochain comparison, using the bundle charts of the actual incidence space. -/
theorem orderedTopology : OrderedTopology := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · have (i : LinePivot × LinePivot) : SecondCountableTopology (range (orderedChart i)) :=
      (orderedChart_open i).isEmbedding.toHomeomorph.symm.secondCountableTopology
    apply TopologicalSpace.secondCountableTopology_of_countable_cover
      (fun i ↦ (orderedChart_open i).isOpen_range)
    exact eq_univ_iff_forall.mpr (fun q ↦ mem_iUnion.mpr (orderedChart_cover q))
  · constructor
    intro q U hU
    obtain ⟨i, z, rfl⟩ := orderedChart_cover q
    let h := orderedChart_open i
    have hpre : orderedChart i ⁻¹' U ∈ 𝓝 z := h.continuous.continuousAt hU
    obtain ⟨K, hK, hKU, hcompact⟩ := local_compact_nhds hpre
    exact ⟨orderedChart i '' K, h.isOpenMap.image_mem_nhds hK,
      image_subset_iff.mpr hKU, hcompact.image h.continuous⟩
  · let : T2Space ProjectivePoints := grassmannian_t2 projectiveBasis projectiveRank
    let : T2Space TerminalGrassmannian := grassmannian_t2 twoStepBasis twoStepRank
    have h : IsEmbedding (incidenceCoordinates : ordered → ProjectivePoints × TerminalGrassmannian) :=
      ⟨⟨rfl⟩, incidenceCoordinates_injective⟩
    exact h.t2Space
  · intro q U hU
    obtain ⟨i, z, rfl⟩ := orderedChart_cover q
    let f := orderedChart i
    let h := orderedChart_open i
    have hpre : f ⁻¹' (U : Set ordered) ∈ 𝓝 z :=
      h.continuous.continuousAt (U.isOpen.mem_nhds hU)
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hpre
    let B := Metric.ball z r
    have hz : z ∈ B := Metric.mem_ball_self hr
    let W : TopologicalSpace.Opens ordered := ⟨f '' B, h.isOpenMap _ Metric.isOpen_ball⟩
    refine ⟨W, ⟨z, hz, rfl⟩, image_subset_iff.mpr hrU, ?_⟩
    exact (h.isEmbedding.homeomorphImage B).contractibleSpace_iff.mp
      ((convex_ball z r).contractibleSpace ⟨z, hz⟩)

end BundleCharts

end

end RepTheorySurvey.Geometric.ConvolutionAnalyticCharts
