import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.GrassmannianCoordinateInclusion
import Mathlib.Data.Finset.Preimage

namespace RepTheorySurvey.Geometric.GrassmannianCoordinateInclusion

noncomputable section

open LatticeModelSpecs hiding coordinateInclusion
open GrassmannianCoordinateInclusionSpecs hiding coordinateInclusion mapPoint
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open Topology
open scoped BigOperators Matrix

abbrev coordinateInclusion := @GrassmannianCoordinateInclusionSpecs.coordinateInclusion
abbrev mapPoint := @GrassmannianCoordinateInclusionSpecs.mapPoint

section Pivots

variable {ι κ : Type} (f : ι ↪ κ) {d : ℕ}

theorem mappedPivot_range :
    Set.range (mappedPivot (d := d) f) = {J | ∀ j : Inside J, j.val ∈ Set.range f} := by
  ext J
  change (∃ I, mappedPivot f I = J) ↔ ∀ j : Inside J, j.val ∈ Set.range f
  constructor
  · rintro ⟨I, rfl⟩ j
    obtain ⟨i, _, hij⟩ := Finset.mem_map.mp j.property
    exact ⟨i, hij⟩
  · intro h
    let K := J.val.preimage f f.injective.injOn
    have hK : K.map f = J.val := by
      ext j
      simp only [Finset.mem_map, K, Finset.mem_preimage]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hj
        obtain ⟨i, rfl⟩ := h ⟨j, hj⟩
        exact ⟨i, hj, rfl⟩
    have hcard : K.card = d := (Finset.card_map f).symm.trans
      ((congrArg Finset.card hK).trans J.property)
    exact ⟨⟨K, hcard⟩, Subtype.ext hK⟩

variable (I : Pivot ι d)

private theorem outsideEmbedding_range_iff (i : Outside (mappedPivot f I)) :
    i ∈ Set.range (outsideEmbedding f I) ↔ i.val ∈ Set.range f := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  · rintro ⟨j, hj⟩
    have hji : j ∉ I.val := fun h ↦ i.property (hj ▸ Finset.mem_map_of_mem f h)
    exact ⟨⟨j, hji⟩, Subtype.ext hj⟩

private theorem extendChartMatrix_apply (A : Matrix (Outside I) (Inside I) ℂ)
    (i : Outside I) (j : Inside (mappedPivot f I)) :
    extendChartMatrix f I A (outsideEmbedding f I i) j = A i ((insideEquiv f I).symm j) := by
  unfold extendChartMatrix
  rw [(outsideEmbedding f I).injective.extend_apply]

private theorem extendChartMatrix_apply_of_notMem_range
    (A : Matrix (Outside I) (Inside I) ℂ)
    (i : Outside (mappedPivot f I)) (hi : i.val ∉ Set.range f) (j : Inside (mappedPivot f I)) :
    extendChartMatrix f I A i j = 0 := by
  have hi' : ¬ ∃ k, outsideEmbedding f I k = i :=
    fun h ↦ hi ((outsideEmbedding_range_iff f I i).mp h)
  unfold extendChartMatrix
  rw [Function.extend_apply' _ _ _ hi']

private theorem extend_extractChartMatrix
    (A : Matrix (Outside (mappedPivot f I)) (Inside (mappedPivot f I)) ℂ)
    (hA : ∀ (i : Outside (mappedPivot f I)), i.val ∉ Set.range f →
      ∀ j : Inside (mappedPivot f I), A i j = 0) :
    extendChartMatrix f I (extractChartMatrix f I A) = A := by
  ext i j
  by_cases hi : i.val ∈ Set.range f
  · obtain ⟨k, rfl⟩ := (outsideEmbedding_range_iff f I i).mpr hi
    rw [extendChartMatrix_apply, extractChartMatrix, Equiv.apply_symm_apply]
  · rw [extendChartMatrix_apply_of_notMem_range f I _ i hi, hA i hi j]

variable [DecidableEq ι] [DecidableEq κ]

private theorem graphMatrix_apply_mapped (A : Matrix (Outside I) (Inside I) ℂ)
    (i : ι) (j : Inside I) :
    graphMatrix (mappedPivot f I) (extendChartMatrix f I A) (f i) (insideEquiv f I j) =
      graphMatrix I A i j := by
  have hmem : f i ∈ (mappedPivot f I).val ↔ i ∈ I.val := Finset.mem_map' f
  by_cases hi : i ∈ I.val
  · have hj : (insideEquiv f I j).val = f j.val := rfl
    simp [graphMatrix, hi, hmem.mpr hi, hj, f.injective.eq_iff]
  · have hi' : f i ∉ (mappedPivot f I).val := fun h ↦ hi (hmem.mp h)
    simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi, dite_eq_right hi']
    change extendChartMatrix f I A (outsideEmbedding f I ⟨i, hi⟩) (insideEquiv f I j) =
      A ⟨i, hi⟩ j
    rw [extendChartMatrix_apply, Equiv.symm_apply_apply]

variable [Fintype ι]

private theorem extendGraph_mulVec (A : Matrix (Outside I) (Inside I) ℂ)
    (v : Inside (mappedPivot f I) → ℂ) :
    graphMatrix (mappedPivot f I) (extendChartMatrix f I A) *ᵥ v =
      extendCoordinates f (graphMatrix I A *ᵥ (v ∘ insideEquiv f I)) := by
  funext j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    rw [extendCoordinates_apply]
    unfold Matrix.mulVec dotProduct
    rw [← (insideEquiv f I).sum_comp
      (fun k ↦ graphMatrix (mappedPivot f I) (extendChartMatrix f I A) (f i) k * v k)]
    simp only [graphMatrix_apply_mapped, Function.comp_apply]
  · have hJ : j ∉ (mappedPivot f I).val := by
      intro h
      obtain ⟨i, _, hij⟩ := Finset.mem_map.mp h
      exact hj ⟨i, hij⟩
    rw [extendCoordinates_apply_of_notMem_range f _ hj,
      show (graphMatrix (mappedPivot f I) (extendChartMatrix f I A) *ᵥ v) j =
        (extendChartMatrix f I A *ᵥ v) ⟨j, hJ⟩ from graphMatrix_outside _ _ _ ⟨j, hJ⟩]
    simp [Matrix.mulVec, dotProduct, extendChartMatrix_apply_of_notMem_range f I A ⟨j, hJ⟩ hj]

end Pivots

section Grassmannians

variable {ι κ V W : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [DecidableEq ι] [DecidableEq κ]
  (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
  {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)

theorem mapPoint_subspace (p : GrassmannianPoints b hd) :
    grassmannianSubspace b' hd' (mapPoint b b' f hd hd' p) =
      (grassmannianSubspace b hd p).map (coordinateInclusion b b' f) :=
  subspacePoint_subspace _ _ _ _

private theorem mapPoint_injective : Function.Injective (mapPoint b b' f hd hd') := by
  intro p q h
  apply grassmannianSubspace_injective b hd
  apply Submodule.map_injective_of_injective (coordinateInclusion_injective b b' f)
  rw [← mapPoint_subspace b b' f hd hd', ← mapPoint_subspace b b' f hd hd', h]

theorem mapPoint_range :
    Set.range (mapPoint b b' f hd hd') =
      {q | grassmannianSubspace b' hd' q ≤ (coordinateInclusion b b' f).range} := by
  ext q
  change (∃ p, mapPoint b b' f hd hd' p = q) ↔
    grassmannianSubspace b' hd' q ≤ (coordinateInclusion b b' f).range
  constructor
  · rintro ⟨p, rfl⟩
    rw [mapPoint_subspace]
    exact LinearMap.map_le_range
  · intro h
    let u := coordinateInclusion b b' f
    let P := (grassmannianSubspace b' hd' q).comap u
    have hmap : P.map u = grassmannianSubspace b' hd' q := Submodule.map_comap_eq_self h
    have hdim : Module.finrank ℂ P = d := by
      rw [(P.equivMapOfInjective u (coordinateInclusion_injective b b' f)).finrank_eq, hmap]
      exact grassmannianSubspace_finrank b' hd' q
    refine ⟨subspacePoint b hd P hdim, grassmannianSubspace_injective b' hd' ?_⟩
    rw [mapPoint_subspace, subspacePoint_subspace]
    exact hmap

omit [DecidableEq ι] [DecidableEq κ] in
private theorem coordinateInclusion_comp :
    b'.equivFun.toLinearMap.comp (coordinateInclusion b b' f) =
      (extendCoordinates f).comp b.equivFun.toLinearMap := by
  ext x j
  exact congrFun (b'.equivFun.apply_symm_apply (extendCoordinates f (b.equivFun x))) j

theorem mapPoint_chart (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) :
    mapPoint b b' f hd hd' (grassmannianChartPoint b hd I A) =
      grassmannianChartPoint b' hd' (mappedPivot f I) (extendChartMatrix f I A) := by
  apply grassmannianSubspace_injective b' hd'
  apply Submodule.map_injective_of_injective b'.equivFun.injective
  rw [mapPoint_subspace, ← Submodule.map_comp, coordinateInclusion_comp, Submodule.map_comp,
    grassmannianChartSubspace, grassmannianChartSubspace, ← LinearMap.range_comp]
  ext x
  change (∃ v, extendCoordinates f (graphMatrix I A *ᵥ v) = x) ↔
    (∃ v, graphMatrix (mappedPivot f I) (extendChartMatrix f I A) *ᵥ v = x)
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v ∘ (insideEquiv f I).symm, ?_⟩
    rw [extendGraph_mulVec]
    have hv : (v ∘ (insideEquiv f I).symm) ∘ insideEquiv f I = v := by
      funext j
      simp
    rw [hv]
  · rintro ⟨v, rfl⟩
    exact ⟨v ∘ insideEquiv f I, (extendGraph_mulVec f I A v).symm⟩

omit [DecidableEq ι] in
private theorem graphMatrix_apply_eq_zero_of_supported
    (J : Pivot κ d) (A : Matrix (Outside J) (Inside J) ℂ)
    (h : grassmannianSubspace b' hd' (grassmannianChartPoint b' hd' J A) ≤
      (coordinateInclusion b b' f).range)
    {i : κ} (hi : i ∉ Set.range f) (j : Inside J) :
    graphMatrix J A i j = 0 := by
  have hcol : (graphMatrix J A).col j ∈
      (grassmannianSubspace b' hd' (grassmannianChartPoint b' hd' J A)).map
        b'.equivFun.toLinearMap := by
    rw [grassmannianChartSubspace]
    exact ⟨Pi.single j 1, by rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]⟩
  obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp hcol
  obtain ⟨v, rfl⟩ := h hw
  calc
    graphMatrix J A i j = b'.equivFun (coordinateInclusion b b' f v) i := (congrFun heq i).symm
    _ = extendCoordinates f (b.equivFun v) i := by
      exact congrFun (b'.equivFun.apply_symm_apply _) i
    _ = 0 := extendCoordinates_apply_of_notMem_range f _ hi

omit [DecidableEq ι] in
theorem unsupported_chart (J : Pivot κ d) (hJ : ∃ j : Inside J, j.val ∉ Set.range f)
    (A : Matrix (Outside J) (Inside J) ℂ) :
    ¬ grassmannianSubspace b' hd' (grassmannianChartPoint b' hd' J A) ≤
      (coordinateInclusion b b' f).range := by
  intro h
  obtain ⟨j, hj⟩ := hJ
  have hz := graphMatrix_apply_eq_zero_of_supported b b' f hd' J A h hj j
  simp [graphMatrix, j.property] at hz

theorem mapPoint_image_chart (I : Pivot ι d) (S : Set (GrassmannianPoints b hd))
    (A : Matrix (Outside (mappedPivot f I)) (Inside (mappedPivot f I)) ℂ) :
    grassmannianChartPoint b' hd' (mappedPivot f I) A ∈ mapPoint b b' f hd hd' '' S ↔
      (∀ (i : Outside (mappedPivot f I)), i.val ∉ Set.range f →
        ∀ j : Inside (mappedPivot f I), A i j = 0) ∧
      grassmannianChartPoint b hd I (extractChartMatrix f I A) ∈ S := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have hsupport : grassmannianSubspace b' hd'
        (grassmannianChartPoint b' hd' (mappedPivot f I) A) ≤
        (coordinateInclusion b b' f).range := by
      rw [← heq, mapPoint_subspace]
      exact LinearMap.map_le_range
    have hz (i : Outside (mappedPivot f I)) (hi : i.val ∉ Set.range f)
        (j : Inside (mappedPivot f I)) : A i j = 0 := by
      simpa only [graphMatrix, Matrix.of_apply, dite_eq_right i.property] using
        graphMatrix_apply_eq_zero_of_supported b b' f hd' _ A hsupport hi j
    refine ⟨hz, ?_⟩
    have hsource : grassmannianChartPoint b hd I (extractChartMatrix f I A) = p := by
      apply mapPoint_injective b b' f hd hd'
      rw [mapPoint_chart, extend_extractChartMatrix f I A hz, heq]
    exact hsource.symm ▸ hp
  · rintro ⟨hz, hp⟩
    refine ⟨_, hp, ?_⟩
    rw [mapPoint_chart, extend_extractChartMatrix f I A hz]

end Grassmannians

section ChartTopology

variable {ι κ : Type} (f : ι ↪ κ) {d : ℕ}

private theorem continuous_extendChartMatrix (I : Pivot ι d) :
    Continuous (extendChartMatrix f I) := by
  apply continuous_matrix
  intro i j
  by_cases hi : i.val ∈ Set.range f
  · obtain ⟨k, rfl⟩ := (outsideEmbedding_range_iff f I i).mpr hi
    simpa only [extendChartMatrix_apply, Function.comp_def] using
      ((continuous_apply ((insideEquiv f I).symm j)).comp (continuous_apply k) :
        Continuous fun A : Matrix (Outside I) (Inside I) ℂ ↦ A k ((insideEquiv f I).symm j))
  · simpa only [extendChartMatrix_apply_of_notMem_range f I _ i hi] using
      (continuous_const : Continuous fun _ : Matrix (Outside I) (Inside I) ℂ ↦ (0 : ℂ))

private theorem continuous_extractChartMatrix (I : Pivot ι d) :
    Continuous (extractChartMatrix f I) :=
  continuous_matrix fun i j ↦
    (continuous_apply (insideEquiv f I j)).comp (continuous_apply (outsideEmbedding f I i))

private theorem continuous_grassmannianChartPoint {M : Type} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ M) (hd : d ≤ Module.finrank ℂ M)
    (I : Pivot ι d) : Continuous (grassmannianChartPoint b hd I) :=
  continuous_iSup_rng (i := I) continuous_coinduced_rng

end ChartTopology

section PointTopology

variable {ι κ V W : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [DecidableEq ι] [DecidableEq κ]
  (b : Module.Basis ι ℂ V) (b' : Module.Basis κ ℂ W) (f : ι ↪ κ)
  {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (hd' : d ≤ Module.finrank ℂ W)

private theorem continuous_mapPoint : Continuous (mapPoint b b' f hd hd') := by
  change Continuous[⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance, grassmannianAnalyticTopology b' hd'] _
  apply continuous_iSup_dom.mpr
  intro I
  apply continuous_coinduced_dom.mpr
  have h : mapPoint b b' f hd hd' ∘ grassmannianChartPoint b hd I =
      grassmannianChartPoint b' hd' (mappedPivot f I) ∘ extendChartMatrix f I :=
    funext (mapPoint_chart b b' f hd hd' I)
  rw [h]
  exact (continuous_grassmannianChartPoint b' hd' (mappedPivot f I)).comp
    (continuous_extendChartMatrix f I)

private theorem isClosedMap_mapPoint : IsClosedMap (mapPoint b b' f hd hd') := by
  intro S hS
  change @IsClosed (GrassmannianPoints b' hd') (⨆ J : Pivot κ d,
    TopologicalSpace.coinduced (grassmannianChartPoint b' hd' J) inferInstance)
    (mapPoint b b' f hd hd' '' S)
  rw [isClosed_iSup_iff]
  intro J
  rw [isClosed_coinduced]
  by_cases hJ : ∀ j : Inside J, j.val ∈ Set.range f
  · have hmem : J ∈ Set.range (mappedPivot f) := by
      rw [mappedPivot_range]
      exact hJ
    obtain ⟨I, rfl⟩ := hmem
    have hpreimage : (grassmannianChartPoint b' hd' (mappedPivot f I)) ⁻¹'
        (mapPoint b b' f hd hd' '' S) =
        (⋂ (i : Outside (mappedPivot f I)), ⋂ (_ : i.val ∉ Set.range f),
          ⋂ (j : Inside (mappedPivot f I)), {A | A i j = 0}) ∩
        (grassmannianChartPoint b hd I ∘ extractChartMatrix f I) ⁻¹' S := by
      ext A
      simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        Function.comp_apply] using mapPoint_image_chart b b' f hd hd' I S A
    rw [hpreimage]
    refine IsClosed.inter ?_ (hS.preimage ((continuous_grassmannianChartPoint b hd I).comp
      (continuous_extractChartMatrix f I)))
    refine isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun j ↦ ?_
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have houtside : ∃ j : Inside J, j.val ∉ Set.range f := not_forall.mp hJ
    have hpreimage : (grassmannianChartPoint b' hd' J) ⁻¹' (mapPoint b b' f hd hd' '' S) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨p, _, hp⟩ := hA
      apply unsupported_chart b b' f hd' J houtside A
      rw [← hp, mapPoint_subspace]
      exact LinearMap.map_le_range
    rw [hpreimage]
    exact isClosed_empty

theorem mapPoint_isClosedEmbedding :
    IsClosedEmbedding (mapPoint b b' f hd hd') :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_mapPoint b b' f hd hd') (mapPoint_injective b b' f hd hd')
    (isClosedMap_mapPoint b b' f hd hd')

end PointTopology

end

end RepTheorySurvey.Geometric.GrassmannianCoordinateInclusion
