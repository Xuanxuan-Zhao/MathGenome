import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.RegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorConstantRank
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SliceStructures
set_option autoImplicit false

namespace SmoothManifolds.RegularLevels
open ModelData AtlasData MapData BoundaryData MapClassData InteriorRankData
  RegularLevelData TangentData DifferentialData Set Filter
open scoped Topology ContDiff
universe u v w

/-- Boundarylessness supplies interior coordinates regardless of the global model. -/
theorem mem_manifoldInterior_of_boundary_empty {d : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold d a M)
    (hS : intrinsicBoundary S = ∅) (p : M) : p ∈ manifoldInterior S := by
  rw [← compl_intrinsicBoundary, hS]
  simp

/-- Smooth maps are continuous in the specified manifold topologies. -/
theorem smoothMap_continuous {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (f : M → N) (hf : IsSmoothMap S T f) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun p => (hf p).1)

/-- The usual closed-fiber argument uses the actual Hausdorff target topology. -/
theorem fiber_closed_proof :
    Specs.SmoothManifolds.Ch03.RegularLevels.fiber_closedType.{u,v} := by
  intro m n a b M N _ _ S T f hf y
  letI := T.topologicalManifold.hausdorff
  exact isClosed_singleton.preimage (smoothMap_continuous S T f hf)

/-- The submersion normal form is available at every point of a regular fiber. -/
theorem regular_fiber_normalForm {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hS : intrinsicBoundary S = ∅) (hT : intrinsicBoundary T = ∅)
    (hf : IsSmoothMap S T f) (y : N) (hy : IsRegularValue S T f y)
    (p : M) (hp : f p = y) : n ≤ m ∧ NormalForm ⊤ S T f p n := by
  have h := InteriorConstantRank.interior_submersion ⊤ (by simp) S T f hf p
    (mem_manifoldInterior_of_boundary_empty S hS p)
    (mem_manifoldInterior_of_boundary_empty T hT (f p)) (hy p hp)
  exact ⟨h.1, h.2.1⟩

/-- No dimension inequality is imposed until the fiber has a point. -/
theorem regular_fiber_dimension_proof :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_dimensionType.{u,v} := by
  intro m n a b M N _ _ S T f hS hT hf y hy
  have hdim : (f ⁻¹' {y}).Nonempty → n ≤ m := by
    rintro ⟨p, hp⟩
    exact (regular_fiber_normalForm S T f hS hT hf y hy p hp).1
  refine ⟨hdim, ?_⟩
  intro hmn
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_le_of_gt hmn) (hdim ⟨p, hp⟩)

/-- In dimension zero, a chart is injective into a one-point model, so its
open source containing p is exactly {p}. This includes half-space models. -/
theorem zero_manifold_singleton_open {b : ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold 0 b N) (y : N) : IsOpen ({y} : Set N) := by
  obtain ⟨d, hd, hy⟩ := T.smoothStructure.property.1.1 y
  have hs : d.source = {y} := by
    ext x
    constructor
    · intro hx
      exact d.injOn hx hy (Subsingleton.elim _ _)
    · rintro rfl
      exact hy
  rw [← hs]
  exact d.open_source

/-- Zero-dimensional target fibers are clopen, without any regularity premise. -/
theorem zero_target_clopen_proof :
    Specs.SmoothManifolds.Ch03.RegularLevels.zero_target_clopenType.{u,v} := by
  intro m a b M N _ _ S T f hf y
  exact ⟨(zero_manifold_singleton_open T y).preimage (smoothMap_continuous S T f hf),
    fiber_closed_proof S T f hf y⟩

open private scalar_comp_at from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

/-- A map constant along a fiber annihilates every tangent vector of the fiber.
This follows directly from the action on germs, without coordinate choices. -/
theorem fiber_differential_comp_zero {k m n : ℕ} {a b c : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (y : N) (R : SmoothManifold k c (f ⁻¹' {y}))
    (p : f ⁻¹' {y})
    (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (f p.val))
    (K : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential S T f p.val L) (hK : IsDifferential R S Subtype.val p K) :
    L.comp K = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply LinearMap.ext
  intro h
  obtain ⟨r, hr, he⟩ := (mem_smoothGermAlgebra_iff T (f p.val) h.val).mp h.property
  let j : SmoothGerm S p.val := ⟨Germ.ofFun (r ∘ f),
    Algebra.subset_adjoin ⟨r ∘ f, scalar_comp_at (hf p.val) hr, rfl⟩⟩
  let z : SmoothGerm R p := algebraMap ℝ (SmoothGerm R p) (r y)
  have hz : Germ.ofFun ((r ∘ f) ∘ (Subtype.val : f ⁻¹' {y} → M)) = z.val := by
    change Germ.ofFun ((r ∘ f) ∘ (Subtype.val : f ⁻¹' {y} → M)) =
      Germ.ofFun (fun _ : f ⁻¹' {y} => r y)
    congr 1
    funext x
    exact congrArg r x.property
  change (L (K v)).val h = 0
  rw [hL (K v) h j r he.symm rfl, hK v j z (r ∘ f) rfl hz]
  exact derivation_kills_constants (germEvaluation R p) v (r y)

/-- Injectivity of the inclusion and rank-nullity upgrade the chain-rule
inclusion to equality with the kernel. -/
theorem regular_fiber_tangent_proof :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_tangentType.{u} := by
  intro m n a b M N _ _ S T f hS hT hf y hy R hR p L K hL hK
  have hinj : Function.Injective K :=
    (MapClasses.smooth_tangent_invariants R S Subtype.val hR.1 p K hK).2.1.mp
      (hR.2.2.1 p)
  have hsurj : Function.Surjective L :=
    (MapClasses.smooth_tangent_invariants S T f hf p.val L hL).2.2.mp
      (hy p.val p.property)
  have hzero := fiber_differential_comp_zero S T f hf y R p L K hL hK
  have hle : LinearMap.range K ≤ LinearMap.ker L := by
    rintro _ ⟨v, rfl⟩
    change L (K v) = 0
    exact DFunLike.congr_fun hzero v
  obtain ⟨hfin, hdim⟩ := tangent_dimension S p.val
  letI := hfin
  have hdimT := (tangent_dimension T (f p.val)).2
  have hdimR := (tangent_dimension R p).2
  have hrange : Module.finrank ℝ (LinearMap.range K) = m - n :=
    (LinearMap.finrank_range_of_inj hinj).trans hdimR
  have hnull := LinearMap.finrank_range_add_finrank_ker (K := ℝ)
    (V := TangentSpace S p.val) (V₂ := TangentSpace T (f p.val)) L
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hdimT, hdim] at hnull
  have hdimker : Module.finrank ℝ (L.ker) = m - n := by
    have heq : n + Module.finrank ℝ (L.ker) = m := hnull
    omega
  letI : Module.Finite ℝ (L.ker) :=
    FiniteDimensional.finiteDimensional_submodule (K := ℝ) (V := TangentSpace S p.val) L.ker
  exact ⟨hinj, Submodule.eq_of_le_of_finrank_eq (K := ℝ)
    (V := TangentSpace S p.val) hle (hrange.trans hdimker.symm)⟩

/-- Re-express Euclidean open coordinates in the model used by slice Specs. -/
noncomputable def chartOfCoordinates {m : ℕ} {M : Type u} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (E m)) (B : E m ≃L[ℝ] Euclidean m) :
    ModelChart m .euclidean M :=
  c.transHomeomorph (B.toHomeomorph.trans (Homeomorph.Set.univ _).symm)

@[simp] theorem chartOfCoordinates_source {m : ℕ} {M : Type u} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (E m)) (B : E m ≃L[ℝ] Euclidean m) :
    (chartOfCoordinates c B).source = c.source := rfl

@[simp] theorem chartOfCoordinates_apply {m : ℕ} {M : Type u} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (E m)) (B : E m ≃L[ℝ] Euclidean m) (p : M) :
    (chartOfCoordinates c B p).val = B (c p) := rfl

/-- The normal-form compatibility data imply compatibility in the precise,
mixed-model sense required by the slice construction. -/
theorem compatible_chartOfCoordinates {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (c : OpenPartialHomeomorph M (E m)) (B : E m ≃L[ℝ] Euclidean m)
    (hc : CompatibleCoordinates ⊤ S c) : SliceData.CompatibleChart S (chartOfCoordinates c B) := by
  obtain ⟨e, he, A, hA, hAi, hsub, hforward, htarget, hinverse⟩ := hc
  intro d hd p hp hpd
  have hpe := (hsub hp).1
  have hpc : c p ∈ A.target := htarget (c.map_source hp)
  have hec : ChartContDiffAt ⊤ e (chartOfCoordinates c B) id p := by
    refine ⟨A.source, A.open_source, (hforward p hp).1,
      (fun z => B (A z)), B.contDiff.comp_contDiffOn hA, ?_⟩
    filter_upwards [c.open_source.mem_nhds hp] with x hx
    change B (A (e x).val) = B (c x)
    rw [(hforward x hx).2]
  have hce : ChartContDiffAt ⊤ (chartOfCoordinates c B) e id p := by
    refine ⟨B.symm ⁻¹' A.target, A.open_target.preimage B.symm.continuous, ?_,
      (fun z => A.symm (B.symm z)), ?_, ?_⟩
    · change B.symm (B (c p)) ∈ A.target
      simpa only [B.symm_apply_apply] using hpc
    · exact hAi.comp B.symm.contDiff.contDiffOn (fun _ hx => hx)
    · filter_upwards [c.open_source.mem_nhds hp] with x hx
      change A.symm (B.symm (B (c x))) = (e x).val
      rw [B.symm_apply_apply]
      have h := hinverse (c x) (c.map_source hx)
      rw [c.left_inv hx] at h
      exact h.symm
  have hed := chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hpe hpd
  have hde := chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d hd e he) hpd hpe
  exact ⟨LocalCoordinateExtension.comp hed hce, LocalCoordinateExtension.comp hec hde⟩

/-- Coordinates on a full slice are exactly the tuples with vanishing normal
coordinates, including the empty tangent or normal block. -/
theorem mem_coordinateSlice_iff {k m : ℕ} (hkm : k ≤ m) (x : Euclidean m) :
    x ∈ SliceData.coordinateSlice k m .euclidean ↔
      ∀ j : Fin m, k ≤ j.val → x j = 0 := by
  constructor
  · rintro ⟨z, _, rfl⟩ j hj
    simp [SliceData.sliceEmbedding, not_lt.mpr hj]
  · intro hx
    refine ⟨(fun i : Fin k => x (i.castLE hkm)), mem_univ _, ?_⟩
    funext j
    dsimp [SliceData.sliceEmbedding]
    split_ifs with hj
    · congr 1
    · exact (hx j (le_of_not_gt hj)).symm

/-- Permute the two coordinate blocks, so the kernel of the standard
projection becomes a slice in the first k coordinates. -/
def blockPermutation (n k : ℕ) : Equiv.Perm (Fin (n + k)) :=
  (finCongr (Nat.add_comm n k)).trans (@finAddFlip k n)

noncomputable def blockLinear (n k : ℕ) : Euclidean (n + k) ≃L[ℝ] Euclidean (n + k) :=
  ({ toFun := fun x j => x (blockPermutation n k j)
     invFun := fun x j => x ((blockPermutation n k).symm j)
     left_inv := fun x => by funext j; simp
     right_inv := fun x => by funext j; simp
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    Euclidean (n + k) ≃ₗ[ℝ] Euclidean (n + k)).toContinuousLinearEquiv

@[simp] theorem blockPermutation_of_lt {n k : ℕ} (j : Fin (n + k)) (hj : j.val < k) :
    blockPermutation n k j = ⟨n + j.val, by omega⟩ := by
  obtain ⟨j, hjm⟩ := j
  dsimp [blockPermutation]
  exact finAddFlip_apply_mk_left hj

@[simp] theorem blockPermutation_of_le {n k : ℕ} (j : Fin (n + k)) (hj : k ≤ j.val) :
    blockPermutation n k j = ⟨j.val - k, by omega⟩ := by
  obtain ⟨j, hjm⟩ := j
  dsimp [blockPermutation]
  exact finAddFlip_apply_mk_right hj _

/-- The permutation identifies the projection kernel with the full slice. -/
theorem blockLinear_slice_iff (n k : ℕ) (x : E (n + k)) :
    blockLinear n k ((InteriorConstantRank.toL2 (n + k)).symm x) ∈
      SliceData.coordinateSlice k (n + k) .euclidean ↔
      normalProjection (n + k) n n x = 0 := by
  rw [mem_coordinateSlice_iff (by omega)]
  constructor
  · intro hx
    ext i
    have hj : k + i.val < n + k := by omega
    have h := hx ⟨k + i.val, hj⟩ (by dsimp; omega)
    change ((InteriorConstantRank.toL2 (n + k)).symm x)
      (blockPermutation n k ⟨k + i.val, hj⟩) = 0 at h
    rw [blockPermutation_of_le _ (by dsimp; omega)] at h
    simp only [Nat.add_sub_cancel_left] at h
    simpa [normalProjection, InteriorConstantRank.toL2, EuclideanSpace.equiv,
      WithLp.equiv, show i.val < n + k by omega] using h
  · intro hx j hj
    have hi : j.val - k < n := by omega
    have h := congrArg (fun z : E n => z ⟨j.val - k, hi⟩) hx
    change ((InteriorConstantRank.toL2 (n + k)).symm x) (blockPermutation n k j) = 0
    rw [blockPermutation_of_le j hj]
    simpa [normalProjection, InteriorConstantRank.toL2, EuclideanSpace.equiv,
      WithLp.equiv, show j.val - k < n + k by omega, hi] using h

/-- A regular fiber is exactly a full slice on the actual chart image; the
coordinate image need not be rectangular. -/
theorem regular_fiber_hasSliceCharts {n k : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (n + k) a M) (T : SmoothManifold n b N) (f : M → N)
    (hS : intrinsicBoundary S = ∅) (hT : intrinsicBoundary T = ∅)
    (hf : IsSmoothMap S T f) (y : N) (hy : IsRegularValue S T f y) :
    SliceData.HasSliceCharts S (f ⁻¹' {y}) k .euclidean := by
  refine ⟨by omega, ?_⟩
  intro p hp
  change f p = y at hp
  obtain ⟨_, c, d, hc, hd, hpc, hcp, hfpd, hdfp, hmap, hform⟩ :=
    regular_fiber_normalForm S T f hS hT hf y hy p hp
  let B : E (n + k) ≃L[ℝ] Euclidean (n + k) :=
    (InteriorConstantRank.toL2 (n + k)).symm.trans (blockLinear n k)
  let C := chartOfCoordinates c B
  have hslice (x : M) (hx : x ∈ c.source) :
      f x = y ↔ (C x).val ∈ SliceData.coordinateSlice k (n + k) .euclidean := by
    have hn := hform (c x) (c.map_source hx)
    rw [c.left_inv hx] at hn
    change f x = y ↔ blockLinear n k ((InteriorConstantRank.toL2 (n + k)).symm (c x)) ∈ _
    rw [blockLinear_slice_iff, ← hn]
    constructor
    · intro h
      simpa only [h, ← hp] using hdfp
    · intro h
      apply d.injOn (hmap hx) (hp ▸ hfpd)
      exact h.trans (by simpa only [hp] using hdfp.symm)
  refine ⟨.euclidean, Or.inl rfl, C, compatible_chartOfCoordinates S c B hc, hpc,
    by omega, ?_, ?_⟩
  · intro h
    cases h
  · ext z
    constructor
    · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
      exact ⟨C.map_source hxc, (hslice x hxc).mp hx⟩
    · intro hz
      refine ⟨C.symm z, ⟨?_, C.map_target hz.1⟩, C.right_inv hz.1⟩
      apply (hslice (C.symm z) (C.map_target hz.1)).mpr
      have hzc : (C (C.symm z)).val = z.val := congrArg Subtype.val (C.right_inv hz.1)
      rw [hzc]
      exact hz.2

/-- Use the conditional slice construction only at its exact declared type.
The empty case uses the separately supplied arbitrary-dimensional interface. -/
theorem regular_fiber_structure_proof
    (hslice : Specs.SmoothManifolds.Ch03.SliceStructures.slice_structureType.{u})
    (hempty : Specs.SmoothManifolds.Ch03.SliceStructures.empty_slice_structureType.{u}) :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_structureType.{u,v} := by
  intro m n a b M N _ _ S T f hS hT hf y hy
  by_cases hne : (f ⁻¹' {y}).Nonempty
  · have hnm := (regular_fiber_dimension_proof S T f hS hT hf y hy).1 hne
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hcharts := regular_fiber_hasSliceCharts S T f hS hT hf y hy
    obtain ⟨R, hR, _, huniq⟩ := hslice S (f ⁻¹' {y}) hS hcharts
    have hdim : n + k - n = k := by omega
    have hresult : ∃ R : SmoothManifold k .euclidean (f ⁻¹' {y}),
        IsSmoothEmbedding R S Subtype.val ∧ intrinsicBoundary R = ∅ ∧
        ((f ⁻¹' {y}).Nonempty → k + n = n + k) ∧
        ∀ Q : SmoothManifold k .euclidean (f ⁻¹' {y}),
          IsSmoothEmbedding Q S Subtype.val → Q.smoothStructure = R.smoothStructure :=
      ⟨R, hR, intrinsicBoundary_euclidean R, by omega, huniq⟩
    rw [hdim]
    exact hresult
  · have he : f ⁻¹' {y} = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he]
    obtain ⟨R, hR, huniq⟩ := hempty S (m - n)
    exact ⟨R, hR, intrinsicBoundary_euclidean R, by simp, fun Q _ => huniq Q⟩

/-- A chart whose source is the whole space is a smooth atlas by itself. -/
theorem singleChartAtlas_smooth {d : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] (c : ModelChart d a X) (hc : c.source = univ) :
    IsContDiffAtlas ⊤ ({c} : Set (ModelChart d a X)) := by
  refine ⟨fun x => ⟨c, mem_singleton c, hc.symm ▸ mem_univ x⟩, ?_⟩
  intro e he d hd
  have he' : e = c := he
  have hd' : d = c := hd
  subst e; subst d
  exact contDiffCompatible_of_germs
    (fun x _ _ => LocalCoordinateExtension.self _ _ x)
    (fun x _ _ => LocalCoordinateExtension.self _ _ x)

/-- The maximal smooth atlas generated by a global chart. -/
noncomputable def singleChartManifold {d : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (c : ModelChart d a X) (hc : c.source = univ) : SmoothManifold d a X where
  topologicalManifold := ⟨inferInstance, inferInstance, {c}, (singleChartAtlas_smooth c hc).1⟩
  smoothStructure := ⟨maximalExtension ⊤ {c},
    maximalExtension_isMaximal (singleChartAtlas_smooth c hc)⟩

theorem singleChartManifold_chart_mem {d : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (c : ModelChart d a X) (hc : c.source = univ) :
    c ∈ (singleChartManifold c hc).smoothStructure.val :=
  subset_maximalExtension (singleChartAtlas_smooth c hc) (mem_singleton c)

/-- The global identity coordinate chart on ordinary Euclidean space. -/
def standardEuclideanChart (d : ℕ) : ModelChart d .euclidean (Euclidean d) :=
  (Homeomorph.Set.univ (Euclidean d)).symm.toOpenPartialHomeomorph

noncomputable def standardEuclideanManifold (d : ℕ) :
    SmoothManifold d .euclidean (Euclidean d) :=
  singleChartManifold (standardEuclideanChart d) rfl

theorem standardEuclideanManifold_standard (d : ℕ) :
    HasStandardEuclideanChart (standardEuclideanManifold d) :=
  ⟨standardEuclideanChart d, singleChartManifold_chart_mem _ _, rfl, fun _ => rfl⟩

/-- Normal coordinates are the trailing block, and have a surjective derivative
also in codimension zero. -/
noncomputable def normalCoordinates {k m : ℕ} (hkm : k ≤ m) :
    Euclidean m →L[ℝ] Euclidean (m - k) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨k + i.val, by omega⟩)

theorem normalCoordinates_surjective {k m : ℕ} (hkm : k ≤ m) :
    Function.Surjective (normalCoordinates hkm) := by
  intro z
  refine ⟨(fun j => if h : k ≤ j.val then z ⟨j.val - k, by omega⟩ else 0), ?_⟩
  ext i
  change (if h : k ≤ k + i.val then z ⟨k + i.val - k, _⟩ else 0) = z i
  simp

theorem normalCoordinates_eq_zero_iff {k m : ℕ} (hkm : k ≤ m) (x : Euclidean m) :
    normalCoordinates hkm x = 0 ↔ x ∈ SliceData.coordinateSlice k m .euclidean := by
  rw [mem_coordinateSlice_iff hkm]
  constructor
  · intro h j hj
    have hi : j.val - k < m - k := by omega
    have hz := congrArg (fun z : Euclidean (m - k) => z ⟨j.val - k, hi⟩) h
    change x ⟨k + (j.val - k), _⟩ = 0 at hz
    have he : (⟨k + (j.val - k), by omega⟩ : Fin m) = j := by ext; dsimp; omega
    simpa only [he] using hz
  · intro h
    ext i
    exact h ⟨k + i.val, by omega⟩ (by dsimp; omega)

/-- Submersions remain submersions after a diffeomorphism of the source. -/
theorem submersion_comp_diffeomorph {d l n : ℕ} {a b c : ModelKind}
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold d a X) (B : SmoothManifold l b Y) (E : SmoothManifold n c Z)
    (h : Diffeomorph A.smoothStructure.val B.smoothStructure.val)
    (g : Y → Z) (hg : IsSmoothMap B E g) (hsub : IsSubmersion B E g) :
    IsSmoothMap A E (g ∘ h.toEquiv) ∧ IsSubmersion A E (g ∘ h.toEquiv) := by
  have hs : IsSmoothMap A E (g ∘ h.toEquiv) := manifoldContDiff_comp ⊤ _ _ _
    B.smoothStructure.property.1.1 h.toEquiv g h.contDiff_toFun hg
  refine ⟨hs, ?_⟩
  intro p
  obtain ⟨e, he, hpe⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := B.smoothStructure.property.1.1 (h.toEquiv p)
  obtain ⟨c, hc, hpc⟩ := E.smoothStructure.property.1.1 (g (h.toEquiv p))
  have hfwd := (h.contDiff_toFun p).2 e he d hd hpe hpd
  have hinv := (h.contDiff_invFun (h.toEquiv p)).2 d hd e he hpd
    (by simpa only [Equiv.symm_apply_apply] using hpe)
  have hcomp := FiniteRegularity.chartDerivative_comp ⊤ (by simp) d e d
    h.toEquiv.symm h.toEquiv (h.toEquiv p) hpd (h.contDiff_invFun _).1 hinv
    (by simpa only [Equiv.symm_apply_apply] using hfwd)
  have hid : h.toEquiv ∘ h.toEquiv.symm = id := by
    funext x
    exact h.toEquiv.apply_symm_apply x
  rw [hid, FiniteRegularity.chartDerivative_id d _ hpd] at hcomp
  simp only [Equiv.symm_apply_apply] at hcomp
  have hsurjh : Function.Surjective (FiniteRegularityData.chartDerivative e d h.toEquiv p) := by
    intro z
    refine ⟨FiniteRegularityData.chartDerivative d e h.toEquiv.symm (h.toEquiv p) z, ?_⟩
    exact (congrArg (fun L : Euclidean l →L[ℝ] Euclidean l => L z) hcomp).symm
  have hG := MapClasses.chart_invariants B E g
    (manifoldContDiff_of_le ⊤ 1 _ _ g (by simp) hg) (h.toEquiv p) d c hd hc hpd hpc
  have hJ := FiniteRegularity.chartDerivative_comp ⊤ (by simp) e d c
    h.toEquiv g p hpe (h.contDiff_toFun p).1 hfwd ((hg _).2 d hd c hc hpd hpc)
  have hResult := MapClasses.chart_invariants A E (g ∘ h.toEquiv)
    (manifoldContDiff_of_le ⊤ 1 _ _ _ (by simp) hs) p e c he hc hpe hpc
  apply hResult.2.2.mpr
  rw [hJ]
  exact ((hG.2.2.mp (hsub _)).comp hsurjh)

/-- A full slice in a compatible chart is the zero set of the trailing
projection. The resulting submersion is on the inherited open structure. -/
theorem defining_submersion_of_slice {k m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (s : Set M) (d : ModelChart m .euclidean M)
    (hcompat : SliceData.CompatibleChart S d)
    (hslice : SliceData.IsSliceChart s k .euclidean d) (p : M) (hp : p ∈ d.source) :
    ∃ (U : Set M) (hU : IsOpen U), p ∈ U ∧
      ∃ A : SmoothManifold m a U,
        A.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (openSubsetAtlas S.smoothStructure.val U hU) ∧
      ∃ E : SmoothManifold (m - k) .euclidean (Euclidean (m - k)),
        HasStandardEuclideanChart E ∧
      ∃ g : U → Euclidean (m - k),
        IsSmoothMap A E g ∧ IsSubmersion A E g ∧
        ∀ x : U, x.val ∈ s ↔ g x = 0 := by
  letI := S.topologicalManifold.hausdorff
  letI := S.topologicalManifold.secondCountable
  let U := d.source
  let hU : IsOpen U := d.open_source
  let D := d.subtypeRestr (s := ⟨U, hU⟩) ⟨⟨p, hp⟩⟩
  have hD : D.source = univ := by
    dsimp only [D]
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext x
    change x.val ∈ d.source ↔ x ∈ univ
    exact iff_true_intro x.property
  let B := singleChartManifold D hD
  let E := standardEuclideanManifold (m - k)
  let e := standardEuclideanChart (m - k)
  have hBm : D ∈ B.smoothStructure.val := singleChartManifold_chart_mem D hD
  have hEm : e ∈ E.smoothStructure.val := singleChartManifold_chart_mem e rfl
  let P := normalCoordinates hslice.1
  let g : U → Euclidean (m - k) := fun x => P (d x.val).val
  have hg : IsSmoothMap B E g := by
    intro x
    apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ B.smoothStructure.property.1
      E.smoothStructure.property.1 g x).mpr
    have hx : x ∈ D.source := hD.symm ▸ mem_univ x
    refine ⟨P.continuous.continuousAt.comp
      (continuous_subtype_val.continuousAt.comp (D.continuousAt hx)),
      D, hBm, e, hEm, hx, mem_univ _, ?_⟩
    exact ⟨univ, isOpen_univ, mem_univ _, P, P.contDiff.contDiffOn,
      Eventually.of_forall (fun _ => rfl)⟩
  have hsub : IsSubmersion B E g := by
    intro x
    have hx : x ∈ D.source := hD.symm ▸ mem_univ x
    have hJ : FiniteRegularityData.chartDerivative D e g x = P :=
      FiniteRegularity.coordinateDerivative_eq D _ x hx P
        ⟨P, P.hasFDerivAt, Eventually.of_forall (fun _ => rfl)⟩
    have hinv := MapClasses.chart_invariants B E g
      (manifoldContDiff_of_le ⊤ 1 _ _ g (by simp) hg) x D e hBm hEm hx (mem_univ _)
    apply hinv.2.2.mpr
    rw [hJ]
    exact normalCoordinates_surjective hslice.1
  obtain ⟨A, _, hA, _⟩ := exists_openSubset_smoothManifold S U hU
  let C := openSubsetAtlas S.smoothStructure.val U hU
  have hC : IsContDiffAtlas ⊤ C :=
    openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 U hU
  have hab : ManifoldContDiff ⊤ C {D} id := by
    intro x
    refine ⟨continuousAt_id, ?_⟩
    rintro _ ⟨hne, c, hc, rfl⟩ e' he' hx _
    have he' : e' = D := he'
    subst e'
    exact LocalCoordinateExtension.precomp
      (hcompat c hc x.val x.property (by simpa using hx)).2 continuousAt_subtype_val rfl
  have hba : ManifoldContDiff ⊤ {D} C id := by
    intro x
    refine ⟨continuousAt_id, ?_⟩
    rintro e' he' _ ⟨hne, c, hc, rfl⟩ _ hx
    have he' : e' = D := he'
    subst e'
    exact LocalCoordinateExtension.precomp
      (hcompat c hc x.val x.property (by simpa using hx)).1 continuousAt_subtype_val rfl
  let h : Diffeomorph A.smoothStructure.val B.smoothStructure.val := {
    toEquiv := Equiv.refl U
    contDiff_toFun := by
      rw [hA]
      exact (manifoldContDiff_maximalExtension_iff ⊤ C {D} hC
        (singleChartAtlas_smooth D hD) id).mpr hab
    contDiff_invFun := by
      rw [hA]
      exact (manifoldContDiff_maximalExtension_iff ⊤ {D} C
        (singleChartAtlas_smooth D hD) hC id).mpr hba }
  have hAg := submersion_comp_diffeomorph A B E h g hg hsub
  refine ⟨U, hU, hp, A, hA, E, standardEuclideanManifold_standard _, g, hAg.1, hAg.2, ?_⟩
  intro x
  have hpoint : x.val ∈ s ↔ (d x.val).val ∈ SliceData.coordinateSlice k m .euclidean := by
    constructor
    · intro hx
      have hz : d x.val ∈ d '' (s ∩ d.source) := ⟨x.val, ⟨hx, x.property⟩, rfl⟩
      rw [hslice.2.2] at hz
      exact hz.2
    · intro hx
      have hz : d x.val ∈ d '' (s ∩ d.source) := by
        rw [hslice.2.2]
        exact ⟨d.map_source x.property, hx⟩
      obtain ⟨z, ⟨hzs, hzd⟩, hzx⟩ := hz
      exact d.injOn hzd x.property hzx ▸ hzs
  exact hpoint.trans (normalCoordinates_eq_zero_iff hslice.1 (d x.val).val).symm

/-- Projection after the full-slice inclusion is the identity. -/
theorem sliceProjection_sliceEmbedding {k n : ℕ} (hkn : k ≤ n) (x : Euclidean k) :
    SliceData.sliceProjection hkn (SliceData.sliceEmbedding k n x) = x := by
  funext i
  simp [SliceData.sliceProjection, SliceData.sliceEmbedding]

/-- Localize a Euclidean inclusion normal form using the embedding topology.
An additional open restriction in the projected chart target ensures that the
whole slice, not only one inclusion, lies in the submanifold image. -/
theorem localize_full_slice {k n : ℕ} {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N]
    (f : P → N) (hf : Topology.IsEmbedding f)
    (e : ModelChart k .euclidean P) (d : ModelChart n .euclidean N)
    (p : P) (hp : p ∈ e.source) (hkn : k ≤ n)
    (hmap : MapsTo f e.source d.source)
    (heq : ∀ x ∈ e.source, (d (f x)).val = SliceData.sliceEmbedding k n (e x).val) :
    ∃ (A : Set N) (hA : IsOpen A), f p ∈ (d.restrOpen A hA).source ∧
      SliceData.IsSliceChart (range f) k .euclidean (d.restrOpen A hA) := by
  obtain ⟨V, hV, hVe⟩ := hf.isInducing.isOpen_iff.mp e.open_source
  let π : ModelSpace n .euclidean → ModelSpace k .euclidean :=
    fun z => ⟨SliceData.sliceProjection hkn z.val, mem_univ _⟩
  have hπ : Continuous π := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => (continuous_apply (i.castLE hkn)).comp continuous_subtype_val)
  have hπeq (x : P) (hx : x ∈ e.source) : π (d (f x)) = e x := by
    apply Subtype.ext
    change SliceData.sliceProjection hkn (d (f x)).val = (e x).val
    rw [heq x hx, sliceProjection_sliceEmbedding]
  let A := V ∩ (d.source ∩ (π ∘ d) ⁻¹' e.target)
  have hA : IsOpen A := hV.inter (d.isOpen_inter_preimage (e.open_target.preimage hπ))
  let C := d.restrOpen A hA
  have hfp : f p ∈ C.source := by
    refine ⟨hmap hp, ?_, hmap hp, ?_⟩
    · change p ∈ f ⁻¹' V
      rwa [hVe]
    · change π (d (f p)) ∈ e.target
      rw [hπeq p hp]
      exact e.map_source hp
  refine ⟨A, hA, hfp, hkn, ?_, ?_⟩
  · intro h
    cases h
  · ext z
    constructor
    · rintro ⟨_, ⟨⟨x, rfl⟩, hxC⟩, rfl⟩
      have hx : x ∈ e.source := by
        rw [← hVe]
        exact hxC.2.1
      refine ⟨C.map_source hxC, (e x).val, (e x).property, ?_⟩
      exact (heq x hx).symm
    · rintro ⟨hz, u, hu, huz⟩
      have hxC := C.map_target hz
      have hdz : d (C.symm z) = z := C.right_inv hz
      have huπ : π z = (⟨u, hu⟩ : ModelSpace k .euclidean) := by
        apply Subtype.ext
        change SliceData.sliceProjection hkn z.val = u
        rw [← huz, sliceProjection_sliceEmbedding]
      have huT : (⟨u, hu⟩ : ModelSpace k .euclidean) ∈ e.target := by
        have ht : π (d (C.symm z)) ∈ e.target := hxC.2.2.2
        rwa [hdz, huπ] at ht
      have hw : e.symm ⟨u, hu⟩ ∈ e.source := e.map_target huT
      have hdw : d (f (e.symm ⟨u, hu⟩)) = z := by
        apply Subtype.ext
        rw [heq _ hw, e.right_inv huT]
        exact huz
      have hfx : f (e.symm ⟨u, hu⟩) = C.symm z :=
        d.injOn (hmap hw) hxC.1 (hdw.trans hdz.symm)
      refine ⟨C.symm z, ⟨⟨e.symm ⟨u, hu⟩, hfx⟩, hxC⟩, C.right_inv hz⟩

/-- Obtain a full slice for an embedded boundaryless submanifold directly
from the accepted immersion normal form. This proof uses no unproved slice
implementation and works in arbitrary universes. -/
theorem embedded_boundaryless_slice {k m : ℕ} {a b : ModelKind}
    {M : Type u} {P : Type v} [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold m a M) (R : SmoothManifold k b P) (f : P → M)
    (hS : intrinsicBoundary S = ∅) (hR : intrinsicBoundary R = ∅)
    (hemb : IsSmoothEmbedding R S f) (p : P) :
    k ≤ m ∧ ∃ d : ModelChart m .euclidean M,
      SliceData.CompatibleChart S d ∧ f p ∈ d.source ∧
        SliceData.IsSliceChart (range f) k .euclidean d := by
  obtain ⟨hkm, ⟨c, d, hc, hd, hpc, _, hpd, _, hmap, hform⟩, _⟩ :=
    InteriorConstantRank.interior_immersion ⊤ (by simp) R S f hemb.1 p
      (mem_manifoldInterior_of_boundary_empty R hR p)
      (mem_manifoldInterior_of_boundary_empty S hS (f p)) (hemb.2.2.1 p)
  let e := chartOfCoordinates c (InteriorConstantRank.toL2 k).symm
  let D := chartOfCoordinates d (InteriorConstantRank.toL2 m).symm
  have heq (x : P) (hx : x ∈ e.source) :
      (D (f x)).val = SliceData.sliceEmbedding k m (e x).val := by
    have hn := hform (c x) (c.map_source hx)
    rw [c.left_inv hx] at hn
    change (InteriorConstantRank.toL2 m).symm (d (f x)) =
      SliceData.sliceEmbedding k m ((InteriorConstantRank.toL2 k).symm (c x))
    rw [hn]
    funext j
    simp [normalProjection, SliceData.sliceEmbedding, InteriorConstantRank.toL2,
      EuclideanSpace.equiv]
  have hf : Topology.IsEmbedding f := by
    obtain ⟨h, hh⟩ := hemb.2.2.2
    have hfun : f = Subtype.val ∘ h := by
      funext x
      exact (hh x).symm
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  obtain ⟨A, hA, hpA, hslice⟩ := localize_full_slice f hf e D p hpc hkm hmap heq
  have hcompat := compatible_chartOfCoordinates S d (InteriorConstantRank.toL2 m).symm hd
  have hcompatrestr : SliceData.CompatibleChart S (D.restrOpen A hA) := by
    intro e' he' x hx hxe'
    exact hcompat e' he' x hx.1 hxe'
  exact ⟨hkm, D.restrOpen A hA, hcompatrestr, hpA, hslice⟩

/-- The converse is local, with a codimension-dimensional Euclidean target.
The general embedding formulation covers a submanifold supplied initially
with an arbitrary topology, by taking f to be its inclusion. -/
theorem local_defining_submersion_proof :
    Specs.SmoothManifolds.Ch03.RegularLevels.local_defining_submersionType.{u,v} := by
  intro k m a b M P _ _ S R f hS hR hemb p
  obtain ⟨hkm, d, hd, hpd, hslice⟩ := embedded_boundaryless_slice S R f hS hR hemb p
  exact ⟨hkm, defining_submersion_of_slice S (range f) d hd hslice (f p) hpd⟩

/-- A smooth map has closed fibers in the manifold topology. -/
theorem fiber_closed :
    Specs.SmoothManifolds.Ch03.RegularLevels.fiber_closedType.{u,v} :=
  fiber_closed_proof

/-- A nonempty regular fiber has the required dimension. -/
theorem regular_fiber_dimension :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_dimensionType.{u,v} :=
  regular_fiber_dimension_proof

/-- The regular fiber has its canonical embedded smooth structure. -/
theorem regular_fiber_structure :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_structureType.{u,v} :=
  regular_fiber_structure_proof SliceStructures.slice_structure
    SliceStructures.empty_slice_structure

/-- Inclusion identifies the fiber tangent space with the differential kernel. -/
theorem regular_fiber_tangent :
    Specs.SmoothManifolds.Ch03.RegularLevels.regular_fiber_tangentType.{u} :=
  regular_fiber_tangent_proof

/-- Fibers of maps to zero-dimensional manifolds are open and closed. -/
theorem zero_target_clopen :
    Specs.SmoothManifolds.Ch03.RegularLevels.zero_target_clopenType.{u,v} :=
  zero_target_clopen_proof

/-- An embedded boundaryless submanifold is locally a submersion zero set. -/
theorem local_defining_submersion :
    Specs.SmoothManifolds.Ch03.RegularLevels.local_defining_submersionType.{u,v} :=
  local_defining_submersion_proof

end SmoothManifolds.RegularLevels
