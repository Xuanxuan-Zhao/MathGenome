import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleMetrics
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace SmoothManifolds.BundleMetrics
open ModelData AtlasData MapData BundleData FrameData BundleMetricData Bundle Set Filter
open scoped Topology
universe u v w

section Construction
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- The linear coordinate map, extended by zero away from its domain. -/
noncomputable def coordinateMap (i : ι) (p : M) : E p →ₗ[ℝ] Euclidean r := by
  letI := B.linear i
  exact (B.trivialization i).linearMapAt ℝ p

@[simp] theorem coordinateMap_of_mem (i : ι) (p : M) (hp : p ∈ B.baseSet i) (x : E p) :
    coordinateMap B i p x = ((B.trivialization i) ⟨p, x⟩).2 := by
  let := B.linear i
  exact congrFun ((B.trivialization i).coe_linearMapAt_of_mem
    ((B.trivialization_baseSet i).symm ▸ hp)) x

/-- The ordinary Euclidean inner product transported to one bundle chart. -/
noncomputable def localForm (i : ι) (p : M) : LinearMap.BilinForm ℝ (E p) :=
  ∑ j : Fin r, LinearMap.BilinForm.linMulLin
    ((LinearMap.proj j).comp (coordinateMap B i p))
    ((LinearMap.proj j).comp (coordinateMap B i p))

@[simp] theorem localForm_apply (i : ι) (p : M) (x y : E p) :
    localForm B i p x y = ∑ j : Fin r, coordinateMap B i p x j * coordinateMap B i p y j := by
  simp [localForm]

theorem localForm_symmetric (i : ι) (p : M) (x y : E p) :
    localForm B i p x y = localForm B i p y x := by
  simp only [localForm_apply, mul_comm]

theorem localForm_nonneg (i : ι) (p : M) (x : E p) : 0 ≤ localForm B i p x x := by
  rw [localForm_apply]
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)

theorem localForm_positive (i : ι) (p : M) (hp : p ∈ B.baseSet i)
    (x : E p) (hx : x ≠ 0) : 0 < localForm B i p x x := by
  rw [localForm_apply]
  have hne : coordinateMap B i p x ≠ 0 := by
    intro hz
    apply hx
    apply (B.fiberCoordinates i p hp).injective
    rw [map_zero]
    simpa only [coordinateMap_of_mem B i p hp,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply] using hz
  exact lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hne))

/-- Original coordinate changes are smooth on their overlaps, proved from
smoothness of the given bundle charts and their inverses. -/
theorem transitionVector_smoothAt (i j : ι) (v : Euclidean r) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ B.baseSet j) :
    VectorSmoothAt S.smoothStructure.val
      (fun q => coordinateMap B j q ((B.trivialization i).symm q v)) p := by
  have hopen (k : ι) : IsOpen (B.baseSet k) :=
    (B.trivialization_baseSet k) ▸ (B.trivialization k).open_baseSet
  let f : M → TotalSpace (Euclidean r) E :=
    fun q => ⟨q, (B.trivialization i).symm q v⟩
  have hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val f p := by
    apply Frames.smoothAt_from_trivialization B S.smoothStructure.property.1 i hi
      (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
      (FrameData.VectorSmoothAt.const _ v p) (fun _ => rfl)
    filter_upwards [(hopen i).mem_nhds hi] with q hq
    exact (B.fiberCoordinates i q hq).apply_symm_apply v
  have ht := (Frames.trivializationCoordinates_smoothAt B j (f p) hj).comp
    B.totalManifold.smoothStructure.property.1.1 hs
  apply ht.congr
  filter_upwards [(hopen j).mem_nhds hj] with q hq
  exact (coordinateMap_of_mem B j q hq _).symm

/-- A local form has smooth Gram coefficients in every other bundle chart. -/
theorem localForm_gram_smoothAt (i j : ι) (l k : Fin r) (p : M)
    (hi : p ∈ B.baseSet i) (hj : p ∈ B.baseSet j) :
    VectorSmoothAt S.smoothStructure.val
      (fun q => localForm B j q ((B.trivialization i).symm q (Pi.single l 1))
        ((B.trivialization i).symm q (Pi.single k 1))) p := by
  simp only [localForm_apply]
  apply FrameData.VectorSmoothAt.sum
  intro m
  have hl := (transitionVector_smoothAt B i j (Pi.single l 1) p hi hj).postcomp
    (ContinuousLinearMap.proj (R := ℝ) m).contDiff
  have hk := (transitionVector_smoothAt B i j (Pi.single k 1) p hi hj).postcomp
    (ContinuousLinearMap.proj (R := ℝ) m).contDiff
  exact (hl.prod hk).postcomp (contDiff_fst.mul contDiff_snd)

/-- The closed supports containing a point form a finite set. -/
noncomputable def activeCharts (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (p : M) : Finset ι :=
  (hf.point_finite p).toFinset

@[simp] theorem mem_activeCharts (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (i : ι) (p : M) :
    i ∈ activeCharts ρ hf p ↔ p ∈ sectionSupport (ρ i) := Set.Finite.mem_toFinset _

/-- A finite sum of bilinear forms in each actual fiber. -/
noncomputable def averagedForm (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (p : M) :
    LinearMap.BilinForm ℝ (E p) :=
  ∑ i ∈ activeCharts ρ hf p, ρ i p • localForm B i p

@[simp] theorem averagedForm_apply (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (p : M) (x y : E p) :
    averagedForm B ρ hf p x y =
      ∑ i ∈ activeCharts ρ hf p, ρ i p * localForm B i p x y := by
  simp [averagedForm]

theorem averagedForm_eq_finsum (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (p : M) (x y : E p) :
    averagedForm B ρ hf p x y = ∑ᶠ i, ρ i p * localForm B i p x y := by
  classical
  rw [averagedForm_apply]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (mem_activeCharts ρ hf i p).mpr
  exact subset_closure (left_ne_zero_of_mul hi)

theorem averagedForm_symmetric (ρ : ι → M → ℝ)
    (hf : LocallyFinite (fun i => sectionSupport (ρ i))) (p : M) (x y : E p) :
    averagedForm B ρ hf p x y = averagedForm B ρ hf p y x := by
  simp only [averagedForm_apply, localForm_symmetric B _ p x y]

theorem averagedForm_positive (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate B.baseSet ρ) (p : M) (x : E p) (hx : x ≠ 0) :
    0 < averagedForm B ρ hρ.2.2.1 p x x := by
  classical
  rw [averagedForm_apply]
  have hex : ∃ i, ρ i p ≠ 0 := by
    by_contra! hh
    have hz : (∑ᶠ i, ρ i p) = 0 := by simp only [hh, finsum_zero]
    have ho := hρ.2.2.2 p
    rw [hz] at ho
    exact zero_ne_one ho
  obtain ⟨i, hi⟩ := hex
  have hmem : p ∈ sectionSupport (ρ i) := subset_closure hi
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hρ.2.1 j p) (localForm_nonneg B j p x)
  · exact ⟨i, (mem_activeCharts ρ hρ.2.2.1 i p).mpr hmem,
      mul_pos (lt_of_le_of_ne (hρ.2.1 i p) (Ne.symm hi))
        (localForm_positive B i p (hsub i hmem) x hx)⟩

/-- Subordination by closed supports makes each weighted local metric smooth
across the edge of its domain. At a point outside the support it vanishes on a
whole neighborhood. -/
theorem weightedGram_smoothAt (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate B.baseSet ρ)
    (i j : ι) (l k : Fin r) (p : M) (hi : p ∈ B.baseSet i) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun q => ρ j q * localForm B j q ((B.trivialization i).symm q (Pi.single l 1))
        ((B.trivialization i).symm q (Pi.single k 1))) p := by
  by_cases hj : p ∈ sectionSupport (ρ j)
  · exact ScalarContDiffAt.mul (hρ.1 j p)
      ((scalarContDiffAt_iff _ _ _ _).mpr
        (localForm_gram_smoothAt B i j l k p hi (hsub j hj)))
  · apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ 0 p)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hj] with q hq
    have hz : ρ j q = 0 := by
      by_contra hn
      exact hq (subset_closure hn)
    simp only [hz, zero_mul]

/-- The locally finite average has smooth coefficients on every chart. -/
theorem averagedForm_smooth (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate B.baseSet ρ) (i : ι) (l k : Fin r) :
    SmoothOnBase S
      (fun q => averagedForm B ρ hρ.2.2.1 q
        ((B.trivialization i).symm q (Pi.single l 1))
        ((B.trivialization i).symm q (Pi.single k 1))) (B.baseSet i) := by
  let f : ι → M → ℝ := fun j q => ρ j q * localForm B j q
    ((B.trivialization i).symm q (Pi.single l 1))
    ((B.trivialization i).symm q (Pi.single k 1))
  have hlf : LocallyFinite (fun j => sectionSupport (f j)) :=
    hρ.2.2.1.subset (fun j => closure_mono (fun q hq => left_ne_zero_of_mul hq))
  intro p hp
  obtain ⟨s, hs⟩ := locallyFinite_eventuallyEq_finsum hlf p
  have hfin : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun q => ∑ j ∈ s, f j q) p :=
    ScalarContDiffAt.sum s (fun j _ => weightedGram_smoothAt B ρ hρ hsub i j l k p hp)
  have hsum := ScalarContDiffAt.congr hfin hs.symm
  have hvec : VectorSmoothAt S.smoothStructure.val (fun q => ∑ᶠ j, f j q) p :=
    (scalarContDiffAt_iff _ _ _ _).mp hsum
  exact hvec.congr (Eventually.of_forall (fun q =>
    (averagedForm_eq_finsum B ρ hρ.2.2.1 q _ _).symm))

/-- Construct a metric from a subordinate smooth partition of unity. -/
noncomputable def metricOfPartition (ρ : ι → M → ℝ)
    (hρ : PartitionData.IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : PartitionData.IsSubordinate B.baseSet ρ) : SmoothFiberMetric B where
  form := averagedForm B ρ hρ.2.2.1
  symmetric := averagedForm_symmetric B ρ hρ.2.2.1
  positive := averagedForm_positive B ρ hρ hsub
  smooth := averagedForm_smooth B ρ hρ hsub

end Construction

/-- Every smooth real finite-rank vector bundle admits a smooth fiber metric,
including over ordinary-boundary manifolds and in rank zero. -/
theorem exists_smoothFiberMetric :
    Specs.SmoothManifolds.Ch05.BundleMetrics.exists_smoothFiberMetricType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S B.baseSet
    (fun i => (B.trivialization_baseSet i) ▸ (B.trivialization i).open_baseSet) B.covers
  exact ⟨metricOfPartition B ρ hρ hsub⟩

end SmoothManifolds.BundleMetrics
