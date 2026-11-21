import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.TightBoundedContinuousRepresentation
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Separation.CompletelyRegular

noncomputable section

namespace ExpandedFA.Supplements.TightBoundedContinuousRepresentation

open Set MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal CompactlySupported Topology
open Spec

universe u v

theorem uniqueness : Uniqueness.{u} := by
  intro X _ _ _ L μ ν hμ hν hLμ hLν
  let := hμ
  let := hν
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact (hLμ f).2.symm.trans (hLν f).2

/-- Algebraic positivity and normalization already imply the norm bound. -/
theorem positive_normalized_bound {X : Type u} [TopologicalSpace X]
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Positive L) (h1 : L 1 = 1)
    (f : X →ᵇ ℝ) : |L f| ≤ ‖f‖ := by
  have hplus := hpos (‖f‖ • (1 : X →ᵇ ℝ) + f) (fun x => by
    change 0 ≤ ‖f‖ * 1 + f x
    linarith [f.neg_norm_le_apply x])
  have hminus := hpos (‖f‖ • (1 : X →ᵇ ℝ) - f) (fun x => by
    simpa using sub_nonneg.mpr (f.apply_le_norm x))
  simp only [map_add, map_sub, map_smul, h1, smul_eq_mul, mul_one] at hplus hminus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Restriction from a compact ambient space to bounded continuous functions. -/
def compactRestriction {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (j : C(X, Y)) :
    C(Y, ℝ) →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun g := (BoundedContinuousFunction.mkOfCompact g).compContinuous j
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] theorem compactRestriction_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (j : C(X, Y)) (g : C(Y, ℝ)) (x : X) : compactRestriction j g x = g (j x) := rfl

/-- The compact Riesz representation step, before using the tightness estimate. -/
theorem compact_representation {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (j : C(X, Y))
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Positive L) (h1 : L 1 = 1) :
    ∃ ν : Measure Y, ν.Regular ∧ IsProbabilityMeasure ν ∧
      ∀ g : C(Y, ℝ), L (compactRestriction j g) = ∫ y, g y ∂ν := by
  let I : C_c(Y, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => L (compactRestriction j g.toContinuousMap)
      map_add' := fun g h => by
        change L (compactRestriction j (g.toContinuousMap + h.toContinuousMap)) = _
        rw [map_add, map_add]
      map_smul' := fun c g => by
        change L (compactRestriction j (c • g.toContinuousMap)) = _
        rw [map_smul, map_smul]
        rfl }
  let Λ : C_c(Y, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ I (by
    intro g hg
    exact hpos _ (fun x => hg (j x)))
  let ν := RealRMK.rieszMeasure Λ
  have hrep (g : C(Y, ℝ)) : L (compactRestriction j g) = ∫ y, g y ∂ν := by
    let g' : C_c(Y, ℝ) := ⟨g, HasCompactSupport.of_compactSpace g⟩
    exact (RealRMK.integral_rieszMeasure Λ g').symm
  have hmass : ν univ = 1 := by
    have h := hrep 1
    have hr : compactRestriction j (1 : C(Y, ℝ)) = 1 := by ext; rfl
    rw [hr, h1] at h
    have heq : ν.real univ = 1 := by simpa using h.symm
    calc ν univ = ENNReal.ofReal (ν.real univ) := (ofReal_measureReal (μ := ν)).symm
         _ = 1 := by rw [heq]; simp
  exact ⟨ν, inferInstance, ⟨hmass⟩, hrep⟩

/-- Tightness of the functional bounds the mass outside the corresponding
compact image. This only uses cutoffs in the compact ambient space. -/
theorem compact_complement_le {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (j : C(X, Y))
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (ν : Measure Y) [ν.Regular] [IsFiniteMeasure ν]
    (hrep : ∀ g : C(Y, ℝ), L (compactRestriction j g) = ∫ y, g y ∂ν)
    (K : Set X) (hK : IsCompact K) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ f : X →ᵇ ℝ,
      |L f| ≤ ‖f.compContinuous ⟨(Subtype.val : K → X), continuous_subtype_val⟩‖ + ε * ‖f‖) :
    ν (j '' K)ᶜ ≤ ENNReal.ofReal ε := by
  have hJ : IsCompact (j '' K) := hK.image j.continuous
  rw [hJ.isClosed.isOpen_compl.measure_eq_iSup_isCompact ν]
  refine iSup_le fun H => iSup_le fun hHJ => iSup_le fun hH => ?_
  obtain ⟨g, hgJ, hgH, hg01⟩ := exists_continuous_zero_one_of_isClosed
    hJ.isClosed hH.isClosed (disjoint_left.mpr (fun y hyJ hyH => hHJ hyH hyJ))
  let f := compactRestriction j g
  have hfK : f.compContinuous ⟨(Subtype.val : K → X), continuous_subtype_val⟩ = 0 := by
    ext x
    exact hgJ (mem_image_of_mem j x.property)
  have hfnorm : ‖f‖ ≤ 1 := (BoundedContinuousFunction.norm_le zero_le_one).mpr (by
    intro x
    change |g (j x)| ≤ 1
    exact (abs_le.mpr ⟨by linarith [(hg01 (j x)).1], (hg01 (j x)).2⟩))
  have hLf : L f ≤ ε := calc
    L f ≤ |L f| := le_abs_self _
    _ ≤ ‖f.compContinuous ⟨(Subtype.val : K → X), continuous_subtype_val⟩‖ + ε * ‖f‖ := hbound f
    _ ≤ ε := by rw [hfK, norm_zero, zero_add]; nlinarith
  have hgint : Integrable g ν := (BoundedContinuousFunction.mkOfCompact g).integrable ν
  calc
    ν H ≤ ENNReal.ofReal (∫ y, g y ∂ν) :=
      hgint.measure_le_integral (Eventually.of_forall fun y => (hg01 y).1)
        (fun y hy => (hgH hy).ge)
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by rwa [← hrep g])

/-- A Borel set in an embedded Borel space is the preimage of an ambient
Borel set, without any measurability assertion about the full image. -/
theorem exists_borel_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {j : X → Y} (hj : Topology.IsInducing j) {A : Set X} (hA : MeasurableSet A) :
    ∃ B : Set Y, MeasurableSet B ∧ j ⁻¹' B = A := by
  apply MeasurableSpace.measurableSet_comap.mp
  have hm : (inferInstance : MeasurableSpace X) =
      MeasurableSpace.comap j (inferInstance : MeasurableSpace Y) := by
    rw [BorelSpace.measurable_eq (α := X), BorelSpace.measurable_eq (α := Y),
      ← borel_comap, ← hj.eq_induced]
  rwa [← hm]

/-- Full outer mass on the image suffices to make every Borel image
null-measurable; the image need not itself be Borel. -/
theorem nullMeasurable_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {j : X → Y} (hj : Topology.IsEmbedding j) (ν : Measure Y)
    (hrange : ∀ᵐ y ∂ν, y ∈ range j) {A : Set X} (hA : MeasurableSet A) :
    NullMeasurableSet (j '' A) ν := by
  obtain ⟨B, hB, hBA⟩ := exists_borel_preimage hj.isInducing hA
  apply hB.nullMeasurableSet.congr
  filter_upwards [hrange] with y hy
  obtain ⟨x, rfl⟩ := hy
  simp only [mem_image, hj.injective.eq_iff, exists_eq_right]
  exact congrArg (fun s : Set X => x ∈ s) hBA

/-- Pulling back along an embedding with full outer mass recovers the
ambient measure under pushforward. -/
theorem map_comap_of_ae_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {j : X → Y} (hj : Topology.IsEmbedding j) (ν : Measure Y)
    (hrange : ∀ᵐ y ∂ν, y ∈ range j) : (ν.comap j).map j = ν := by
  ext B hB
  rw [Measure.map_apply hj.continuous.measurable hB,
    Measure.comap_preimage j ν hj.injective hj.continuous.measurable
      (fun _ hA => nullMeasurable_image hj ν hrange hA) hB]
  apply measure_congr
  filter_upwards [hrange] with y hy
  simp [hy]

/-- Compact inner regularity transfers through a full-mass embedding. -/
theorem innerRegular_comap_of_ae_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {j : X → Y} (hj : Topology.IsEmbedding j) (ν : Measure Y) [ν.InnerRegular]
    (hrange : ∀ᵐ y ∂ν, y ∈ range j) : (ν.comap j).InnerRegular := by
  have himage := fun A hA => nullMeasurable_image hj ν hrange (A := A) hA
  constructor
  intro A hA r hr
  rw [Measure.comap_apply₀ j ν hj.injective himage hA.nullMeasurableSet] at hr
  obtain ⟨B, hBA, hB, hBeq⟩ := (himage A hA).exists_measurable_subset_ae_eq
  have hrB : r < ν B := by rwa [measure_congr hBeq]
  obtain ⟨H, hHB, hH, hrH⟩ := Measure.InnerRegular.innerRegular hB r hrB
  have hHrange : H ⊆ range j := hHB.trans (hBA.trans (image_subset_range j A))
  refine ⟨j ⁻¹' H, ?_, hj.isInducing.isCompact_preimage' hH hHrange, ?_⟩
  · intro x hx
    exact hj.injective.mem_set_image.mp (hBA (hHB hx))
  · rw [Measure.comap_apply₀ j ν hj.injective himage
      (hj.continuous.measurable hH.measurableSet).nullMeasurableSet,
      image_preimage_eq_of_subset hHrange]
    exact hrH

/-- The complement estimates imply full outer mass on the embedded space. -/
theorem ae_range_of_compactTight {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (j : C(X, Y))
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (ν : Measure Y) [ν.Regular] [IsFiniteMeasure ν]
    (hrep : ∀ g : C(Y, ℝ), L (compactRestriction j g) = ∫ y, g y ∂ν)
    (htight : CompactTight L) : ∀ᵐ y ∂ν, y ∈ range j := by
  rw [ae_iff]
  change ν (range j)ᶜ = 0
  by_contra hne
  obtain ⟨δ, hδ, hδmass⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hne)
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨K, hK, hbound⟩ := htight δ hδreal
  have hle : ν (range j)ᶜ ≤ (δ : ℝ≥0∞) := calc
    ν (range j)ᶜ ≤ ν (j '' K)ᶜ :=
      measure_mono (compl_subset_compl.mpr (image_subset_range j K))
    _ ≤ ENNReal.ofReal δ := compact_complement_le j L ν hrep K hK δ hδreal.le hbound
    _ = δ := ENNReal.ofReal_coe_nnreal
  exact (not_lt_of_ge hle) hδmass

/-- Real bounded continuous functions extend to the native Stone–Čech space.
The compact closed ball keeps this valid even for an empty domain. -/
theorem stoneCechRestriction_surjective (X : Type u) [TopologicalSpace X] :
    Function.Surjective (compactRestriction
      (⟨stoneCechUnit, continuous_stoneCechUnit⟩ : C(X, _root_.StoneCech X))) := by
  intro f
  let g : X → ↥(Metric.closedBall (0 : ℝ) ‖f‖) :=
    fun x => ⟨f x, by simpa using f.norm_coe_le_norm x⟩
  have hg : Continuous g := f.continuous.subtype_mk _
  let F : C(_root_.StoneCech X, ℝ) :=
    ⟨fun z => (stoneCechExtend hg z).val,
      continuous_subtype_val.comp (continuous_stoneCechExtend hg)⟩
  refine ⟨F, ?_⟩
  ext x
  exact congrArg Subtype.val (stoneCechExtend_stoneCechUnit hg x)

/-- The full source assertion on arbitrary metric spaces. In particular,
neither completeness nor separability nor local compactness is assumed. -/
theorem tight_representation : TightRepresentation.{u} := by
  intro X _ _ _ L hpos h1 htight
  let Y := _root_.StoneCech X
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  let j : C(X, Y) := ⟨stoneCechUnit, continuous_stoneCechUnit⟩
  have hj : Topology.IsEmbedding j := isEmbedding_stoneCechUnit
  obtain ⟨ν, hνreg, hνprob, hνrep⟩ := compact_representation j L hpos h1
  let := hνreg
  let := hνprob
  have hrange := ae_range_of_compactTight j L ν hνrep htight
  let μ := ν.comap j
  have hmap : μ.map j = ν := map_comap_of_ae_range hj ν hrange
  have hμmass : μ univ = 1 := by
    have h := congrArg (fun ρ : Measure Y => ρ univ) hmap
    rw [Measure.map_apply j.continuous.measurable MeasurableSet.univ, preimage_univ] at h
    exact h.trans (measure_univ : ν univ = 1)
  have : μ.InnerRegular := innerRegular_comap_of_ae_range hj ν hrange
  have hμrep : Represents L μ := by
    intro f
    obtain ⟨g, hg⟩ := stoneCechRestriction_surjective X f
    refine ⟨f.integrable μ, ?_⟩
    calc
      L f = L (compactRestriction j g) := by rw [hg]
      _ = ∫ y, g y ∂ν := hνrep g
      _ = ∫ x, g (j x) ∂μ := by
        rw [← hmap]
        exact integral_map j.continuous.measurable.aemeasurable
          g.continuous.measurable.aestronglyMeasurable
      _ = ∫ x, f x ∂μ := by
        congr 1
        exact congrArg (fun b : X →ᵇ ℝ => (b : X → ℝ)) hg
  refine ⟨μ, ⟨hμmass, ?_, ?_⟩, hμrep, ?_⟩
  · intro ε hε
    obtain ⟨K, _, hK, hsmall⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
      (measure_ne_top μ univ) hε
    exact ⟨K, hK, by simpa only [← compl_eq_univ_sdiff] using hsmall⟩
  · intro A hA
    exact hA.measure_eq_iSup_isCompact μ
  · intro η hη hηrep
    exact uniqueness X L η μ hη inferInstance hηrep hμrep

end ExpandedFA.Supplements.TightBoundedContinuousRepresentation
