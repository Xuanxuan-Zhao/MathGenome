import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.PlanarDiskIntegralBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C12.OrientedPlanarDiskGeometry
import MathGenome.Internal.MultivariableAnalysis.D04.C12.ClassicalIntegralCalibrations
import MathGenome.Internal.MultivariableAnalysis.D04.C10.NegligibleSeams
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Set Filter Topology Function
open scoped RealInnerProductSpace ContDiff BigOperators Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D04.PlanarDiskIntegralBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.OrientedPlanarDiskGeometry.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.NegligibleSeams.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model

lemma parameters_eq_closedBall (r : ℝ) (hr : 0 ≤ r) :
    diskParameters r = Metric.closedBall 0 r := by
  ext u
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    D04.PlanarDiskGeometry.parameter_norm r hr u

lemma parameters_compact (r : ℝ) (hr : 0 ≤ r) : IsCompact (diskParameters r) := by
  rw [parameters_eq_closedBall r hr]
  exact isCompact_closedBall 0 r

lemma parameters_jordan (r : ℝ) (hr : 0 < r) : Jordan (diskParameters r) :=
  (D04.Calibrations.disk_volume r hr).1

lemma parameters_integrable (r : ℝ) (hr : 0 < r) (f : diskParameters r → ℝ)
    (hf : Continuous f) : RegionIntegrable f := by
  letI : CompactSpace (diskParameters r) :=
    isCompact_iff_compactSpace.mp (parameters_compact r hr.le)
  apply D04.JordanRegions.integrable_of_null_relative_discontinuities (by norm_num)
    (parameters_jordan r hr) f
  · exact ⟨_, fun x => (isCompact_range hf).isBounded.exists_norm_le.choose_spec _ ⟨x,rfl⟩⟩
  · apply D04.NullCovers.null_mono (T := ∅) _ D04.ExceptionalSets.null_empty
    rintro x ⟨hx, hh⟩
    exact (hh hf.continuousAt).elim

/-- Convert a proper region integral to the support-enclosing-box convention.
The integrability assumption rules out identification of undefined values. -/
lemma region_proper {S : Set (E 2)} {f : S → ℝ} (hf : RegionIntegrable f) :
    ProperIntegrable f ∧ coefficientIntegral f = regionIntegral f := by
  have hsup : support (zeroExtension f) ⊆ S := by
    intro u hu
    by_contra h
    exact hu (D04.JordanRegions.zeroExtension_of_not_mem f h)
  obtain ⟨Q,hQ,hi⟩ := hf.2
  have hp : ProperIntegrable f := ⟨(D04.JordanRegions.encloses_bounded hQ).subset hsup,
    Q, (closure_mono hsup).trans hQ, hi⟩
  refine ⟨hp, ?_⟩
  obtain ⟨hi', hv⟩ := D04.DirectedSubstitution.proper_on_box hp Q
    ((closure_mono hsup).trans hQ)
  exact hv.trans (D04.JordanRegions.integral_eq_on_enclosing_box f hf hQ hi').symm

lemma adjoint_apply (A : E 2 →ₗᵢ[ℝ] E 3) (u : E 2) :
    A.toContinuousLinearMap.adjoint (A u) = u := by
  have h := congrArg (fun B : E 2 →L[ℝ] E 2 => B u) A.adjoint_comp_self
  exact h

lemma affine_derivative (x : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (u : E 2) :
    HasFDerivAt (fun v => x + A v) A.toContinuousLinearMap u := by
  convert (A.toContinuousLinearMap.hasFDerivAt.const_add x) using 1
  rfl

/-- The whole compact disk is not a chart. This chart covers precisely its
relative interior; its smaller closed parameter disks are legitimate pieces. -/
def interiorChart (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r) :
    EmbeddedChart 1 2 3 (planarDisk x N r) where
  half := false
  half_pos := by simp
  source := Metric.ball 0 r
  source_open := ⟨Metric.ball 0 r, Metric.isOpen_ball, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := Metric.ball x r
  ambient_open := Metric.isOpen_ball
  toFun u := x + A u
  invFun y := A.toContinuousLinearMap.adjoint (y-x)
  map_source := by
    intro u hu
    have hn : ‖u‖ < r := by simpa using hu
    refine ⟨hmap ▸ ⟨u, (D04.PlanarDiskGeometry.parameter_norm r hr.le u).mpr hn.le, rfl⟩, ?_⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hn
  map_target := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hmap.symm ▸ hy.1
    simpa [adjoint_apply, Metric.mem_ball, dist_eq_norm] using hy.2
  left_inv := by intro u _; simp [adjoint_apply]
  right_inv := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hmap.symm ▸ hy.1
    simp [adjoint_apply]
  continuous_toFun := (continuous_const.add A.continuous).continuousOn
  continuous_invFun := (A.toContinuousLinearMap.adjoint.continuous.comp
    (continuous_id.sub continuous_const)).continuousOn
  regular := by
    intro u hu
    refine ⟨univ, (fun v => x + A v), isOpen_univ, mem_univ _, fun _ _ => rfl,
      (contDiff_const.add A.toContinuousLinearMap.contDiff).contDiffOn, ?_⟩
    intro v _
    rw [(affine_derivative x A v).fderiv]
    exact A.injective

lemma interiorChart_differential (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3)
    (r : ℝ) (hr : 0 < r) (hmap) (u : E 2) (hu : u ∈ Metric.ball 0 r) :
    chartDifferential (interiorChart x N A r hr hmap) u = A.toContinuousLinearMap := by
  exact (D04.EmbeddedChart.differential_extension _ hu isOpen_univ (mem_univ _)
    (fun _ _ => rfl) (affine_derivative x A u).differentiableAt).trans
    (affine_derivative x A u).fderiv

lemma interiorChart_density (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3)
    (r : ℝ) (hr : 0 < r) (hmap) (u : E 2) (hu : u ∈ Metric.ball 0 r) :
    chartDensity (interiorChart x N A r hr hmap) u = 1 := by
  change gramDensity (fun i => chartDifferential (interiorChart x N A r hr hmap) u (standardBasis 2 i)) = 1
  rw [interiorChart_differential x N A r hr hmap u hu]
  dsimp only [gramDensity]
  simp only [LinearIsometry.coe_toContinuousLinearMap, A.inner_map_map]
  have he : (fun i j : Fin 2 => ⟪standardBasis 2 i, standardBasis 2 j⟫) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D04.standardBasis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [he, Matrix.det_one, Real.sqrt_one]

/-- Positive radii increasing towards the desired radius. -/
def innerRadius (r : ℝ) (j : ℕ) : ℝ := r - r / (j + 2 : ℝ)

lemma innerRadius_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < innerRadius r j := by
  have hj : (1 : ℝ) < j + 2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hd : r / (j + 2 : ℝ) < r := (div_lt_self hr hj)
  exact sub_pos.mpr hd

lemma innerRadius_lt {r : ℝ} (hr : 0 < r) (j : ℕ) : innerRadius r j < r := by
  exact sub_lt_self _ (by positivity)

lemma innerRadius_tendsto (r : ℝ) : Tendsto (innerRadius r) atTop (𝓝 r) := by
  have h : Tendsto (fun j : ℕ => r / (j + 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun j : ℕ => r - r / (j + 2 : ℝ)) atTop (𝓝 r)
  simpa only [sub_zero] using (tendsto_const_nhds (x := r)).sub h

lemma compact_inner_disks (r : ℝ) (hr : 0 < r) (K : Set (E 2)) (hK : IsCompact K)
    (hs : K ⊆ Metric.ball 0 r) :
    ∀ᶠ j in atTop, K ⊆ diskParameters (innerRadius r j) := by
  rcases K.eq_empty_or_nonempty with he | he
  · simp [he]
  obtain ⟨u, hu, hm⟩ := hK.exists_isMaxOn he continuous_norm.continuousOn
  have hur : ‖u‖ < r := by simpa using hs hu
  filter_upwards [(innerRadius_tendsto r).eventually_const_lt hur] with j hj v hv
  exact (D04.PlanarDiskGeometry.parameter_norm _ (innerRadius_pos hr j).le v).mpr
    ((hm hv).trans hj.le)

lemma parameter_circle_null (r : ℝ) (hr : 0 < r) :
    Specs.D04.C06.NullCovers.Model.Null (Metric.sphere (0 : E 2) r) := by
  have hj := parameters_jordan r hr
  have hz := (D04.JordanRegions.jordan_iff_boundary (by norm_num) _
    (D04.JordanRegions.jordan_bounded hj)).mp hj
  rw [parameters_eq_closedBall r hr.le, frontier_closedBall _ hr.ne'] at hz
  exact D04.NullCovers.contentZero_null hz

lemma circle_image (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r) :
    (fun u => x + A u) '' Metric.sphere 0 r = planarCircle x N r := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hn : ‖u‖ = r := by simpa using hu
    have hd : x + A u ∈ planarDisk x N r := hmap ▸
      ⟨u, (D04.PlanarDiskGeometry.parameter_norm r hr.le u).mpr hn.le, rfl⟩
    exact ⟨hd.1, by simpa [dist_eq_norm] using hn⟩
  · intro hy
    have hd : y ∈ planarDisk x N r := ⟨hy.1, hy.2.le⟩
    obtain ⟨u, hu, rfl⟩ := hmap.symm ▸ hd
    refine ⟨u, ?_, rfl⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using hy.2

lemma circle_negligible (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r)
    (hM : IsEmbeddedManifold 1 2 (planarDisk x N r)) :
    IsCompact (planarCircle x N r) ∧ AreaNull (planarDisk x N r) (planarCircle x N r) := by
  have he := circle_image x N A r hr hmap
  constructor
  · rw [← he]
    exact (isCompact_sphere 0 r).image (continuous_const.add A.continuous)
  · apply D04.NegligibleSeams.areaNull_of_hausdorff_two_zero hM
    have hz := (D04.NullPreservation.null_iff_hausdorff_zero (by norm_num) _).mp
      (parameter_circle_null r hr)
    have hAff : ContDiff ℝ 1 (fun u : E 2 => x + A u) :=
      contDiff_const.add A.toContinuousLinearMap.contDiff
    have hh := D04.NegligibleSeams.contDiffOn_hausdorff_two_zero isOpen_univ
      hAff.contDiffOn hz
    simpa only [inter_univ, he] using hh

/-- A compact Jordan truncation in the actual affine interior chart. -/
def diskPiece (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r) (j : ℕ) :
    ChartPiece (planarDisk x N r) where
  chart := interiorChart x N A r hr hmap
  domain := diskParameters (innerRadius r j)
  compact := parameters_compact _ (innerRadius_pos hr j).le
  jordan := parameters_jordan _ (innerRadius_pos hr j)
  subset_source := by
    intro u hu
    have hn := (D04.PlanarDiskGeometry.parameter_norm _ (innerRadius_pos hr j).le u).mp hu
    simpa only [interiorChart, Metric.mem_ball, dist_zero_right] using
      hn.trans_lt (innerRadius_lt hr j)

/-- Truncations avoid the genuine circular boundary. No claim that the closed
boundary itself fits in an interior chart is needed. -/
def diskTruncation (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r) (j : ℕ) :
    SurfaceTruncation (planarDisk x N r) (planarCircle x N r) where
  count := 1
  piece _ := diskPiece x N A r hr hmap j
  avoids _ := by
    rintro y ⟨u, hu, rfl⟩
    have hus := (diskPiece x N A r hr hmap j).subset_source hu
    refine ⟨((interiorChart x N A r hr hmap).map_source hus).1, ?_⟩
    intro hc
    have hd : dist (x + A u) x < r :=
      ((interiorChart x N A r hr hmap).map_source hus).2
    exact (ne_of_lt hd) hc.2
  overlaps i k hik := (hik (Subsingleton.elim _ _)).elim

lemma truncationSet_eq (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap) (j : ℕ) :
    truncationSet (diskTruncation x N A r hr hmap j) =
      (fun u => x + A u) '' diskParameters (innerRadius r j) := by
  change (⋃ _ : Fin 1, (fun u => x + A u) '' diskParameters (innerRadius r j)) = _
  exact iUnion_const _

lemma diskTruncation_exhausts (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3) (r : ℝ) (hr : 0 < r)
    (hmap : (fun u => x + A u) '' diskParameters r = planarDisk x N r) :
    ExhaustsComplement (diskTruncation x N A r hr hmap) := by
  intro K hK hs
  let c := interiorChart x N A r hr hmap
  have hright (y : E 3) (hy : y ∈ K) : x + A (c.invFun y) = y := by
    apply c.right_inv
    have hyM := (hs hy).1
    refine ⟨hyM, ?_⟩
    have hn : dist y x < r := lt_of_le_of_ne hyM.2 (fun he => (hs hy).2 ⟨hyM.1, he⟩)
    exact hn
  have hc : Continuous c.invFun :=
    A.toContinuousLinearMap.adjoint.continuous.comp (continuous_id.sub continuous_const)
  have hb : c.invFun '' K ⊆ Metric.ball 0 r := by
    rintro u ⟨y, hy, rfl⟩
    apply c.map_target
    have hyM := (hs hy).1
    exact ⟨hyM, lt_of_le_of_ne hyM.2 (fun he => (hs hy).2 ⟨hyM.1, he⟩)⟩
  filter_upwards [compact_inner_disks r hr _ (hK.image hc) hb] with j hj y hy
  rw [truncationSet_eq]
  exact ⟨c.invFun y, hj ⟨y,hy,rfl⟩, hright y hy⟩

/-- The existing quantitative seam proof works for any compact area-null
exception, as its chart-level theorem states. -/
lemma surface_truncation_limit {M Z : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (hc : IsCompact M) (hZ : IsCompact Z) (hz : AreaNull M Z)
    (f : M → ℝ) (hf : Continuous f) (T : ℕ → SurfaceTruncation M Z)
    (hT : ExhaustsComplement T) :
    Tendsto (fun j => truncationIntegral (T j) f) atTop (𝓝 (surfaceIntegral M f)) := by
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hc
  obtain ⟨P⟩ := D04.ManifoldIntegral.chart_partition_exists hM (univ : Set M) isCompact_univ
  rw [D04SurfaceAssembly.scalar_chart_formula hM hc f hf P (subset_univ _)]
  have hconv := tendsto_finsetSum Finset.univ (fun i _ =>
    D04.NegligibleSeams.chart_truncation_convergence hM hZ hz f hf T hT
      (P.chart i) (P.weight i) (P.partition.1 i).continuous
      (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2)
  simpa only [← D04.NegligibleSeams.truncation_partition_formula hM _ P f hf] using hconv

lemma support_zeroExtension_subset {S : Set (E 2)} (f : S → ℝ) :
    support (zeroExtension f) ⊆ S := by
  intro x hx
  by_contra h
  exact hx (D04.JordanRegions.zeroExtension_of_not_mem f h)

lemma innerParameters_subset (r : ℝ) (hr : 0 < r) (j : ℕ) :
    diskParameters (innerRadius r j) ⊆ diskParameters r := by
  intro u hu
  exact (D04.PlanarDiskGeometry.parameter_norm r hr.le u).mpr
    (((D04.PlanarDiskGeometry.parameter_norm _ (innerRadius_pos hr j).le u).mp hu).trans
      (innerRadius_lt hr j).le)

lemma extension_apply {S : Set (E 2)} (f : S → ℝ) (u : S) :
    zeroExtension f u = f u := by
  exact D04.JordanRegions.zeroExtension_apply f u

lemma extension_of_not_mem {S : Set (E 2)} (f : S → ℝ) {u : E 2} (hu : u ∉ S) :
    zeroExtension f u = 0 := by
  exact D04.JordanRegions.zeroExtension_of_not_mem f hu

/-- The planar Riemann integrals have the same exhaustion limit, proved with
compact null-set majorants. Continuity is only required on the closed disk. -/
lemma planar_truncation_limit (r : ℝ) (hr : 0 < r) (F : E 2 → ℝ)
    (hF : ContinuousOn F (diskParameters r)) :
    Tendsto (fun j => regionIntegral (fun u : diskParameters (innerRadius r j) => F u))
      atTop (𝓝 (regionIntegral (fun u : diskParameters r => F u))) := by
  let a : diskParameters r → ℝ := fun u => F u
  let b (j : ℕ) : diskParameters r → ℝ := fun u =>
    if (u : E 2) ∈ diskParameters (innerRadius r j) then F u else 0
  let f (j : ℕ) : diskParameters (innerRadius r j) → ℝ := fun u => F u
  have haR : RegionIntegrable a := parameters_integrable r hr a hF.domRestrict
  have hfR (j : ℕ) : RegionIntegrable (f j) :=
    parameters_integrable _ (innerRadius_pos hr j) (f j)
      (hF.mono (innerParameters_subset r hr j)).domRestrict
  have hz (j : ℕ) : zeroExtension (b j) = zeroExtension (f j) := by
    funext u
    by_cases hu : u ∈ diskParameters (innerRadius r j)
    · rw [extension_apply (b j) ⟨u, innerParameters_subset r hr j hu⟩,
        extension_apply (f j) ⟨u,hu⟩]
      simp [b, f, hu]
    · rw [extension_of_not_mem (f j) hu]
      by_cases huv : u ∈ diskParameters r
      · rw [extension_apply (b j) ⟨u,huv⟩]
        simp [b, hu]
      · exact extension_of_not_mem (b j) huv
  have hb (j : ℕ) : ProperIntegrable (b j) :=
    (D04.DirectedSubstitution.proper_congr (hz j)).1.mpr (region_proper (hfR j)).1
  have hbval (j : ℕ) : coefficientIntegral (b j) = regionIntegral (f j) :=
    (D04.DirectedSubstitution.proper_congr (hz j)).2.trans (region_proper (hfR j)).2
  obtain ⟨B,hB⟩ := haR.1
  let C := diskParameters r
  let K := Metric.sphere (0 : E 2) r
  have hev (U : Set (E 2)) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∀ᶠ j in atTop, ∀ u ∈ C \ U, u ∉ (∅ : Set (E 2)) →
        zeroExtension a u = zeroExtension (b j) u := by
    have hs : C \ U ⊆ Metric.ball 0 r := by
      intro u hu
      have hn := (D04.PlanarDiskGeometry.parameter_norm r hr.le u).mp hu.1
      have hne : ‖u‖ ≠ r := by
        intro he
        exact hu.2 (hKU (by simpa [K, Metric.mem_sphere] using he))
      simpa using lt_of_le_of_ne hn hne
    filter_upwards [compact_inner_disks r hr (C \ U)
      ((parameters_compact r hr.le).diff hU) hs] with j hj u hu _
    rw [extension_apply a ⟨u,hu.1⟩,
      extension_apply (b j) ⟨u,hu.1⟩]
    simp only [b, if_pos (hj hu)]
    rfl
  have hbound (j : ℕ) (u : E 2) (_ : u ∉ (∅ : Set (E 2))) :
      |zeroExtension a u - zeroExtension (b j) u| ≤ max B 0 := by
    by_cases hu : u ∈ diskParameters r
    · rw [extension_apply a ⟨u,hu⟩,
        extension_apply (b j) ⟨u,hu⟩]
      dsimp only [b]
      split_ifs with ht
      · simp only [a, sub_self, abs_zero]; exact le_max_right _ _
      · simpa only [sub_zero, Real.norm_eq_abs] using (hB ⟨u,hu⟩).trans (le_max_left B 0)
    · rw [extension_of_not_mem a hu,
        extension_of_not_mem (b j) hu, sub_self, abs_zero]
      exact le_max_right _ _
  have h := D04.NegligibleSeams.Riemann.proper_truncation_convergence a b
    (region_proper haR).1 hb C K (parameters_compact r hr.le) (isCompact_sphere 0 r)
    (parameter_circle_null r hr) (support_zeroExtension_subset a)
    (fun j => support_zeroExtension_subset (b j)) (fun _ => ∅)
    (fun _ => D04.ExceptionalSets.null_empty) (max B 0) (le_max_right _ _) hbound hev
  simpa only [hbval, (region_proper haR).2] using h

lemma truncation_integral (x N : E 3) (A : E 2 →ₗᵢ[ℝ] E 3)
    (r : ℝ) (hr : 0 < r) (hmap) (j : ℕ) (g : E 3 → ℝ) :
    truncationIntegral (diskTruncation x N A r hr hmap j)
      (fun y : planarDisk x N r => g y) =
      regionIntegral (fun u : diskParameters (innerRadius r j) => g (x + A u)) := by
  change (∑ i : Fin 1, pieceIntegral (diskPiece x N A r hr hmap j)
    (fun y : planarDisk x N r => g y)) = _
  rw [Fin.sum_univ_one]
  unfold pieceIntegral
  congr 1
  funext u
  change g (x + A u) * chartDensity (interiorChart x N A r hr hmap) u = _
  rw [interiorChart_density x N A r hr hmap u
    ((diskPiece x N A r hr hmap j).subset_source u.property), mul_one]

theorem disk_integral : Specs.D04.C12.PlanarDiskIntegralBridge.disk_integralType := by
  intro x N hN A hmap r hr g hg
  obtain ⟨B, hBorth, hBsurj, hB⟩ := D04.PlanarDiskGeometry.disk_geometry x N hN
  have hc : IsCompact (planarDisk x N r) := by
    exact (D04.compact_iff_isCompact _).mp (hB r hr).2.1
  have hM := (hB r hr).2.2.1
  have hfg : Continuous (fun y : planarDisk x N r => g y) := hg.domRestrict
  have hparam : ContinuousOn (fun u => g (x + A u)) (diskParameters r) :=
    hg.comp (continuous_const.add A.continuous).continuousOn
      (fun u hu => hmap r hr ▸ ⟨u,hu,rfl⟩)
  obtain ⟨P,hPi,_⟩ := D04SurfaceAssembly.scalar_construction hM hc _ hfg
  refine ⟨⟨P,hPi⟩, parameters_integrable r hr _ hparam.domRestrict, ?_⟩
  obtain ⟨hZ,hz⟩ := circle_negligible x N A r hr (hmap r hr) hM
  have hs := surface_truncation_limit hM hc hZ hz _ hfg
    (diskTruncation x N A r hr (hmap r hr))
    (diskTruncation_exhausts x N A r hr (hmap r hr))
  have hp := planar_truncation_limit r hr (fun u => g (x + A u)) hparam
  have he : (fun j => truncationIntegral (diskTruncation x N A r hr (hmap r hr) j)
      (fun y : planarDisk x N r => g y)) =
      (fun j => regionIntegral (fun u : diskParameters (innerRadius r j) => g (x + A u))) := by
    funext j
    exact truncation_integral x N A r hr (hmap r hr) j g
  rw [he] at hs
  exact tendsto_nhds_unique hs hp

theorem disk_area : Specs.D04.C12.PlanarDiskIntegralBridge.disk_areaType := by
  intro x N hN r hr
  obtain ⟨A, _, _, hA⟩ := D04.PlanarDiskGeometry.disk_geometry x N hN
  have he := (disk_integral x N hN A (fun s hs => (hA s hs).1) r hr
    (fun _ => 1) continuousOn_const).2.2
  have hv := D04.JordanRegions.regionIntegral_one (diskParameters r)
  have harea : surfaceIntegral (planarDisk x N r) (fun _ => 1) = Real.pi * r ^ 2 :=
    he.trans (hv.trans (D04.Calibrations.disk_volume r hr).2)
  exact ⟨harea, harea.symm ▸ mul_pos Real.pi_pos (sq_pos_of_pos hr)⟩

end D04.PlanarDiskIntegralBridge
