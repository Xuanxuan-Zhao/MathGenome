import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.OrientedPlanarDiskGeometry
import MathGenome.Internal.MultivariableAnalysis.D04.C12.DiskHemisphereAndBoxSigns
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace D04.PlanarDiskGeometry
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C12.OrientedPlanarDiskGeometry
open Model

abbrev diskParameters := Model.diskParameters
abbrev planarDisk := Model.planarDisk
abbrev planarCircle := Model.planarCircle

local notation "HDisk" => Specs.D04.C12.DiskHemisphereAndBoxSigns.Model.disk
local notation "HCircle" => Specs.D04.C12.DiskHemisphereAndBoxSigns.Model.equator

open private norm_sq3 inner3 basis3 from MathGenome.Internal.MultivariableAnalysis.D04.C12.DiskHemisphereAndBoxSigns

lemma norm_sq2 (u : E 2) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    star_trivial]
  norm_num [pow_two]

/-- Inclusion of the horizontal parameter plane with its Euclidean metric. -/
def horizontalInclusion : E 2 →ₗᵢ[ℝ] E 3 where
  toLinearMap :=
    { toFun := fun u => WithLp.toLp 2 ![u 0, u 1, 0]
      map_add' := by intro u v; ext i; fin_cases i <;> simp
      map_smul' := by intro t u; ext i; fin_cases i <;> simp }
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq3, norm_sq2]
    simp

def horizontalProjection : E 3 →L[ℝ] E 2 :=
  (show E 3 →ₗ[ℝ] E 2 from
    { toFun := fun y => WithLp.toLp 2 ![y 0, y 1]
      map_add' := by intro u v; ext i; fin_cases i <;> simp
      map_smul' := by intro t u; ext i; fin_cases i <;> simp }).toContinuousLinearMap

@[simp] lemma horizontalProjection_inclusion (u : E 2) :
    horizontalProjection (horizontalInclusion u) = u := by
  ext i; fin_cases i <;> rfl

lemma inclusion_projection {y : E 3} (hy : y 2 = 0) :
    horizontalInclusion (horizontalProjection y) = y := by
  ext i; fin_cases i <;> first | rfl | exact hy.symm

lemma horizontal_inner (y : E 3) : ⟪y, standardBasis 3 2⟫ = y 2 := by
  simp [inner3, D04.standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]

/-- An interior chart for the closed horizontal disk. -/
def horizontalInteriorChart (r : ℝ) : EmbeddedChart 1 2 3 (HDisk r) where
  half := false
  half_pos := by simp
  source := {u | u 0 ^ 2 + u 1 ^ 2 < r ^ 2}
  source_open := ⟨{u | u 0 ^ 2 + u 1 ^ 2 < r ^ 2},
    isOpen_lt (by fun_prop) continuous_const, by simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := {y | y 0 ^ 2 + y 1 ^ 2 < r ^ 2}
  ambient_open := isOpen_lt (by fun_prop) continuous_const
  toFun := horizontalInclusion
  invFun := horizontalProjection
  map_source := by intro u hu; exact ⟨⟨rfl, hu.le⟩, hu⟩
  map_target := by intro y hy; exact hy.2
  left_inv := by intro u _; exact horizontalProjection_inclusion u
  right_inv := by intro y hy; exact inclusion_projection hy.1.1
  continuous_toFun := horizontalInclusion.continuous.continuousOn
  continuous_invFun := horizontalProjection.continuous.continuousOn
  regular := by
    intro u hu
    refine ⟨univ, horizontalInclusion, isOpen_univ, mem_univ _,
      fun _ _ => rfl, horizontalInclusion.toContinuousLinearMap.contDiff.contDiffOn, ?_⟩
    intro v _
    change Function.Injective (fderiv ℝ horizontalInclusion.toContinuousLinearMap v)
    rw [horizontalInclusion.toContinuousLinearMap.fderiv]
    exact horizontalInclusion.injective

lemma horizontal_manifold (r : ℝ) (hr : 0 < r) : IsEmbeddedManifold 1 2 (HDisk r) := by
  refine ⟨⟨le_rfl, by simp⟩, by norm_num, ?_⟩
  intro y hy
  rcases lt_or_eq_of_le hy.2 with hlt | heq
  · refine ⟨horizontalInteriorChart r, horizontalProjection y, ⟨hlt, ?_⟩,
      inclusion_projection hy.1⟩
    simp [horizontalInteriorChart]
  · obtain ⟨_, c, u, hc, hu, hf, hp⟩ := (D04.SignExamples.disk_signs r hr y ⟨hy.1, heq⟩).1
    exact ⟨c, u, ⟨hu, fun _ => hf⟩, hp⟩

lemma horizontal_boundary (r : ℝ) (hr : 0 < r) :
    intrinsicBoundary 1 2 (HDisk r) = HCircle r := by
  ext y
  constructor
  · intro hy
    have hym := hy.1
    refine ⟨hym.1, ?_⟩
    apply le_antisymm hym.2
    by_contra h
    have hlt : y 0 ^ 2 + y 1 ^ 2 < r ^ 2 := lt_of_not_ge h
    let c := horizontalInteriorChart r
    have hu : horizontalProjection y ∈ c.source := hlt
    have hh := (D04.chart_intrinsicBoundary c ⟨le_rfl, by simp⟩ (by norm_num)
      _ hu).mp ((inclusion_projection hym.1).symm ▸ hy)
    exact Bool.noConfusion hh.1
  · intro hy
    exact (D04.SignExamples.disk_signs r hr y hy).1

/-- Transport a chart by an ambient rigid affine map. -/
def affineChart {M P : Set (E 3)} (e : E 3 ≃ₗᵢ[ℝ] E 3) (x : E 3)
    (he : ∀ y, x + e y ∈ P ↔ y ∈ M) (c : EmbeddedChart 1 2 3 M) :
    EmbeddedChart 1 2 3 P where
  half := c.half
  half_pos := c.half_pos
  source := c.source
  source_open := c.source_open
  ambient := (fun y => e.symm (y - x)) ⁻¹' c.ambient
  ambient_open := c.ambient_open.preimage (by fun_prop)
  toFun := fun u => x + e (c.toFun u)
  invFun := fun y => c.invFun (e.symm (y - x))
  map_source := by
    intro u hu
    exact ⟨(he _).mpr (c.map_source hu).1, by simpa using (c.map_source hu).2⟩
  map_target := by
    intro y hy
    apply c.map_target
    exact ⟨(he _).mp (by simpa using hy.1), hy.2⟩
  left_inv := by intro u hu; simpa using c.left_inv u hu
  right_inv := by
    intro y hy
    rw [c.right_inv _ ⟨(he _).mp (by simpa using hy.1), hy.2⟩, e.apply_symm_apply]
    abel
  continuous_toFun := continuous_const.continuousOn.add
    (e.continuous.comp_continuousOn c.continuous_toFun)
  continuous_invFun := c.continuous_invFun.comp (by fun_prop)
    (fun y hy => ⟨(he _).mp (by simpa using hy.1), hy.2⟩)
  regular := by
    intro u hu
    obtain ⟨W, g, hW, huW, hg, hgd, hgi⟩ := c.regular u hu
    refine ⟨W, fun v => x + e (g v), hW, huW,
      fun v hv => congrArg (fun z => x + e z) (hg hv),
      contDiffOn_const.add (e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hgd), ?_⟩
    intro v hv
    have hd := (hgd.differentiableOn (by simp) v hv).differentiableAt (hW.mem_nhds hv)
    have hcomp := ((e.toContinuousLinearEquiv.hasFDerivAt.comp v hd.hasFDerivAt).const_add x).fderiv
    change Function.Injective (fderiv ℝ (fun z => x + (e.toContinuousLinearEquiv ∘ g) z) v)
    rw [hcomp]
    exact e.injective.comp (hgi v hv)

lemma affine_manifold {M P : Set (E 3)} (e : E 3 ≃ₗᵢ[ℝ] E 3) (x : E 3)
    (he : ∀ y, x + e y ∈ P ↔ y ∈ M) (hM : IsEmbeddedManifold 1 2 M) :
    IsEmbeddedManifold 1 2 P := by
  refine ⟨hM.1, hM.2.1, ?_⟩
  intro y hy
  have hz : e.symm (y - x) ∈ M := (he _).mp (by simpa using hy)
  obtain ⟨c, u, hu, hp⟩ := hM.2.2 _ hz
  refine ⟨affineChart e x he c, u, hu, ?_⟩
  change x + e (c.toFun u) = y
  rw [hp, e.apply_symm_apply]
  abel

lemma affine_boundary {M P : Set (E 3)} (e : E 3 ≃ₗᵢ[ℝ] E 3) (x : E 3)
    (he : ∀ y, x + e y ∈ P ↔ y ∈ M) :
    intrinsicBoundary 1 2 P =
      (fun y => x + e y) '' intrinsicBoundary 1 2 M := by
  have hf : ∀ y, e.symm (-x) + e.symm y ∈ M ↔ y ∈ P := by
    intro y
    simpa [map_add, ← map_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (he (e.symm (y - x))).symm
  ext y
  constructor
  · rintro ⟨hym, c, u, hc, hu, hflat, hp⟩
    let d := affineChart e.symm (e.symm (-x)) hf c
    have hb : d.toFun u ∈ intrinsicBoundary 1 2 M :=
      ⟨(d.map_source hu).1, d, u, hc, hu, hflat, rfl⟩
    refine ⟨d.toFun u, hb, ?_⟩
    change x + e (e.symm (-x) + e.symm (c.toFun u)) = y
    simp [hp]
  · rintro ⟨z, ⟨hzm, c, u, hc, hu, hflat, hp⟩, rfl⟩
    let d := affineChart e x he c
    have hb : d.toFun u ∈ intrinsicBoundary 1 2 P :=
      ⟨(d.map_source hu).1, d, u, hc, hu, hflat, rfl⟩
    simpa only [d, affineChart, hp] using hb

/-- A constraint valid on the manifold annihilates every canonical tangent,
including tangent vectors at the intrinsic boundary. -/
lemma tangent_orthogonal {M : Set (E 3)} (hM : IsEmbeddedManifold 1 2 M)
    (x N : E 3) (hc : ∀ y ∈ M, ⟪y - x, N⟫ = 0)
    (y : M) : ∀ v ∈ tangentSpace 1 2 M y, ⟪N, v⟫ = 0 := by
  obtain ⟨c, u, hu, hp⟩ := hM.2.2 y y.property
  have hd := (innerSL ℝ N).hasFDerivAt.comp_hasFDerivWithinAt u
    ((D04.EmbeddedChart.hasDifferential c hM.1 hu.1).sub_const x)
  have hz : HasFDerivWithinAt (𝕜 := ℝ) (fun t => ⟪N, c.toFun t - x⟫) 0 c.source u := by
    apply (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ℝ) u c.source).congr' _ hu.1
    intro t ht
    exact (real_inner_comm _ _).trans (hc _ (c.map_source ht).1)
  have he := (D04.EmbeddedChart.source_uniqueDiff c u hu.1).eq hd hz
  intro v hv
  rw [← hp] at hv
  have hv' : v ∈ LinearMap.range (chartDifferential c u).toLinearMap :=
    (D04.tangentSpace_chart c hM.1 hM.2.1 u hu.1) ▸ hv
  obtain ⟨w, rfl⟩ := hv'
  exact congrArg (fun L : E 2 →L[ℝ] ℝ => L w) he

lemma planar_compact (x N : E 3) (r : ℝ) : Compact (planarDisk x N r) := by
  apply (D04.compact_iff_isCompact _).mpr
  have hc : IsClosed {y : E 3 | ⟪y - x, N⟫ = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  exact (isCompact_closedBall x r).inter_left hc

lemma horizontal_disk_norm (r : ℝ) (hr : 0 ≤ r) (y : E 3) :
    y ∈ HDisk r ↔ y 2 = 0 ∧ ‖y‖ ≤ r := by
  change (y 2 = 0 ∧ y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2) ↔ _
  constructor
  · rintro ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    have hh := norm_sq3 y
    rw [hz] at hh
    nlinarith [norm_nonneg y]
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    have hh := norm_sq3 y
    rw [hz] at hh
    nlinarith [norm_nonneg y]

lemma horizontal_circle_norm (r : ℝ) (hr : 0 ≤ r) (y : E 3) :
    y ∈ HCircle r ↔ y 2 = 0 ∧ ‖y‖ = r := by
  change (y 2 = 0 ∧ y 0 ^ 2 + y 1 ^ 2 = r ^ 2) ↔ _
  constructor
  · rintro ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    have hh := norm_sq3 y
    rw [hz] at hh
    nlinarith [norm_nonneg y]
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    have hh := norm_sq3 y
    rw [hz, hn] at hh
    nlinarith

lemma parameter_norm (r : ℝ) (hr : 0 ≤ r) (u : E 2) :
    u ∈ diskParameters r ↔ ‖u‖ ≤ r := by
  change u 0 ^ 2 + u 1 ^ 2 ≤ r ^ 2 ↔ _
  rw [← norm_sq2]
  exact sq_le_sq₀ (norm_nonneg u) hr

/-- Orthogonal reflection supplies an ambient isometry carrying the vertical
unit vector to the prescribed unit normal. -/
lemma normal_isometry (N : E 3) (hN : ‖N‖ = 1) :
    ∃ e : E 3 ≃ₗᵢ[ℝ] E 3, e (standardBasis 3 2) = N := by
  refine ⟨(ℝ ∙ (standardBasis 3 2 - N))ᗮ.reflection, ?_⟩
  apply Submodule.reflection_sub
  change ‖(EuclideanSpace.basisFun (Fin 3) ℝ) 2‖ = ‖N‖
  simp [hN]

lemma disk_transport (x N : E 3) (e : E 3 ≃ₗᵢ[ℝ] E 3)
    (he : e (standardBasis 3 2) = N) (r : ℝ) (hr : 0 ≤ r) (y : E 3) :
    x + e y ∈ planarDisk x N r ↔ y ∈ HDisk r := by
  rw [horizontal_disk_norm r hr]
  change (⟪x + e y - x, N⟫ = 0 ∧ dist (x + e y) x ≤ r) ↔ _
  rw [add_sub_cancel_left, ← he, e.inner_map_map, horizontal_inner]
  simp [dist_eq_norm]

lemma circle_transport (x N : E 3) (e : E 3 ≃ₗᵢ[ℝ] E 3)
    (he : e (standardBasis 3 2) = N) (r : ℝ) (hr : 0 ≤ r) :
    (fun y => x + e y) '' HCircle r = planarCircle x N r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz, hn⟩ := (horizontal_circle_norm r hr z).mp hz
    change ⟪x + e z - x, N⟫ = 0 ∧ dist (x + e z) x = r
    rw [add_sub_cancel_left, ← he, e.inner_map_map, horizontal_inner]
    exact ⟨hz, by simpa [dist_eq_norm] using hn⟩
  · intro hy
    refine ⟨e.symm (y - x), ?_, by simp⟩
    apply (horizontal_circle_norm r hr _).mpr
    constructor
    · rw [← horizontal_inner, ← e.inner_map_map, he, e.apply_symm_apply]
      exact hy.1
    · rw [e.symm.norm_map]
      simpa only [dist_eq_norm] using hy.2

theorem disk_geometry : disk_geometryType := by
  intro x N hN
  obtain ⟨e, he⟩ := normal_isometry N hN
  let A : E 2 →ₗᵢ[ℝ] E 3 := e.toLinearIsometry.comp horizontalInclusion
  have hA (u : E 2) : ⟪A u, N⟫ = 0 := by
    change ⟪e (horizontalInclusion u), N⟫ = 0
    rw [← he, e.inner_map_map, horizontal_inner]
    rfl
  have hsurj (v : E 3) (hv : ⟪v, N⟫ = 0) : ∃ u, A u = v := by
    have hz : (e.symm v) 2 = 0 := by
      rw [← horizontal_inner, ← e.inner_map_map, he, e.apply_symm_apply]
      exact hv
    refine ⟨horizontalProjection (e.symm v), ?_⟩
    change e (horizontalInclusion (horizontalProjection (e.symm v))) = v
    rw [inclusion_projection hz, e.apply_symm_apply]
  refine ⟨A, hA, hsurj, ?_⟩
  intro r hr
  have htrans := disk_transport x N e he r hr.le
  have hM := affine_manifold e x htrans (horizontal_manifold r hr)
  refine ⟨?_, planar_compact x N r, hM, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      change ⟪x + A u - x, N⟫ = 0 ∧ dist (x + A u) x ≤ r
      rw [add_sub_cancel_left]
      exact ⟨hA u, by simpa [dist_eq_norm] using (parameter_norm r hr.le u).mp hu⟩
    · intro hy
      obtain ⟨u, hu⟩ := hsurj (y - x) hy.1
      refine ⟨u, ?_, ?_⟩
      · apply (parameter_norm r hr.le u).mpr
        rw [← A.norm_map, hu]
        exact hy.2
      · change x + A u = y
        rw [hu]; abel
  · exact (affine_boundary e x htrans).trans
      ((congrArg (fun S => (fun y => x + e y) '' S) (horizontal_boundary r hr)).trans
        (circle_transport x N e he r hr.le))
  · refine ⟨⟨fun _ => N, continuous_const, ?_⟩, fun _ => rfl⟩
    intro y
    exact ⟨hN, tangent_orthogonal hM x N (fun _ hy => hy.1) y⟩

end D04.PlanarDiskGeometry
