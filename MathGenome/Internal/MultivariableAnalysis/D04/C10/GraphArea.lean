import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.GraphArea
import MathGenome.Internal.MultivariableAnalysis.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C07.CoordinateSeamsVolumes
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set Function Filter Topology
open scoped RealInnerProductSpace
namespace D04.GraphArea
open PatchGeometryGram AreaIntegral JordanRegions Darboux
open Specs.D04.C07.CoordinateSeamsVolumes.Model
open Specs.D04.C07.CoordinateCharts.Model

abbrev graphMap := Specs.D04.C10.GraphArea.Model.graphMap
abbrev graphPartial := Specs.D04.C10.GraphArea.Model.graphPartial
abbrev paraboloidHeight := Specs.D04.C10.GraphArea.Model.paraboloidHeight
abbrev radialIntegral := Specs.D04.C10.GraphArea.Model.radialIntegral
abbrev polarSeam := Specs.D04.C10.GraphArea.Model.polarSeam

/-- The derivative of a graph retains its two input coordinates. -/
def graphDerivative (L : E 2 →L[ℝ] ℝ) : E 2 →L[ℝ] E 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![EuclideanSpace.proj 0, EuclideanSpace.proj 1, L])

lemma graphDerivative_apply (L : E 2 →L[ℝ] ℝ) (v : E 2) :
    graphDerivative L v = WithLp.toLp 2 ![v 0, v 1, L v] := by
  ext i
  fin_cases i <;> simp [graphDerivative]

lemma graph_hasFDerivAt (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (graphMap g) (graphDerivative (fderiv ℝ g x)) x := by
  apply (PiLp.hasFDerivAt_toLp 2 _).comp x
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  · exact hg.hasFDerivAt

lemma graph_columns (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    columns (fderiv ℝ (graphMap g) x).toLinearMap 0 = WithLp.toLp 2 ![1, 0, graphPartial g x 0] ∧
    columns (fderiv ℝ (graphMap g) x).toLinearMap 1 = WithLp.toLp 2 ![0, 1, graphPartial g x 1] := by
  rw [(graph_hasFDerivAt g x hg).fderiv]
  constructor <;> ext i <;> fin_cases i <;>
    simp [columns, Specs.D04.C10.PatchGeometryGram.columnsValue,
      Specs.D04.C10.PatchGeometryGram.Model.columns, graphDerivative_apply,
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
      EuclideanSpace.basisFun_apply, graphPartial, Specs.D04.C10.GraphArea.Model.graphPartial]

lemma graph_derivative_injective (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    Injective (fderiv ℝ (graphMap g) x) := by
  rw [(graph_hasFDerivAt g x hg).fderiv]
  intro v w h
  ext i
  fin_cases i
  · exact congrArg (fun z : E 3 => z 0) h
  · exact congrArg (fun z : E 3 => z 1) h

lemma graph_cross (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    areaVector (graphMap g) x = WithLp.toLp 2 ![-graphPartial g x 0, -graphPartial g x 1, 1] := by
  change cross (columns _ 0) (columns _ 1) = _
  rw [(graph_columns g x hg).1, (graph_columns g x hg).2]
  ext i
  fin_cases i <;>
    simp [cross, Specs.D04.C10.PatchGeometryGram.crossValue,
      Specs.D04.C10.PatchGeometryGram.Model.cross, crossProduct]

lemma graph_density (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    patchJacobian (graphMap g) x =
      Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2) := by
  change gramFactor _ = _
  rw [gram_cross]
  change ‖areaVector (graphMap g) x‖ = _
  rw [graph_cross g x hg, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

lemma graph_regular : Specs.D04.C10.GraphArea.graph_regularType := by
  intro U g hU hg
  have hcg : ContDiffOn ℝ 1 (graphMap g) U := by
    apply PiLp.contDiff_toLp.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
    · exact hg
  refine ⟨⟨hU, hcg, fun x hx => graph_derivative_injective g x
    ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)⟩, ?_⟩
  apply Topology.IsEmbedding.of_comp
    (continuousOn_iff_continuous_domRestrict.mp hcg.continuousOn)
    (g := fun y : E 3 => WithLp.toLp 2 ![y 0, y 1])
  · fun_prop
  · convert Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ U) using 1
    funext x
    ext i
    fin_cases i <;> rfl

lemma graph_upward (g : E 2 → ℝ) (x : E 2) (hg : DifferentiableAt ℝ g x) :
    IsUnitNormal (tangentPlane (graphMap g) x) (unitNormal (graphMap g) x) ∧
    0 < (unitNormal (graphMap g) x) 2 ∧
    unitNormal (graphMap g) x =
      (Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2))⁻¹ •
        WithLp.toLp 2 ![-graphPartial g x 0, -graphPartial g x 1, 1] := by
  have hinj := graph_derivative_injective g x hg
  have hd := graph_density g x hg
  have hn : unitNormal (graphMap g) x =
      (Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2))⁻¹ •
        WithLp.toLp 2 ![-graphPartial g x 0, -graphPartial g x 1, 1] := by
    change ‖areaVector (graphMap g) x‖⁻¹ • areaVector (graphMap g) x = _
    have he : ‖areaVector (graphMap g) x‖ = patchJacobian (graphMap g) x :=
      (gram_cross _).symm
    rw [he, hd, graph_cross g x hg]
  refine ⟨(normal_choices_linear _ hinj _).mpr (Or.inl rfl), ?_, hn⟩
  rw [hn]
  change 0 < _⁻¹ * (1 : ℝ)
  simp only [mul_one]
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

lemma graph_area (U D : Set (E 2)) (g : E 2 → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hD : IsCompact D)
    (hJ : Jordan D) (hDU : D ⊆ U) :
    AreaIntegrable D (graphMap g) (fun _ => 1) ∧
    parametrizedArea D (graphMap g) = regionIntegral (fun x : D =>
      Real.sqrt (1 + (graphPartial g x 0)^2 + (graphPartial g x 1)^2)) := by
  have hp := (graph_regular U g hU hg).1
  refine ⟨parametrized_area_integrable hp hD hJ hDU, ?_⟩
  rw [(parametrized_area_formula D (graphMap g)).2]
  congr 1
  funext x
  exact graph_density g x ((hg.contDiffAt (hU.mem_nhds (hDU x.property))).differentiableAt one_ne_zero)

lemma graph_flux (U D : Set (E 2)) (g : E 2 → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hD : IsCompact D)
    (hJ : Jordan D) (hDU : D ⊆ U) (F : graphMap g '' D → E 3) (hF : Continuous F) :
    FluxIntegrable D (graphMap g) F ∧
    normalFluxIntegral D (graphMap g) F (unitNormal (graphMap g)) =
      regionIntegral (fun x : D => -(F (imagePoint D (graphMap g) x) 0) * graphPartial g x 0 -
        (F (imagePoint D (graphMap g) x) 1) * graphPartial g x 1 +
        F (imagePoint D (graphMap g) x) 2) := by
  have hp := (graph_regular U g hU hg).1
  refine ⟨flux_integrable hp hD hJ hDU F hF, ?_⟩
  rw [← flux_eq_normal_integral hp hDU F]
  change regionIntegral (fluxIntegrand D (graphMap g) F) = _
  congr 1
  funext x
  change ⟪F _, areaVector (graphMap g) x⟫ = _
  rw [graph_cross g x ((hg.contDiffAt (hU.mem_nhds (hDU x.property))).differentiableAt one_ne_zero)]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

lemma paraboloid_contDiff : ContDiff ℝ 1 paraboloidHeight := by
  unfold paraboloidHeight Specs.D04.C10.GraphArea.Model.paraboloidHeight
  fun_prop

lemma paraboloid_partials (x : E 2) :
    graphPartial paraboloidHeight x 0 = 2 * x 0 ∧
    graphPartial paraboloidHeight x 1 = 2 * x 1 := by
  have hd := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := x)).pow 2).add
    (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := x)).pow 2)
  have he : fderiv ℝ paraboloidHeight x = _ := hd.fderiv
  change fderiv ℝ paraboloidHeight x = _ at he
  constructor <;>
    simp [graphPartial, Specs.D04.C10.GraphArea.Model.graphPartial, he,
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
      EuclideanSpace.basisFun_apply]

lemma paraboloid_density (x : E 2) :
    patchJacobian (graphMap paraboloidHeight) x =
      Real.sqrt (1 + 4 * ((x 0)^2 + (x 1)^2)) := by
  rw [graph_density _ _ (paraboloid_contDiff.differentiable one_ne_zero x),
    (paraboloid_partials x).1, (paraboloid_partials x).2]
  congr 1
  ring

lemma radial_continuous : Continuous (fun r : ℝ => r * Real.sqrt (1 + 4 * r^2)) := by
  fun_prop

lemma radial_primitive_deriv (r : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + 4 * t^2) ^ (3 / 2 : ℝ) / 12)
      (r * Real.sqrt (1 + 4 * r^2)) r := by
  have hd := (((hasDerivAt_id r).pow 2).const_mul 4).const_add 1
  have hh := (hd.rpow_const (p := (3 / 2 : ℝ)) (Or.inr (by norm_num))).div_const 12
  convert hh using 1
  · rfl
  dsimp only [id_eq, Pi.pow_apply] at *
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

lemma radial_evaluation (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : E 1 => x 0 * Real.sqrt (1 + 4 * (x 0)^2)) (intervalBox 0 a ha) ∧
    radialIntegral a ha = ((1 + 4 * a^2) ^ (3 / 2 : ℝ) - 1) / 12 := by
  have hi : Integrable (fun x : E 1 => x 0 * Real.sqrt (1 + 4 * (x 0)^2))
      (intervalBox 0 a ha) :=
    ExceptionalSets.integrable_continuous (by decide) _ _
      ((radial_continuous.comp (EuclideanSpace.proj (0 : Fin 1)).continuous).continuousOn)
  refine ⟨hi, ?_⟩
  obtain ⟨hs, hval⟩ := (scalar_integral _ 0 a ha).2 hi
  change lowerIntegral _ _ = _
  change lowerIntegral _ _ = _ at hval
  rw [hval]
  have hv := SingleVariableAnalysis.Riemann.real_ftc_second
    (fun t : ℝ => (1 + 4 * t^2) ^ (3 / 2 : ℝ) / 12)
    (fun t : ℝ => t * Real.sqrt (1 + 4 * t^2)) 0 a ha
    (by fun_prop) (fun x _ => radial_primitive_deriv x) hs
  change SingleVariableAnalysis.Riemann.realIntegral _ hs = _ at hv
  rw [hv]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, Real.one_rpow]
  ring

/-- Every point in the closed polar rectangle maps into the closed disk.
No local inverse is asserted on its singular faces. -/
lemma polar_mem_disk (a : ℝ) (ha : 0 ≤ a) (p : E 2)
    (hp : p ∈ carrier (polarBox a 0 ha)) : polar p ∈ disk a := by
  have hs : ‖polar p‖^2 = (p 0)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [Fin.sum_univ_two, polar, Specs.D04.C07.CoordinateCharts.Model.polar]
      using CoordinateCharts.circle_squares (p 0) (p 1)
  have h0 : 0 ≤ p 0 ∧ p 0 ≤ a := hp 0
  have hn : ‖polar p‖ = p 0 := by nlinarith [norm_nonneg (polar p)]
  simpa only [disk, Metric.mem_closedBall, dist_zero_right, hn] using h0.2

/-- Fubini on the closed polar rectangle is ordinary Riemann Fubini: all
radial slices are continuous and every angular slice has the same integral. -/
lemma polar_rectangle_radial (a : ℝ) (ha : 0 ≤ a) :
    regionIntegral (fun p : carrier (polarBox a 0 ha) =>
      (p : E 2) 0 * Real.sqrt (1 + 4 * ((p : E 2) 0)^2)) =
      2 * Real.pi * radialIntegral a ha := by
  let A := intervalBox 0 a ha
  let B := intervalBox 0 (2 * Real.pi) (by positivity)
  let f : E 2 → ℝ := fun p => p 0 * Real.sqrt (1 + 4 * (p 0)^2)
  have hf : Continuous f := radial_continuous.comp (EuclideanSpace.proj 0).continuous
  have hQ : Darboux.productBox A B = polarBox a 0 ha := by
    apply Subdivision.box_ext <;> ext i <;> fin_cases i <;>
      first | rfl | (change 2 * Real.pi = 0 + 2 * Real.pi; ring)
  have hfi : Integrable f (Darboux.productBox A B) :=
    ExceptionalSets.integrable_continuous (by decide) _ _ hf.continuousOn
  have he (y : E 1) : (fun x => f (Darboux.productPoint x y)) =
      (fun x : E 1 => x 0 * Real.sqrt (1 + 4 * (x 0)^2)) := by
    funext x
    rfl
  have hs (y : E 1) (_hy : y ∈ carrier B) :
      Integrable (fun x => f (Darboux.productPoint x y)) A := by
    rw [he y]
    exact (radial_evaluation a ha).1
  obtain ⟨houter, hv⟩ := Darboux.fubini_slices_reverse A B f hfi hs
    (fun _ => radialIntegral a ha) (by intro y hy; rfl)
  have hvalue : lowerIntegral f (polarBox a 0 ha) = 2 * Real.pi * radialIntegral a ha := by
    rw [← hQ]
    change lowerIntegral (fun _ : E 1 => radialIntegral a ha) B =
      lowerIntegral f (Darboux.productBox A B) at hv
    rw [← hv, (constant_integrals B (radialIntegral a ha)).1]
    have hc : content B = 2 * Real.pi := by
      simp [B, content, Specs.D04.C06.DarbouxIntegral.Model.content,
        Specs.D04.C06.DarbouxIntegral.Model.intervalBox]
    rw [hc, mul_comm]
  have hreg : RegionIntegrable (fun p : carrier (polarBox a 0 ha) => f p) :=
    region_integrable_of_continuous (DiscontinuityCriterion.carrier_compact _)
      (ImproperExhaustions.jordan_box _) _ (hf.comp continuous_subtype_val)
  have hbridge := CoordinateSeamsVolumes.rectangle_integral_bridge (by decide)
    (polarBox a 0 ha) _ hreg
  have hzero : EqOn (zeroExtension (fun p : carrier (polarBox a 0 ha) => f p)) f
      (carrier (polarBox a 0 ha)) := by
    intro x hx
    exact zeroExtension_apply _ ⟨x, hx⟩
  exact hbridge.2.symm.trans ((lowerIntegral_congr hzero).trans hvalue)

lemma paraboloid_zero : Specs.D04.C10.GraphArea.paraboloid_zeroType := by
  have hp := (graph_regular univ paraboloidHeight isOpen_univ paraboloid_contDiff.contDiffOn).1
  have hz := CoordinateSeamsVolumes.zero_radius.1 (n := 2) (by decide)
  exact parametrized_area_zero_volume hp (isCompact_closedBall _ _) hz.1 (subset_univ _) hz.2.1

lemma paraboloid_polar (a : ℝ) (ha : 0 ≤ a) :
    AreaIntegrable (disk a) (graphMap paraboloidHeight) (fun _ => 1) ∧
    parametrizedArea (disk a) (graphMap paraboloidHeight) = 2 * Real.pi * radialIntegral a ha := by
  have hp := (graph_regular univ paraboloidHeight isOpen_univ paraboloid_contDiff.contDiffOn).1
  have hJ := (CoordinateSeamsVolumes.disk_area a ha).1
  have hA := parametrized_area_integrable hp (isCompact_closedBall _ _) hJ (subset_univ _)
  refine ⟨hA, ?_⟩
  rcases eq_or_lt_of_le ha with rfl | hpos
  · have hz : radialIntegral 0 ha = 0 := by
      rw [(radial_evaluation 0 ha).2]
      norm_num
    rw [hz, mul_zero]
    exact paraboloid_zero
  let f : disk a → ℝ := fun x => Real.sqrt (1 + 4 * (((x : E 2) 0)^2 + ((x : E 2) 1)^2))
  have hf : Continuous f := by fun_prop
  have hfi := region_integrable_of_continuous (isCompact_closedBall _ _) hJ f hf
  let g : carrier (polarBox a 0 ha) → ℝ := fun p =>
    (p : E 2) 0 * Real.sqrt (1 + 4 * ((p : E 2) 0)^2)
  have hg : Continuous g := radial_continuous.comp
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
  -- The shared polar formula is proved by regular compact exhaustion of
  -- the open polar rectangle (chart_box_formula), followed by zero-content
  -- face estimates. In particular, it does not assert regularity at r = 0.
  have hpolar := CoordinateSeamsVolumes.polar_formula a 0 hpos (disk a) (Subset.rfl) f hfi g
    ⟨bounded_of_continuous (DiscontinuityCriterion.carrier_compact _) g hg, ?_⟩
  swap
  · intro p _
    change g p = zeroExtension f (polar p) * (p : E 2) 0
    have hext := zeroExtension_apply f ⟨polar p, polar_mem_disk a ha p p.property⟩
    change zeroExtension f (polar p) = _ at hext
    rw [hext]
    change (p : E 2) 0 * Real.sqrt (1 + 4 * ((p : E 2) 0)^2) =
      Real.sqrt (1 + 4 * ((polar p 0)^2 + (polar p 1)^2)) * (p : E 2) 0
    change (p : E 2) 0 * Real.sqrt (1 + 4 * ((p : E 2) 0)^2) =
      Real.sqrt (1 + 4 * (((p : E 2) 0 * Real.cos ((p : E 2) 1))^2 +
        ((p : E 2) 0 * Real.sin ((p : E 2) 1))^2)) * (p : E 2) 0
    rw [CoordinateCharts.circle_squares]
    ring
  have harea : parametrizedArea (disk a) (graphMap paraboloidHeight) = regionIntegral f := by
    rw [(parametrized_area_formula _ _).2]
    congr 1
    funext x
    exact paraboloid_density x
  exact harea.trans (hpolar.2.symm.trans (polar_rectangle_radial a ha))

lemma paraboloid_area (a : ℝ) (ha : 0 ≤ a) :
    parametrizedArea (disk a) (graphMap paraboloidHeight) =
      Real.pi / 6 * ((1 + 4 * a^2) ^ (3 / 2 : ℝ) - 1) := by
  rw [(paraboloid_polar a ha).2, (radial_evaluation a ha).2]
  ring

lemma paraboloid_seam : Specs.D04.C10.GraphArea.paraboloid_seamType := by
  intro a ha
  have hz : NullCovers.ContentZero (polarSeam a ha) := by
    simpa [polarSeam, Specs.D04.C10.GraphArea.Model.polarSeam] using
      CoordinateSeamsVolumes.polar_seams a 0 ha
  have hclosed : IsClosed {p : E 2 | p 0 = 0 ∨ p 1 = 0 ∨ p 1 = 2 * Real.pi} := by
    exact ((isClosed_eq (by fun_prop) continuous_const).union
      ((isClosed_eq (by fun_prop) continuous_const).union
        (isClosed_eq (by fun_prop) continuous_const)))
  have hcompact : IsCompact (polarSeam a ha) :=
    ((DiscontinuityCriterion.carrier_compact (polarBox a 0 ha)).inter_right hclosed).image
      CoordinateCharts.polar_contDiff.continuous
  have hJ := (LinearVolume.contentZero_jordan_volume (by decide) _ hcompact.isBounded hz).1
  have hp := (graph_regular univ paraboloidHeight isOpen_univ paraboloid_contDiff.contDiffOn).1
  have harea := area_zero_content hp hcompact hJ (subset_univ _) hz (fun _ => 1)
    ⟨1, fun _ => by norm_num⟩
  exact ⟨hz, harea.1, harea.2⟩

end D04.GraphArea
