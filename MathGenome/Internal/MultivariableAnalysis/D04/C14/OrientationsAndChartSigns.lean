import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OrientationsAndChartSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C14.ChartIndependentTangentSpaces

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
namespace Orientations
open EmbeddedChart
open Specs.D04.C14.OrientationsAndChartSigns.Model


theorem basis_orientation_iff :
    Specs.D04.C14.OrientationsAndChartSigns.basis_orientation_iffType :=
  Module.Basis.orientation_eq_iff_det_pos

theorem orientation_basis : Specs.D04.C14.OrientationsAndChartSigns.orientation_basisType := by
  intro k V _ _ b hk o
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  exact ⟨b.adjustToOrientation o, b.orientation_adjustToOrientation o⟩

theorem orientation_two_classes :
    Specs.D04.C14.OrientationsAndChartSigns.orientation_two_classesType := by
  intro k V _ _ b
  exact ⟨Module.Ray.ne_neg_self _, b.orientation_eq_or_eq_neg⟩

/-- The representative of an orientation is positive on precisely its bases. -/
theorem representative_pos_iff {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (o : Orientation ℝ V (Fin k)) (b : Module.Basis (Fin k) ℝ V) :
    0 < o.someVector b ↔ b.orientation = o := by
  have h : b.orientation = o ↔ SameRay ℝ b.det o.someVector := by
    rw [← ray_eq_iff b.det_ne_zero o.someVector_ne_zero,
      Module.Ray.someVector_ray]
    rfl
  rw [h]
  conv_rhs => rw [o.someVector.eq_smul_basis_det b,
    sameRay_smul_right_iff_of_ne b.det_ne_zero
      ((o.someVector.map_basis_ne_zero_iff b).mpr o.someVector_ne_zero)]

theorem sign_eq_one_iff {a : ℝ} : Real.sign a = 1 ↔ 0 < a := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · norm_num [Real.sign_of_neg h, not_lt.mpr h.le]
  · simp
  · simp [Real.sign_of_pos h, h]

theorem sign_mul (a b : ℝ) : Real.sign (a*b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;>
    rcases lt_trichotomy b 0 with hb | rfl | hb
  all_goals first
    | simp
    | rw [Real.sign_of_neg ha, Real.sign_of_neg hb,
        Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb)]; norm_num
    | rw [Real.sign_of_neg ha, Real.sign_of_pos hb,
        Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb)]; norm_num
    | rw [Real.sign_of_pos ha, Real.sign_of_neg hb,
        Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb)]; norm_num
    | rw [Real.sign_of_pos ha, Real.sign_of_pos hb,
        Real.sign_of_pos (mul_pos ha hb)]; norm_num

/-- The actual chart differential is a bijection onto its tangent space. -/
theorem tangentChartMap_bijective {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (u : E k) (hu : u ∈ c.source) : Function.Bijective (tangentChartMap c u hu) := by
  constructor
  · intro v w h
    exact EmbeddedChart.differential_injective c hr hu (congrArg Subtype.val h)
  · intro v
    have hv := v.property
    have hv' := (tangentSpace_chart c hr hkn u hu).le hv
    obtain ⟨w, hw⟩ := hv'
    exact ⟨w, Subtype.ext hw⟩

def chartBasis {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (u : E k) (hu : u ∈ c.source) :
    Module.Basis (Fin k) ℝ (tangentSpace r k M (c.toFun u)) :=
  (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k).map (LinearEquiv.ofBijective (tangentChartMap c u hu)
    (tangentChartMap_bijective c hr hkn u hu))

theorem chart_basis_exists : Specs.D04.C14.OrientationsAndChartSigns.chart_basis_existsType := by
  intro r k n M c hr hkn u hu
  exact ⟨chartBasis c hr hkn u hu, fun _ => rfl⟩

theorem chartCoefficient_ne_zero {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) (u : E k) (hu : u ∈ c.source) :
    chartCoefficient o c u hu ≠ 0 := by
  exact ((o _ _).someVector.map_basis_ne_zero_iff (chartBasis c hr hkn u hu)).mpr
    (o _ _).someVector_ne_zero

theorem chartSign_basis : Specs.D04.C14.OrientationsAndChartSigns.chartSign_basisType := by
  intro r k n M o c u hu b hb
  have he : (fun i => tangentChartMap c u hu (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i)) = b := by
    funext i
    exact Subtype.ext (hb i).symm
  change Real.sign ((o _ _).someVector _) = 1 ↔ _
  rw [he, sign_eq_one_iff, representative_pos_iff]

theorem chartSign_values : Specs.D04.C14.OrientationsAndChartSigns.chartSign_valuesType := by
  intro r k n M o c hr hkn u hu
  exact (Real.sign_apply_eq_of_ne_zero _ (chartCoefficient_ne_zero o c hr hkn u hu)).symm

/-- Evaluation of a pulled-back top covector is multiplied by the determinant. -/
theorem alternating_comp {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V [⋀^Fin k]→ₗ[ℝ] ℝ) (G : E k →ₗ[ℝ] V) (A : E k →ₗ[ℝ] E k) :
    f (fun i => G (A (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i))) =
      f (fun i => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i)) * LinearMap.det A := by
  let q := f.compLinearMap G
  change q (A ∘ Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k) = q (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k) * LinearMap.det A
  conv_lhs => rw [q.eq_smul_basis_det (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k)]
  simp only [smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one]

/-- Equality at a common ambient point identifies the two tangent modules. -/
theorem coefficient_change_at {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) {x y : E n} (hx : x ∈ M) (hy : y ∈ M)
    (F : E k →ₗ[ℝ] tangentSpace r k M x) (G : E k →ₗ[ℝ] tangentSpace r k M y)
    (hxy : x = y) (A : E k →ₗ[ℝ] E k)
    (h : ∀ w, (F w).val = (G (A w)).val) :
    (o x hx).someVector (fun i => F (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i)) =
      (o y hy).someVector (fun i => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i)) * LinearMap.det A := by
  subst y
  have he : F = G.comp A := by
    apply LinearMap.ext
    intro w
    exact Subtype.ext (h w)
  rw [he]
  exact alternating_comp (o x hx).someVector G A

/-- Change of parameter for the evaluation coefficient at the same tangent point. -/
theorem chartCoefficient_change {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c d : EmbeddedChart r k n M)
    (u v : E k) (hu : u ∈ c.source) (hv : v ∈ d.source)
    (hx : d.toFun v = c.toFun u) (A : E k →ₗ[ℝ] E k)
    (hA : (chartDifferential c u).toLinearMap =
      (chartDifferential d v).toLinearMap.comp A) :
    chartCoefficient o c u hu = chartCoefficient o d v hv * LinearMap.det A :=
  coefficient_change_at o _ _ (tangentChartMap c u hu) (tangentChartMap d v hv)
    hx.symm A (fun w => DFunLike.congr_fun hA w)

theorem chartSign_transition :
    Specs.D04.C14.OrientationsAndChartSigns.chartSign_transitionType := by
  intro r k n M o c d hr hkn u hu hv
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn u hu
  have hd : chartDifferential c u =
      (chartDifferential d (chartTransition c d u)).comp A.toContinuousLinearMap := by
    apply (D04.EmbeddedChart.overlap_uniqueDiff c d u hu).eq (f := c.toFun)
      ((D04.EmbeddedChart.hasDifferential c hr hu.1).mono inter_subset_left)
    exact ((D04.EmbeddedChart.hasDifferential d hr hv).comp u hA
      (fun v hv => (D04.EmbeddedChart.transition_mem c d hv).1)).congr'
      (fun v hv => (d.right_inv _ ⟨(c.map_source hv.1).1, hv.2⟩).symm) hu
  have he := chartCoefficient_change o c d u (chartTransition c d u) hu.1 hv
    (d.right_inv _ ⟨(c.map_source hu.1).1, hu.2⟩) A.toLinearEquiv.toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap hd)
  change Real.sign (chartCoefficient o c u hu.1) =
    Real.sign (chartCoefficient o d (chartTransition c d u) hv) * Real.sign _
  rw [he, sign_mul, hA.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff c d u hu)]
  rfl

theorem chartSign_reparametrize :
    Specs.D04.C14.OrientationsAndChartSigns.chartSign_reparametrizeType := by
  intro r k n M o c d hr h hm he u hu A hA
  have hd : chartDifferential c u = (chartDifferential d (h u)).comp A := by
    apply (D04.EmbeddedChart.source_uniqueDiff c u hu).eq
      (D04.EmbeddedChart.hasDifferential c hr hu)
    exact ((D04.EmbeddedChart.hasDifferential d hr (hm hu)).comp u hA hm).congr'
      (fun v hv => he hv) hu
  have hc := chartCoefficient_change o c d u (h u) hu (hm hu) (he hu).symm A.toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap hd)
  change Real.sign (chartCoefficient o c u hu) = Real.sign (chartCoefficient o d (h u) (hm hu)) * _
  rw [hc, sign_mul]

theorem reflection_basis (k : ℕ) (i j : Fin k) :
    coordinateReflection k i (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k j) =
      (Function.update (1 : Fin k → ℝˣ) i (-1) j) •
        Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k j := by
  change ((Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k).equiv _ _)
    (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k j) = _
  rw [Module.Basis.equiv_apply]
  exact Module.Basis.unitsSMul_apply j

theorem reflection_coordinate (k : ℕ) (i : Fin k) (u : E k) (j : Fin k) :
    coordinateReflection k i u j = if j = i then -u j else u j := by
  have he : ((EuclideanSpace.proj j).comp (coordinateReflection k i).toContinuousLinearMap).toLinearMap =
      (if j = i then -EuclideanSpace.proj j else EuclideanSpace.proj j).toLinearMap := by
    apply (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k).ext
    intro a
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, reflection_basis]
    by_cases hj : j = i <;> by_cases ha : a = i
    all_goals simp [hj, ha,
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
  have hh := DFunLike.congr_fun he u
  by_cases hj : j = i <;> simpa [hj] using hh

theorem reflection_properties : Specs.D04.C14.OrientationsAndChartSigns.reflection_propertiesType := by
  intro k i
  refine ⟨?_, ?_, reflection_coordinate k i⟩
  · change LinearMap.det ((Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k).equiv
      ((Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k).unitsSMul
        (Function.update 1 i (-1))) (Equiv.refl _)).toLinearMap = -1
    rw [Module.Basis.det_basis, Module.Basis.det_unitsSMul_self]
    have he : (fun j => ((Function.update (1 : Fin k → ℝˣ) i (-1) j) : ℝ)) =
        Function.update (1 : Fin k → ℝ) i (-1) := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  · intro u
    ext j
    simp only [reflection_coordinate]
    split_ifs <;> simp

/-- Reparametrizing an open chart by any linear coordinate isomorphism. -/
def precomposeOpenChart {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    (hc : c.half = false) (e : E k ≃L[ℝ] E k) : EmbeddedChart r k n M where
  half := false
  half_pos := by simp
  source := e ⁻¹' c.source
  source_open := by
    obtain ⟨W, hW, he⟩ := c.source_open
    have hcs : c.source = W := by simpa [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hc] using he
    refine ⟨e ⁻¹' W, hW.preimage e.continuous, ?_⟩
    simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace, hcs]
  ambient := c.ambient
  ambient_open := c.ambient_open
  toFun := c.toFun ∘ e
  invFun := e.symm ∘ c.invFun
  map_source := fun _ hu => c.map_source hu
  map_target := by
    intro x hx
    change e (e.symm (c.invFun x)) ∈ c.source
    simpa using c.map_target hx
  left_inv := by
    intro u hu
    change e.symm (c.invFun (c.toFun (e u))) = u
    rw [c.left_inv _ hu, e.symm_apply_apply]
  right_inv := by
    intro x hx
    change c.toFun (e (e.symm (c.invFun x))) = x
    rw [e.apply_symm_apply, c.right_inv _ hx]
  continuous_toFun := c.continuous_toFun.comp e.continuous.continuousOn (fun _ hu => hu)
  continuous_invFun := e.symm.continuous.continuousOn.comp c.continuous_invFun
    (fun _ _ => mem_univ _)
  regular := by
    intro u hu
    obtain ⟨W, g, hW, huW, he, hg, hinj⟩ := c.regular (e u) hu
    refine ⟨e ⁻¹' W, g ∘ e, hW.preimage e.continuous, huW, ?_, ?_, ?_⟩
    · intro w hw
      exact he ⟨hw.1, hw.2⟩
    · exact hg.comp e.contDiff.contDiffOn (fun _ hw => hw)
    · intro w hw
      have hdg := (hg.contDiffAt (hW.mem_nhds hw)).differentiableAt
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
      rw [(hdg.hasFDerivAt.comp w e.hasFDerivAt).fderiv]
      exact (hinj (e w) hw).comp e.injective

theorem precomposeOpenChart_differential {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    (hc : c.half = false) (e : E k ≃L[ℝ] E k) (u : E k)
    (hu : u ∈ (precomposeOpenChart c hr hc e).source) :
    chartDifferential (precomposeOpenChart c hr hc e) u =
      (chartDifferential c (e u)).comp e.toContinuousLinearMap := by
  apply (D04.EmbeddedChart.source_uniqueDiff (precomposeOpenChart c hr hc e) u hu).eq
    (D04.EmbeddedChart.hasDifferential (precomposeOpenChart c hr hc e) hr hu)
  exact (D04.EmbeddedChart.hasDifferential c hr hu).comp u e.hasFDerivAt.hasFDerivWithinAt
    (fun _ hw => hw)

theorem precomposeOpenChart_sign {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hc : c.half = false) (e : E k ≃L[ℝ] E k)
    (u : E k) (hu : u ∈ (precomposeOpenChart c hr hc e).source) :
    chartSign o (precomposeOpenChart c hr hc e) u hu =
      chartSign o c (e u) hu * Real.sign (LinearMap.det e.toLinearMap) := by
  have he := chartCoefficient_change o (precomposeOpenChart c hr hc e) c u (e u) hu hu rfl
    e.toLinearMap (congrArg ContinuousLinearMap.toLinearMap
      (precomposeOpenChart_differential c hr hc e u hu))
  change Real.sign (chartCoefficient o _ u hu) = Real.sign (chartCoefficient o c (e u) hu) * _
  rw [he, sign_mul]

/-- A restriction preserves the ordered differential columns and their sign. -/
theorem restriction_sign {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hs : d.source ⊆ c.source) (hf : d.toFun = c.toFun)
    (u : E k) (hu : u ∈ d.source) :
    chartSign o d u hu = chartSign o c u (hs hu) := by
  have hd : chartDifferential d u = chartDifferential c u := by
    apply (D04.EmbeddedChart.source_uniqueDiff d u hu).eq
      (D04.EmbeddedChart.hasDifferential d hr hu)
    rw [hf]
    exact (D04.EmbeddedChart.hasDifferential c hr (hs hu)).mono hs
  have he := chartCoefficient_change o d c u u hu (hs hu) (congrFun hf u).symm
    (LinearMap.id) (by simpa using congrArg ContinuousLinearMap.toLinearMap hd)
  change Real.sign (chartCoefficient o d u hu) = Real.sign (chartCoefficient o c u (hs hu))
  simpa only [LinearMap.det_id, mul_one] using congrArg Real.sign he

/-- A relatively open chart may be restricted inside its Euclidean interior
and then recorded as an open chart of the same manifold. -/
theorem open_chart_restriction {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (W : Set (E k)) (hW : IsOpen W) (hWs : W ⊆ c.source) :
    ∃ d : EmbeddedChart r k n M,
      d.half = false ∧ d.source = W ∧ d.toFun = c.toFun := by
  obtain ⟨d, hs, _, hf, _, _⟩ := embeddedChart_restrict_parameter c W hW
  have he : d.source = W := hs.trans (inter_eq_right.mpr hWs)
  let e : EmbeddedChart r k n M := {d with
    half := false
    half_pos := by simp
    source_open := ⟨W, hW, by simpa [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace] using he⟩}
  exact ⟨e, rfl, he, hf⟩

/-- Local constancy supplies a small open parameter neighborhood on which the
original chart sign is constant. -/
theorem constant_sign_neighborhood {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source) (hi : ¬ IsBoundaryParameter c u) :
    ∃ (W : Set (E k)) (hWs : W ⊆ c.source), IsOpen W ∧ u ∈ W ∧
      ∀ w (hw : w ∈ W), chartSign o.atPoint c w (hWs hw) =
        chartSign o.atPoint c u hu := by
  obtain ⟨U, hU, huU, hconst⟩ := (o.locally_constant c).exists_open ⟨u, hu⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨V, hVs, hV, huV⟩ := mem_nhds_iff.mp
    (D04.EmbeddedChart.source_mem_nhds c hu hi)
  have huT : u ∈ T := by
    have : (⟨u, hu⟩ : c.source) ∈ Subtype.val ⁻¹' T := hTU ▸ huU
    exact this
  refine ⟨V ∩ T, fun w hw => hVs hw.1, hV.inter hT, ⟨huV, huT⟩, ?_⟩
  intro w hw
  exact hconst ⟨w, hVs hw.1⟩ (hTU ▸ hw.2)


theorem positive_interior_chart :
    Specs.D04.C14.OrientationsAndChartSigns.positive_interior_chartType := by
  intro r k n M o c u hu hi
  obtain ⟨W, hWs, hW, huW, hconst⟩ := constant_sign_neighborhood o c u hu hi
  obtain ⟨d, hdhalf, hds, hdf⟩ := open_chart_restriction c W hW hWs
  have hud : u ∈ d.source := hds ▸ huW
  have hdsign : ∀ w (hw : w ∈ d.source), chartSign o.atPoint d w hw = chartSign o.atPoint c u hu := by
    intro w hw
    rw [restriction_sign o.atPoint c d o.manifold.1 (hds ▸ hWs) hdf w hw]
    exact hconst w (hds ▸ hw)
  rcases chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 u hu with hp | hn
  · exact ⟨d, u, hdhalf, hud, congrFun hdf u, fun w hw => (hdsign w hw).trans hp⟩
  · change chartSign o.atPoint c u hu = -1 at hn
    let i : Fin k := ⟨0, o.positive_dimension⟩
    let R := coordinateReflection k i
    let e := precomposeOpenChart d o.manifold.1 hdhalf R
    have hinv : ∀ w, R (R w) = w := (reflection_properties k i).2.1
    have hve : R u ∈ e.source := by
      change R (R u) ∈ d.source
      rwa [hinv]
    refine ⟨e, R u, rfl, hve, ?_, ?_⟩
    · change d.toFun (R (R u)) = c.toFun u
      rw [hinv, hdf]
    · intro w hw
      change chartSign o.atPoint (precomposeOpenChart d o.manifold.1 hdhalf R) w hw = 1
      rw [precomposeOpenChart_sign o.atPoint d o.manifold.1 hdhalf R w hw,
        hdsign (R w) hw, hn]
      have hdet := (reflection_properties k i).1
      change LinearMap.det R.toLinearMap = -1 at hdet
      rw [hdet, Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
      norm_num

theorem one_dimensional_halfspace_reflection :
    Specs.D04.C14.OrientationsAndChartSigns.one_dimensional_halfspace_reflectionType := by
  have he : ∀ u : E 1, coordinateReflection 1 0 u 0 = -u 0 := by
    intro u
    simp [reflection_coordinate]
  constructor
  · ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      change coordinateReflection 1 0 v 0 ≤ 0
      rw [he]
      exact neg_nonpos.mpr hv
    · intro hu
      refine ⟨coordinateReflection 1 0 u, ?_, (reflection_properties 1 0).2.1 u⟩
      change 0 ≤ coordinateReflection 1 0 u 0
      rw [he]
      exact neg_nonneg.mpr hu
  · intro h
    have hv : Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1 0 ∈ halfSpace 1 := by
      change 0 ≤ Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1 0 (Fin.last 0)
      norm_num [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
        PiLp.single_apply]
    have hh := h hv
    change 0 ≤ coordinateReflection 1 0 (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1 0) 0 at hh
    rw [he] at hh
    norm_num [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      PiLp.single_apply] at hh


theorem chartSign_reverse : Specs.D04.C14.OrientationsAndChartSigns.chartSign_reverseType := by
  intro r k n M o c hr hkn u hu
  let b := chartBasis c hr hkn u hu
  have hb : ∀ i, (b i).val = chartDifferential c u
      (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis k i) := fun _ => rfl
  have hpos := chartSign_basis o c u hu b hb
  have hneg := chartSign_basis (fun x hx => -o x hx) c u hu b hb
  rcases chartSign_values o c hr hkn u hu with hs | hs
  · change chartSign o c u hu = 1 at hs
    have ho := hpos.mp hs
    have hne : chartSign (fun x hx => -o x hx) c u hu ≠ 1 := by
      intro h
      have hh := hneg.mp h
      rw [← ho] at hh
      exact Module.Ray.ne_neg_self _ hh
    have hh := (chartSign_values (fun x hx => -o x hx) c hr hkn u hu).resolve_left hne
    change chartSign (fun x hx => -o x hx) c u hu = -chartSign o c u hu
    rw [hs]
    exact hh
  · change chartSign o c u hu = -1 at hs
    have ho : o (c.toFun u) (c.map_source hu).1 = -b.orientation := by
      apply (b.orientation_ne_iff_eq_neg _).mp
      intro h
      have he := hpos.mpr h.symm
      rw [hs] at he
      norm_num at he
    have hh : chartSign (fun x hx => -o x hx) c u hu = 1 := by
      apply hneg.mpr
      rw [ho]
      exact (neg_neg b.orientation).symm
    change chartSign (fun x hx => -o x hx) c u hu = -chartSign o c u hu
    rw [hh, hs]
    norm_num

theorem line_det (A : E 1 →ₗ[ℝ] E 1) :
    LinearMap.det A = A (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1 0) 0 := by
  rw [← LinearMap.det_toMatrix (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1),
    Matrix.det_fin_one, LinearMap.toMatrix_apply]
  rfl

theorem boundary_line_transition_positive :
    Specs.D04.C14.OrientationsAndChartSigns.boundary_line_transition_positiveType := by
  intro r n M c d hr hkn u hu hb
  classical
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn u hu
  have hb' := (chart_transition_boundary c d hr hkn u hu).mp hb
  have hcone := (chart_transition_cones c d hr hkn u hu A hA).1
  change A '' (if IsBoundaryParameter c u then halfSpace 1 else univ) =
    (if IsBoundaryParameter d (chartTransition c d u) then halfSpace 1 else univ) at hcone
  rw [ite_eq_left hb, ite_eq_left hb'] at hcone
  let e := Specs.D04.C01.EuclideanInterfaces.Model.standardBasis 1 0
  have he : e ∈ halfSpace 1 := by
    change 0 ≤ e 0
    norm_num [e, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hAe : 0 ≤ A e 0 := by
    have hh : A e ∈ A '' halfSpace 1 := ⟨e, he, rfl⟩
    rw [hcone] at hh
    exact hh
  rw [hA.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff c d u hu)]
  have hn := A.toLinearEquiv.isUnit_det'.ne_zero
  apply lt_of_le_of_ne ?_ (Ne.symm hn)
  rw [line_det]
  exact hAe

/-- Reversing an orientation preserves the required local constancy. -/
def reverseOrientation {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) : PositiveManifoldOrientation r k M where
  positive_dimension := o.positive_dimension
  manifold := o.manifold
  atPoint x hx := -o.atPoint x hx
  locally_constant := by
    intro c
    have he : (fun u : c.source =>
        Specs.D04.C14.OrientationsAndChartSigns.Model.chartSign (fun x hx => -o.atPoint x hx) c u u.property) =
        (fun u : c.source => -chartSign o.atPoint c u u.property) := by
      funext u
      exact chartSign_reverse o.atPoint c o.manifold.1 o.manifold.2.1 u u.property
    rw [he]
    exact (o.locally_constant c).comp (fun s : ℝ => -s)

theorem boundary_line_sign_same {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r 1 M) (c d : EmbeddedChart r 1 n M)
    (u v : E 1) (hu : u ∈ c.source) (hv : v ∈ d.source)
    (hb : IsBoundaryParameter c u) (hx : d.toFun v = c.toFun u) :
    chartSign o.atPoint d v hv = chartSign o.atPoint c u hu := by
  have hcd : u ∈ chartOverlap c d := ⟨hu, by
    change c.toFun u ∈ d.ambient
    rw [← hx]
    exact (d.map_source hv).2⟩
  have ht : chartTransition c d u = v := by
    change d.invFun (c.toFun u) = v
    rw [← hx, d.left_inv v hv]
  have hpos := boundary_line_transition_positive c d o.manifold.1 o.manifold.2.1 u hcd hb
  have hs := chartSign_transition o.atPoint c d o.manifold.1 o.manifold.2.1 u hcd
    (D04.EmbeddedChart.transition_mem c d hcd).1
  change chartSign o.atPoint c u hu = chartSign o.atPoint d (chartTransition c d u) _ * _ at hs
  rw [Real.sign_of_pos hpos, mul_one] at hs
  simpa only [ht] using hs.symm

theorem negative_boundary_chart :
    Specs.D04.C14.OrientationsAndChartSigns.negative_boundary_chartType := by
  intro r n M o c u hu hb
  have hvalues := chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 u hu
  have hex : ∃ p : PositiveManifoldOrientation r 1 M,
      (p.atPoint = o.atPoint ∨ p.atPoint = fun x hx => -o.atPoint x hx) ∧
      chartSign p.atPoint c u hu = -1 := by
    rcases hvalues with hp | hn
    · refine ⟨reverseOrientation o, Or.inr rfl, ?_⟩
      change chartSign (fun x hx => -o.atPoint x hx) c u hu = -1
      rw [chartSign_reverse o.atPoint c o.manifold.1 o.manifold.2.1 u hu]
      change chartSign o.atPoint c u hu = 1 at hp
      rw [hp]
    · exact ⟨o, Or.inl rfl, hn⟩
  obtain ⟨p, hp, hs⟩ := hex
  refine ⟨p, hp, hs, ?_⟩
  intro d v hv hx
  exact (boundary_line_sign_same p c d u v hu hv hb hx).trans hs


theorem zero_orientation_arbitrary :
    Specs.D04.C14.OrientationsAndChartSigns.zero_orientation_arbitraryType := by
  intro n M s hs
  exact ⟨fun x => ⟨s x, hs x⟩, fun _ => rfl⟩

abbrev SpaceOrientation := Specs.D04.C14.OrientationsAndChartSigns.Model.SpaceOrientation
abbrev TangentOrientationField := @Specs.D04.C14.OrientationsAndChartSigns.Model.TangentOrientationField
abbrev chartCoefficient := @Specs.D04.C14.OrientationsAndChartSigns.Model.chartCoefficient
abbrev chartSign := @Specs.D04.C14.OrientationsAndChartSigns.Model.chartSign
abbrev PositiveManifoldOrientation := @Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation
abbrev ZeroManifoldOrientation := @Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation
abbrev ManifoldOrientation := @Specs.D04.C14.OrientationsAndChartSigns.Model.ManifoldOrientation
abbrev coordinateReflection := Specs.D04.C14.OrientationsAndChartSigns.Model.coordinateReflection

end Orientations
end D04
