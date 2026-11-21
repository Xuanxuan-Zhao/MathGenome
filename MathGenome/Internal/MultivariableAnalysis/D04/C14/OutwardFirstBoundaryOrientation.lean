import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OrientationsAndChartSigns
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Alternating.Curry

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04BoundaryOrientation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model

theorem gram_invertible {k n : ℕ} (A : E k →L[ℝ] E n)
    (hA : Function.Injective A) : (A.adjoint.comp A).IsInvertible := by
  have hi := A.adjoint_comp_self_injective_iff.mpr hA
  exact ⟨(LinearEquiv.ofBijective (A.adjoint.comp A).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv, rfl⟩

theorem dualNormal_inner {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) (w : E (d+1)) :
    inner ℝ (dualNormal A) (A w) = w (Fin.last d) := by
  unfold dualNormal
  rw [← A.adjoint_inner_left]
  change inner ℝ ((A.adjoint.comp A) ((A.adjoint.comp A).inverse _)) w = _
  rw [(gram_invertible A hA).self_apply_inverse]
  simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem dualNormal_ne_zero {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) : dualNormal A ≠ 0 := by
  intro h
  have hh := dualNormal_inner A hA (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d))
  rw [h, inner_zero_left] at hh
  norm_num [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply] at hh

theorem normal_inner {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) (w : E (d+1)) :
    inner ℝ (normalOfDifferential A) (A w) = -‖dualNormal A‖⁻¹ * w (Fin.last d) := by
  rw [normalOfDifferential, real_inner_smul_left, dualNormal_inner A hA]

theorem normal_norm {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) : ‖normalOfDifferential A‖ = 1 := by
  rw [normalOfDifferential, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (dualNormal_ne_zero A hA))]

theorem normal_parameter {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) :
    ∃ w : E (d+1), A w = normalOfDifferential A ∧ w (Fin.last d) < 0 := by
  let z := (A.adjoint.comp A).inverse (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d))
  have hz : z (Fin.last d) = ‖dualNormal A‖ ^ 2 := by
    simpa only [dualNormal, z, real_inner_self_eq_norm_sq] using
      (dualNormal_inner A hA z).symm
  refine ⟨-‖dualNormal A‖⁻¹ • z, by simp [normalOfDifferential, dualNormal, z], ?_⟩
  change -‖dualNormal A‖⁻¹ * z (Fin.last d) < 0
  rw [hz]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr (norm_pos_iff.mpr
    (dualNormal_ne_zero A hA)))) (sq_pos_of_pos (norm_pos_iff.mpr (dualNormal_ne_zero A hA)))

/-- A unit vector perpendicular to the flat image is determined by its outward side. -/
theorem normal_unique {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) (v : E n) (hv : ‖v‖ = 1)
    (ho : ∀ w : E (d+1), w (Fin.last d) = 0 → inner ℝ v (A w) = 0)
    (z : E (d+1)) (hz : A z = v) (hzneg : z (Fin.last d) < 0) :
    v = normalOfDifferential A := by
  let t := inner ℝ v (A (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d)))
  have hfun : ∀ w : E (d+1), inner ℝ v (A w) = t * w (Fin.last d) := by
    intro w
    have hf : (w - w (Fin.last d) • Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d)) (Fin.last d) = 0 := by
      simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]
    have hh := ho _ hf
    simp only [map_sub, map_smul, inner_sub_right, real_inner_smul_right] at hh
    dsimp [t]
    linarith
  have he : v = t • dualNormal A := by
    have hh : ∀ w : E (d+1), inner ℝ (v - t • dualNormal A) (A w) = 0 := by
      intro w
      rw [inner_sub_left, real_inner_smul_left, hfun, dualNormal_inner A hA]
      ring
    let p := (A.adjoint.comp A).inverse (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d))
    have hdiff : A (z - t • p) = v - t • dualNormal A := by
      simp [p, hz, dualNormal]
    have heq := hh (z - t • p)
    rw [hdiff, real_inner_self_eq_norm_sq] at heq
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp heq))
  have ht : t < 0 := by
    have hh := hfun z
    rw [hz, real_inner_self_eq_norm_sq, hv] at hh
    have : 0 < t * z (Fin.last d) := by linarith
    exact neg_of_mul_pos_left this hzneg.le
  have htval : t = -‖dualNormal A‖⁻¹ := by
    have hh : -t * ‖dualNormal A‖ = 1 := by
      have := congrArg norm he
      simpa [norm_smul, Real.norm_eq_abs, abs_of_neg ht, hv] using this.symm
    have hn := norm_ne_zero_iff.mpr (dualNormal_ne_zero A hA)
    apply (eq_neg_iff_add_eq_zero).mpr
    field_simp
    linarith
  rw [he, htval]
  rfl

theorem boundary_velocity_change {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M)
    (c e : EmbeddedChart r (d+1) n M) (u v : E (d+1))
    (hu : u ∈ c.source) (hv : v ∈ e.source)
    (hbu : IsBoundaryParameter c u) (hbv : IsBoundaryParameter e v)
    (hx : e.toFun v = c.toFun u) (z : E (d+1)) :
    ∃ w, chartDifferential c u w = chartDifferential e v z ∧
      (w (Fin.last d) < 0 ↔ z (Fin.last d) < 0) := by
  classical
  have hev : v ∈ chartOverlap e c := ⟨hv, by
    change e.toFun v ∈ c.ambient
    rw [hx]
    exact (c.map_source hu).2⟩
  have ht : chartTransition e c v = u := by
    change c.invFun (e.toFun v) = u
    rw [hx, c.left_inv _ hu]
  obtain ⟨A, hA, _⟩ := D04.chart_transition_derivatives e c hM.1 hM.2.1 v hev
  have hd : chartDifferential e v =
      (chartDifferential c (chartTransition e c v)).comp A.toContinuousLinearMap := by
    apply (D04.EmbeddedChart.overlap_uniqueDiff e c v hev).eq
      ((D04.EmbeddedChart.hasDifferential e hM.1 hv).mono inter_subset_left)
    exact ((D04.EmbeddedChart.hasDifferential c hM.1
      (D04.EmbeddedChart.transition_mem e c hev).1).comp v hA
      (fun w hw => (D04.EmbeddedChart.transition_mem e c hw).1)).congr'
      (fun w hw => (c.right_inv _ ⟨(e.map_source hw.1).1, hw.2⟩).symm) hev
  have hcone := (D04.chart_transition_cones e c hM.1 hM.2.1 v hev A hA).1
  change A '' (if IsBoundaryParameter e v then halfSpace (d+1) else univ) =
    (if IsBoundaryParameter c (chartTransition e c v) then halfSpace (d+1) else univ) at hcone
  rw [ht, ite_eq_left hbv, ite_eq_left hbu] at hcone
  have hm : A z ∈ halfSpace (d+1) ↔ z ∈ halfSpace (d+1) := by
    constructor
    · intro h
      rw [← hcone] at h
      obtain ⟨w, hw, he⟩ := h
      rwa [A.injective he] at hw
    · intro h
      rw [← hcone]
      exact ⟨z, h, rfl⟩
  refine ⟨A z, ?_, ?_⟩
  · simpa only [ht, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      using (DFunLike.congr_fun hd z).symm
  · change (0 ≤ A z (Fin.last d) ↔ 0 ≤ z (Fin.last d)) at hm
    simpa only [not_le] using not_congr hm

theorem outward_chart_independent :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.outward_chart_independentType := by
  intro r d n M hM c u hu hb w
  constructor
  · rintro ⟨e, v, z, hv, hbv, hx, hz, hzn⟩
    obtain ⟨a, ha, hn⟩ := boundary_velocity_change hM c e u v hu hv hb hbv hx z
    have haw : a = w := D04.EmbeddedChart.differential_injective c hM.1 hu (ha.trans hz)
    exact haw ▸ hn.mpr hzn
  · intro hw
    exact ⟨c, u, w, hu, hb, rfl, rfl, hw⟩

theorem conormal_chart_formula :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.conormal_chart_formulaType := by
  intro r d n M hM c u hu hb
  have hi := D04.EmbeddedChart.differential_injective c hM.1 hu
  obtain ⟨w, hw, hwn⟩ := normal_parameter (chartDifferential c u) hi
  refine ⟨?_, normal_norm _ hi, ?_, c, u, w, hu, hb, rfl, hw, hwn⟩
  · rw [D04.tangentSpace_chart c hM.1 hM.2.1 u hu]
    exact ⟨w, hw⟩
  · intro v hv
    have he := D04.tangentSpace_intrinsic_boundary c hM.1 hM.2.1 hb.1 u hu hb.2
    change v ∈ (tangentSpace r d (intrinsicBoundary r (d+1) M) (c.toFun u) : Set (E n)) at hv
    rw [he] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [normal_inner _ hi, show z (Fin.last d) = 0 from hz, mul_zero]

theorem conormal_exists_unique :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.conormal_exists_uniqueType := by
  intro r d n M hM x hx
  obtain ⟨hxM, c, u, hc, hu, hflat, hux⟩ := hx
  subst x
  refine ⟨normalOfDifferential (chartDifferential c u),
    conormal_chart_formula hM c u hu ⟨hc, hflat⟩, ?_⟩
  intro v hv
  obtain ⟨e, a, z, ha, hb, he, hz, hzn⟩ := hv.2.2.2
  obtain ⟨w, hw, hwn⟩ := boundary_velocity_change hM c e u a hu ha
    ⟨hc, hflat⟩ hb he z
  apply normal_unique (chartDifferential c u)
    (D04.EmbeddedChart.differential_injective c hM.1 hu) v hv.2.1
  · intro z hz
    apply hv.2.2.1
    change chartDifferential c u z ∈ (tangentSpace r d (intrinsicBoundary r (d+1) M) (c.toFun u) : Set (E n))
    rw [D04.tangentSpace_intrinsic_boundary c hM.1 hM.2.1 hc u hu hflat]
    exact ⟨z, hz, rfl⟩
  · exact hw.trans hz
  · exact hwn.mpr hzn

theorem normal_continuousAt {d n : ℕ} (A : E (d+1) →L[ℝ] E n)
    (hA : Function.Injective A) : ContinuousAt (@normalOfDifferential d n) A := by
  have hG : Continuous (fun B : E (d+1) →L[ℝ] E n => B.adjoint.comp B) :=
    Continuous.clm_comp (ContinuousLinearMap.adjoint.continuous) continuous_id
  have hunit : IsUnit (A.adjoint.comp A) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr (gram_invertible A hA).bijective
  obtain ⟨g, hg⟩ := hunit
  have hinv : ContinuousAt (fun B : E (d+1) →L[ℝ] E n => (B.adjoint.comp B).inverse) A := by
    rw [← ContinuousLinearMap.ringInverse_eq_inverse]
    have hinvG : ContinuousAt Ring.inverse (A.adjoint.comp A) := by
      rw [← hg]
      exact NormedRing.inverse_continuousAt g
    exact hinvG.comp (f := fun B : E (d+1) →L[ℝ] E n => B.adjoint.comp B) hG.continuousAt
  have hq : ContinuousAt (@dualNormal d n) A := by
    exact continuousAt_id.clm_apply (hinv.clm_apply continuousAt_const)
  exact (hq.norm.inv₀ (norm_ne_zero_iff.mpr (dualNormal_ne_zero A hA))).neg.smul hq

theorem chart_differential_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) :
    ContinuousOn (chartDifferential c) c.source := by
  have hreg : ContDiffOn ℝ r c.toFun c.source := by
    intro u hu
    obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
    apply (hg.contDiffAt (hW.mem_nhds huW)).contDiffWithinAt.congr_of_eventuallyEq
    · exact eventuallyEq_of_mem
        (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) he.symm
    · exact (he ⟨hu, huW⟩).symm
  exact hreg.continuousOn_fderivWithin (D04.EmbeddedChart.source_uniqueDiff c) hr.1

def outwardConormal {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M) : E n :=
  Classical.choose (conormal_exists_unique hM x x.property).exists

theorem outwardConormal_spec {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M) :
    IsOutwardUnitConormal r d M x (outwardConormal hM x) :=
  Classical.choose_spec (conormal_exists_unique hM x x.property).exists

theorem outwardConormal_chart {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (c : EmbeddedChart r (d+1) n M)
    (x : intrinsicBoundary r (d+1) M) (hx : (x : E n) ∈ c.ambient) :
    outwardConormal hM x = normalOfDifferential (chartDifferential c (c.invFun x)) := by
  have hm : (x : E n) ∈ M ∩ c.ambient := ⟨x.property.1, hx⟩
  have hu := c.map_target hm
  have hb : IsBoundaryParameter c (c.invFun x) := by
    apply (D04.chart_intrinsicBoundary c hM.1 hM.2.1 _ hu).mp
    rw [c.right_inv _ hm]
    exact x.property
  have hn := conormal_chart_formula hM c _ hu hb
  rw [c.right_inv _ hm] at hn
  exact (conormal_exists_unique hM x x.property).unique (outwardConormal_spec hM x) hn

theorem outwardConormal_continuous {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) : Continuous (outwardConormal hM) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨_, c, u, _, hu, _, hux⟩ := x.property
  have hx : (x : E n) ∈ c.ambient := by rw [← hux]; exact (c.map_source hu).2
  let U : Set (intrinsicBoundary r (d+1) M) := Subtype.val ⁻¹' c.ambient
  have hU : U ∈ 𝓝 x := (c.ambient_open.preimage continuous_subtype_val).mem_nhds hx
  have hc : ContinuousAt (fun y : intrinsicBoundary r (d+1) M =>
      normalOfDifferential (chartDifferential c (c.invFun y))) x := by
    have hi := c.continuous_invFun (x : E n) ⟨x.property.1, hx⟩
    have hi' : ContinuousAt (fun y : intrinsicBoundary r (d+1) M => c.invFun y) x := by
      apply (hi.comp (continuous_subtype_val.continuousAt.continuousWithinAt (s := U))
        (fun y hy => ⟨y.property.1, hy⟩)).continuousAt
      exact hU
    have hd := (chart_differential_continuous c hM.1) (c.invFun x)
      (c.map_target ⟨x.property.1, hx⟩)
    have hd' : ContinuousAt (fun y : intrinsicBoundary r (d+1) M =>
        chartDifferential c (c.invFun y)) x := by
      apply (hd.comp (f := fun y : intrinsicBoundary r (d+1) M => c.invFun y) (hi'.continuousWithinAt (s := U)) (fun y hy =>
        c.map_target ⟨y.property.1, hy⟩)).continuousAt
      exact hU
    exact (normal_continuousAt _ (D04.EmbeddedChart.differential_injective c hM.1
      (c.map_target ⟨x.property.1, hx⟩))).comp (f := fun y : intrinsicBoundary r (d+1) M => chartDifferential c (c.invFun y)) hd'
  exact hc.congr_of_eventuallyEq
    (eventually_of_mem hU (fun y hy => outwardConormal_chart hM c y hy))

theorem continuous_conormal :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.continuous_conormalType := by
  intro r d n M hM
  refine ⟨outwardConormal hM, ⟨outwardConormal_continuous hM, outwardConormal_spec hM⟩, ?_⟩
  intro ν hν
  funext x
  exact (conormal_exists_unique hM x x.property).unique (hν.2 x) (outwardConormal_spec hM x)

theorem boundary_point_sign :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.boundary_point_signType := by
  classical
  intro r n M o ν _
  let s : ZeroManifoldOrientation (intrinsicBoundary r 1 M) :=
    fun x => if PositiveOutwardLine o x (ν x) then ⟨1, Or.inl rfl⟩ else ⟨-1, Or.inr rfl⟩
  have hs : ∀ x, ((s x).val = 1 ↔ PositiveOutwardLine o x (ν x)) ∧
      ((s x).val = -1 ↔ ¬ PositiveOutwardLine o x (ν x)) := by
    intro x
    by_cases h : PositiveOutwardLine o x (ν x) <;> simp [s, h] <;> norm_num
  refine ⟨s, hs, ?_⟩
  intro t ht
  funext x
  apply Subtype.ext
  rcases (s x).property with h | h
  · rw [h]
    exact (ht x).1.mpr ((hs x).1.mp h)
  · rw [h]
    exact (ht x).2.mpr ((hs x).2.mp h)

def halfspaceChart (r : ℕ∞ω) (d : ℕ) :
    EmbeddedChart r (d+1) (d+1) (halfSpace (d+1)) where
  half := true
  half_pos := by omega
  source := halfSpace (d+1)
  source_open := ⟨univ, isOpen_univ, by simp [parameterSpace]⟩
  ambient := univ
  ambient_open := isOpen_univ
  toFun := id
  invFun := id
  map_source := fun _ h => ⟨h, mem_univ _⟩
  map_target := fun _ h => h.1
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  continuous_toFun := continuous_id.continuousOn
  continuous_invFun := continuous_id.continuousOn
  regular := by
    intro u _
    exact ⟨univ, id, isOpen_univ, mem_univ _, fun _ _ => rfl,
      contDiff_id.contDiffOn, fun _ _ => by simpa using Function.injective_id⟩

theorem halfspaceChart_differential (r : ℕ∞ω) (d : ℕ) (x : E (d+1))
    (hx : x ∈ halfSpace (d+1)) :
    chartDifferential (halfspaceChart r d) x = ContinuousLinearMap.id ℝ _ := by
  exact (hasFDerivWithinAt_id x _).fderivWithin
    (D04.EmbeddedChart.source_uniqueDiff (halfspaceChart r d) x hx)

theorem halfspace_conormal (r : ℕ∞ω) (hr : ManifoldRegularity r)
    (d : ℕ) (x : E (d+1)) (hx : x ∈ flatBoundary (d+1)) :
    IsOutwardUnitConormal r d (halfSpace (d+1)) x
      (-Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d)) := by
  let c := halfspaceChart r d
  have hxs : x ∈ c.source := by
    change 0 ≤ x (Fin.last d)
    rw [show x (Fin.last d) = 0 from hx]
  have hd := halfspaceChart_differential r d x hxs
  change Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c x = ContinuousLinearMap.id ℝ _ at hd
  have ht := D04.tangentSpace_chart c hr le_rfl x hxs
  change tangentSpace r (d+1) (halfSpace (d+1)) x = _ at ht
  have hb := D04.tangentSpace_intrinsic_boundary c hr le_rfl rfl x hxs hx
  change (tangentSpace r d (intrinsicBoundary r (d+1) (halfSpace (d+1))) x : Set (E (d+1))) = _ at hb
  refine ⟨?_, ?_, ?_, c, x,
    -Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d), hxs,
    ⟨rfl, hx⟩, rfl, ?_, ?_⟩
  · rw [ht, hd]
    exact ⟨_, rfl⟩
  · simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]
  · intro v hv
    change v ∈ (tangentSpace r d (intrinsicBoundary r (d+1) (halfSpace (d+1))) x : Set (E (d+1))) at hv
    rw [hb, hd] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left] using congrArg Neg.neg hw
  · rw [hd]
    rfl
  · norm_num [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]

theorem outward_first_standard_determinant (d : ℕ) :
    (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1)).det
      (Fin.cons (-Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) (Fin.last d))
        (fun i : Fin d => Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc)) =
      (-1 : ℝ)^(d+1) := by
  classical
  let B := Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1)
  let V : Fin (d+1) → E (d+1) := Fin.cons (-B (Fin.last d)) (fun i : Fin d => B i.castSucc)
  change B.det V = _
  rw [Module.Basis.det_apply, Matrix.det_succ_row _ (Fin.last d)]
  have hlast : ∀ j : Fin d, B.repr (V j.succ) (Fin.last d) = 0 := by
    intro j
    simp [V]
  have hminor : (B.toMatrix V).submatrix (Fin.last d).succAbove (0 : Fin (d+1)).succAbove = 1 := by
    ext i j
    simp [Module.Basis.toMatrix_apply, V, Fin.succAbove_last, Fin.succAbove_zero,
      Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [Fin.sum_univ_succ]
  simp only [Module.Basis.toMatrix_apply, hlast, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hminor]
  simp [V, pow_succ]

theorem halfspace_orientation :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.halfspace_orientationType := by
  intro r hr d x hx
  let c := halfspaceChart r d
  have hxs : x ∈ c.source := by
    change 0 ≤ x (Fin.last d)
    rw [show x (Fin.last d) = 0 from hx]
  have ht := D04.tangentSpace_chart c hr le_rfl x hxs
  have hb := D04.tangentSpace_intrinsic_boundary c hr le_rfl rfl x hxs hx
  change tangentSpace r (d+1) (halfSpace (d+1)) x = _ at ht
  change (tangentSpace r d (intrinsicBoundary r (d+1) (halfSpace (d+1))) x : Set (E (d+1))) = _ at hb
  have hd : chartDifferential c x = ContinuousLinearMap.id ℝ _ := halfspaceChart_differential r d x hxs
  rw [hd] at ht hb
  refine ⟨halfspace_conormal r hr d x hx, ?_, ?_, outward_first_standard_determinant d⟩
  · simpa using ht
  · simpa using hb

theorem boundary_tangent_le {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M) :
    tangentSpace r d (intrinsicBoundary r (d+1) M) x ≤ tangentSpace r (d+1) M x := by
  obtain ⟨_, c, u, hc, hu, hf, hx⟩ := x.property
  rw [← hx, D04.tangentSpace_chart c hM.1 hM.2.1 u hu]
  intro w hw
  change w ∈ (tangentSpace r d (intrinsicBoundary r (d+1) M) (c.toFun u) : Set (E n)) at hw
  rw [D04.tangentSpace_intrinsic_boundary c hM.1 hM.2.1 hc u hu hf] at hw
  obtain ⟨v, _, rfl⟩ := hw
  exact ⟨v, rfl⟩

theorem conormal_independent {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    {x ν : E n} (hν : IsOutwardUnitConormal r d M x ν) :
    ∀ t : ℝ, ∀ w ∈ tangentSpace r d (intrinsicBoundary r (d+1) M) x,
      t • ν + w = 0 → t = 0 := by
  intro t w hw he
  have h := congrArg (inner ℝ ν) he
  simpa [inner_add_right, real_inner_smul_right, hν.2.2.1 w hw,
    real_inner_self_eq_norm_sq, hν.2.1] using h

theorem conormal_spans {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) {x ν : E n}
    (hν : IsOutwardUnitConormal r d M x ν) :
    ∀ v ∈ tangentSpace r (d+1) M x,
      ∃ t : ℝ, v + t • ν ∈ tangentSpace r d (intrinsicBoundary r (d+1) M) x := by
  obtain ⟨c, u, w, hu, hb, hx, hw, hwn⟩ := hν.2.2.2
  intro v hv
  rw [← hx, D04.tangentSpace_chart c hM.1 hM.2.1 u hu] at hv
  obtain ⟨z, rfl⟩ := hv
  refine ⟨-z (Fin.last d) / w (Fin.last d), ?_⟩
  have hflat : z + (-z (Fin.last d) / w (Fin.last d)) • w ∈ flatBoundary (d+1) := by
    change z (Fin.last d) + (-z (Fin.last d) / w (Fin.last d)) * w (Fin.last d) = 0
    field_simp [ne_of_lt hwn]
    ring
  change (chartDifferential c u) z + _ • ν ∈ _
  rw [← hw, ← map_smul, ← map_add]
  change (chartDifferential c u) _ ∈ (tangentSpace r d (intrinsicBoundary r (d+1) M) x : Set (E n))
  rw [← hx, D04.tangentSpace_intrinsic_boundary c hM.1 hM.2.1 hb.1 u hu hb.2]
  exact ⟨_, hflat, rfl⟩

def extendedBoundaryBasis {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (ν : E n) (hν : IsOutwardUnitConormal r d M x ν)
    (b : Module.Basis (Fin d) ℝ (tangentSpace r d (intrinsicBoundary r (d+1) M) x)) :
    Module.Basis (Fin (d+1)) ℝ (tangentSpace r (d+1) M x) :=
  Module.Basis.mkFinConsOfLE ν hν.1 b (boundary_tangent_le hM x)
    (conormal_independent hν) (conormal_spans hM hν)

theorem extendedBoundaryBasis_apply {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (ν : E n) (hν : IsOutwardUnitConormal r d M x ν)
    (b : Module.Basis (Fin d) ℝ (tangentSpace r d (intrinsicBoundary r (d+1) M) x)) :
    (extendedBoundaryBasis hM x ν hν b : Fin (d+1) → tangentSpace r (d+1) M x) =
      Fin.cons ⟨ν, hν.1⟩ (Submodule.inclusion (boundary_tangent_le hM x) ∘ b) :=
  Module.Basis.coe_mkFinConsOfLE _ _ _ _ _ _

def boundaryForm {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (ν : E n) (hν : IsOutwardUnitConormal r d M x ν) :
    (tangentSpace r d (intrinsicBoundary r (d+1) M) x) [⋀^Fin d]→ₗ[ℝ] ℝ :=
  ((o.atPoint x x.property.1).someVector.curryLeft ⟨ν, hν.1⟩).compLinearMap
    (Submodule.inclusion (boundary_tangent_le o.manifold x))

theorem boundaryForm_basis {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (ν : E n) (hν : IsOutwardUnitConormal r d M x ν)
    (b : Module.Basis (Fin d) ℝ (tangentSpace r d (intrinsicBoundary r (d+1) M) x)) :
    boundaryForm o x ν hν b =
      (o.atPoint x x.property.1).someVector (extendedBoundaryBasis o.manifold x ν hν b) := by
  rw [extendedBoundaryBasis_apply]
  rfl

theorem boundaryForm_ne_zero {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M) (x : intrinsicBoundary r (d+1) M)
    (ν : E n) (hν : IsOutwardUnitConormal r d M x ν) : boundaryForm o x ν hν ≠ 0 := by
  have hB := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  let b := Module.finBasisOfFinrankEq ℝ
    (tangentSpace r d (intrinsicBoundary r (d+1) M) x)
    (D04.tangentSpace_finrank hB x x.property)
  have hnonzero := ((o.atPoint x x.property.1).someVector.map_basis_ne_zero_iff
    (extendedBoundaryBasis o.manifold x ν hν b)).mpr
    (o.atPoint x x.property.1).someVector_ne_zero
  intro h
  have he := boundaryForm_basis o x ν hν b
  rw [h] at he
  exact hnonzero he.symm

def boundaryOrientationField {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (ν : intrinsicBoundary r (d+1) M → E n)
    (hν : ∀ x : intrinsicBoundary r (d+1) M, IsOutwardUnitConormal r d M x (ν x)) :
    TangentOrientationField r d (intrinsicBoundary r (d+1) M) :=
  fun x hx => rayOfNeZero ℝ (boundaryForm o ⟨x, hx⟩ (ν ⟨x, hx⟩) (hν ⟨x, hx⟩))
    (boundaryForm_ne_zero o ⟨x, hx⟩ (ν ⟨x, hx⟩) (hν ⟨x, hx⟩))

theorem basis_orientation_ray_iff {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V [⋀^Fin d]→ₗ[ℝ] ℝ) (hF : F ≠ 0) (b : Module.Basis (Fin d) ℝ V) :
    b.orientation = rayOfNeZero ℝ F hF ↔ 0 < F b := by
  change rayOfNeZero ℝ b.det b.det_ne_zero = rayOfNeZero ℝ F hF ↔ _
  rw [ray_eq_iff]
  conv_lhs => rw [F.eq_smul_basis_det b,
    sameRay_smul_right_iff_of_ne b.det_ne_zero ((F.map_basis_ne_zero_iff b).mpr hF)]

theorem boundaryOrientationField_positive {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (ν : intrinsicBoundary r (d+1) M → E n)
    (hν : ∀ x : intrinsicBoundary r (d+1) M, IsOutwardUnitConormal r d M x (ν x))
    (x : intrinsicBoundary r (d+1) M)
    (b : Module.Basis (Fin d) ℝ (tangentSpace r d (intrinsicBoundary r (d+1) M) x)) :
    b.orientation = boundaryOrientationField o ν hν x x.property ↔ PositiveWithOutward o x (ν x) b := by
  change b.orientation = rayOfNeZero ℝ _ _ ↔ _
  rw [basis_orientation_ray_iff, boundaryForm_basis, D04.Orientations.representative_pos_iff]
  constructor
  · intro h
    refine ⟨extendedBoundaryBasis o.manifold x (ν x) (hν x) b, ?_, ?_, h⟩
    · rw [extendedBoundaryBasis_apply]
      rfl
    · intro i
      rw [extendedBoundaryBasis_apply]
      rfl
  · rintro ⟨B, hB0, hBs, hB⟩
    have he : extendedBoundaryBasis o.manifold x (ν x) (hν x) b = B := by
      apply DFunLike.ext
      intro i
      rw [extendedBoundaryBasis_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Subtype.ext hB0.symm
      · exact Subtype.ext (hBs j).symm
    rwa [he]

theorem cons_standard_det (d : ℕ) (z : E (d+1)) :
    (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1)).det
      (Fin.cons z (fun i : Fin d => Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc)) =
      (-1 : ℝ)^d * z (Fin.last d) := by
  classical
  let B := Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1)
  let V : Fin (d+1) → E (d+1) := Fin.cons z (fun i : Fin d => B i.castSucc)
  change B.det V = _
  rw [Module.Basis.det_apply, Matrix.det_succ_row _ (Fin.last d)]
  have hlast : ∀ j : Fin d, B.repr (V j.succ) (Fin.last d) = 0 := by intro j; simp [V]
  have hminor : (B.toMatrix V).submatrix (Fin.last d).succAbove (0 : Fin (d+1)).succAbove = 1 := by
    ext i j
    simp [Module.Basis.toMatrix_apply, V, Fin.succAbove_last, Fin.succAbove_zero,
      Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [Fin.sum_univ_succ]
  simp only [Module.Basis.toMatrix_apply, hlast, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hminor]
  simp only [V, Fin.cons_zero, Fin.val_zero, add_zero, Matrix.det_one, mul_one]
  rfl

theorem alternating_cons_standard {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V [⋀^Fin (d+1)]→ₗ[ℝ] ℝ) (G : E (d+1) →ₗ[ℝ] V) (z : E (d+1)) :
    F (Fin.cons (G z) (fun i : Fin d => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc))) =
      F (fun i => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i)) *
        ((-1 : ℝ)^d * z (Fin.last d)) := by
  let f := F.compLinearMap G
  have he : (Fin.cons (G z) (fun i : Fin d => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc))) =
      G ∘ (Fin.cons z (fun i : Fin d => Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]
  change f _ = f _ * _
  conv_lhs => rw [f.eq_smul_basis_det (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1))]
  rw [smul_apply, smul_eq_mul, cons_standard_det]

theorem boundaryChart_differential {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r (d+1) n M) (hr : ManifoldRegularity r) (hkn : d+1 ≤ n)
    (hc : c.half = true) (v : E d) (hv : v ∈ (D04.EmbeddedChart.boundaryChart c hr hkn hc).source) :
    chartDifferential (D04.EmbeddedChart.boundaryChart c hr hkn hc) v =
      (chartDifferential c (D04.flatInclusion d v)).comp (D04.flatInclusion d) := by
  apply (D04.EmbeddedChart.source_uniqueDiff (D04.EmbeddedChart.boundaryChart c hr hkn hc) v hv).eq
    (D04.EmbeddedChart.hasDifferential _ hr hv)
  exact (D04.EmbeddedChart.hasDifferential c hr hv).comp v
    (D04.flatInclusion d).hasFDerivAt.hasFDerivWithinAt (fun _ h => h)

theorem flatInclusion_basis (d : ℕ) (i : Fin d) :
    D04.flatInclusion d (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis d i) =
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
  · simp [Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]

theorem ray_representative_sign {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V [⋀^Fin d]→ₗ[ℝ] ℝ) (hF : F ≠ 0) (v : Fin d → V) :
    Real.sign ((rayOfNeZero ℝ F hF).someVector v) = Real.sign (F v) := by
  let o := rayOfNeZero ℝ F hF
  have hs : SameRay ℝ o.someVector F :=
    (ray_eq_iff o.someVector_ne_zero hF).mp (Module.Ray.someVector_ray o)
  obtain ⟨t, ht, he⟩ := hs.exists_pos_left o.someVector_ne_zero hF
  have hev := congrArg (fun f : V [⋀^Fin d]→ₗ[ℝ] ℝ => f v) he
  simp only [smul_apply, smul_eq_mul] at hev
  rw [← hev, D04.Orientations.sign_mul, Real.sign_of_pos ht, one_mul]

theorem boundary_chart_sign {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (ν : intrinsicBoundary r (d+1) M → E n)
    (hν : ∀ x : intrinsicBoundary r (d+1) M, IsOutwardUnitConormal r d M x (ν x))
    (c : EmbeddedChart r (d+1) n M) (hc : c.half = true)
    (v : E d) (hv : v ∈ (D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hc).source) :
    chartSign (boundaryOrientationField o ν hν)
        (D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hc) v hv =
      chartSign o.atPoint c (D04.flatInclusion d v) hv * (-1 : ℝ)^(d+1) := by
  let b := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hc
  let u := D04.flatInclusion d v
  have hb : IsBoundaryParameter c u := ⟨hc, D04.flatInclusion_last d v⟩
  let x : intrinsicBoundary r (d+1) M := ⟨c.toFun u,
    (D04.chart_intrinsicBoundary c o.manifold.1 o.manifold.2.1 u hv).mpr hb⟩
  have hux := hν x
  have hrange := hux.1
  rw [D04.tangentSpace_chart c o.manifold.1 o.manifold.2.1 u hv] at hrange
  obtain ⟨z, hz⟩ := hrange
  have hzn : z (Fin.last d) < 0 :=
    (outward_chart_independent o.manifold c u hv hb z).mp (hz ▸ hux.2.2.2)
  let G : E (d+1) →ₗ[ℝ] tangentSpace r (d+1) M x := tangentChartMap c u hv
  let F := (o.atPoint x x.property.1).someVector
  have hval : boundaryForm o x (ν x) hux
      (fun i => tangentChartMap b v hv (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis d i)) =
      chartCoefficient o.atPoint c u hv * ((-1 : ℝ)^d * z (Fin.last d)) := by
    have htuple : Fin.cons (⟨ν x, hux.1⟩ : tangentSpace r (d+1) M x)
        (fun i => Submodule.inclusion (boundary_tangent_le o.manifold x)
          (tangentChartMap b v hv (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis d i))) =
        Fin.cons (α := fun _ : Fin (d+1) => tangentSpace r (d+1) M x) (G z) (fun i : Fin d => G (Specs.D04.C01.EuclideanInterfaces.Model.standardBasis (d+1) i.castSucc)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Subtype.ext hz.symm
      · apply Subtype.ext
        change chartDifferential b v _ = chartDifferential c u _
        rw [boundaryChart_differential c o.manifold.1 o.manifold.2.1 hc v hv,
          ContinuousLinearMap.comp_apply, flatInclusion_basis]
    change F (Fin.cons _ _) = _
    rw [htuple, alternating_cons_standard]
    rfl
  change Real.sign ((rayOfNeZero ℝ (boundaryForm o x (ν x) hux) _).someVector _) = _
  erw [ray_representative_sign, hval, D04.Orientations.sign_mul, D04.Orientations.sign_mul,
    Real.sign_of_neg hzn]
  have hs : Real.sign ((-1 : ℝ)^d) = (-1 : ℝ)^d := by
    rcases neg_one_pow_eq_or ℝ d with h | h <;> rw [h] <;> norm_num [Real.sign_of_neg]
  rw [hs, pow_succ]
  rfl

theorem sign_locally_constant {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : Continuous f) (hn : ∀ x, f x ≠ 0) : IsLocallyConstant (fun x => Real.sign (f x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  rcases (hn x).lt_or_gt with hx | hx
  · have hev := hf.continuousAt.eventually (Iio_mem_nhds hx)
    filter_upwards [hev] with y hy
    rw [Real.sign_of_neg hy, Real.sign_of_neg hx]
  · have hev := hf.continuousAt.eventually (Ioi_mem_nhds hx)
    filter_upwards [hev] with y hy
    rw [Real.sign_of_pos hy, Real.sign_of_pos hx]

theorem field_sign_locally_constant {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (p : TangentOrientationField r k M)
    (b a : EmbeddedChart r k n M)
    (ha : IsLocallyConstant (fun u : a.source => chartSign p a u u.property))
    (v : b.source) (hv : b.toFun v ∈ a.ambient) :
    ∃ U : Set b.source, IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ U, chartSign p b w w.property = chartSign p b v v.property := by
  let P : Set b.source := {w | b.toFun w ∈ a.ambient}
  have hP : IsOpen P := a.ambient_open.preimage b.continuous_toFun.domRestrict
  let J : P → chartOverlap b a := fun w => ⟨w.val.val, w.val.property, w.property⟩
  have hJ : Continuous J := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let T : P → a.source := fun w => ⟨chartTransition b a w.val.val,
    (D04.EmbeddedChart.transition_mem b a (J w).property).1⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    exact (D04.EmbeddedChart.transition_continuous b a).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun w => (J w).property)
  have hA := ha.comp_continuous hT
  have hdiff := (D04.chart_transition_regular b a hM.1 hM.2.1).1.continuousOn_fderivWithin
    (D04.EmbeddedChart.overlap_uniqueDiff b a) hM.1.1
  let D : P → E k →L[ℝ] E k := fun w =>
    fderivWithin ℝ (chartTransition b a) (chartOverlap b a) w.val.val
  have hD : Continuous D := hdiff.comp_continuous
    (continuous_subtype_val.comp continuous_subtype_val) (fun w => (J w).property)
  have hdet : Continuous (fun w : P => LinearMap.det (D w).toLinearMap) :=
    ContinuousLinearMap.continuous_det.comp hD
  have hn : ∀ w : P, LinearMap.det (D w).toLinearMap ≠ 0 := by
    intro w
    obtain ⟨A, hA, _⟩ := D04.chart_transition_derivatives b a hM.1 hM.2.1 _ (J w).property
    change LinearMap.det (fderivWithin ℝ (chartTransition b a) (chartOverlap b a) _).toLinearMap ≠ 0
    rw [hA.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff b a _ (J w).property)]
    exact A.toLinearEquiv.isUnit_det'.ne_zero
  have hS := hA.mul (sign_locally_constant _ hdet hn)
  have he : (fun w : P => chartSign p b w.val.val w.val.property) =
      (fun w : P => chartSign p a (T w).val (T w).property * Real.sign (LinearMap.det (D w).toLinearMap)) := by
    funext w
    exact D04.Orientations.chartSign_transition p b a hM.1 hM.2.1 _ (J w).property (T w).property
  have hlocal : IsLocallyConstant (fun w : P => chartSign p b w.val.val w.val.property) := by
    rw [he]
    exact hS
  obtain ⟨Q, hQ, hvQ, hconst⟩ := hlocal.exists_open ⟨v, hv⟩
  refine ⟨Subtype.val '' Q, hP.isOpenMap_subtype_val _ hQ, ⟨⟨v, hv⟩, hvQ, rfl⟩, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  exact hconst z hz

theorem boundaryOrientationField_locally_constant {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+1) M)
    (ν : intrinsicBoundary r (d+1) M → E n)
    (hν : ∀ x : intrinsicBoundary r (d+1) M, IsOutwardUnitConormal r d M x (ν x))
    (b : EmbeddedChart r d n (intrinsicBoundary r (d+1) M)) :
    IsLocallyConstant (fun v : b.source => chartSign (boundaryOrientationField o ν hν) b v v.property) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro v
  have hx := (b.map_source v.property).1
  obtain ⟨_, c, u, hc, hu, hf, hux⟩ := hx
  let a := D04.EmbeddedChart.boundaryChart c o.manifold.1 o.manifold.2.1 hc
  have ha : IsLocallyConstant (fun w : a.source =>
      chartSign (boundaryOrientationField o ν hν) a w w.property) := by
    let I : a.source → c.source := fun w => ⟨D04.flatInclusion d w, w.property⟩
    have hI : Continuous I := ((D04.flatInclusion d).continuous.comp continuous_subtype_val).subtype_mk _
    have hL := ((o.locally_constant c).comp_continuous hI).mul
      (IsLocallyConstant.const ((-1 : ℝ)^(d+1)))
    have he : (fun w : a.source => chartSign (boundaryOrientationField o ν hν) a w w.property) =
        (fun w : a.source => chartSign o.atPoint c (I w).val (I w).property * (-1 : ℝ)^(d+1)) := by
      funext w
      exact boundary_chart_sign o ν hν c hc w w.property
    rw [he]
    exact hL
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  exact field_sign_locally_constant hbM (boundaryOrientationField o ν hν) b a ha v (by
    change b.toFun v ∈ c.ambient
    rw [← hux]
    exact (c.map_source hu).2)

def inducedBoundaryOrientation {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r (d+2) M)
    (ν : intrinsicBoundary r (d+2) M → E n)
    (hν : ∀ x : intrinsicBoundary r (d+2) M, IsOutwardUnitConormal r (d+1) M x (ν x)) :
    PositiveManifoldOrientation r (d+1) (intrinsicBoundary r (d+2) M) where
  positive_dimension := Nat.succ_pos _
  manifold := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold o.manifold)).1
  atPoint := boundaryOrientationField o ν hν
  locally_constant := boundaryOrientationField_locally_constant o ν hν

theorem manifoldOrientation_ext {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (a b : PositiveManifoldOrientation r k M) (h : a.atPoint = b.atPoint) : a = b := by
  cases a
  cases b
  dsimp at h
  cases h
  rfl

theorem boundary_orientation :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.boundary_orientationType := by
  intro r d n M o ν hν
  refine ⟨inducedBoundaryOrientation o ν hν, boundaryOrientationField_positive o ν hν, ?_⟩
  intro bO hbO
  have he : bO.atPoint = (inducedBoundaryOrientation o ν hν).atPoint := by
    funext x hx
    have hB := bO.manifold
    let b := Module.finBasisOfFinrankEq ℝ (tangentSpace r (d+1) (intrinsicBoundary r (d+2) M) x)
      (D04.tangentSpace_finrank hB x hx)
    obtain ⟨c, hc⟩ := D04.Orientations.orientation_basis b (Nat.succ_pos _) (bO.atPoint x hx)
    exact ((boundaryOrientationField_positive o ν hν ⟨x, hx⟩ c).mpr ((hbO ⟨x, hx⟩ c).mp hc)).symm.trans hc |>.symm
  exact manifoldOrientation_ext _ _ he

def linePoint (t : ℝ) : E 1 := t • standardBasis 1 0

@[simp] theorem linePoint_coord (t : ℝ) (i : Fin 1) : linePoint t i = t := by
  fin_cases i
  simp [linePoint, standardBasis, EuclideanSpace.basisFun_apply]

def endpointChart (r : ℕ∞ω) (a b : ℝ) (_hab : a < b) (upper : Bool) :
    EmbeddedChart r 1 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} where
  half := true
  half_pos := by omega
  source := {u | 0 ≤ u 0 ∧ u 0 < b-a}
  source_open := ⟨{u | u 0 < b-a}, isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const, rfl⟩
  ambient := if upper then {x | a < x 0} else {x | x 0 < b}
  ambient_open := by
    cases upper
    · exact isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const
    · exact isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  toFun := if upper then (fun u => linePoint b - u) else (fun u => linePoint a + u)
  invFun := if upper then (fun x => linePoint b - x) else (fun x => x - linePoint a)
  map_source := by
    intro u hu
    cases upper
    · change (a ≤ (linePoint a + u) 0 ∧ (linePoint a + u) 0 ≤ b) ∧ (linePoint a + u) 0 < b
      simp only [PiLp.add_apply, linePoint_coord]
      exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, by linarith [hu.2]⟩
    · change (a ≤ (linePoint b - u) 0 ∧ (linePoint b - u) 0 ≤ b) ∧ a < (linePoint b - u) 0
      simp only [PiLp.sub_apply, linePoint_coord]
      exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, by linarith [hu.2]⟩
  map_target := by
    intro x hx
    cases upper
    · change 0 ≤ (x - linePoint a) 0 ∧ (x - linePoint a) 0 < b-a
      change (a ≤ x 0 ∧ x 0 ≤ b) ∧ x 0 < b at hx
      simp only [PiLp.sub_apply, linePoint_coord]
      exact ⟨by linarith [hx.1.1], by linarith [hx.2]⟩
    · change 0 ≤ (linePoint b - x) 0 ∧ (linePoint b - x) 0 < b-a
      change (a ≤ x 0 ∧ x 0 ≤ b) ∧ a < x 0 at hx
      simp only [PiLp.sub_apply, linePoint_coord]
      exact ⟨by linarith [hx.1.2], by linarith [hx.2]⟩
  left_inv := by intro u _; cases upper <;> simp
  right_inv := by intro x _; cases upper <;> simp
  continuous_toFun := by
    cases upper
    · exact (continuous_const.add continuous_id).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
  continuous_invFun := by
    cases upper
    · exact (continuous_id.sub continuous_const).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
  regular := by
    intro u hu
    cases upper
    · refine ⟨univ, fun u => linePoint a + u, isOpen_univ, mem_univ _, fun _ _ => rfl,
        (contDiff_const.add contDiff_id).contDiffOn, ?_⟩
      intro v _
      have hd : fderiv ℝ (fun u : E 1 => linePoint a + u) v = ContinuousLinearMap.id ℝ _ :=
        ((hasFDerivAt_id (𝕜 := ℝ) v).const_add (linePoint a)).fderiv
      rw [hd]
      exact Function.injective_id
    · refine ⟨univ, fun u => linePoint b - u, isOpen_univ, mem_univ _, fun _ _ => rfl,
        (contDiff_const.sub contDiff_id).contDiffOn, ?_⟩
      intro v _
      have hd : fderiv ℝ (fun u : E 1 => linePoint b - u) v = -ContinuousLinearMap.id ℝ _ :=
        ((hasFDerivAt_id (𝕜 := ℝ) v).const_sub (linePoint b)).fderiv
      rw [hd]
      exact neg_injective

theorem endpointChart_differential (r : ℕ∞ω) (a b : ℝ) (hab : a < b) (upper : Bool)
    (u : E 1) (hu : u ∈ (endpointChart r a b hab upper).source) :
    chartDifferential (endpointChart r a b hab upper) u =
      if upper then -ContinuousLinearMap.id ℝ (E 1) else ContinuousLinearMap.id ℝ (E 1) := by
  apply HasFDerivWithinAt.fderivWithin _
    (D04.EmbeddedChart.source_uniqueDiff (endpointChart r a b hab upper) u hu)
  cases upper
  · exact ((hasFDerivAt_id u).const_add (linePoint a)).hasFDerivWithinAt
  · exact ((hasFDerivAt_id u).const_sub (linePoint b)).hasFDerivWithinAt

theorem endpoint_mem_boundary (r : ℕ∞ω) (a b : ℝ) (hab : a < b) (upper : Bool) :
    linePoint (if upper then b else a) ∈
      intrinsicBoundary r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} := by
  let c := endpointChart r a b hab upper
  have h0 : (0 : E 1) ∈ c.source := ⟨by simp, by simpa using sub_pos.mpr hab⟩
  have hx : c.toFun 0 = linePoint (if upper then b else a) := by
    cases upper <;> simp [c, endpointChart]
  refine ⟨?_, c, 0, rfl, h0, rfl, hx⟩
  rw [← hx]
  exact (c.map_source h0).1

theorem normal_id (d : ℕ) : normalOfDifferential (ContinuousLinearMap.id ℝ (E (d+1))) =
    -standardBasis (d+1) (Fin.last d) := by
  simp [normalOfDifferential, dualNormal, standardBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.adjoint_id]

theorem normal_neg_id (d : ℕ) : normalOfDifferential (-ContinuousLinearMap.id ℝ (E (d+1))) =
    standardBasis (d+1) (Fin.last d) := by
  simp [normalOfDifferential, dualNormal, standardBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.comp_neg, ContinuousLinearMap.adjoint_id]

theorem endpoint_conormal {r : ℕ∞ω} (a b : ℝ) (hab : a < b)
    (hM : IsEmbeddedManifold r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) (upper : Bool) :
    IsOutwardUnitConormal r 0 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}
      (linePoint (if upper then b else a))
      (if upper then standardBasis 1 0 else -standardBasis 1 0) := by
  let c := endpointChart r a b hab upper
  have h0 : (0 : E 1) ∈ c.source := ⟨by simp, by simpa using sub_pos.mpr hab⟩
  have h := conormal_chart_formula hM c 0 h0 ⟨rfl, rfl⟩
  rw [endpointChart_differential r a b hab upper 0 h0] at h
  cases upper
  · simpa [c, endpointChart, normal_id] using h
  · simpa [c, endpointChart, normal_neg_id] using h

theorem line_basis_exists {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 1 M) (x : intrinsicBoundary r 1 M) (ν : E n)
    (hν : IsOutwardUnitConormal r 0 M x ν) :
    ∃ B : Module.Basis (Fin 1) ℝ (tangentSpace r 1 M x), (B 0).val = ν := by
  let b := Module.finBasisOfFinrankEq ℝ (tangentSpace r 1 M x) (D04.tangentSpace_finrank hM x x.property.1)
  let z : tangentSpace r 1 M x := ⟨ν, hν.1⟩
  let t := b.repr z 0
  have hz : t • b 0 = z := by
    simpa only [Fin.sum_univ_one] using b.sum_repr z
  have ht : t ≠ 0 := by
    intro ht
    have he : ν = 0 := by
      have := congrArg Subtype.val hz
      simpa only [ht, zero_smul, Submodule.coe_zero] using this.symm
    have := hν.2.1
    rw [he, norm_zero] at this
    norm_num at this
  let B := b.unitsSMul (fun _ => Units.mk0 t ht)
  refine ⟨B, ?_⟩
  have he : B 0 = t • b 0 := by rw [Module.Basis.unitsSMul_apply]; rfl
  exact congrArg Subtype.val (he.trans hz)

theorem interval_endpoint_signs :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.interval_endpoint_signsType := by
  intro r a b hab ε hε o hstd
  let M : Set (E 1) := {x | a ≤ x 0 ∧ x 0 ≤ b}
  let ha := endpoint_mem_boundary r a b hab false
  let hb := endpoint_mem_boundary r a b hab true
  let ν := outwardConormal o.manifold
  have hν := outwardConormal_spec o.manifold
  obtain ⟨s, hs, _⟩ := boundary_point_sign o ν hν
  have hpos : ∀ x : intrinsicBoundary r 1 M, PositiveOutwardLine o x (ν x) ↔ 0 < ε * ν x 0 := by
    intro x
    constructor
    · rintro ⟨B, hB, hBo⟩
      have h := (hstd x x.property.1 B).mp hBo
      rwa [hB] at h
    · intro hp
      obtain ⟨B, hB⟩ := line_basis_exists o.manifold x (ν x) (hν x)
      refine ⟨B, hB, (hstd x x.property.1 B).mpr ?_⟩
      rwa [hB]
  have hνa : ν ⟨linePoint a, ha⟩ = -standardBasis 1 0 := by
    exact (conormal_exists_unique o.manifold _ ha).unique (hν ⟨_, ha⟩)
      (endpoint_conormal a b hab o.manifold false)
  have hνb : ν ⟨linePoint b, hb⟩ = standardBasis 1 0 := by
    exact (conormal_exists_unique o.manifold _ hb).unique (hν ⟨_, hb⟩)
      (endpoint_conormal a b hab o.manifold true)
  rcases hε with rfl | rfl
  · refine ⟨ha, hb, ν, s, outwardConormal_continuous o.manifold, hν,
      fun x => (hs x).1, (hs ⟨linePoint a, ha⟩).2.mpr ?_, (hs ⟨linePoint b, hb⟩).1.mpr ?_⟩
    · rw [hpos, hνa]
      norm_num [standardBasis, EuclideanSpace.basisFun_apply]
    · rw [hpos, hνb]
      norm_num [standardBasis, EuclideanSpace.basisFun_apply]
  · refine ⟨ha, hb, ν, s, outwardConormal_continuous o.manifold, hν,
      fun x => (hs x).1, ?_, (hs ⟨linePoint b, hb⟩).2.mpr ?_⟩
    · have hp : PositiveOutwardLine o ⟨linePoint a, ha⟩ (ν ⟨linePoint a, ha⟩) := by
        rw [hpos, hνa]
        norm_num [standardBasis, EuclideanSpace.basisFun_apply]
      simpa only [linePoint, neg_neg] using (hs ⟨linePoint a, ha⟩).1.mpr hp
    · rw [hpos, hνb]
      norm_num [standardBasis, EuclideanSpace.basisFun_apply]

theorem sign_mul_positive_iff (q t : ℝ) (hq : q ≠ 0) :
    0 < Real.sign q * t ↔ 0 < q * t := by
  rcases hq.lt_or_gt with h | h
  · rw [Real.sign_of_neg h]
    constructor <;> intro ht <;> nlinarith
  · rw [Real.sign_of_pos h]
    constructor <;> intro ht <;> nlinarith

theorem line_orientation_test (T : Submodule ℝ (E 1))
    (O : SpaceOrientation 1 T) (b B : Module.Basis (Fin 1) ℝ T)
    (β : ℝ) (hβ : β = 1 ∨ β = -1) (hb : (b 0).val 0 = β) :
    B.orientation = O ↔
      0 < Real.sign (O.someVector b) * β * (B 0).val 0 := by
  have he : b.det B * β = (B 0).val 0 := by
    have hh := congrArg (fun w : T => w.val 0) (b.sum_repr (B 0))
    rw [Module.Basis.det_apply, Matrix.det_fin_one]
    simpa only [Fin.sum_univ_one, Submodule.coe_smul, PiLp.smul_apply,
      smul_eq_mul, Module.Basis.toMatrix_apply, hb] using hh
  have hd : b.det B = β * (B 0).val 0 := by
    rcases hβ with rfl | rfl <;> linarith
  have hF : O.someVector B = O.someVector b * b.det B := by
    conv_lhs => rw [O.someVector.eq_smul_basis_det b]
    rfl
  rw [← D04.Orientations.representative_pos_iff O B, hF, hd]
  simpa only [mul_assoc] using (sign_mul_positive_iff (O.someVector b) (β * (B 0).val 0)
    ((O.someVector.map_basis_ne_zero_iff b).mpr O.someVector_ne_zero)).symm

theorem endpoint_chart_basis_test {r : ℕ∞ω} {a b : ℝ} (hab : a < b)
    (o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
    (upper : Bool) (u : E 1) (hu : u ∈ (endpointChart r a b hab upper).source)
    (x : E 1) (hx : a ≤ x 0 ∧ x 0 ≤ b)
    (hpoint : (endpointChart r a b hab upper).toFun u = x)
    (B : Module.Basis (Fin 1) ℝ (tangentSpace r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x)) :
    B.orientation = o.atPoint x hx ↔
      0 < chartSign o.atPoint (endpointChart r a b hab upper) u hu *
        (if upper then -1 else 1) * (B 0).val 0 := by
  subst x
  let c := endpointChart r a b hab upper
  let b0 := D04.Orientations.chartBasis c o.manifold.1 o.manifold.2.1 u hu
  apply line_orientation_test _ _ b0 B
  · cases upper <;> simp
  · change (chartDifferential c u (standardBasis 1 0)) 0 = _
    rw [endpointChart_differential r a b hab upper u hu]
    cases upper <;> simp [standardBasis, EuclideanSpace.basisFun_apply]

theorem endpoint_chart_sign_constant {r : ℕ∞ω} {a b : ℝ} (hab : a < b)
    (o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
    (upper : Bool) (u v : E 1)
    (hu : u ∈ (endpointChart r a b hab upper).source)
    (hv : v ∈ (endpointChart r a b hab upper).source) :
    chartSign o.atPoint (endpointChart r a b hab upper) u hu =
      chartSign o.atPoint (endpointChart r a b hab upper) v hv := by
  let c := endpointChart r a b hab upper
  have hcv : Convex ℝ c.source :=
    (convex_Ico (0 : ℝ) (b-a)).linear_preimage (EuclideanSpace.proj 0).toLinearMap
  haveI : PreconnectedSpace c.source := isPreconnected_iff_preconnectedSpace.mp hcv.isPreconnected
  exact congrFun ((o.locally_constant c).eq_const (⟨v, hv⟩ : c.source)) ⟨u, hu⟩

theorem interval_orientation_classification {r : ℕ∞ω} (a b : ℝ) (hab : a < b)
    (o : PositiveManifoldOrientation r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ (x : E 1) (hx : a ≤ x 0 ∧ x 0 ≤ b)
        (B : Module.Basis (Fin 1) ℝ (tangentSpace r 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x)),
        B.orientation = o.atPoint x hx ↔ 0 < ε * (B 0).val 0 := by
  let c := endpointChart r a b hab false
  let d := endpointChart r a b hab true
  have h0c : (0 : E 1) ∈ c.source := ⟨by simp, by simpa using sub_pos.mpr hab⟩
  have h0d : (0 : E 1) ∈ d.source := h0c
  let m := linePoint ((b-a)/2)
  have hmc : m ∈ c.source := by
    change 0 ≤ linePoint ((b-a)/2) 0 ∧ linePoint ((b-a)/2) 0 < b-a
    simp only [linePoint_coord]
    constructor <;> linarith
  have hmov : m ∈ chartOverlap c d := ⟨hmc, by
    change a < (linePoint a + m) 0
    simp only [PiLp.add_apply, linePoint_coord, m]
    linarith⟩
  have hmT : chartTransition c d m ∈ d.source := (D04.EmbeddedChart.transition_mem c d hmov).1
  have hder : HasFDerivWithinAt (chartTransition c d) (-ContinuousLinearMap.id ℝ (E 1)) (chartOverlap c d) m :=
    (((hasFDerivAt_id (𝕜 := ℝ) m).const_add (linePoint a)).const_sub (linePoint b)).hasFDerivWithinAt
  have hdet : LinearMap.det (-ContinuousLinearMap.id ℝ (E 1)).toLinearMap = -1 := by
    rw [D04.Orientations.line_det]
    norm_num [standardBasis, EuclideanSpace.basisFun_apply]
  have hsign := D04.Orientations.chartSign_transition o.atPoint c d o.manifold.1 o.manifold.2.1 m hmov hmT
  rw [hder.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff c d m hmov), hdet,
    Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0), mul_neg_one,
    endpoint_chart_sign_constant hab o false m 0 hmc h0c,
    endpoint_chart_sign_constant hab o true _ 0 hmT h0d] at hsign
  refine ⟨chartSign o.atPoint c 0 h0c,
    D04.Orientations.chartSign_values o.atPoint c o.manifold.1 o.manifold.2.1 0 h0c, ?_⟩
  intro x hx
  by_cases hxb : x 0 < b
  · have hxm : x ∈ {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} ∩ c.ambient := ⟨hx, hxb⟩
    have hu := c.map_target hxm
    have hpoint := c.right_inv x hxm
    have ht := endpoint_chart_basis_test hab o false (c.invFun x) hu x hx hpoint
    intro B
    simpa only [Bool.false_eq_true, ite_false, mul_one,
      endpoint_chart_sign_constant hab o false _ 0 hu h0c] using ht B
  · have hax : a < x 0 := by linarith [hx.2]
    have hxm : x ∈ {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} ∩ d.ambient := ⟨hx, hax⟩
    have hu := d.map_target hxm
    have hpoint := d.right_inv x hxm
    have ht := endpoint_chart_basis_test hab o true (d.invFun x) hu x hx hpoint
    intro B
    simpa only [ite_true, mul_neg_one, endpoint_chart_sign_constant hab o true _ 0 hu h0d,
      ← hsign] using ht B

theorem oriented_interval_endpoint_signs :
    Specs.D04.C14.OutwardFirstBoundaryOrientation.oriented_interval_endpoint_signsType := by
  intro r a b hab o
  obtain ⟨ε, hε, hstd⟩ := interval_orientation_classification a b hab o
  exact ⟨ε, hε, hstd, interval_endpoint_signs a b hab ε hε o hstd⟩

abbrev IsOutwardVector := @Specs.D04.C14.OutwardFirstBoundaryOrientation.Model.IsOutwardVector
abbrev IsOutwardUnitConormal := @Specs.D04.C14.OutwardFirstBoundaryOrientation.Model.IsOutwardUnitConormal
abbrev normalOfDifferential := @Specs.D04.C14.OutwardFirstBoundaryOrientation.Model.normalOfDifferential

end D04BoundaryOrientation
