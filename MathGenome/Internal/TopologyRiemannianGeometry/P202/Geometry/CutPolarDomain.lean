import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutPolarDomain
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CutCriterion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace P202.Geometry.CutPolarDomain
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  SmoothManifolds.PartitionData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.CompletenessData P202.CompleteExponentialData
  P202.CutTimeData P202.CutCriterionData P202.CutPolarData
  P202.CurvatureData P202.ExponentialJacobiData
open Set Filter
open scoped Topology ENNReal
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Any linear coordinates induce the usual topology on the actual unit sphere. -/
theorem direction_coordinates_continuous (g : RiemannianMetric S) (p : M)
    (E D : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    letI := directionTopology g p E
    Continuous (fun v : UnitDirection g p => D v.val) := by
  letI := directionTopology g p E
  have h : Continuous (fun v : UnitDirection g p => E v.val) := continuous_induced_dom
  have hD := (E.symm.trans D).toContinuousLinearEquiv.continuous.comp h
  change Continuous (fun v : UnitDirection g p => D (E.symm (E v.val))) at hD
  simpa only [E.symm_apply_apply] using hD

/-- The exponential of a fixed radius varies continuously with the direction. -/
theorem sphere_exponential_continuous
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (t : ℝ) :
    letI := directionTopology g p E
    Continuous (fun v : UnitDirection g p => fiberExponential F p (t • v.val)) := by
  letI := directionTopology g p E
  have hcoords : Continuous (fun v : UnitDirection g p => t • E v.val) :=
    (direction_coordinates_continuous g p E E).const_smul t
  have h := (CompleteExponentialMinimizers.exponential_coordinates_continuous C F hF p hfull E).comp hcoords
  simpa only [Function.comp_def,map_smul,E.symm_apply_apply] using h

/-- Nonsingularity at a strict interior point of a minimizing ray. -/
theorem interior_nonsingular [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) {t : ℝ} (ht : 0 < t)
    (htc : ENNReal.ofReal t < cutTime g F p v) :
    Function.Bijective (fiberDifferential S F p (t • v.val)) := by
  obtain ⟨_,_,htI,hnot⟩ :=
    CutCriterion.interior_unique_nonconjugate S g hn hc C hC R hR F hF p v t ht htc
  by_contra hsing
  exact hnot ((ExponentialJacobi.conjugacy_singularity S g C hC R hR F hF p v.val t ht htI).mpr hsing)

/-- A fixed strict interior radius remains minimizing for nearby directions.
This is the stability step, on the original sphere topology. -/
theorem nearby_minimizing_time [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (v : UnitDirection g p) {t : ℝ} (ht : 0 < t)
    (htc : ENNReal.ofReal t < cutTime g F p v) :
    letI := directionTopology g p E
    ∀ᶠ v' in 𝓝 v, t ∈ minimizingTimes g F p v' := by
  letI := directionTopology g p E
  have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
  have htmem := (hi.2.2.2.1 t).mpr ⟨ht.le,htc.le⟩
  obtain ⟨hmin,huniq⟩ := CutCriterion.interior_unique g hn hc C hC F hF p v ht htc
  have hqp : fiberExponential F p (t • v.val) ≠ p := by
    intro heq
    have h := htmem.2
    rw [heq,CompleteExponentialMinimizers.lengthDistance_self] at h
    linarith
  obtain ⟨D,c,U,hcInv,hU,hqU,hUc,hstable⟩ :=
    CutCriterion.minimizing_stability S g hn hc C hC F hF p _ _ hqp hmin huniq
      (interior_nonsingular g hn hc C hC R hR F hF p v ht htc)
  let x : UnitDirection g p → ModelSpace n .euclidean := fun u => ⟨D (t • u.val),mem_univ _⟩
  have hcoords : Continuous (fun u : UnitDirection g p => t • D u.val) :=
    (direction_coordinates_continuous g p E D).const_smul t
  have hxc : Continuous x := by
    simpa only [x,map_smul] using hcoords.subtype_mk (fun _ => mem_univ _)
  have hfc := sphere_exponential_continuous g C F hF p hi.1 E t
  have hxv : x v ∈ c.target := by
    have heq : x v = c (fiberExponential F p (t • v.val)) :=
      Subtype.ext hcInv.2.2.1.symm
    rw [heq]
    exact c.map_source hcInv.2.1
  have hnear : ∀ᶠ u in 𝓝 v, fiberExponential F p (t • u.val) ∈ U ∧ x u ∈ c.target := by
    filter_upwards [hfc.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU),
      hxc.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hxv)] with u hu hx
    exact ⟨hu,hx⟩
  filter_upwards [hnear] with u hu
  have he : fiberExponential F p (t • u.val) = c.symm (x u) := by
    simpa only [x,D.symm_apply_apply] using hcInv.2.2.2 (x u) hu.2
  have hinv : D.symm (c (fiberExponential F p (t • u.val))).val = t • u.val := by
    rw [he,c.right_inv hu.2]
    exact D.symm_apply_apply _
  have hm := (hstable _ hu.1 (t • u.val)).mpr hinv.symm
  refine ⟨ht.le,?_⟩
  simpa only [SmoothMetrics.tangentNorm_smul,u.property,mul_one,abs_of_pos ht] using hm.2.symm

/-- The extended supremum is continuous, including at infinite cut time.
For a lower bound use a larger strict interior radius and stability there;
for an upper bound use the strict failure of radial minimality. -/
theorem cut_time_continuous : P202Specs.Geometry.CutPolarDomain.cut_time_continuousType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p E
  letI := directionTopology g p E
  apply continuous_iff_continuousAt.mpr
  intro v
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨t,hat,htc⟩ := exists_between ha
    have htfin : t ≠ ⊤ := ne_top_of_lt htc
    have htpos : 0 < t := lt_of_le_of_lt bot_le hat
    have htr : 0 < t.toReal := ENNReal.toReal_pos (ne_of_gt htpos) htfin
    have htc' : ENNReal.ofReal t.toReal < cutTime g F p v := by
      rwa [ENNReal.ofReal_toReal htfin]
    filter_upwards [nearby_minimizing_time g hn hc C hC R hR F hF p E v htr htc'] with u hu
    have hi := CutTime.cut_time_interval S g hn hc C hC F hF p u
    have hh := ((hi.2.2.2.1 t.toReal).mp hu).2
    rw [ENNReal.ofReal_toReal htfin] at hh
    exact hat.trans_le hh
  · intro b hb
    obtain ⟨a,ha,hb'⟩ := exists_between hb
    have hafin : a ≠ ⊤ := ne_top_of_lt hb'
    have hapos : 0 < a := (CutTime.cut_time_interval S g hn hc C hC F hF p v).2.1.trans ha
    have hta : 0 < a.toReal := ENNReal.toReal_pos (ne_of_gt hapos) hafin
    have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
    have hnot : a.toReal ∉ minimizingTimes g F p v := by
      rw [hi.2.2.2.1,ENNReal.ofReal_toReal hafin]
      exact fun h => (not_le_of_gt ha) h.2
    have hlt : lengthDistance g p (fiberExponential F p (a.toReal • v.val)) < a.toReal := by
      have hle := CompleteExponentialMinimizers.distance_exponential_le_norm g C hC F hF p hi.1 (a.toReal • v.val)
      rw [SmoothMetrics.tangentNorm_smul,v.property,mul_one,abs_of_pos hta] at hle
      exact lt_of_le_of_ne hle (fun h => hnot ⟨hta.le,h⟩)
    have hd : Continuous (fun u : UnitDirection g p =>
        lengthDistance g p (fiberExponential F p (a.toReal • u.val))) :=
      (CompleteExponentialMinimizers.lengthDistance_continuous g).comp
        (continuous_const.prodMk (sphere_exponential_continuous g C F hF p hi.1 E a.toReal))
    have hnear := (isOpen_lt hd continuous_const).mem_nhds hlt
    filter_upwards [hnear] with u hu
    have hiu := CutTime.cut_time_interval S g hn hc C hC F hF p u
    have hcu : cutTime g F p u < a := by
      by_contra h
      have hm := (hiu.2.2.2.1 a.toReal).mpr
        ⟨hta.le,by simpa only [ENNReal.ofReal_toReal hafin] using not_lt.mp h⟩
      exact (ne_of_lt hu) hm.2
    exact hcu.trans hb'

/-- Positive-radius polar coordinates are unique in the original tangent fiber. -/
theorem polar_vector_injective (g : RiemannianMetric S) (p : M)
    {tv su : ℝ × UnitDirection g p} (ht : 0 < tv.1) (hs : 0 < su.1)
    (heq : tv.1 • tv.2.val = su.1 • su.2.val) : tv = su := by
  have hnorm := congrArg (tangentNorm g p) heq
  simp only [SmoothMetrics.tangentNorm_smul,tv.2.property,su.2.property,mul_one,
    abs_of_pos ht,abs_of_pos hs] at hnorm
  apply Prod.ext hnorm
  apply Subtype.ext
  have h := congrArg (fun z : TangentSpace S p => tv.1⁻¹ • z) heq
  rw [← hnorm] at h
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul] using h

/-- A strict interior endpoint cannot be a cut endpoint in another direction. -/
theorem interior_mem_regular [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (tv : ℝ × UnitDirection g p) (htv : tv ∈ polarDomain g F p) :
    polarMap g F p tv ∈ regularDomain g F p := by
  obtain ⟨hm,huniq⟩ := CutCriterion.interior_unique g hn hc C hC F hF p tv.2 htv.1 htv.2
  have hd : lengthDistance g p (polarMap g F p tv) = tv.1 := by
    change lengthDistance g p (fiberExponential F p (tv.1 • tv.2.val)) = tv.1
    rw [← hm.2,SmoothMetrics.tangentNorm_smul,tv.2.property,mul_one,abs_of_pos htv.1]
  have hqp : polarMap g F p tv ≠ p := by
    intro heq
    rw [heq,CompleteExponentialMinimizers.lengthDistance_self] at hd
    linarith [htv.1]
  change ¬ (_ ∨ _)
  rintro (hp | ⟨v,hfin,hv⟩)
  · exact hqp hp
  · have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
    have ht : 0 < (cutTime g F p v).toReal := (hi.2.2.2.2.1 hfin).2.1
    have hmem : (cutTime g F p v).toReal ∈ minimizingTimes g F p v := by
      rw [(hi.2.2.2.2.1 hfin).1]
      exact ⟨ht.le,le_rfl⟩
    have hm' := CutCriterion.radial_minimizing_initial_vector g F p v hmem
    have heq : (cutTime g F p v).toReal • v.val = tv.1 • tv.2.val :=
      huniq _ (by change MinimizingInitialVector g F p (polarMap g F p tv) _; rw [← hv]; exact hm')
    have hpolar := polar_vector_injective g p (tv := ((cutTime g F p v).toReal,v)) (su := tv) ht htv.1 heq
    have hrad := congrArg Prod.fst hpolar
    have hdir := congrArg Prod.snd hpolar
    change v = tv.2 at hdir
    rw [hdir] at hrad
    have hf : ENNReal.ofReal tv.1 = cutTime g F p tv.2 := by
      rw [← hrad,ENNReal.ofReal_toReal (hdir ▸ hfin)]
    exact (ne_of_lt htv.2) hf

/-- Normalize a nonzero actual tangent vector with its metric norm. -/
def normalizedDirection (g : RiemannianMetric S) (p : M)
    (w : TangentSpace S p) (hw : 0 < tangentNorm g p w) : UnitDirection g p :=
  ⟨(tangentNorm g p w)⁻¹ • w,by
    rw [SmoothMetrics.tangentNorm_smul,abs_of_pos (inv_pos.mpr hw)]
    exact inv_mul_cancel₀ (ne_of_gt hw)⟩

theorem norm_smul_normalizedDirection (g : RiemannianMetric S) (p : M)
    (w : TangentSpace S p) (hw : 0 < tangentNorm g p w) :
    tangentNorm g p w • (normalizedDirection g p w hw).val = w := by
  change tangentNorm g p w • ((tangentNorm g p w)⁻¹ • w) = w
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hw),one_smul]

/-- A minimizing vector to a point other than p is nonzero. -/
theorem minimizing_norm_pos
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p q : M) (w : TangentSpace S p) (hqp : q ≠ p)
    (hw : MinimizingInitialVector g F p q w) : 0 < tangentNorm g p w := by
  apply lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p w)
  intro hz
  have hw0 : w = 0 := (SmoothMetrics.tangentNorm_eq_zero_iff g p w).mp hz.symm
  exact hqp (hw.1.symm.trans (hw0 ▸ (ExponentialNormalCoordinates.zero_section_at C F hF p).2))

/-- Every minimizing vector to a regular endpoint is strictly before cut time. -/
theorem regular_minimizing_polar [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p q : M) (hq : q ∈ regularDomain g F p) (w : TangentSpace S p)
    (hw : MinimizingInitialVector g F p q w) :
    ∃ tv ∈ polarDomain g F p, tv.1 • tv.2.val = w ∧ polarMap g F p tv = q := by
  have hqp : q ≠ p := fun h => hq (Or.inl h)
  have hpos := minimizing_norm_pos g C F hF p q w hqp hw
  let v := normalizedDirection g p w hpos
  let t := tangentNorm g p w
  have htw : t • v.val = w := norm_smul_normalizedDirection g p w hpos
  have hm : t ∈ minimizingTimes g F p v := by
    refine ⟨hpos.le,?_⟩
    rw [htw,hw.1]
    exact hw.2.symm
  have hi := CutTime.cut_time_interval S g hn hc C hC F hF p v
  have hle := ((hi.2.2.2.1 t).mp hm).2
  have hlt : ENNReal.ofReal t < cutTime g F p v := by
    apply lt_of_le_of_ne hle
    intro heq
    have hfin : cutTime g F p v ≠ ⊤ := by rw [← heq]; exact ENNReal.ofReal_ne_top
    have hreal : (cutTime g F p v).toReal = t := by
      rw [← heq,ENNReal.toReal_ofReal hpos.le]
    apply hq
    refine Or.inr ⟨v,hfin,?_⟩
    change fiberExponential F p ((cutTime g F p v).toReal • v.val) = q
    rw [hreal,htw,hw.1]
  exact ⟨(t,v),⟨hpos,hlt⟩,htw,by change fiberExponential F p (t • v.val) = q; rw [htw,hw.1]⟩

/-- Global bijection, with all cut endpoints and the basepoint excluded. -/
theorem polar_bijection : P202Specs.Geometry.CutPolarDomain.polar_bijectionType.{u} := by
  intro n M _ _ S g hn hc C hC _R _hR F hF p
  refine ⟨fun tv htv => interior_mem_regular g hn hc C hC F hF p tv htv,?_,?_⟩
  · intro tv htv su hsu heq
    obtain ⟨hm,huniq⟩ := CutCriterion.interior_unique g hn hc C hC F hF p tv.2 htv.1 htv.2
    obtain ⟨hm',_⟩ := CutCriterion.interior_unique g hn hc C hC F hF p su.2 hsu.1 hsu.2
    have hv : su.1 • su.2.val = tv.1 • tv.2.val := huniq _ (by change MinimizingInitialVector g F p (polarMap g F p tv) _; rw [heq]; exact hm')
    exact (polar_vector_injective g p hsu.1 htv.1 hv).symm
  · intro q hq
    obtain ⟨w,hw⟩ := CutCriterion.minimizing_initial_vector_exists g C hC hc F hF p q
    obtain ⟨tv,htv,_,heq⟩ := regular_minimizing_polar g hn hc C hC F hF p q hq w hw
    exact ⟨tv,htv,heq⟩

/-- A metric norm is smooth away from zero in every linear coordinate system. -/
theorem norm_contDiffAt (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (x : Euclidean n)
    (hx : 0 < tangentNorm g p (E.symm x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Euclidean n => tangentNorm g p (E.symm y)) x := by
  let B := ((g.form p).compl₁₂ E.symm.toLinearMap E.symm.toLinearMap).toContinuousBilinearMap
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun y => B y y) := B.contDiff.clm_apply contDiff_id
  have hne : B x x ≠ 0 := by
    change pairing g p (E.symm x) (E.symm x) ≠ 0
    rw [← SmoothMetrics.tangentNorm_sq]
    exact pow_ne_zero _ (ne_of_gt hx)
  exact hB.contDiffAt.sqrt hne

/-- The polar domain is open in the product of the positive-radius line
and the actual unit tangent sphere. -/
theorem polar_domain_open [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    letI := directionTopology g p E
    IsOpen (polarDomain g F p) := by
  letI := directionTopology g p E
  have hc' := cut_time_continuous S g hn hc C hC R hR F hF p E
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (ENNReal.continuous_ofReal.comp continuous_fst) (hc'.comp continuous_snd))

/-- The nonzero tangent vectors strictly before cut time form an open set
in every linear coordinate system. -/
theorem initial_vectors_open [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    IsOpen {x : Euclidean n | ∃ tv ∈ polarDomain g F p, tv.1 • tv.2.val = E.symm x} := by
  letI := directionTopology g p E
  let N : Euclidean n → ℝ := fun x => tangentNorm g p (E.symm x)
  have hN : Continuous N := (CutCriterion.fiber_norm_compact_coordinates g p E).1
  let A := {x : Euclidean n | 0 < N x}
  have hA : IsOpen A := isOpen_lt continuous_const hN
  let f : A → ℝ × UnitDirection g p := fun x =>
    (N x.val,normalizedDirection g p (E.symm x.val) x.property)
  have hf : Continuous f := by
    apply Continuous.prodMk (hN.comp continuous_subtype_val)
    apply continuous_induced_rng.mpr
    have h : Continuous (fun x : A => (N x.val)⁻¹ • x.val) :=
      ((hN.comp continuous_subtype_val).inv₀
        (fun x : A => ne_of_gt x.property)).smul continuous_subtype_val
    simpa only [Function.comp_def,f,normalizedDirection,map_smul,E.apply_symm_apply] using h
  have hB : IsOpen (f ⁻¹' polarDomain g F p) :=
    (polar_domain_open g hn hc C hC R hR F hF p E).preimage hf
  have hEq : {x : Euclidean n | ∃ tv ∈ polarDomain g F p, tv.1 • tv.2.val = E.symm x} =
      Subtype.val '' (f ⁻¹' polarDomain g F p) := by
    ext x
    constructor
    · rintro ⟨tv,htv,hvec⟩
      have hNx : N x = tv.1 := by
        change tangentNorm g p (E.symm x) = tv.1
        rw [← hvec,SmoothMetrics.tangentNorm_smul,tv.2.property,mul_one,abs_of_pos htv.1]
      let a : A := ⟨x,by change 0 < N x; rw [hNx]; exact htv.1⟩
      refine ⟨a,?_,rfl⟩
      have hfa : f a = tv := polar_vector_injective g p a.property htv.1
        ((norm_smul_normalizedDirection g p (E.symm x) a.property).trans hvec.symm)
      change f a ∈ polarDomain g F p
      rwa [hfa]
    · rintro ⟨a,ha,rfl⟩
      exact ⟨f a,ha,norm_smul_normalizedDirection g p (E.symm a.val) a.property⟩
  rw [hEq]
  exact hA.isOpenMap_subtype_val _ hB

/-- Every regular endpoint admits an exponential chart with a whole open
neighborhood inside the regular domain. -/
theorem regular_inverse_chart [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p q : M) (hq : q ∈ regularDomain g F p) :
    ∃ (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (c : ModelChart n .euclidean M) (U : Set M),
      MinimizingInitialVector g F p q w ∧ IsExponentialInverseAt F p w E c ∧
      IsOpen U ∧ q ∈ U ∧ U ⊆ regularDomain g F p ∩ c.source ∧
      ∀ y ∈ U, ∃ tv ∈ polarDomain g F p,
        tv.1 • tv.2.val = E.symm (c y).val ∧ polarMap g F p tv = y := by
  obtain ⟨w,hw⟩ := CutCriterion.minimizing_initial_vector_exists g C hC hc F hF p q
  obtain ⟨tv,htv,htw,htq⟩ := regular_minimizing_polar g hn hc C hC F hF p q hq w hw
  have hbij : Function.Bijective (fiberDifferential S F p w) := by
    rw [← htw]
    exact interior_nonsingular g hn hc C hC R hR F hF p tv.2 htv.1 htv.2
  have hfull : FullExponentialAt F p :=
    (CutTime.cut_time_interval S g hn hc C hC F hF p tv.2).1
  obtain ⟨E,c,hinv⟩ := CutCriterion.exponential_inverse_of_nonsingular C F hF p hfull w hbij
  let V : Set (Euclidean n) := {x | ∃ su ∈ polarDomain g F p, su.1 • su.2.val = E.symm x}
  have hV : IsOpen V := initial_vectors_open g hn hc C hC R hR F hF p E
  let U := c.source ∩ (fun y => (c y).val) ⁻¹' V
  have hU : IsOpen U :=
    (continuous_subtype_val.comp_continuousOn c.continuousOn).isOpen_inter_preimage c.open_source hV
  have hqU : q ∈ U := by
    refine ⟨hw.1 ▸ hinv.2.1,?_⟩
    change (c q).val ∈ V
    refine ⟨tv,htv,?_⟩
    rw [htw,← hw.1,hinv.2.2.1,E.symm_apply_apply]
  have hlocal : ∀ y ∈ U, ∃ su ∈ polarDomain g F p,
      su.1 • su.2.val = E.symm (c y).val ∧ polarMap g F p su = y := by
    intro y hy
    obtain ⟨su,hsu,hvec⟩ := hy.2
    refine ⟨su,hsu,hvec,?_⟩
    change fiberExponential F p (su.1 • su.2.val) = y
    rw [hvec,hinv.2.2.2 (c y) (c.map_source hy.1),c.left_inv hy.1]
  refine ⟨w,E,c,U,hw,hinv,hU,hqU,?_,hlocal⟩
  intro y hy
  obtain ⟨su,hsu,_,hsy⟩ := hlocal y hy
  exact ⟨hsy ▸ interior_mem_regular g hn hc C hC F hF p su hsu,hy.1⟩

/-- The regular domain is open in the original manifold topology. -/
theorem regular_domain_open [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    IsOpen (regularDomain g F p) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨w,E,c,U,_,_,hU,hqU,hsub,_⟩ := regular_inverse_chart g hn hc C hC R hR F hF p q hq
  exact mem_of_superset (hU.mem_nhds hqU) (fun y hy => (hsub hy).1)

/-- The polar bijection and smooth local radius/normalization inverses. -/
theorem polar_diffeomorphism : P202Specs.Geometry.CutPolarDomain.polar_diffeomorphismType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p
  have hb := polar_bijection S g hn hc C hC R hR F hF p
  refine ⟨hb,regular_domain_open g hn hc C hC R hR F hF p,
    polar_domain_open g hn hc C hC R hR F hF p,?_⟩
  intro q hq
  obtain ⟨w,E,c,U,hw,hinv,hU,hqU,hsub,hlocal⟩ := regular_inverse_chart g hn hc C hC R hR F hF p q hq
  refine ⟨w,E,c,U,hw,hinv,hU,hqU,hsub,?_,?_,?_⟩
  · intro y hy tv htv
    obtain ⟨su,hsu,hvec,hsy⟩ := hlocal y hy
    constructor
    · intro hty
      have heq : tv = su := hb.2.1 htv hsu (hty.trans hsy.symm)
      subst tv
      refine ⟨?_,hvec⟩
      rw [← hvec,SmoothMetrics.tangentNorm_smul,su.2.property,mul_one,abs_of_pos hsu.1]
    · rintro ⟨_,htvec⟩
      change fiberExponential F p (tv.1 • tv.2.val) = y
      rw [htvec,hinv.2.2.2 (c y) (c.map_source (hsub hy).2),c.left_inv (hsub hy).2]
  · intro y hy
    obtain ⟨tv,htv,hvec,_⟩ := hlocal y hy
    have hN : 0 < tangentNorm g p (E.symm (c y).val) := by
      rw [← hvec,SmoothMetrics.tangentNorm_smul,tv.2.property,mul_one,abs_of_pos htv.1]
      exact htv.1
    have hnorm := norm_contDiffAt g p E (c y).val hN
    exact ⟨hnorm,hnorm.inv (ne_of_gt hN) |>.smul contDiffAt_id⟩
  · intro d hd x hxd
    have hfull : FullExponentialAt F p :=
      HopfRinow.full_exponential_of_geodesicallyComplete C
        ((HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
    exact ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF p E d hd x (hfull _) hxd

theorem norm_fderiv (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (x y : Euclidean n)
    (hx : 0 < tangentNorm g p (E.symm x)) :
    fderiv ℝ (fun z : Euclidean n => tangentNorm g p (E.symm z)) x y =
      (tangentNorm g p (E.symm x))⁻¹ * pairing g p (E.symm x) (E.symm y) := by
  let B := ((g.form p).compl₁₂ E.symm.toLinearMap E.symm.toLinearMap).toContinuousBilinearMap
  have hne : B x x ≠ 0 := by
    change pairing g p (E.symm x) (E.symm x) ≠ 0
    rw [← SmoothMetrics.tangentNorm_sq]
    exact pow_ne_zero _ (ne_of_gt hx)
  have hd := (B.hasFDerivAt.clm_apply (hasFDerivAt_id x)).sqrt hne
  dsimp only [id_eq] at hd
  change fderiv ℝ (fun z => Real.sqrt (B z z)) x y = _
  rw [hd.fderiv]
  change (1 / (2 * tangentNorm g p (E.symm x))) *
    (pairing g p (E.symm x) (E.symm y) + pairing g p (E.symm y) (E.symm x)) = _
  rw [show pairing g p (E.symm y) (E.symm x) = pairing g p (E.symm x) (E.symm y) from g.symmetric p _ _]
  field_simp
  ring

/-- The distance is the metric norm throughout the open set of regular
minimizing initial vectors. -/
theorem distance_exponential_eq_norm [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w : TangentSpace S p)
    (hw : ∃ tv ∈ polarDomain g F p, tv.1 • tv.2.val = w) :
    lengthDistance g p (fiberExponential F p w) = tangentNorm g p w := by
  obtain ⟨tv,htv,rfl⟩ := hw
  exact (CutCriterion.interior_unique g hn hc C hC F hF p tv.2 htv.1 htv.2).1.2.symm

/-- Smoothness of the distance on precisely the stated open complement. -/
theorem distance_smooth [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p q : M) (hq : q ∈ regularDomain g F p) :
    ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (lengthDistance g p) q := by
  obtain ⟨w,E,c,U,hw,hinv,hU,hqU,hsub,hlocal⟩ := regular_inverse_chart g hn hc C hC R hR F hF p q hq
  let N : Euclidean n → ℝ := fun x => tangentNorm g p (E.symm x)
  let A := {x : Euclidean n | 0 < N x}
  have hA : IsOpen A := isOpen_lt continuous_const (CutCriterion.fiber_norm_compact_coordinates g p E).1
  have hNA : ContDiffOn ℝ (⊤ : ℕ∞) N A :=
    fun x hx => (norm_contDiffAt g p E x hx).contDiffWithinAt
  have hqA : (c q).val ∈ A := by
    change 0 < tangentNorm g p (E.symm (c q).val)
    rw [← hw.1,hinv.2.2.1,E.symm_apply_apply]
    exact minimizing_norm_pos g C F hF p q w (fun h => hq (Or.inl h)) hw
  apply SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 hinv.1 (hsub hqU).2
  refine ⟨A,hA,hqA,N,hNA,?_⟩
  filter_upwards [hU.mem_nhds hqU] with y hy
  obtain ⟨tv,htv,hvec,hsy⟩ := hlocal y hy
  have hm := (CutCriterion.interior_unique g hn hc C hC F hF p tv.2 htv.1 htv.2).1
  change tangentNorm g p (E.symm (c y).val) = lengthDistance g p y
  rw [← hvec]
  exact hm.2.trans (congrArg (lengthDistance g p) hsy)

/-- Transport of the actual differential across an endpoint equality. -/
theorem scalarDerivative_cast (f : M → ℝ) {p q : M} (h : p = q)
    (V : TangentSpace S p) :
    scalarDerivative S f q (castTangent S h V) = scalarDerivative S f p V := by
  subst q
  rfl

/-- Differentiating distance after the exponential on its open regular
initial-vector domain. This uses the scalar chain rule for the genuine
intrinsic velocity of the exponential, not a postulated differential. -/
theorem distance_differential [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 0 < n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (tv : ℝ × UnitDirection g p) (htv : tv ∈ polarDomain g F p)
    (z : TangentSpace S p) :
    scalarDerivative S (lengthDistance g p) (polarMap g F p tv)
      (fiberDifferential S F p (tv.1 • tv.2.val) z) =
      (tangentNorm g p (tv.1 • tv.2.val))⁻¹ * pairing g p (tv.1 • tv.2.val) z := by
  let w := tv.1 • tv.2.val
  let E := selectedCoordinates S p
  have hpos : 0 < tangentNorm g p w := by
    rw [SmoothMetrics.tangentNorm_smul,tv.2.property,mul_one,abs_of_pos htv.1]
    exact htv.1
  have hfull := (CutTime.cut_time_interval S g hn hc C hC F hF p tv.2).1
  have hv : (⟨p,w⟩ : Phase S) ∈ exponentialDomain F := hfull w
  let c : ℝ → M := fun s => fiberExponential F p (w + s • z)
  have h0 : fiberExponential F p w = c 0 := by simp only [c,zero_smul,add_zero]
  have hvel := ExponentialJacobi.fiber_ray_velocity C F hF p w z hv
  have hsm := distance_smooth g hn hc C hC R hR F hF p _ (interior_mem_regular g hn hc C hC F hF p tv htv)
  have hsm0 : VectorSmoothAt S.smoothStructure.val (lengthDistance g p) (c 0) := by
    apply (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    exact h0 ▸ hsm
  have hd := hasDerivWithinAt_univ.mp (CurveCovariantDerivative.scalar_chain hvel (lengthDistance g p) hsm0)
  rw [scalarDerivative_cast] at hd
  have hx : HasDerivAt (fun s : ℝ => E w + s • E z) (E z) 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (E z)).const_add (E w)
  have hnorm := ((norm_contDiffAt g p E (E w) (by simpa only [E.symm_apply_apply] using hpos)).differentiableAt (by simp)).hasFDerivAt
  have hdN := hnorm.comp_hasDerivAt_of_eq (0 : ℝ) hx (by simp)
  rw [norm_fderiv g p E (E w) (E z) (by simpa only [E.symm_apply_apply] using hpos)] at hdN
  simp only [E.symm_apply_apply] at hdN
  have hN : HasDerivAt (fun s : ℝ => tangentNorm g p (w + s • z))
      ((tangentNorm g p w)⁻¹ * pairing g p w z) 0 := by
    simpa only [Function.comp_def,map_add,map_smul,E.symm_apply_apply] using hdN
  have hV := initial_vectors_open g hn hc C hC R hR F hF p E
  have hwV : E w ∈ {x : Euclidean n | ∃ su ∈ polarDomain g F p, su.1 • su.2.val = E.symm x} :=
    ⟨tv,htv,(E.symm_apply_apply w).symm⟩
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∃ su ∈ polarDomain g F p, su.1 • su.2.val = w + s • z := by
    have hxc : Continuous (fun s : ℝ => E w + s • E z) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hwV0 : E w + (0 : ℝ) • E z ∈ {x : Euclidean n | ∃ su ∈ polarDomain g F p, su.1 • su.2.val = E.symm x} := by
      simpa only [zero_smul,add_zero] using hwV
    have he := hxc.continuousAt.preimage_mem_nhds (hV.mem_nhds hwV0)
    change ∀ᶠ s in 𝓝 (0 : ℝ), ∃ su ∈ polarDomain g F p, su.1 • su.2.val = E.symm (E w + s • E z) at he
    simpa only [map_add,map_smul,E.symm_apply_apply] using he
  have heq : (fun s => lengthDistance g p (c s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => tangentNorm g p (w + s • z)) := by
    filter_upwards [hnear] with s hs
    exact distance_exponential_eq_norm g hn hc C hC F hF p _ hs
  exact hd.unique (hN.congr_of_eventuallyEq heq)

/-- Gauss lemma for the canonical intrinsic differential (the source and
target charts here are exactly the charts used by its definition). -/
theorem canonical_gauss
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (w z : TangentSpace S p) (hw : (⟨p,w⟩ : Phase S) ∈ exponentialDomain F) :
    pairing g (fiberExponential F p w) (fiberDifferential S F p w w)
      (fiberDifferential S F p w z) = pairing g p w z := by
  exact GaussLemma.gauss_lemma S g C hC F hF p w hw
    (selectedChart S p).val (selectedChart S p).property.1 (selectedChart S p).property.2
    (selectedChart S (fiberExponential F p w)).val
    (selectedChart S (fiberExponential F p w)).property.1
    (selectedChart S (fiberExponential F p w)).property.2 z

/-- Smooth distance and its unit radial gradient on the regular complement. -/
theorem distance_regular : P202Specs.Geometry.CutPolarDomain.distance_regularType.{u} := by
  intro n M _ _ S g hn hc C hC R hR F hF p q hq
  refine ⟨distance_smooth g hn hc C hC R hR F hF p q hq,?_⟩
  obtain ⟨w,hw⟩ := CutCriterion.minimizing_initial_vector_exists g C hC hc F hF p q
  obtain ⟨tv,htv,htw,htq⟩ := regular_minimizing_polar g hn hc C hC F hF p q hq w hw
  have hu := (CutCriterion.interior_unique g hn hc C hC F hF p tv.2 htv.1 htv.2).2
  have huniq : ∀ z, MinimizingInitialVector g F p q z → z = w := by
    intro z hz
    rw [← htw]
    exact hu z (by change MinimizingInitialVector g F p (polarMap g F p tv) _; rw [htq]; exact hz)
  have hpos := minimizing_norm_pos g C F hF p q w (fun h => hq (Or.inl h)) hw
  have hfull := (CutTime.cut_time_interval S g hn hc C hC F hF p tv.2).1
  have hv : (⟨p,w⟩ : Phase S) ∈ exponentialDomain F := hfull w
  have hnrad : tangentNorm g (fiberExponential F p w) (fiberDifferential S F p w w) = tangentNorm g p w := by
    have hsq := canonical_gauss g C hC F hF p w w hv
    rw [← SmoothMetrics.tangentNorm_sq,← SmoothMetrics.tangentNorm_sq] at hsq
    nlinarith [SmoothMetrics.tangentNorm_nonneg g (fiberExponential F p w) (fiberDifferential S F p w w),
      SmoothMetrics.tangentNorm_nonneg g p w]
  refine ⟨w,hw.1,hw,huniq,?_,?_,?_⟩
  · rw [SmoothMetrics.tangentNorm_smul,abs_of_pos (inv_pos.mpr hpos)]
    have hcast : tangentNorm g q (castTangent S hw.1 (fiberDifferential S F p w w)) =
        tangentNorm g (fiberExponential F p w) (fiberDifferential S F p w w) := by
      generalize hw.1 = h
      cases h
      rfl
    rw [hcast,hnrad,inv_mul_cancel₀ (ne_of_gt hpos)]
  · intro X
    have hbij : Function.Bijective (fiberDifferential S F p w) := by
      rw [← htw]
      exact interior_nonsingular g hn hc C hC R hR F hF p tv.2 htv.1 htv.2
    obtain ⟨z,hz⟩ := hbij.2 ((castTangent S hw.1).symm X)
    have hX : X = castTangent S hw.1 (fiberDifferential S F p w z) := by
      rw [hz,LinearEquiv.apply_symm_apply]
    rw [hX]
    have hpair : pairing g q
        ((tangentNorm g p w)⁻¹ • castTangent S hw.1 (fiberDifferential S F p w w))
        (castTangent S hw.1 (fiberDifferential S F p w z)) =
        (tangentNorm g p w)⁻¹ * pairing g p w z := by
      rw [show pairing g q
        ((tangentNorm g p w)⁻¹ • castTangent S hw.1 (fiberDifferential S F p w w))
        (castTangent S hw.1 (fiberDifferential S F p w z)) =
        (tangentNorm g p w)⁻¹ * pairing g (fiberExponential F p w)
          (fiberDifferential S F p w w) (fiberDifferential S F p w z) by
            generalize hw.1 = h
            cases h
            simp only [castTangent,LinearEquiv.refl_apply,pairing,map_smul,LinearMap.smul_apply,smul_eq_mul]]
      rw [canonical_gauss g C hC F hF p w z hv]
    rw [hpair,scalarDerivative_cast]
    have hd := distance_differential g hn hc C hC R hR F hF p tv htv z
    change scalarDerivative S (lengthDistance g p) (fiberExponential F p (tv.1 • tv.2.val))
      (fiberDifferential S F p (tv.1 • tv.2.val) z) = _ at hd
    rw [htw] at hd
    exact hd.symm
  · refine ⟨(selectedChart S p).val,(selectedChart S p).property.1,
      (selectedChart S p).property.2,
      (selectedChart S (fiberExponential F p w)).val,
      (selectedChart S (fiberExponential F p w)).property.1,
      (selectedChart S (fiberExponential F p w)).property.2,rfl,?_⟩
    exact GaussLemma.fiberDifferential_radial C F hF p w hv
      (selectedChart S p).val (selectedChart S p).property.1 (selectedChart S p).property.2
      (selectedChart S (fiberExponential F p w)).val
      (selectedChart S (fiberExponential F p w)).property.1
      (selectedChart S (fiberExponential F p w)).property.2

theorem cut_polar : P202Specs.Geometry.CutPolarDomain.cut_polarType.{u} :=
  ⟨CutCriterion.finite_cut_criterion,CutCriterion.interior_unique_nonconjugate,
    cut_time_continuous,polar_diffeomorphism,distance_regular⟩

end P202.Geometry.CutPolarDomain
