import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutTime
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HopfRinow
import Mathlib.Topology.Order.Monotone

open scoped ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace P202.Geometry.CutTime
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.CurveData
  P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.CompletenessData P202.CompleteExponentialData
  P202.CutTimeData
open Set
universe u

abbrev UnitDirection := @P202.CutTimeData.UnitDirection
abbrev minimizingTimes := @P202.CutTimeData.minimizingTimes
noncomputable abbrev cutTime := @P202.CutTimeData.cutTime
noncomputable abbrev cutPoint := @P202.CutTimeData.cutPoint
abbrev cutLocus := @P202.CutTimeData.cutLocus
abbrev polarDomain := @P202.CutTimeData.polarDomain

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Completeness supplies the global exponential, with no extra choice
assumptions on the metric manifold. -/
theorem complete_exponential_exists :
    P202Specs.Geometry.CutTime.complete_exponential_existsType.{u} := by
  intro n M _ _ S g hc
  obtain ⟨C,hC,_⟩ := LeviCivita.exists_unique g
  obtain ⟨F,hF⟩ := ExponentialNormalCoordinates.family_exists S C
  refine ⟨C,F,hC,hF,?_⟩
  intro p
  exact HopfRinow.full_exponential_of_geodesicallyComplete C
    ((HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p

/-- A segment of a complete unit radial geodesic has distance at most its
duration. The representative and its length come from the actual geodesic. -/
theorem radial_distance_le (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : UnitDirection g p)
    {a b : ℝ} (hab : a ≤ b) :
    lengthDistance g (fiberExponential F p (a • v.val))
      (fiberExponential F p (b • v.val)) ≤ b-a := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp [CompleteExponentialMinimizers.lengthDistance_self]
  have hI := CompleteExponentialMinimizers.full_interval C F hF p hfull v.val
  have hdom : Icc a b ⊆ (F.interval ⟨p,v.val⟩).carrier := by
    rw [hI]
    exact subset_univ _
  let γ := CompleteExponentialMinimizers.geodesicRepresentative C
    (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩) (hF ⟨p,v.val⟩).2.2.1 hab.le hdom
  have hid (t : ℝ) : fiberExponential F p (t • v.val) = (F.curve ⟨p,v.val⟩ t).1 :=
    (ExponentialNormalCoordinates.radial_identity_at C F hF p v.val t
      (by rw [hI]; trivial)).2
  have hunit : tangentNorm g (F.curve ⟨p,v.val⟩ a).1
      (F.curve ⟨p,v.val⟩ a).2 = 1 := by
    have hs := GeodesicIVP.constant_speed S g C hC (F.interval ⟨p,v.val⟩)
      (F.curve ⟨p,v.val⟩) (hF ⟨p,v.val⟩).2.2.1 a
      (by rw [hI]; trivial) 0 (hF ⟨p,v.val⟩).1
    rw [hs,(hF ⟨p,v.val⟩).2.1]
    exact v.property
  have hL : length g γ = b-a := by
    change (∫ t in a..b, speed g γ t) = _
    rw [GeodesicCriticalityCorners.geodesic_piece_length_of_eqOn g C hC
      (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩)
      (hF ⟨p,v.val⟩).2.2.1 hab hdom γ (fun _ _ => rfl),hunit,one_mul]
  have hd := CompleteExponentialMinimizers.lengthDistance_le_length g γ
  rw [hL] at hd
  change lengthDistance g (F.curve ⟨p,v.val⟩ a).1
    (F.curve ⟨p,v.val⟩ b).1 ≤ b-a at hd
  simpa only [hid] using hd

/-- Every initial segment of a minimizing ray minimizes. -/
theorem minimizingTimes_downward [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M) (hfull : FullExponentialAt F p)
    (v : UnitDirection g p) {s t : ℝ} (hs : s ∈ minimizingTimes g F p v)
    (ht : 0 ≤ t) (hts : t ≤ s) : t ∈ minimizingTimes g F p v := by
  refine ⟨ht,le_antisymm ?_ ?_⟩
  · have h := CompleteExponentialMinimizers.distance_exponential_le_norm
      g C hC F hF p hfull (t • v.val)
    simpa only [SmoothMetrics.tangentNorm_smul,v.property,abs_of_nonneg ht,mul_one] using h
  · have htri := CompleteExponentialMinimizers.lengthDistance_triangle g p
      (fiberExponential F p (t • v.val)) (fiberExponential F p (s • v.val))
    have hseg := radial_distance_le g C hC F hF p hfull v hts
    rw [hs.2] at htri
    linarith

/-- Closedness uses continuity in the original topology, of both the
actual distance and the entire exponential ray. -/
theorem minimizingTimes_closed [PreconnectedSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hfull : FullExponentialAt F p) (v : UnitDirection g p) :
    IsClosed (minimizingTimes g F p v) := by
  have hc : Continuous (fun t : ℝ =>
      lengthDistance g p (fiberExponential F p (t • v.val))) :=
    (CompleteExponentialMinimizers.lengthDistance_continuous g).comp
      (continuous_const.prodMk
        (CompleteExponentialMinimizers.radial_position_continuous C F hF p hfull v.val))
  exact isClosed_Ici.inter (isClosed_eq hc continuous_id)

/-- Local radial minimality gives a genuinely positive equality time. -/
theorem positive_minimizing_time (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ∈ minimizingTimes g F p v := by
  obtain ⟨E,r,R,d,hE,hr,hrR,hd,hmin⟩ :=
    NormalMinimality.normal_minimality S g C hC F hF p
  have hnorm : tangentNorm g p ((r/2) • v.val) = r/2 := by
    rw [SmoothMetrics.tangentNorm_smul,v.property,mul_one,abs_of_pos (by linarith)]
  have hsmall : tangentNorm g p ((r/2) • v.val) < r := by rw [hnorm]; linarith
  obtain ⟨hq,heq⟩ := (hmin ((r/2) • v.val) hsmall).2.1
  refine ⟨r/2,by linarith,by linarith,?_⟩
  change lengthDistance g p (fiberExponential F p ((r/2) • v.val)) = _
  exact heq.trans hnorm

/-- An elementary closed initial interval in the nonnegative real line is
recovered exactly from its extended nonnegative supremum. This handles both
bounded and unbounded rays, without converting infinity to a real endpoint. -/
theorem mem_iff_le_extended_sup {A : Set ℝ} (hclosed : IsClosed A)
    (hzero : (0 : ℝ) ∈ A) (hnonneg : ∀ s ∈ A, 0 ≤ s)
    (hdown : ∀ s ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ s → t ∈ A) (t : ℝ) :
    t ∈ A ↔ 0 ≤ t ∧ ENNReal.ofReal t ≤ sSup (ENNReal.ofReal '' A) := by
  constructor
  · intro ht
    exact ⟨hnonneg t ht,le_sSup (mem_image_of_mem _ ht)⟩
  rintro ⟨ht,hsup⟩
  by_cases hb : BddAbove A
  · have hne : A.Nonempty := ⟨0,hzero⟩
    have hr : sSup A ∈ A := hclosed.csSup_mem hne hb
    have hsup_le : sSup (ENNReal.ofReal '' A) ≤ ENNReal.ofReal (sSup A) := by
      apply sSup_le
      rintro _ ⟨s,hs,rfl⟩
      exact ENNReal.ofReal_le_ofReal (le_csSup hb hs)
    exact hdown _ hr t ht
      ((ENNReal.ofReal_le_ofReal_iff (hnonneg _ hr)).mp (hsup.trans hsup_le))
  · obtain ⟨s,hs,hts⟩ := not_bddAbove_iff.mp hb t
    exact hdown s hs t ht hts.le

/-- The positive closed initial interval assertion, including its finite
endpoint and the separate infinite case. -/
theorem cut_time_interval : P202Specs.Geometry.CutTime.cut_time_intervalType.{u} := by
  intro n M _ _ S g _hn hc C hC F hF p v
  have hfull : FullExponentialAt F p :=
    HopfRinow.full_exponential_of_geodesicallyComplete C
      ((HopfRinow.hopf_rinow S g C hC).1.mp hc) F hF p
  have hclosed := minimizingTimes_closed g C F hF p hfull v
  have hzero : (0 : ℝ) ∈ minimizingTimes g F p v := by
    refine ⟨le_rfl,?_⟩
    rw [zero_smul,(ExponentialNormalCoordinates.zero_section_at C F hF p).2]
    exact CompleteExponentialMinimizers.lengthDistance_self g p
  have hmem (t : ℝ) : t ∈ minimizingTimes g F p v ↔
      0 ≤ t ∧ ENNReal.ofReal t ≤ cutTime g F p v :=
    mem_iff_le_extended_sup hclosed hzero (fun _ hs => hs.1)
      (fun _ hs _ ht hts => minimizingTimes_downward g C hC F hF p hfull v hs ht hts) t
  obtain ⟨ε,hε,hεmem⟩ := positive_minimizing_time g C hC F hF p v
  have hpos : 0 < cutTime g F p v :=
    (ENNReal.ofReal_pos.mpr hε).trans_le ((hmem ε).mp hεmem).2
  refine ⟨hfull,hpos,hclosed,hmem,?_,?_⟩
  · intro hfin
    have hset : minimizingTimes g F p v = Icc 0 (cutTime g F p v).toReal := by
      ext t
      rw [hmem,ENNReal.ofReal_le_iff_le_toReal hfin]
      rfl
    refine ⟨hset,ENNReal.toReal_pos (ne_of_gt hpos) hfin,?_⟩
    have hend : (cutTime g F p v).toReal ∈ minimizingTimes g F p v := by
      rw [hset]
      exact ⟨ENNReal.toReal_nonneg,le_rfl⟩
    exact hend.2
  · intro hinf
    change cutTime g F p v = (⊤ : ℝ≥0∞) at hinf
    ext t
    rw [hmem,hinf]
    simp

end P202.Geometry.CutTime
