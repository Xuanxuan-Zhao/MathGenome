import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.OmegaSection
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.OmegaTopology
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Nullclines
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.MonotoneCrossings
noncomputable section
open Set Filter Metric
open scoped Topology
namespace D13Unified.Ch13.OmegaSection
open Ch06.StateDerivative Ch13.Nullclines Ch13.MonotoneCrossings
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch13.Nullclines
open Specs.D13Unified.Ch13.OmegaSection
open Specs.D13Unified.Ch11.OmegaTopology

lemma segmentPoint_continuous (S : StraightSegment) : Continuous (segmentPointValue S) :=
  continuous_const.add (continuous_id.smul continuous_const)

lemma segmentCarrier_compact (S : StraightSegment) : IsCompact (segmentCarrierValue S) :=
  isCompact_Icc.image (segmentPoint_continuous S)

/-- Local transversality prevents any finite accumulation of actual meetings.
Compactness here concerns only a finite time interval. -/
lemma finite_crossings
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (S : TransverseSegment F)
    (a b : ℝ) (hI : Icc a b ⊆ (flowInterval F x).carrier) :
    {t ∈ Icc a b | flow F t x ∈ segmentCarrierValue S.toStraightSegment}.Finite := by
  let H := {t ∈ Icc a b | flow F t x ∈ segmentCarrierValue S.toStraightSegment}
  have hc := (flow_ivp F hF hx).1.1.continuousOn.mono hI
  have hcompact : IsCompact H := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc
      (segmentCarrier_compact S.toStraightSegment).isClosed) (fun _ ht => ht.1)
  apply hcompact.finite
  apply IsDiscrete.of_nhdsWithin
  intro t ht
  apply le_pure_iff.mpr
  have he := (hlocal F hF x hx S t (hI ht.1) ht.2).mono (fun _ h => h.2.2)
  have he' : ∀ᶠ r in 𝓝 t, r ≠ t → flow F r x ∉ segmentCarrierValue S.toStraightSegment :=
    eventually_nhdsWithin_iff.mp he
  filter_upwards [he'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrH
  by_contra hn
  exact hr hn hrH.2

/-- Any three chronologically ordered meetings have their middle coordinate
between the other two. The finite sorted list retains every intermediate hit. -/
lemma crossing_between
    (hall : Specs.D13Unified.Ch13.MonotoneCrossings.AllIntersections)
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (S : TransverseSegment F) {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (haS : flow F a x ∈ segmentCarrierValue S.toStraightSegment)
    (hbS : flow F b x ∈ segmentCarrierValue S.toStraightSegment)
    (hcS : flow F c x ∈ segmentCarrierValue S.toStraightSegment) :
    let u := fun t => segmentCoordinateValue S.toStraightSegment (flow F t x)
    (u a ≤ u b ∧ u b ≤ u c) ∨ (u c ≤ u b ∧ u b ≤ u a) := by
  classical
  let H := {t ∈ Icc a c | flow F t x ∈ segmentCarrierValue S.toStraightSegment}
  have hH := finite_crossings hlocal F hF x hx S a c
    (fun t ht => hcomplete (ha.trans ht.1))
  let s := hH.toFinset
  let e := s.orderIsoOfFin rfl
  let t : ℕ → ℝ := fun n => if hn : n < s.card then (e ⟨n,hn⟩).val else 0
  have ht (i : Fin s.card) : t i.val = (e i).val := by simp [t]
  have hmem (i : Fin s.card) : (e i).val ∈ H := by
    exact hH.mem_toFinset.mp (e i).property
  have hsucc (n : ℕ) (hn : n+1 ∈ Iio s.card) :
      Successive F S.toStraightSegment x (t n) (t (n+1)) := by
    have hn' : n+1 < s.card := hn
    have hn0 : n < s.card := by omega
    rw [ht ⟨n,hn0⟩, ht ⟨n+1,hn'⟩]
    refine ⟨ha.trans (hmem ⟨n,hn0⟩).1.1,
      e.strictMono (show (⟨n,hn0⟩ : Fin s.card) < ⟨n+1,hn'⟩ from Nat.lt_succ_self n),
      hcomplete (ha.trans (hmem ⟨n,hn0⟩).1.1),
      hcomplete (ha.trans (hmem ⟨n+1,hn'⟩).1.1),
      (hmem ⟨n,hn0⟩).2, (hmem ⟨n+1,hn'⟩).2, ?_⟩
    intro r hr hrS
    have hrH : r ∈ H := ⟨⟨(hmem ⟨n,hn0⟩).1.1.trans hr.1.le,
      hr.2.le.trans (hmem ⟨n+1,hn'⟩).1.2⟩, hrS⟩
    let j := e.symm ⟨r,hH.mem_toFinset.mpr hrH⟩
    have hej : (e j).val = r := by simp [j]
    have hnj : n < j.val := by
      have := e.lt_iff_lt.mp (show e ⟨n,hn0⟩ < e j by change _ < (e j).val; rw [hej]; exact hr.1)
      exact this
    have hjn : j.val < n+1 := by
      have := e.lt_iff_lt.mp (show e j < e ⟨n+1,hn'⟩ by change (e j).val < _; rw [hej]; exact hr.2)
      exact this
    omega
  have haH : a ∈ H := ⟨⟨le_rfl, (hab.trans hbc).le⟩, haS⟩
  have hbH : b ∈ H := ⟨⟨hab.le,hbc.le⟩, hbS⟩
  have hcH : c ∈ H := ⟨⟨(hab.trans hbc).le,le_rfl⟩, hcS⟩
  let i := e.symm ⟨a,hH.mem_toFinset.mpr haH⟩
  let j := e.symm ⟨b,hH.mem_toFinset.mpr hbH⟩
  let k := e.symm ⟨c,hH.mem_toFinset.mpr hcH⟩
  have hti : t i.val = a := by rw [ht]; simp [i]
  have htj : t j.val = b := by rw [ht]; simp [j]
  have htk : t k.val = c := by rw [ht]; simp [k]
  have hij : i.val < j.val := by
    change i < j
    apply e.lt_iff_lt.mp
    change (e i).val < (e j).val
    simpa [i,j] using hab
  have hjk : j.val < k.val := by
    change j < k
    apply e.lt_iff_lt.mp
    change (e j).val < (e k).val
    simpa [j,k] using hbc
  rcases hall F hF x hx S (Iio s.card) (isLowerSet_Iio _) t hsucc with h | h | h
  · have hij' := congrArg (segmentCoordinateValue S.toStraightSegment)
      ((h.1 i.val i.isLt).trans (h.1 j.val j.isLt).symm)
    have hjk' := congrArg (segmentCoordinateValue S.toStraightSegment)
      ((h.1 j.val j.isLt).trans (h.1 k.val k.isLt).symm)
    rw [hti,htj] at hij'
    rw [htj,htk] at hjk'
    exact Or.inl ⟨hij'.le,hjk'.le⟩
  · have h₁ := h i.isLt j.isLt hij
    have h₂ := h j.isLt k.isLt hjk
    dsimp only at h₁ h₂
    rw [hti,htj] at h₁
    rw [htj,htk] at h₂
    exact Or.inl ⟨h₁.le,h₂.le⟩
  · have h₁ := h i.isLt j.isLt hij
    have h₂ := h j.isLt k.isLt hjk
    dsimp only at h₁ h₂
    rw [hti,htj] at h₁
    rw [htj,htk] at h₂
    exact Or.inr ⟨h₂.le,h₁.le⟩


lemma segmentCoordinate_continuous (S : StraightSegment) :
    Continuous (segmentCoordinateValue S) := by
  unfold segmentCoordinateValue
  fun_prop

lemma signedHeight_continuous (S : StraightSegment) :
    Continuous (Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue S) := by
  unfold Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue
  fun_prop

lemma point_of_height_zero (S : StraightSegment) (p : Plane)
    (hh : Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue S p = 0) :
    segmentPointValue S (segmentCoordinateValue S p) = p := by
  have hd : S.direction.1 ^ 2 + S.direction.2 ^ 2 ≠ 0 := by
    intro he
    have h₁ : S.direction.1 = 0 := by nlinarith [sq_nonneg S.direction.2]
    have h₂ : S.direction.2 = 0 := by nlinarith [sq_nonneg S.direction.1]
    exact S.direction_ne_zero (Prod.ext h₁ h₂)
  change S.direction.1 * (p.2 - S.center.2) -
    S.direction.2 * (p.1 - S.center.1) = 0 at hh
  apply Prod.ext
  · change S.center.1 + segmentCoordinateValue S p * S.direction.1 = p.1
    unfold segmentCoordinateValue
    field_simp [hd]
    nlinarith [congrArg (fun t : ℝ => t * S.direction.2) hh]
  · change S.center.2 + segmentCoordinateValue S p * S.direction.2 = p.2
    unfold segmentCoordinateValue
    field_simp [hd]
    nlinarith [congrArg (fun t : ℝ => t * S.direction.1) hh]


/-- A local section projection obtained by the intermediate value theorem.
The elapsed time can be made arbitrarily small. This is the small-time
projection property of a flowbox, established here in the fixed affine section. -/
lemma move_to_section
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (S : TransverseSegment F) (z : Plane)
    (hz : z ∈ sectionInteriorValue S.toStraightSegment)
    (U : Set Plane) (hU : U ∈ 𝓝 z) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 z, ∀ y ∈ V, ∃ s : ℝ,
      |s| < ε ∧ (s,y) ∈ flowDomain F ∧
      flow F s y ∈ U ∩ sectionInteriorValue S.toStraightSegment := by
  have hzS : z ∈ segmentCarrierValue S.toStraightSegment :=
    image_mono Ioo_subset_Icc_self hz
  have hzΩ := S.transverse.1 hzS
  have hz0 := Ch11.Flow.flow_zero F hF z hzΩ
  have hreg := Ch11.Flow.flow_regularity 1 le_rfl F hF
  have hcoord : segmentCoordinateValue S.toStraightSegment z ∈ Ioo (-S.radius) S.radius := by
    obtain ⟨u,hu,rfl⟩ := hz
    rw [coordinate_point S.toStraightSegment u]
    exact hu
  let Q : Plane → ℝ := fun p => normalComponentValue F S.toStraightSegment z *
    Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue S.toStraightSegment p
  have hQc : Continuous Q := continuous_const.mul (signedHeight_continuous _)
  have hc0 : ContinuousAt (fun q : ℝ × Plane => flow F q.1 q.2) (0,z) :=
    (hreg.2.1.contDiffAt (hreg.1.mem_nhds hz0.1)).continuousAt
  have hsmall : ∀ᶠ q : ℝ × Plane in 𝓝 (0,z),
      q ∈ flowDomain F ∧ flow F q.1 q.2 ∈ U ∧
      segmentCoordinateValue S.toStraightSegment (flow F q.1 q.2) ∈
        Ioo (-S.radius) S.radius := by
    have hcu : ∀ᶠ p in 𝓝 z, p ∈ U ∧ segmentCoordinateValue S.toStraightSegment p ∈
        Ioo (-S.radius) S.radius :=
      inter_mem hU ((segmentCoordinate_continuous _).continuousAt (isOpen_Ioo.mem_nhds hcoord))
    have hpull := hc0.eventually (by simpa only [hz0.2] using hcu)
    exact inter_mem (hreg.1.mem_nhds hz0.1) hpull
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hlocal0 := hlocal F hF z hzΩ S 0 hz0.1.2 (by simpa [hz0.2] using hzS)
  have hlocal' : ∀ᶠ r in 𝓝 (0 : ℝ), r ≠ 0 →
      0 < normalComponentValue F S.toStraightSegment z *
        (Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue S.toStraightSegment
          (flow F r z) / r) := by
    have hh := eventually_nhdsWithin_iff.mp hlocal0
    filter_upwards [hh] with r hr hne
    simpa only [hz0.2, sub_zero] using (hr hne).2.1
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hlocal'
  let d := min ε (min ρ δ) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d < ε := by have := min_le_left ε (min ρ δ); dsimp [d]; linarith
  have hdρ : d < ρ := by
    have := (min_le_right ε (min ρ δ)).trans (min_le_left ρ δ)
    dsimp [d]; linarith
  have hdδ : d < δ := by
    have := (min_le_right ε (min ρ δ)).trans (min_le_right ρ δ)
    dsimp [d]; linarith
  have hgood {r : ℝ} {y : Plane} (hr : |r| < ρ) (hy : dist y z < ρ) :=
    hball (show (r,y) ∈ Metric.ball (0,z) ρ by
      rw [Metric.mem_ball, Prod.dist_eq]
      simpa only [Real.dist_eq, sub_zero] using max_lt hr hy)
  have hpQ : 0 < Q (flow F d z) := by
    have hp := hδball (show d ∈ Metric.ball 0 δ by simpa [Real.dist_eq, abs_of_pos hd])
      (ne_of_gt hd)
    rw [← mul_div_assoc] at hp
    exact (div_pos_iff_of_pos_right hd).mp hp
  have hnQ : Q (flow F (-d) z) < 0 := by
    have hn := hδball (show -d ∈ Metric.ball 0 δ by
      simpa [Real.dist_eq, abs_of_pos hd]) (by linarith : -d ≠ 0)
    rw [← mul_div_assoc] at hn
    rcases (div_pos_iff).mp hn with hn | hn <;> dsimp [Q] <;> linarith
  have hc (r : ℝ) (hr : |r| < ρ) : ContinuousAt (fun y => Q (flow F r y)) z :=
    hQc.continuousAt.comp
      ((hreg.2.1.contDiffAt (hreg.1.mem_nhds
        (hgood hr (by simpa using hρ)).1)).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt)
  have hneg : ∀ᶠ y in 𝓝 z, Q (flow F (-d) y) < 0 :=
    (hc (-d) (by simpa [abs_of_pos hd] using hdρ)).eventually (Iio_mem_nhds hnQ)
  have hpos : ∀ᶠ y in 𝓝 z, 0 < Q (flow F d y) :=
    (hc d (by simpa [abs_of_pos hd] using hdρ)).eventually (Ioi_mem_nhds hpQ)
  refine ⟨{y | dist y z < ρ ∧ Q (flow F (-d) y) < 0 ∧ 0 < Q (flow F d y)},
    inter_mem (Metric.ball_mem_nhds z hρ) (hneg.and hpos), ?_⟩
  intro y hy
  have hg (r : ℝ) (hr : r ∈ Icc (-d) d) :=
    hgood ((abs_le.mpr hr).trans_lt hdρ) hy.1
  have hcont : ContinuousOn (fun r => Q (flow F r y)) (Icc (-d) d) :=
    hQc.comp_continuousOn (hreg.2.1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => (hg r hr).1))
  obtain ⟨s,hs,hsQ⟩ := intermediate_value_Icc (show -d ≤ d by linarith) hcont
    (show (0 : ℝ) ∈ Icc (Q (flow F (-d) y)) (Q (flow F d y)) from
      ⟨hy.2.1.le,hy.2.2.le⟩)
  have hsheight : Specs.D13Unified.Ch13.MonotoneCrossings.signedHeightValue
      S.toStraightSegment (flow F s y) = 0 :=
    (mul_eq_zero.mp hsQ).resolve_left (S.transverse.2 z hzS)
  exact ⟨s, (abs_le.mpr hs).trans_lt hdε, (hg s hs).1,
    (hg s hs).2.1, ⟨segmentCoordinateValue S.toStraightSegment (flow F s y),
      (hg s hs).2.2, point_of_height_zero _ _ hsheight⟩⟩


/-- Every omega point in the section is approached by arbitrarily late
actual section meetings. The shift from a late orbit point has the prescribed
arbitrarily small upper bound, and all times remain in the original lifespan. -/
lemma late_section_hit
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (S : TransverseSegment F) (z : Plane)
    (hzω : z ∈ omegaValue F x) (hzS : z ∈ sectionInteriorValue S.toStraightSegment)
    (U : Set Plane) (hU : U ∈ 𝓝 z) (T : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t s : ℝ, 0 ≤ t ∧ |s| < ε ∧ 0 ≤ t+s ∧ T < t+s ∧
      t ∈ (flowInterval F x).carrier ∧ t+s ∈ (flowInterval F x).carrier ∧
      flow F (t+s) x ∈ U ∩ sectionInteriorValue S.toStraightSegment := by
  obtain ⟨V,hV,hmove⟩ := move_to_section hlocal F hF S z hzS U hU ε hε
  obtain ⟨t,ht,htop,hlim⟩ := (Ch11.OmegaTopology.sequence_characterization F x z).mp hzω
  obtain ⟨n,hnV,hnT⟩ := ((hlim.eventually hV).and
    (htop.eventually_gt_atTop (max 0 T + ε))).exists
  obtain ⟨s,hs,hsdom,hsU⟩ := hmove _ hnV
  have hslo : -ε < s := (abs_lt.mp hs).1
  have ht0 : 0 ≤ t n+s := by linarith [le_max_left (0 : ℝ) T]
  have htT : T < t n+s := by linarith [le_max_right (0 : ℝ) T]
  have htime := hcomplete ht0
  have he := (Ch11.Flow.flow_translation F hF x hx (t n) (ht n).1).2 s
    (by simpa only [add_comm s (t n)] using htime)
  refine ⟨t n,s,(ht n).2,hs,ht0,htT,(ht n).1,htime,?_⟩
  simpa only [he,add_comm s (t n)] using hsU

lemma late_hit
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (S : TransverseSegment F) (z : Plane)
    (hzω : z ∈ omegaValue F x) (hzS : z ∈ sectionInteriorValue S.toStraightSegment)
    (U : Set Plane) (hU : U ∈ 𝓝 z) (T : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ T < t ∧
      flow F t x ∈ U ∩ sectionInteriorValue S.toStraightSegment := by
  obtain ⟨t,s,_,_,ht0,htT,_,_,hU⟩ :=
    late_section_hit hlocal F hF x hx hcomplete S z hzω hzS U hU T 1 zero_lt_one
  exact ⟨t+s,ht0,htT,hU⟩

/-- Late orbit points can be moved onto the section with shifts tending to
zero. Both the original times and shifted times tend to infinity. -/
lemma late_section_sequence
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (S : TransverseSegment F) (z : Plane)
    (hzω : z ∈ omegaValue F x) (hzS : z ∈ sectionInteriorValue S.toStraightSegment) :
    ∃ t s : ℕ → ℝ,
      (∀ n, t n ∈ (flowInterval F x).carrier ∧
        t n+s n ∈ (flowInterval F x).carrier ∧
        flow F (t n+s n) x ∈ sectionInteriorValue S.toStraightSegment) ∧
      Tendsto t atTop atTop ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n => t n+s n) atTop atTop ∧
      Tendsto (fun n => flow F (t n+s n) x) atTop (𝓝 z) := by
  have hex (n : ℕ) := late_section_hit hlocal F hF x hx hcomplete S z hzω hzS
    (Metric.ball z (1 / ((n : ℝ)+1))) (Metric.ball_mem_nhds z (by positivity))
    ((n : ℝ)+1) (1 / ((n : ℝ)+1)) (by positivity)
  choose t s ht using hex
  have hbound : Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsbound (n : ℕ) : |s n| ≤ 1 / ((n : ℝ)+1) := (ht n).2.1.le
  have hshift (n : ℕ) : (n : ℝ) ≤ t n+s n := by linarith [(ht n).2.2.2.1]
  have htime (n : ℕ) : (n : ℝ) ≤ t n := by
    have he : 1 / ((n : ℝ)+1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hs : s n ≤ 1 := (le_abs_self _).trans ((hsbound n).trans he)
    linarith [(ht n).2.2.2.1]
  refine ⟨t,s,?_,tendsto_atTop_mono htime tendsto_natCast_atTop_atTop,?_,
    tendsto_atTop_mono hshift tendsto_natCast_atTop_atTop,?_⟩
  · intro n
    exact ⟨(ht n).2.2.2.2.1, (ht n).2.2.2.2.2.1, (ht n).2.2.2.2.2.2.2⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using
      squeeze_zero (fun n => abs_nonneg (s n)) hsbound hbound
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => (ht n).2.2.2.2.2.2.1.le) hbound

/-- The two-sequence limit argument is expressed by three alternating late
meetings on opposite sides of a coordinate threshold. -/
lemma omega_coordinates_equal
    (hall : Specs.D13Unified.Ch13.MonotoneCrossings.AllIntersections)
    (hlocal : Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing)
    (F : AutonomousODE Plane) (hF : ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain)
    (x : Plane) (hx : x ∈ F.domain) (hcomplete : Ici 0 ⊆ (flowInterval F x).carrier)
    (S : TransverseSegment F) {z w : Plane}
    (hzω : z ∈ omegaValue F x) (hzS : z ∈ sectionInteriorValue S.toStraightSegment)
    (hwω : w ∈ omegaValue F x) (hwS : w ∈ sectionInteriorValue S.toStraightSegment) :
    segmentCoordinateValue S.toStraightSegment z =
      segmentCoordinateValue S.toStraightSegment w := by
  suffices h : ∀ z w : Plane, z ∈ omegaValue F x →
      z ∈ sectionInteriorValue S.toStraightSegment → w ∈ omegaValue F x →
      w ∈ sectionInteriorValue S.toStraightSegment →
      ¬ segmentCoordinateValue S.toStraightSegment z <
        segmentCoordinateValue S.toStraightSegment w by
    exact le_antisymm (le_of_not_gt (h w z hwω hwS hzω hzS))
      (le_of_not_gt (h z w hzω hzS hwω hwS))
  intro z w hzω hzS hwω hwS hzw
  let u := segmentCoordinateValue S.toStraightSegment
  let m := (u z + u w) / 2
  have hzm : u z < m := by dsimp [m,u]; linarith
  have hmw : m < u w := by dsimp [m,u]; linarith
  have hlow : {y | u y < m} ∈ 𝓝 z :=
    (segmentCoordinate_continuous _).continuousAt (Iio_mem_nhds hzm)
  have hhigh : {y | m < u y} ∈ 𝓝 w :=
    (segmentCoordinate_continuous _).continuousAt (Ioi_mem_nhds hmw)
  obtain ⟨a,ha,_,haU⟩ := late_hit hlocal F hF x hx hcomplete S z hzω hzS _ hlow 0
  obtain ⟨b,_,hab,hbU⟩ := late_hit hlocal F hF x hx hcomplete S w hwω hwS _ hhigh a
  obtain ⟨c,_,hbc,hcU⟩ := late_hit hlocal F hF x hx hcomplete S z hzω hzS _ hlow b
  have habc := crossing_between hall hlocal F hF x hx hcomplete S ha hab hbc
    (image_mono Ioo_subset_Icc_self haU.2)
    (image_mono Ioo_subset_Icc_self hbU.2)
    (image_mono Ioo_subset_Icc_self hcU.2)
  have h₁ : u (flow F a x) < m := haU.1
  have h₂ : m < u (flow F b x) := hbU.1
  have h₃ : u (flow F c x) < m := hcU.1
  rcases habc with habc | habc
  · exact (not_lt_of_ge habc.2) (h₃.trans h₂)
  · exact (not_lt_of_ge habc.2) (h₁.trans h₂)


/-- Conditional draft only. Every frozen premise is retained, in the supplied
order; the original closed target is reserved for genuine dependency closure. -/
theorem omega_section_conditional :
    Specs.D13Unified.Ch13.MonotoneCrossings.AllIntersections →
    Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing →
    Specs.D13Unified.Ch13.MonotoneCrossings.MonotoneIntersections →
    Specs.D13Unified.Ch13.MonotoneCrossings.RepeatedIntersection →
    Specs.D13Unified.Ch13.MonotoneCrossings.SuccessiveOrder →
    Specs.D13Unified.Ch13.OmegaSection.OmegaSection := by
  intro hall hlocal _hmonotone _hrepeated _horder F hF x hx hcomplete S z hz w hw
  have hcoord := omega_coordinates_equal hall hlocal F hF x hx hcomplete S
    hz.1 hz.2 hw.1 hw.2
  obtain ⟨u,hu,he⟩ := hz.2
  obtain ⟨v,hv,he'⟩ := hw.2
  rw [← he, ← he', coordinate_point S.toStraightSegment u,
    coordinate_point S.toStraightSegment v] at hcoord
  exact he.symm.trans ((congrArg (segmentPointValue S.toStraightSegment) hcoord).trans he')

theorem regular_section_conditional :
    Specs.D13Unified.Ch13.MonotoneCrossings.AllIntersections →
    Specs.D13Unified.Ch13.MonotoneCrossings.LocalCrossing →
    Specs.D13Unified.Ch13.MonotoneCrossings.MonotoneIntersections →
    Specs.D13Unified.Ch13.MonotoneCrossings.RepeatedIntersection →
    Specs.D13Unified.Ch13.MonotoneCrossings.SuccessiveOrder →
    Specs.D13Unified.Ch13.OmegaSection.RegularSection := by
  intro hall hlocal hmonotone hrepeated horder F hF x hx hcomplete p hp hregular R hR
  obtain ⟨S,hcenter,hradius⟩ := small_transverse_segment F hF p hp hregular R hR
  have hunique := omega_section_conditional hall hlocal hmonotone hrepeated horder
    F hF x hx hcomplete S
  refine ⟨S,hcenter,hradius,hunique,?_⟩
  intro hpω
  have hpS : p ∈ sectionInteriorValue S.toStraightSegment := by
    refine ⟨0,⟨by linarith [S.radius_pos],S.radius_pos⟩,?_⟩
    simp [segmentPointValue,hcenter]
  apply Set.Subset.antisymm
  · intro y hy
    exact Set.mem_singleton_iff.mpr (hunique hy ⟨hpω,hpS⟩)
  · intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ⟨hpω,hpS⟩

end D13Unified.Ch13.OmegaSection

theorem _root_.«D13Unified».«Ch13».«OmegaSection».«omega_section» : _root_.«Specs».«D13Unified».«Ch13».«OmegaSection».«OmegaSection» :=
  @_root_.«D13Unified».«Ch13».«OmegaSection».«omega_section_conditional» (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«all_intersections») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«local_crossing») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«monotone_intersections») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«repeated_intersection») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«successive_order»)
theorem _root_.«D13Unified».«Ch13».«OmegaSection».«regular_section» : _root_.«Specs».«D13Unified».«Ch13».«OmegaSection».«RegularSection» :=
  @_root_.«D13Unified».«Ch13».«OmegaSection».«regular_section_conditional» (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«all_intersections») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«local_crossing») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«monotone_intersections») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«repeated_intersection») (@_root_.«D13Unified».«Ch13».«MonotoneCrossings».«successive_order»)
