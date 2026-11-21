import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.SectionDecay
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Geometric section contraction, compact control of return arcs, and
concatenation on actual maximal domains, including the real-time decay rate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.SectionDecay
open Ch06.StateDerivative
open Specs.D13Unified.Ch14.ReturnMap
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] lemma cumulativeTime_zero {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (v : ℓ.ker) :
    cumulativeTime d v 0 = 0 := by simp [cumulativeTime]

lemma cumulativeTime_succ {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (v : ℓ.ker) (j : ℕ) :
    cumulativeTime d v (j+1) = cumulativeTime d v j +
      d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v) := by
  simp [cumulativeTime, Finset.sum_range_succ]

/-- Continuity of the actual return branch allows the quantitative time
window to be imposed on a smaller open section neighborhood. -/
lemma return_time_window {k : ℕ} (_hk : 1 ≤ k) {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (hT : 0 < T) :
    ∃ V : Set ℓ.ker, IsOpen V ∧ (0 : ℓ.ker) ∈ V ∧ V ⊆ d.P.source ∧
      ∀ v ∈ V, T/2 < d.τ v ∧ d.τ v < 3*T/2 := by
  have hc : ContinuousAt d.τ 0 := d.time_regular.continuousOn.continuousAt
    (d.P.open_source.mem_nhds d.source_zero)
  have hmem : d.τ 0 ∈ Ioo (T/2) (3*T/2) := by rw [d.time_zero]; constructor <;> linarith
  have hn := hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
  obtain ⟨V,hV,hVo,h0⟩ := mem_nhds_iff.mp (inter_mem hn
    (d.P.open_source.mem_nhds d.source_zero))
  exact ⟨V,hVo,h0,fun _ hv => (hV hv).2, fun _ hv => (hV hv).1⟩

lemma iterate_mem {S : Type*} {P : S → S} {U : Set S} (hU : MapsTo P U U)
    {v : S} (hv : v ∈ U) (j : ℕ) : P^[j] v ∈ U := by
  induction j with
  | zero => exact hv
  | succ j ih => simpa only [Function.iterate_succ_apply'] using hU ih

/-- Both bounds are non-strict because the zeroth cumulative time is zero. -/
lemma cumulativeTime_bounds {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    {U : Set ℓ.ker} (hU : MapsTo d.P U U)
    (htime : ∀ w ∈ U, T/2 < d.τ w ∧ d.τ w < 3*T/2)
    {v : ℓ.ker} (hv : v ∈ U) (j : ℕ) :
    (j : ℝ) * (T/2) ≤ cumulativeTime d v j ∧
      cumulativeTime d v j ≤ (j : ℝ) * (3*T/2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cumulativeTime_succ]
    have h := htime _ (iterate_mem hU hv j)
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, h.1, h.2]

lemma cumulativeTime_tendsto {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (hT : 0 < T)
    {U : Set ℓ.ker} (hU : MapsTo d.P U U)
    (htime : ∀ w ∈ U, T/2 < d.τ w ∧ d.τ w < 3*T/2)
    {v : ℓ.ker} (hv : v ∈ U) : Tendsto (cumulativeTime d v) atTop atTop := by
  apply tendsto_atTop_mono (fun j => (cumulativeTime_bounds d hU htime hv j).1)
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by linarith : 0 < T/2)

/-- Every nonnegative real time lies on one of the successive return arcs.
No assumption of forward completeness is used. -/
lemma exists_return_arc {k : ℕ} {F : AutonomousODE E} {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (hT : 0 < T)
    {U : Set ℓ.ker} (hU : MapsTo d.P U U)
    (htime : ∀ w ∈ U, T/2 < d.τ w ∧ d.τ w < 3*T/2)
    {v : ℓ.ker} (hv : v ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, cumulativeTime d v j ≤ t ∧ t < cumulativeTime d v (j+1) := by
  have hex : ∃ n : ℕ, t < cumulativeTime d v n :=
    ((cumulativeTime_tendsto d hT hU htime hv).eventually
      (eventually_gt_atTop t)).exists
  let n := Nat.find hex
  have hn : t < cumulativeTime d v n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by intro he; simp [he, not_lt_of_ge ht] at hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨j, ?_, by simpa only [hj] using hn⟩
  have hjn : j < Nat.find hex := by change j < n; omega
  exact le_of_not_gt (Nat.find_min hex hjn)

section Flow
variable [FiniteDimensional ℝ E]

/-- Inductively rebase the canonical maximal trajectory at each return.
This proves existence at every node as well as the value there. -/
lemma return_nodes {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    {U : Set ℓ.ker} (hsrc : U ⊆ d.P.source) (hU : MapsTo d.P U U)
    {v : ℓ.ker} (hv : v ∈ U) (j : ℕ) :
    (cumulativeTime d v j, p + (v : E)) ∈ flowDomain F ∧
      flow F (cumulativeTime d v j) (p + (v : E)) =
        p + ((d.P : ℓ.ker → ℓ.ker)^[j] v : E) := by
  have hpv := d.section_domain v (d.source_section (hsrc hv))
  induction j with
  | zero => simpa using Ch11.Flow.flow_zero F hF _ hpv
  | succ j ih =>
    have hz := hsrc (iterate_mem hU hv j)
    have ht := d.time_near _ hz
    have hτ : d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v) ∈ Icc 0 (T + d.δ) :=
      ⟨le_of_lt (d.time_positive _ hz), le_of_lt ht.2⟩
    have hdom := d.flow_domain _ hz _ hτ
    have htrans := Ch11.Flow.flow_translation F hF _ hpv _ ih.1.2
    rw [ih.2] at htrans
    have hsum : d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v) + cumulativeTime d v j ∈
        (flowInterval F (p + (v : E))).carrier := by
      have hh := hdom.2
      rw [htrans.1] at hh
      exact hh
    constructor
    · exact ⟨hpv, by simpa only [cumulativeTime_succ, add_comm] using hsum⟩
    · rw [cumulativeTime_succ, add_comm, ← htrans.2 _ hsum, d.map_formula _ hz]
      simp only [Function.iterate_succ_apply']

/-- A whole return segment is admissible on the original maximal interval;
its value agrees with the segment based at the corresponding section point. -/
lemma return_arc {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ)
    {U : Set ℓ.ker} (hsrc : U ⊆ d.P.source) (hU : MapsTo d.P U U)
    {v : ℓ.ker} (hv : v ∈ U) (j : ℕ)
    {s : ℝ} (hs : s ∈ Icc 0 (d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v))) :
    (cumulativeTime d v j + s, p + (v : E)) ∈ flowDomain F ∧
      flow F (cumulativeTime d v j + s) (p + (v : E)) =
        flow F s (p + ((d.P : ℓ.ker → ℓ.ker)^[j] v : E)) := by
  have hz := hsrc (iterate_mem hU hv j)
  have hdom := d.flow_domain _ hz s ⟨hs.1, hs.2.trans (d.time_near _ hz).2.le⟩
  have hn := return_nodes hF d hsrc hU hv j
  have htrans := Ch11.Flow.flow_translation F hF _ hn.1.1 _ hn.1.2
  rw [hn.2] at htrans
  have hsum : s + cumulativeTime d v j ∈ (flowInterval F (p + (v : E))).carrier := by
    have hh := hdom.2
    rw [htrans.1] at hh
    exact hh
  exact ⟨⟨hn.1.1, by simpa only [add_comm] using hsum⟩,
    by simpa only [add_comm] using (htrans.2 s hsum).symm⟩

/-- Divergence of return times and exact domain rebasing rule out a finite
forward endpoint. Thus the concatenated solution is the actual maximal flow. -/
lemma forward_existence {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (hT : 0 < T)
    {U : Set ℓ.ker} (hsrc : U ⊆ d.P.source) (hU : MapsTo d.P U U)
    (htime : ∀ w ∈ U, T/2 < d.τ w ∧ d.τ w < 3*T/2)
    {v : ℓ.ker} (hv : v ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    (t, p + (v : E)) ∈ flowDomain F := by
  obtain ⟨j,hj,hj'⟩ := exists_return_arc d hT hU htime hv ht
  have hs : t - cumulativeTime d v j ∈
      Icc 0 (d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v)) := by
    rw [cumulativeTime_succ] at hj'
    constructor <;> linarith
  have h := (return_arc hF d hsrc hU hv j hs).1
  simpa only [add_sub_cancel] using h

end Flow

section CompactArcs
variable [FiniteDimensional ℝ E]

/-- The compact period trace is exactly the shared maximal orbit object. -/
lemma orbit_eq_period_trace (F : AutonomousODE E) (p : E) (T : ℝ) (hT : 0 < T)
    (hc : Ch11.Orbits.IsComplete F p)
    (hper : Function.Periodic (fun t => flow F t p) T) :
    Ch11.Orbits.orbit F p = (flow F · p) '' Icc 0 T := by
  change (flow F · p) '' (flowInterval F p).carrier = _
  apply Subset.antisymm
  · rintro _ ⟨t,ht,rfl⟩
    obtain ⟨s,hs,he⟩ := hper.exists_mem_Ico₀ hT t
    exact ⟨s,⟨hs.1,hs.2.le⟩,he.symm⟩
  · apply image_mono
    rw [hc]
    exact subset_univ _

/-- Uniform differentiable control during one entire return. The compact
confining set is a neighborhood of the whole periodic orbit inside Ω. -/
lemma compact_return_arcs {k : ℕ} {F : AutonomousODE E}
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} {T : ℝ}
    {ℓ : E →L[ℝ] ℝ} (d : FirstReturnData k F p T ℓ) (_hT : 0 < T)
    (hper : Function.Periodic (fun t => flow F t p) T) :
    ∃ V : Set ℓ.ker, IsOpen V ∧ (0 : ℓ.ker) ∈ V ∧ V ⊆ d.P.source ∧
      ∃ L : ℝ, 0 < L ∧ ∃ K : Set E, IsCompact K ∧
        (flow F · p) '' Icc 0 T ⊆ interior K ∧ K ⊆ F.domain ∧
        ∀ v ∈ V, ∀ s ∈ Icc 0 (d.τ v),
          flow F s (p + (v : E)) ∈ K ∧
          Metric.infDist (flow F s (p + (v : E))) ((flow F · p) '' Icc 0 T) ≤ L * ‖v‖ := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (d.P.open_source.mem_nhds d.source_zero)
  let B : Set ℓ.ker := Metric.closedBall 0 (r/2)
  have hBsub : B ⊆ d.P.source := by
    intro v hv
    apply hrsub
    exact lt_of_le_of_lt (show dist v 0 ≤ r/2 from hv) (by linarith)
  have h0B : (0 : ℓ.ker) ∈ B := Metric.mem_closedBall_self (by positivity)
  let Q : Set (ℝ × ℓ.ker) := Icc 0 (T + d.δ) ×ˢ B
  let G : ℝ × ℓ.ker → E := fun q => flow F q.1 (p + (q.2 : E))
  have hdom : ∀ q ∈ Q, (q.1, p + (q.2 : E)) ∈ flowDomain F := by
    intro q hq
    exact d.flow_domain _ (hBsub hq.2) _ hq.1
  have hreg := Ch11.Flow.flow_regularity 1 (by omega) F hF
  have hG : ContDiffOn ℝ 1 G Q := by
    exact hreg.2.1.comp (contDiffOn_fst.prodMk
      (contDiffOn_const.add (ℓ.ker.subtypeL.contDiff.comp_contDiffOn contDiffOn_snd))) hdom
  have hQc : IsCompact Q := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨L,hL⟩ := hG.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc (0 : ℝ) (T + d.δ)).prod (convex_closedBall (0 : ℓ.ker) (r/2))) hQc
  have hΓsub : (flow F · p) '' Icc 0 T ⊆ G '' Q := by
    rintro _ ⟨s,hs,rfl⟩
    refine ⟨(s,0), ⟨⟨hs.1,by linarith [hs.2,d.δ_pos]⟩,h0B⟩,?_⟩
    simp [G]
  have hKc : IsCompact (G '' Q) := hQc.image_of_continuousOn hG.continuousOn
  have hKdom : G '' Q ⊆ F.domain := by
    rintro _ ⟨q,hq,rfl⟩
    exact hreg.2.2 _ (hdom q hq)
  obtain ⟨K,hKc',hKint,hKsub⟩ := exists_compact_between hKc F.isOpen_domain hKdom
  refine ⟨Metric.ball 0 (r/2), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    (fun v hv => hBsub (Metric.ball_subset_closedBall hv)),
    (L : ℝ) + 1, by positivity, K,hKc',hΓsub.trans hKint,hKsub,?_⟩
  intro v hv s hs
  have hvB : v ∈ B := Metric.ball_subset_closedBall hv
  have hvsrc := hBsub hvB
  have hsQ : (s,v) ∈ Q := ⟨⟨hs.1,hs.2.trans (d.time_near v hvsrc).2.le⟩,hvB⟩
  have hs0Q : (s,(0 : ℓ.ker)) ∈ Q := ⟨hsQ.1,h0B⟩
  have hdist : dist (flow F s (p + (v : E))) (flow F s p) ≤ (L : ℝ) * ‖v‖ := by
    simpa only [G, zero_add, add_zero, ZeroMemClass.coe_zero,
      Prod.dist_eq, dist_self, zero_max, dist_zero_right, max_eq_right (norm_nonneg v)] using
        hL.dist_le_mul (s,v) hsQ (s,0) hs0Q
  have hsΓ : flow F s p ∈ (flow F · p) '' Icc 0 T := by
    by_cases hsT : s ≤ T
    · exact ⟨s,⟨hs.1,hsT⟩,rfl⟩
    · refine ⟨s-T,⟨by linarith,?_⟩,?_⟩
      · have ht := (d.time_near v hvsrc).2
        linarith [d.δ_lt_period, hs.2]
      · simpa only [sub_add_cancel] using (hper (s-T)).symm
  exact ⟨interior_subset (hKint (mem_image_of_mem G hsQ)),
    (Metric.infDist_le_dist_of_mem hsΓ).trans
      (hdist.trans (by nlinarith [norm_nonneg v]))⟩

end CompactArcs

/-- Quantitative conversion on a full return arc. The factor θ⁻¹ is needed
because t may be near the end of the j-th arc, rather than at its start. -/
lemma geometric_to_exponential {θ b : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hb : 0 < b)
    {j : ℕ} {t : ℝ} (ht : t ≤ (j + 1 : ℝ) * b) :
    θ ^ j ≤ θ⁻¹ * Real.exp (-(-Real.log θ / b) * t) := by
  have hlog := Real.log_neg hθ hθ1
  have hmul := mul_le_mul_of_nonpos_left ht (le_of_lt hlog)
  have hexp : ((j : ℝ) + 1) * Real.log θ ≤ -(-Real.log θ / b) * t := by
    have hmul' : (((j : ℝ) + 1) * Real.log θ) * b ≤ Real.log θ * t := by
      nlinarith only [hmul]
    have hdiv := (le_div_iff₀ hb).mpr hmul'
    convert hdiv using 1; field_simp
  have he := Real.exp_le_exp.mpr hexp
  have heq : Real.exp (((j : ℝ) + 1) * Real.log θ) = θ ^ j * θ := by
    rw [add_mul, Real.exp_add, Real.exp_nat_mul, one_mul, Real.exp_log hθ]
  rw [heq] at he
  calc
    θ ^ j = θ⁻¹ * (θ ^ j * θ) := by field_simp
    _ ≤ θ⁻¹ * Real.exp (-(-Real.log θ / b) * t) := mul_le_mul_of_nonneg_left he (by positivity)

section Discrete
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An adapted size using a supremum, rather than a series. -/
def adaptedSize (B : V →L[ℝ] V) (β : ℝ) (v : V) : ℝ :=
  ⨆ j : ℕ, β⁻¹ ^ j * ‖(B ^ j) v‖

lemma weighted_power_bound (B : V →L[ℝ] V) {C r β : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrβ : r < β)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖)
    (j : ℕ) (v : V) : β⁻¹ ^ j * ‖(B ^ j) v‖ ≤ C * ‖v‖ := by
  have hβ : 0 < β := lt_of_le_of_lt hr hrβ
  calc
    β⁻¹ ^ j * ‖(B ^ j) v‖ ≤ β⁻¹ ^ j * (C * r ^ j * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hpow j v) (by positivity)
    _ = C * (r/β) ^ j * ‖v‖ := by rw [div_eq_mul_inv,mul_pow]; ring
    _ ≤ C * 1 * ‖v‖ := by
      gcongr
      exact pow_le_one₀ (by positivity) (le_of_lt ((div_lt_one hβ).mpr hrβ))
    _ = C * ‖v‖ := by ring

lemma adaptedSize_bounds (B : V →L[ℝ] V) {C r β : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrβ : r < β)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖) (v : V) :
    ‖v‖ ≤ adaptedSize B β v ∧ adaptedSize B β v ≤ C * ‖v‖ := by
  have hbd : BddAbove (Set.range (fun j : ℕ => β⁻¹ ^ j * ‖(B ^ j) v‖)) :=
    ⟨C * ‖v‖, by rintro _ ⟨j,rfl⟩; exact weighted_power_bound B hC hr hrβ hpow j v⟩
  constructor
  · simpa only [adaptedSize,pow_zero,one_mul,one_apply_eq_self] using le_ciSup hbd 0
  · exact ciSup_le (fun j => weighted_power_bound B hC hr hrβ hpow j v)

lemma adaptedSize_add_bound (B : V →L[ℝ] V) {C r β : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrβ : r < β)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖) (v w : V) :
    adaptedSize B β v ≤ adaptedSize B β w + C * ‖v-w‖ := by
  have hβ : 0 < β := lt_of_le_of_lt hr hrβ
  have hbd : BddAbove (Set.range (fun j : ℕ => β⁻¹ ^ j * ‖(B ^ j) w‖)) :=
    ⟨C * ‖w‖, by rintro _ ⟨j,rfl⟩; exact weighted_power_bound B hC hr hrβ hpow j w⟩
  apply ciSup_le
  intro j
  calc
    β⁻¹ ^ j * ‖(B ^ j) v‖ ≤
        β⁻¹ ^ j * (‖(B ^ j) w‖ + ‖(B ^ j) (v-w)‖) := by
      gcongr
      have he : (B^j) v = (B^j) w + (B^j) (v-w) := by simp
      rw [he]
      exact norm_add_le _ _
    _ = β⁻¹ ^ j * ‖(B ^ j) w‖ + β⁻¹ ^ j * ‖(B ^ j) (v-w)‖ := by ring
    _ ≤ adaptedSize B β w + C * ‖v-w‖ :=
      add_le_add (le_ciSup hbd j) (weighted_power_bound B hC hr hrβ hpow j (v-w))

lemma continuous_adaptedSize (B : V →L[ℝ] V) {C r β : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrβ : r < β)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖) :
    Continuous (adaptedSize B β) := by
  apply LipschitzWith.continuous (K := ⟨C,hC⟩)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change dist (adaptedSize B β v) (adaptedSize B β w) ≤ C * dist v w
  rw [Real.dist_eq, abs_le, dist_eq_norm]
  constructor
  · have h := adaptedSize_add_bound B hC hr hrβ hpow w v
    rw [norm_sub_rev w v] at h
    linarith
  · have h := adaptedSize_add_bound B hC hr hrβ hpow v w
    linarith

lemma adaptedSize_linear_step (B : V →L[ℝ] V) {C r β : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrβ : r < β)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖) (v : V) :
    adaptedSize B β (B v) ≤ β * adaptedSize B β v := by
  have hβ : 0 < β := lt_of_le_of_lt hr hrβ
  have hbd : BddAbove (Set.range (fun j : ℕ => β⁻¹ ^ j * ‖(B ^ j) v‖)) :=
    ⟨C * ‖v‖, by rintro _ ⟨j,rfl⟩; exact weighted_power_bound B hC hr hrβ hpow j v⟩
  apply ciSup_le
  intro j
  calc
    β⁻¹ ^ j * ‖(B ^ j) (B v)‖ = β * (β⁻¹ ^ (j+1) * ‖(B ^ (j+1)) v‖) := by
      rw [pow_succ B, mul_apply_eq_comp, pow_succ]
      field_simp
    _ ≤ β * adaptedSize B β v := mul_le_mul_of_nonneg_left (le_ciSup hbd (j+1)) hβ.le

/-- A power estimate for the derivative implies nonlinear geometric decay on
an invariant open neighborhood, inside any prescribed neighborhood. -/
lemma discrete_decay_of_power_bound {P : V → V} (hP0 : P 0 = 0)
    (B : V →L[ℝ] V) (hP : HasFDerivAt P B 0) {C r : ℝ}
    (hC : 1 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hpow : ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖)
    {W : Set V} (hW : W ∈ 𝓝 0) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧ U ⊆ W ∧ MapsTo P U U ∧
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        ∀ v ∈ U, ∀ j : ℕ, ‖P^[j] v‖ ≤ C * θ ^ j * ‖v‖ := by
  let β := (r+1)/2
  let θ := (β+1)/2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hrβ : r < β := by dsimp [β]; linarith
  have hβθ : β < θ := by dsimp [θ,β]; linarith
  have hθ : 0 < θ := by linarith
  have hθ1 : θ < 1 := by dsimp [θ,β]; linarith
  have hCpos : 0 < C := by linarith
  let a := adaptedSize B β
  have hab (v : V) := adaptedSize_bounds B hCpos.le hr hrβ hpow v
  have ha0 : a 0 = 0 := by apply le_antisymm (by simpa using (hab 0).2) (by simpa using (hab 0).1)
  have hrem : ∀ᶠ v : V in 𝓝 0, ‖P v - B v‖ ≤ ((θ-β)/C) * ‖v‖ := by
    have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hP).bound
      (show 0 < (θ-β)/C by positivity)
    simpa [hP0] using h
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW hrem)
  let U : Set V := {v | a v < δ}
  have hUsub : U ⊆ W := by
    intro v hv
    exact (hδsub (show v ∈ Metric.ball 0 δ by
      rw [Metric.mem_ball,dist_zero_right]; exact (hab v).1.trans_lt hv)).1
  have hstep (v : V) (hv : v ∈ U) : a (P v) ≤ θ * a v := by
    have hvr := (hδsub (show v ∈ Metric.ball 0 δ by
      rw [Metric.mem_ball,dist_zero_right]; exact (hab v).1.trans_lt hv)).2
    have heq : C * ((θ-β)/C) = θ-β := by field_simp
    calc
      a (P v) ≤ a (B v) + C * ‖P v-B v‖ := adaptedSize_add_bound B hCpos.le hr hrβ hpow _ _
      _ ≤ β * a v + C * (((θ-β)/C) * ‖v‖) :=
        add_le_add (adaptedSize_linear_step B hCpos.le hr hrβ hpow v)
          (mul_le_mul_of_nonneg_left hvr hCpos.le)
      _ = β * a v + (θ-β) * ‖v‖ := by rw [← mul_assoc,heq]
      _ ≤ θ * a v := by nlinarith [(hab v).1]
  have hU : MapsTo P U U := by
    intro v hv
    have hav : 0 ≤ a v := (norm_nonneg v).trans (hab v).1
    exact (hstep v hv).trans_lt ((mul_le_of_le_one_left hav hθ1.le).trans_lt hv)
  refine ⟨U, (continuous_adaptedSize B hCpos.le hr hrβ hpow).isOpen_preimage _ isOpen_Iio,
    by change a 0 < δ; rw [ha0]; exact hδ, hUsub,hU,θ,hθ,hθ1,?_⟩
  intro v hv j
  have hj : a (P^[j] v) ≤ θ ^ j * a v := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply',pow_succ]
      exact (hstep _ (iterate_mem hU hv j)).trans (by nlinarith)
  exact (hab _).1.trans (hj.trans (by nlinarith [(hab v).2, pow_nonneg hθ.le j]))

end Discrete

section SpectralBridge
open scoped Matrix.Norms.Operator
open Matrix
open Ch08.MatrixPowerCriteria
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Transfer the accepted real matrix power criterion through the actual
finite basis. This preserves the arbitrary original norm on the section. -/
lemma power_bound_of_strict_spectrum (B : V →L[ℝ] V)
    (hspec : StrictSpectrum (complexify (LinearMap.toMatrix (Module.finBasis ℝ V)
      (Module.finBasis ℝ V) B.toLinearMap))) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧
      ∀ j : ℕ, ∀ v : V, ‖(B ^ j) v‖ ≤ C * r ^ j * ‖v‖ := by
  let b := Module.finBasis ℝ V
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M := LinearMap.toMatrix b b B.toLinearMap
  obtain ⟨r,hr,hr1,C,hC,hM⟩ := (realGeometricCriterion M).mpr hspec
  have hone (v : V) : M *ᵥ e v = e (B v) := by
    exact B.toLinearMap.toMatrix_mulVec_repr b b v
  have hpowers (j : ℕ) (v : V) : (M ^ j) *ᵥ e v = e ((B ^ j) v) := by
    induction j generalizing v with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec,hone,ih,pow_succ]
      rfl
  let C' := 1 + ‖e.symm.toContinuousLinearMap‖ * C * ‖e.toContinuousLinearMap‖
  have hC' : 1 ≤ C' := by
    have hn : 0 ≤ ‖e.symm.toContinuousLinearMap‖ * C * ‖e.toContinuousLinearMap‖ := by positivity
    dsimp [C']; linarith
  refine ⟨C',r,hC',hr,hr1,?_⟩
  intro j v
  have he := e.toContinuousLinearMap.le_opNorm v
  have hei := e.symm.toContinuousLinearMap.le_opNorm (e ((B^j) v))
  simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hei
  have hmat := Matrix.linfty_opNorm_mulVec (M ^ j) (e v)
  rw [hpowers] at hmat
  calc
    ‖(B ^ j) v‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ((B^j) v)‖ := hei
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖M ^ j‖ * ‖e v‖) := by gcongr
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ((C * r ^ j) *
        (‖e.toContinuousLinearMap‖ * ‖v‖)) := by
      gcongr
      · exact hM j
      · exact he
    _ ≤ C' * r ^ j * ‖v‖ := by dsimp [C']; nlinarith [pow_nonneg hr.le j, norm_nonneg v]

/-- The full nonlinear section contraction, inside any prescribed neighborhood. -/
lemma discrete_decay_of_strict_spectrum {P : V → V} (hP0 : P 0 = 0)
    (hP : DifferentiableAt ℝ P 0)
    (hspec : StrictSpectrum (complexify (LinearMap.toMatrix (Module.finBasis ℝ V)
      (Module.finBasis ℝ V) (fderiv ℝ P 0).toLinearMap)))
    {W : Set V} (hW : W ∈ 𝓝 0) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧ U ⊆ W ∧ MapsTo P U U ∧
      ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧
        ∀ v ∈ U, ∀ j : ℕ, ‖P^[j] v‖ ≤ C * θ ^ j * ‖v‖ := by
  obtain ⟨C,r,hC,hr,hr1,hpow⟩ := power_bound_of_strict_spectrum (fderiv ℝ P 0) hspec
  obtain ⟨U,hUo,h0U,hUW,hUU,θ,hθ,hθ1,hdec⟩ :=
    discrete_decay_of_power_bound hP0 _ hP.hasFDerivAt hC hr.le hr1 hpow hW
  exact ⟨U,hUo,h0U,hUW,hUU,C,θ,by linarith,hθ,hθ1,hdec⟩

end SpectralBridge

/-- Section contraction and its quantitative extension to every real forward
time. This is the entire section stage of d13:14:orbital-stability. -/
theorem section_decay : Specs.D13Unified.Ch14.SectionDecay.SectionDecayExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T hT hc hperiod hmin hnonconst ℓ d hspec
  rw [orbit_eq_period_trace F p T hT hc hperiod]
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  obtain ⟨Vt,hVto,h0Vt,hVtsrc,hVtime⟩ := return_time_window hk d hT
  obtain ⟨Va,hVao,h0Va,hVasrc,L,hL,K,hK,hΓK,hKdom,harcs⟩ :=
    compact_return_arcs hF1 d hT hperiod
  have hP : DifferentiableAt ℝ (d.P : ℓ.ker → ℓ.ker) 0 :=
    (d.map_regular.contDiffAt (d.P.open_source.mem_nhds d.source_zero)).differentiableAt
      (by exact_mod_cast (show k ≠ 0 by omega))
  obtain ⟨U,hUo,h0U,hUW,hU,C,θ,hC,hθ,hθ1,hdec⟩ :=
    discrete_decay_of_strict_spectrum d.map_zero hP hspec
      (inter_mem (hVto.mem_nhds h0Vt) (hVao.mem_nhds h0Va))
  have hsrc : U ⊆ d.P.source := fun _ hv => hVtsrc (hUW hv).1
  have htime : ∀ w ∈ U, T/2 < d.τ w ∧ d.τ w < 3*T/2 :=
    fun _ hv => hVtime _ (hUW hv).1
  let b := 3*T/2
  let α := -Real.log θ / b
  have hb : 0 < b := by dsimp [b]; positivity
  have hα : 0 < α := div_pos (neg_pos.mpr (Real.log_neg hθ hθ1)) hb
  refine ⟨U,hUo,h0U,hsrc,hU,C,θ,L*C*θ⁻¹,α,hC,hθ,hθ1,by positivity,hα,
    K,hK,hΓK,hKdom,?_⟩
  intro v hv
  refine ⟨(fun j => ⟨iterate_mem hU hv j,hdec v hv j⟩),?_,htime,
    (fun j => cumulativeTime_bounds d hU htime hv j),
    cumulativeTime_tendsto d hT hU htime hv,
    (fun j s hs => return_arc hF1 d hsrc hU hv j hs),?_⟩
  · apply squeeze_zero_norm (fun j => hdec v hv j)
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1
    simpa using (tendsto_const_nhds.mul hp).mul_const ‖v‖
  · intro t ht
    obtain ⟨j,hj,hj'⟩ := exists_return_arc d hT hU htime hv ht
    have hs : t - cumulativeTime d v j ∈
        Icc 0 (d.τ ((d.P : ℓ.ker → ℓ.ker)^[j] v)) := by
      rw [cumulativeTime_succ] at hj'
      constructor <;> linarith
    have heq := return_arc hF1 d hsrc hU hv j hs
    simp only [add_sub_cancel] at heq
    have hlocal := harcs _ (hUW (iterate_mem hU hv j)).2 _ hs
    have hcount : t ≤ (j + 1 : ℝ) * b := by
      have hbnd := (cumulativeTime_bounds d hU htime hv (j+1)).2
      push_cast at hbnd
      exact hj'.le.trans hbnd
    have hconv := geometric_to_exponential hθ hθ1 hb hcount
    refine ⟨heq.1, heq.2 ▸ hlocal.1, ?_⟩
    rw [heq.2]
    calc
      Metric.infDist (flow F (t-cumulativeTime d v j)
          (p + ((d.P : ℓ.ker → ℓ.ker)^[j] v : E))) ((flow F · p) '' Icc 0 T)
          ≤ L * ‖(d.P : ℓ.ker → ℓ.ker)^[j] v‖ := hlocal.2
      _ ≤ L * (C * θ ^ j * ‖v‖) := mul_le_mul_of_nonneg_left (hdec v hv j) hL.le
      _ = (L*C*‖v‖) * θ ^ j := by ring
      _ ≤ (L*C*‖v‖) * (θ⁻¹ * Real.exp (-α*t)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
      _ = (L*C*θ⁻¹) * Real.exp (-α*t) * ‖v‖ := by ring

end D13Unified.Ch14.SectionDecay
