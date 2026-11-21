import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.Lyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.StabilityDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Omega
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch12.Lyapunov
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch11.OmegaTopology
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch12.Lyapunov
open Ch06.StateDerivative
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The chain rule uses the actual derivative equation on the maximal interval. -/
lemma energy_hasDerivAt (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U) {x : E} (hx : x ∈ F.domain)
    {t : ℝ} (ht : t ∈ (flowInterval F x).carrier) (hy : flow F t x ∈ U) :
    HasDerivAt (fun s => V (flow F s x)) (lieDerivative F V (flow F t x)) t := by
  have hd := (hV.differentiableOn (by norm_num) (flow F t x) hy).differentiableAt
    (hU.mem_nhds hy)
  convert hd.hasFDerivAt.comp_hasDerivAt t ((flow_ivp F hF hx).1.2.2 t ht) using 1 <;> rfl

/-- On any available compact time segment confined to U, energy cannot increase. -/
lemma energy_antitone (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U)
    (hdec : ∀ y ∈ U, lieDerivative F V y ≤ 0)
    {x : E} (hx : x ∈ F.domain) {a b : ℝ}
    (hI : Icc a b ⊆ (flowInterval F x).carrier)
    (hstay : ∀ s ∈ Icc a b, flow F s x ∈ U) :
    AntitoneOn (fun s => V (flow F s x)) (Icc a b) := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :=
    energy_hasDerivAt F hF hU hV hx (hI hs) (hstay s hs)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact hV.continuousOn.comp ((flow_ivp F hF hx).1.1.continuousOn.mono hI) hstay
  · intro s hs
    exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hd s (interior_subset hs)).deriv]
    exact hdec _ (hstay s (interior_subset hs))

/-- A compact sublevel with a strict boundary margin traps every forward
trajectory starting in it. Continuous induction supplies the no-exit argument. -/
lemma sublevel_positivelyInvariant (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    (hUΩ : U ⊆ F.domain) {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U)
    (hdec : ∀ y ∈ U, lieDerivative F V y ≤ 0)
    {r c : ℝ} (hball : closedBall (0 : E) r ⊆ U)
    (hmargin : ∀ y ∈ closedBall (0 : E) r, V y ≤ c → ‖y‖ < r) :
    positiveInvariantValue F (closedBall 0 r ∩ V ⁻¹' Iic c) := by
  let S := closedBall (0 : E) r ∩ V ⁻¹' Iic c
  have hSc : IsClosed S :=
    (hV.continuousOn.mono hball).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hSΩ : S ⊆ F.domain := fun y hy => hUΩ (hball hy.1)
  refine ⟨hSΩ, ?_⟩
  intro x hx T hT hT0
  have hivp := flow_ivp F hF (hSΩ hx)
  have hI : Icc 0 T ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hivp.2.1 hT
  let A : Set ℝ := (fun t => flow F t x) ⁻¹' S
  have hAc : IsClosed (A ∩ Icc 0 T) := by
    rw [inter_comm]
    exact (hivp.1.1.continuousOn.mono hI).preimage_isClosed_of_isClosed isClosed_Icc hSc
  have hA0 : (0 : ℝ) ∈ A := by
    change flow F 0 x ∈ S
    have hzero : flow F 0 x = x := hivp.2.2
    rw [hzero]
    exact hx
  apply hAc.mem_of_ge_of_forall_exists_gt hA0 hT0
  intro t ht
  have htI := hI ⟨ht.2.1, ht.2.2.le⟩
  have hxt : flow F t x ∈ S := ht.1
  have hnorm : flow F t x ∈ ball (0 : E) r := by
    simpa only [mem_ball, dist_zero_right] using hmargin _ hxt.1 hxt.2
  have hnear : ∀ᶠ s in 𝓝 t, flow F s x ∈ ball (0 : E) r :=
    (hivp.1.1.continuousOn.continuousAt
      ((flowInterval F x).isOpen.mem_nhds htI)).eventually (isOpen_ball.mem_nhds hnorm)
  obtain ⟨d, hd, hlocal⟩ := Metric.eventually_nhds_iff.mp hnear
  let b := t + min d (T-t) / 2
  have hmin : 0 < min d (T-t) := lt_min hd (sub_pos.mpr ht.2.2)
  have htb : t < b := by dsimp [b]; linarith
  have hbT : b ≤ T := by dsimp [b]; have := min_le_right d (T-t); linarith
  have hbd : b-t < d := by dsimp [b]; have := min_le_left d (T-t); linarith
  have hloc (s : ℝ) (hs : s ∈ Icc t b) : flow F s x ∈ ball (0 : E) r := by
    apply hlocal
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    exact (sub_le_sub_right hs.2 t).trans_lt hbd
  have hseg : Icc t b ⊆ Icc 0 T := Icc_subset_Icc ht.2.1 hbT
  have he := energy_antitone F hF hU hV hdec (hSΩ hx)
    (hseg.trans hI) (fun s hs => hball (ball_subset_closedBall (hloc s hs)))
  refine ⟨b, ?_, htb, hbT⟩
  change flow F b x ∈ S
  exact ⟨ball_subset_closedBall (hloc b ⟨htb.le, le_rfl⟩),
    (he ⟨le_rfl, htb.le⟩ ⟨htb.le, le_rfl⟩ htb.le).trans hxt.2⟩

/-- Positive definiteness produces a compact trapping neighborhood in every
prescribed small ball. This also covers the zero-dimensional state space. -/
lemma trapping_neighborhood (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    (h0U : (0 : E) ∈ U) (hUΩ : U ⊆ F.domain)
    {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U) (hV0 : V 0 = 0)
    (hpos : ∀ x ∈ U, x ≠ 0 → 0 < V x)
    (hdec : ∀ x ∈ U, lieDerivative F V x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S : Set E,
      IsCompact S ∧ positiveInvariantValue F S ∧ ball 0 δ ⊆ S ∧
        S ⊆ U ∩ ball 0 ε := by
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let r := min d ε / 2
  have hr : 0 < r := half_pos (lt_min hd hε)
  have hrd : r < d := by dsimp [r]; have := min_le_left d ε; linarith
  have hrε : r < ε := by dsimp [r]; have := min_le_right d ε; linarith
  have hbU : closedBall (0 : E) r ⊆ U := (closedBall_subset_ball hrd).trans hdU
  obtain ⟨m, hm, hmV⟩ := (isCompact_sphere (0 : E) r).exists_forall_le'
    (hV.continuousOn.mono (sphere_subset_closedBall.trans hbU)) (a := 0) (by
      intro y hy
      apply hpos y (hbU (sphere_subset_closedBall hy))
      intro hy0
      have : (0 : ℝ) = r := by simpa [hy0] using hy
      linarith)
  let c := m / 2
  have hc : 0 < c := half_pos hm
  have hmargin : ∀ y ∈ closedBall (0 : E) r, V y ≤ c → ‖y‖ < r := by
    intro y hy hv
    have hy' : ‖y‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hy
    apply lt_of_le_of_ne hy'
    intro heq
    have hs : y ∈ sphere (0 : E) r := by simpa only [mem_sphere, dist_zero_right] using heq
    have := hmV y hs
    dsimp [c] at hv
    linarith
  let S := closedBall (0 : E) r ∩ V ⁻¹' Iic c
  have hSc : IsClosed S :=
    (hV.continuousOn.mono hbU).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hnear : ∀ᶠ y in 𝓝 (0 : E), V y < c :=
    (hV.continuousOn.continuousAt (hU.mem_nhds h0U)).eventually
      (Iio_mem_nhds (by simpa [hV0] using hc))
  obtain ⟨a, ha, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min a r, lt_min ha hr, S, (isCompact_closedBall 0 r).of_isClosed_subset hSc
    inter_subset_left, sublevel_positivelyInvariant F hF hU hUΩ hV hdec hbU hmargin, ?_, ?_⟩
  · intro y hy
    have hya : dist y 0 < a := (mem_ball.mp hy).trans_le (min_le_left _ _)
    have hyr : dist y 0 < r := (mem_ball.mp hy).trans_le (min_le_right _ _)
    exact ⟨hyr.le, (hsmall hya).le⟩
  · intro y hy
    exact ⟨hbU hy.1, closedBall_subset_ball hrε hy.1⟩

/-- Lyapunov stability with complete forward existence in the original domain. -/
theorem stability : Stability.{u} := by
  intro E _ _ _ F hF h0 heq U hU h0U hUΩ V hV hV0 hpos hdec ε hε
  obtain ⟨δ, hδ, S, hS, hinv, hδS, hSU⟩ :=
    trapping_neighborhood F hF hU h0U hUΩ hV hV0 hpos hdec hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx hsmall
  have hxS := hδS (show x ∈ ball 0 δ by simpa only [mem_ball, dist_zero_right] using hsmall)
  obtain ⟨hcomplete, hstay⟩ := Ch11.Invariant.compact_forward_complete F hF S hS hinv x hxS
  exact ⟨fun t ht => ⟨hx, hcomplete ht⟩, fun t ht => by
    simpa only [mem_ball, dist_zero_right] using (hSU (hstay t ht)).2⟩

/-- A strictly decreasing energy on a compact trapping set forces convergence.
The omega-limit set is used only after its compact-containment hypotheses
have been established for the actual positive orbit. -/
lemma converges_of_strict_on_compact (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U) (hV0 : V 0 = 0)
    (hpos : ∀ y ∈ U, y ≠ 0 → 0 < V y)
    (hdec : ∀ y ∈ U, lieDerivative F V y ≤ 0)
    (hstrict : ∀ y ∈ U, y ≠ 0 → lieDerivative F V y < 0)
    {S : Set E} (hS : IsCompact S) (hinv : positiveInvariantValue F S)
    (hSU : S ⊆ U) {x : E} (hx : x ∈ S) :
    Tendsto (fun t : ℝ => flow F t x) atTop (𝓝 (0 : E)) := by
  have hxΩ := hinv.1 hx
  obtain ⟨hcomplete, hstay⟩ := Ch11.Invariant.compact_forward_complete F hF S hS hinv x hx
  have hKS : closure (positiveOrbit F x) ⊆ S := by
    apply hS.isClosed.closure_subset_iff.mpr
    rintro y ⟨t, ht, rfl⟩
    exact hstay t ht.2
  have hK : IsCompact (closure (positiveOrbit F x)) :=
    hS.of_isClosed_subset isClosed_closure hKS
  obtain ⟨_, hne, _, _, hωK, _, hfull, _, hseq, hdist⟩ :=
    Ch11.Omega.compact_omega F hF x hxΩ hK (hKS.trans hinv.1)
  have hωS : omegaValue F x ⊆ S := hωK.trans hKS
  have hanti : AntitoneOn (fun t : ℝ => V (flow F t x)) (Ici 0) := by
    intro a ha b hb hab
    have hI : Icc a b ⊆ (flowInterval F x).carrier :=
      fun t ht => hcomplete (ha.trans ht.1)
    have he := energy_antitone F hF hU hV hdec hxΩ hI
      (fun t ht => hSU (hstay t (ha.trans ht.1)))
    exact he ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let g : ℝ → ℝ := fun t => V (flow F (max t 0) x)
  have hg : Antitone g := fun a b hab => hanti (show max a 0 ∈ Ici (0 : ℝ) from le_max_right a 0)
    (show max b 0 ∈ Ici (0 : ℝ) from le_max_right b 0) (max_le_max_right 0 hab)
  have hnonneg (y : E) (hy : y ∈ S) : 0 ≤ V y := by
    by_cases hy0 : y = 0
    · simp [hy0, hV0]
    · exact (hpos y (hSU hy) hy0).le
  have hbound : BddBelow (range g) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hnonneg _ (hstay _ (le_max_right _ _))
  let ℓ : ℝ := ⨅ t, g t
  have hlim : Tendsto (fun t : ℝ => V (flow F t x)) atTop (𝓝 ℓ) := by
    apply (tendsto_atTop_ciInf hg hbound).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [g, max_eq_left ht]
  have hvalue (y : E) (hy : y ∈ omegaValue F x) : V y = ℓ := by
    obtain ⟨t, _, htTop, hty⟩ := (hseq y).mp hy
    have hc : ContinuousAt V y := hV.continuousOn.continuousAt (hU.mem_nhds (hSU (hωS hy)))
    exact tendsto_nhds_unique (hc.tendsto.comp hty) (hlim.comp htTop)
  have hzero (y : E) (hy : y ∈ omegaValue F x) : y = 0 := by
    have hyΩ := hinv.1 (hωS hy)
    have hyv := flow_ivp F hF hyΩ
    have h0I : (0 : ℝ) ∈ (flowInterval F y).carrier := hyv.2.1
    have hzeroFlow : flow F 0 y = y := hyv.2.2
    have hconst : ∀ t : ℝ, V (flow F t y) = ℓ :=
      fun t => hvalue _ ((hfull y hy).2 t)
    have hder := energy_hasDerivAt F hF hU hV hyΩ h0I
      (hSU (hωS ((hfull y hy).2 0)))
    have hc : HasDerivAt (fun t : ℝ => V (flow F t y)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) ℓ).congr_of_eventuallyEq (Eventually.of_forall hconst)
    have hz : lieDerivative F V y = 0 := by simpa only [hzeroFlow] using hder.unique hc
    by_contra hy0
    exact (ne_of_lt (hstrict y (hSU (hωS hy)) hy0)) hz
  have hω0 : omegaValue F x = {0} := by
    apply Subset.antisymm
    · intro y hy
      simpa only [mem_singleton_iff] using hzero y hy
    · obtain ⟨y, hy⟩ := hne
      have hy0 := hzero y hy
      simpa only [hy0, singleton_subset_iff] using hy
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [hω0, infDist_singleton, dist_zero_right] using hdist

/-- Strict negativity away from zero gives local asymptotic stability. -/
theorem asymptotic_stability : AsymptoticStability.{u} := by
  intro E _ _ _ F hF h0 heq U hU h0U hUΩ V hV hV0 hpos hstrict
  have hdec : ∀ x ∈ U, lieDerivative F V x ≤ 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0, lieDerivative, heq]
    · exact (hstrict x hx hx0).le
  refine ⟨stability F hF h0 heq U hU h0U hUΩ V hV hV0 hpos hdec, ?_⟩
  obtain ⟨δ, hδ, S, hS, hinv, hδS, hSU⟩ :=
    trapping_neighborhood F hF hU h0U hUΩ hV hV0 hpos hdec (ε := 1) zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro x hx hsmall
  have hxS := hδS (show x ∈ ball 0 δ by simpa only [mem_ball, dist_zero_right] using hsmall)
  have hcomplete := (Ch11.Invariant.compact_forward_complete F hF S hS hinv x hxS).1
  exact ⟨fun t ht => ⟨hx, hcomplete ht⟩,
    converges_of_strict_on_compact F hF hU hV hV0 hpos hdec hstrict hS hinv
      (fun y hy => (hSU hy).1) hxS⟩

/-- Integrating factor estimate, valid on any available segment on which
all the hypotheses hold. No global existence is assumed in this lemma. -/
lemma energy_exponential_bound (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 1 V U) (k : ℝ)
    (hdec : ∀ y ∈ U, lieDerivative F V y ≤ -k * V y)
    {x : E} (hx : x ∈ F.domain) {t : ℝ} (ht : 0 ≤ t)
    (hI : Icc 0 t ⊆ (flowInterval F x).carrier)
    (hstay : ∀ s ∈ Icc 0 t, flow F s x ∈ U) :
    V (flow F t x) ≤ Real.exp (-k * t) * V x := by
  let W : ℝ → ℝ := fun s => Real.exp (k*s) * V (flow F s x)
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt W (Real.exp (k*s) * (k * V (flow F s x) +
        lieDerivative F V (flow F s x))) s := by
    have he : HasDerivAt (fun z : ℝ => Real.exp (k*z)) (Real.exp (k*s) * k) s :=
      by simpa using ((hasDerivAt_id s).const_mul k).exp
    convert he.mul (energy_hasDerivAt F hF hU hV hx (hI hs) (hstay s hs)) using 1
    ring
  have hm : AntitoneOn W (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      have := hdec _ (hstay s (interior_subset hs))
      linarith
  have hzero : flow F 0 x = x := (flow_ivp F hF hx).2.2
  have he : Real.exp (k*t) * V (flow F t x) ≤ V x := by
    simpa only [W, mul_zero, Real.exp_zero, hzero, one_mul] using
      hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (k*t))).mp
  calc
    Real.exp (k*t) * V (flow F t x) ≤ V x := he
    _ = Real.exp (k*t) * (Real.exp (-k*t) * V x) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp

omit [FiniteDimensional ℝ E] in
/-- Taking square roots preserves the precise coefficient and half-rate. -/
lemma quadratic_norm_estimate {c₁ c₂ c₃ t a b : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : c₁ * a ^ 2 ≤ Real.exp (-(c₃/c₂)*t) * (c₂ * b ^ 2)) :
    a ≤ Real.sqrt (c₂/c₁) * Real.exp (-c₃*t/(2*c₂)) * b := by
  have hs : Real.sqrt (c₂/c₁) ^ 2 = c₂/c₁ :=
    Real.sq_sqrt (div_nonneg hc₂.le hc₁.le)
  have he : Real.exp (-c₃*t/(2*c₂)) ^ 2 = Real.exp (-(c₃/c₂)*t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hR : 0 ≤ Real.sqrt (c₂/c₁) * Real.exp (-c₃*t/(2*c₂)) * b :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) hb
  have hsq : c₁ * (Real.sqrt (c₂/c₁) * Real.exp (-c₃*t/(2*c₂)) * b) ^ 2 =
      Real.exp (-(c₃/c₂)*t) * (c₂ * b ^ 2) := by
    rw [mul_pow, mul_pow, hs, he]
    field_simp
  have hh : a ^ 2 ≤ (Real.sqrt (c₂/c₁) * Real.exp (-c₃*t/(2*c₂)) * b) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hc₁).mp
    rwa [hsq]
  nlinarith

/-- Quadratic Lyapunov bounds give the exact exponential estimate in the
source, uniformly in all nearby initial states and every real time t ≥ 0. -/
theorem exponential_stability : ExponentialStability.{u} := by
  intro E _ _ _ F hF h0 heq U hU h0U hUΩ V hV c₁ c₂ c₃ hc₁ hc₂ hc₃ hquad hdot
  have hV0 : V 0 = 0 := by
    have := hquad 0 h0U
    exact le_antisymm (by simpa using this.2) (by simpa using this.1)
  have hpos : ∀ x ∈ U, x ≠ 0 → 0 < V x := by
    intro x hx hx0
    exact (mul_pos hc₁ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).trans_le (hquad x hx).1
  have hdec : ∀ x ∈ U, lieDerivative F V x ≤ 0 := by
    intro x hx
    exact (hdot x hx).trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc₃.le) (sq_nonneg _))
  have hlinear : ∀ x ∈ U, lieDerivative F V x ≤ -(c₃/c₂) * V x := by
    intro x hx
    calc
      lieDerivative F V x ≤ -c₃ * ‖x‖ ^ 2 := hdot x hx
      _ = -(c₃/c₂) * (c₂ * ‖x‖ ^ 2) := by field_simp
      _ ≤ -(c₃/c₂) * V x :=
        mul_le_mul_of_nonpos_left (hquad x hx).2 (neg_nonpos.mpr (div_nonneg hc₃.le hc₂.le))
  obtain ⟨δ, hδ, S, hS, hinv, hδS, hSU⟩ :=
    trapping_neighborhood F hF hU h0U hUΩ hV hV0 hpos hdec (ε := 1) zero_lt_one
  have hestimate : ∀ x ∈ F.domain, ‖x‖ < δ → forwardCompleteValue F hF x ∧
      ∀ t : ℝ, 0 ≤ t → flow F t x ∈ U ∧
        ‖flow F t x‖ ≤ Real.sqrt (c₂/c₁) * Real.exp (-c₃*t/(2*c₂)) * ‖x‖ := by
    intro x hx hxsmall
    have hxS := hδS (show x ∈ ball 0 δ by simpa only [mem_ball, dist_zero_right] using hxsmall)
    obtain ⟨hcomplete, hstay⟩ := Ch11.Invariant.compact_forward_complete F hF S hS hinv x hxS
    refine ⟨fun t ht => ⟨hx, hcomplete ht⟩, ?_⟩
    intro t ht
    have hxtU : flow F t x ∈ U := (hSU (hstay t ht)).1
    refine ⟨hxtU, ?_⟩
    have hI : Icc 0 t ⊆ (flowInterval F x).carrier := fun s hs => hcomplete hs.1
    have henergy := energy_exponential_bound F hF hU hV (c₃/c₂) hlinear hx ht hI
      (fun s hs => (hSU (hstay s hs.1)).1)
    apply quadratic_norm_estimate hc₁ hc₂ (norm_nonneg _) (norm_nonneg _)
    exact (hquad _ hxtU).1 |>.trans (henergy.trans
      (mul_le_mul_of_nonneg_left (hquad x (hSU hxS).1).2 (Real.exp_nonneg _)))
  refine ⟨?_, δ, hδ, hestimate⟩
  refine ⟨Real.sqrt (c₂/c₁), c₃/(2*c₂), δ,
    Real.sqrt_pos.mpr (div_pos hc₂ hc₁), div_pos hc₃ (mul_pos (by norm_num) hc₂), hδ, ?_⟩
  intro x hx hsmall
  obtain ⟨hcomplete, he⟩ := hestimate x hx hsmall
  refine ⟨hcomplete, ?_⟩
  intro t ht
  convert (he t ht).2 using 1
  congr 2
  congr 1
  ring

end D13Unified.Ch12.Lyapunov
