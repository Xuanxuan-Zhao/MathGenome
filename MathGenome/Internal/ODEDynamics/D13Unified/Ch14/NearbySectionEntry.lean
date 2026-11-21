import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.NearbySectionEntry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.ReturnBranch
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Uniform section entry near a compact periodic orbit (paper.tex, lines
3117–3128). Ambient implicit crossing charts are chosen near each phase.
Compactness supplies uniform radii and Lipschitz bounds; a nearest orbit
point converts displacement estimates to distance from the whole orbit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.NearbySectionEntry
open Ch06.StateDerivative Ch06.C1Dependence Ch11.Orbits
open Specs.D13Unified.Ch01.AutonomousParameters
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma complete_time (F : AutonomousODE E) {p : E} (hc : IsComplete F p) (s : ℝ) :
    s ∈ (flowInterval F p).carrier := by rw [hc]; trivial

omit [FiniteDimensional ℝ E] in
lemma periodic_orbit_image (F : AutonomousODE E) {p : E}
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T) :
    orbit F p = (fun t => flow F t p) '' Icc 0 T := by
  apply Subset.antisymm
  · rintro x ⟨t, _, rfl⟩
    obtain ⟨s, hs, he⟩ := hperiod.exists_mem_Ico₀ hT t
    exact ⟨s, ⟨hs.1, hs.2.le⟩, he.symm⟩
  · rintro x ⟨s, _, rfl⟩
    exact ⟨s, complete_time F hc s, rfl⟩

lemma periodic_orbit_compact (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T) :
    IsCompact (orbit F p) := by
  rw [periodic_orbit_image F hT hc hperiod]
  exact isCompact_Icc.image_of_continuousOn ((flow_ivp F hF hp).1.1.continuousOn.mono
    (fun s _ => complete_time F hc s))

lemma periodic_orbit_nearest (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T) (x : E) :
    ∃ s ∈ Icc 0 T, ‖x - flow F s p‖ = Metric.infDist x (orbit F p) := by
  have hne : (orbit F p).Nonempty := ⟨p, 0, (flow_ivp F hF hp).2.1,
    (flow_ivp F hF hp).2.2⟩
  obtain ⟨q, hq, hd⟩ := (periodic_orbit_compact F hF hp hT hc hperiod).exists_infDist_eq_dist hne x
  rw [periodic_orbit_image F hT hc hperiod] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  exact ⟨s, hs, by simpa only [dist_eq_norm] using hd.symm⟩

lemma phase_return (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T) (s : ℝ) :
    (2*T-s, flow F s p) ∈ flowDomain F ∧
      flow F (2*T-s) (flow F s p) = p := by
  have hs := complete_time F hc s
  have ht := Ch11.Flow.flow_translation F hF p hp s hs
  have hq := (flow_ivp F hF hp).1.2.1 s hs
  refine ⟨⟨hq, ?_⟩, ?_⟩
  · rw [ht.1]
    exact complete_time F hc _
  · rw [ht.2 _ (complete_time F hc _)]
    have hr : flow F (T+T) p = p := (hperiod T).trans (by
      simpa only [zero_add] using (hperiod 0).trans (flow_ivp F hF hp).2.2)
    rw [show 2*T-s+s = T+T by ring]
    exact hr

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Compactness turns finitely many local radius/constant estimates into one
uniform estimate. The witness permitted by `P` may depend on the chart. -/
lemma compact_uniform_estimate {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) (P : A → E → ℝ → Prop)
    (hmono : ∀ a h C D, C ≤ D → P a h C → P a h D)
    (hloc : ∀ a ∈ K, ∃ V ∈ 𝓝 a, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ b ∈ V ∩ K, ∀ h : E, ‖h‖ < r → P b h C) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ a ∈ K, ∀ h : E, ‖h‖ < r → P a h C := by
  let Q : Set A → Prop := fun B => ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
    ∀ a ∈ B ∩ K, ∀ h : E, ‖h‖ < r → P a h C
  have hQ : Q K := by
    apply hK.induction_on (p := Q)
    · exact ⟨1,1,by norm_num,by norm_num,by simp⟩
    · intro B D hBD
      rintro ⟨r,C,hr,hC,h⟩
      exact ⟨r,C,hr,hC,fun a ha => h a ⟨hBD ha.1,ha.2⟩⟩
    · intro B D
      rintro ⟨r,C,hr,hC,h⟩ ⟨r',C',hr',hC',h'⟩
      refine ⟨min r r',max C C',lt_min hr hr',lt_max_of_lt_left hC,?_⟩
      intro a ha v hv
      rcases ha.1 with haB | haD
      · exact hmono a v C _ (le_max_left _ _) (h a ⟨haB,ha.2⟩ v
          (lt_of_lt_of_le hv (min_le_left _ _)))
      · exact hmono a v C' _ (le_max_right _ _) (h' a ⟨haD,ha.2⟩ v
          (lt_of_lt_of_le hv (min_le_right _ _)))
    · intro a ha
      obtain ⟨V,hV,r,C,hr,hC,h⟩ := hloc a ha
      exact ⟨V,mem_nhdsWithin_of_mem_nhds hV,r,C,hr,hC,h⟩
  obtain ⟨r,C,hr,hC,h⟩ := hQ
  exact ⟨r,C,hr,hC,fun a ha => h a ⟨ha,ha⟩⟩

/-- C¹ maps near a compact zero section have a uniform bound for increments
normal to that section, and those increments stay in the original open set. -/
lemma compact_normal_estimate {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {K : Set A} (hK : IsCompact K) {U : Set (A × E)} (hU : IsOpen U)
    (H : A × E → B) (hH : ∀ a ∈ K, ContDiffAt ℝ 1 H (a,0))
    (hKU : ∀ a ∈ K, (a,0) ∈ U) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ a ∈ K, ∀ h : E, ‖h‖ < r →
      (a,h) ∈ U ∧ ‖H (a,h) - H (a,0)‖ ≤ C * ‖h‖ := by
  apply compact_uniform_estimate hK (fun a h C =>
    (a,h) ∈ U ∧ ‖H (a,h) - H (a,0)‖ ≤ C * ‖h‖)
  · intro a h C D hCD he
    exact ⟨he.1,he.2.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))⟩
  · intro a ha
    obtain ⟨L,V,hV,hL⟩ := (hH a ha).exists_lipschitzOnWith
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds (hKU a ha)))
    refine ⟨Metric.ball a r,Metric.ball_mem_nhds _ hr,r,(L : ℝ)+1,hr,by positivity,?_⟩
    intro b hb h hh
    have h₁ : (b,h) ∈ Metric.ball (a,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using ⟨hb.1,hh⟩
    have h₀ : (b,(0 : E)) ∈ Metric.ball (a,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using ⟨hb.1,hr⟩
    refine ⟨(hball h₁).2,?_⟩
    have he := hL.dist_le_mul _ (hball h₁).1 _ (hball h₀).1
    rw [dist_prod_same_left,dist_zero_right,dist_eq_norm] at he
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Scalar implicit crossing time for arbitrary ambient initial points. The
initial point need not lie on the section, and the crossing need not be a
return to the initial point. -/
lemma implicit_crossing_time (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p q : E} {R : ℝ}
    (hbase : (R,q) ∈ flowDomain F) (hr : flow F R q = p)
    (ℓ : E →L[ℝ] ℝ) (ha : ℓ (F.eval p) ≠ 0) :
    ∃ τ : E → ℝ, τ q = R ∧ ContDiffAt ℝ 1 τ q ∧
      (∀ᶠ a : E × ℝ in 𝓝 (q,R),
        (a.2,a.1) ∈ flowDomain F ∧
        (ℓ (flow F a.2 a.1 - p) = 0 ↔ a.2 = τ a.1)) ∧
      (∀ᶠ x : E in 𝓝 q,
        (τ x,x) ∈ flowDomain F ∧ ℓ (flow F (τ x) x - p) = 0) := by
  let H : E × ℝ → E := fun a => flow F a.2 a.1
  let g : E × ℝ → ℝ := fun a => ℓ (H a - p)
  have hreg := Ch11.Flow.flow_regularity 1 (by omega) F hF
  have hcdH : ContDiffAt ℝ 1 H (q,R) :=
    (hreg.2.1.contDiffAt (hreg.1.mem_nhds hbase)).comp (q,R)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hcd : ContDiffAt ℝ 1 g (q,R) :=
    ℓ.contDiff.contDiffAt.comp (q,R) (hcdH.sub contDiffAt_const)
  let M := fderiv ℝ (flow F R) q
  let L : E × ℝ →L[ℝ] E :=
    M.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval p))
  have hdH : HasFDerivAt H L (q,R) := by
    have hf := ReturnBranch.flow_joint_derivative F hF hbase
    rw [hr] at hf
    have hh := hf.comp (q,R) ((hasFDerivAt_snd (𝕜 := ℝ) (p := (q,R))).prodMk
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (q,R))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro a
    simp [L,M,ContinuousLinearMap.coprod_apply,add_comm]
  have hdg : HasFDerivAt g (ℓ.comp L) (q,R) :=
    ℓ.hasFDerivAt.comp (q,R) (hdH.sub_const p)
  have hright : (fderiv ℝ g (q,R)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (ℓ (F.eval p)) := by
    rw [hdg.fderiv]
    apply ContinuousLinearMap.ext
    intro r
    simp [L]
  have hinv : ((fderiv ℝ g (q,R)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [hright]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (ContinuousLinearMap.id ℝ ℝ).smulRight ((ℓ (F.eval p))⁻¹)) <;>
      apply ContinuousLinearMap.ext <;> intro r <;> simp [ha]
  let τ := hcd.implicitFunction one_ne_zero hinv
  have hτq : τ q = R := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hτcd : ContDiffAt ℝ 1 τ q := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hg0 : g (q,R) = 0 := by simp [g,H,hr]
  have hdom : ∀ᶠ a : E × ℝ in 𝓝 (q,R), (a.2,a.1) ∈ flowDomain F :=
    (continuous_snd.prodMk continuous_fst).continuousAt.preimage_mem_nhds
      (hreg.1.mem_nhds hbase)
  have hpair : ∀ᶠ a : E × ℝ in 𝓝 (q,R),
      (a.2,a.1) ∈ flowDomain F ∧ (g a = 0 ↔ a.2 = τ a.1) := by
    filter_upwards [hdom,hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv]
      with a hd he
    exact ⟨hd,by simpa only [hg0,eq_comm] using he⟩
  refine ⟨τ,hτq,hτcd,hpair,?_⟩
  have ht : Tendsto (fun x => (x,τ x)) (𝓝 q) (𝓝 (q,R)) := by
    simpa only [hτq,id_eq] using tendsto_id.prodMk_nhds hτcd.continuousAt.tendsto
  filter_upwards [ht.eventually hpair] with x hx
  exact ⟨hx.1,hx.2.mpr rfl⟩

lemma phase_time_domain (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (hc : IsComplete F p) (t s : ℝ) :
    (t,flow F s p) ∈ flowDomain F ∧ flow F t (flow F s p) = flow F (t+s) p := by
  have hs := complete_time F hc s
  have ht := Ch11.Flow.flow_translation F hF p hp s hs
  exact ⟨⟨(flow_ivp F hF hp).1.2.1 s hs,by rw [ht.1]; exact complete_time F hc _⟩,
    ht.2 t (complete_time F hc _)⟩

lemma complete_trajectory_contDiff (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (hc : IsComplete F p) : ContDiff ℝ 1 (fun s => flow F s p) := by
  apply contDiffOn_univ.mp
  simpa only [show (flowInterval F p).carrier = univ from hc] using (flow_ivp F hF hp).1.1

/-- Uniform finite-time estimates before entry, measured against the same
phase on the reference orbit. No existence for nearby states is assumed. -/
lemma uniform_phase_flow_estimate (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T B : ℝ} (hc : IsComplete F p) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 B, ∀ h : E, ‖h‖ < r →
        (t,flow F s p+h) ∈ flowDomain F ∧
        ‖flow F t (flow F s p+h) - flow F (t+s) p‖ ≤ C * ‖h‖ := by
  let K : Set (ℝ × ℝ) := Icc 0 B ×ˢ Icc 0 T
  let H : (ℝ × ℝ) × E → E := fun a => flow F a.1.1 (flow F a.1.2 p+a.2)
  let J : (ℝ × ℝ) × E → ℝ × E := fun a => (a.1.1,flow F a.1.2 p+a.2)
  have hγ := complete_trajectory_contDiff F hF hp hc
  have hJ : ContDiff ℝ 1 J :=
    (contDiff_fst.fst).prodMk ((hγ.comp (contDiff_snd.comp contDiff_fst)).add contDiff_snd)
  have ho := isOpen_flowDomain F hF
  have hU : IsOpen (J ⁻¹' flowDomain F) := ho.preimage hJ.continuous
  have hKU : ∀ a ∈ K, (a, (0 : E)) ∈ J ⁻¹' flowDomain F := by
    intro a _
    simpa [J] using (phase_time_domain F hF hp hc a.1 a.2).1
  have hH : ∀ a ∈ K, ContDiffAt ℝ 1 H (a,0) := by
    intro a ha
    exact ((autonomous_joint_c1 F hF).contDiffAt (ho.mem_nhds (hKU a ha))).comp
      (a,0) hJ.contDiffAt
  obtain ⟨r,C,hr,hC,he⟩ := compact_normal_estimate (isCompact_Icc.prod isCompact_Icc)
    hU H hH hKU
  refine ⟨r,C,hr,hC,?_⟩
  intro s hs t ht h hh
  have he' := he (t,s) ⟨ht,hs⟩ h hh
  refine ⟨he'.1,?_⟩
  simpa only [H,add_zero,(phase_time_domain F hF hp hc t s).2] using he'.2

/-- One phase and one displacement admit an entry, with the indicated
constant. This is a local-chart predicate, not a phase projection. -/
def PhaseEntry (F : AutonomousODE E) (p : E) (ℓ : E →L[ℝ] ℝ)
    (S : Set ℓ.ker) (B s : ℝ) (h : E) (C : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t ≤ B ∧ (t,flow F s p+h) ∈ flowDomain F ∧
    (∃ v ∈ S, flow F t (flow F s p+h) = p+(v : E)) ∧
    ‖flow F t (flow F s p+h)-p‖ ≤ C*‖h‖

/-- A local ambient crossing chart vanishes on the nearby reference arc.
Its Lipschitz estimate therefore measures displacement from that arc,
rather than distance from the center of the chart. -/
lemma local_phase_entry (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T)
    (ℓ : E →L[ℝ] ℝ) (ha : ℓ (F.eval p) ≠ 0)
    (S : Set ℓ.ker) (hS : IsOpen S) (h0S : (0 : ℓ.ker) ∈ S)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Icc 0 T) :
    ∃ V ∈ 𝓝 s₀, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ s ∈ V ∩ Icc 0 T, ∀ h : E, ‖h‖ < r → PhaseEntry F p ℓ S (3*T) s h C := by
  let γ : ℝ → E := fun s => flow F s p
  let q := γ s₀
  let R := 2*T-s₀
  have hreturn := phase_return F hF hp hc hperiod s₀
  obtain ⟨τ,hτq,hτcd,hpair,hgraph⟩ := implicit_crossing_time F hF hreturn.1 hreturn.2 ℓ ha
  change τ q = R at hτq
  change ContDiffAt ℝ 1 τ q at hτcd
  let P : E → E := fun x => flow F (τ x) x
  have hPq : P q = p := by
    change flow F (τ q) q = p
    rw [hτq]
    exact hreturn.2
  have ho := isOpen_flowDomain F hF
  have hPcd : ContDiffAt ℝ 1 P q := by
    have hflow : ContDiffAt ℝ 1 (fun a : ℝ × E => flow F a.1 a.2) (τ q,q) := by
      rw [hτq]
      exact (autonomous_joint_c1 F hF).contDiffAt (ho.mem_nhds hreturn.1)
    have hh := hflow.comp (f := fun x : E => (τ x,x)) q (hτcd.prodMk (contDiffAt_id (x := q) (𝕜 := ℝ)))
    simpa only [P,Function.comp_def,id_eq] using hh
  let Q := ReturnBranch.transverseProjection ℓ (F.eval p) ha
  have hQzero : Q (P q-p) = 0 := by rw [hPq,sub_self]; simp
  have hsection : ∀ᶠ x in 𝓝 q, Q (P x-p) ∈ S := by
    have hcont : ContinuousAt (fun x => Q (P x-p)) q :=
      Q.continuous.continuousAt.comp (hPcd.continuousAt.sub continuousAt_const)
    exact hcont.preimage_mem_nhds (by rw [hQzero]; exact hS.mem_nhds h0S)
  have htimes : ∀ᶠ x in 𝓝 q, τ x ∈ Ioo 0 (3*T) := by
    apply hτcd.continuousAt.preimage_mem_nhds
    rw [hτq]
    exact Ioo_mem_nhds (by change 0 < 2*T-s₀; linarith [hs₀.2]) (by change 2*T-s₀ < 3*T; linarith [hs₀.1])
  obtain ⟨L,W,hW,hL⟩ := hPcd.exists_lipschitzOnWith
  have hgood : ∀ᶠ x in 𝓝 q,
      x ∈ W ∧ τ x ∈ Ioo 0 (3*T) ∧ Q (P x-p) ∈ S ∧
      (τ x,x) ∈ flowDomain F ∧ ℓ (P x-p) = 0 := by
    filter_upwards [hW,htimes,hsection,hgraph] with x hx ht hz hg
    exact ⟨hx,ht,hz,hg⟩
  obtain ⟨a,haPos,haGood⟩ := Metric.mem_nhds_iff.mp hgood
  have hγ := complete_trajectory_contDiff F hF hp hc
  have hnear : ∀ᶠ s in 𝓝 s₀, γ s ∈ Metric.ball q (a/2) :=
    hγ.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
  have hcurve : Tendsto (fun s => (γ s,2*T-s)) (𝓝 s₀) (𝓝 (q,R)) :=
    hγ.continuous.continuousAt.tendsto.prodMk_nhds
      (continuousAt_const.sub continuousAt_id).tendsto
  have hvanish : ∀ᶠ s in 𝓝 s₀, P (γ s) = p := by
    filter_upwards [hcurve.eventually hpair] with s hs
    have hr := (phase_return F hF hp hc hperiod s).2
    have he : ℓ (flow F (2*T-s) (γ s)-p) = 0 := by rw [hr]; simp
    have hτ : τ (γ s) = 2*T-s := (hs.2.mp he).symm
    exact (congrArg (fun t => flow F t (γ s)) hτ).trans hr
  refine ⟨{s | γ s ∈ Metric.ball q (a/2) ∧ P (γ s) = p},
    inter_mem hnear hvanish,a/2,(L : ℝ)+1,by positivity,by positivity,?_⟩
  intro s hs h hh
  have hxball : γ s+h ∈ Metric.ball q a := by
    rw [Metric.mem_ball,dist_eq_norm]
    calc ‖γ s+h-q‖ = ‖(γ s-q)+h‖ := by congr 1; abel
         _ ≤ ‖γ s-q‖+‖h‖ := norm_add_le _ _
         _ < a := by have hn := hs.1.1; rw [Metric.mem_ball,dist_eq_norm] at hn; linarith
  have hqball : γ s ∈ Metric.ball q a :=
    Metric.ball_subset_ball (by linarith) hs.1.1
  have hx := haGood hxball
  have hq' := haGood hqball
  refine ⟨τ (γ s+h),hx.2.1.1,hx.2.1.2.le,hx.2.2.2.1,?_,?_⟩
  · refine ⟨Q (P (γ s+h)-p),hx.2.2.1,?_⟩
    have he : (Q (P (γ s+h)-p) : E) = P (γ s+h)-p := by
      rw [ReturnBranch.transverseProjection_apply,hx.2.2.2.2]
      simp
    change P (γ s+h) = p+_
    rw [he]
    abel
  · have he := hL.dist_le_mul _ hx.1 _ hq'.1
    rw [hs.1.2,dist_eq_norm,dist_eq_norm] at he
    have he' : ‖P (γ s+h)-p‖ ≤ (L : ℝ)*‖h‖ := by simpa using he
    exact he'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- A finite covering of the phase interval gives uniform entry constants.
Different points may use different local crossing charts. -/
lemma uniform_phase_entry (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete F p)
    (hperiod : Function.Periodic (fun t => flow F t p) T)
    (ℓ : E →L[ℝ] ℝ) (ha : ℓ (F.eval p) ≠ 0)
    (S : Set ℓ.ker) (hS : IsOpen S) (h0S : (0 : ℓ.ker) ∈ S) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ s ∈ Icc 0 T, ∀ h : E, ‖h‖ < r →
      PhaseEntry F p ℓ S (3*T) s h C := by
  apply compact_uniform_estimate isCompact_Icc (PhaseEntry F p ℓ S (3*T))
  · intro s h C D hCD
    rintro ⟨t,ht,hB,hd,hS,he⟩
    exact ⟨t,ht,hB,hd,hS,he.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))⟩
  · exact local_phase_entry F hF hp hT hc hperiod ℓ ha S hS h0S

/-- Uniform positive section entry for every point sufficiently near the
whole periodic orbit, including points of the orbit itself. -/
theorem nearby_section_entry :
    Specs.D13Unified.Ch14.NearbySectionEntry.NearbySectionEntryExpected.{u} := by
  intro E _ _ _ F hF p hp T hT hc hperiod ℓ ha S hS h0S
  obtain ⟨r₁,C₁,hr₁,hC₁,hentry⟩ := uniform_phase_entry F hF hp hT hc hperiod ℓ ha S hS h0S
  obtain ⟨r₂,C₂,hr₂,hC₂,hflow⟩ := uniform_phase_flow_estimate F hF hp (T := T) (B := 3*T) hc
  refine ⟨min r₁ r₂,3*T,C₁,C₂,lt_min hr₁ hr₂,by positivity,hC₁,hC₂,?_⟩
  intro x hx
  obtain ⟨s,hs,hdist⟩ := periodic_orbit_nearest F hF hp hT hc hperiod x
  let h := x-flow F s p
  have hsmall₁ : ‖h‖ < r₁ := by
    dsimp only [h]; rw [hdist]; exact lt_of_lt_of_le hx (min_le_left _ _)
  have hsmall₂ : ‖h‖ < r₂ := by
    dsimp only [h]; rw [hdist]; exact lt_of_lt_of_le hx (min_le_right _ _)
  have hrepr : flow F s p+h = x := by dsimp [h]; abel
  obtain ⟨t,ht,hB,hdom,hsection,hbound⟩ := hentry s hs h hsmall₁
  rw [hrepr] at hdom hsection hbound
  have hpre : ∀ a ∈ Icc 0 t, (a,x) ∈ flowDomain F ∧
      ‖flow F a x-flow F (a+s) p‖ ≤ C₂*Metric.infDist x (orbit F p) := by
    intro a ha
    have he := hflow s hs a ⟨ha.1,ha.2.trans hB⟩ h hsmall₂
    simpa only [hrepr,h,hdist] using he
  refine ⟨(hpre 0 ⟨le_rfl,ht.le⟩).1.1,t,ht,hB,fun a ha => (hpre a ha).1,
    hsection,?_,?_⟩
  · simpa only [h,hdist] using hbound
  · intro a ha
    have hm : flow F (a+s) p ∈ orbit F p := ⟨a+s,complete_time F hc _,rfl⟩
    exact (Metric.infDist_le_dist_of_mem hm).trans
      (by simpa only [dist_eq_norm] using (hpre a ha).2)

end D13Unified.Ch14.NearbySectionEntry
