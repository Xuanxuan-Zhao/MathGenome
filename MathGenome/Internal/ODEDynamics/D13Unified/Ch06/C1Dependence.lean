import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.C1Dependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.StateDerivative
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.Autonomization
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open StateDerivative

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The autonomous maximal domain is open in elapsed time and initial state. -/
lemma isOpen_flowDomain (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain) :
    IsOpen (flowDomain F) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hx := flow_ivp F hF hq.1
  obtain ⟨a,b,h0,ht,hJ⟩ := Ch05.OpenDomain.compact_enclosure
    (flowInterval F q.2) hx.2.1 hq.2
  obtain ⟨V,hVo,hVq,hVU,hVJ,_⟩ := local_joint_variation F hF q.2 hq.1 a b
    ⟨h0.1.le,h0.2.le⟩ hJ
  exact mem_of_superset (prod_mem_nhds (Ioo_mem_nhds ht.1 ht.2) (hVo.mem_nhds hVq))
    (fun r hr => ⟨hVU hr.2, hVJ r.2 hr.2 ⟨hr.1.1.le,hr.1.2.le⟩⟩)

/-- Continuous partial derivatives give joint C¹ regularity of the autonomous
flow, before the clock and constant parameters are added. -/
lemma autonomous_joint_c1 (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) :
    ContDiffOn ℝ 1 (fun q : ℝ × E => flow F q.1 q.2) (flowDomain F) := by
  let T : ℝ → E → ℝ →L[ℝ] E := fun t ξ =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F t ξ))
  let Y : ℝ → E → E →L[ℝ] E := fun t ξ => fderiv ℝ (fun η => flow F t η) ξ
  have ho := isOpen_flowDomain F hF
  have hD := maximal_domain_derivative F hF
  have hTc : ContinuousOn (fun q : ℝ × E => T q.1 q.2) (flowDomain F) := by
    exact (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      (hF.continuousOn.comp (continuousOn_flow F hF)
      (fun q hq => (flow_ivp F hF hq.1).1.2.1 q.1 hq.2))
  have hYc : ContinuousOn (fun q : ℝ × E => Y q.1 q.2) (flowDomain F) := hD.2.1
  have hd (q : ℝ × E) (hq : q ∈ flowDomain F) :
      HasFDerivAt (fun r : ℝ × E => flow F r.1 r.2)
        ((T q.1 q.2).coprod (Y q.1 q.2)) q := by
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod (f := fun t ξ => flow F t ξ)
      (f₁ := T) (f₂ := Y)
    · filter_upwards [ho.mem_nhds hq] with r hr
      exact ((flow_ivp F hF hr.1).1.2.2 r.1 hr.2).hasFDerivAt
    · filter_upwards [ho.mem_nhds hq] with r hr
      exact hD.1 r hr
    · exact hTc.continuousAt (ho.mem_nhds hq)
    · exact hYc.continuousAt (ho.mem_nhds hq)
  rw [show (1 : ℕ∞ω) = 0+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen ho]
  refine ⟨fun q hq => (hd q hq).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  have hc : ContinuousOn (fun q : ℝ × E => (T q.1 q.2).coprod (Y q.1 q.2))
      (flowDomain F) := hTc.continuousLinearMapCoprod hYc
  exact hc.congr (fun q hq => (hd q hq).fderiv)

/-- The enlarged field is C¹ on exactly the original joint open set. -/
lemma contDiffOn_autonomize (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) :
    ContDiffOn ℝ 1 F.autonomize.eval F.autonomize.domain := by
  have h := ((contDiffOn_const (c := (1 : ℝ))).prodMk hF).prodMk (contDiffOn_const (c := (0 : P)))
  exact h.congr (fun q hq => (ParameterODE.autonomize_eval F q hq))

private lemma elapsed_cancel (I : OpenTimeInterval) (s : ℝ) :
    (I.elapsed (-s)).elapsed s = I := by
  have h : ((I.elapsed (-s)).elapsed s).carrier = I.carrier := by
    ext t
    simp [OpenTimeInterval.elapsed, TimeInterval.elapsed]
  cases I with
  | mk I hi =>
    cases I with
    | mk C hn ho =>
      simp only [OpenTimeInterval.elapsed, TimeInterval.elapsed] at h ⊢
      congr 2

/-- Canonical choices agree under autonomization on their entire actual
maximal intervals. Maximality is used in both directions. -/
lemma maximal_autonomization (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {s : ℝ} {ξ : E} {p : P} (hq : ((s,ξ),p) ∈ F.domain) :
    (flowInterval F.autonomize ((s,ξ),p)).carrier =
      ((parameterMaximalIntervalValue F s ξ p).elapsed s).carrier ∧
    ∀ h ∈ (flowInterval F.autonomize ((s,ξ),p)).carrier,
      flow F.autonomize h ((s,ξ),p) =
        ((s+h, parameterSolutionCurveValue F s ξ p (s+h)),p) := by
  have hLip := F.locallyLipschitzInState_of_contDiffOn hF
  have hG := contDiffOn_autonomize F hF
  have hGLip := F.autonomize.locallyLipschitzInState_of_contDiffOn hG
  let I := parameterMaximalIntervalValue F s ξ p
  let x := parameterSolutionCurveValue F s ξ p
  let J := flowInterval F.autonomize ((s,ξ),p)
  let y := fun h => flow F.autonomize h ((s,ξ),p)
  obtain ⟨hx,hs,hξ,hmax,hend,hr,hu⟩ := ParameterODE.canonical_solution F hLip s ξ p hq
  obtain ⟨hy,h0,hy0,hymax,hyend,hyr,hyu⟩ := ODE.canonical_solution F.autonomize.toODE
    hGLip 0 ((s,ξ),p) hq
  have hxP : IsClassicalParameterIVPOn F p I x s ξ :=
    (classicalParameterIVPOn_iff F p I x s ξ).mpr ⟨hx,hs,hξ⟩
  have hl := (autonomization_classical_lift_iff F p I x s ξ).mp hxP
  have hl' := (classicalAutonomousIVPOn_iff F.autonomize (I.elapsed s)
    (autonomizationLift s p x) 0 ((s,ξ),p)).mp hl
  have hsub := hyr (I.elapsed s) (autonomizationLift s p x) hl'
  let K := J.elapsed (-s)
  have hyA : IsClassicalAutonomousIVPOn F.autonomize J y 0 ((s,ξ),p) :=
    (classicalAutonomousIVPOn_iff F.autonomize J y 0 ((s,ξ),p)).mpr ⟨hy,h0,hy0⟩
  have hyK : IsAutonomousIVPOn F.autonomize (K.toTimeInterval.elapsed s) y 0 ((s,ξ),p) := by
    have hc := (classicalAutonomous_iff_solutionOn F.autonomize J y).mp hyA.1
    have he : K.elapsed s = J := elapsed_cancel J s
    change IsAutonomousIVPOn F.autonomize (K.elapsed s).toTimeInterval y 0 ((s,ξ),p)
    rw [he]
    exact ⟨hc,h0,hy0⟩
  have hrec := autonomization_recover F p K.toTimeInterval y s ξ hyK
  have hrecC : IsClassicalParameterIVPOn F p K (autonomizationRecover s y) s ξ :=
    ⟨(classicalParameter_iff_solutionOn F p K _).mpr hrec.1.1,hrec.1.2⟩
  have hback := hr K (autonomizationRecover s y)
    ((classicalParameterIVPOn_iff F p K _ s ξ).mp hrecC)
  have hJI : J.carrier ⊆ (I.elapsed s).carrier := by
    intro h hh
    have hK : s+h ∈ K.carrier := by
      simpa [K, OpenTimeInterval.elapsed, TimeInterval.elapsed] using hh
    exact hback.1 hK
  refine ⟨Subset.antisymm hJI hsub.1, ?_⟩
  intro h hh
  exact hsub.2 (hJI hh)

lemma autonomization_domain (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    (q : ℝ × ((ℝ × E) × P)) :
    q ∈ parameterSolutionDomainValue F ↔
      (q.1-q.2.1.1,q.2) ∈ flowDomain F.autonomize := by
  constructor
  · intro hq
    refine ⟨hq.1, ?_⟩
    rw [(maximal_autonomization F hF hq.1).1]
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using hq.2
  · intro hq
    refine ⟨hq.1, ?_⟩
    have ht := hq.2
    rw [(maximal_autonomization F hF hq.1).1] at ht
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using ht

lemma solution_eq_autonomized (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {q : ℝ × ((ℝ × E) × P)} (hq : q ∈ parameterSolutionDomainValue F) :
    solution F q = (flow F.autonomize (q.1-q.2.1.1) q.2).1.2 := by
  have ha := (autonomization_domain F hF q).mp hq
  have he := (maximal_autonomization F hF hq.1).2 _ ha.2
  have hv := (ParameterODE.solutionValue_on_domain F
    (F.locallyLipschitzInState_of_contDiffOn hF) q.1 q.2.1.1 q.2.1.2 q.2.2 hq).1
  change parameterSolutionValueValue F q.1 q.2.1.1 q.2.1.2 q.2.2 = _
  rw [he, hv]
  simp

/-- The solution map is jointly C¹ on its actual open maximal domain. -/
theorem joint_c1 : Specs.D13Unified.Ch06.C1Dependence.JointC1.{u,v} := by
  intro E _ _ _ P _ _ _ F hF
  have ho := Ch05.OpenDomain.open_domain F (F.locallyLipschitzInState_of_contDiffOn hF)
  refine ⟨ho, ?_⟩
  have hG := autonomous_joint_c1 F.autonomize (contDiffOn_autonomize F hF)
  have hchange : ContDiffOn ℝ 1
      (fun q : ℝ × ((ℝ × E) × P) => (q.1-q.2.1.1,q.2))
      (parameterSolutionDomainValue F) :=
    (contDiffOn_fst.sub contDiffOn_snd.fst.fst).prodMk contDiffOn_snd
  have hc := (hG.comp hchange (fun q hq => (autonomization_domain F hF q).mp hq)).fst.snd
  exact hc.congr (fun q hq => solution_eq_autonomized F hF hq)

/-- Terminal-time differentiation is the original equation on its actual domain. -/
theorem terminal_derivative : Specs.D13Unified.Ch06.C1Dependence.TerminalDerivative.{u,v} := by
  intro E _ _ _ P _ _ _ F hF t s ξ p ht
  have hx := ParameterODE.solutionValue_ivp F
    (F.locallyLipschitzInState_of_contDiffOn hF) s ξ p ht.1
  exact hx.1.2.2 t ht.2

/-- Fixed coordinate maps in the enlarged state, with its inherited norm. -/
def stateProjection : ((ℝ × E) × P) →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) P)

def clockProjection : ((ℝ × E) × P) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) P)

def stateInjection : E →L[ℝ] ((ℝ × E) × P) :=
  ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)).prod 0

def parameterInjection : P →L[ℝ] ((ℝ × E) × P) :=
  ((0 : P →L[ℝ] ℝ).prod (0 : P →L[ℝ] E)).prod (ContinuousLinearMap.id ℝ P)

lemma hasFDerivAt_state_insert (s : ℝ) (p : P) (ξ : E) :
    HasFDerivAt (fun η => ((s,η),p)) stateInjection ξ :=
  ((hasFDerivAt_const s ξ).prodMk (hasFDerivAt_id ξ)).prodMk (hasFDerivAt_const p ξ)

lemma hasFDerivAt_parameter_insert (s : ℝ) (ξ : E) (p : P) :
    HasFDerivAt (fun q => ((s,ξ),q)) parameterInjection p :=
  ((hasFDerivAt_const s p).prodMk (hasFDerivAt_const ξ p)).prodMk (hasFDerivAt_id p)

/-- The derivative of the enlarged vector field, on its actual domain. -/
lemma fderiv_autonomize (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) {q : (ℝ × E) × P} (hq : q ∈ F.domain) :
    fderiv ℝ F.autonomize.eval q =
      ((0 : ((ℝ × E) × P) →L[ℝ] ℝ).prod (fderiv ℝ (field F) q)).prod 0 := by
  have hd := (hF.contDiffAt (F.isOpen_domain.mem_nhds hq)).differentiableAt_one.hasFDerivAt
  have he : F.autonomize.eval =ᶠ[𝓝 q] (fun r => ((1, field F r), (0 : P))) := by
    filter_upwards [F.isOpen_domain.mem_nhds hq] with r hr
    exact ParameterODE.autonomize_eval F r hr
  exact (((hasFDerivAt_const (1 : ℝ) q).prodMk hd).prodMk
    (hasFDerivAt_const (0 : P) q)).congr_of_eventuallyEq he |>.fderiv

/-- Clock and parameter rows of the initial-state derivative are prescribed
by the clock and constant-parameter equations, not by an additional assumption. -/
lemma flow_derivative_coordinates (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {h : ℝ} {q : (ℝ × E) × P} (hq : (h,q) ∈ flowDomain F.autonomize) :
    let W := fderiv ℝ (fun r => flow F.autonomize h r) q
    clockProjection.comp W = (clockProjection : ((ℝ × E) × P) →L[ℝ] ℝ) ∧
    (ContinuousLinearMap.snd ℝ (ℝ × E) P).comp W = ContinuousLinearMap.snd ℝ (ℝ × E) P := by
  have hG := contDiffOn_autonomize F hF
  have hW := (maximal_domain_derivative F.autonomize hG).1 (h,q) hq
  have hn : ∀ᶠ r in 𝓝 q, (h,r) ∈ flowDomain F.autonomize :=
    (continuous_const.prodMk continuous_id).continuousAt
      ((isOpen_flowDomain F.autonomize hG).mem_nhds hq)
  have hec : (fun r => (flow F.autonomize h r).1.1) =ᶠ[𝓝 q] (fun r => r.1.1+h) := by
    filter_upwards [hn] with r hr
    exact congrArg (fun z : (ℝ × E) × P => z.1.1)
      ((maximal_autonomization F hF hr.1).2 h hr.2)
  have hep : (fun r => (flow F.autonomize h r).2) =ᶠ[𝓝 q] (fun r => r.2) := by
    filter_upwards [hn] with r hr
    have he := congrArg (fun z : (ℝ × E) × P => z.2) ((maximal_autonomization F hF hr.1).2 h hr.2)
    exact he
  have hc := (clockProjection (E := E) (P := P)).hasFDerivAt.comp q hW
  have hp := (ContinuousLinearMap.snd ℝ (ℝ × E) P).hasFDerivAt.comp q hW
  refine ⟨?_, ?_⟩
  · exact hc.unique (((clockProjection (E := E) (P := P)).hasFDerivAt.add_const h).congr_of_eventuallyEq hec)
  · exact hp.unique ((ContinuousLinearMap.snd ℝ (ℝ × E) P).hasFDerivAt.congr_of_eventuallyEq hep)

lemma state_derivative_autonomized (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    HasFDerivAt (fun η => solution F (t,((s,η),p)))
      (stateProjection.comp ((fderiv ℝ (fun r => flow F.autonomize (t-s) r) ((s,ξ),p)).comp
        stateInjection)) ξ := by
  have hW := (maximal_domain_derivative F.autonomize (contDiffOn_autonomize F hF)).1
    (t-s,((s,ξ),p)) ((autonomization_domain F hF _).mp hq)
  have hd := (stateProjection (E := E) (P := P)).hasFDerivAt.comp ξ
    (hW.comp ξ (hasFDerivAt_state_insert s p ξ))
  apply hd.congr_of_eventuallyEq
  have hn := (continuous_const.prodMk ((continuous_const.prodMk continuous_id).prodMk continuous_const)).continuousAt
    ((joint_c1 F hF).1.mem_nhds hq)
  filter_upwards [hn] with η hη
  exact solution_eq_autonomized F hF hη

lemma parameter_derivative_autonomized (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    HasFDerivAt (fun r => solution F (t,((s,ξ),r)))
      (stateProjection.comp ((fderiv ℝ (fun r => flow F.autonomize (t-s) r) ((s,ξ),p)).comp
        parameterInjection)) p := by
  have hW := (maximal_domain_derivative F.autonomize (contDiffOn_autonomize F hF)).1
    (t-s,((s,ξ),p)) ((autonomization_domain F hF _).mp hq)
  have hd := (stateProjection (E := E) (P := P)).hasFDerivAt.comp p
    (hW.comp p (hasFDerivAt_parameter_insert s ξ p))
  apply hd.congr_of_eventuallyEq
  have hn := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    ((joint_c1 F hF).1.mem_nhds hq)
  filter_upwards [hn] with r hr
  exact solution_eq_autonomized F hF hr

lemma stateCoefficient_eq (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    stateCoefficient F s ξ p t =
      (fderiv ℝ (field F) ((t,solution F (t,((s,ξ),p))),p)).comp stateInjection := by
  have hg := (ParameterODE.solutionValue_on_domain F
    (F.locallyLipschitzInState_of_contDiffOn hF) t s ξ p hq).2
  have hd := (hF.contDiffAt (F.isOpen_domain.mem_nhds hg)).differentiableAt_one.hasFDerivAt
  exact (hd.comp (solution F (t,((s,ξ),p)))
    (hasFDerivAt_state_insert t p (solution F (t,((s,ξ),p))))).fderiv

lemma parameterCoefficient_eq (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    parameterCoefficient F s ξ p t =
      (fderiv ℝ (field F) ((t,solution F (t,((s,ξ),p))),p)).comp parameterInjection := by
  have hg := (ParameterODE.solutionValue_on_domain F
    (F.locallyLipschitzInState_of_contDiffOn hF) t s ξ p hq).2
  have hd := (hF.contDiffAt (F.isOpen_domain.mem_nhds hg)).differentiableAt_one.hasFDerivAt
  exact (hd.comp _ (hasFDerivAt_parameter_insert t _ p)).fderiv

lemma autonomized_flow_value (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    flow F.autonomize (t-s) ((s,ξ),p) = ((t,solution F (t,((s,ξ),p))),p) := by
  have ha := (autonomization_domain F hF _).mp hq
  have he := (maximal_autonomization F hF hq.1).2 (t-s) ha.2
  have hs : s+(t-s)=t := by ring
  rw [hs] at he
  have hv := (ParameterODE.solutionValue_on_domain F
    (F.locallyLipschitzInState_of_contDiffOn hF) t s ξ p hq).1
  simpa only [solution, hv] using he

/-- Linear algebra of the state and constant-parameter columns of the enlarged
variation. Its clock row is zero and its parameter row is the identity. -/
lemma variation_columns (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    let W := fderiv ℝ (fun r => flow F.autonomize (t-s) r) ((s,ξ),p)
    (∀ v : E, W (stateInjection v) = stateInjection
      ((stateProjection : ((ℝ × E) × P) →L[ℝ] E) (W (stateInjection v)))) ∧
    (∀ v : P, W (parameterInjection v) = stateInjection
      ((stateProjection : ((ℝ × E) × P) →L[ℝ] E) (W (parameterInjection v))) + parameterInjection v) := by
  dsimp only
  let W := fderiv ℝ (fun r => flow F.autonomize (t-s) r) ((s,ξ),p)
  have hc := flow_derivative_coordinates F hF ((autonomization_domain F hF _).mp hq)
  constructor
  · intro v
    have hclock := congrArg (fun L : ((ℝ × E) × P) →L[ℝ] ℝ => L (stateInjection v)) hc.1
    have hparam := congrArg (fun L : ((ℝ × E) × P) →L[ℝ] P => L (stateInjection v)) hc.2
    apply Prod.ext
    · apply Prod.ext
      · simpa [clockProjection, stateInjection] using hclock
      · rfl
    · simpa [stateInjection] using hparam
  · intro v
    have hclock := congrArg (fun L : ((ℝ × E) × P) →L[ℝ] ℝ => L (parameterInjection v)) hc.1
    have hparam := congrArg (fun L : ((ℝ × E) × P) →L[ℝ] P => L (parameterInjection v)) hc.2
    apply Prod.ext
    · apply Prod.ext
      · simpa [clockProjection, stateInjection, parameterInjection] using hclock
      · simp [stateInjection, parameterInjection, stateProjection]
    · simpa [stateInjection, parameterInjection] using hparam

/-- Both variational differential equations follow from the already proved
full operator variation of the autonomous enlarged flow. -/
lemma variational_derivatives (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {t s : ℝ} {ξ : E} {p : P} (hq : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
    HasDerivAt (stateVariation F s ξ p)
      ((stateCoefficient F s ξ p t).comp (stateVariation F s ξ p t)) t ∧
    HasDerivAt (parameterVariation F s ξ p)
      ((stateCoefficient F s ξ p t).comp (parameterVariation F s ξ p t) +
        parameterCoefficient F s ξ p t) t := by
  let G := F.autonomize
  let q := ((s,ξ),p)
  let W : ℝ → ((ℝ × E) × P) →L[ℝ] ((ℝ × E) × P) :=
    fun r => fderiv ℝ (fun z => flow G (r-s) z) q
  let Vx := fun r => (stateProjection (E := E) (P := P)).comp ((W r).comp stateInjection)
  let Vp := fun r => (stateProjection (E := E) (P := P)).comp ((W r).comp parameterInjection)
  have hx (r : ℝ) (hr : (r,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
      stateVariation F s ξ p r = Vx r := (state_derivative_autonomized F hF hr).fderiv
  have hp (r : ℝ) (hr : (r,((s,ξ),p)) ∈ parameterSolutionDomainValue F) :
      parameterVariation F s ξ p r = Vp r := (parameter_derivative_autonomized F hF hr).fderiv
  have he := autonomized_flow_value F hF hq
  have hy := (ParameterODE.solutionValue_on_domain F
    (F.locallyLipschitzInState_of_contDiffOn hF) t s ξ p hq).2
  have hcols := variation_columns F hF hq
  have hcoef : coefficient G q (t-s) =
      ((0 : ((ℝ × E) × P) →L[ℝ] ℝ).prod
        (fderiv ℝ (field F) ((t,solution F (t,((s,ξ),p))),p))).prod 0 := by
    change fderiv ℝ F.autonomize.eval (flow F.autonomize (t-s) ((s,ξ),p)) = _
    rw [he]
    exact fderiv_autonomize F hF hy
  have hd := ((maximal_domain_derivative G (contDiffOn_autonomize F hF)).2.2 q hq.1).2.1
    (t-s) ((autonomization_domain F hF _).mp hq).2
  have hdW : HasDerivAt W ((coefficient G q (t-s)).comp (W t)) t := by
    simpa only [W, Function.comp_def, id_eq, one_smul] using
      hd.scomp t ((hasDerivAt_id t).sub_const s)
  have hdx : HasDerivAt Vx
      ((stateProjection (E := E) (P := P)).comp
        (((coefficient G q (t-s)).comp (W t)).comp stateInjection)) t := by
    simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, zero_add, add_zero]
      using (hasDerivAt_const t (stateProjection (E := E) (P := P))).clm_comp
        (hdW.clm_comp (hasDerivAt_const t (stateInjection (E := E) (P := P))))
  have hdp : HasDerivAt Vp
      ((stateProjection (E := E) (P := P)).comp
        (((coefficient G q (t-s)).comp (W t)).comp parameterInjection)) t := by
    simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, zero_add, add_zero]
      using (hasDerivAt_const t (stateProjection (E := E) (P := P))).clm_comp
        (hdW.clm_comp (hasDerivAt_const t (parameterInjection (E := E) (P := P))))
  have hex : (stateProjection (E := E) (P := P)).comp
      (((coefficient G q (t-s)).comp (W t)).comp stateInjection) =
      (stateCoefficient F s ξ p t).comp (stateVariation F s ξ p t) := by
    rw [hcoef, stateCoefficient_eq F hF hq, hx t hq]
    ext v
    change (fderiv ℝ (field F) _) (W t (stateInjection v)) =
      (fderiv ℝ (field F) _) (stateInjection ((stateProjection (E := E) (P := P)) (W t (stateInjection v))))
    rw [hcols.1 v]
    simp [stateInjection, stateProjection]
  have hep : (stateProjection (E := E) (P := P)).comp
      (((coefficient G q (t-s)).comp (W t)).comp parameterInjection) =
      (stateCoefficient F s ξ p t).comp (parameterVariation F s ξ p t) +
        parameterCoefficient F s ξ p t := by
    rw [hcoef, stateCoefficient_eq F hF hq, parameterCoefficient_eq F hF hq, hp t hq]
    ext v
    change (fderiv ℝ (field F) _) (W t (parameterInjection v)) =
      (fderiv ℝ (field F) _) (stateInjection ((stateProjection (E := E) (P := P)) (W t (parameterInjection v)))) +
        (fderiv ℝ (field F) _) (parameterInjection v)
    rw [hcols.2 v, map_add]
    simp [stateInjection, stateProjection, parameterInjection]
  have hn : ∀ᶠ r in 𝓝 t, (r,((s,ξ),p)) ∈ parameterSolutionDomainValue F :=
    (continuous_id.prodMk continuous_const).continuousAt ((joint_c1 F hF).1.mem_nhds hq)
  refine ⟨(hdx.congr_deriv hex).congr_of_eventuallyEq ?_,
    (hdp.congr_deriv hep).congr_of_eventuallyEq ?_⟩
  · filter_upwards [hn] with r hr
    exact hx r hr
  · filter_upwards [hn] with r hr
    exact hp r hr

lemma continuousOn_coefficients (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {s : ℝ} {ξ : E} {p : P} (hs : ((s,ξ),p) ∈ F.domain) :
    ContinuousOn (stateCoefficient F s ξ p) (parameterMaximalIntervalValue F s ξ p).carrier ∧
    ContinuousOn (parameterCoefficient F s ξ p) (parameterMaximalIntervalValue F s ξ p).carrier := by
  let I := parameterMaximalIntervalValue F s ξ p
  have hx := ParameterODE.solutionValue_ivp F (F.locallyLipschitzInState_of_contDiffOn hF) s ξ p hs
  have hg : ContinuousOn (fun r => ((r,solution F (r,((s,ξ),p))),p)) I.carrier :=
    (continuousOn_id.prodMk hx.1.1.continuousOn).prodMk continuousOn_const
  have hD := (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp hg hx.1.2.1
  refine ⟨(hD.clm_comp (continuousOn_const (c := stateInjection))).congr ?_,
    (hD.clm_comp (continuousOn_const (c := parameterInjection))).congr ?_⟩
  · intro t ht
    exact stateCoefficient_eq F hF ⟨hs,ht⟩
  · intro t ht
    exact parameterCoefficient_eq F hF ⟨hs,ht⟩

/-- Uniqueness for a continuous linear inhomogeneous equation on an actual
open interval follows by restriction to every compact enclosure. -/
lemma linear_uniqueness {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [CompleteSpace R] (I : OpenTimeInterval) {s : ℝ} (hs : s ∈ I.carrier)
    (A : ℝ → R →L[ℝ] R) (B : ℝ → R) (ζ : R)
    (hA : ContinuousOn A I.carrier) (hB : ContinuousOn B I.carrier)
    (U V : ℝ → R) (hUc : ContinuousOn U I.carrier) (hVc : ContinuousOn V I.carrier)
    (hU0 : U s = ζ) (hV0 : V s = ζ)
    (hUd : ∀ t ∈ I.carrier, HasDerivAt U (A t (U t) + B t) t)
    (hVd : ∀ t ∈ I.carrier, HasDerivAt V (A t (V t) + B t) t) :
    EqOn U V I.carrier := by
  intro t ht
  obtain ⟨a,b,hs',ht',hJ⟩ := Ch05.OpenDomain.compact_enclosure I hs ht
  have hsJ : s ∈ Icc a b := ⟨hs'.1.le,hs'.2.le⟩
  have hAJ := hA.mono hJ
  have hBJ := hB.mono hJ
  have hU := (LinearVolterra.differential_equivalence a b s A B ζ U hsJ hAJ hBJ).mpr
    ⟨hUc.mono hJ,hU0,fun r hr => (hUd r (hJ hr)).hasDerivWithinAt⟩
  have hV := (LinearVolterra.differential_equivalence a b s A B ζ V hsJ hAJ hBJ).mpr
    ⟨hVc.mono hJ,hV0,fun r hr => (hVd r (hJ hr)).hasDerivWithinAt⟩
  obtain ⟨W,hW,hu⟩ := LinearVolterra.existence a b s A B ζ hsJ hAJ hBJ
  exact (hu U hU ⟨ht'.1.le,ht'.2.le⟩).trans (hu V hV ⟨ht'.1.le,ht'.2.le⟩).symm

lemma variation_initial_values (F : ParameterODE E P)
    (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {s : ℝ} {ξ : E} {p : P} (hs : ((s,ξ),p) ∈ F.domain) :
    stateVariation F s ξ p s = ContinuousLinearMap.id ℝ E ∧
    parameterVariation F s ξ p s = 0 := by
  have hx := ParameterODE.solutionValue_ivp F (F.locallyLipschitzInState_of_contDiffOn hF) s ξ p hs
  have hq : (s,((s,ξ),p)) ∈ parameterSolutionDomainValue F := ⟨hs,hx.2.1⟩
  have hW0 := ((maximal_domain_derivative F.autonomize
    (contDiffOn_autonomize F hF)).2.2 ((s,ξ),p) hs).1
  constructor
  · change fderiv ℝ (fun η => solution F (s,((s,η),p))) ξ = _
    rw [(state_derivative_autonomized F hF hq).fderiv, sub_self, hW0]
    ext v
    rfl
  · change fderiv ℝ (fun r => solution F (s,((s,ξ),r))) p = _
    rw [(parameter_derivative_autonomized F hF hq).fderiv, sub_self, hW0]
    ext v
    rfl

/-- The state derivative exists and is the unique solution of Y′ = AY,
Y(s) = Id, throughout the canonical maximal interval. -/
theorem state_variation : Specs.D13Unified.Ch06.C1Dependence.StateVariation.{u,v} := by
  intro E _ _ _ P _ _ _ F hF s ξ p hs
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let I := parameterMaximalIntervalValue F s ξ p
  have hinit := variation_initial_values F hF hs
  have hdx (t : ℝ) (ht : t ∈ I.carrier) := (variational_derivatives F hF ⟨hs,ht⟩).1
  refine ⟨hinit.1, ?_, ?_⟩
  · intro t ht
    exact ⟨(state_derivative_autonomized F hF ⟨hs,ht⟩).differentiableAt.hasFDerivAt,hdx t ht⟩
  · intro Y hY hY0 hYd
    have hAc := (continuousOn_coefficients F hF hs).1
    have hA : ContinuousOn (fun t => ContinuousLinearMap.compL ℝ E E E
        (stateCoefficient F s ξ p t)) I.carrier :=
      (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hAc
    have hVc : ContinuousOn (stateVariation F s ξ p) I.carrier :=
      fun t ht => (hdx t ht).continuousAt.continuousWithinAt
    have hsI := (ParameterODE.solutionValue_ivp F
      (F.locallyLipschitzInState_of_contDiffOn hF) s ξ p hs).2.1
    apply linear_uniqueness I hsI _ (fun _ => 0) (ContinuousLinearMap.id ℝ E)
      hA continuousOn_const Y (stateVariation F s ξ p) hY hVc hY0 hinit.1
    · intro t ht
      simpa only [ContinuousLinearMap.compL_apply, add_zero] using hYd t ht
    · intro t ht
      simpa only [ContinuousLinearMap.compL_apply, add_zero] using hdx t ht

/-- The parameter derivative exists and is the unique solution of
Z′ = AZ + Dₚf, Z(s) = 0, on the same full maximal interval. -/
theorem parameter_variation : Specs.D13Unified.Ch06.C1Dependence.ParameterVariation.{u,v} := by
  intro E _ _ _ P _ _ _ F hF s ξ p hs
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let I := parameterMaximalIntervalValue F s ξ p
  have hinit := variation_initial_values F hF hs
  have hdp (t : ℝ) (ht : t ∈ I.carrier) := (variational_derivatives F hF ⟨hs,ht⟩).2
  refine ⟨hinit.2, ?_, ?_⟩
  · intro t ht
    exact ⟨(parameter_derivative_autonomized F hF ⟨hs,ht⟩).differentiableAt.hasFDerivAt,hdp t ht⟩
  · intro Z hZ hZ0 hZd
    have hcoeff := continuousOn_coefficients F hF hs
    have hA : ContinuousOn (fun t => ContinuousLinearMap.compL ℝ P E E
        (stateCoefficient F s ξ p t)) I.carrier :=
      (ContinuousLinearMap.compL ℝ P E E).continuous.comp_continuousOn hcoeff.1
    have hVc : ContinuousOn (parameterVariation F s ξ p) I.carrier :=
      fun t ht => (hdp t ht).continuousAt.continuousWithinAt
    have hsI := (ParameterODE.solutionValue_ivp F
      (F.locallyLipschitzInState_of_contDiffOn hF) s ξ p hs).2.1
    apply linear_uniqueness I hsI _ (parameterCoefficient F s ξ p) 0
      hA hcoeff.2 Z (parameterVariation F s ξ p) hZ hVc hZ0 hinit.2
    · intro t ht
      simpa only [ContinuousLinearMap.compL_apply] using hZd t ht
    · intro t ht
      simpa only [ContinuousLinearMap.compL_apply] using hdp t ht

/-- All variational derivatives are jointly continuous in the terminal time,
starting time, initial state and parameter on the actual maximal domain. -/
theorem continuous_variations : Specs.D13Unified.Ch06.C1Dependence.ContinuousVariations.{u,v} := by
  intro E _ _ _ P _ _ _ F hF
  have hc := joint_c1 F hF
  have hD := hc.2.continuousOn_fderiv_of_isOpen hc.1 le_rfl
  refine ⟨(hD.clm_comp (continuousOn_const (c :=
    (0 : E →L[ℝ] ℝ).prod (stateInjection (E := E) (P := P))))).congr ?_,
    (hD.clm_comp (continuousOn_const (c :=
      (0 : P →L[ℝ] ℝ).prod (parameterInjection (E := E) (P := P))))).congr ?_⟩
  · intro q hq
    have hd := (hc.2.contDiffAt (hc.1.mem_nhds hq)).differentiableAt_one.hasFDerivAt
    exact (hd.comp q.2.1.2 ((hasFDerivAt_const q.1 q.2.1.2).prodMk
      (hasFDerivAt_state_insert q.2.1.1 q.2.2 q.2.1.2))).fderiv
  · intro q hq
    have hd := (hc.2.contDiffAt (hc.1.mem_nhds hq)).differentiableAt_one.hasFDerivAt
    exact (hd.comp q.2.2 ((hasFDerivAt_const q.1 q.2.2).prodMk
      (hasFDerivAt_parameter_insert q.2.1.1 q.2.1.2 q.2.2))).fderiv

end D13Unified.Ch06.C1Dependence
