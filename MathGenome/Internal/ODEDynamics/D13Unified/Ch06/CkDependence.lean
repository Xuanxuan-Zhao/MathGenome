import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.C1Dependence

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch06.CkDependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open StateDerivative C1Dependence

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The tangent system on Ω × End(E), with no bound on its operator coordinate. -/
def tangentField (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain) :
    AutonomousODE (E × (E →L[ℝ] E)) where
  domain := Prod.fst ⁻¹' F.domain
  isOpen_domain := F.isOpen_domain.preimage continuous_fst
  field := fun q => (F.eval q.val.1, (fderiv ℝ F.eval q.val.1).comp q.val.2)
  continuous_field := by
    have hc : ContinuousOn (fun q : E × (E →L[ℝ] E) => fderiv ℝ F.eval q.1)
        (Prod.fst ⁻¹' F.domain) := (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
      continuousOn_fst (fun q hq => hq)
    have hb : ContinuousOn (fun q : E × (E →L[ℝ] E) => F.eval q.1)
        (Prod.fst ⁻¹' F.domain) := hF.continuousOn.comp continuousOn_fst (fun q hq => hq)
    exact continuousOn_iff_continuous_domRestrict.mp (hb.prodMk (hc.clm_comp continuousOn_snd))

lemma tangentField_eval (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {q : E × (E →L[ℝ] E)} (hq : q.1 ∈ F.domain) :
    (tangentField F hF).eval q = (F.eval q.1, (fderiv ℝ F.eval q.1).comp q.2) := by
  simp [AutonomousODE.eval, autonomousEvalValue, tangentField, hq]

lemma contDiffOn_tangentField (k : ℕ) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (hFk : ContDiffOn ℝ ((k : ℕ∞ω)+1) F.eval F.domain) :
    ContDiffOn ℝ k (tangentField F hF).eval (tangentField F hF).domain := by
  have hd : ContDiffOn ℝ k (fderiv ℝ F.eval) F.domain :=
    hFk.fderiv_of_isOpen F.isOpen_domain le_rfl
  have hc : ContDiffOn ℝ k (fun q : E × (E →L[ℝ] E) => fderiv ℝ F.eval q.1)
      (Prod.fst ⁻¹' F.domain) := hd.comp contDiffOn_fst (fun q hq => hq)
  have hb : ContDiffOn ℝ k (fun q : E × (E →L[ℝ] E) => F.eval q.1)
      (Prod.fst ⁻¹' F.domain) := (hFk.of_le (show (k : ℕ∞ω) ≤ k+1 from le_self_add)).comp
    contDiffOn_fst (fun q hq => hq)
  exact (hb.prodMk (hc.clm_comp contDiffOn_snd)).congr
    (fun q hq => tangentField_eval F hF hq)

/-- The lifted trajectory reaches every allowed original terminal time. This
uses a Volterra solution on a compact enclosure, not a global existence claim. -/
lemma tangent_flow (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (hG : ContDiffOn ℝ 1 (tangentField F hF).eval (tangentField F hF).domain)
    {q : ℝ × E} (hq : q ∈ flowDomain F) :
    (q.1,(q.2,ContinuousLinearMap.id ℝ E)) ∈ flowDomain (tangentField F hF) ∧
      (flow (tangentField F hF) q.1 (q.2,ContinuousLinearMap.id ℝ E)).2 =
        fderiv ℝ (fun η => flow F q.1 η) q.2 := by
  have hx := flow_ivp F hF hq.1
  obtain ⟨a,b,h0,ht,hJ⟩ := Ch05.OpenDomain.compact_enclosure
    (flowInterval F q.2) hx.2.1 hq.2
  obtain ⟨Y,hY,hY0,hYd,hu⟩ := variational_existence F hF q.2 hq.1 a b
    ⟨h0.1.le,h0.2.le⟩ hJ
  let K : OpenTimeInterval :=
    ⟨⟨Ioo a b, ⟨0,h0⟩, ordConnected_Ioo⟩, isOpen_Ioo⟩
  have hsub : K.carrier ⊆ Icc a b := Ioo_subset_Icc_self
  have hYd' (r : ℝ) (hr : r ∈ K.carrier) :
      HasDerivAt Y ((coefficient F q.2 r).comp (Y r)) r :=
    (hYd r (hsub hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hYc1 : ContDiffOn ℝ 1 Y K.carrier := by
    rw [show (1 : ℕ∞ω) = 0+1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen K.isOpen]
    refine ⟨fun r hr => (hYd' r hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact ((continuousOn_coefficient F hF hq.1 hJ).clm_comp hY.1).mono hsub |>.congr
      (fun r hr => (hYd' r hr).deriv)
  let z : ℝ → E × (E →L[ℝ] E) := fun r => (flow F r q.2,Y r)
  have hz : classicalIVPOnValue (tangentField F hF).toODE K z 0
      (q.2,ContinuousLinearMap.id ℝ E) := by
    refine ⟨⟨(hx.1.1.mono (hsub.trans hJ)).prodMk hYc1, ?_, ?_⟩, h0, ?_⟩
    · intro r hr
      exact hx.1.2.1 r (hJ (hsub hr))
    · intro r hr
      have hxr := hx.1.2.2 r (hJ (hsub hr))
      have hmem : flow F r q.2 ∈ F.domain := hx.1.2.1 r (hJ (hsub hr))
      have he := tangentField_eval F hF (q := (flow F r q.2,Y r)) hmem
      rw [AutonomousODE.toODE_eval, he]
      exact hxr.prodMk (hYd' r hr)
    · exact Prod.ext hx.2.2 hY0
  have hcan := ODE.canonical_solution (tangentField F hF).toODE
    ((tangentField F hF).locallyLipschitzInState_of_contDiffOn hG)
    0 (q.2,ContinuousLinearMap.id ℝ E) hq.1
  obtain ⟨_,_,_,_,_,hr,_⟩ := hcan
  have he := hr K z hz
  refine ⟨⟨hq.1,he.1 ht⟩, ?_⟩
  have hval := congrArg Prod.snd (he.2 ht)
  exact hval.trans (state_derivative F hF q.2 hq.1 a b ⟨h0.1.le,h0.2.le⟩
    hJ Y hY q.1 (hsub ht)).fderiv.symm

/-- The full derivative is assembled from its time and initial-state parts. -/
lemma flow_fderiv (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {q : ℝ × E} (hq : q ∈ flowDomain F) :
    fderiv ℝ (fun r : ℝ × E => flow F r.1 r.2) q =
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F q.1 q.2))).comp
        (ContinuousLinearMap.fst ℝ ℝ E)) +
      ((fderiv ℝ (fun η => flow F q.1 η) q.2).comp (ContinuousLinearMap.snd ℝ ℝ E)) := by
  have ho := isOpen_flowDomain F hF
  have hd := maximal_domain_derivative F hF
  have ht : ContinuousOn
      (fun r : ℝ × E => (ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F r.1 r.2)))
      (flowDomain F) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      (hF.continuousOn.comp (continuousOn_flow F hF)
        (fun r hr => (flow_ivp F hF hr.1).1.2.1 r.1 hr.2))
  apply HasFDerivAt.fderiv
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod (f := fun t ξ => flow F t ξ)
    (f₁ := fun t ξ => (ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F t ξ)))
    (f₂ := fun t ξ => fderiv ℝ (fun η => flow F t η) ξ)
  · filter_upwards [ho.mem_nhds hq] with r hr
    exact ((flow_ivp F hF hr.1).1.2.2 r.1 hr.2).hasFDerivAt
  · filter_upwards [ho.mem_nhds hq] with r hr
    exact hd.1 r hr
  · exact ht.continuousAt (ho.mem_nhds hq)
  · exact hd.2.1.continuousAt (ho.mem_nhds hq)

/-- Induction is uniform in the state space, so it applies to the tangent
system in the successor step. -/
theorem autonomous_joint_ck : ∀ (k : ℕ), 1 ≤ k →
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (F : AutonomousODE E), ContDiffOn ℝ k F.eval F.domain →
      ContDiffOn ℝ k (fun q : ℝ × E => flow F q.1 q.2) (flowDomain F) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk E _ _ _ F hF
    by_cases hk0 : k = 0
    · subst k
      exact autonomous_joint_c1 F hF
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
    have hFk : ContDiffOn ℝ k F.eval F.domain := hF.of_le (by exact_mod_cast Nat.le_succ k)
    have hFk' : ContDiffOn ℝ ((k : ℕ∞ω)+1) F.eval F.domain := by
      simpa only [Nat.cast_add, Nat.cast_one] using hF
    let G := tangentField F hF1
    have hGk : ContDiffOn ℝ k G.eval G.domain := contDiffOn_tangentField k F hF1 hFk'
    have hG1 : ContDiffOn ℝ 1 G.eval G.domain := hGk.of_le (by exact_mod_cast hk1)
    have hf := ih hk1 F hFk
    have hg := ih hk1 G hGk
    have hchange : ContDiffOn ℝ k
        (fun q : ℝ × E => (q.1,(q.2,ContinuousLinearMap.id ℝ E))) (flowDomain F) :=
      contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)
    have hvar := (hg.comp hchange (fun q hq => (tangent_flow F hF1 hG1 hq).1)).snd
    have hstate : ContDiffOn ℝ k
        (fun q : ℝ × E => fderiv ℝ (fun η => flow F q.1 η) q.2) (flowDomain F) :=
      hvar.congr (fun q hq => (tangent_flow F hF1 hG1 hq).2.symm)
    have htime : ContDiffOn ℝ k
        (fun q : ℝ × E => (ContinuousLinearMap.id ℝ ℝ).smulRight (F.eval (flow F q.1 q.2)))
        (flowDomain F) :=
      contDiffOn_const.smulRight (hFk.comp hf
        (fun q hq => (flow_ivp F hF1 hq.1).1.2.1 q.1 hq.2))
    have hd : ContDiffOn ℝ k (fderiv ℝ (fun q : ℝ × E => flow F q.1 q.2))
        (flowDomain F) :=
      ((htime.clm_comp contDiffOn_const).add (hstate.clm_comp contDiffOn_const)).congr
        (fun q hq => flow_fderiv F hF1 hq)
    have hc : ContDiffOn ℝ ((k : ℕ∞ω)+1)
        (fun q : ℝ × E => flow F q.1 q.2) (flowDomain F) :=
      (contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_flowDomain F hF1)).mpr
        ⟨(autonomous_joint_c1 F hF1).differentiableOn (by simp), by simp, hd⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hc

theorem joint_ck : Specs.D13Unified.Ch06.CkDependence.JointCk.{u,v} := by
  intro E _ _ _ P _ _ _ k hk F hF
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by exact_mod_cast hk)
  refine ⟨(joint_c1 F hF1).1, ?_⟩
  have hG : ContDiffOn ℝ k F.autonomize.eval F.autonomize.domain := by
    exact (((contDiffOn_const (c := (1 : ℝ))).prodMk hF).prodMk
      (contDiffOn_const (c := (0 : P)))).congr
        (fun q hq => ParameterODE.autonomize_eval F q hq)
  have hchange : ContDiffOn ℝ k
      (fun q : ℝ × ((ℝ × E) × P) => (q.1-q.2.1.1,q.2))
      (parameterSolutionDomainValue F) :=
    (contDiffOn_fst.sub contDiffOn_snd.fst.fst).prodMk contDiffOn_snd
  have hc := ((autonomous_joint_ck k hk F.autonomize hG).comp hchange
    (fun q hq => (autonomization_domain F hF1 q).mp hq)).fst.snd
  exact hc.congr (fun q hq => solution_eq_autonomized F hF1 hq)

theorem terminal_ck : Specs.D13Unified.Ch06.CkDependence.TerminalCk.{u,v} := by
  intro E _ _ _ P _ _ _ k hk F hF
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by exact_mod_cast hk)
  have hd (q : ℝ × ((ℝ × E) × P)) (hq : q ∈ parameterSolutionDomainValue F) :
      HasDerivAt (fun t => solution F (t,q.2))
        (field F ((q.1,solution F q),q.2.2)) q.1 :=
    terminal_derivative F hF1 q.1 q.2.1.1 q.2.1.2 q.2.2 hq
  refine ⟨hd, ?_⟩
  have hc := hF.comp ((contDiffOn_fst.prodMk (joint_ck k hk F hF).2).prodMk
    contDiffOn_snd.snd) (fun q hq => (ParameterODE.solutionValue_on_domain F
      (F.locallyLipschitzInState_of_contDiffOn hF1) q.1 q.2.1.1 q.2.1.2 q.2.2 hq).2)
  exact hc.congr (fun q hq => (hd q hq).deriv)

theorem joint_smooth : Specs.D13Unified.Ch06.CkDependence.JointSmooth.{u,v} := by
  intro E _ _ _ P _ _ _ F hF
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by simp)
  refine ⟨(joint_c1 F hF1).1, ?_⟩
  rw [contDiffOn_infty]
  intro k
  by_cases hk : k = 0
  · subst k
    exact (joint_c1 F hF1).2.of_le (by simp)
  · exact (joint_ck k (Nat.one_le_iff_ne_zero.mpr hk) F (hF.of_le (by simp))).2

end D13Unified.Ch06.CkDependence
