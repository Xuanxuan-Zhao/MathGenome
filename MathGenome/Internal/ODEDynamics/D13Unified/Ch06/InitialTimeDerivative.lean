import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.InitialTimeDerivative
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.C1Dependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.Rebase

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch06.InitialTimeDerivative
open C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u v

/-- Differentiate the rebasing identity along the original trajectory. -/
theorem starting_time_derivative :
    Specs.D13Unified.Ch06.InitialTimeDerivative.StartingTimeDerivative.{u,v} := by
  intro E _ _ _ P _ _ _ F hF t s ξ p ht
  have hLip := F.locallyLipschitzInState_of_contDiffOn hF
  have hx := ParameterODE.solutionValue_ivp F hLip s ξ p ht.1
  have hinit : solution F (s,((s,ξ),p)) = ξ := hx.2.2
  let g : ℝ × E → E := fun q => solution F (t,((q.1,q.2),p))
  let D := fderiv ℝ g (s,ξ)
  have hj := joint_c1 F hF
  have hd := (hj.2.contDiffAt (hj.1.mem_nhds ht)).differentiableAt_one
  have hi : DifferentiableAt ℝ (fun q : ℝ × E => (t, (q,p))) (s,ξ) := by
    fun_prop
  have hgdiff : DifferentiableAt ℝ g (s,ξ) := by
    simpa only [g, Function.comp_def] using hd.comp (s,ξ) hi
  have hg : HasFDerivAt g D (s,ξ) := hgdiff.hasFDerivAt
  have hv : HasDerivAt (fun r => solution F (r,((s,ξ),p)))
      (parameterEvalValue F s ξ p) s := by
    simpa only [hinit] using terminal_derivative F hF s s ξ p ⟨ht.1,hx.2.1⟩
  have hpath := (hasDerivAt_id s).prodMk hv
  have hc := hg.comp_hasDerivAt_of_eq s hpath (by simp only [hinit, id_eq])
  have heq : (fun r => g (r, solution F (r,((s,ξ),p)))) =ᶠ[𝓝 s]
      (fun _ => solution F (t,((s,ξ),p))) := by
    filter_upwards [(parameterMaximalIntervalValue F s ξ p).isOpen.mem_nhds hx.2.1]
      with r hr
    exact (ParameterODE.rebase F hLip s ξ p ht.1 r hr
      (solution F (r,((s,ξ),p))) rfl).2 t ht.2
  have hz : D (1,parameterEvalValue F s ξ p) = 0 := by
    have hc' : HasDerivAt (fun r => g (r,solution F (r,((s,ξ),p))))
        (D (1,parameterEvalValue F s ξ p)) s := by
      simpa only [Function.comp_def, id_eq] using hc
    exact (hc'.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s _)
  have hs : HasDerivAt (fun r => g (r,ξ)) (D (1,0)) s := by
    simpa only [Function.comp_def, id_eq] using
      hg.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s ξ))
  have hstate : HasFDerivAt (fun η => g (s,η))
      (D.comp ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) ξ :=
    hg.comp ξ ((hasFDerivAt_const s ξ).prodMk (hasFDerivAt_id ξ))
  have hY : (stateVariation F s ξ p t) (parameterEvalValue F s ξ p) =
      D (0,parameterEvalValue F s ξ p) := by
    change (fderiv ℝ (fun η => g (s,η)) ξ) _ = _
    rw [hstate.fderiv]
    rfl
  have hresult : D (1,0) = -(stateVariation F s ξ p t) (parameterEvalValue F s ξ p) := by
    rw [hY]
    apply eq_neg_iff_add_eq_zero.mpr
    rw [← D.map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hz
  exact hresult ▸ hs

@[simp] lemma timeField_eval (t x p : ℝ) : parameterEvalValue timeField t x p = t := by
  simp [parameterEvalValue, timeField]

lemma timeField_c1 : ContDiffOn ℝ 1 (field timeField) timeField.domain := by
  have he : field timeField = fun q : (ℝ × ℝ) × ℝ => q.1.1 := by
    funext q
    exact timeField_eval _ _ _
  rw [he]
  exact contDiffOn_fst.fst

lemma explicitSolution_terminal (t s ξ : ℝ) :
    HasDerivAt (fun r => explicitSolution r s ξ) t t := by
  have h : HasDerivAt (fun r : ℝ => ξ + (r^2 - s^2) / 2)
      (0 + (2 * t^(2-1) * 1) / 2) t :=
    (hasDerivAt_const t ξ).add
      (((hasDerivAt_id t).pow 2).sub_const (s^2) |>.div_const 2)
  exact h.congr_deriv (by ring)

lemma explicitSolution_start (t s ξ : ℝ) :
    HasDerivAt (fun r => explicitSolution t r ξ) (-s) s := by
  have h : HasDerivAt (fun r : ℝ => ξ + (t^2 - r^2) / 2)
      (0 + (0 - 2 * s^(2-1) * 1) / 2) s :=
    (hasDerivAt_const s ξ).add
      (((hasDerivAt_const s (t^2)).sub ((hasDerivAt_id s).pow 2)).div_const 2)
  exact h.congr_deriv (by ring)

/-- The explicit polynomial curve fills the entire canonical maximal interval. -/
lemma timeField_solution (t s ξ p : ℝ) :
    (t,((s,ξ),p)) ∈ parameterSolutionDomainValue timeField ∧
    solution timeField (t,((s,ξ),p)) = explicitSolution t s ξ := by
  let I : OpenTimeInterval := ⟨⟨univ,univ_nonempty,ordConnected_univ⟩,isOpen_univ⟩
  have hLip := timeField.locallyLipschitzInState_of_contDiffOn timeField_c1
  have hx : IsClassicalParameterIVPOn timeField p I (fun r => explicitSolution r s ξ) s ξ := by
    refine ⟨⟨?_, ?_, ?_⟩, mem_univ s, ?_⟩
    · dsimp [explicitSolution]
      fun_prop
    · intro r hr
      exact mem_univ _
    · intro r hr
      simpa only [timeField_eval] using explicitSolution_terminal r s ξ
    · simp [explicitSolution]
  obtain ⟨_,_,_,_,_,hcover,_⟩ := ParameterODE.canonical_solution timeField hLip s ξ p (mem_univ _)
  have hc := hcover I (fun r => explicitSolution r s ξ)
    ((classicalParameterIVPOn_iff timeField p I _ s ξ).mp hx)
  have ht : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue timeField :=
    ⟨mem_univ _, hc.1 (mem_univ t)⟩
  exact ⟨ht, ((ParameterODE.solutionValue_on_domain timeField hLip t s ξ p ht).1).trans
    (hc.2 (mem_univ t))⟩

/-- x′ = t has starting derivative −s, which differs from −t for s ≠ t. -/
theorem nonautonomous_example :
    Specs.D13Unified.Ch06.InitialTimeDerivative.NonautonomousExample := by
  refine ⟨timeField_c1, ?_⟩
  intro t s ξ p
  have hs : HasDerivAt (fun r => solution timeField (t,((r,ξ),p))) (-s) s := by
    have he : (fun r => solution timeField (t,((r,ξ),p))) =
        fun r => explicitSolution t r ξ := funext (fun r => (timeField_solution t r ξ p).2)
    rw [he]
    exact explicitSolution_start t s ξ
  have ht : HasDerivAt (fun r => solution timeField (r,((s,ξ),p))) t t := by
    have he : (fun r => solution timeField (r,((s,ξ),p))) =
        fun r => explicitSolution r s ξ := funext (fun r => (timeField_solution r s ξ p).2)
    rw [he]
    exact explicitSolution_terminal t s ξ
  refine ⟨(timeField_solution t s ξ p).1, (timeField_solution t s ξ p).2, hs, ht, ?_⟩
  intro hst
  rw [hs.deriv, timeField_eval]
  simpa only [ne_eq, neg_inj] using hst

end D13Unified.Ch06.InitialTimeDerivative
