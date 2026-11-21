import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence

/-! The partial autonomous flow, on its actual maximal domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch11.Flow
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch11.Flow
open Ch06.StateDerivative Ch06.C1Dependence
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem flow_regularity : Regularity.{u} := by
  intro E _ _ _ k hk F hF
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  exact ⟨isOpen_flowDomain F hF1, Ch06.CkDependence.autonomous_joint_ck k hk F hF,
    fun q hq => (flow_ivp F hF1 hq.1).1.2.1 q.1 hq.2⟩

theorem flow_zero : InitialValue.{u} := by
  intro E _ _ _ F hF x hx
  have h := flow_ivp F hF hx
  exact ⟨⟨hx,h.2.1⟩,h.2.2⟩

omit [FiniteDimensional ℝ E] in
/-- Translating time preserves the autonomous equation on precisely the
translated open interval. No values outside the interval are used. -/
lemma shift_solution (F : AutonomousODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (hx : classicalSolutionOnValue F.toODE I x) (s : ℝ) :
    classicalSolutionOnValue F.toODE (I.elapsed s) (fun t => x (s+t)) := by
  refine ⟨hx.1.comp (contDiffOn_const.add contDiffOn_id) (fun t ht => ht),
    fun t ht => hx.2.1 (s+t) ht, ?_⟩
  intro t ht
  have hd := (hx.2.2 (s+t) ht).scomp t ((hasDerivAt_id t).const_add s)
  convert hd using 1 <;> simp [Function.comp_def, AutonomousODE.toODE_eval]

/-- Two coverage applications establish both inclusions of maximal intervals. -/
theorem flow_translation : Translation.{u} := by
  intro E _ _ _ F hF x hx s hs
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  have hcan := ODE.canonical_solution F.toODE hL 0 x hx
  have hX := flow_ivp F hF hx
  have hη : flow F s x ∈ F.domain := hX.1.2.1 s hs
  have hY := flow_ivp F hF hη
  have hcanY := ODE.canonical_solution F.toODE hL 0 (flow F s x) hη
  have hshift : classicalIVPOnValue F.toODE ((flowInterval F x).elapsed s)
      (fun t => flow F (s+t) x) 0 (flow F s x) :=
    ⟨shift_solution F _ _ hX.1 s, by simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed],
      by simp⟩
  have hsub := hcanY.2.2.2.2.2.1 _ _ hshift
  change ((flowInterval F x).elapsed s).carrier ⊆
      (flowInterval F (flow F s x)).carrier ∧
    EqOn (fun t => flow F t (flow F s x)) (fun t => flow F (s+t) x)
      ((flowInterval F x).elapsed s).carrier at hsub
  have hm : -s ∈ ((flowInterval F x).elapsed s).carrier := by
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using hX.2.1
  have hback0 : flow F (-s) (flow F s x) = x := by
    exact (hsub.2 hm).trans (by simpa using hX.2.2)
  have hback : classicalIVPOnValue F.toODE
      ((flowInterval F (flow F s x)).elapsed (-s))
      (fun t => flow F (-s+t) (flow F s x)) 0 x := by
    refine ⟨shift_solution F _ _ hY.1 (-s), ?_, ?_⟩
    · simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using hsub.1 hm
    · simpa using hback0
  have hsubBack := hcan.2.2.2.2.2.1 _ _ hback
  change ((flowInterval F (flow F s x)).elapsed (-s)).carrier ⊆
      (flowInterval F x).carrier ∧ _ at hsubBack
  have hI : (flowInterval F (flow F s x)).carrier =
      {t : ℝ | t+s ∈ (flowInterval F x).carrier} := by
    apply Subset.antisymm
    · intro t ht
      have hb : t+s ∈ ((flowInterval F (flow F s x)).elapsed (-s)).carrier := by
        simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using ht
      exact hsubBack.1 hb
    · intro t ht
      apply hsub.1
      simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed, add_comm] using ht
  refine ⟨hI, ?_⟩
  intro t ht
  have ht' : t ∈ ((flowInterval F x).elapsed s).carrier := by
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed, add_comm] using ht
  simpa only [add_comm s t] using hsub.2 ht'

lemma isOpen_timeDomain (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    (t : ℝ) : IsOpen (timeDomainValue F t) :=
  (isOpen_flowDomain F hF).preimage (continuous_const.prodMk continuous_id)

lemma contDiffOn_timeMap (k : ℕ) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) (t : ℝ) :
    ContDiffOn ℝ k (flow F t) (timeDomainValue F t) := by
  exact (Ch06.CkDependence.autonomous_joint_ck k hk F hF).comp
    (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)

/-- Each allowed forward trajectory can be retraced for exactly the opposite
elapsed time; the terminal point is admissible initial data. -/
lemma reverse_flow (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {t : ℝ} {x : E} (hx : x ∈ timeDomainValue F t) :
    flow F t x ∈ timeDomainValue F (-t) ∧ flow F (-t) (flow F t x) = x := by
  have hX := flow_ivp F hF hx.1
  have hη : flow F t x ∈ F.domain := hX.1.2.1 t hx.2
  have hT := flow_translation F hF x hx.1 t hx.2
  have hzero : -t+t ∈ (flowInterval F x).carrier := by simpa using hX.2.1
  refine ⟨⟨hη, ?_⟩, ?_⟩
  · rw [hT.1]
    exact hzero
  · exact (hT.2 (-t) hzero).trans (by simpa using hX.2.2)

theorem time_diffeomorphism : TimeDiffeomorphism.{u} := by
  intro E _ _ _ k hk F hF t
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have ho := isOpen_timeDomain F hF1 t
  have hor := isOpen_timeDomain F hF1 (-t)
  have hc := contDiffOn_timeMap k hk F hF t
  have hcr := contDiffOn_timeMap k hk F hF (-t)
  have hrev (y : E) (hy : y ∈ timeDomainValue F (-t)) :
      flow F (-t) y ∈ timeDomainValue F t ∧ flow F t (flow F (-t) y) = y := by
    simpa only [neg_neg] using reverse_flow F hF1 hy
  have hi : (flow F t) '' timeDomainValue F t = timeDomainValue F (-t) := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (reverse_flow F hF1 hx).1
    · intro y hy
      exact ⟨_,(hrev y hy).1,(hrev y hy).2⟩
  let e : OpenPartialHomeomorph E E :=
    { toFun := flow F t
      invFun := flow F (-t)
      source := timeDomainValue F t
      target := timeDomainValue F (-t)
      map_source' := fun _ hx => (reverse_flow F hF1 hx).1
      map_target' := fun y hy => (hrev y hy).1
      left_inv' := fun _ hx => (reverse_flow F hF1 hx).2
      right_inv' := fun y hy => (hrev y hy).2
      continuousOn_toFun := hc.continuousOn
      continuousOn_invFun := hcr.continuousOn
      open_source := ho
      open_target := hor }
  exact ⟨ho,hor,hi,e,rfl,rfl,rfl,rfl,hc,hcr⟩

/-- Differentiating the time-shift identity at zero transports the velocity.
The identity holds on a neighborhood of zero by openness of the lifespan. -/
theorem flow_pushforward : Pushforward.{u} := by
  intro E _ _ _ F hF q hq
  have hX := flow_ivp F hF hq.1
  have hzero : flow F 0 q.2 = q.2 := hX.2.2
  have hstate := (maximal_domain_derivative F hF).1 q hq
  have hinner : HasDerivAt (fun s => flow F s q.2) (F.eval q.2) 0 := by
    simpa only [AutonomousODE.toODE_eval, hzero] using hX.1.2.2 0 hX.2.1
  have hstate' : HasFDerivAt (flow F q.1)
      (fderiv ℝ (flow F q.1) q.2) (flow F 0 q.2) := by
    rw [hzero]
    exact hstate
  have hleft := hstate'.comp_hasDerivAt 0 hinner
  have hterminal := hX.1.2.2 q.1 hq.2
  have hright : HasDerivAt (fun s => flow F (q.1+s) q.2)
      (F.eval (flow F q.1 q.2)) 0 := by
    have hd := hterminal.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add q.1)
      (by simp)
    convert hd using 1 <;> simp [Function.comp_def, AutonomousODE.toODE_eval]
  have hn0 : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ (flowInterval F q.2).carrier :=
    (flowInterval F q.2).isOpen.mem_nhds hX.2.1
  have hnt : ∀ᶠ s in 𝓝 (0 : ℝ), q.1+s ∈ (flowInterval F q.2).carrier := by
    have hc : ContinuousAt (fun s : ℝ => q.1+s) 0 :=
      continuousAt_const.add continuousAt_id
    apply hc.preimage_mem_nhds
    simpa only [add_zero] using (flowInterval F q.2).isOpen.mem_nhds hq.2
  have he : (fun s => flow F q.1 (flow F s q.2)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => flow F (q.1+s) q.2) := by
    filter_upwards [hn0,hnt] with s hs hts
    exact (flow_translation F hF q.2 hq.1 s hs).2 q.1 hts
  exact (hleft.congr_of_eventuallyEq he.symm).unique hright

end D13Unified.Ch11.Flow
