import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.BasicConditionalIdentities
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.IntegralConvergence

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch03

universe u

/-- Conditional monotone convergence for any chosen measurable versions,
with all inequalities and the limit holding outside one G-measurable null set. -/
theorem nonnegativeConditionalExpectationVersions_monotone_convergence :
    Specs.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence.versionsMonotoneConvergenceType := by
  intro Ω G F P _ hGF Xn X hXn hX hmono hlim Un U hUn hU
  have hUnm : ∀ n, Measurable[G] (Un n) := fun n => (hUn n).1
  have hUnmono : ∀ᵐ ω ∂P, Monotone (fun n => Un n ω) := by
    have hstep : ∀ n, Un n ≤ᵐ[P] Un (n + 1) := by
      intro n
      apply ae_le_of_forall_conditional_setLIntegral_le G P hGF _ _ (hUnm n) (hUnm (n + 1))
      intro A hA
      rw [(hUn n).2 A hA, (hUn (n + 1)).2 A hA]
      exact lintegral_mono_ae (ae_restrict_of_ae
        (hmono.mono fun ω hω => hω (Nat.le_succ n)))
    filter_upwards [ae_all_iff.mpr hstep] with ω hω
    exact monotone_nat_of_le_succ hω
  let V : Ω → ℝ≥0∞ := fun ω => ⨆ n, Un n ω
  have hVm : Measurable[G] V := Measurable.iSup hUnm
  have hVlim : ∀ᵐ ω ∂P, Tendsto (fun n => Un n ω) atTop (𝓝 (V ω)) :=
    hUnmono.mono fun ω hω => tendsto_atTop_iSup hω
  have hV : IsNonnegativeConditionalExpectationVersion G P X V := by
    refine ⟨hVm, ?_⟩
    intro A hA
    have hconvUn := (Ch01.monotone_convergence (P.restrict A) Un V
      (fun n => (hUnm n).mono hGF le_rfl) (hVm.mono hGF le_rfl)
      (ae_restrict_of_ae hUnmono) (ae_restrict_of_ae hVlim)).2
    have hconvXn := (Ch01.monotone_convergence (P.restrict A) Xn X hXn hX
      (ae_restrict_of_ae hmono) (ae_restrict_of_ae hlim)).2
    simp_rw [(hUn _).2 A hA] at hconvUn
    exact tendsto_nhds_unique hconvUn hconvXn
  have hVU : V =ᵐ[P] U :=
    nonnegativeConditionalExpectationVersion_ae_unique G P hGF X V U hX hV hU
  -- Successive inequalities and equality with the supremum are measurable in G.
  let S : Set Ω := (⋂ n, {ω | Un n ω ≤ Un (n + 1) ω}) ∩ {ω | V ω = U ω}
  have hSm : MeasurableSet[G] S :=
    (MeasurableSet.iInter fun n => measurableSet_le (hUnm n) (hUnm (n + 1))).inter
      (measurableSet_eq_fun hVm hU.1)
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [hUnmono, hVU] with ω hω heq
    exact ⟨Set.mem_iInter.mpr (fun n => hω (Nat.le_succ n)), heq⟩
  refine ⟨Sᶜ, hSm.compl, ?_, ?_⟩
  · exact ae_iff.mp hSae
  · intro ω hω
    have hωS : ω ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hω
    have hωmono : Monotone (fun n => Un n ω) :=
      monotone_nat_of_le_succ (Set.mem_iInter.mp hωS.1)
    refine ⟨hωmono, ?_⟩
    have hωlim := tendsto_atTop_iSup hωmono
    change Tendsto (fun n => Un n ω) atTop (𝓝 (V ω)) at hωlim
    rwa [hωS.2] at hωlim

/-- The canonical conditional expectations are versions and increase to the
canonical conditional expectation of the limit on one common measurable event. -/
theorem nonnegativeConditionalExpectation_monotone_convergence :
    Specs.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence.canonicalMonotoneConvergenceType := by
  intro Ω G F P _ hGF Xn X hXn hX hmono hlim
  have hUn := fun n => nonnegativeConditionalExpectation_isVersion G P hGF (Xn n) (hXn n)
  have hU := nonnegativeConditionalExpectation_isVersion G P hGF X hX
  exact ⟨hUn, hU, nonnegativeConditionalExpectationVersions_monotone_convergence
    G P hGF Xn X hXn hX hmono hlim _ _ hUn hU⟩

end ProbabilityFoundations.Ch03
