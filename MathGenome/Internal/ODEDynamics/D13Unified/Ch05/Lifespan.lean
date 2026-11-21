import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.Lifespan
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.OpenDomain
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap

/-! Semicontinuity of the actual maximal lifespan endpoints.
For a forward threshold choose a finite time above both the threshold and
initial time, still below the reference right endpoint. Openness of the
maximal domain keeps that time in all nearby solution intervals. The backward
proof chooses a finite time below both the threshold and initial time.
The argument also applies when either reference endpoint is infinite. -/
noncomputable section
open Set Filter Topology
namespace D13Unified.Ch05.Lifespan
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The interval and endpoint parts of canonical maximal-solution correctness. -/
lemma endpoint_description (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    (q : F.domain) :
    parameterLowerEndpointValue F q.val.1.1 q.val.1.2 q.val.2 < (q.val.1.1 : EReal) ∧
    (q.val.1.1 : EReal) < parameterUpperEndpointValue F q.val.1.1 q.val.1.2 q.val.2 ∧
    (parameterMaximalIntervalValue F q.val.1.1 q.val.1.2 q.val.2).carrier =
      {t : ℝ | parameterLowerEndpointValue F q.val.1.1 q.val.1.2 q.val.2 < (t : EReal) ∧
        (t : EReal) < parameterUpperEndpointValue F q.val.1.1 q.val.1.2 q.val.2} := by
  obtain ⟨_hx, _hs, _hξ, _hmax, hend, _⟩ :=
    ParameterODE.canonical_solution F hF q.val.1.1 q.val.1.2 q.val.2 q.property
  exact hend

/-- Every fixed admissible terminal time remains admissible near the datum. -/
lemma eventually_mem_interval (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    (q : F.domain) {t : ℝ}
    (ht : t ∈ (parameterMaximalIntervalValue F q.val.1.1 q.val.1.2 q.val.2).carrier) :
    ∀ᶠ r : F.domain in 𝓝 q,
      t ∈ (parameterMaximalIntervalValue F r.val.1.1 r.val.1.2 r.val.2).carrier := by
  have hD := OpenDomain.open_domain F hF
  have hq : (t, q.val) ∈ parameterSolutionDomainValue F := ⟨q.property, ht⟩
  have hcont : Continuous (fun r : F.domain => (t, r.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have hnear : ∀ᶠ r : F.domain in 𝓝 q, (t, r.val) ∈ parameterSolutionDomainValue F :=
    (hcont.tendsto q) (hD.mem_nhds hq)
  exact hnear.mono fun _ h => h.2

/-- Forward lifespan is lower semicontinuous, including at `+∞`. -/
theorem lowerSemicontinuous_upperEndpoint :
    Specs.D13Unified.Ch05.Lifespan.lowerSemicontinuousUpperEndpointExpected.{u,v} := by
  intro E _ _ _ P _ _ _ F hF q a ha
  have hend := endpoint_description F hF q
  obtain ⟨t, hat, htupper⟩ := EReal.exists_between_coe_real (max_lt ha hend.2.1)
  have hst : (q.val.1.1 : EReal) < (t : EReal) :=
    (le_max_right a (q.val.1.1 : EReal)).trans_lt hat
  have htin : t ∈ (parameterMaximalIntervalValue F q.val.1.1 q.val.1.2 q.val.2).carrier := by
    rw [hend.2.2]
    exact ⟨hend.1.trans hst, htupper⟩
  filter_upwards [eventually_mem_interval F hF q htin] with r hr
  rw [(endpoint_description F hF r).2.2] at hr
  exact ((le_max_left a (q.val.1.1 : EReal)).trans_lt hat).trans hr.2

/-- Backward lifespan is upper semicontinuous, including at `-∞`. -/
theorem upperSemicontinuous_lowerEndpoint :
    Specs.D13Unified.Ch05.Lifespan.upperSemicontinuousLowerEndpointExpected.{u,v} := by
  intro E _ _ _ P _ _ _ F hF q a ha
  have hend := endpoint_description F hF q
  obtain ⟨t, htlower, hta⟩ := EReal.exists_between_coe_real (lt_min ha hend.1)
  have hts : (t : EReal) < (q.val.1.1 : EReal) :=
    hta.trans_le (min_le_right a (q.val.1.1 : EReal))
  have htin : t ∈ (parameterMaximalIntervalValue F q.val.1.1 q.val.1.2 q.val.2).carrier := by
    rw [hend.2.2]
    exact ⟨htlower, hts.trans hend.2.1⟩
  filter_upwards [eventually_mem_interval F hF q htin] with r hr
  rw [(endpoint_description F hF r).2.2] at hr
  exact hr.1.trans (hta.trans_le (min_le_left a (q.val.1.1 : EReal)))

end D13Unified.Ch05.Lifespan
