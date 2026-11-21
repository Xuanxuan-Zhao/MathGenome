import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalStability
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.NearbySectionEntry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.OrbitalDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.SectionDecay

import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.NearbySectionEntry
/-! Conditional derivation of paper.tex, d13:14:orbital-stability.
Only the full independently specified nearby-section entry theorem is a premise.
The original closed target is intentionally left for genuine dependency closure. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.OrbitalStability
open Ch06.StateDerivative Ch11.Orbits
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch14.OrbitalDefinitions
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Absorb any uniformly bounded delay into an exponential constant. -/
lemma exponential_delay {α A a t : ℝ} (hα : 0 ≤ α) (ha : a ≤ A) :
    Real.exp (-α * (t-a)) ≤ Real.exp (α*A) * Real.exp (-α*t) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- An exponential distance bound gives both stability and attraction, with
forward existence retained in both conclusions. -/
lemma asymptotic_of_exponential (F : AutonomousODE E) (Γ : Set E)
    (h : exponentiallyOrbitallyStableValue F Γ) :
    orbitalAsymptoticallyStableValue F Γ := by
  obtain ⟨C,hC,α,hα,δ,hδ,hbound⟩ := h
  constructor
  · intro ε hε
    refine ⟨min δ (ε / C), lt_min hδ (div_pos hε hC), ?_⟩
    intro x hx hdist
    obtain ⟨hforward,hdec⟩ := hbound x hx (hdist.trans_le (min_le_left _ _))
    refine ⟨hforward, fun t ht => ?_⟩
    have he : Real.exp (-α*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      Metric.infDist (flow F t x) Γ ≤ C * Real.exp (-α*t) * Metric.infDist x Γ :=
        hdec t ht
      _ ≤ C * 1 * Metric.infDist x Γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le)
          Metric.infDist_nonneg
      _ = C * Metric.infDist x Γ := by ring
      _ < ε := by
        simpa only [mul_comm] using
          (lt_div_iff₀ hC).mp (hdist.trans_le (min_le_right _ _))
  · refine ⟨δ,hδ,fun x hx hdist => ?_⟩
    obtain ⟨hforward,hdec⟩ := hbound x hx hdist
    refine ⟨hforward, ?_⟩
    have he : Tendsto (fun t : ℝ => Real.exp (-α*t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hα))
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-α*t) * Metric.infDist x Γ)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul he).mul_const (Metric.infDist x Γ)
    exact squeeze_zero' (Eventually.of_forall fun t => Metric.infDist_nonneg)
      (eventually_atTop.2 ⟨0, fun t ht => hdec t ht⟩) hlim

/-- The full conditional theorem: every nearby state first enters the small
invariant section neighborhood, then follows its complete forward trajectory.
The estimate before entry and the shifted section estimate share one constant. -/
theorem orbital_stability_conditional
    (entry : Specs.D13Unified.Ch14.NearbySectionEntry.NearbySectionEntryExpected.{u}) :
    Specs.D13Unified.Ch14.OrbitalStability.OrbitalStabilityExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T hT hc hperiod hmin hn ℓ d hspec
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hℓ : ℓ (F.eval p) ≠ 0 := by
    simpa [AutonomousODE.eval] using d.section_transverse 0 d.section_zero
  obtain ⟨U,hUo,h0U,hUsrc,hUU,C₀,θ,C₁,α,hC₀,hθ,hθ1,hC₁,hα,
    K,hK,hΓK,hKdom,hsection⟩ :=
    SectionDecay.section_decay k hk F hF p hp T hT hc hperiod hmin hn ℓ d hspec
  obtain ⟨δ,A,L₁,L₂,hδ,hA,hL₁,hL₂,hentry⟩ :=
    entry F hF1 p hp T hT hc hperiod ℓ hℓ U hUo h0U
  let M := L₂ + C₁*L₁
  let C := M * Real.exp (α*A)
  have hM : 0 < M := by dsimp [M]; positivity
  have hC : 0 < C := mul_pos hM (Real.exp_pos _)
  have hL₂M : L₂ ≤ M := le_add_of_nonneg_right (mul_pos hC₁ hL₁).le
  have hCLM : C₁*L₁ ≤ M := by dsimp [M]; linarith
  have hexp : exponentiallyOrbitallyStableValue F (orbit F p) := by
    refine ⟨C,hC,α,hα,δ,hδ,?_⟩
    intro x hx hdist
    obtain ⟨hx',a,ha,haA,hpre,⟨v,hv,hvflow⟩,hvnorm,hprebound⟩ := hentry x hdist
    have haDom := hpre a ⟨ha.le,le_rfl⟩
    have htrans := Ch11.Flow.flow_translation F hF1 x hx a haDom.2
    rw [hvflow] at htrans
    have hsec := (hsection v hv).2.2.2.2.2.2
    have hall (t : ℝ) (ht : 0 ≤ t) : (t,x) ∈ flowDomain F ∧
        Metric.infDist (flow F t x) (orbit F p) ≤
          C * Real.exp (-α*t) * Metric.infDist x (orbit F p) := by
      have hD : 0 ≤ Metric.infDist x (orbit F p) := Metric.infDist_nonneg
      by_cases hta : t ≤ a
      · have hta' : t ∈ Icc 0 a := ⟨ht,hta⟩
        refine ⟨hpre t hta', (hprebound t hta').trans ?_⟩
        have hdelay := exponential_delay hα.le (hta.trans haA) (t := t)
        simp only [sub_self, mul_zero, Real.exp_zero] at hdelay
        have hcge : L₂ ≤ C * Real.exp (-α*t) := by
          calc
            L₂ ≤ M := hL₂M
            _ ≤ M * (Real.exp (α*A) * Real.exp (-α*t)) :=
              le_mul_of_one_le_right hM.le hdelay
            _ = C * Real.exp (-α*t) := by dsimp [C]; ring
        exact mul_le_mul_of_nonneg_right hcge hD
      · have hafter : 0 ≤ t-a := by linarith
        have hs := hsec (t-a) hafter
        have htI : t ∈ (flowInterval F x).carrier := by
          have hq := hs.1.2
          rw [htrans.1] at hq
          simpa using hq
        refine ⟨⟨hx,htI⟩,?_⟩
        have heq : flow F (t-a) (p + (v : E)) = flow F t x := by
          simpa using htrans.2 (t-a) (by simpa using htI)
        have hvnorm' : ‖v‖ ≤ L₁ * Metric.infDist x (orbit F p) := by
          simpa [hvflow] using hvnorm
        rw [← heq]
        calc
          Metric.infDist (flow F (t-a) (p + (v : E))) (orbit F p)
              ≤ C₁ * Real.exp (-α*(t-a)) * ‖v‖ := hs.2.2
          _ ≤ C₁ * Real.exp (-α*(t-a)) * (L₁ * Metric.infDist x (orbit F p)) :=
            mul_le_mul_of_nonneg_left hvnorm' (by positivity)
          _ = (C₁*L₁) * Real.exp (-α*(t-a)) * Metric.infDist x (orbit F p) := by ring
          _ ≤ M * (Real.exp (α*A) * Real.exp (-α*t)) * Metric.infDist x (orbit F p) := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact mul_le_mul hCLM (exponential_delay hα.le haA) (Real.exp_pos _).le hM.le
          _ = C * Real.exp (-α*t) * Metric.infDist x (orbit F p) := by dsimp [C]; ring
    exact ⟨⟨hx, fun t ht => (hall t ht).1.2⟩,fun t ht => (hall t ht).2⟩
  exact ⟨hexp, asymptotic_of_exponential F (orbit F p) hexp⟩

end D13Unified.Ch14.OrbitalStability

universe v8_closure_c25bb4b67b5badf4_u0
theorem _root_.«D13Unified».«Ch14».«OrbitalStability».«orbital_stability» : _root_.«Specs».«D13Unified».«Ch14».«OrbitalStability».«OrbitalStabilityExpected».{v8_closure_c25bb4b67b5badf4_u0} :=
  @_root_.«D13Unified».«Ch14».«OrbitalStability».«orbital_stability_conditional».{v8_closure_c25bb4b67b5badf4_u0} (@_root_.«D13Unified».«Ch14».«NearbySectionEntry».«nearby_section_entry».{v8_closure_c25bb4b67b5badf4_u0})
