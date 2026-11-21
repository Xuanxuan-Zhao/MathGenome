import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalAndTotalVariance
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalLpContraction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.IntegrableConditionalPullout
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Tactic.Ring

/-! Conditional and total variance, paper.tex 1043–1061. We use L2 contraction,
Hölder integrability, pull-out, and the fixed-point identity to expand the
conditional square. Integration and preservation of the mean then give the
centered second-moment identity, including constant variables. -/

open MeasureTheory

namespace ProbabilityFoundations.Ch03
universe u

theorem conditional_variance_integrability :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectation G P X
      let V := realConditionalExpectation G P (fun ω => (X ω - M ω) ^ 2)
      MemLp M 2 P ∧ Integrable X P ∧ Integrable M P ∧
        Integrable (fun ω => X ω ^ 2) P ∧
        Integrable (fun ω => M ω ^ 2) P ∧
        Integrable (fun ω => M ω * X ω) P ∧
        Integrable (fun ω => (X ω - M ω) ^ 2) P ∧ Integrable V P ∧
        Integrable (fun ω => (X ω - ∫ t, X t ∂P) ^ 2) P ∧
        Integrable (fun ω => (M ω - ∫ t, M t ∂P) ^ 2) P := by
  intro Ω G F P _ hGF X hX
  dsimp only
  have hc := realConditionalExpectation_lp_contraction G P hGF 2 (by norm_num) X hX
  have hM := hc.2.1
  exact ⟨hM, hc.1, integrable_condExp, hX.integrable_sq, hM.integrable_sq,
    hM.integrable_mul hX, (hX.sub hM).integrable_sq, integrable_condExp,
    (hX.sub (memLp_const (∫ t, X t ∂P))).integrable_sq,
    (hM.sub (memLp_const (∫ t, realConditionalExpectation G P X t ∂P))).integrable_sq⟩

theorem conditional_variance_eq :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectation G P X
      realConditionalExpectation G P (fun ω => (X ω - M ω) ^ 2) =ᵐ[P]
        (fun ω => realConditionalExpectation G P (fun t => X t ^ 2) ω - M ω ^ 2) := by
  intro Ω G F P _ hGF X hX
  let M := realConditionalExpectation G P X
  have hc := conditional_variance_integrability G P hGF X hX
  have hXi := hc.2.1
  have hXsq := hc.2.2.2.1
  have hMsq := hc.2.2.2.2.1
  have hMX := hc.2.2.2.2.2.1
  have hMm : Measurable[G] M := stronglyMeasurable_condExp.measurable
  have hpull := (realConditionalExpectation_mul G P hGF M X hMm hXi hMX).2
  have hfixed := realConditionalExpectation_fixed G P hGF (fun ω => M ω ^ 2)
    (hMm.pow_const 2) hMsq
  have hsub := condExp_sub hXsq (hMX.const_mul 2) G
  have hadd := condExp_add (hXsq.sub (hMX.const_mul 2)) hMsq G
  have hscale := condExp_smul (2 : ℝ) (fun ω => M ω * X ω) G (μ := P)
  have hexpand : (fun ω => (X ω - M ω) ^ 2) =
      (fun ω => X ω ^ 2 - 2 * (M ω * X ω) + M ω ^ 2) := by
    funext ω
    ring
  change realConditionalExpectation G P (fun ω => (X ω - M ω) ^ 2) =ᵐ[P] _
  rw [hexpand]
  filter_upwards [hpull, hfixed, hsub, hadd, hscale] with ω hp hf hs ha hm
  change condExp G P (fun ω => X ω ^ 2 - 2 * (M ω * X ω) + M ω ^ 2) ω = _
  change condExp G P (fun ω => X ω ^ 2 - 2 * (M ω * X ω) + M ω ^ 2) ω =
    condExp G P (fun ω => X ω ^ 2 - 2 * (M ω * X ω)) ω +
      condExp G P (fun ω => M ω ^ 2) ω at ha
  change condExp G P (fun ω => X ω ^ 2 - 2 * (M ω * X ω)) ω =
    condExp G P (fun ω => X ω ^ 2) ω -
      condExp G P (fun ω => 2 * (M ω * X ω)) ω at hs
  change condExp G P (fun ω => 2 * (M ω * X ω)) ω =
    2 * condExp G P (fun ω => M ω * X ω) ω at hm
  change condExp G P (fun ω => M ω * X ω) ω = M ω * M ω at hp
  change condExp G P (fun ω => M ω ^ 2) ω = M ω ^ 2 at hf
  rw [ha, hs, hm, hp, hf]
  change condExp G P (fun t => X t ^ 2) ω - 2 * (M ω * M ω) + M ω ^ 2 =
    condExp G P (fun t => X t ^ 2) ω - M ω ^ 2
  ring

/-- The project's centered second moment agrees with the usual second-moment
formula on L2. This bridge uses only almost-everywhere measurability. -/
private theorem realVariance_eq_second_moment {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    Ch01.realVariance P X = (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 := by
  change (∫ ω, (X ω - ∫ t, X t ∂P) ^ 2 ∂P) = _
  rw [← ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  exact ProbabilityTheory.variance_eq_sub hX

theorem total_variance :
  ∀ {Ω : Type u} (G : MeasurableSpace Ω) [F : MeasurableSpace Ω]
    (P : Measure[F] Ω) [IsProbabilityMeasure P], G ≤ F →
    ∀ (X : Ω → ℝ), MemLp X 2 P →
      let M := realConditionalExpectation G P X
      let V := realConditionalExpectation G P (fun ω => (X ω - M ω) ^ 2)
      Ch01.realVariance P X = (∫ ω, V ω ∂P) + Ch01.realVariance P M := by
  intro Ω G F P _ hGF X hX
  let M := realConditionalExpectation G P X
  have hc := conditional_variance_integrability G P hGF X hX
  have hM := hc.1
  have hMsq := hc.2.2.2.2.1
  have hEV : (∫ ω, realConditionalExpectation G P (fun ω => (X ω - M ω) ^ 2) ω ∂P) =
      (∫ ω, X ω ^ 2 ∂P) - ∫ ω, M ω ^ 2 ∂P := by
    rw [integral_congr_ae (conditional_variance_eq G P hGF X hX),
      integral_sub (show Integrable (realConditionalExpectation G P (fun ω => X ω ^ 2)) P
        from integrable_condExp) hMsq,
      integral_realConditionalExpectation G P hGF _ hX.integrable_sq]
  have hmean : (∫ ω, M ω ∂P) = ∫ ω, X ω ∂P := integral_condExp hGF
  change Ch01.realVariance P X = _ + Ch01.realVariance P M
  rw [hEV, realVariance_eq_second_moment P X hX,
    realVariance_eq_second_moment P M hM, hmean]
  ring

end ProbabilityFoundations.Ch03
