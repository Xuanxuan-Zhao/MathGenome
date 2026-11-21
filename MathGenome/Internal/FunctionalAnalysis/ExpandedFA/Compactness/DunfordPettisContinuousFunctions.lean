import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.DunfordPettisContinuousFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.DunfordPettisCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.VitaliHahnSaks
import Mathlib.MeasureTheory.Function.Egorov

namespace ExpandedFA.Compactness.DunfordPettisContinuousFunctions

open Set Filter MeasureTheory
open scoped Topology ENNReal ZeroAtInfty
open FunctionSpaces.ScalarRieszMarkovSpec FunctionSpaces.ScalarRieszMarkov
open Specs.ExpandedFA.Compactness.VitaliHahnSaks

universe u w
noncomputable section

/-- Egorov plus uniform absolute continuity of variations controls diagonal
integrals. This uses a single finite control measure, with no topological or
countability assumptions on the underlying measurable space. -/
theorem tendsto_scalarIntegral_of_uniformVariation
    {K : Type u} [MeasurableSpace K] {𝕜 : Type} [RCLike 𝕜]
    (ρ : Measure K) [IsFiniteMeasure ρ] (μ : ℕ → VectorMeasure K 𝕜)
    [∀ n, IsFiniteMeasure (μ n).variation]
    (f : ℕ → K → 𝕜) (hf : ∀ n, StronglyMeasurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ n).variation)
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0))
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbound : ∀ n x, ‖f n x‖ ≤ C)
    (hmass : ∀ n, (μ n).variation.real univ ≤ M)
    (hv : UniformVariation ρ μ) :
    Tendsto (fun n => scalarIntegral (μ n) (f n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let a := ε / (2 * (C + 1))
  let b := ε / (2 * (M + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨δ, hδ, hsmall⟩ := hv a ha
  obtain ⟨s, hs, hρs, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' (μ := ρ)
    hf stronglyMeasurable_const (Eventually.of_forall hpoint)
    (ENNReal.ofReal_pos.mpr (half_pos hδ))
  have hρs' : ρ s < ENNReal.ofReal δ :=
    hρs.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith))
  have hvar (n : ℕ) : (μ n).variation.real s ≤ a := by
    apply ENNReal.toReal_le_of_le_ofReal ha.le
    exact (le_iSup (fun n => (μ n).variation s) n).trans (hsmall s hs hρs').le
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif b hb)
  refine ⟨N, fun n hn => ?_⟩
  have hmajor : ∀ x, ‖f n x‖ ≤ s.indicator (fun _ => C) x + b := by
    intro x
    by_cases hx : x ∈ s
    · simpa [hx] using (hbound n x).trans (le_add_of_nonneg_right hb.le)
    · have hh := hN n hn x hx
      simpa [hx, dist_zero_left, dist_zero_right] using hh.le
  have hiC : Integrable (s.indicator (fun _ : K => C)) (μ n).variation :=
    (integrable_const C).indicator hs
  have hib : Integrable (fun _ : K => b) (μ n).variation := integrable_const b
  have hint : (∫ x, ‖f n x‖ ∂(μ n).variation) ≤
      C * (μ n).variation.real s + b * (μ n).variation.real univ := by
    calc
      _ ≤ ∫ x, (s.indicator (fun _ => C) x + b) ∂(μ n).variation :=
        integral_mono (hfi n).norm (hiC.add hib) hmajor
      _ = _ := by
        rw [integral_add hiC hib, integral_indicator hs, setIntegral_const, integral_const]
        simp only [smul_eq_mul, mul_comm, Measure.real]
  have hCa : C * a < ε / 2 := by
    have hh : (C + 1) * a = ε / 2 := by dsimp [a]; field_simp
    nlinarith
  have hMb : b * M < ε / 2 := by
    have hh : b * (M + 1) = ε / 2 := by dsimp [b]; field_simp
    nlinarith
  rw [dist_zero_right]
  exact (scalarIntegral_l1_bound (μ n) (f n)).trans hint |>.trans_lt
    (lt_of_le_of_lt (add_le_add
      (mul_le_mul_of_nonneg_left (hvar n) hC)
      (mul_le_mul_of_nonneg_left (hmass n) hb.le)) (by linarith))


/-- Point evaluation is a scalar-linear bounded functional, also when the
compact space is empty (in which case there is no point to evaluate). -/
def pointEvaluation {K : Type u} [TopologicalSpace K] {𝕜 : Type} [RCLike 𝕜]
    (x : K) : C₀(K, 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by simpa using f.toBCF.norm_coe_le_norm x)

private theorem bounded_of_weakNull {𝕜 : Type} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E)
    (hx : ∀ g : E →L[𝕜] 𝕜, Tendsto (fun n => g (x n)) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C := by
  apply P1.C12BoundedSequences.norm_bound_of_scalar_bounds 𝕜 E ℕ x
  intro g
  obtain ⟨C, hC⟩ := (hx g).norm.bddAbove_range
  exact ⟨C, fun n => hC (mem_range_self n)⟩

/-- Riesz--Markov supplies genuine scalar measures for the full norm dual.
Weak convergence of that dual invokes the accepted VHS application. -/
theorem zeroAtInfty_weakNull_testing (𝕜 : Type) [RCLike 𝕜]
    (hrmk : ScalarRepresentation.{u} 𝕜) (hvhs : WeakApplication.{u} 𝕜)
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] :
    DunfordPettisCriterion.WeakNullTestingProperty 𝕜 C₀(K, 𝕜) := by
  intro f L hf hL
  choose μ hμ hrep hnorm huniq using fun n => hrmk K (L n)
  obtain ⟨ν, hν, hνrep, _⟩ := hrmk K (0 : C₀(K, 𝕜) →L[𝕜] 𝕜)
  have hweak : MeasureWeakConverges μ ν := by
    refine ⟨L, 0, fun n g => (hrep n g).2, fun g => (hνrep g).2, ?_⟩
    intro T
    simpa only [map_zero] using hL T
  have hvariation := (hvhs K μ ν hμ hν hweak).2.1
  letI : ∀ n, IsFiniteMeasure (μ n).variation := fun n => ⟨(hμ n).1⟩
  letI : IsFiniteMeasure (controlMeasure μ) :=
    (VitaliHahnSaks.control_measure_theorem 𝕜 K μ hμ).1
  obtain ⟨C, hC, hCf⟩ := bounded_of_weakNull f hf
  obtain ⟨M, hM, hML⟩ := bounded_of_weakNull L hL
  have hlim := tendsto_scalarIntegral_of_uniformVariation (controlMeasure μ) μ
    (fun n x => f n x) (fun n => (f n).continuous.stronglyMeasurable)
    (fun n => (hrep n (f n)).1) (fun x => hf (pointEvaluation x))
    C M hC hM (fun n x => ((f n).toBCF.norm_coe_le_norm x).trans (hCf n))
    (fun n => by rw [← hnorm n]; exact hML n) hvariation
  simpa only [← fun n => (hrep n (f n)).2] using hlim

/-- The compact C(K)–C₀(K) isometry transports both weak-null sequences,
including all bidual tests on the functional sequence. -/
theorem continuous_weakNull_testing (𝕜 : Type) [RCLike 𝕜]
    (hrmk : ScalarRepresentation.{u} 𝕜) (hvhs : WeakApplication.{u} 𝕜)
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] :
    DunfordPettisCriterion.WeakNullTestingProperty 𝕜 C(K, 𝕜) := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, _, _⟩ := compact_identification K 𝕜
  let A := e.toContinuousLinearEquiv.toContinuousLinearMap
  let B := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let S := P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 C₀(K, 𝕜) C(K, 𝕜) B
  intro f L hf hL
  have htest := zeroAtInfty_weakNull_testing 𝕜 hrmk hvhs K
    (fun n => A (f n)) (fun n => S (L n))
    (fun g => hf (g.comp A)) (fun T => hL (T.comp S))
  convert htest using 1
  funext n
  change L n (f n) = L n (e.symm (e (f n)))
  rw [e.symm_apply_apply]

/-- Combine the diagonal test with the accepted Dunford--Pettis criterion. -/
theorem continuousFunctions_theorem (𝕜 : Type) [RCLike 𝕜]
    (hrmk : ScalarRepresentation.{u} 𝕜) (hvhs : WeakApplication.{u} 𝕜) :
    Spec.ContinuousFunctionsTheorem.{u,w} 𝕜 := by
  intro K _ _ _
  have ht := continuous_weakNull_testing 𝕜 hrmk hvhs K
  exact ⟨ht, fun Y _ _ _ T hT =>
    DunfordPettisCriterion.testing_implies_operator_property 𝕜 C(K, 𝕜) Y ht T hT⟩

theorem real_theorem : Spec.RealTheorem.{u,w} :=
  continuousFunctions_theorem ℝ real_representation VitaliHahnSaks.weak_application_signed

theorem complex_theorem : Spec.ComplexTheorem.{u,w} :=
  continuousFunctions_theorem ℂ complex_representation VitaliHahnSaks.weak_application_complex

end
end ExpandedFA.Compactness.DunfordPettisContinuousFunctions
