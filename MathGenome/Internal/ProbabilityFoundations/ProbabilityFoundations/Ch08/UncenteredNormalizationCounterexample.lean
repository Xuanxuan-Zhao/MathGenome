import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample

lemma partialSum_eq {Ω : Type*} (n : ℕ) (ω : Ω) : partialSum n ω = n := by
  simp [partialSum, oneVariable]

lemma normalizedSum_eq {Ω : Type*} {p : ℝ} {n : ℕ} (hn : 0 < n) (ω : Ω) :
    normalizedSum p n ω = (n : ℝ) ^ (1 - 1 / p) := by
  rw [normalizedSum, partialSum_eq, Real.rpow_sub (by exact_mod_cast hn), Real.rpow_one]

lemma oneVariable_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : iIndepFun (oneVariable (Ω := Ω)) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    by_cases h : (1 : ℝ) ∈ sets a
    · have hpre : oneVariable (Ω := Ω) a ⁻¹' sets a = Set.univ := by
        ext ω
        simp [oneVariable, h]
      simpa only [Finset.set_biInter_insert, hpre, Set.univ_inter,
        Finset.prod_insert ha, measure_univ, one_mul] using
        ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi))
    · have hpre : oneVariable (Ω := Ω) a ⁻¹' sets a = ∅ := by
        ext ω
        simp [oneVariable, h]
      rw [Finset.set_biInter_insert, Finset.prod_insert ha, hpre]
      simp

lemma normalizedSum_tendsto {Ω : Type*} {p : ℝ} (hp : 1 < p) (ω : Ω) :
    Tendsto (fun n : ℕ => normalizedSum p n ω) atTop atTop := by
  have hexp : 0 < 1 - 1 / p := by
    have : 1 / p < 1 := (div_lt_one (by linarith)).2 hp
    linarith
  have h := (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (normalizedSum_eq hn ω).symm

/-- The constant-one counterexample to dropping the mean-zero assumption. -/
theorem counterexample :
    Specs.ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample.counterexampleType := by
  intro Ω mΩ μ hμ p hp hp2
  refine ⟨fun _ => measurable_const, oneVariable_independent μ,
    fun _ _ => IdentDistrib.refl measurable_const.aemeasurable, ?_,
    fun n ω hn => normalizedSum_eq hn ω, fun ω => normalizedSum_tendsto hp ω, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hempty : {ω : Ω | r < |oneVariable 1 ω|} = ∅ := by
      ext ω
      simp [oneVariable, not_lt.mpr hr]
    simp [hempty]
  · intro hconv
    have hzero := (tendstoInMeasure_iff_measureReal_norm.mp hconv) 1 (by norm_num)
    have hone : Tendsto (fun n => μ.real {ω : Ω | (1 : ℝ) ≤ ‖normalizedSum p n ω - 0‖})
        atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      have hdiv := normalizedSum_tendsto (Ω := Unit) hp ()
      filter_upwards [hdiv.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
      have hall : {ω : Ω | (1 : ℝ) ≤ ‖normalizedSum p n ω - 0‖} = Set.univ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, sub_zero, Real.norm_eq_abs]
        have hval : normalizedSum p n ω = normalizedSum p n () := rfl
        rw [hval]
        exact hn.trans (le_abs_self _)
      rw [hall]
      simp
    exact one_ne_zero (tendsto_nhds_unique hone hzero)

end ProbabilityFoundations.Ch08.UncenteredNormalizationCounterexample
