import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.MaximalCoupling
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.TotalVariation
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Interfaces

open MeasureTheory
open scoped ENNReal Classical
universe u v
namespace P207.Markov
noncomputable section

/-- The coupling inequality on any probability space with the given marginals. -/
theorem totalVariation_le_disagreement
    {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ ν : ProbabilityLaw S) (U V : Ω → S)
    (hU : Measurable U) (hV : Measurable V)
    (hmU : P.map U = μ.toMeasure) (hmV : P.map V = ν.toMeasure) :
    totalVariation μ ν ≤ (P {ω | U ω ≠ V ω}).toReal := by
  have hevent (A : Set S) :
      (lawEvent μ A).toReal - (lawEvent ν A).toReal ≤
        (P {ω | U ω ≠ V ω}).toReal := by
    have hsub : U ⁻¹' A ⊆ (V ⁻¹' A) ∪ {ω | U ω ≠ V ω} := by
      intro ω hω
      by_cases h : U ω = V ω
      · exact Or.inl (by simpa [h] using hω)
      · exact Or.inr h
    have h := ENNReal.toReal_le_add
      ((measure_mono hsub).trans (measure_union_le _ _))
      (measure_ne_top P _) (measure_ne_top P _)
    rw [lawEvent_eq_measure, lawEvent_eq_measure, ← hmU, ← hmV,
      Measure.map_apply hU (MeasurableSet.of_discrete),
      Measure.map_apply hV (MeasurableSet.of_discrete)]
    linarith
  have hevent' (A : Set S) :
      (lawEvent ν A).toReal - (lawEvent μ A).toReal ≤
        (P {ω | U ω ≠ V ω}).toReal := by
    have hsub : V ⁻¹' A ⊆ (U ⁻¹' A) ∪ {ω | U ω ≠ V ω} := by
      intro ω hω
      by_cases h : U ω = V ω
      · exact Or.inl (by simpa [h] using hω)
      · exact Or.inr h
    have h := ENNReal.toReal_le_add
      ((measure_mono hsub).trans (measure_union_le _ _))
      (measure_ne_top P _) (measure_ne_top P _)
    rw [lawEvent_eq_measure, lawEvent_eq_measure, ← hmU, ← hmV,
      Measure.map_apply hU (MeasurableSet.of_discrete),
      Measure.map_apply hV (MeasurableSet.of_discrete)]
    linarith
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact abs_le.mpr ⟨by linarith [hevent' A], hevent A⟩

namespace MaximalCoupling

/-- The common diagonal mass. -/
private def common {S : Type u} (μ ν : ProbabilityLaw S) (i : S) : ℝ≥0∞ :=
  min (μ i) (ν i)

private def residual {S : Type u} (μ ν : ProbabilityLaw S) (i : S) : ℝ≥0∞ :=
  μ i - common μ ν i

private def remainder {S : Type u} (μ ν : ProbabilityLaw S) : ℝ≥0∞ :=
  1 - ∑' i, common μ ν i

private lemma common_symm {S : Type u} (μ ν : ProbabilityLaw S) :
    common μ ν = common ν μ := by
  funext i
  exact min_comm _ _

private lemma remainder_symm {S : Type u} (μ ν : ProbabilityLaw S) :
    remainder μ ν = remainder ν μ := by rw [remainder, remainder, common_symm]

private lemma sum_residual {S : Type u} (μ ν : ProbabilityLaw S) :
    ∑' i, residual μ ν i = remainder μ ν := by
  apply ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (overlap_le_one μ ν))
  rw [← ENNReal.tsum_add]
  calc
    _ = ∑' i, μ i := by
      apply tsum_congr
      intro i
      exact tsub_add_cancel_of_le (min_le_left _ _)
    _ = 1 := μ.tsum_coe

private lemma remainder_ne_top {S : Type u} (μ ν : ProbabilityLaw S) :
    remainder μ ν ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

/-- The unnormalized diagonal plus the product of the two residual masses.
Division by zero is harmless: both residuals then vanish. -/
private def mass {S : Type u} (μ ν : ProbabilityLaw S) (p : S × S) : ℝ≥0∞ :=
  (if p.2 = p.1 then common μ ν p.1 else 0) +
    residual μ ν p.1 * (residual ν μ p.2 / remainder μ ν)

private lemma row_mass {S : Type u} (μ ν : ProbabilityLaw S) (i : S) :
    ∑' j, mass μ ν (i,j) = μ i := by
  simp only [mass]
  rw [ENNReal.tsum_add]
  have hd : (∑' j, if j = i then common μ ν i else 0) = common μ ν i := by
    simp
  rw [hd, ENNReal.tsum_mul_left]
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, sum_residual, ← remainder_symm μ ν]
  by_cases h : remainder μ ν = 0
  · have hr : residual μ ν i = 0 := by
      have := (ENNReal.tsum_eq_zero.mp ((sum_residual μ ν).trans h)) i
      exact this
    rw [h, hr]
    have hsum : common μ ν i + residual μ ν i = μ i :=
      add_tsub_cancel_of_le (min_le_left _ _)
    simpa only [hr, add_zero, zero_mul] using hsum
  · rw [ENNReal.mul_inv_cancel h (remainder_ne_top μ ν), mul_one]
    exact add_tsub_cancel_of_le (min_le_left _ _)

private lemma mass_swap {S : Type u} (μ ν : ProbabilityLaw S) (i j : S) :
    mass μ ν (i,j) = mass ν μ (j,i) := by
  simp only [mass, ← remainder_symm μ ν, div_eq_mul_inv]
  congr 1
  · by_cases h : j = i
    · simp [h, common_symm]
    · simp [h, Ne.symm h]
  · ac_rfl

private lemma col_mass {S : Type u} (μ ν : ProbabilityLaw S) (j : S) :
    ∑' i, mass μ ν (i,j) = ν j := by
  simp_rw [mass_swap μ ν]
  exact row_mass ν μ j

private lemma sum_mass {S : Type u} (μ ν : ProbabilityLaw S) :
    ∑' p, mass μ ν p = 1 := by
  rw [ENNReal.tsum_prod']
  simp_rw [row_mass]
  exact μ.tsum_coe

/-- Common masses on the diagonal and the independent residuals off it. -/
private def joint {S : Type u} (μ ν : ProbabilityLaw S) : ProbabilityLaw (S × S) :=
  ⟨mass μ ν, ENNReal.summable.hasSum_iff.mpr (sum_mass μ ν)⟩

private lemma map_fst {S : Type u} (μ ν : ProbabilityLaw S) :
    (joint μ ν).map Prod.fst = μ := by
  apply PMF.ext
  intro i
  rw [PMF.map_apply]
  rw [ENNReal.tsum_prod']
  calc
    (∑' a, ∑' b, if i = a then joint μ ν (a,b) else 0) =
        ∑' b, joint μ ν (i,b) := by
      rw [tsum_eq_single i]
      · simp
      · intro a ha
        simp [Ne.symm ha]
    _ = μ i := row_mass μ ν i

private lemma map_snd {S : Type u} (μ ν : ProbabilityLaw S) :
    (joint μ ν).map Prod.snd = ν := by
  apply PMF.ext
  intro j
  rw [PMF.map_apply]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc
    (∑' b, ∑' a, if j = b then joint μ ν (a,b) else 0) =
        ∑' a, joint μ ν (a,j) := by
      rw [tsum_eq_single j]
      · simp
      · intro b hb
        simp [Ne.symm hb]
    _ = ν j := col_mass μ ν j

private lemma diagonal_mass {S : Type u} (μ ν : ProbabilityLaw S) (i : S) :
    mass μ ν (i,i) = common μ ν i := by
  have hzero : residual μ ν i = 0 ∨ residual ν μ i = 0 := by
    rcases le_total (μ i) (ν i) with h | h
    · exact Or.inl (by simp [residual, common, min_eq_left h])
    · exact Or.inr (by simp [residual, common, min_eq_left h])
  rcases hzero with h | h <;> simp [mass, h]

private lemma diagonal_event {S : Type u} (μ ν : ProbabilityLaw S) :
    lawEvent (joint μ ν) {p | p.1 = p.2} = ∑' i, common μ ν i := by
  rw [lawEvent]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  calc
    (∑' j, {p : S × S | p.1 = p.2}.indicator (joint μ ν) (i,j)) =
        joint μ ν (i,i) := by
      rw [tsum_eq_single i]
      · simp
      · intro j hj
        simp [Ne.symm hj]
    _ = common μ ν i := diagonal_mass μ ν i

private lemma lawEvent_compl {T : Type*} (ρ : ProbabilityLaw T) (A : Set T) :
    lawEvent ρ Aᶜ = 1 - lawEvent ρ A := by
  apply ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (by
      calc
        lawEvent ρ A ≤ ∑' i, ρ i := by
          apply ENNReal.tsum_le_tsum
          intro i
          by_cases hi : i ∈ A <;> simp [hi]
        _ = 1 := ρ.tsum_coe))
  rw [lawEvent, lawEvent, ← ENNReal.tsum_add]
  calc
    _ = ∑' i, ρ i := by
      apply tsum_congr
      intro i
      by_cases hi : i ∈ A <;> simp [hi]
    _ = 1 := ρ.tsum_coe

private lemma disagreement_event {S : Type u} [Countable S] (μ ν : ProbabilityLaw S) :
    (lawEvent (joint μ ν) {p | p.1 ≠ p.2}).toReal = totalVariation μ ν := by
  have hc : {p : S × S | p.1 ≠ p.2} = {p : S × S | p.1 = p.2}ᶜ := rfl
  rw [hc, lawEvent_compl, diagonal_event]
  rw [totalVariation_eq_one_sub_overlap, ← overlap_toReal]
  -- The total mass is finite, so truncated subtraction agrees with real subtraction.
  have hle := overlap_le_one μ ν
  simp only [common]
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  rfl

end MaximalCoupling

/-- Every pair of countable laws has a coupling attaining the coupling bound. -/
theorem exists_maximal_coupling {S : Type u} [Countable S] (μ ν : ProbabilityLaw S) :
    ∃ ρ : ProbabilityLaw (S × S),
      ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
      (lawEvent ρ {p | p.1 ≠ p.2}).toReal = totalVariation μ ν :=
  ⟨MaximalCoupling.joint μ ν, MaximalCoupling.map_fst μ ν,
    MaximalCoupling.map_snd μ ν, MaximalCoupling.disagreement_event μ ν⟩

end
end P207.Markov
