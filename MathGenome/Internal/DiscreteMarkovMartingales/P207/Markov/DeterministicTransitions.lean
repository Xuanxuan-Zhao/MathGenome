import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.DeterministicTransitions
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Interfaces
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory Filter
open scoped ENNReal MeasureTheory Classical

universe u v

namespace P207.Markov

noncomputable section

namespace DeterministicTransitions

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] mΩ in
/-- Expand a function of a discrete random variable into its singleton pieces. -/
private theorem expansion (Y : Ω → S) (f : S → ℝ) (ω : Ω) :
    (∑' j, f j * Set.indicator {ω | Y ω = j} (fun _ => (1 : ℝ)) ω) = f (Y ω) := by
  classical
  rw [tsum_eq_single (Y ω)]
  · simp
  · intro j hj
    simp [Ne.symm hj]

omit [IsProbabilityMeasure μ] in
private theorem pieces_measurable {Y : Ω → S} (hY : Measurable Y) (f : S → ℝ) (j : S) :
    AEStronglyMeasurable (fun ω => f j * Set.indicator {ω | Y ω = j}
      (fun _ => (1 : ℝ)) ω) μ := by
  exact (measurable_const.mul (measurable_const.indicator
    (hY (measurableSet_singleton j)))).aestronglyMeasurable

private theorem pieces_finite {Y : Ω → S} (hY : Measurable Y) (f : S → ℝ)
    (hf : ∀ j, ‖f j‖ ≤ 1) :
    (∑' j, ∫⁻ ω, ‖f j * Set.indicator {ω | Y ω = j}
      (fun _ => (1 : ℝ)) ω‖ₑ ∂μ) ≠ ∞ := by
  rw [← lintegral_tsum (fun j => (pieces_measurable hY f j).enorm)]
  have heq : (fun ω => ∑' j, ‖f j * Set.indicator {ω | Y ω = j}
      (fun _ => (1 : ℝ)) ω‖ₑ) = fun ω => ‖f (Y ω)‖ₑ := by
    funext ω
    rw [tsum_eq_single (Y ω)]
    · simp
    · intro j hj
      simp [Ne.symm hj]
  rw [heq]
  apply ne_of_lt
  calc
    ∫⁻ ω, ‖f (Y ω)‖ₑ ∂μ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro ω
      change ‖f (Y ω)‖ₑ ≤ (1 : ℝ≥0∞)
      simpa only [← ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hf (Y ω))
    _ < ∞ := by simp

/-- Singleton conditional probabilities determine conditional expectations of bounded functions. -/
theorem condExp_discrete {Y Z : Ω → S} (hY : Measurable Y)
    (Q : StochasticMatrix S) (ℱ : MeasurableSpace Ω)
    (hQ : ∀ j, μ[(fun ω => Set.indicator {ω | Y ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ] =ᵐ[μ] fun ω => realMatrix Q (Z ω) j)
    (f : S → ℝ) (hf : ∀ j, ‖f j‖ ≤ 1) :
    μ[(fun ω => f (Y ω)) | ℱ] =ᵐ[μ]
      fun ω => ∑' j, f j * realMatrix Q (Z ω) j := by
  have hexp : (fun ω => f (Y ω)) = fun ω => ∑' j, f j *
      Set.indicator {ω | Y ω = j} (fun _ => (1 : ℝ)) ω := by
    funext ω
    exact (expansion Y f ω).symm
  rw [hexp]
  refine (condExp_tsum (fun j => pieces_measurable (mΩ := mΩ) hY f j)
    (pieces_finite (mΩ := mΩ) hY f hf)).trans ?_
  have hj : ∀ j, μ[(fun ω => f j * Set.indicator {ω | Y ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ] =ᵐ[μ]
      fun ω => f j * realMatrix Q (Z ω) j := by
    intro j
    exact (condExp_smul (f j) _ ℱ).trans ((hQ j).fun_comp (fun x => f j * x))
  filter_upwards [ae_all_iff.mpr hj] with ω hω
  exact tsum_congr hω

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
private theorem entry_norm_le_one (Q : StochasticMatrix S) (i j : S) :
    ‖realMatrix Q i j‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (realMatrix_nonneg Q i j)]
  exact (ENNReal.toReal_mono (by simp) (entry_le_one Q i j)).trans_eq (by simp)

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
private theorem event_toReal (Q : StochasticMatrix S) (i : S) (A : Set S) :
    (event Q i A).toReal =
      ∑' j, (A.indicator (fun _ => (1 : ℝ)) j) * realMatrix Q i j := by
  change (∑' j, A.indicator (Q i) j).toReal = _
  calc
    _ = ∑' j, (A.indicator (Q i) j).toReal :=
      ENNReal.tsum_toReal_eq (fun j => by
        by_cases hj : j ∈ A <;> simp [hj, entry_ne_top])
    _ = _ := by
      apply tsum_congr
      intro j
      by_cases hj : j ∈ A <;> simp [hj, realMatrix]

variable [Nonempty S] {P : StochasticMatrix S} {ν : ProbabilityLaw S}
  {X : ℕ → Ω → S} {ℱ : Filtration ℕ mΩ}

/-- The tower property iterates the given one-step identity on singletons. -/
theorem transition_singleton (h : IsMarkovChain P ν X ℱ μ) (m n : ℕ) (j : S) :
    μ[(fun ω => Set.indicator {ω | X (n + m) ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ]
      fun ω => realMatrix (power P m) (X n ω) j := by
  induction m generalizing j with
  | zero =>
    simp only [Nat.add_zero]
    have hmeas : Measurable[ℱ n] (fun ω => Set.indicator {ω | X n ω = j}
        (fun _ => (1 : ℝ)) ω) :=
      measurable_const.indicator ((h.1 n) (measurableSet_singleton j))
    have hint : Integrable (fun ω => Set.indicator {ω | X n ω = j}
        (fun _ => (1 : ℝ)) ω) μ :=
      (integrable_const (1 : ℝ)).indicator (h.1.measurable (measurableSet_singleton j))
    have hc := condExp_of_stronglyMeasurable (ℱ.le n) hmeas.stronglyMeasurable hint
    rw [hc]
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hj : X n ω = j
    · simp [power_zero, realMatrix, identity_apply, hj]
    · simp [power_zero, realMatrix, identity_apply, hj, Ne.symm hj]
  | succ m ih =>
    have ht : μ[(fun ω => Set.indicator {ω | X (n + (m + 1)) ω = j}
        (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ]
        μ[(fun ω => realMatrix P (X (n + m) ω) j) | ℱ n] := by
      have hs := h.2.2 (n + m) j
      rw [Nat.add_assoc] at hs
      exact (condExp_condExp_of_le (ℱ.mono (Nat.le_add_right n m))
        (ℱ.le (n + m))).symm.trans (condExp_congr_ae hs)
    refine ht.trans ?_
    have hh := condExp_discrete (hY := h.1.measurable) (power P m) (ℱ n)
      (fun x => ih x) (fun x => realMatrix P x j)
      (fun x => entry_norm_le_one P x j)
    refine hh.trans (Filter.Eventually.of_forall fun ω => ?_)
    change (∑' x, realMatrix P x j * realMatrix (power P m) (X n ω) x) =
      realMatrix (power P (m + 1)) (X n ω) j
    exact (tsum_congr (fun x => mul_comm _ _)).trans
      (realMatrix_comp_tsum (power P m) P (X n ω) j).symm

/-- Extend the iterated singleton formula to every subset of the discrete state space. -/
theorem transition_event (h : IsMarkovChain P ν X ℱ μ) (m n : ℕ) (A : Set S) :
    μ[(fun ω => Set.indicator {ω | X (n + m) ω ∈ A}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ]
      fun ω => (event (power P m) (X n ω) A).toReal := by
  have hh := condExp_discrete (hY := h.1.measurable) (power P m) (ℱ n)
    (fun j => transition_singleton h m n j) (A.indicator (fun _ => (1 : ℝ)))
    (fun j => by by_cases hj : j ∈ A <;> simp [hj])
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ)) (X (n + m) ω)) =
      (fun ω => Set.indicator {ω | X (n + m) ω ∈ A} (fun _ => (1 : ℝ)) ω) := by
    funext ω
    by_cases hj : X (n + m) ω ∈ A <;> simp [hj]
  rw [heq] at hh
  refine hh.trans ?_
  exact Filter.Eventually.of_forall (fun ω => (event_toReal (power P m) (X n ω) A).symm)

/-- Integrating the time-zero transition formula identifies each marginal mass. -/
theorem marginal_mass (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) (j : S) :
    μ {ω | X n ω = j} = evolve ν P n j := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
    ((evolve ν P n).apply_ne_top j)).mp
  have hf : Measurable (fun i => realMatrix (power P n) i j) := measurable_of_countable _
  have hfi : Integrable (fun i => realMatrix (power P n) i j) ν.toMeasure :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun i => entry_norm_le_one (power P n) i j)
  have hmap : ∫ ω, realMatrix (power P n) (X 0 ω) j ∂μ =
      ∫ i, realMatrix (power P n) i j ∂ν.toMeasure := by
    rw [← integral_map_of_stronglyMeasurable h.1.measurable hf.stronglyMeasurable,
      chain_initial_law P ν X ℱ μ h]
  have hsum : ∫ i, realMatrix (power P n) i j ∂ν.toMeasure =
      (evolve ν P n j).toReal := by
    rw [integral_countable hfi]
    change (∑' i, (ν.toMeasure {i}).toReal * realMatrix (power P n) i j) =
      (∑' i, ν i * power P n i j).toReal
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top (ν.apply_ne_top i)
      ((power P n i).apply_ne_top j))]
    apply tsum_congr
    intro i
    rw [law_measure_singleton, ENNReal.toReal_mul]
    rfl
  have hc := integral_congr_ae (transition_singleton h n 0 j)
  rw [integral_condExp (ℱ.le 0)] at hc
  simp only [Nat.zero_add] at hc
  have hset : MeasurableSet {ω | X n ω = j} := h.1.measurable (measurableSet_singleton j)
  rw [integral_indicator hset, setIntegral_const, smul_eq_mul, mul_one] at hc
  exact hc.trans (hmap.trans hsum)

/-- Singleton equality determines the entire marginal probability measure. -/
theorem marginal_measure (h : IsMarkovChain P ν X ℱ μ) (n : ℕ) :
    μ.map (X n) = (evolve ν P n).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply h.1.measurable (measurableSet_singleton j), law_measure_singleton]
  exact marginal_mass h n j

end DeterministicTransitions

/-- Deterministic-time transition probabilities in the chain's supplied filtration. -/
theorem transition_probabilities : DeterministicTransitionsSpec.transition_probabilities.{u, v} := by
  intro S _ _ _ _ Ω mΩ P ν X ℱ μ _ h m n A
  exact DeterministicTransitions.transition_event h m n A

/-- The law at every time, including zero, is the initial law acted on by the transition power. -/
theorem marginal_law : DeterministicTransitionsSpec.marginal_law.{u, v} := by
  intro S _ _ _ _ Ω mΩ P ν X ℱ μ _ h n
  exact DeterministicTransitions.marginal_measure h n

end
end P207.Markov
