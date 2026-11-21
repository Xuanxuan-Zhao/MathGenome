import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StationaryReturnTimes
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ExcursionMeasure
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Stationarity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClassRecurrence

open MeasureTheory
open scoped ENNReal Classical
universe u
namespace P207.Markov
noncomputable section

/-- Iteration of the invariance equation for an arbitrary nonnegative measure. -/
theorem invariantMass_power {S : Type u} (P : StochasticMatrix S)
    (f : S → ℝ≥0∞) (hf : ∀ j, ∑' k, f k * P k j = f j) (n : ℕ) (j : S) :
    ∑' k, f k * power P n k j = f j := by
  induction n generalizing j with
  | zero => simp [power_zero, identity_apply]
  | succ n ih =>
    calc
      (∑' k, f k * power P (n + 1) k j) =
          ∑' k, ∑' l, (f k * power P n k l) * P l j := by
        simp_rw [power_succ, comp_apply, ← ENNReal.tsum_mul_left, mul_assoc]
      _ = ∑' l, ∑' k, (f k * power P n k l) * P l j := ENNReal.tsum_comm
      _ = ∑' l, f l * P l j := by simp_rw [ENNReal.tsum_mul_right, ih]
      _ = f j := hf j

/-- A nonnegative invariant measure vanishing at one state vanishes throughout
an irreducible chain, even if its total mass is infinite. -/
theorem invariantMass_eq_zero_of_zero {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (f : S → ℝ≥0∞)
    (hf : ∀ j, ∑' k, f k * P k j = f j) (i : S) (hi : f i = 0) :
    ∀ j, f j = 0 := by
  intro j
  obtain ⟨n, hn⟩ := (hP j i).1
  have hb : f j * power P n j i ≤ 0 := by
    calc
      f j * power P n j i ≤ ∑' k, f k * power P n k i := ENNReal.le_tsum (f := fun k => f k * power P n k i) j
      _ = 0 := (invariantMass_power P f hf n i).trans hi
  exact (mul_eq_zero.mp (le_antisymm hb bot_le)).resolve_right hn.ne'

/-- Two ordered invariant measures with finite coordinates and a common
reference coordinate coincide. Subtraction is justified by adding back the
smaller invariant measure and cancelling its finite coordinate. -/
theorem invariantMass_eq_of_le {S : Type u} (P : StochasticMatrix S)
    (hP : Irreducible P) (f g : S → ℝ≥0∞)
    (hf : ∀ j, ∑' k, f k * P k j = f j)
    (hg : ∀ j, ∑' k, g k * P k j = g j)
    (hgf : ∀ j, g j ≤ f j) (hfin : ∀ j, f j ≠ ⊤)
    (i : S) (hi : g i = f i) : g = f := by
  let d : S → ℝ≥0∞ := fun j => f j - g j
  have hadd (j : S) : d j + g j = f j := tsub_add_cancel_of_le (hgf j)
  have hd : ∀ j, ∑' k, d k * P k j = d j := by
    intro j
    have hgj : g j ≠ ⊤ := ne_top_of_le_ne_top (hfin j) (hgf j)
    apply (ENNReal.add_left_inj hgj).mp
    calc
      (∑' k, d k * P k j) + g j =
          ∑' k, (d k + g k) * P k j := by
        rw [← hg j, ← ENNReal.tsum_add]
        simp_rw [add_mul]
      _ = f j := by simp_rw [hadd]; exact hf j
      _ = d j + g j := (hadd j).symm
  have hdi : d i = 0 := by simp [d, hi]
  have hz := invariantMass_eq_zero_of_zero P hP d hd i hdi
  funext j
  simpa only [hz j, zero_add] using hadd j

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

private def excursionStepMass (P : StochasticMatrix S) (i : S) (n : ℕ) (j : S) : ℝ≥0∞ :=
  statePathLaw P i {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω n = j}

private theorem excursionStepMass_zero (P : StochasticMatrix S) (i j : S) :
    excursionStepMass P i 0 j = if i = j then 1 else 0 := by
  let : Nonempty S := ⟨i⟩
  have h := (coordinate_isMarkovChain P (PMF.pure i)).2.1 j
  simpa [excursionStepMass, zero_lt_returnTime, coordinate, PMF.pure_apply, statePathLaw, eq_comm] using h

private theorem excursionStepMass_self_succ (P : StochasticMatrix S) (i : S) (n : ℕ) :
    excursionStepMass P i (n + 1) i = 0 := by
  unfold excursionStepMass
  have he : {ω : ℕ → S | ((n + 1 : ℕ) : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = i} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ω ⟨hlt, heq⟩
    have hle := (positiveReturnTime_le_iff coordinate i ω (n + 1)).mpr
      ⟨n + 1, by omega, le_rfl, heq⟩
    exact (not_lt_of_ge hle) hlt
  rw [he, measure_empty]

private theorem excursionStepMass_succ (P : StochasticMatrix S) (i j : S) (n : ℕ)
    (hji : j ≠ i) :
    excursionStepMass P i (n + 1) j = ∑' k, excursionStepMass P i n k * P k j := by
  rw [show (∑' k, excursionStepMass P i n k * P k j) =
    statePathLaw P i {ω | (n : WithTop ℕ) < returnTime i ω ∧ ω (n + 1) = j} from
      excursion_transition P i j n]
  unfold excursionStepMass
  congr 1
  ext ω
  constructor
  · rintro ⟨hlt, heq⟩
    exact ⟨lt_trans (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)) hlt, heq⟩
  · rintro ⟨hlt, heq⟩
    refine ⟨lt_of_not_ge ?_, heq⟩
    intro hle
    obtain ⟨k, hk, hkn, hki⟩ :=
      (positiveReturnTime_le_iff coordinate i ω (n + 1)).mp hle
    have hkn' : ¬ k ≤ n := by
      intro h
      have hle' := (positiveReturnTime_le_iff coordinate i ω n).mpr ⟨k, hk, h, hki⟩
      exact (not_lt_of_ge hle') hlt
    have hk' : k = n + 1 := by omega
    subst k
    exact hji (heq.symm.trans hki)

/-- Partial killed-chain potentials are bounded by every invariant measure
whose reference mass is one. This is a finite induction, with no recurrence
assumption and no assumed occupation certificate. -/
theorem excursionMass_le_invariantMass (P : StochasticMatrix S) (i : S)
    (f : S → ℝ≥0∞) (hf : ∀ j, ∑' k, f k * P k j = f j) (hi : f i = 1) :
    ∀ j, excursionMass P i j ≤ f j := by
  have hsum (N : ℕ) (j : S) :
      ∑ n ∈ Finset.range N, excursionStepMass P i n j ≤ f j := by
    induction N generalizing j with
    | zero => simp
    | succ N ih =>
      by_cases hji : j = i
      · subst j
        rw [Finset.sum_range_succ']
        simp only [excursionStepMass_self_succ, Finset.sum_const_zero, zero_add,
          excursionStepMass_zero, ite_true, hi]
        exact le_rfl
      · rw [Finset.sum_range_succ', excursionStepMass_zero, ite_eq_right (Ne.symm hji), add_zero]
        simp_rw [excursionStepMass_succ P i j _ hji]
        have hswap : (∑ n ∈ Finset.range N, ∑' k, excursionStepMass P i n k * P k j) =
            ∑' k, (∑ n ∈ Finset.range N, excursionStepMass P i n k) * P k j := by
          clear ih
          induction N with
          | zero => simp
          | succ N ihN =>
            simp only [Finset.sum_range_succ, ihN, add_mul, ENNReal.tsum_add]
        rw [hswap]
        calc
          (∑' k, (∑ n ∈ Finset.range N, excursionStepMass P i n k) * P k j) ≤
              ∑' k, f k * P k j :=
            ENNReal.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (ih k) (show 0 ≤ P k j from zero_le))
          _ = f j := hf j
  intro j
  rw [excursionMass_eq_tsum, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => hsum N j

/-- Domination for an arbitrary stationary probability of positive reference
mass; in particular no irreducibility or recurrence is assumed here. -/
theorem excursionMass_le_stationary (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) (i : S) (hi : 0 < π i) :
    ∀ j, excursionMass P i j ≤ π j / π i := by
  apply excursionMass_le_invariantMass P i (fun j => π j / π i)
  · intro j
    simp only [div_eq_mul_inv]
    simp_rw [mul_right_comm (π _) (π i)⁻¹]
    rw [ENNReal.tsum_mul_right, (stationary_iff_masses P π).mp hπ j]
  · exact ENNReal.div_self hi.ne' (π.apply_ne_top i)

/-- This direction includes construction of an actual stationary probability. -/
theorem exists_stationary_of_positiveRecurrent (P : StochasticMatrix S)
    (i : S) (hi : PositiveRecurrent P i) :
    ∃ π : ProbabilityLaw S, IsStationary P π := by
  obtain ⟨π, _, hπ⟩ := excursion_stationary_probability P i hi
  exact ⟨π, hπ⟩

/-- The probabilistic domination bound implies finite mean return, without
assuming recurrence or any occupation equality. -/
theorem positiveRecurrent_of_excursionMass_le (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (i : S) (hi : 0 < π i)
    (hdom : ∀ j, excursionMass P i j ≤ π j / π i) : PositiveRecurrent P i := by
  have hb : meanReturnTime P i ≤ (π i)⁻¹ := by
    rw [← excursionMass_total]
    calc
      (∑' j, excursionMass P i j) ≤ ∑' j, π j / π i := ENNReal.tsum_le_tsum hdom
      _ = (π i)⁻¹ := by simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right, π.tsum_coe, one_mul]
  exact lt_of_le_of_lt hb (ENNReal.inv_lt_top.mpr hi)

/-- Algebraic identification of the excursion measure from the domination
bound. The bound is the sole additional hypothesis of this assembly lemma. -/
theorem excursionMass_eq_of_le_stationary (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (hP : Irreducible P) (hπ : IsStationary P π)
    (i : S) (hdom : ∀ j, excursionMass P i j ≤ π j / π i) :
    ∀ j, excursionMass P i j = π j / π i := by
  have hpos := stationary_positive P π hP hπ i
  have hrec := positiveRecurrent_recurrent P i
    (positiveRecurrent_of_excursionMass_le P π i hpos hdom)
  have hinv : ∀ j, ∑' k, (π k / π i) * P k j = π j / π i := by
    intro j
    simp only [div_eq_mul_inv]
    simp_rw [mul_right_comm (π _) (π i)⁻¹]
    rw [ENNReal.tsum_mul_right, (stationary_iff_masses P π).mp hπ j]
  have hfin : ∀ j, π j / π i ≠ ⊤ := by
    intro j
    exact ENNReal.div_ne_top (π.apply_ne_top j) hpos.ne'
  have he := invariantMass_eq_of_le P hP (fun j => π j / π i) (excursionMass P i)
    hinv (excursionMass_invariant P i hrec) hdom hfin i
    (by rw [excursionMass_self, ENNReal.div_self hpos.ne' (π.apply_ne_top i)])
  exact congrFun he

/-- Every state of an irreducible chain with a stationary probability has
finite mean return, derived from domination rather than assumed recurrence. -/
theorem stationary_positiveRecurrent : StationaryReturnTimesSpec.stationary_positiveRecurrent.{u} := by
  intro S _ _ _ P π hP hπ i
  have hi := stationary_positive P π hP hπ i
  exact positiveRecurrent_of_excursionMass_le P π i hi
    (excursionMass_le_stationary P π hπ i hi)

theorem stationary_probability_iff_positiveRecurrent :
    StationaryReturnTimesSpec.stationary_probability_iff_positiveRecurrent.{u} := by
  intro S _ _ _ P hP
  constructor
  · rintro ⟨π, hπ⟩
    obtain ⟨i, hi⟩ : ∃ i, 0 < π i := by
      by_contra hn
      have hz : ∀ i, π i = 0 := fun i => le_antisymm
        (not_lt.mp (fun hh => hn ⟨i, hh⟩)) bot_le
      have ht := π.tsum_coe
      simp only [hz, tsum_zero] at ht
      exact zero_ne_one ht
    exact ⟨i, stationary_positiveRecurrent P π hP hπ i⟩
  · rintro ⟨i, hi⟩
    exact exists_stationary_of_positiveRecurrent P i hi

theorem stationary_excursionMass : StationaryReturnTimesSpec.stationary_excursionMass.{u} := by
  intro S _ _ _ P π hP hπ i
  exact excursionMass_eq_of_le_stationary P π hP hπ i
    (excursionMass_le_stationary P π hπ i (stationary_positive P π hP hπ i))

theorem stationary_meanReturnTime : StationaryReturnTimesSpec.stationary_meanReturnTime.{u} := by
  intro S _ _ _ P π hP hπ i
  have ht : meanReturnTime P i = (π i)⁻¹ := by
    rw [← excursionMass_total]
    simp_rw [stationary_excursionMass P π hP hπ i, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, π.tsum_coe, one_mul]
  rw [ht, one_div, inv_inv]

theorem stationary_probability_unique : StationaryReturnTimesSpec.stationary_probability_unique.{u} := by
  intro S _ _ _ P π ρ hP hπ hρ
  apply PMF.ext
  intro i
  exact (stationary_meanReturnTime P π hP hπ i).trans
    (stationary_meanReturnTime P ρ hP hρ i).symm

omit [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Stationary mass propagates along any accessible route, also in a reducible chain. -/
theorem stationary_positive_of_accessible (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : IsStationary P π) {i j : S} (hi : 0 < π i) (hij : Accessible P i j) :
    0 < π j := by
  obtain ⟨n, hn⟩ := hij
  have he := congrArg (fun ν : PMF S => ν j) (stationary_evolve P π hπ n)
  rw [evolve_apply] at he
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hi, hn⟩)
    ((ENNReal.le_tsum (f := fun k => π k * power P n k j) i).trans_eq he)

/-- A positive recurrent state makes every accessible state positive recurrent.
This directly proves the class consequence, including proper closed classes,
without changing the original chain or its canonical expectations. -/
theorem positiveRecurrent_of_accessible (P : StochasticMatrix S) {i j : S}
    (hi : PositiveRecurrent P i) (hij : Accessible P i j) : PositiveRecurrent P j := by
  obtain ⟨π, hmass, hπ⟩ := excursion_stationary_probability P i hi
  have hpi : 0 < π i := by
    rw [hmass i, excursionMass_self]
    exact ENNReal.div_pos one_ne_zero hi.ne
  have hpj := stationary_positive_of_accessible P π hπ hpi hij
  exact positiveRecurrent_of_excursionMass_le P π j hpj
    (excursionMass_le_stationary P π hπ j hpj)

theorem positiveRecurrent_iff_of_communicate :
    StationaryReturnTimesSpec.positiveRecurrent_iff_of_communicate.{u} := by
  intro S _ _ _ P i j h
  exact ⟨fun hi => positiveRecurrent_of_accessible P hi h.1,
    fun hj => positiveRecurrent_of_accessible P hj h.2⟩

theorem nullRecurrent_iff_of_communicate :
    StationaryReturnTimesSpec.nullRecurrent_iff_of_communicate.{u} := by
  intro S _ _ _ P i j h
  have hp := positiveRecurrent_iff_of_communicate P h
  have hr := recurrent_iff_of_communicate P h
  have hn (k : S) : NullRecurrent P k ↔ Recurrent P k ∧ ¬ PositiveRecurrent P k := by
    simp only [NullRecurrent, PositiveRecurrent, not_lt, top_le_iff]
  rw [hn i, hn j, hr, hp]

end
end P207.Markov
