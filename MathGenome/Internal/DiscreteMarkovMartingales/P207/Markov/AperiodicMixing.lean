import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.AperiodicMixing
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.EventualPositivity
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.StationaryReturnTimes
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.ClosedRecurrentClasses
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.MaximalCoupling

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical MeasureTheory
universe u
namespace P207.Markov
noncomputable section

namespace AperiodicMixing

/-- An actual probability law with independent coordinates. -/
def productLaw {S : Type u} (μ ν : ProbabilityLaw S) : ProbabilityLaw (S × S) :=
  ⟨fun p => μ p.1 * ν p.2, ENNReal.summable.hasSum_iff.mpr (by
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, ν.tsum_coe, mul_one, μ.tsum_coe])⟩

@[simp] lemma productLaw_apply {S : Type u} (μ ν : ProbabilityLaw S) (p : S × S) :
    productLaw μ ν p = μ p.1 * ν p.2 := rfl

lemma productLaw_fst {S : Type u} (μ ν : ProbabilityLaw S) :
    (productLaw μ ν).map Prod.fst = μ := by
  ext i
  simp only [PMF.map_apply, productLaw_apply, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · simp [ENNReal.tsum_mul_left, ν.tsum_coe]
  · intro a ha
    simp [Ne.symm ha]

lemma productLaw_snd {S : Type u} (μ ν : ProbabilityLaw S) :
    (productLaw μ ν).map Prod.snd = ν := by
  ext j
  simp only [PMF.map_apply, productLaw_apply, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm, tsum_eq_single j]
  · simp [ENNReal.tsum_mul_right, μ.tsum_coe]
  · intro b hb
    simp [Ne.symm hb]

def productKernel {S : Type u} (P : StochasticMatrix S) : StochasticMatrix (S × S) :=
  fun p => productLaw (P p.1) (P p.2)

lemma productKernel_power {S : Type u} (P : StochasticMatrix S) (n : ℕ)
    (p q : S × S) :
    power (productKernel P) n p q = power P n p.1 q.1 * power P n p.2 q.2 := by
  induction n generalizing p q with
  | zero =>
    simp only [power_zero, identity_apply]
    by_cases h₁ : q.1 = p.1 <;> by_cases h₂ : q.2 = p.2 <;>
      simp [Prod.ext_iff, h₁, h₂]
  | succ n ih =>
    rw [chapman_kolmogorov (productKernel P) n 1]
    simp only [power_one, productKernel, productLaw_apply, ih, ENNReal.tsum_prod']
    simp_rw [mul_mul_mul_comm (power P n p.1 _) (power P n p.2 _),
      ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    rw [chapman_kolmogorov P n 1, chapman_kolmogorov P n 1]
    simp only [power_one]

lemma productKernel_irreducible {S : Type u} (P : StochasticMatrix S)
    (hI : Irreducible P) (hA : ∀ i, Aperiodic P i) :
    Irreducible (productKernel P) := by
  have hreach (p q : S × S) : Accessible (productKernel P) p q := by
    obtain ⟨N, hN⟩ := eventual_power_pos P hI hA p.1 q.1
    obtain ⟨M, hM⟩ := eventual_power_pos P hI hA p.2 q.2
    refine ⟨max N M, ?_⟩
    rw [productKernel_power]
    exact ENNReal.mul_pos (hN _ (le_max_left _ _)).ne' (hM _ (le_max_right _ _)).ne'
  exact fun p q => ⟨hreach p q, hreach q p⟩

lemma productKernel_stationary {S : Type u} (P : StochasticMatrix S)
    (π : ProbabilityLaw S) (hπ : IsStationary P π) :
    IsStationary (productKernel P) (productLaw π π) := by
  apply (stationary_iff_masses _ _).mpr
  intro q
  simp only [productLaw_apply, productKernel, ENNReal.tsum_prod']
  simp_rw [mul_mul_mul_comm (π _) (π _), ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_right, (stationary_iff_masses P π).mp hπ]

/-- On the diagonal a single transition is used for both coordinates. -/
def coalescingKernel {S : Type u} (P : StochasticMatrix S) :
    StochasticMatrix (S × S) :=
  fun p => if p.1 = p.2 then (P p.1).map (fun i => (i, i)) else productKernel P p

lemma coalescingKernel_fst {S : Type u} (P : StochasticMatrix S) (p : S × S) :
    (coalescingKernel P p).map Prod.fst = P p.1 := by
  by_cases hp : p.1 = p.2
  · rw [coalescingKernel, if_pos hp, PMF.map_comp]
    exact PMF.map_id _
  · simp [coalescingKernel, hp, productKernel, productLaw_fst]

lemma coalescingKernel_snd {S : Type u} (P : StochasticMatrix S) (p : S × S) :
    (coalescingKernel P p).map Prod.snd = P p.2 := by
  by_cases hp : p.1 = p.2
  · rw [coalescingKernel, if_pos hp, PMF.map_comp]
    change (P p.1).map id = P p.2
    rw [PMF.map_id, hp]
  · simp [coalescingKernel, hp, productKernel, productLaw_snd]

lemma power_map_of_kernel_map {S T : Type u} (Q : StochasticMatrix S)
    (P : StochasticMatrix T) (f : S → T) (hf : ∀ x, (Q x).map f = P (f x))
    (n : ℕ) (x : S) : (power Q n x).map f = power P n (f x) := by
  induction n with
  | zero => simp [power_zero, identity, PMF.pure_map]
  | succ n ih =>
    change ((power Q n x).bind Q).map f = (power P n (f x)).bind P
    rw [PMF.map_bind]
    simp_rw [hf]
    calc
      _ = ((power Q n x).map f).bind P := (PMF.bind_map _ _ _).symm
      _ = _ := by rw [ih]

lemma coalescingKernel_power_diagonal {S : Type u} (P : StochasticMatrix S)
    (n : ℕ) (i : S) :
    power (coalescingKernel P) n (i, i) = (power P n i).map (fun j => (j, j)) := by
  induction n with
  | zero => simp [power_zero, identity, PMF.pure_map]
  | succ n ih =>
    change (power (coalescingKernel P) n (i, i)).bind (coalescingKernel P) =
      ((power P n i).bind P).map (fun j => (j, j))
    rw [ih, PMF.bind_map, PMF.map_bind]
    congr 1
    funext j
    simp [Function.comp_def, coalescingKernel]

lemma lawEvent_bind {S T : Type u} (μ : ProbabilityLaw S) (Q : S → ProbabilityLaw T)
    (A : Set T) : lawEvent (μ.bind Q) A = ∑' i, μ i * lawEvent (Q i) A := by
  classical
  unfold lawEvent
  change (∑' j, A.indicator (fun j => ∑' i, μ i * Q i j) j) = _
  calc
    (∑' j, A.indicator (fun j => ∑' i, μ i * Q i j) j) =
        ∑' j, ∑' i, μ i * A.indicator (Q i) j := by
      apply tsum_congr
      intro j
      by_cases hj : j ∈ A <;> simp [hj]
    _ = ∑' i, μ i * ∑' j, A.indicator (Q i) j := by
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]

lemma lawEvent_pure {S : Type u} (i : S) (A : Set S) :
    lawEvent (PMF.pure i) A = if i ∈ A then 1 else 0 := by
  unfold lawEvent
  rw [tsum_eq_single i]
  · simp [Set.indicator, PMF.pure_apply]
  · intro j hj
    by_cases hjA : j ∈ A <;> simp [Set.indicator, hjA, PMF.pure_apply, hj]

lemma lawEvent_map {S T : Type u} (μ : ProbabilityLaw S) (f : S → T) (A : Set T) :
    lawEvent (μ.map f) A = lawEvent μ (f ⁻¹' A) := by
  rw [PMF.map, lawEvent_bind]
  unfold lawEvent
  apply tsum_congr
  intro i
  rw [show (∑' j, A.indicator ((PMF.pure ∘ f) i) j) =
    if f i ∈ A then 1 else 0 from lawEvent_pure (f i) A]
  by_cases hi : f i ∈ A <;> simp [hi]

def diagonal {S : Type u} : Set (S × S) := {p | p.1 = p.2}

lemma coalescingKernel_disagreement_diagonal {S : Type u} (P : StochasticMatrix S)
    (n : ℕ) (i : S) :
    lawEvent (power (coalescingKernel P) n (i, i)) diagonalᶜ = 0 := by
  rw [coalescingKernel_power_diagonal, lawEvent_map]
  simp [lawEvent, diagonal]

section Discrete
variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

local instance (Q : StochasticMatrix S) (i : S) : IsProbabilityMeasure (statePathLaw Q i) :=
  by
  letI : Nonempty S := ⟨i⟩
  exact pathLaw_probability Q (PMF.pure i)

lemma productKernel_hitting_diagonal (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hI : Irreducible P) (hA : ∀ i, Aperiodic P i) (hπ : IsStationary P π)
    (p : S × S) : hittingProbability (productKernel P) diagonal p = 1 := by
  letI : Nonempty S := ⟨p.1⟩
  have hK := productKernel_irreducible P hI hA
  have hrec := positiveRecurrent_recurrent (productKernel P) (p.1, p.1)
    (stationary_positiveRecurrent _ _ hK (productKernel_stationary P π hπ) _)
  have hhit := hittingProbability_recurrent_of_accessible (productKernel P) hrec
    (hK (p.1, p.1) p).1
  apply le_antisymm (hittingProbability_le_one _ _ _) _
  rw [← hhit]
  apply measure_mono
  intro ω hω
  obtain ⟨n, hn⟩ := (hittingTime_finite_iff _ ω).mp hω
  apply (hittingTime_finite_iff _ ω).mpr
  exact ⟨n, by simpa only [Set.mem_singleton_iff] using hn ▸ (show (p.1, p.1) ∈ diagonal from rfl)⟩

/-- This proves finite meeting for the actual canonical coalescing chain;
it is derived from recurrence, not supplied as a certificate. -/
lemma coalescingKernel_hitting_diagonal (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hI : Irreducible P) (hA : ∀ i, Aperiodic P i) (hπ : IsStationary P π)
    (p : S × S) : hittingProbability (coalescingKernel P) diagonal p = 1 := by
  letI : Nonempty S := ⟨p.1⟩
  apply le_antisymm (hittingProbability_le_one _ _ _) _
  rw [← productKernel_hitting_diagonal P π hI hA hπ p]
  apply hittingProbability_least (productKernel P) diagonal
    (hittingProbability (coalescingKernel P) diagonal)
  · exact fun q hq => hittingProbability_boundary _ _ _ hq
  · intro q hq
    rw [hittingProbability_harmonic _ _ _ hq]
    have hq' : q.1 ≠ q.2 := hq
    simp only [action, coalescingKernel, if_neg hq']

lemma hitting_cutoff_of_mem (Q : StochasticMatrix S) (A : Set S) (i : S)
    (hi : i ∈ A) (n : ℕ) :
    statePathLaw Q i {ω | hittingTime A ω ≤ n} = 1 := by
  letI : Nonempty S := ⟨i⟩
  apply (mem_ae_iff_prob_eq_one (measurableSet_hittingTime_le A n)).mp
  filter_upwards [coordinate_zero_ae Q i] with ω hω
  exact (hittingTime_le_iff _ _ _).mpr ⟨0, Nat.zero_le n, hω ▸ hi⟩

lemma hitting_cutoff_zero (Q : StochasticMatrix S) (A : Set S) (i : S) :
    statePathLaw Q i {ω | hittingTime A ω ≤ (0 : ℕ)} =
      if i ∈ A then 1 else 0 := by
  letI : Nonempty S := ⟨i⟩
  by_cases hi : i ∈ A
  · simpa only [if_pos hi] using hitting_cutoff_of_mem Q A i hi 0
  · rw [if_neg hi]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [coordinate_zero_ae Q i] with ω hω
    change ¬ hittingTime A ω ≤ (0 : ℕ)
    intro hn
    obtain ⟨k, hk, hkA⟩ := (hittingTime_le_iff A ω 0).mp hn
    have hk0 : k = 0 := by omega
    subst k
    exact hi (hω ▸ hkA)

/-- For an absorbing set the finite-time mass outside it is precisely the
mass not yet hit. This is proved by the finite-horizon recursion. -/
lemma cutoff_add_outside (Q : StochasticMatrix S) (A : Set S)
    (habs : ∀ i ∈ A, ∀ n, lawEvent (power Q n i) Aᶜ = 0)
    (n : ℕ) (i : S) :
    statePathLaw Q i {ω | hittingTime A ω ≤ n} + lawEvent (power Q n i) Aᶜ = 1 := by
  letI : Nonempty S := ⟨i⟩
  induction n generalizing i with
  | zero =>
    rw [hitting_cutoff_zero, power_zero]
    change (if i ∈ A then 1 else 0) + lawEvent (PMF.pure i) Aᶜ = 1
    rw [lawEvent_pure]
    by_cases hi : i ∈ A <;> simp [hi]
  | succ n ih =>
    by_cases hi : i ∈ A
    · rw [hitting_cutoff_of_mem Q A i hi, habs i hi, add_zero]
    · rw [hittingTime_cutoff_step Q A i hi n]
      have he : power Q (n + 1) i = (Q i).bind (power Q n) := by
        rw [Nat.add_comm n 1, power_add, power_one]
        rfl
      rw [he, lawEvent_bind, ← ENNReal.tsum_add]
      simp_rw [← mul_add, ih, mul_one]
      exact (Q i).tsum_coe

lemma tendsto_outside_of_hitting (Q : StochasticMatrix S) (A : Set S)
    (habs : ∀ i ∈ A, ∀ n, lawEvent (power Q n i) Aᶜ = 0)
    (hhit : ∀ i, hittingProbability Q A i = 1) (i : S) :
    Tendsto (fun n => (lawEvent (power Q n i) Aᶜ).toReal) atTop (𝓝 0) := by
  letI : Nonempty S := ⟨i⟩
  have hm : Monotone (fun n : ℕ => {ω : ℕ → S | hittingTime A ω ≤ n}) := by
    intro n m hnm ω hω
    exact hω.trans (WithTop.coe_le_coe.mpr hnm)
  have hu : (⋃ n : ℕ, {ω : ℕ → S | hittingTime A ω ≤ n}) =
      {ω | hittingTime A ω < ⊤} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, hittingTime_le_iff,
      hittingTime_finite_iff]
    exact ⟨fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩⟩
  have ht := tendsto_measure_iUnion_atTop (μ := statePathLaw Q i) hm
  rw [hu] at ht
  change Tendsto (fun n : ℕ => statePathLaw Q i {ω | hittingTime A ω ≤ n}) atTop
    (𝓝 (hittingProbability Q A i)) at ht
  rw [hhit i] at ht
  have htR := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  have he (n : ℕ) : (lawEvent (power Q n i) Aᶜ).toReal =
      1 - (statePathLaw Q i {ω | hittingTime A ω ≤ n}).toReal := by
    have h := congrArg ENNReal.toReal (cutoff_add_outside Q A habs n i)
    rw [ENNReal.toReal_add (measure_ne_top _ _)
      (by rw [lawEvent_eq_measure]; exact measure_ne_top _ _), ENNReal.toReal_one] at h
    linarith
  simp_rw [he]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub htR

lemma tendsto_coalescing_disagreement (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hI : Irreducible P) (hA : ∀ i, Aperiodic P i) (hπ : IsStationary P π)
    (p : S × S) :
    Tendsto (fun n => (lawEvent (power (coalescingKernel P) n p) diagonalᶜ).toReal)
      atTop (𝓝 0) := by
  apply tendsto_outside_of_hitting _ diagonal
    (fun q hq n => ?_) (coalescingKernel_hitting_diagonal P π hI hA hπ) p
  rcases q with ⟨i, j⟩
  change i = j at hq
  subst j
  exact coalescingKernel_disagreement_diagonal P n i

lemma lawEvent_le_one (μ : ProbabilityLaw S) (A : Set S) : lawEvent μ A ≤ 1 := by
  rw [lawEvent_eq_measure]
  exact prob_le_one

lemma lawEvent_evolve_real (μ : ProbabilityLaw S) (Q : StochasticMatrix S)
    (A : Set S) (n : ℕ) :
    (lawEvent (evolve μ Q n) A).toReal =
      ∑' i, (μ i).toReal * (lawEvent (power Q n i) A).toReal := by
  rw [evolve, lawEvent_bind, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]
  · intro i
    exact ENNReal.mul_ne_top (μ.apply_ne_top i)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (lawEvent_le_one _ _))

/-- A summable probability law dominates every finite-time event probability.
Thus this step has no restrictions on the support of the initial law. -/
lemma tendsto_event_evolve_of_rows (μ : ProbabilityLaw S) (Q : StochasticMatrix S)
    (A : Set S)
    (h : ∀ i, Tendsto (fun n => (lawEvent (power Q n i) A).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (lawEvent (evolve μ Q n) A).toReal) atTop (𝓝 0) := by
  simp_rw [lawEvent_evolve_real]
  have ht : Tendsto
      (fun n => ∑' i, (μ i).toReal * (lawEvent (power Q n i) A).toReal)
      atTop (𝓝 (∑' _i : S, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (summable_mass μ)
    · intro i
      simpa using (tendsto_const_nhds (x := (μ i).toReal)).mul (h i)
    · apply Filter.Eventually.of_forall
      intro n i
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg)]
      have hb : (lawEvent (power Q n i) A).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top (lawEvent_le_one _ _)
      simpa using mul_le_mul_of_nonneg_left hb (ENNReal.toReal_nonneg (a := μ i))
  simpa using ht

lemma evolve_coalescing_fst (P : StochasticMatrix S) (μ ν : ProbabilityLaw S) (n : ℕ) :
    (evolve (productLaw μ ν) (coalescingKernel P) n).map Prod.fst = evolve μ P n := by
  unfold evolve
  rw [PMF.map_bind]
  simp_rw [power_map_of_kernel_map _ P Prod.fst (coalescingKernel_fst P)]
  calc
    _ = ((productLaw μ ν).map Prod.fst).bind (power P n) := (PMF.bind_map _ _ _).symm
    _ = _ := by rw [productLaw_fst]

lemma evolve_coalescing_snd (P : StochasticMatrix S) (μ ν : ProbabilityLaw S) (n : ℕ) :
    (evolve (productLaw μ ν) (coalescingKernel P) n).map Prod.snd = evolve ν P n := by
  unfold evolve
  rw [PMF.map_bind]
  simp_rw [power_map_of_kernel_map _ P Prod.snd (coalescingKernel_snd P)]
  calc
    _ = ((productLaw μ ν).map Prod.snd).bind (power P n) := (PMF.bind_map _ _ _).symm
    _ = _ := by rw [productLaw_snd]

lemma totalVariation_nonneg (μ ν : ProbabilityLaw S) : 0 ≤ totalVariation μ ν := by
  rw [totalVariation_eq_half_tsum]
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => abs_nonneg _))

/-- The actual pair process is the canonical path law of the constructed
kernel. Both coordinate marginals have exactly the prescribed evolution. -/
lemma coalescing_path_marginals (P : StochasticMatrix S) (μ ν : ProbabilityLaw S)
    (n : ℕ) :
    (pathLaw (coalescingKernel P) (productLaw μ ν)).map (fun ω => (ω n).1) =
      (evolve μ P n).toMeasure ∧
    (pathLaw (coalescingKernel P) (productLaw μ ν)).map (fun ω => (ω n).2) =
      (evolve ν P n).toMeasure := by
  letI : Nonempty S := ⟨μ.support_nonempty.choose⟩
  have hm := DeterministicTransitions.marginal_measure
    (coordinate_isMarkovChain (coalescingKernel P) (productLaw μ ν)) n
  constructor
  · have hf := congrArg (fun m : Measure (S × S) => m.map Prod.fst) hm
    rw [Measure.map_map measurable_fst (measurable_pi_apply n),
      PMF.toMeasure_map Prod.fst _ measurable_fst, evolve_coalescing_fst] at hf
    exact hf
  · have hs := congrArg (fun m : Measure (S × S) => m.map Prod.snd) hm
    rw [Measure.map_map measurable_snd (measurable_pi_apply n),
      PMF.toMeasure_map Prod.snd _ measurable_snd, evolve_coalescing_snd] at hs
    exact hs

/-- Disintegration at time zero transfers the proved state-start hitting
property to the constructed pair chain with any initial probability law. -/
lemma coalescing_path_meeting (P : StochasticMatrix S) (π μ : ProbabilityLaw S)
    (hI : Irreducible P) (hA : ∀ i, Aperiodic P i) (hπ : IsStationary P π) :
    ∀ᵐ ω ∂pathLaw (coalescingKernel P) (productLaw μ π),
      hittingTime diagonal ω < ⊤ := by
  letI : Nonempty S := ⟨μ.support_nonempty.choose⟩
  let Q := coalescingKernel P
  let ρ := productLaw μ π
  let B : Set (ℕ → S × S) := {ω | hittingTime diagonal ω < ⊤}
  have hB : MeasurableSet B := measurableSet_hittingTime_finite diagonal
  apply (mem_ae_iff_prob_eq_one hB).mpr
  let K := (pathKernel Q).comap (coordinate 0) (measurable_pi_apply 0)
  have hm := FixedFutureLaw.future_measure (coordinate_isMarkovChain Q ρ)
    0 Set.univ MeasurableSet.univ
  rw [Measure.restrict_univ] at hm
  simp only [Nat.zero_add, coordinate] at hm
  change (pathLaw Q ρ).map id = K ∘ₘ pathLaw Q ρ at hm
  rw [Measure.map_id] at hm
  have he := congrArg (fun m : Measure (ℕ → S × S) => m B) hm
  rw [Measure.bind_apply hB K.aemeasurable] at he
  change pathLaw Q ρ B = ∫⁻ ω, hittingProbability Q diagonal (ω 0) ∂pathLaw Q ρ at he
  have hhit (q : S × S) : hittingProbability Q diagonal q = 1 :=
    coalescingKernel_hitting_diagonal P π hI hA hπ q
  simp_rw [hhit] at he
  simpa using he

end Discrete
end AperiodicMixing

/-- Total variation convergence from every initial law, including arbitrary
infinite support. The joint law is obtained by iterating the coalescing kernel. -/
theorem aperiodic_tendsto_totalVariation_evolve :
    AperiodicMixingSpec.aperiodic_tendsto_totalVariation_evolve.{u} := by
  intro S _ _ _ P π hI hA hπ μ
  let Q := AperiodicMixing.coalescingKernel P
  let ρ := AperiodicMixing.productLaw μ π
  have ht := AperiodicMixing.tendsto_event_evolve_of_rows ρ Q
    AperiodicMixing.diagonalᶜ
    (AperiodicMixing.tendsto_coalescing_disagreement P π hI hA hπ)
  apply squeeze_zero (fun n => AperiodicMixing.totalVariation_nonneg _ _) (fun n => ?_) ht
  have hf : (evolve ρ Q n).toMeasure.map Prod.fst = (evolve μ P n).toMeasure := by
    rw [PMF.toMeasure_map Prod.fst _ measurable_fst, AperiodicMixing.evolve_coalescing_fst]
  have hs : (evolve ρ Q n).toMeasure.map Prod.snd = π.toMeasure := by
    rw [PMF.toMeasure_map Prod.snd _ measurable_snd, AperiodicMixing.evolve_coalescing_snd,
      stationary_evolve P π hπ n]
  simpa only [lawEvent_eq_measure, AperiodicMixing.diagonal, Set.compl_ofPred] using
    totalVariation_le_disagreement (evolve ρ Q n).toMeasure (evolve μ P n) π
      Prod.fst Prod.snd measurable_fst measurable_snd hf hs

theorem aperiodic_tendsto_totalVariation :
    AperiodicMixingSpec.aperiodic_tendsto_totalVariation.{u} := by
  intro S _ _ _ P π hI hA hπ i
  simpa only [evolve, PMF.pure_bind] using
    aperiodic_tendsto_totalVariation_evolve P π hI hA hπ (PMF.pure i)

/-- W14 constructs the stationary law and supplies uniqueness. The only
existence hypothesis here is a positive recurrent state of the given chain. -/
theorem exists_unique_stationary_mixing :
    AperiodicMixingSpec.exists_unique_stationary_mixing.{u} := by
  intro S _ _ _ P hI hpos hA
  obtain ⟨π, hπ⟩ := (stationary_probability_iff_positiveRecurrent P hI).mpr hpos
  exact ⟨π, hπ, fun ρ hρ => stationary_probability_unique P ρ π hI hρ hπ,
    aperiodic_tendsto_totalVariation P π hI hA hπ,
    aperiodic_tendsto_totalVariation_evolve P π hI hA hπ⟩

end
end P207.Markov
