import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Interfaces

open MeasureTheory
open scoped ENNReal MeasureTheory Classical

universe u v

namespace P207.Markov

noncomputable section

/- Candidate aliases expose exactly the shared canonical objects. -/
namespace Interfaces

abbrev ProbabilityLaw : InterfacesSpec.ProbabilityLawType.{u} :=
  @P207.Markov.ProbabilityLaw.{u}

abbrev StochasticMatrix : InterfacesSpec.StochasticMatrixType.{u} :=
  @P207.Markov.StochasticMatrix.{u}

abbrev lawEvent : InterfacesSpec.lawEventType.{u} :=
  @P207.Markov.lawEvent.{u}

abbrev event : InterfacesSpec.eventType.{u} :=
  @P207.Markov.event.{u}

abbrev action : InterfacesSpec.actionType.{u} :=
  @P207.Markov.action.{u}

abbrev comp : InterfacesSpec.compType.{u} :=
  @P207.Markov.comp.{u}

abbrev identity : InterfacesSpec.identityType.{u} :=
  @P207.Markov.identity.{u}

abbrev power : InterfacesSpec.powerType.{u} :=
  @P207.Markov.power.{u}

abbrev evolve : InterfacesSpec.evolveType.{u} :=
  @P207.Markov.evolve.{u}

abbrev realMatrix : InterfacesSpec.realMatrixType.{u} :=
  @P207.Markov.realMatrix.{u}

abbrev ofMass : InterfacesSpec.ofMassType.{u} :=
  @P207.Markov.ofMass.{u}

abbrev ofRealMatrix : InterfacesSpec.ofRealMatrixType.{u} :=
  @P207.Markov.ofRealMatrix.{u}

abbrev IsMarkovChain : InterfacesSpec.IsMarkovChainType.{u, v} :=
  @P207.Markov.IsMarkovChain.{u, v}

end Interfaces

theorem entry_nonneg {S : Type u} (P : StochasticMatrix S) (i j : S) :
    0 ≤ P i j := by
  exact zero_le

theorem entry_le_one {S : Type u} (P : StochasticMatrix S) (i j : S) :
    P i j ≤ 1 := by
  exact (P i).coe_le_one j

theorem entry_ne_top {S : Type u} (P : StochasticMatrix S) (i j : S) :
    P i j ≠ ∞ := by
  exact (P i).apply_ne_top j

theorem row_sum {S : Type u} (P : StochasticMatrix S) (i : S) :
    ∑' j, P i j = 1 := by
  exact (P i).tsum_coe

theorem ofMass_apply {S : Type u} (p : S → S → ℝ≥0∞) (h : ∀ i, ∑' j, p i j = 1) (i j : S) :
    ofMass p h i j = p i j := by
  rfl

theorem ofMass_rows {S : Type u} (P : StochasticMatrix S) :
    ofMass (fun i j => P i j) (fun i => (P i).tsum_coe) = P := by
  rfl

theorem lawEvent_eq_subtype {S : Type u} (ν : ProbabilityLaw S) (A : Set S) :
    lawEvent ν A = ∑' j : A, ν j := by
  classical
  exact (tsum_subtype A ν).symm

theorem event_eq_subtype {S : Type u} (P : StochasticMatrix S) (i : S) (A : Set S) :
    event P i A = ∑' j : A, P i j := by
  exact lawEvent_eq_subtype (P i) A

theorem lawEvent_eq_measure {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S) (A : Set S) :
    lawEvent ν A = ν.toMeasure A := by
  exact (ν.toMeasure_apply_eq_tsum A).symm

theorem event_eq_measure {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (P : StochasticMatrix S) (i : S) (A : Set S) :
    event P i A = (P i).toMeasure A := by
  exact lawEvent_eq_measure (P i) A

theorem law_measure_singleton {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S) (i : S) :
    ν.toMeasure {i} = ν i := by
  exact ν.toMeasure_apply_singleton i (measurableSet_singleton i)

theorem law_measure_probability {S : Type u} [MeasurableSpace S] (ν : ProbabilityLaw S) :
    IsProbabilityMeasure ν.toMeasure := by
  infer_instance

theorem measure_law_roundtrip {S : Type u} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ν.toPMF.toMeasure = ν := by
  exact ν.toPMF_toMeasure

theorem law_measure_roundtrip {S : Type u} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S) :
    ν.toMeasure.toPMF = ν := by
  exact ν.toMeasure_toPMF

theorem event_univ {S : Type u} (P : StochasticMatrix S) (i : S) :
    event P i Set.univ = 1 := by
  simp [event, lawEvent]

theorem event_singleton {S : Type u} (P : StochasticMatrix S) (i j : S) :
    event P i {j} = P i j := by
  classical
  simp [event, lawEvent, Set.indicator_singleton]

theorem action_apply {S : Type u} (P : StochasticMatrix S) (f : S → ℝ≥0∞) (i : S) :
    action P f i = ∑' j, P i j * f j := by
  rfl

theorem action_indicator {S : Type u} (P : StochasticMatrix S) (A : Set S) (i : S) :
    action P (A.indicator (fun _ => 1)) i = event P i A := by
  classical
  apply tsum_congr
  intro j
  by_cases h : j ∈ A <;> simp [h]

theorem comp_apply {S : Type u} (P Q : StochasticMatrix S) (i j : S) :
    comp P Q i j = ∑' x, P i x * Q x j := by
  rfl

theorem comp_row_sum {S : Type u} (P Q : StochasticMatrix S) (i : S) :
    ∑' j, comp P Q i j = 1 := by
  exact (comp P Q i).tsum_coe

theorem comp_assoc {S : Type u} (P Q R : StochasticMatrix S) :
    comp (comp P Q) R = comp P (comp Q R) := by
  funext i
  exact PMF.bind_bind (P i) Q R

theorem identity_apply {S : Type u} (i j : S) :
    identity i j = if j = i then 1 else 0 := by
  exact PMF.pure_apply i j

theorem identity_comp {S : Type u} (P : StochasticMatrix S) :
    comp identity P = P := by
  funext i
  exact PMF.pure_bind i P

theorem comp_identity {S : Type u} (P : StochasticMatrix S) :
    comp P identity = P := by
  funext i
  exact PMF.bind_pure (P i)

theorem power_zero {S : Type u} (P : StochasticMatrix S) :
    power P 0 = identity := by
  rfl

theorem power_succ {S : Type u} (P : StochasticMatrix S) (n : ℕ) :
    power P (n + 1) = comp (power P n) P := by
  rfl

theorem power_one {S : Type u} (P : StochasticMatrix S) :
    power P 1 = P := by
  exact identity_comp P

theorem power_add {S : Type u} (P : StochasticMatrix S) (m n : ℕ) :
    power P (m + n) = comp (power P m) (power P n) := by
  induction n with
  | zero => exact (comp_identity _).symm
  | succ n ih =>
    rw [Nat.add_succ, power_succ, ih, power_succ, comp_assoc]

theorem chapman_kolmogorov {S : Type u} (P : StochasticMatrix S) (m n : ℕ) (i j : S) :
    power P (m + n) i j = ∑' x, power P m i x * power P n x j := by
  rw [power_add]
  rfl

theorem power_row_sum {S : Type u} (P : StochasticMatrix S) (n : ℕ) (i : S) :
    ∑' j, power P n i j = 1 := by
  exact (power P n i).tsum_coe

theorem evolve_apply {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ) (j : S) :
    evolve ν P n j = ∑' i, ν i * power P n i j := by
  rfl

theorem evolve_sum {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ) :
    ∑' j, evolve ν P n j = 1 := by
  exact (evolve ν P n).tsum_coe

theorem evolve_zero {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) :
    evolve ν P 0 = ν := by
  exact PMF.bind_pure ν

theorem evolve_add {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (m n : ℕ) :
    evolve ν P (m + n) = evolve (evolve ν P m) P n := by
  unfold evolve
  rw [power_add]
  exact (PMF.bind_bind ν (power P m) (power P n)).symm

theorem realMatrix_nonneg {S : Type u} (P : StochasticMatrix S) (i j : S) :
    0 ≤ realMatrix P i j := by
  exact ENNReal.toReal_nonneg

theorem realMatrix_rowsum {S : Type u} (P : StochasticMatrix S) (i : S) :
    ∑' j, realMatrix P i j = 1 := by
  change ∑' j, (P i j).toReal = 1
  rw [← ENNReal.tsum_toReal_eq (fun j => (P i).apply_ne_top j), (P i).tsum_coe]
  rfl

theorem ofReal_realMatrix {S : Type u} (P : StochasticMatrix S) (i j : S) :
    ENNReal.ofReal (realMatrix P i j) = P i j := by
  exact ENNReal.ofReal_toReal ((P i).apply_ne_top j)

theorem realMatrix_comp_tsum {S : Type u} (P Q : StochasticMatrix S) (i j : S) :
    realMatrix (comp P Q) i j = ∑' x, realMatrix P i x * realMatrix Q x j := by
  change (∑' x, P i x * Q x j).toReal = _
  rw [ENNReal.tsum_toReal_eq (fun x => ENNReal.mul_ne_top ((P i).apply_ne_top x) ((Q x).apply_ne_top j))]
  simp only [realMatrix, ENNReal.toReal_mul]

theorem realMatrix_comp {S : Type u} [Fintype S] (P Q : StochasticMatrix S) :
    realMatrix (comp P Q) = realMatrix P * realMatrix Q := by
  ext i j
  rw [realMatrix_comp_tsum, tsum_fintype]
  rfl

theorem realMatrix_identity {S : Type u} [Fintype S] [DecidableEq S] :
    realMatrix (identity : StochasticMatrix S) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realMatrix, identity, PMF.pure_apply, Matrix.one_apply, eq_comm, h]

theorem realMatrix_power {S : Type u} [Fintype S] [DecidableEq S] (P : StochasticMatrix S) (n : ℕ) :
    realMatrix (power P n) = realMatrix P ^ n := by
  induction n with
  | zero => exact realMatrix_identity
  | succ n ih => rw [power_succ, realMatrix_comp, ih, pow_succ]

theorem ofRealMatrix_apply {S : Type u} [Fintype S] (p : Matrix S S ℝ) (h₀ : ∀ i j, 0 ≤ p i j) (h₁ : ∀ i, ∑ j, p i j = 1) (i j : S) :
    ofRealMatrix p h₀ h₁ i j = ENNReal.ofReal (p i j) := by
  rfl

theorem realMatrix_ofRealMatrix {S : Type u} [Fintype S] (p : Matrix S S ℝ) (h₀ : ∀ i j, 0 ≤ p i j) (h₁ : ∀ i, ∑ j, p i j = 1) :
    realMatrix (ofRealMatrix p h₀ h₁) = p := by
  ext i j
  exact ENNReal.toReal_ofReal (h₀ i j)

theorem realMatrix_finite_rowsum {S : Type u} [Fintype S] (P : StochasticMatrix S) (i : S) :
    ∑ j, realMatrix P i j = 1 := by
  simpa only [tsum_fintype] using realMatrix_rowsum P i

theorem ofRealMatrix_realMatrix {S : Type u} [Fintype S] (P : StochasticMatrix S) (h₀ : ∀ i j, 0 ≤ realMatrix P i j) (h₁ : ∀ i, ∑ j, realMatrix P i j = 1) :
    ofRealMatrix (realMatrix P) h₀ h₁ = P := by
  funext i
  apply PMF.ext
  intro j
  exact ofReal_realMatrix P i j

theorem isMarkovChain_iff {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω] (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsMarkovChain P ν X ℱ μ ↔
    (∀ n, Measurable[ℱ n] (X n)) ∧
    (∀ i, μ {ω | X 0 ω = i} = ν i) ∧
    ∀ n j, μ[(fun ω => Set.indicator {ω | X (n + 1) ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ] fun ω => (P (X n ω) j).toReal := by
  rfl

theorem chain_initial_law {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω] (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : IsMarkovChain P ν X ℱ μ) :
    μ.map (X 0) = ν.toMeasure := by
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply h.1.measurable (measurableSet_singleton i), law_measure_singleton]
  exact h.2.1 i

end

end P207.Markov
