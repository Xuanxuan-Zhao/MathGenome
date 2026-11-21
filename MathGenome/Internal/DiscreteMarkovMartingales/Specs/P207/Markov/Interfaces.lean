import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Matrix.Mul

/-!
Canonical countable-state interfaces for paper.tex, §2.1 and the
Chapman--Kolmogorov assertion in §2.2. A row is represented by a PMF;
in particular no row can have infinite mass at a point. ENNReal
multiplication supplies the stipulated convention `0 * ∞ = 0`.
The process always uses its explicitly supplied filtration.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory Classical

universe u v

namespace P207.Markov

abbrev ProbabilityLaw (S : Type u) := PMF S
abbrev StochasticMatrix (S : Type u) := S → ProbabilityLaw S

noncomputable section

def lawEvent {S : Type u} (ν : ProbabilityLaw S) (A : Set S) : ℝ≥0∞ :=
  ∑' j, A.indicator ν j

def event {S : Type u} (P : StochasticMatrix S) (i : S) (A : Set S) : ℝ≥0∞ :=
  lawEvent (P i) A

def action {S : Type u} (P : StochasticMatrix S) (f : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  ∑' j, P i j * f j

def comp {S : Type u} (P Q : StochasticMatrix S) : StochasticMatrix S :=
  fun i => (P i).bind Q

def identity {S : Type u} : StochasticMatrix S := PMF.pure

def power {S : Type u} (P : StochasticMatrix S) : ℕ → StochasticMatrix S :=
  Nat.rec identity (fun _ Q => comp Q P)

def evolve {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S)
    (n : ℕ) : ProbabilityLaw S := ν.bind (power P n)

def realMatrix {S : Type u} (P : StochasticMatrix S) : Matrix S S ℝ :=
  fun i j => (P i j).toReal

/-- Every matrix of nonnegative extended masses with row sums one is represented. -/
def ofMass {S : Type u} (p : S → S → ℝ≥0∞) (h : ∀ i, ∑' j, p i j = 1) :
    StochasticMatrix S :=
  fun i => ⟨p i, ENNReal.summable.hasSum_iff.mpr (h i)⟩

/-- Conversely, every ordinary finite real stochastic matrix is represented. -/
def ofRealMatrix {S : Type u} [Fintype S] (p : Matrix S S ℝ)
    (h₀ : ∀ i j, 0 ≤ p i j) (h₁ : ∀ i, ∑ j, p i j = 1) : StochasticMatrix S :=
  fun i => PMF.ofFintype (fun j => ENNReal.ofReal (p i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h₀ i j), h₁ i]
    exact ENNReal.ofReal_one)

/-- The full discrete sigma algebra is explicit, as is the probability-space
assumption. Adaptation and the one-step condition refer to this same `ℱ`. -/
def IsMarkovChain {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  Adapted ℱ X ∧
    (∀ i, μ {ω | X 0 ω = i} = ν i) ∧
    ∀ n j, μ[(fun ω => Set.indicator {ω | X (n + 1) ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ] fun ω => realMatrix P (X n ω) j

end

namespace InterfacesSpec

def ProbabilityLawType :=
  Type u → Type u

noncomputable def ProbabilityLawValue : ProbabilityLawType.{u} :=
  PMF

def StochasticMatrixType :=
  Type u → Type u

noncomputable def StochasticMatrixValue : StochasticMatrixType.{u} :=
  fun S => S → ProbabilityLaw S

def lawEventType :=
  {S : Type u} → ProbabilityLaw S → Set S → ℝ≥0∞

noncomputable def lawEventValue : lawEventType.{u} :=
  fun {_} ν A => ∑' j, A.indicator ν j

def eventType :=
  {S : Type u} → StochasticMatrix S → S → Set S → ℝ≥0∞

noncomputable def eventValue : eventType.{u} :=
  fun {_} P i A => lawEvent (P i) A

def actionType :=
  {S : Type u} → StochasticMatrix S → (S → ℝ≥0∞) → S → ℝ≥0∞

noncomputable def actionValue : actionType.{u} :=
  fun {_} P f i => ∑' j, P i j * f j

def compType :=
  {S : Type u} → StochasticMatrix S → StochasticMatrix S → StochasticMatrix S

noncomputable def compValue : compType.{u} :=
  fun {_} P Q i => (P i).bind Q

def identityType :=
  {S : Type u} → StochasticMatrix S

noncomputable def identityValue : identityType.{u} :=
  fun {_} => PMF.pure

def powerType :=
  {S : Type u} → StochasticMatrix S → ℕ → StochasticMatrix S

noncomputable def powerValue : powerType.{u} :=
  fun {_} P => Nat.rec identity (fun _ Q => comp Q P)

def evolveType :=
  {S : Type u} → ProbabilityLaw S → StochasticMatrix S → ℕ → ProbabilityLaw S

noncomputable def evolveValue : evolveType.{u} :=
  fun {_} ν P n => ν.bind (power P n)

def realMatrixType :=
  {S : Type u} → StochasticMatrix S → Matrix S S ℝ

noncomputable def realMatrixValue : realMatrixType.{u} :=
  fun {_} P i j => (P i j).toReal

def ofMassType :=
  {S : Type u} → (p : S → S → ℝ≥0∞) → (∀ i, ∑' j, p i j = 1) → StochasticMatrix S

noncomputable def ofMassValue : ofMassType.{u} :=
  @ofMass

def ofRealMatrixType :=
  {S : Type u} → [Fintype S] → (p : Matrix S S ℝ) → (∀ i j, 0 ≤ p i j) → (∀ i, ∑ j, p i j = 1) → StochasticMatrix S

noncomputable def ofRealMatrixValue : ofRealMatrixType.{u} :=
  @ofRealMatrix

def IsMarkovChainType :=
  {S : Type u} → [Countable S] → [Nonempty S] → [MeasurableSpace S] → [DiscreteMeasurableSpace S] → {Ω : Type v} → [m : MeasurableSpace Ω] → StochasticMatrix S → ProbabilityLaw S → (ℕ → Ω → S) → Filtration ℕ m → (μ : Measure Ω) → [IsProbabilityMeasure μ] → Prop

noncomputable def IsMarkovChainValue : IsMarkovChainType.{u, v} :=
  fun {_} [_] [_] [_] [_] {_} [_] P ν X ℱ μ [_] =>
  (∀ n, Measurable[ℱ n] (X n)) ∧
  (∀ i, μ {ω | X 0 ω = i} = ν i) ∧
  ∀ n j, μ[(fun ω => Set.indicator {ω | X (n + 1) ω = j}
    (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ] fun ω => (P (X n ω) j).toReal

def entry_nonneg : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  0 ≤ P i j

def entry_le_one : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  P i j ≤ 1

def entry_ne_top : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  P i j ≠ ∞

def row_sum : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S),
  ∑' j, P i j = 1

def ofMass_apply : Prop :=
  ∀ {S : Type u} (p : S → S → ℝ≥0∞) (h : ∀ i, ∑' j, p i j = 1) (i j : S),
  ofMass p h i j = p i j

def ofMass_rows : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
  ofMass (fun i j => P i j) (fun i => (P i).tsum_coe) = P

def lawEvent_eq_subtype : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (A : Set S),
  lawEvent ν A = ∑' j : A, ν j

def event_eq_subtype : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S) (A : Set S),
  event P i A = ∑' j : A, P i j

def lawEvent_eq_measure : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S) (A : Set S),
  lawEvent ν A = ν.toMeasure A

def event_eq_measure : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (P : StochasticMatrix S) (i : S) (A : Set S),
  event P i A = (P i).toMeasure A

def law_measure_singleton : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S) (i : S),
  ν.toMeasure {i} = ν i

def law_measure_probability : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (ν : ProbabilityLaw S),
  IsProbabilityMeasure ν.toMeasure

def measure_law_roundtrip : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν],
  ν.toPMF.toMeasure = ν

def law_measure_roundtrip : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] (ν : ProbabilityLaw S),
  ν.toMeasure.toPMF = ν

def event_univ : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S),
  event P i Set.univ = 1

def event_singleton : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  event P i {j} = P i j

def action_apply : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (f : S → ℝ≥0∞) (i : S),
  action P f i = ∑' j, P i j * f j

def action_indicator : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (A : Set S) (i : S),
  action P (A.indicator (fun _ => 1)) i = event P i A

def comp_apply : Prop :=
  ∀ {S : Type u} (P Q : StochasticMatrix S) (i j : S),
  comp P Q i j = ∑' x, P i x * Q x j

def comp_row_sum : Prop :=
  ∀ {S : Type u} (P Q : StochasticMatrix S) (i : S),
  ∑' j, comp P Q i j = 1

def comp_assoc : Prop :=
  ∀ {S : Type u} (P Q R : StochasticMatrix S),
  comp (comp P Q) R = comp P (comp Q R)

def identity_apply : Prop :=
  ∀ {S : Type u} (i j : S),
  identity i j = if j = i then 1 else 0

def identity_comp : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
  comp identity P = P

def comp_identity : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
  comp P identity = P

def power_zero : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
  power P 0 = identity

def power_succ : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (n : ℕ),
  power P (n + 1) = comp (power P n) P

def power_one : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S),
  power P 1 = P

def power_add : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (m n : ℕ),
  power P (m + n) = comp (power P m) (power P n)

def chapman_kolmogorov : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (m n : ℕ) (i j : S),
  power P (m + n) i j = ∑' x, power P m i x * power P n x j

def power_row_sum : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (n : ℕ) (i : S),
  ∑' j, power P n i j = 1

def evolve_apply : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ) (j : S),
  evolve ν P n j = ∑' i, ν i * power P n i j

def evolve_sum : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (n : ℕ),
  ∑' j, evolve ν P n j = 1

def evolve_zero : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S),
  evolve ν P 0 = ν

def evolve_add : Prop :=
  ∀ {S : Type u} (ν : ProbabilityLaw S) (P : StochasticMatrix S) (m n : ℕ),
  evolve ν P (m + n) = evolve (evolve ν P m) P n

def realMatrix_nonneg : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  0 ≤ realMatrix P i j

def realMatrix_rowsum : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i : S),
  ∑' j, realMatrix P i j = 1

def ofReal_realMatrix : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (i j : S),
  ENNReal.ofReal (realMatrix P i j) = P i j

def realMatrix_comp_tsum : Prop :=
  ∀ {S : Type u} (P Q : StochasticMatrix S) (i j : S),
  realMatrix (comp P Q) i j = ∑' x, realMatrix P i x * realMatrix Q x j

def realMatrix_comp : Prop :=
  ∀ {S : Type u} [Fintype S] (P Q : StochasticMatrix S),
  realMatrix (comp P Q) = realMatrix P * realMatrix Q

def realMatrix_identity : Prop :=
  ∀ {S : Type u} [Fintype S] [DecidableEq S],
  realMatrix (identity : StochasticMatrix S) = 1

def realMatrix_power : Prop :=
  ∀ {S : Type u} [Fintype S] [DecidableEq S] (P : StochasticMatrix S) (n : ℕ),
  realMatrix (power P n) = realMatrix P ^ n

def ofRealMatrix_apply : Prop :=
  ∀ {S : Type u} [Fintype S] (p : Matrix S S ℝ) (h₀ : ∀ i j, 0 ≤ p i j) (h₁ : ∀ i, ∑ j, p i j = 1) (i j : S),
  ofRealMatrix p h₀ h₁ i j = ENNReal.ofReal (p i j)

def realMatrix_ofRealMatrix : Prop :=
  ∀ {S : Type u} [Fintype S] (p : Matrix S S ℝ) (h₀ : ∀ i j, 0 ≤ p i j) (h₁ : ∀ i, ∑ j, p i j = 1),
  realMatrix (ofRealMatrix p h₀ h₁) = p

def realMatrix_finite_rowsum : Prop :=
  ∀ {S : Type u} [Fintype S] (P : StochasticMatrix S) (i : S),
  ∑ j, realMatrix P i j = 1

def ofRealMatrix_realMatrix : Prop :=
  ∀ {S : Type u} [Fintype S] (P : StochasticMatrix S) (h₀ : ∀ i j, 0 ≤ realMatrix P i j) (h₁ : ∀ i, ∑ j, realMatrix P i j = 1),
  ofRealMatrix (realMatrix P) h₀ h₁ = P

def isMarkovChain_iff : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω] (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
  IsMarkovChain P ν X ℱ μ ↔
    (∀ n, Measurable[ℱ n] (X n)) ∧
    (∀ i, μ {ω | X 0 ω = i} = ν i) ∧
    ∀ n j, μ[(fun ω => Set.indicator {ω | X (n + 1) ω = j}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ] fun ω => (P (X n ω) j).toReal

def chain_initial_law : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S] [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω] (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : IsMarkovChain P ν X ℱ μ),
  μ.map (X 0) = ν.toMeasure

end InterfacesSpec

end P207.Markov
