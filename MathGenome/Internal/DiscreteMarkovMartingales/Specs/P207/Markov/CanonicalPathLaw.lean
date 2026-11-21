import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Interfaces
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Canonical countable-state path law, paper.tex §2.2. All measures on
`ℕ → S` use its product measurable space. The shared definitions below
contain no assumed existence, uniqueness, or Markov certificates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

universe u v

namespace P207.Markov

noncomputable section

/-- Evaluation of the path at time `n`. -/
def coordinate {S : Type u} (n : ℕ) (ω : ℕ → S) : S := ω n

/-- Atomic prefix through time `n`, including time zero. -/
def prefixCylinder {S : Type u} (n : ℕ) (x : ℕ → S) : Set (ℕ → S) :=
  {ω | ∀ k ≤ n, ω k = x k}

/-- The natural filtration of the canonical coordinates. -/
def coordinateFiltration {S : Type u} [MeasurableSpace S] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
  P207.naturalFiltration coordinate (fun n => measurable_pi_apply n)

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The one-step history kernel only reads the last state. -/
def historyKernel (P : StochasticMatrix S) (n : ℕ) :
    Kernel ((k : Finset.Iic n) → S) S :=
  Kernel.ofFunOfCountable (fun x => (P (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure)

instance historyKernel_isMarkovKernel (P : StochasticMatrix S) (n : ℕ) :
    IsMarkovKernel (historyKernel P n) := by
  constructor
  intro x
  change IsProbabilityMeasure (P (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure
  infer_instance

/-- Ionescu--Tulcea with initial distribution `ν` and the last-state kernels. -/
@[instance_reducible] def pathLaw (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    Measure (ℕ → S) := Kernel.trajMeasure ν.toMeasure (historyKernel P)

instance pathLaw_isProbabilityMeasure (P : StochasticMatrix S) (ν : ProbabilityLaw S) :
    IsProbabilityMeasure (pathLaw P ν) := by
  unfold pathLaw
  infer_instance

/-- Law when the initial state is fixed. -/
@[instance_reducible] def statePathLaw (P : StochasticMatrix S) (i : S) :
    Measure (ℕ → S) := pathLaw P (PMF.pure i)

/-- The measurable family of laws started at each state. -/
def pathKernel (P : StochasticMatrix S) : Kernel S (ℕ → S) :=
  Kernel.ofFunOfCountable (statePathLaw P)

/-- `E_i` for real path functions (Bochner integral, as in Mathlib). -/
def stateExpectation (P : StochasticMatrix S) (i : S) (g : (ℕ → S) → ℝ) : ℝ :=
  ∫ ω, g ω ∂statePathLaw P i

namespace CanonicalPathLawSpec

/-- Types and values for the candidate aliases of the shared objects. -/
def coordinateType := {S : Type u} → ℕ → (ℕ → S) → S
def coordinateValue : coordinateType.{u} := @coordinate

def prefixCylinderType := {S : Type u} → ℕ → (ℕ → S) → Set (ℕ → S)
def prefixCylinderValue : prefixCylinderType.{u} := @prefixCylinder

def coordinateFiltrationType := {S : Type u} → [MeasurableSpace S] →
  Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S))
def coordinateFiltrationValue : coordinateFiltrationType.{u} := @coordinateFiltration

def historyKernelType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → (n : ℕ) →
    Kernel ((k : Finset.Iic n) → S) S
def historyKernelValue : historyKernelType.{u} := @historyKernel

def pathLawType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → ProbabilityLaw S → Measure (ℕ → S)
def pathLawValue : pathLawType.{u} := @pathLaw

def statePathLawType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → Measure (ℕ → S)
def statePathLawValue : statePathLawType.{u} := @statePathLaw

def pathKernelType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → Kernel S (ℕ → S)
def pathKernelValue : pathKernelType.{u} := @pathKernel

def stateExpectationType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ((ℕ → S) → ℝ) → ℝ
def stateExpectationValue : stateExpectationType.{u} := @stateExpectation

-- Each theorem is a full proposition, independent of the implementation.
def pathLaw_probability : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (ν : ProbabilityLaw S),
    IsProbabilityMeasure (pathLaw P ν)

def pathLaw_prefix : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (n : ℕ) (x : ℕ → S),
    pathLaw P ν (prefixCylinder n x) = ν (x 0) * ∏ k ∈ Finset.range n, P (x k) (x (k + 1))

def pathLaw_unique : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (ν : ProbabilityLaw S)
    (ρ : Measure (ℕ → S)) [IsProbabilityMeasure ρ],
    (∀ n x, ρ (prefixCylinder n x) =
      ν (x 0) * ∏ k ∈ Finset.range n, P (x k) (x (k + 1))) → ρ = pathLaw P ν

def coordinate_isMarkovChain : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (ν : ProbabilityLaw S),
    IsMarkovChain P ν coordinate coordinateFiltration (pathLaw P ν)

def chain_pathLaw : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ → μ.map (fun ω n => X n ω) = pathLaw P ν

def pathKernel_apply : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S),
    pathKernel P i = statePathLaw P i

def pathKernel_markov : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S), IsMarkovKernel (pathKernel P)

def measurable_statePathLaw : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S), Measurable (statePathLaw P)

end CanonicalPathLawSpec
end
end P207.Markov
