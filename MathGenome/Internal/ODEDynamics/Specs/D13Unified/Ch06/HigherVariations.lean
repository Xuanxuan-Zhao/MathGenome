import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Independent statements for paper.tex, Theorem d13:06:variations.

The state space is any finite dimensional real normed space. `H` is the
actual iterated Fréchet derivative of the shared canonical maximal flow.
`OrderedFinpartition j` enumerates set partitions of `Fin j`, with each
block and the list of blocks in a canonical order (increasing elements
within a block, increasing greatest elements between blocks). It does not
enumerate arbitrary orderings of the same partition.
-/
noncomputable section
open Set
open scoped ContDiff
open Specs.D13Unified.Ch01.AutonomousParameters

namespace D13Unified.Ch06.HigherVariations
open StateDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The j-th state derivative; the zeroth order is also useful in calculus. -/
def H (F : AutonomousODE E) (j : ℕ) (t : ℝ) (ξ : E) : E [×j]→L[ℝ] E :=
  iteratedFDeriv ℝ j (flow F t) ξ

/-- The summand for one set partition, retaining all block directions. -/
def partitionTerm (F : AutonomousODE E) {j : ℕ} (c : OrderedFinpartition j)
    (t : ℝ) (ξ : E) (v : Fin j → E) : E :=
  iteratedFDeriv ℝ c.length (autonomousEvalValue F) (flow F t ξ)
    (fun i => H F (c.partSize i) t ξ (v ∘ c.emb i))

def partitionSum (F : AutonomousODE E) (j : ℕ) (t : ℝ) (ξ : E)
    (v : Fin j → E) : E :=
  ∑ c : OrderedFinpartition j, partitionTerm F c t ξ v

/-- Exactly the terms with at least two blocks. For positive j, the omitted
term is the unique one-block partition. -/
def lowerForcing (F : AutonomousODE E) (j : ℕ) (t : ℝ) (ξ : E)
    (v : Fin j → E) : E :=
  ∑ c : OrderedFinpartition j,
    if 1 < c.length then partitionTerm F c t ξ v else 0

/-- The unique partition consisting of the whole nonempty index set. -/
def oneBlock (j : ℕ) (hj : 0 < j) : OrderedFinpartition j where
  length := 1
  partSize := fun _ => j
  partSize_pos := fun _ => hj
  emb := fun _ => id
  emb_strictMono := fun _ => strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by intro i _ l _ h; exact (h (Subsingleton.elim _ _)).elim
  cover := fun x => ⟨0,x,rfl⟩

def initialValue {j : ℕ} (v : Fin j → E) : E :=
  if hj : j = 1 then v ⟨0, by omega⟩ else 0

end D13Unified.Ch06.HigherVariations

namespace Specs.D13Unified.Ch06.HigherVariations
open _root_.D13Unified _root_.D13Unified.Ch06
open StateDerivative _root_.D13Unified.Ch06.HigherVariations
universe u

def InitialValues : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ ξ ∈ F.domain,
      (∀ v : Fin 1 → E, H F 1 0 ξ v = v 0) ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ k → H F j 0 ξ = 0

/-- A separately useful spatial chain rule. It does not by itself assert
that the time derivative of the highest variation exists. -/
def SpatialChainRule : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ q ∈ flowDomain F, ∀ v : Fin j → E,
      iteratedFDeriv ℝ j ((autonomousEvalValue F) ∘ flow F q.1) q.2 v =
        partitionSum F j q.1 q.2 v

def TimeEquations : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ q ∈ flowDomain F, ∀ v : Fin j → E,
      HasDerivAt (fun t => H F j t q.2 v) (partitionSum F j q.1 q.2 v) q.1

/-- Symmetry includes equality of all mixed directional components. -/
def Symmetry : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ q ∈ flowDomain F, ∀ v : Fin j → E, ∀ σ : Equiv.Perm (Fin j),
      H F j q.1 q.2 (v ∘ σ) = H F j q.1 q.2 v

/-- The unique one-block contribution and the lower-order forcing.
The last clause proves every block in that forcing has size less than j. -/
def PartitionDecomposition : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (j : ℕ) (hj : 0 < j) (t : ℝ) (ξ : E) (v : Fin j → E),
      partitionTerm F (oneBlock j hj) t ξ v =
        fderiv ℝ (autonomousEvalValue F) (flow F t ξ) (H F j t ξ v) ∧
      partitionSum F j t ξ v =
        fderiv ℝ (autonomousEvalValue F) (flow F t ξ) (H F j t ξ v) + lowerForcing F j t ξ v ∧
      ∀ c : OrderedFinpartition j, 1 < c.length → ∀ i, c.partSize i < j

def LinearHierarchy : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ j : ℕ, 1 ≤ j → j ≤ k →
    ∀ ξ ∈ F.domain, ∀ v : Fin j → E,
      ContinuousOn (fun t => H F j t ξ v) (flowInterval F ξ).carrier ∧
      H F j 0 ξ v = initialValue v ∧
      ContinuousOn (fun t => lowerForcing F j t ξ v) (flowInterval F ξ).carrier ∧
      (∀ t ∈ (flowInterval F ξ).carrier,
        HasDerivAt (fun r => H F j r ξ v)
          (coefficient F ξ t (H F j t ξ v) + lowerForcing F j t ξ v) t) ∧
      ∀ Y : ℝ → E, ContinuousOn Y (flowInterval F ξ).carrier →
        Y 0 = initialValue v →
        (∀ t ∈ (flowInterval F ξ).carrier,
          HasDerivAt Y (coefficient F ξ t (Y t) + lowerForcing F j t ξ v) t) →
        EqOn Y (fun t => H F j t ξ v) (flowInterval F ξ).carrier

def SecondVariation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 2 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ ξ ∈ F.domain, ∀ v w : E,
      H F 2 0 ξ ![v,w] = 0 ∧
      ∀ t ∈ (flowInterval F ξ).carrier,
        HasDerivAt (fun r => H F 2 r ξ ![v,w])
          (coefficient F ξ t (H F 2 t ξ ![v,w]) +
            iteratedFDeriv ℝ 2 (autonomousEvalValue F) (flow F t ξ)
              ![H F 1 t ξ (fun _ => v), H F 1 t ξ (fun _ => w)]) t

end Specs.D13Unified.Ch06.HigherVariations
