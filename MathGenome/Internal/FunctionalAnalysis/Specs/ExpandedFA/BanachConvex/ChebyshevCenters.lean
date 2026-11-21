import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Bounded

/-! The Chebyshev stage of paper.tex, `fa2:p2:asymptotic-center`.
The ambient space is real, and all suprema below are ordinary real suprema.
Nonemptiness and boundedness are explicit hypotheses whenever the supremum
is used as a radius. No compactness or positive diameter is required for
existence, uniqueness or convergence of minimizing sequences. -/
namespace ExpandedFA.BanachConvex.ChebyshevCenters
open Set Filter
universe u
noncomputable section

/-- Supremum of all distances to the set. -/
def radius {X : Type u} [NormedAddCommGroup X] (A : Set X) (x : X) : ℝ :=
  sSup ((fun a => ‖x - a‖) '' A)

/-- The threshold formulation of coercivity on the whole space. -/
def RadiusCoercive {X : Type u} [NormedAddCommGroup X] (A : Set X) : Prop :=
  ∀ b : ℝ, ∃ R : ℝ, ∀ x : X, R ≤ ‖x‖ → b < radius A x

/-- A center belongs to C and minimizes the actual radius over all of C. -/
def IsCenter {X : Type u} [NormedAddCommGroup X] (C A : Set X) (c : X) : Prop :=
  c ∈ C ∧ ∀ x ∈ C, radius A c ≤ radius A x

namespace Spec

def Regularity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : Set X), A.Nonempty → Bornology.IsBounded A →
    ConvexOn ℝ univ (radius A) ∧ LipschitzWith 1 (radius A) ∧ RadiusCoercive A

def UniqueCenter : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C A : Set X), C.Nonempty → IsClosed C → Convex ℝ C →
    A.Nonempty → Bornology.IsBounded A → A ⊆ C → ∃! c : X, IsCenter C A c

def MinimizingSequences : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C A : Set X), C.Nonempty → IsClosed C → Convex ℝ C →
    A.Nonempty → Bornology.IsBounded A → A ⊆ C →
    ∀ c : X, IsCenter C A c → ∀ x : ℕ → X,
    (∀ n, x n ∈ C) → Tendsto (fun n => radius A (x n)) atTop (nhds (radius A c)) →
    Tendsto x atTop (nhds c)

def StrictDiameter : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C A : Set X), C.Nonempty → IsClosed C → Convex ℝ C →
    A.Nonempty → Bornology.IsBounded A → A ⊆ C →
    ∀ c : X, IsCenter C A c → 0 < Metric.diam A → radius A c < Metric.diam A

end Spec
end
end ExpandedFA.BanachConvex.ChebyshevCenters
