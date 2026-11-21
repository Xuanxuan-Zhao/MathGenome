import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.ChebyshevCenters
import Mathlib.Topology.Order.LiminfLimsup

/-! The asymptotic and tail stage of `fa2:p2:asymptotic-center`.
All limits of vectors use the norm topology, and all radii are real.
The later strong/weak limit identifications are allocated separately. -/
namespace ExpandedFA.BanachConvex.AsymptoticCenters
open Set Filter
universe u
noncomputable section

/-- The actual set of points in the n-th tail, including its first point. -/
def tailSet {X : Type u} (a : ℕ → X) (n : ℕ) : Set X := a '' Ici n

/-- Radius of a tail set, using the shared Chebyshev radius. -/
def tailRadius {X : Type u} [NormedAddCommGroup X] (a : ℕ → X) (n : ℕ) (x : X) : ℝ :=
  ChebyshevCenters.radius (tailSet a n) x

/-- The ordinary real limsup of the distances to the bounded sequence. -/
def radius {X : Type u} [NormedAddCommGroup X] (a : ℕ → X) (x : X) : ℝ :=
  limsup (fun n => ‖x - a n‖) atTop

def RadiusCoercive {X : Type u} [NormedAddCommGroup X] (a : ℕ → X) : Prop :=
  ∀ b : ℝ, ∃ R : ℝ, ∀ x : X, R ≤ ‖x‖ → b < radius a x

def IsCenter {X : Type u} [NormedAddCommGroup X] (C : Set X) (a : ℕ → X) (c : X) : Prop :=
  c ∈ C ∧ ∀ x ∈ C, radius a c ≤ radius a x

namespace Spec

def Regularity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : ℕ → X), Bornology.IsBounded (range a) →
    (∃ M : ℝ, ∀ x, 0 ≤ radius a x ∧ radius a x ≤ ‖x‖ + M) ∧
    ConvexOn ℝ univ (radius a) ∧ LipschitzWith 1 (radius a) ∧ RadiusCoercive a

def TailLimit : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] (a : ℕ → X),
    Bornology.IsBounded (range a) → ∀ x,
    Antitone (fun n => tailRadius a n x) ∧
    Tendsto (fun n => tailRadius a n x) atTop (nhds (radius a x))

def UniqueCenter : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X) (a : ℕ → X), C.Nonempty → IsClosed C → Convex ℝ C →
    Bornology.IsBounded (range a) → (∀ n, a n ∈ C) → ∃! c : X, IsCenter C a c

def MinimizingSequences : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X) (a : ℕ → X), C.Nonempty → IsClosed C → Convex ℝ C →
    Bornology.IsBounded (range a) → (∀ n, a n ∈ C) →
    ∀ c, IsCenter C a c → ∀ x : ℕ → X, (∀ n, x n ∈ C) →
    Tendsto (fun n => radius a (x n)) atTop (nhds (radius a c)) →
    Tendsto x atTop (nhds c)

def TailCenterExistence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X) (a : ℕ → X), C.Nonempty → IsClosed C → Convex ℝ C →
    Bornology.IsBounded (range a) → (∀ n, a n ∈ C) →
    ∃ cn : ℕ → X, ∀ n, ChebyshevCenters.IsCenter C (tailSet a n) (cn n)

def TailCenters : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X) (a : ℕ → X), C.Nonempty → IsClosed C → Convex ℝ C →
    Bornology.IsBounded (range a) → (∀ n, a n ∈ C) →
    ∀ c, IsCenter C a c → ∀ cn : ℕ → X,
    (∀ n, ChebyshevCenters.IsCenter C (tailSet a n) (cn n)) →
    Tendsto cn atTop (nhds c) ∧
    Tendsto (fun n => tailRadius a n (cn n)) atTop (nhds (radius a c)) ∧
    Tendsto (fun n => radius a (cn n)) atTop (nhds (radius a c))

end Spec
end
end ExpandedFA.BanachConvex.AsymptoticCenters
