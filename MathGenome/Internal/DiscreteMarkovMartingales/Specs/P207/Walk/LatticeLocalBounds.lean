import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeFourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Independent statements for the peaks and local estimates in
`paper.tex`, Lemma `p207:lem:lattice-fourier`.
The coordinates below are angular coordinates in the existing torus;
their domain carries the Euclidean L² norm, not the product supremum norm. -/

namespace P207.Walk

noncomputable section

/-- The second peak, as a point of the angular torus. -/
def piPoint (d : ℕ) : Torus d := fun _ => (Real.pi : AddCircle (2 * Real.pi))

/-- Translation of the angular quotient map, with Euclidean domain. -/
def angularLift {d : ℕ} (center : Torus d)
    (u : EuclideanSpace ℝ (Fin d)) : Torus d :=
  fun j => center j + (u j : AddCircle (2 * Real.pi))

namespace LatticeLocalBoundsSpec

def piPointType := (d : ℕ) → Torus d
def piPointValue : piPointType := fun d _ => (Real.pi : AddCircle (2 * Real.pi))

def angularLiftType := {d : ℕ} → Torus d → EuclideanSpace ℝ (Fin d) → Torus d
def angularLiftValue : angularLiftType := fun center u =>
  fun j => center j + (u j : AddCircle (2 * Real.pi))

def peaks : Prop := ∀ (d : ℕ) [NeZero d] (t : Torus d),
  |phi t| = 1 ↔ t = 0 ∨ t = piPoint d

/-- A genuine open chart parametrizes a neighborhood of each peak by
the actual quotient-and-translation map. A positive closed Euclidean ball
lies in its source, and the two estimates hold on that ball. -/
def local_quadratic : Prop := ∀ (d : ℕ) [NeZero d] (center : Torus d),
  (center = 0 ∨ center = piPoint d) →
  ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (Torus d))
      (a b η : ℝ),
    0 < a ∧ 0 < b ∧ 0 < η ∧
    (∀ u, e u = angularLift center u) ∧
    e 0 = center ∧
    Metric.closedBall 0 η ⊆ e.source ∧
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ η →
      a * ‖u‖ ^ 2 ≤ 1 - |phi (e u)| ∧
      1 - |phi (e u)| ≤ b * ‖u‖ ^ 2

end LatticeLocalBoundsSpec
end
end P207.Walk
