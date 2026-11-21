import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Independent statements for `chapters/04.tex`, `d04:04:contraction`.
`S` carries the induced Euclidean metric. `T^[j] x₀` is the orbit starting
at `x₀`: its zeroth term is `x₀` and its successor is obtained by applying `T`.
All error norms below are taken in the shared Euclidean ambient space.
There is no positive-dimension or positive-contraction-constant hypothesis.
-/

open Set Filter Topology
namespace Specs.D04.C04.Contraction
open Specs.D04.C01.EuclideanInterfaces.Model

def contraction_principleType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)), IsComplete S → S.Nonempty →
    ∀ (T : S → S) (q : ℝ), 0 ≤ q → q < 1 →
      (∀ x y : S, ‖(T x : E n) - (T y : E n)‖ ≤
        q * ‖(x : E n) - (y : E n)‖) →
      ∃ xStar : S,
        T xStar = xStar ∧
        (∀ y : S, T y = y → y = xStar) ∧
        (∀ x₀ : S,
          Tendsto (fun j : ℕ => (T^[j] x₀ : E n)) atTop (𝓝 (xStar : E n)) ∧
          ∀ j : ℕ, ‖(T^[j] x₀ : E n) - (xStar : E n)‖ ≤
            q ^ j / (1 - q) * ‖(T x₀ : E n) - (x₀ : E n)‖) ∧
        (∀ x : S, ‖(x : E n) - (xStar : E n)‖ ≤
          ‖(x : E n) - (T x : E n)‖ / (1 - q))

def closed_set_completeType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)), Closed S → IsComplete S

def closed_ball_completeType : Prop :=
  ∀ {n : ℕ} (a : E n) (r : ℝ), IsComplete {x : E n | ‖x - a‖ ≤ r}

end Specs.D04.C04.Contraction
