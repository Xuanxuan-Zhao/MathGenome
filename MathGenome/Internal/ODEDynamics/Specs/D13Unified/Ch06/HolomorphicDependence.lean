import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HolomorphicLimits
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Independent specification of paper.tex, d13:06:analytic-dependence.

Complex time, state and parameter tuples are flattened only to reuse the
canonical absolutely convergent coordinate-power-series definition. All balls
below are actual open balls; their finite-pi norms give complex polydiscs.
No existence or uniqueness certificate is assumed by these definitions.
-/
namespace D13Unified.Ch06.HolomorphicDependence

open Filter Metric Set
open scoped Topology
open D13Unified.Ch06.HolomorphicLimits

abbrev State (n : ℕ) := Fin n → ℂ
abbrev FieldPoint (n m : ℕ) := Fin (n + m + 1) → ℂ
abbrev MovingPoint (n m : ℕ) := Fin (n + m + 2) → ℂ

/-- The original field's point `(z,w,λ)` in complex coordinates. -/
def fieldPoint {n m : ℕ} (z : ℂ) (w : State n) (p : State m) : FieldPoint n m :=
  Fin.cons z (Fin.append w p)

def stateCoordinates {n m : ℕ} (q : Fin (n + m) → ℂ) : State n :=
  fun i => q (Fin.castAdd m i)

def parameterCoordinates {n m : ℕ} (q : Fin (n + m) → ℂ) : State m :=
  fun i => q (Fin.natAdd n i)

/-- Product of terminal-time, initial-state and parameter neighborhoods. -/
def fixedProduct {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m)
    (a b c : ℝ) : Set (FieldPoint n m) :=
  {q | q 0 ∈ ball z₀ a ∧ stateCoordinates (Fin.tail q) ∈ ball w₀ b ∧
    parameterCoordinates (Fin.tail q) ∈ ball p₀ c}

/-- Product of terminal-time, initial-time, initial-state and parameter neighborhoods. -/
def movingProduct {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m)
    (a e b c : ℝ) : Set (MovingPoint n m) :=
  {q | q 0 ∈ ball z₀ a ∧ Fin.tail q 0 ∈ ball z₀ e ∧
    stateCoordinates (Fin.tail (Fin.tail q)) ∈ ball w₀ b ∧
    parameterCoordinates (Fin.tail (Fin.tail q)) ∈ ball p₀ c}

/-- Competitors can be defined on any open complex neighborhood of the
initial time. Equality is asserted only as a germ there. The derivative is
complex and forces holomorphy of the competitor on its neighborhood. -/
def UniqueSolutionGerm {n m : ℕ} (U : Set (FieldPoint n m))
    (f : FieldPoint n m → State n) (η : ℂ) (ξ : State n) (p : State m)
    (u : ℂ → State n) : Prop :=
  ∀ (V : Set ℂ) (v : ℂ → State n), IsOpen V → η ∈ V → v η = ξ →
    (∀ z ∈ V, fieldPoint z (v z) p ∈ U ∧
      HasDerivAt v (f (fieldPoint z (v z) p)) z) →
    v =ᶠ[𝓝 η] u

/-- Complete fixed-initial-time conclusion. -/
def FixedTimeConclusion {n m : ℕ} (U : Set (FieldPoint n m))
    (f : FieldPoint n m → State n) (z₀ : ℂ) (w₀ : State n) (p₀ : State m) : Prop :=
  ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    ∃ W : ℂ → State n → State m → State n,
      CoordinateHolomorphicOn (fixedProduct z₀ w₀ p₀ a b c)
        (fun q => W (q 0) (stateCoordinates (Fin.tail q))
          (parameterCoordinates (Fin.tail q))) ∧
      ∀ ξ ∈ ball w₀ b, ∀ p ∈ ball p₀ c,
        W z₀ ξ p = ξ ∧
        (∀ z ∈ ball z₀ a, fieldPoint z (W z ξ p) p ∈ U ∧
          HasDerivAt (fun t => W t ξ p) (f (fieldPoint z (W z ξ p) p)) z) ∧
        UniqueSolutionGerm U f z₀ ξ p (fun z => W z ξ p)

/-- Complete varying-initial-time conclusion. `e ≤ a` ensures that all
permitted initial times also belong to the common terminal-time disc. -/
def MovingTimeConclusion {n m : ℕ} (U : Set (FieldPoint n m))
    (f : FieldPoint n m → State n) (z₀ : ℂ) (w₀ : State n) (p₀ : State m) : Prop :=
  ∃ a e b c : ℝ, 0 < a ∧ 0 < e ∧ e ≤ a ∧ 0 < b ∧ 0 < c ∧
    ∃ W : ℂ → ℂ → State n → State m → State n,
      CoordinateHolomorphicOn (movingProduct z₀ w₀ p₀ a e b c)
        (fun q => W (q 0) (Fin.tail q 0) (stateCoordinates (Fin.tail (Fin.tail q)))
          (parameterCoordinates (Fin.tail (Fin.tail q)))) ∧
      ∀ η ∈ ball z₀ e, ∀ ξ ∈ ball w₀ b, ∀ p ∈ ball p₀ c,
        W η η ξ p = ξ ∧
        (∀ z ∈ ball z₀ a, fieldPoint z (W z η ξ p) p ∈ U ∧
          HasDerivAt (fun t => W t η ξ p) (f (fieldPoint z (W z η ξ p) p)) z) ∧
        UniqueSolutionGerm U f η ξ p (fun z => W z η ξ p)

end D13Unified.Ch06.HolomorphicDependence

namespace Specs.D13Unified.Ch06.HolomorphicDependence

open _root_.D13Unified.Ch06.HolomorphicLimits
open _root_.D13Unified.Ch06.HolomorphicDependence
open Filter
open scoped Topology

/-- Both parts of the source theorem, in all finite state and parameter dimensions. -/
def holomorphic_dependence_type : Prop :=
  ∀ (n m : ℕ) (U : Set (FieldPoint n m)) (f : FieldPoint n m → State n)
    (z₀ : ℂ) (w₀ : State n) (p₀ : State m),
    IsOpen U → fieldPoint z₀ w₀ p₀ ∈ U → CoordinateHolomorphicOn U f →
    FixedTimeConclusion U f z₀ w₀ p₀ ∧ MovingTimeConclusion U f z₀ w₀ p₀

/-- The source's uniqueness-of-germs component, independently stated for
any two complex differential solutions on arbitrary open neighborhoods. -/
def solution_germ_unique_type : Prop :=
  ∀ {n m : ℕ} {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n},
    IsOpen U → CoordinateHolomorphicOn U f →
    ∀ {V W : Set ℂ} {u v : ℂ → State n} {η : ℂ} {p : State m},
      IsOpen V → IsOpen W → η ∈ V → η ∈ W →
      (∀ z ∈ V, fieldPoint z (u z) p ∈ U ∧
        HasDerivAt u (f (fieldPoint z (u z) p)) z) →
      (∀ z ∈ W, fieldPoint z (v z) p ∈ U ∧
        HasDerivAt v (f (fieldPoint z (v z) p)) z) →
      u η = v η → u =ᶠ[𝓝 η] v

end Specs.D13Unified.Ch06.HolomorphicDependence
