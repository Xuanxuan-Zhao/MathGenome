import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
Independent statements for paper.tex, d10:16:dini (lines 2496–2509).
The topology on X is arbitrary: compactness carries no separation or
nonemptiness condition. Pointwise monotonicity is non-strict. The two
epsilon statements spell out the common stage for every point of X.
-/

open Filter
open scoped Topology
universe u

namespace Specs.D10Topology.Ch16.Dini

def dini_increasing : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (f : X → ℝ),
    (∀ n, Continuous (F n)) → Continuous f →
    (∀ x, Monotone (fun n => F n x)) →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    TendstoUniformly F f atTop

def dini_decreasing : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (f : X → ℝ),
    (∀ n, Continuous (F n)) → Continuous f →
    (∀ x, Antitone (fun n => F n x)) →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    TendstoUniformly F f atTop

def dini_increasing_epsilon : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (f : X → ℝ),
    (∀ n, Continuous (F n)) → Continuous f →
    (∀ x, Monotone (fun n => F n x)) →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

def dini_decreasing_epsilon : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (f : X → ℝ),
    (∀ n, Continuous (F n)) → Continuous f →
    (∀ x, Antitone (fun n => F n x)) →
    (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

end Specs.D10Topology.Ch16.Dini
