import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic

/-!
Independent types for K03.05.lhopital_zero, paper.tex:892–904.
An ambient real function represents its restriction to the open interval J.
`J ∈ 𝓝[>] a` (respectively `𝓝[<] a`) means J contains a right
(respectively left) approach segment at a. `J ∈ atTop` and `J ∈ atBot`
mean J contains the corresponding infinite tail. Thus bounded intervals,
half-lines and the whole line are all admitted; endpoint values of f and g
are arbitrary. The theorem is also valid if J extends past a finite endpoint.

The output filter l is arbitrary, a harmless strengthening that simultaneously
includes every finite output L (`l = 𝓝 L`), +∞ (`l = atTop`), and -∞
(`l = atBot`). These are limits of real-valued functions; the latter two
are infinite output limits, not real values. Both the eventually nonzero
assertion and the quotient limit concern exactly the selected input approach.
No nonvanishing of g or continuity of either derivative is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch05.LhopitalZero

open Set Filter
open scoped Topology

def lhopitalZeroRight : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (a : ℝ) (l : Filter ℝ),
    IsOpen J → OrdConnected J → J ∈ (𝓝[>] a : Filter ℝ) →
    DifferentiableOn ℝ f J → DifferentiableOn ℝ g J →
    (∀ x ∈ J, deriv g x ≠ 0) →
    Tendsto f (𝓝[>] a) (𝓝 0) → Tendsto g (𝓝[>] a) (𝓝 0) →
    Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) l →
    (∀ᶠ x in (𝓝[>] a), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (𝓝[>] a) l

def lhopitalZeroLeft : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (a : ℝ) (l : Filter ℝ),
    IsOpen J → OrdConnected J → J ∈ (𝓝[<] a : Filter ℝ) →
    DifferentiableOn ℝ f J → DifferentiableOn ℝ g J →
    (∀ x ∈ J, deriv g x ≠ 0) →
    Tendsto f (𝓝[<] a) (𝓝 0) → Tendsto g (𝓝[<] a) (𝓝 0) →
    Tendsto (fun x => deriv f x / deriv g x) (𝓝[<] a) l →
    (∀ᶠ x in (𝓝[<] a), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (𝓝[<] a) l

def lhopitalZeroAtTop : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (l : Filter ℝ),
    IsOpen J → OrdConnected J → J ∈ (atTop : Filter ℝ) →
    DifferentiableOn ℝ f J → DifferentiableOn ℝ g J →
    (∀ x ∈ J, deriv g x ≠ 0) →
    Tendsto f (atTop) (𝓝 0) → Tendsto g (atTop) (𝓝 0) →
    Tendsto (fun x => deriv f x / deriv g x) (atTop) l →
    (∀ᶠ x in (atTop), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (atTop) l

def lhopitalZeroAtBot : Prop :=
  ∀ (f g : ℝ → ℝ) (J : Set ℝ) (l : Filter ℝ),
    IsOpen J → OrdConnected J → J ∈ (atBot : Filter ℝ) →
    DifferentiableOn ℝ f J → DifferentiableOn ℝ g J →
    (∀ x ∈ J, deriv g x ≠ 0) →
    Tendsto f (atBot) (𝓝 0) → Tendsto g (atBot) (𝓝 0) →
    Tendsto (fun x => deriv f x / deriv g x) (atBot) l →
    (∀ᶠ x in (atBot), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (atBot) l

end Specs.SingleVariableAnalysis.Ch05.LhopitalZero
