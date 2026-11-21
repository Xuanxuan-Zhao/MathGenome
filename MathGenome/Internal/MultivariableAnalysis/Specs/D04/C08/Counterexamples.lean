import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.MeasureBridge
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements of the three examples and the measure applicability
remark in Chapter 8. `closedIntegral` is the shared Darboux lower integral on
an unoriented closed interval. All its uses below have ordered endpoints.
Riemann integrability and comparison with the measure integral are separate
obligations; a default value of a measure integral is never an integrability
certificate. Improper Riemann values are limits of these proper integrals. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace Specs.D04.C08.Counterexamples.Model
open Specs.D04.C06.DarbouxIntegral.Model

def interval (a b : ℝ) : Box 1 := intervalBox (min a b) (max a b) (min_le_max)
def RiemannOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Integrable (fun x : E 1 => f (x 0)) (interval a b)
def closedIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  lowerIntegral (fun x : E 1 => f (x 0)) (interval a b)

def spike (x t : ℝ) : ℝ := if 0 < x ∧ x < t then t⁻¹ else 0
/-- The normalization is 30, since the unnormalized polynomial has integral 1/30. -/
def psi (u : ℝ) : ℝ := if u ∈ Icc 1 2 then 30 * (u - 1)^2 * (2 - u)^2 else 0
def escape (x t : ℝ) : ℝ := t * psi (t * x)
def cauchy (x p : ℝ) : ℝ := (1 + (x - p)^2)⁻¹

def halflineMass (t : ℝ) : ℝ := ∫ x in Ioi 0, escape x t
/-- Absolute exterior mass; the integrands in these examples are nonnegative. -/
def exteriorMass (R p : ℝ) : ℝ := ∫ x in (Icc (-R) R)ᶜ, cauchy x p
end Specs.D04.C08.Counterexamples.Model

namespace Specs.D04.C08.Counterexamples
open Model

abbrev intervalType := ℝ → ℝ → Specs.D04.C06.DarbouxIntegral.Model.Box 1
def intervalValue : intervalType := Model.interval
abbrev RiemannOnType := (ℝ → ℝ) → ℝ → ℝ → Prop
def RiemannOnValue : RiemannOnType := Model.RiemannOn
abbrev closedIntegralType := (ℝ → ℝ) → ℝ → ℝ → ℝ
def closedIntegralValue : closedIntegralType := Model.closedIntegral
abbrev spikeType := ℝ → ℝ → ℝ
def spikeValue : spikeType := Model.spike
abbrev psiType := ℝ → ℝ
def psiValue : psiType := Model.psi
abbrev escapeType := ℝ → ℝ → ℝ
def escapeValue : escapeType := Model.escape
abbrev cauchyType := ℝ → ℝ → ℝ
def cauchyValue : cauchyType := Model.cauchy
abbrev halflineMassType := ℝ → ℝ
def halflineMassValue : halflineMassType := Model.halflineMass
abbrev exteriorMassType := ℝ → ℝ → ℝ
def exteriorMassValue : exteriorMassType := Model.exteriorMass

def closedIntegral_bridgeType : Prop := ∀ (f : ℝ → ℝ) a b, a ≤ b → RiemannOn f a b →
  MeasureTheory.IntegrableOn f (Icc a b) ∧ closedIntegral f a b = ∫ x in a..b, f x

def spike_integrableType : Prop := ∀ t ∈ Icc (0 : ℝ) 1, RiemannOn (fun x => spike x t) 0 1
def spike_massType : Prop := ∀ t ∈ Ioo (0 : ℝ) 1, closedIntegral (fun x => spike x t) 0 1 = 1
def spike_pointwiseType : Prop := ∀ x : ℝ,
  Tendsto (spike x) (𝓝[>] 0) (𝓝 0)
def spike_zeroType : Prop := (∀ x, spike x 0 = 0) ∧ closedIntegral (fun x => spike x 0) 0 1 = 0

def psi_propertiesType : Prop := ContDiff ℝ 1 psi ∧ (∀ u, 0 ≤ psi u) ∧
  Function.support psi ⊆ Icc 1 2 ∧ MeasureTheory.Integrable psi ∧ (∫ u, psi u) = 1

def escape_regularType : Prop := (∀ t, Continuous (fun x => escape x t)) ∧
  (∀ t a b, RiemannOn (fun x => escape x t) a b)
/-- This stronger local assertion implies uniform convergence on each bounded interval. -/
def escape_local_zeroType : Prop := ∀ A ≥ (0 : ℝ), ∃ δ > (0 : ℝ),
  ∀ t ∈ Ioo (0 : ℝ) δ, ∀ x ∈ Icc (0 : ℝ) A, escape x t = 0

def escape_uniformType : Prop := ∀ A ≥ (0 : ℝ),
  TendstoUniformlyOn (fun t x => escape x t) (fun _ => 0) (𝓝[>] 0) (Icc (0 : ℝ) A)
def escape_derivType : Prop := ∀ x ≥ (0 : ℝ),
  HasDerivWithinAt (escape x) 0 (Ici 0) 0

def escape_massType : Prop := ∀ t > (0 : ℝ),
  MeasureTheory.IntegrableOn (fun x => escape x t) (Ioi 0) ∧ halflineMass t = 1

def escape_improperType : Prop := ∀ t > (0 : ℝ),
  Tendsto (fun n : ℕ => closedIntegral (fun x => escape x t) 0 n) atTop (𝓝 1)
def escape_zero_massType : Prop := (∀ x, escape x 0 = 0) ∧ halflineMass 0 = 0 ∧
  (∀ n : ℕ, closedIntegral (fun x => escape x 0) 0 n = 0)
def escape_discontinuousType : Prop := ¬ ContinuousWithinAt halflineMass (Ici 0) 0
/-- No neighborhood of zero has uniform absolute exterior tails. -/
def escape_no_uniform_tailsType : Prop := ∀ δ > (0 : ℝ), ∀ R ≥ (0 : ℝ),
  ∃ t ∈ Ioo (0 : ℝ) δ, (∫ x in Ioi R, escape x t) = 1

/-- Failure of the actual finite-truncation uniform Cauchy criterion. -/
def escape_no_uniform_riemann_tailsType : Prop := ∀ δ > (0 : ℝ),
  ¬ (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, ∀ t ∈ Icc (0 : ℝ) δ,
    |closedIntegral (fun x => escape x t) 0 m - closedIntegral (fun x => escape x t) 0 n| < ε)

def cauchy_regularType : Prop := ∀ p : ℝ,
  Continuous (fun x => cauchy x p) ∧ (∀ x, 0 < cauchy x p) ∧
  ∀ a b, RiemannOn (fun x => cauchy x p) a b

def cauchy_massType : Prop := ∀ p : ℝ,
  MeasureTheory.Integrable (fun x => cauchy x p) ∧ (∫ x, cauchy x p) = Real.pi

def cauchy_improperType : Prop := ∀ p : ℝ,
  Tendsto (fun n : ℕ => closedIntegral (fun x => cauchy x p) (-(n : ℝ)) n)
    atTop (𝓝 Real.pi)

def cauchy_compact_boundType : Prop := ∀ K : Set ℝ, IsCompact K →
  ∃ C > (0 : ℝ), ∀ p ∈ K, ∀ x : ℝ, cauchy x p ≤ C / (1 + x^2)
def cauchy_compact_tailsType : Prop := ∀ K : Set ℝ, IsCompact K →
  ∀ ε > (0 : ℝ), ∃ N ≥ (0 : ℝ), ∀ R ≥ N, ∀ p ∈ K, exteriorMass R p < ε
/-- Compact parameter sets also satisfy the finite proper Riemann tail test. -/
def cauchy_compact_riemann_tailsType : Prop := ∀ K : Set ℝ, IsCompact K →
  ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, ∀ p ∈ K,
    |closedIntegral (fun x => cauchy x p) (-(m : ℝ)) m -
      closedIntegral (fun x => cauchy x p) (-(n : ℝ)) n| < ε

/-- The center can also be required to exceed any prescribed lower bound. -/
def cauchy_escape_massType : Prop := ∀ R ≥ (0 : ℝ), ∀ ε > (0 : ℝ), ∀ A : ℝ,
  ∃ p > A, Real.pi - ε < exteriorMass R p

def cauchy_no_uniform_tailsType : Prop := ¬ (∀ ε > (0 : ℝ), ∃ N ≥ (0 : ℝ),
  ∀ R ≥ N, ∀ p : ℝ, exteriorMass R p < ε)

/-- The symmetric proper Riemann integrals fail the uniform Cauchy criterion
when every real center is allowed. -/
def cauchy_no_uniform_riemann_tailsType : Prop :=
  ¬ (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, ∀ p : ℝ,
    |closedIntegral (fun x => cauchy x p) (-(m : ℝ)) m -
      closedIntegral (fun x => cauchy x p) (-(n : ℝ)) n| < ε)

/-- F4 is used for measure integrals with its actual measurability and domination
hypotheses. No Riemann assertion about the limit is a conclusion. -/
def dominated_convergenceType : Prop := ∀ (F : ℕ → ℝ → ℝ) (f M : ℝ → ℝ),
  (∀ n, AEStronglyMeasurable (F n)) → MeasureTheory.Integrable M →
  (∀ n, ∀ᵐ x, ‖F n x‖ ≤ M x) →
  (∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
  Tendsto (fun n => ∫ x, F n x) atTop (𝓝 (∫ x, f x))

/-- Riemann comparison requires the bridge's preexisting integrability
hypothesis. This is independent of any pointwise-limit assumption. -/
def riemann_applicabilityType : Prop := Specs.D04.C06.MeasureBridge.box_bridgeType ∧
  Specs.D04.C06.MeasureBridge.region_bridgeType ∧ Specs.D04.C06.MeasureBridge.improper_bridgeType
end Specs.D04.C08.Counterexamples
