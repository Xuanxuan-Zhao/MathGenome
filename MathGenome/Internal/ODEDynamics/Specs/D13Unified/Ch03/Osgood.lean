import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.IntegralFormulation

/-! Independent statements for paper.tex, Theorem d13:03:osgood. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D13Unified

/-- A modulus on the nonnegative half-line, with the improper reciprocal
integral diverging at zero. Values on negative arguments are irrelevant. -/
structure OsgoodModulus (ω : ℝ → ℝ) : Prop where
  continuous : ContinuousOn ω (Ici 0)
  monotone : MonotoneOn ω (Ici 0)
  zero : ω 0 = 0
  positive : ∀ r, 0 < r → 0 < ω r
  divergent : ∀ δ, 0 < δ →
    Tendsto (fun ε : ℝ => ∫ r in ε..δ, (ω r)⁻¹) (𝓝[>] 0) atTop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual closed local time-state box and its modulus estimate. -/
def OsgoodBox (F : ODE E) (c : ℝ) (z : E) (a b : ℝ) (ω : ℝ → ℝ) : Prop :=
  (Icc (c-a) (c+a) ×ˢ Metric.closedBall z b) ⊆ F.domain ∧
  ∀ t ∈ Icc (c-a) (c+a), ∀ u ∈ Metric.closedBall z b,
    ∀ v ∈ Metric.closedBall z b, ‖F.eval t u - F.eval t v‖ ≤ ω ‖u-v‖

def LocalOsgoodAt (F : ODE E) (c : ℝ) (z : E) : Prop :=
  ∃ a > 0, ∃ b > 0, ∃ ω : ℝ → ℝ, OsgoodModulus ω ∧ OsgoodBox F c z a b ω

end D13Unified

namespace Specs.D13Unified.Ch03.Osgood
open _root_.D13Unified
universe u

/-- Agreement throughout a common interval as long as both graphs stay in
the controlled compact box; the base time can be anywhere in that interval. -/
def boxUniquenessExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I : TimeInterval)
    (x y : ℝ → E) (c : ℝ) (z : E) (a b : ℝ) (ω : ℝ → ℝ),
    0 < a → 0 < b → OsgoodModulus ω → OsgoodBox F c z a b ω →
    _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I x → _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I y →
    I.carrier ⊆ Icc (c-a) (c+a) →
    (∀ t ∈ I.carrier, x t ∈ Metric.closedBall z b) →
    (∀ t ∈ I.carrier, y t ∈ Metric.closedBall z b) →
    ∀ s ∈ I.carrier, x s = y s → EqOn x y I.carrier

/-- A neighborhood on both sides of the common initial time, relative to
the actual common interval, including any included endpoints. -/
def localUniquenessExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I J : TimeInterval) (x y : ℝ → E),
    _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I x → _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F J y →
    ∀ s ∈ I.carrier ∩ J.carrier, x s = y s → LocalOsgoodAt F s (x s) →
    ∃ h > 0, EqOn x y ((I.carrier ∩ J.carrier) ∩ Ioo (s-h) (s+h))

/-- Local propagation on the entire common interval. Local modulus control
is required only at common graph points where the two curves agree. -/
def intervalUniquenessExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I J : TimeInterval) (x y : ℝ → E),
    _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I x → _root_.Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F J y →
    (∀ t ∈ I.carrier ∩ J.carrier, x t = y t → LocalOsgoodAt F t (x t)) →
    ∀ s ∈ I.carrier ∩ J.carrier, x s = y s → EqOn x y (I.carrier ∩ J.carrier)

end Specs.D13Unified.Ch03.Osgood
