import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.Separation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent specification of paper.tex, Proposition d13:02:energy. -/
noncomputable section
open Set

namespace D13Unified.MechanicalEnergy

/-- A C² scalar mechanical trajectory on its actual open time interval.
`V'` records the C¹ derivative of the potential on its interval, using within
 derivatives when a state endpoint is included. There is no assertion off `J`.
The equation is stated using the ordinary time derivatives of `y`. -/
structure Data where
  I : OpenTimeInterval
  J : TimeInterval
  V : ℝ → ℝ
  V' : ℝ → ℝ
  potential_c1 : ContDiffOn ℝ 1 V J.carrier
  continuous_force : ContinuousOn V' J.carrier
  potential_deriv : ∀ u ∈ J.carrier, HasDerivWithinAt V (V' u) J.carrier u
  y : ℝ → ℝ
  trajectory_c2 : ContDiffOn ℝ 2 y I.carrier
  graph : MapsTo y I.carrier J.carrier
  equation : ∀ t ∈ I.carrier, HasDerivAt (deriv y) (-V' (y t)) t

/-- Kinetic plus potential energy; no choice of a first integral is an input. -/
def energy (d : Data) (t : ℝ) : ℝ := (deriv d.y t)^2 / 2 + d.V (d.y t)

/-- One chosen nonturning branch, with either orientation. Positivity and sign
are required only along the trajectory, not on an externally imposed larger set. -/
structure Branch (d : Data) where
  K : OpenTimeInterval
  subset_time : K.carrier ⊆ d.I.carrier
  s : ℝ
  mem_s : s ∈ K.carrier
  σ : ℝ
  sign_choice : σ = 1 ∨ σ = -1
  positive : ∀ t ∈ K.carrier, 0 < energy d s - d.V (d.y t)
  velocity_sign : ∀ t ∈ K.carrier, 0 ≤ σ * deriv d.y t

end D13Unified.MechanicalEnergy

namespace Specs.D13Unified.Ch02.MechanicalEnergy
open _root_.D13Unified _root_.D13Unified.MechanicalEnergy

/-- Conservation is on the entire time interval, without a nonzero-velocity
hypothesis, and in particular includes turning points. -/
def conservationExpected : Prop := ∀ (d : Data) (s t : ℝ),
  s ∈ d.I.carrier → t ∈ d.I.carrier → energy d t = energy d s

/-- The signed square-root equation, the actual range as a nonvanishing state
interval, and recovery by the upstream inverse-integral construction. The
primitive identity is oriented and includes times on either side of `s`.
The constructed maximal first-order branch extends this mechanical branch;
no converse at a turning point is asserted. -/
def recoveryExpected : Prop := ∀ (d : Data) (b : Branch d),
  (∀ t ∈ b.K.carrier,
    deriv d.y t = b.σ * Real.sqrt (2 * (energy d b.s - d.V (d.y t)))) ∧
  ∃ q : Separation.Data,
    q.I = b.K ∧ q.J.carrier = d.y '' b.K.carrier ∧
    q.a = (fun _ => 1) ∧
    q.g = (fun u => b.σ * Real.sqrt (2 * (energy d b.s - d.V u))) ∧
    q.s = b.s ∧ q.ξ = d.y b.s ∧
    (∀ t ∈ b.K.carrier, Separation.primitive q (d.y t) = t - b.s) ∧
    b.K.carrier ⊆ Separation.branch q ∧
    EqOn (Separation.formula q) d.y b.K.carrier ∧
    ∃ x : Solution q.ode,
      x.interval.carrier = Separation.branch q ∧
      EqOn x.representative (Separation.formula q) x.interval.carrier ∧
      Ch01.SolutionConcepts.maximalValue x ∧
      b.K.carrier ⊆ x.interval.carrier ∧
      EqOn x.representative d.y b.K.carrier

end Specs.D13Unified.Ch02.MechanicalEnergy
