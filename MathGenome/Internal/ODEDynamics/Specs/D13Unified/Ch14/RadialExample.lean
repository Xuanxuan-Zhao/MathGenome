import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Annulus
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.Multipliers
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalStability

/-! Independent statements for paper.tex, Example d13:14:radial-example.
The field, complete circle and partial flow are the shared polynomial oscillator.
The moving frame uses the Euclidean radial and tangential vectors at exp(it).
The return operator is the derivative of an actual local first-return map. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch14.RadialExample
open _root_.D13Unified _root_.D13Unified.Ch13.Annulus
open _root_.D13Unified.Ch06.StateDerivative
open Ch14.ReturnMap Ch14.Multipliers Ch14.OrbitalDefinitions

def PeriodExpected : Prop := Ch13.Annulus.PeriodicCircle

/-- Linearization of the actual radial equation, and its normalized solution. -/
def RadialVariationExpected : Prop :=
  (∀ r : ℝ, HasDerivAt (fun u : ℝ => u*(1-u^2)) (1-3*r^2) r) ∧
  (∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.exp (-2*u))
    (-2 * Real.exp (-2*t)) t) ∧ Real.exp (-2*(0:ℝ)) = 1 ∧
  Real.exp (-2*(2*Real.pi)) = Real.exp (-4*Real.pi) ∧
  0 < Real.exp (-4*Real.pi) ∧ Real.exp (-4*Real.pi) < 1

/-- The genuine state derivative in radial/tangential coordinates. At initial
point 1, re z is radial displacement and im z is angular displacement. Rotation
by exp(it) gives the corresponding actual moving vectors along the circle. -/
def CoordinateVariationExpected : Prop :=
  ∀ t : ℝ, ∀ z : ℂ,
    (fderiv ℝ (flow oscillator t) 1) z =
      circleCurve t * ((Real.exp (-2*t) * z.re : ℝ) + (z.im : ℂ)*Complex.I)

/-- Every actual first-return branch at 1 on the real-axis section has the
computed transverse derivative and the full monodromy characteristic polynomial.
The fixed tangential vector explicitly rules out strict contraction of all
full-monodromy multipliers. Existence of these data is also asserted. -/
def ReturnMultipliersExpected : Prop :=
  VariationConclusions oscillator 1 (2*Real.pi) ∧
  Nonempty (FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM) ∧
  ∀ d : FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM,
    (∀ v : Complex.imCLM.ker,
      (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0) v =
        Real.exp (-4*Real.pi) • v) ∧
    (orbitVariation oscillator 1 (2*Real.pi)).toLinearMap.charpoly =
      (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (Real.exp (-4*Real.pi))) ∧
    orbitVariation oscillator 1 (2*Real.pi) Complex.I = Complex.I ∧
    ¬ (∀ μ : ℂ,
      Polynomial.IsRoot
        ((orbitVariation oscillator 1 (2*Real.pi)).toLinearMap.charpoly.map
          (algebraMap ℝ ℂ)) μ →
        ‖μ‖ < 1)

/-- Attraction is a uniform exponential distance estimate for all sufficiently
nearby states, with genuine forward existence and orbital asymptotic stability. -/
def OrbitalAttractionExpected : Prop :=
  exponentiallyOrbitallyStableValue oscillator unitCircle ∧
    orbitalAsymptoticallyStableValue oscillator unitCircle

end Specs.D13Unified.Ch14.RadialExample
