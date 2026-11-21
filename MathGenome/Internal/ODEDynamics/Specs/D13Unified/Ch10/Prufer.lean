import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Separation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Independent statements for the Prüfer part of the oscillation proof in
paper.tex, Chapter 10, d13:10:oscillation. The only coefficient hypotheses are
those of `RegularProblem.Problem`: p is C¹ and positive, q,w are continuous,
and w is positive, on the fixed nondegenerate compact interval.

All ambient representatives are used only on [a,b]. The angle is constructed
by integrating angular velocity; it is not a principal argument with jumps,
and no oscillation or zero count is assumed. Parameter derivatives below are
ordinary derivatives in λ, while x derivatives are within the actual interval.
-/
noncomputable section
open Set MeasureTheory
namespace Specs.D13Unified.Ch10.Prufer
open RegularProblem Separation

/-- The real normalized initial-value problem, without a right boundary condition. -/
def Normalized (P : Problem) (lam : ℝ) (u : ℝ → ℝ) : Prop :=
  IsRealSolution P lam u ∧ u P.a = 0 ∧ flux P u P.a = 1

/-- A choice from the normalized IVP. Existence is a theorem, not an assumed
certificate; uniqueness is required only on [a,b]. -/
def solution (P : Problem) (lam : ℝ) : ℝ → ℝ :=
  Classical.epsilon (Normalized P lam)

def radius (P : Problem) (lam x : ℝ) : ℝ :=
  Real.sqrt (solution P lam x ^ 2 + flux P (solution P lam) x ^ 2)

def angularVelocity (P : Problem) (lam x : ℝ) : ℝ :=
  ((P.p x)⁻¹ * flux P (solution P lam) x ^ 2 +
    (lam * P.w x - P.q x) * solution P lam x ^ 2) / radius P lam x ^ 2

/-- The actual lifted argument, normalized to zero at a, defined without
presupposing the existence of any angle lift. -/
def angle (P : Problem) (lam x : ℝ) : ℝ :=
  ∫ t in P.a..x, angularVelocity P lam t

def variation (P : Problem) (lam x : ℝ) : ℝ :=
  deriv (fun mu => solution P mu x) lam

def fluxVariation (P : Problem) (lam x : ℝ) : ℝ :=
  deriv (fun mu => flux P (solution P mu) x) lam

/-- Existence and uniqueness for the normalized scalar family on all of [a,b]. -/
def NormalizedSolution : Prop := ∀ (P : Problem) (lam : ℝ),
  Normalized P lam (solution P lam) ∧
  ∀ u : ℝ → ℝ, Normalized P lam u → EqOn u (solution P lam) (intervalValue P)

/-- The explicit integral construction is a positive-radius, continuous lift. -/
def AngleLift : Prop := ∀ (P : Problem) (lam : ℝ),
  ContinuousOn (radius P lam) (intervalValue P) ∧
  ContinuousOn (angle P lam) (intervalValue P) ∧ angle P lam P.a = 0 ∧
  ∀ x ∈ intervalValue P,
    0 < radius P lam x ∧
    solution P lam x = radius P lam x * Real.sin (angle P lam x) ∧
    flux P (solution P lam) x = radius P lam x * Real.cos (angle P lam x)

/-- The spatial derivative, with one-sided derivatives at both endpoints. -/
def AngleDerivative : Prop := ∀ (P : Problem) (lam : ℝ),
  ∀ x ∈ intervalValue P,
    HasDerivWithinAt (angle P lam)
      ((P.p x)⁻¹ * Real.cos (angle P lam x) ^ 2 +
        (lam * P.w x - P.q x) * Real.sin (angle P lam x) ^ 2)
      (intervalValue P) x

/-- Upward crossings at every zero, including one-sided endpoint crossings. -/
def UpwardCrossings : Prop := ∀ (P : Problem) (lam : ℝ),
  ∀ x ∈ intervalValue P, solution P lam x = 0 →
    HasDerivWithinAt (angle P lam) (P.p x)⁻¹ (intervalValue P) x ∧
    0 < (P.p x)⁻¹

/-- Parameter differentiability on the same fixed interval and the actual
inhomogeneous variational system. In particular no time derivative of q or w
is an assumption. Flux variation equals p times the spatial derivative of v. -/
def ParameterVariation : Prop := ∀ (P : Problem) (lam : ℝ),
  ContinuousOn (variation P lam) (intervalValue P) ∧
  ContinuousOn (fluxVariation P lam) (intervalValue P) ∧
  variation P lam P.a = 0 ∧ fluxVariation P lam P.a = 0 ∧
  ∀ x ∈ intervalValue P,
    HasDerivAt (fun mu => solution P mu x) (variation P lam x) lam ∧
    HasDerivAt (fun mu => flux P (solution P mu) x) (fluxVariation P lam x) lam ∧
    HasDerivWithinAt (variation P lam) ((P.p x)⁻¹ * fluxVariation P lam x)
      (intervalValue P) x ∧
    HasDerivWithinAt (fluxVariation P lam)
      ((P.q x - lam * P.w x) * variation P lam x - P.w x * solution P lam x)
      (intervalValue P) x

/-- The parameter derivative of the lifted angle, on the whole common interval.
The numerator is the modified Wronskian and also the displayed oriented integral. -/
def AngleParameterDerivative : Prop := ∀ (P : Problem) (lam : ℝ),
  ∀ x ∈ intervalValue P,
    HasDerivAt (fun mu => angle P mu x)
      ((∫ t in P.a..x, P.w t * solution P lam t ^ 2) / radius P lam x ^ 2) lam ∧
    flux P (solution P lam) x * variation P lam x -
        solution P lam x * fluxVariation P lam x =
      ∫ t in P.a..x, P.w t * solution P lam t ^ 2

/-- Strict positivity at b; the parameter is arbitrary real, not an eigenvalue. -/
def TerminalStrictness : Prop := ∀ (P : Problem) (lam : ℝ),
  0 < (∫ t in P.a..P.b, P.w t * solution P lam t ^ 2) / radius P lam P.b ^ 2

/-- Flux of the spatial parameter variation, with actual within derivatives. -/
def FluxVariationIdentity : Prop := ∀ (P : Problem) (lam : ℝ),
  ∀ x ∈ intervalValue P, flux P (variation P lam) x = fluxVariation P lam x

/-- Parameter differentiability also of the positive radius. -/
def RadiusParameterDerivative : Prop := ∀ (P : Problem) (lam : ℝ),
  ∀ x ∈ intervalValue P,
    HasDerivAt (fun mu => radius P mu x)
      ((solution P lam x * variation P lam x +
        flux P (solution P lam) x * fluxVariation P lam x) / radius P lam x) lam

/-- The terminal formula and strict sign together, for every real λ. -/
def TerminalParameterDerivative : Prop := ∀ (P : Problem) (lam : ℝ),
  HasDerivAt (fun mu => angle P mu P.b)
    ((∫ t in P.a..P.b, P.w t * solution P lam t ^ 2) / radius P lam P.b ^ 2) lam ∧
  0 < (∫ t in P.a..P.b, P.w t * solution P lam t ^ 2) / radius P lam P.b ^ 2

end Specs.D13Unified.Ch10.Prufer
