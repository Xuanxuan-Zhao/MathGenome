import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Analytic interface for the continuous-graph proof of paper.tex 4972–4987.
All measures are ordinary Lebesgue volume. Product coordinates carry their
ordinary product topology; the intermediate Euclidean plane has its L² norm.
No smoothness of the graph height or Stokes premise is part of this interface.
-/
noncomputable section
open Set MeasureTheory
namespace P202Specs.ContinuousGraphFlux
open P202Specs.PlanarRegionTopology

/-- Positively oriented orthonormal coordinates when `‖e‖ = 1`. -/
def frame (p e : Plane) (q : ℝ × ℝ) : Plane :=
  p + q.1 • e + q.2 • quarterTurn e

def strictEpigraph (p e : Plane) (g : ℝ → ℝ) : Set Plane :=
  frame p e '' {q : ℝ × ℝ | g q.1 < q.2}

def closedEpigraph (p e : Plane) (g : ℝ → ℝ) : Set Plane :=
  frame p e '' {q : ℝ × ℝ | g q.1 ≤ q.2}

def graph (p e : Plane) (g : ℝ → ℝ) : Set Plane :=
  range (fun x => frame p e (x, g x))

def projection (c : RegularJordanCurve) (p e : Plane) (t : ℝ) : ℝ :=
  inner ℝ e (realLift c.parametrization t - p)

/-- Only the join points are masked, not neighborhoods of the joins. -/
def removeJoins (c : RegularJordanCurve) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  if (t : ParameterCircle) ∈ c.joins then 0 else h t

namespace Expected

/-- The explicitly prescribed linear rotation is an L² isometry, and the
actual product-coordinate affine map preserves the existing Lebesgue volume. -/
def frameTransport : Prop := ∀ (p e : Plane), ‖e‖ = 1 →
  (∃ L : Plane ≃ₗᵢ[ℝ] Plane, ∀ v, L v = v 0 • e + v 1 • quarterTurn e) ∧
  (∃ H : (ℝ × ℝ) ≃ₜ Plane, (H : (ℝ × ℝ) → Plane) = frame p e) ∧
  MeasurePreserving (frame p e) volume volume

/-- Exact transport of the vertical derivative, including the scale. -/
def frameDerivative : Prop := ∀ (p e : Plane) (f : Plane → ℝ),
  ContDiff ℝ 1 f → ∀ q : ℝ × ℝ,
    fderiv ℝ (f ∘ frame p e) q (0, 1) =
      fderiv ℝ f (frame p e q) (quarterTurn e)

def graphNull : Prop := ∀ (p e : Plane), ‖e‖ = 1 →
  ∀ (g : ℝ → ℝ), Continuous g →
    volume (graph p e g) = 0 ∧
    strictEpigraph p e g =ᵐ[volume] closedEpigraph p e g

/-- The inward vertical direction gives the negative graph trace. Both
integrability statements and both strict/closed epigraph identities are included. -/
def verticalFlux : Prop := ∀ (p e : Plane), ‖e‖ = 1 →
  ∀ (g : ℝ → ℝ), Continuous g → ∀ (f : Plane → ℝ),
  ContDiff ℝ 1 f → HasCompactSupport f →
    Integrable (fun z => fderiv ℝ f z (quarterTurn e)) ∧
    Integrable (fun x => f (frame p e (x, g x))) ∧
    IntegrableOn (fun z => fderiv ℝ f z (quarterTurn e)) (strictEpigraph p e g) ∧
    IntegrableOn (fun z => fderiv ℝ f z (quarterTurn e)) (closedEpigraph p e g) ∧
    (∫ z in strictEpigraph p e g, fderiv ℝ f z (quarterTurn e)) =
      -(∫ x : ℝ, f (frame p e (x, g x))) ∧
    (∫ z in closedEpigraph p e g, fderiv ℝ f z (quarterTurn e)) =
      -(∫ x : ℝ, f (frame p e (x, g x)))

/-- Directed substitution on the original real lift, in either direction,
including intervals crossing the period seam. Continuity of `f` suffices here. -/
def parameterSubstitution : Prop := ∀ (c : RegularJordanCurve) (p e : Plane),
  ‖e‖ = 1 → ∀ (g : ℝ → ℝ), Continuous g →
  ∀ (f : Plane → ℝ), Continuous f → ∀ (a b : ℝ), |b - a| < 1 →
  (StrictMonoOn (projection c p e) (uIcc a b) ∨
    StrictAntiOn (projection c p e) (uIcc a b)) →
  (∀ t ∈ uIcc a b, realLift c.parametrization t =
    frame p e (projection c p e t, g (projection c p e t))) →
  IntervalIntegrable (fun t => f (realLift c.parametrization t) *
    inner ℝ e (deriv (realLift c.parametrization) t)) volume a b ∧
  IntervalIntegrable (fun x => f (frame p e (x, g x))) volume
    (projection c p e a) (projection c p e b) ∧
  (∫ t in a..b, f (realLift c.parametrization t) *
    inner ℝ e (deriv (realLift c.parametrization) t)) =
    ∫ x in projection c p e a..projection c p e b, f (frame p e (x, g x))

/-- Finite join removal holds for arbitrary scalar integrands. -/
def finiteJoinRemoval : Prop := ∀ (c : RegularJordanCurve) (a b : ℝ),
  |b - a| < 1 →
  {t ∈ uIcc a b | (t : ParameterCircle) ∈ c.joins}.Finite ∧
  ∀ h : ℝ → ℝ,
    (IntervalIntegrable (removeJoins c h) volume a b ↔
      IntervalIntegrable h volume a b) ∧
    (∫ t in a..b, removeJoins c h t) = ∫ t in a..b, h t

end Expected
end P202Specs.ContinuousGraphFlux
