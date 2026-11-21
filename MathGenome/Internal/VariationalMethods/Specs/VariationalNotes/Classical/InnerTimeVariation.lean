import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.DistributionalPrimitive

/-! Statements for paper.tex, Lemma `inner-time-variation` (3182–3207).
The ambient fields are used only on the closed reference interval. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical.InnerTime

/-- The energy in the sign convention of the manuscript: L - p · u'. -/
def energy {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (t : ℝ) : ℝ :=
  L.value (t, stateField I m u t, velocityField I m u t) -
    fderiv ℝ (fun v => L.value (t, stateField I m u t, v))
      (velocityField I m u t) (velocityField I m u t)

/-- The partial derivative in time, holding state and velocity fixed. -/
def timePartial {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (t : ℝ) : ℝ :=
  deriv (fun r => L.value (r, stateField I m u t, velocityField I m u t)) t

def timeMap (ζ : ℝ → ℝ) (s t : ℝ) : ℝ := t + s * ζ t

/-- This is a weak identity, not the definition of stationarity. -/
def WeakIdentity {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m) : Prop :=
  ∀ ζ : ℝ → ℝ, smoothInteriorTest I ζ →
    ∫ t in I.a..I.b, timePartial L u t * ζ t + energy L u t * deriv ζ t = 0

end VariationalNotes.Classical.InnerTime

namespace Specs.VariationalNotes.Classical.InnerTime
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.InnerTime

def energyPairing : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m) (t : I.Points),
    energy L u t = L.value (graphPoint u t) - inner ℝ (momentum L u t) (u.velocity t)

def fieldsContinuous : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 →
    ContinuousOn (energy L u) (Icc I.a I.b) ∧
    ContinuousOn (timePartial L u) (Icc I.a I.b)

def actionDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → ∀ ζ : ℝ → ℝ, smoothInteriorTest I ζ →
    HasDerivAt (innerTimeAction L u ζ)
      (∫ t in I.a..I.b, timePartial L u t * ζ t + energy L u t * deriv ζ t) 0

def integrandDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → ∀ ζ : ℝ → ℝ, ∀ t ∈ Icc I.a I.b,
    HasDerivAt (fun s : ℝ =>
      L.value (t + s * ζ t, stateField I m u t,
        (1 + s * deriv ζ t)⁻¹ • velocityField I m u t) * (1 + s * deriv ζ t))
      (timePartial L u t * ζ t + energy L u t * deriv ζ t) 0

def stationaryWeakIdentity : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → innerTimeStationary L u → WeakIdentity L u

/-- General closed-interval consequence of the scalar distributional theorem.
In particular the endpoints use within derivatives, not derivatives of an
arbitrary ambient extension. -/
def regularityFromWeakIdentity : Prop :=
  ∀ (a b : ℝ), a < b → ∀ p q : ℝ → ℝ,
    ContinuousOn p (Icc a b) → ContinuousOn q (Icc a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, p t * deriv φ t + q t * φ t = 0) →
    ContDiffOn ℝ 1 p (Icc a b) ∧
    (∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t) ∧
    (∀ t ∈ Ioo a b, HasDerivAt p (q t) t)

def energyRegularity : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → innerTimeStationary L u →
    ContDiffOn ℝ 1 (energy L u) (Icc I.a I.b) ∧
    (∀ t ∈ Icc I.a I.b,
      HasDerivWithinAt (energy L u) (timePartial L u t) (Icc I.a I.b) t) ∧
    (∀ t ∈ Ioo I.a I.b, HasDerivAt (energy L u) (timePartial L u t) t)

def energyRegularityOfWeakIdentity : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → WeakIdentity L u →
    ContDiffOn ℝ 1 (energy L u) (Icc I.a I.b) ∧
    (∀ t ∈ Icc I.a I.b,
      HasDerivWithinAt (energy L u) (timePartial L u t) (Icc I.a I.b) t) ∧
    (∀ t ∈ Ioo I.a I.b, HasDerivAt (energy L u) (timePartial L u t) t)

def timeMapsIncreasing : Prop :=
  ∀ (I : Interval) (ζ : ℝ → ℝ), smoothInteriorTest I ζ →
    ∃ ε > 0, ∀ s : ℝ, |s| < ε →
      (∀ t : ℝ, 0 < 1 + s * deriv ζ t) ∧ StrictMono (timeMap ζ s) ∧
      timeMap ζ s I.a = I.a ∧ timeMap ζ s I.b = I.b

/-- The time changes are smooth increasing diffeomorphisms on the real line,
fixing the endpoints and restricting to bijections of the reference interval. -/
def timeDiffeomorphisms : Prop :=
  ∀ (I : Interval) (ζ : ℝ → ℝ), smoothInteriorTest I ζ →
    ∃ ε > 0, ∀ s : ℝ, |s| < ε →
      (∀ t : ℝ, 0 < 1 + s * deriv ζ t) ∧
      timeMap ζ s I.a = I.a ∧ timeMap ζ s I.b = I.b ∧
      ∃ e : ℝ ≃o ℝ, (∀ t, e t = timeMap ζ s t) ∧
        ContDiff ℝ ∞ (e : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e.symm : ℝ → ℝ) ∧
        BijOn (timeMap ζ s) (Icc I.a I.b) (Icc I.a I.b)

/-- Physical curves, with the defining transport relation and change-of-variable
identity. Norm convergence is exactly C¹ convergence of the shared jet space. -/
def transportedCurves : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → ∀ ζ : ℝ → ℝ, smoothInteriorTest I ζ →
    ∃ v : ℝ → C1Curve I m, v 0 = u ∧ Tendsto v (𝓝 0) (𝓝 u) ∧
      ∃ ε > 0, ∀ s : ℝ, |s| < ε →
        graphAdmissible L (v s) ∧
        (v s).state I.left = u.state I.left ∧
        (v s).state I.right = u.state I.right ∧
        (∀ t ∈ Icc I.a I.b,
          stateField I m (v s) (timeMap ζ s t) = stateField I m u t) ∧
        action L (v s) = innerTimeAction L u ζ s

def minimaStationary : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (xₐ xᵦ : State m), regularNearGraph L u 1 →
    (weakLocalMinimum L xₐ xᵦ u ∨ strongLocalMinimum L xₐ xᵦ u) →
    innerTimeStationary L u

end Specs.VariationalNotes.Classical.InnerTime
