import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FirstVariation
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.InnerTimeVariation

/-! Source: paper.tex 3209–3266. Time–state constraints are represented by
sets and their two-sided curve velocities. The chart version below explicitly
covers the range of the derivative of every local smooth parametrization. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical.Boundary

abbrev Configuration (I : Interval) (m : ℕ) := ℝ × ℝ × C1Curve I m

def referenceConfiguration {I : Interval} {m : ℕ} (u : C1Curve I m) :
    Configuration I m := (I.a, I.b, u)

def timeScale (I : Interval) (A B : ℝ) : ℝ := (B - A) / (I.b - I.a)

/-- The moving action, expressed on the fixed reference interval by increasing
 affine change of variable. State displacements in this representation are total. -/
def referenceAction {I : Interval} {m : ℕ} (L : Lagrangian m)
    (c : Configuration I m) : ℝ :=
  ∫ t in I.a..I.b, L.value
    (affineTime I c.1 c.2.1 t, stateField I m c.2.2 t,
      (timeScale I c.1 c.2.1)⁻¹ • velocityField I m c.2.2 t) * timeScale I c.1 c.2.1

/-- The ordinary physical action uses the within derivative on the physical
closed interval. The change-of-variable theorem is an obligation below. -/
def physicalAction {I : Interval} {m : ℕ} {u : C1Curve I m}
    (L : Lagrangian m) (v : MovingEndpointVariation u) (s : ℝ) : ℝ :=
  ∫ r in v.leftTime s..v.rightTime s,
    L.value (r, v.physicalCurve s r,
      derivWithin (v.physicalCurve s) (Icc (v.leftTime s) (v.rightTime s)) r)

def variationConfiguration {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (s : ℝ) : Configuration I m :=
  (v.leftTime s, v.rightTime s, v.rescaled s)

def referenceAdmissible {I : Interval} {m : ℕ} (L : Lagrangian m)
    (c : Configuration I m) : Prop :=
  c.1 < c.2.1 ∧ ∀ t : I.Points,
    (affineTime I c.1 c.2.1 t, c.2.2.state t,
      (timeScale I c.1 c.2.1)⁻¹ • c.2.2.velocity t) ∈ L.domain

def constrainedConfigurations {I : Interval} {m : ℕ} (L : Lagrangian m)
    (Sₐ Sᵦ : Set (ℝ × State m)) : Set (Configuration I m) :=
  {c | referenceAdmissible L c ∧
    (c.1, c.2.2.state I.left) ∈ Sₐ ∧ (c.2.1, c.2.2.state I.right) ∈ Sᵦ}

/-- The product topology is the C¹ topology after affine rescaling, with both
endpoint times variable. Endpoint constraints are independent. -/
def constrainedLocalMinimum {I : Interval} {m : ℕ} (L : Lagrangian m)
    (Sₐ Sᵦ : Set (ℝ × State m)) (u : C1Curve I m) : Prop :=
  referenceConfiguration u ∈ constrainedConfigurations L Sₐ Sᵦ ∧
    IsLocalMinOn (referenceAction L) (constrainedConfigurations L Sₐ Sᵦ)
      (referenceConfiguration u)

/-- Tangent vectors as velocities of two-sided differentiable feasible curves.
For smooth submanifolds these are precisely the usual tangent vectors. The
parametrization formulation below also states the annihilation directly. -/
def endpointTangent {m : ℕ} (S : Set (ℝ × State m)) (x v : ℝ × State m) : Prop :=
  ∃ γ : ℝ → ℝ × State m, γ 0 = x ∧ HasDerivAt γ v 0 ∧
    ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ S

def endpointCovector {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : I.Points) (v : ℝ × State m) : ℝ :=
  inner ℝ (momentum L u t) v.2 + InnerTime.energy L u t * v.1

def boundaryValue {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (v : MovingEndpointVariation u) : ℝ :=
  endpointCovector L u I.right ((endpointTimeDisplacements u v).2,
    (endpointDisplacements u v).2) -
  endpointCovector L u I.left ((endpointTimeDisplacements u v).1,
    (endpointDisplacements u v).1)

/-- The affine infinitesimal time displacement of a moving family. -/
def variationTimeField {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (t : ℝ) : ℝ :=
  affineTime I (deriv v.leftTime 0) (deriv v.rightTime 0) t

def variationTimeSlope {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) : ℝ :=
  timeScale I (deriv v.leftTime 0) (deriv v.rightTime 0)

/-- Bulk derivative before integration by parts. -/
def movingVariationIntegral {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (v : MovingEndpointVariation u) : ℝ :=
  ∫ t in I.a..I.b,
    InnerTime.timePartial L u t * variationTimeField v t +
    variationDensity (momentumField L u) (stateGradientField L u)
      (stateField I m (deriv v.rescaled 0)) (velocityField I m (deriv v.rescaled 0)) t +
    InnerTime.energy L u t * variationTimeSlope v

/-- Pointwise Euler–Lagrange equation on the interior; no C² assumption. -/
def momentumEquation {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) : Prop :=
  ∀ t ∈ Ioo I.a I.b, HasDerivAt (momentumField L u) (stateGradientField L u t) t

end VariationalNotes.Classical.Boundary

namespace Specs.VariationalNotes.Classical.Boundary
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.Boundary

/-- Integration by parts uses only C¹ states and the inner time identity. -/
def boundaryIntegral : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → momentumEquation L u → innerTimeStationary L u →
    ∀ (w : C1Curve I m) (h dh : ℝ → ℝ),
      ContinuousOn h (Icc I.a I.b) → ContinuousOn dh (Icc I.a I.b) →
      (∀ t ∈ Ioo I.a I.b, HasDerivAt h (dh t) t) →
      (∫ t in I.a..I.b,
        InnerTime.timePartial L u t * h t +
        variationDensity (momentumField L u) (stateGradientField L u)
          (stateField I m w) (velocityField I m w) t +
        InnerTime.energy L u t * dh t) =
      endpointCovector L u I.right (h I.b, w.state I.right) -
        endpointCovector L u I.left (h I.a, w.state I.left)

/-- Endpoint lifting, stated without any action-derivative hypothesis. The
transformed graphs remain admissible by openness and compactness. This is the
explicit affine interpolation construction from paper.tex 3244–3256. -/
def endpointLiftConstruction : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    graphAdmissible L u →
    ∀ (α β : ℝ → ℝ × State m) (da db : ℝ × State m),
      α 0 = (I.a, u.state I.left) → β 0 = (I.b, u.state I.right) →
      HasDerivAt α da 0 → HasDerivAt β db 0 →
      ∃ v : MovingEndpointVariation u,
        (∀ s, v.leftTime s = (α s).1 ∧ v.rightTime s = (β s).1 ∧
          (v.rescaled s).state I.left = (α s).2 ∧
          (v.rescaled s).state I.right = (β s).2) ∧
        endpointTimeDisplacements u v = (da.1, db.1) ∧
        endpointDisplacements u v = (da.2, db.2) ∧
        ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t : I.Points,
          (affineTime I (v.leftTime s) (v.rightTime s) t, (v.rescaled s).state t,
            ((v.rightTime s - v.leftTime s) / (I.b - I.a))⁻¹ •
              (v.rescaled s).velocity t) ∈ L.domain

/-- Pullback really equals the physical action near zero. -/
def movingActionChangeOfVariables : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → ∀ v : MovingEndpointVariation u,
      physicalAction L v =ᶠ[𝓝 (0 : ℝ)] fun s => referenceAction L (variationConfiguration v s)

/-- Differentiation on the fixed reference interval, requiring differentiability
only at zero of the times and the rescaled C¹ family. -/
def movingActionDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → ∀ v : MovingEndpointVariation u,
      HasDerivAt (fun s => referenceAction L (variationConfiguration v s))
        (movingVariationIntegral L u v) 0

def movingIntegralBoundaryValue : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → momentumEquation L u → innerTimeStationary L u →
    ∀ v : MovingEndpointVariation u, movingVariationIntegral L u v = boundaryValue L u v

/-- Full first variation for arbitrary moving families differentiable at zero
in C¹, not merely affine families or families smooth in the variation parameter. -/
def movingBoundaryDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 → momentumEquation L u → innerTimeStationary L u →
    ∀ v : MovingEndpointVariation u,
      HasDerivAt (fun s => referenceAction L (variationConfiguration v s))
          (boundaryValue L u v) 0 ∧
      HasDerivAt (physicalAction L v) (boundaryValue L u v) 0

/-- General constraint sets give a stronger two-sided curve-velocity result.
For a smooth submanifold, its tangent space is the space of these velocities. -/
def transversality : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (Sₐ Sᵦ : Set (ℝ × State m)),
    regularNearGraph L u 1 → constrainedLocalMinimum L Sₐ Sᵦ u →
    (∀ v, endpointTangent Sₐ (I.a, u.state I.left) v →
      endpointCovector L u I.left v = 0) ∧
    (∀ v, endpointTangent Sᵦ (I.b, u.state I.right) v →
      endpointCovector L u I.right v = 0)

/-- Explicit local parametrization interpretation of the submanifold tangent
statement. No global chart or global parametrization is required. -/
def chartTransversality : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (Sₐ Sᵦ : Set (ℝ × State m)),
    regularNearGraph L u 1 → constrainedLocalMinimum L Sₐ Sᵦ u →
    ∀ (d : ℕ) (e : State d → ℝ × State m) (x : State d)
      (D : State d →L[ℝ] ℝ × State m),
      HasFDerivAt e D x →
      ((e x = (I.a, u.state I.left) ∧ ∀ᶠ y in 𝓝 x, e y ∈ Sₐ) →
        ∀ v, endpointCovector L u I.left (D v) = 0) ∧
      ((e x = (I.b, u.state I.right) ∧ ∀ᶠ y in 𝓝 x, e y ∈ Sᵦ) →
        ∀ v, endpointCovector L u I.right (D v) = 0)

/-- Algebraic specializations retain the actual L - p · u′ energy convention. -/
def covectorSpecialCases : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m) (t : I.Points),
    ((∀ z : State m, endpointCovector L u t (0, z) = 0) ↔ momentum L u t = 0) ∧
    ((∀ r : ℝ, endpointCovector L u t (r, 0) = 0) ↔
      L.value (graphPoint u t) - inner ℝ (momentum L u t) (u.velocity t) = 0) ∧
    (∀ T : Set (State m),
      (∀ z ∈ T, endpointCovector L u t (0, z) = 0) ↔
        ∀ z ∈ T, inner ℝ (momentum L u t) z = 0)

def fixedTimeFreeState : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (S : Set (ℝ × State m)), regularNearGraph L u 1 →
    (constrainedLocalMinimum L ({I.a} ×ˢ (univ : Set (State m))) S u →
      momentum L u I.left = 0) ∧
    (constrainedLocalMinimum L S ({I.b} ×ˢ (univ : Set (State m))) u →
      momentum L u I.right = 0)

def freeTerminalTimeFixedState : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (S : Set (ℝ × State m)) (z : State m), regularNearGraph L u 1 →
    constrainedLocalMinimum L S ((univ : Set ℝ) ×ˢ {z}) u →
    L.value (graphPoint u I.right) -
      inner ℝ (momentum L u I.right) (u.velocity I.right) = 0

/-- Fixed time with an arbitrary state constraint: annihilation on all two-sided
state tangents, in particular the tangent space of a smooth state submanifold. -/
def fixedTimeConstrainedState : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (S : Set (ℝ × State m)) (N : Set (State m)), regularNearGraph L u 1 →
    constrainedLocalMinimum L S ({I.b} ×ˢ N) u →
    ∀ (γ : ℝ → State m) (v : State m), γ 0 = u.state I.right →
      HasDerivAt γ v 0 → (∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ N) →
      inner ℝ (momentum L u I.right) v = 0

end Specs.VariationalNotes.Classical.Boundary
