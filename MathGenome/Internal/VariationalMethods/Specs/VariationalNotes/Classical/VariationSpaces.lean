import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Submodule

/-!
Shared conventions for paper.tex, chapter 7, §§1, 2 and 7.
A C¹ curve is a continuous state/velocity jet, with the velocity certified
as the derivative within the closed interval (one-sided at its endpoints).
The inherited product sup norm is max(‖u‖∞, ‖u′‖∞).
All functions used in integrals are extended by zero outside their intervals;
the extension has no effect on interval integrals or within derivatives.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical

structure Interval where
  a : ℝ
  b : ℝ
  increasing : a < b

abbrev State (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Interval.Points (I : Interval) := Set.Icc I.a I.b

variable (I : Interval) (m : ℕ)

def Interval.left : I.Points := ⟨I.a, le_rfl, I.increasing.le⟩
def Interval.right : I.Points := ⟨I.b, I.increasing.le, le_rfl⟩

/-- An arbitrary extension is used only under a within derivative or integral. -/
def extendState (u : C(I.Points, State m)) (t : ℝ) : State m :=
  if ht : t ∈ Set.Icc I.a I.b then u ⟨t, ht⟩ else 0

@[simp] theorem extendState_zero : extendState I m 0 = 0 := by
  funext t
  by_cases ht : t ∈ Set.Icc I.a I.b <;> simp [extendState, ht]

@[simp] theorem extendState_add (f g : C(I.Points, State m)) :
    extendState I m (f + g) = extendState I m f + extendState I m g := by
  funext t
  by_cases ht : t ∈ Set.Icc I.a I.b <;> simp [extendState, ht]

@[simp] theorem extendState_smul (c : ℝ) (f : C(I.Points, State m)) :
    extendState I m (c • f) = c • extendState I m f := by
  funext t
  by_cases ht : t ∈ Set.Icc I.a I.b <;> simp [extendState, ht]

/-- The compatibility submodule makes the C¹ space a normed real vector space. -/
def curveJets : Submodule ℝ (C(I.Points, State m) × C(I.Points, State m)) where
  carrier := {j | ∀ t : I.Points,
    HasDerivWithinAt (extendState I m j.1) (j.2 t) (Set.Icc I.a I.b) t}
  zero_mem' := by
    intro t
    change HasDerivWithinAt (extendState I m 0) 0 (Set.Icc I.a I.b) t
    rw [extendState_zero]
    exact hasDerivWithinAt_const _ _ _
  add_mem' := by
    intro f g hf hg t
    change HasDerivWithinAt (extendState I m (f.1 + g.1))
      (f.2 t + g.2 t) (Set.Icc I.a I.b) t
    rw [extendState_add]
    exact HasDerivWithinAt.add (hf t) (hg t)
  smul_mem' := by
    intro c f hf t
    change HasDerivWithinAt (extendState I m (c • f.1))
      (c • f.2 t) (Set.Icc I.a I.b) t
    rw [extendState_smul]
    exact (hf t).const_smul c

abbrev C1Curve := ↥(curveJets I m)

variable {I m}

def C1Curve.state (u : C1Curve I m) : C(I.Points, State m) := u.val.1
def C1Curve.velocity (u : C1Curve I m) : C(I.Points, State m) := u.val.2

def stateField (I : Interval) (m : ℕ) (u : C1Curve I m) : ℝ → State m := extendState I m u.state
def velocityField (I : Interval) (m : ℕ) (u : C1Curve I m) : ℝ → State m := extendState I m u.velocity

/-- The endpoint-zero vector space V, with the induced C¹ norm. -/
def endpointZero (I : Interval) (m : ℕ) : Submodule ℝ (C1Curve I m) where
  carrier := {η | η.state I.left = 0 ∧ η.state I.right = 0}
  zero_mem' := by constructor <;> rfl
  add_mem' := by
    intro f g hf hg
    constructor
    · change f.state I.left + g.state I.left = 0
      rw [hf.1, hg.1, add_zero]
    · change f.state I.right + g.state I.right = 0
      rw [hf.2, hg.2, add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · change c • f.state I.left = 0
      rw [hf.1, smul_zero]
    · change c • f.state I.right = 0
      rw [hf.2, smul_zero]

/-- Domain is open in time × state × velocity. No global smoothness is built in. -/
structure Lagrangian (m : ℕ) where
  domain : Set (ℝ × State m × State m)
  isOpen_domain : IsOpen domain
  value : (ℝ × State m × State m) → ℝ

def graphPoint (u : C1Curve I m) (t : I.Points) : ℝ × State m × State m :=
  (t, u.state t, u.velocity t)

def graphAdmissible (L : Lagrangian m) (u : C1Curve I m) : Prop :=
  ∀ t : I.Points, graphPoint u t ∈ L.domain

def fixedEndpointClass (L : Lagrangian m) (xₐ xᵦ : State m) : Set (C1Curve I m) :=
  {u | graphAdmissible L u ∧ u.state I.left = xₐ ∧ u.state I.right = xᵦ}

/-- Lebesgue action on C¹ curves; use graphAdmissible for its domain. -/
def action (L : Lagrangian m) (u : C1Curve I m) : ℝ :=
  ∫ t in I.a..I.b, L.value (t, stateField I m u t, velocityField I m u t)

/-- Euclidean gradients identify state/velocity covectors by Riesz. -/
def momentum (L : Lagrangian m) (u : C1Curve I m) (t : I.Points) : State m :=
  (InnerProductSpace.toDual ℝ (State m)).symm
    (fderiv ℝ (fun v => L.value (t, u.state t, v)) (u.velocity t))

def stateGradient (L : Lagrangian m) (u : C1Curve I m) (t : I.Points) : State m :=
  (InnerProductSpace.toDual ℝ (State m)).symm
    (fderiv ℝ (fun z => L.value (t, z, u.velocity t)) (u.state t))

/-- C¹ regularity near the entire closed graph, including its endpoints. -/
def regularNearGraph (L : Lagrangian m) (u : C1Curve I m) (k : ℕ∞) : Prop :=
  ∃ U : Set (ℝ × State m × State m), IsOpen U ∧
    (∀ t : I.Points, graphPoint u t ∈ U) ∧ U ⊆ L.domain ∧
    ContDiffOn ℝ k L.value U

/-- Sup norm of positions only, so velocities are unrestricted in this distance. -/
def uniformDistance (u v : C1Curve I m) : ℝ := ‖u.state - v.state‖

/-- Weak means the norm topology on C¹, never weak Banach convergence. -/
def weakLocalMinimum (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m) : Prop :=
  u ∈ fixedEndpointClass L xₐ xᵦ ∧ ∃ ε > 0, ∀ v ∈ fixedEndpointClass L xₐ xᵦ,
    ‖v - u‖ < ε → action L u ≤ action L v

/-- Strong means a uniform neighborhood in the same C¹ admissible class. -/
def strongLocalMinimum (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m) : Prop :=
  u ∈ fixedEndpointClass L xₐ xᵦ ∧ ∃ ε > 0, ∀ v ∈ fixedEndpointClass L xₐ xᵦ,
    uniformDistance v u < ε → action L u ≤ action L v

/-- A finite partition with C¹ restrictions, allowing distinct one-sided velocities.
Every consecutive pair of knots defines one closed smooth piece. -/
def piecewiseC1 (u : C(I.Points, State m)) : Prop :=
  ∃ knots : Finset ℝ, I.a ∈ knots ∧ I.b ∈ knots ∧
    (∀ c ∈ knots, c ∈ Set.Icc I.a I.b) ∧
    ∀ c ∈ knots, ∀ d ∈ knots, c < d →
      (∀ e ∈ knots, ¬ (c < e ∧ e < d)) →
      ContDiffOn ℝ 1 (extendState I m u) (Set.Icc c d)

/-- At a corner both limiting graphs must be in the Lagrangian domain. -/
def piecewiseAdmissible (L : Lagrangian m) (u : C(I.Points, State m)) : Prop :=
  ∃ knots : Finset ℝ, I.a ∈ knots ∧ I.b ∈ knots ∧
    (∀ c ∈ knots, c ∈ Set.Icc I.a I.b) ∧
    ∀ c ∈ knots, ∀ d ∈ knots, c < d →
      (∀ e ∈ knots, ¬ (c < e ∧ e < d)) →
      ContDiffOn ℝ 1 (extendState I m u) (Set.Icc c d) ∧
      ∀ t ∈ Set.Icc c d,
        (t, extendState I m u t,
          derivWithin (extendState I m u) (Set.Icc c d) t) ∈ L.domain

def piecewiseFixedEndpointClass (L : Lagrangian m) (xₐ xᵦ : State m) :
    Set C(I.Points, State m) :=
  {u | piecewiseAdmissible L u ∧ u I.left = xₐ ∧ u I.right = xᵦ}

/-- Derivative values at the finitely many knots are immaterial to the action. -/
def piecewiseAction (L : Lagrangian m) (u : C(I.Points, State m)) : ℝ :=
  ∫ t in I.a..I.b,
    L.value (t, extendState I m u t,
      derivWithin (extendState I m u) (Set.Icc I.a I.b) t)

def piecewiseStrongLocalMinimum (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C(I.Points, State m)) : Prop :=
  u ∈ piecewiseFixedEndpointClass L xₐ xᵦ ∧
    ∃ ε > 0, ∀ v ∈ piecewiseFixedEndpointClass L xₐ xᵦ,
      ‖v - u‖ < ε → piecewiseAction L u ≤ piecewiseAction L v

/-- Tests are globally smooth with compact support contained in the open interval. -/
def smoothInteriorTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Interval) (η : ℝ → E) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Set.Ioo I.a I.b

/-- Stationarity is an actual derivative of the tested action. -/
def stateStationary (L : Lagrangian m) (u : C1Curve I m) : Prop :=
  ∀ η : ℝ → State m, smoothInteriorTest I η →
    HasDerivAt (fun s : ℝ => ∫ t in I.a..I.b,
      L.value (t, stateField I m u t + s • η t,
        velocityField I m u t + s • deriv η t)) 0 0

/-- Pull back by t_s(t)=t+sζ(t); u_s(t_s(t))=u(t).
The positive Jacobian and endpoint fixation hold for sufficiently small s,
and their derivation belongs to the inner-time-variation theorem. -/
def innerTimeAction (L : Lagrangian m) (u : C1Curve I m)
    (ζ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in I.a..I.b,
    L.value (t + s * ζ t, stateField I m u t,
      (1 + s * deriv ζ t)⁻¹ • velocityField I m u t) * (1 + s * deriv ζ t)

def innerTimeStationary (L : Lagrangian m) (u : C1Curve I m) : Prop :=
  ∀ ζ : ℝ → ℝ, smoothInteriorTest I ζ → HasDerivAt (innerTimeAction L u ζ) 0 0

/-- Increasing affine reference-interval rescaling when aₛ<bₛ. -/
def affineTime (I : Interval) (aₛ bₛ t : ℝ) : ℝ :=
  aₛ + ((t - I.a) / (I.b - I.a)) * (bₛ - aₛ)

/-- Families are required only locally in s. Their pulled-back states form a
C¹-differentiable family in the normed C¹ space. Physical curves outside
[a_s,b_s] have no prescribed meaning. -/
structure MovingEndpointVariation (u : C1Curve I m) where
  leftTime : ℝ → ℝ
  rightTime : ℝ → ℝ
  physicalCurve : ℝ → ℝ → State m
  rescaled : ℝ → C1Curve I m
  left_zero : leftTime 0 = I.a
  right_zero : rightTime 0 = I.b
  rescaled_zero : rescaled 0 = u
  increasing_near : ∀ᶠ s in 𝓝 (0 : ℝ), leftTime s < rightTime s
  rescaling_near : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t : I.Points,
    (rescaled s).state t = physicalCurve s (affineTime I (leftTime s) (rightTime s) t)
  left_differentiable : DifferentiableAt ℝ leftTime 0
  right_differentiable : DifferentiableAt ℝ rightTime 0
  rescaled_differentiable : DifferentiableAt ℝ rescaled 0

/-- Total endpoint state displacement, not the fixed-time vertical component. -/
def endpointDisplacements (u : C1Curve I m) (v : MovingEndpointVariation u) :
    State m × State m :=
  ((deriv v.rescaled 0).state I.left, (deriv v.rescaled 0).state I.right)

def endpointTimeDisplacements (u : C1Curve I m) (v : MovingEndpointVariation u) : ℝ × ℝ :=
  (deriv v.leftTime 0, deriv v.rightTime 0)

end VariationalNotes.Classical

namespace VariationalNotes.Classical.VariationSpacesSpec

def curveSpaceType := Interval → ℕ → Type

def curveSpaceValue : curveSpaceType := @C1Curve

def lagrangiansType := ℕ → Type

def lagrangiansValue : lagrangiansType := @Lagrangian

def variationSpaceType := ∀ (I : Interval) (m : ℕ), Submodule ℝ (C1Curve I m)

def variationSpaceValue : variationSpaceType := @endpointZero

def graphAdmissibleType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → Prop

def graphAdmissibleValue : graphAdmissibleType := @graphAdmissible

def fixedEndpointClassType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → State m → State m → Set (C1Curve I m)

def fixedEndpointClassValue : fixedEndpointClassType := @fixedEndpointClass

def actionType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → ℝ

def actionValue : actionType := @action

def momentumType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → I.Points → State m

def momentumValue : momentumType := @momentum

def stateGradientType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → I.Points → State m

def stateGradientValue : stateGradientType := @stateGradient

def regularNearGraphType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → ℕ∞ → Prop

def regularNearGraphValue : regularNearGraphType := @regularNearGraph

def uniformDistanceType := ∀ {I : Interval} {m : ℕ}, C1Curve I m → C1Curve I m → ℝ

def uniformDistanceValue : uniformDistanceType := @uniformDistance

def weakLocalMinimumType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → State m → State m → C1Curve I m → Prop

def weakLocalMinimumValue : weakLocalMinimumType := @weakLocalMinimum

def strongLocalMinimumType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → State m → State m → C1Curve I m → Prop

def strongLocalMinimumValue : strongLocalMinimumType := @strongLocalMinimum

def piecewiseC1Type := ∀ {I : Interval} {m : ℕ}, C(I.Points, State m) → Prop

def piecewiseC1Value : piecewiseC1Type := @piecewiseC1

def piecewiseAdmissibleType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C(I.Points, State m) → Prop

def piecewiseAdmissibleValue : piecewiseAdmissibleType := @piecewiseAdmissible

def piecewiseFixedEndpointClassType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → State m → State m → Set C(I.Points, State m)

def piecewiseFixedEndpointClassValue : piecewiseFixedEndpointClassType := @piecewiseFixedEndpointClass

def piecewiseActionType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C(I.Points, State m) → ℝ

def piecewiseActionValue : piecewiseActionType := @piecewiseAction

def piecewiseStrongLocalMinimumType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → State m → State m → C(I.Points, State m) → Prop

def piecewiseStrongLocalMinimumValue : piecewiseStrongLocalMinimumType := @piecewiseStrongLocalMinimum

def smoothStateTestType := Interval → ∀ (m : ℕ), (ℝ → State m) → Prop

def smoothStateTestValue : smoothStateTestType := fun I m η => smoothInteriorTest I (η : ℝ → State m)

def smoothTimeTestType := Interval → (ℝ → ℝ) → Prop

def smoothTimeTestValue : smoothTimeTestType := fun I ζ => smoothInteriorTest I (ζ : ℝ → ℝ)

def stateStationaryType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → Prop

def stateStationaryValue : stateStationaryType := @stateStationary

def innerTimeActionType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → (ℝ → ℝ) → ℝ → ℝ

def innerTimeActionValue : innerTimeActionType := @innerTimeAction

def innerTimeStationaryType := ∀ {I : Interval} {m : ℕ}, Lagrangian m → C1Curve I m → Prop

def innerTimeStationaryValue : innerTimeStationaryType := @innerTimeStationary

def affineTimeType := Interval → ℝ → ℝ → ℝ → ℝ

def affineTimeValue : affineTimeType := @affineTime

def movingEndpointVariationsType := ∀ {I : Interval} {m : ℕ}, C1Curve I m → Type

def movingEndpointVariationsValue : movingEndpointVariationsType := @MovingEndpointVariation

def endpointDisplacementsType := ∀ {I : Interval} {m : ℕ} (u : C1Curve I m), MovingEndpointVariation u → State m × State m

def endpointDisplacementsValue : endpointDisplacementsType := @endpointDisplacements

def endpointTimeDisplacementsType := ∀ {I : Interval} {m : ℕ} (u : C1Curve I m), MovingEndpointVariation u → ℝ × ℝ

def endpointTimeDisplacementsValue : endpointTimeDisplacementsType := @endpointTimeDisplacements

def curve_derivativeType : Prop := ∀ (I : Interval) (m : ℕ) (u : C1Curve I m) (t : I.Points),
    HasDerivWithinAt (stateField I m u) (u.velocity t) (Set.Icc I.a I.b) t

def velocity_eq_derivWithinType : Prop := ∀ (I : Interval) (m : ℕ) (u : C1Curve I m) (t : I.Points),
    u.velocity t = derivWithin (stateField I m u) (Set.Icc I.a I.b) t

def curve_normType : Prop := ∀ (I : Interval) (m : ℕ) (u : C1Curve I m),
    ‖u‖ = max ‖u.state‖ ‖u.velocity‖

def momentum_pairingType : Prop := ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (t : I.Points) (w : State m),
    inner ℝ (momentum L u t) w =
      fderiv ℝ (fun v => L.value (t, u.state t, v)) (u.velocity t) w

def stateGradient_pairingType : Prop := ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m)
    (t : I.Points) (w : State m),
    inner ℝ (stateGradient L u t) w =
      fderiv ℝ (fun z => L.value (t, z, u.velocity t)) (u.state t) w

def affineTime_endpointsType : Prop := ∀ (I : Interval) (aₛ bₛ : ℝ),
    affineTime I aₛ bₛ I.a = aₛ ∧ affineTime I aₛ bₛ I.b = bₛ

def affineTime_increasingType : Prop := ∀ (I : Interval) (aₛ bₛ : ℝ), aₛ < bₛ →
    StrictMono (affineTime I aₛ bₛ)

def piecewiseAdmissible_regularType : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C(I.Points, State m)),
    piecewiseAdmissible L u → piecewiseC1 u

def endpointDisplacements_totalType : Prop :=
  ∀ (I : Interval) (m : ℕ) (u : C1Curve I m) (v : MovingEndpointVariation u),
    endpointDisplacements u v =
      (deriv (fun s => v.physicalCurve s (v.leftTime s)) 0,
       deriv (fun s => v.physicalCurve s (v.rightTime s)) 0)

def c1_contDiffOnType : Prop :=
  ∀ (I : Interval) (m : ℕ) (u : C1Curve I m),
    ContDiffOn ℝ 1 (stateField I m u) (Set.Icc I.a I.b)

def piecewiseAction_of_C1Type : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    piecewiseAction L u.state = action L u

def graphAdmissible_piecewiseType : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    graphAdmissible L u → piecewiseAdmissible L u.state

end VariationalNotes.Classical.VariationSpacesSpec
