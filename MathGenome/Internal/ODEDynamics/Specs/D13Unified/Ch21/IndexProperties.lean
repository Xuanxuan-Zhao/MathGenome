import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent specification of Lemma d13:21:index-properties.
The oriented Euclidean plane is represented by ℂ, with coordinates (re,im).
Loops have the closed unit interval as domain; no regularity is included in
`Loop` beyond continuity. In particular, no separation theorem is assumed. -/
namespace Specs.D13Unified.Ch21.IndexProperties
open unitInterval
open scoped Topology
noncomputable section

structure Loop where
  map : C(I, ℂ)
  closed : map 0 = map 1

instance : CoeFun Loop (fun _ => I → ℂ) := ⟨fun α => α.map⟩
def LoopType := Type
def LoopValue : LoopType := Loop

def period : ℂ := 2 * (Real.pi : ℂ) * Complex.I

def Avoids (α : Loop) (p : ℂ) : Prop := ∀ t, α t ≠ p

def IsLogLift (α : Loop) (p : ℂ) (L : C(I, ℂ)) : Prop :=
  ∀ t, Complex.exp (L t) = α t - p

def IsArgument (α : Loop) (p : ℂ) (θ : C(I, ℝ)) : Prop :=
  ∀ t, α t - p = (‖α t - p‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

/-- Endpoint change of an actual continuous logarithmic lift. -/
def HasIndex (α : Loop) (p : ℂ) (k : ℤ) : Prop :=
  ∃ L : C(I, ℂ), IsLogLift α p L ∧ L 1 - L 0 = (k : ℂ) * period

/-- Totalized by zero at points on the trace. Existence and uniqueness off
 the trace are obligations, not fields or certificates in this definition. -/
def index (α : Loop) (p : ℂ) : ℤ := by
  classical
  exact if h : ∃ k, HasIndex α p k then Classical.choose h else 0

def planeDet (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

def circleLoop (γ : C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ)) : Loop where
  map := ⟨fun t => γ (Specs.D13Unified.Ch15.CircleLift.quotientMap t),
    γ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)⟩
  closed := by
    change γ ((0 : ℝ) : AddCircle (1 : ℝ)) = γ ((1 : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_zero, AddCircle.coe_period]

def log_lift_existsStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p → ∃ L : C(I, ℂ), IsLogLift α p L

def log_lifts_differ_by_integerStatement : Prop :=
  ∀ (α : Loop) (p : ℂ) (L M : C(I, ℂ)),
    IsLogLift α p L → IsLogLift α p M →
    ∃ k : ℤ, ∀ t, L t = M t + (k : ℂ) * period

def index_exists_uniqueStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p → ∃! k : ℤ, HasIndex α p k

def index_characterizationStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p →
    ∀ k : ℤ, HasIndex α p k ↔ k = index α p

def argument_lift_existsStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p →
    ∃ θ : C(I, ℝ), IsArgument α p θ ∧
      θ 1 - θ 0 = 2 * Real.pi * (index α p : ℝ)

def argument_lift_independentStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p →
    ∀ θ : C(I, ℝ), IsArgument α p θ →
      θ 1 - θ 0 = 2 * Real.pi * (index α p : ℝ)

/-- Free loop homotopies: the basepoint is allowed to move. -/
def homotopy_invariantStatement : Prop :=
  ∀ (α β : Loop) (p : ℂ) (H : C(I × I, ℂ)),
    (∀ t, H (0, t) = α t) → (∀ t, H (1, t) = β t) →
    (∀ s, H (s, 0) = H (s, 1)) → (∀ s t, H (s, t) ≠ p) →
    index α p = index β p

def index_locally_constantStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p →
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℂ, dist q p < ε →
      Avoids α q ∧ index α q = index α p

def index_zero_outside_ballStatement : Prop :=
  ∀ α : Loop, ∃ R : ℝ, 0 < R ∧ ∀ p : ℂ, R < ‖p‖ →
    Avoids α p ∧ index α p = 0

/-- C¹ on the closed interval includes the one-sided endpoint derivatives.
The derivative function is supplied explicitly so no global extension is assumed. -/
def integral_formulaStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p →
    ∀ (f f' : ℝ → ℂ), (∀ t : I, f t = α t) →
      ContinuousOn f (Set.Icc 0 1) → ContinuousOn f' (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Icc 0 1) t) →
      (index α p : ℝ) = (2 * Real.pi)⁻¹ *
        ∫ t in (0 : ℝ)..1, planeDet (f t - p) (f' t) / ‖f t - p‖ ^ 2

/-- The periodic real lift respects equality modulo every integer. -/
def circle_periodic_liftStatement : Prop :=
  ∀ (γ : C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ)) (x : ℝ) (k : ℤ),
    γ (Specs.D13Unified.Ch15.CircleLift.quotientMap (x + (k : ℝ))) =
      γ (Specs.D13Unified.Ch15.CircleLift.quotientMap x)

def circle_parameter_eqStatement : Prop :=
  ∀ x y : ℝ, Specs.D13Unified.Ch15.CircleLift.quotientMap x =
    Specs.D13Unified.Ch15.CircleLift.quotientMap y ↔ ∃ k : ℤ, x = y + (k : ℝ)

def circle_traceStatement : Prop :=
  ∀ γ : C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ),
    Set.range (circleLoop γ) = Set.range γ

def circle_avoidsStatement : Prop :=
  ∀ (γ : C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ)) (p : ℂ),
    Avoids (circleLoop γ) p ↔ ∀ x, γ x ≠ p


def index_characterization_by_argumentStatement : Prop :=
  ∀ (α : Loop) (p : ℂ), Avoids α p → ∀ k : ℤ,
    (∃ θ : C(I, ℝ), IsArgument α p θ ∧ θ 1 - θ 0 = 2 * Real.pi * (k : ℝ)) ↔
      k = index α p

def plane_coordinatesStatement : Prop :=
  ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 ∧
    (Complex.I * z).re = -z.im ∧ (Complex.I * z).im = z.re

def circle_integral_formulaStatement : Prop :=
  ∀ (γ : C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ)) (p : ℂ),
    (∀ x, γ x ≠ p) → ∀ f' : ℝ → ℂ, ContinuousOn f' (Set.Icc 0 1) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => γ (Specs.D13Unified.Ch15.CircleLift.quotientMap t))
        (f' t) (Set.Icc 0 1) t) →
    (index (circleLoop γ) p : ℝ) = (2 * Real.pi)⁻¹ *
      ∫ t in (0 : ℝ)..1,
        planeDet (γ (Specs.D13Unified.Ch15.CircleLift.quotientMap t) - p) (f' t) /
          ‖γ (Specs.D13Unified.Ch15.CircleLift.quotientMap t) - p‖ ^ 2

def AvoidsType := Loop → ℂ → Prop
def IsLogLiftType := Loop → ℂ → C(I, ℂ) → Prop
def IsArgumentType := Loop → ℂ → C(I, ℝ) → Prop
def HasIndexType := Loop → ℂ → ℤ → Prop
def indexType := Loop → ℂ → ℤ
def periodType := ℂ
def planeDetType := ℂ → ℂ → ℝ
def circleLoopType := C(Specs.D13Unified.Ch15.CircleLift.Circle, ℂ) → Loop

end
end Specs.D13Unified.Ch21.IndexProperties
