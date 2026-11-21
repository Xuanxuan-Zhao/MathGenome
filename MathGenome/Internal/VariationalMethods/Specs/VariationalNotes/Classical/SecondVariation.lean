import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical

/-- State-state block of the full Hessian, with time held fixed. -/
def secondVariationZZ {m : ℕ} (L : Lagrangian m)
    (x : ℝ × State m × State m) (z w : State m) : ℝ :=
  fderiv ℝ (fderiv ℝ L.value) x (0, z, 0) (0, w, 0)

/-- State-velocity block: the first Hessian slot is the state insertion.
For a C² Lagrangian the reversed velocity-state block is its transpose. -/
def secondVariationZV {m : ℕ} (L : Lagrangian m)
    (x : ℝ × State m × State m) (z v : State m) : ℝ :=
  fderiv ℝ (fderiv ℝ L.value) x (0, z, 0) (0, 0, v)

def secondVariationVV {m : ℕ} (L : Lagrangian m)
    (x : ℝ × State m × State m) (v w : State m) : ℝ :=
  fderiv ℝ (fderiv ℝ L.value) x (0, 0, v) (0, 0, w)

/-- The displayed Hessian-block integral, defined before imposing minimality
or endpoint conditions on the direction. All blocks are evaluated at the
unperturbed state-velocity graph. -/
def secondVariationForm {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u η : C1Curve I m) : ℝ :=
  ∫ t in I.a..I.b,
    let x := (t, stateField I m u t, velocityField I m u t)
    let z := stateField I m η t
    let v := velocityField I m η t
    secondVariationZZ L x z z + 2 * secondVariationZV L x z v +
      secondVariationVV L x v v

end VariationalNotes.Classical

namespace Specs.VariationalNotes.Classical.SecondVariation
open _root_.VariationalNotes.Classical

def hessianZZType := ∀ {m : ℕ}, Lagrangian m →
  (ℝ × State m × State m) → State m → State m → ℝ
def hessianZZValue : hessianZZType := @secondVariationZZ

def hessianZVType := ∀ {m : ℕ}, Lagrangian m →
  (ℝ × State m × State m) → State m → State m → ℝ
def hessianZVValue : hessianZVType := @secondVariationZV

def hessianVVType := ∀ {m : ℕ}, Lagrangian m →
  (ℝ × State m × State m) → State m → State m → ℝ
def hessianVVValue : hessianVVType := @secondVariationVV

def quadraticFormType := ∀ {I : Interval} {m : ℕ},
  Lagrangian m → C1Curve I m → C1Curve I m → ℝ
def quadraticFormValue : quadraticFormType := @secondVariationForm

/-- The mixed block agrees with the symmetric Euclidean Hessian. -/
def mixedHessian_symmetric : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 2 → ∀ (t : I.Points) (z v : State m),
      secondVariationZV L (graphPoint u t) z v =
        fderiv ℝ (fderiv ℝ L.value) (graphPoint u t) (0, 0, v) (0, z, 0)

/-- Existence and value of the twice directional derivative, without minimality
and for all C¹ directions (not only endpoint-zero directions). -/
def classicalSecondActionDerivative : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u η : C1Curve I m),
    regularNearGraph L u 2 →
      HasDerivAt (deriv (fun s : ℝ => action L (u + s • η)))
        (secondVariationForm L u η) 0

/-- The second derivative and its nonnegativity at a weak C¹ local minimum,
with precisely the source's endpoint-zero C¹ class. -/
def classicalSecondVariation : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (xₐ xᵦ : State m)
    (u : C1Curve I m),
    weakLocalMinimum L xₐ xᵦ u → regularNearGraph L u 2 →
    ∀ η : C1Curve I m, η ∈ endpointZero I m →
      HasDerivAt (deriv (fun s : ℝ => action L (u + s • η)))
        (secondVariationForm L u η) 0 ∧ 0 ≤ secondVariationForm L u η

end Specs.VariationalNotes.Classical.SecondVariation
