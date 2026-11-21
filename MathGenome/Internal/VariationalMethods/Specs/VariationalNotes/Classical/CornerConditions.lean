import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.BoundaryTransversality
import Mathlib.Topology.Order.ProjIcc

/-!
The two closed pieces retain their separate velocities at the common endpoint.
A competitor is represented by its corner time and its two C¹ pullbacks under
increasing affine rescaling. Their endpoint states must agree exactly. Thus
these are joined piecewise C¹ competitors, not independently moving endpoints.
The action is the sum of the two integrals after change of variable.

Uniform closeness below is measured in physical time: at every point of each
rescaled piece, compare its position to the reference position at that physical
time. Since both affine maps are onto their physical intervals, this is precisely
the uniform neighborhood of the joined physical curve. Clamping only extends the
reference outside the exterior endpoints and does not change this distance.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical.Corner

structure Domain where
  a : ℝ
  c : ℝ
  b : ℝ
  left_lt : a < c
  right_lt : c < b

def Domain.left (K : Domain) : Interval := ⟨K.a, K.c, K.left_lt⟩
def Domain.right (K : Domain) : Interval := ⟨K.c, K.b, K.right_lt⟩

def Domain.whole (K : Domain) : Interval := ⟨K.a, K.b, K.left_lt.trans K.right_lt⟩

def Domain.leftToWhole (K : Domain) (t : K.left.Points) : K.whole.Points :=
  ⟨t, t.property.1, t.property.2.trans K.right_lt.le⟩

def Domain.rightToWhole (K : Domain) (t : K.right.Points) : K.whole.Points :=
  ⟨t, K.left_lt.le.trans t.property.1, t.property.2⟩

abbrev Configuration (K : Domain) (m : ℕ) :=
  ℝ × C1Curve K.left m × C1Curve K.right m

def reference {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) : Configuration K m := (K.c, u, v)

def leftConfiguration {K : Domain} {m : ℕ} (x : Configuration K m) :
    Boundary.Configuration K.left m := (K.a, x.1, x.2.1)

def rightConfiguration {K : Domain} {m : ℕ} (x : Configuration K m) :
    Boundary.Configuration K.right m := (x.1, K.b, x.2.2)

def totalAction {K : Domain} {m : ℕ} (L : Lagrangian m) (x : Configuration K m) : ℝ :=
  Boundary.referenceAction L (leftConfiguration x) +
    Boundary.referenceAction L (rightConfiguration x)

/-- `freeTime = false` fixes the corner time; the joined state is free in both cases. -/
def feasible {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m) (freeTime : Bool) :
    Set (Configuration K m) := {x |
  Boundary.referenceAdmissible L (leftConfiguration x) ∧
  Boundary.referenceAdmissible L (rightConfiguration x) ∧
  x.2.1.state K.left.left = u.state K.left.left ∧
  x.2.2.state K.right.right = v.state K.right.right ∧
  x.2.1.state K.left.right = x.2.2.state K.right.left ∧
  (freeTime = false → x.1 = K.c)}

def clampedState {I : Interval} {m : ℕ} (u : C1Curve I m) (t : ℝ) : State m :=
  u.state (projIcc I.a I.b I.increasing.le t)

/-- The actual continuous joined state, extended constantly at the outer endpoints. -/
def referenceState {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (t : ℝ) : State m :=
  if t ≤ K.c then clampedState u t else clampedState v t

def UniformClose {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (x : Configuration K m) (ε : ℝ) : Prop :=
  (∀ t : K.left.Points, ‖x.2.1.state t -
    referenceState u v (affineTime K.left K.a x.1 t)‖ < ε) ∧
  (∀ t : K.right.Points, ‖x.2.2.state t -
    referenceState u v (affineTime K.right x.1 K.b t)‖ < ε)

/-- The given continuous curve has these two closed C¹ restrictions. -/
def Represents {K : Domain} {m : ℕ} (w : C(K.whole.Points, State m))
    (u : C1Curve K.left m) (v : C1Curve K.right m) : Prop :=
  (∀ t, w (K.leftToWhole t) = u.state t) ∧
  (∀ t, w (K.rightToWhole t) = v.state t)

/-- In the fixed-time class the two smooth pieces end at the prescribed corner;
with time free all continuous piecewise C¹ competitors are allowed. This is the
shared physical uniform minimum, with that optional restriction on competitors. -/
def PiecewiseMinimum {K : Domain} {m : ℕ} (L : Lagrangian m)
    (w : C(K.whole.Points, State m)) (freeTime : Bool) : Prop :=
  w ∈ piecewiseFixedEndpointClass L (w K.whole.left) (w K.whole.right) ∧
  ∃ ε > 0, ∀ f ∈ piecewiseFixedEndpointClass L (w K.whole.left) (w K.whole.right),
    (freeTime = false →
      ContDiffOn ℝ 1 (extendState K.whole m f) (Icc K.a K.c) ∧
      ContDiffOn ℝ 1 (extendState K.whole m f) (Icc K.c K.b)) →
    ‖f - w‖ < ε → piecewiseAction L w ≤ piecewiseAction L f

end VariationalNotes.Classical.Corner

namespace Specs.VariationalNotes.Classical.Corner
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.Corner

/-- Physical formulation of the fixed-time conclusion, using the shared
piecewise action and sup norm on continuous curves. -/
def fixedTimeMomentum : Prop :=
  ∀ (K : Domain) (m : ℕ) (L : Lagrangian m)
    (w : C(K.whole.Points, State m)) (u : C1Curve K.left m) (v : C1Curve K.right m),
    Represents w u v → regularNearGraph L u 1 → regularNearGraph L v 1 →
    PiecewiseMinimum L w false →
    momentum L u K.left.right = momentum L v K.right.left

/-- Physical formulation with free corner time. For `true`, PiecewiseMinimum
is equivalent to the shared piecewiseStrongLocalMinimum. -/
def freeTimeConditions : Prop :=
  ∀ (K : Domain) (m : ℕ) (L : Lagrangian m)
    (w : C(K.whole.Points, State m)) (u : C1Curve K.left m) (v : C1Curve K.right m),
    Represents w u v → regularNearGraph L u 1 → regularNearGraph L v 1 →
    PiecewiseMinimum L w true →
    momentum L u K.left.right = momentum L v K.right.left ∧
    (L.value (graphPoint u K.left.right) -
      inner ℝ (momentum L u K.left.right) (u.velocity K.left.right)) =
    (L.value (graphPoint v K.right.left) -
      inner ℝ (momentum L v K.right.left) (v.velocity K.right.left))

/-- Direct specialization to the shared continuous piecewise C¹ competitor
class and its uniform strong minimum. This covers the manuscript's piecewise
C² stationary case without any extra regularity or stationarity assumption. -/
def strongMinimumConditions : Prop :=
  ∀ (K : Domain) (m : ℕ) (L : Lagrangian m)
    (w : C(K.whole.Points, State m)) (u : C1Curve K.left m) (v : C1Curve K.right m),
    Represents w u v → regularNearGraph L u 1 → regularNearGraph L v 1 →
    piecewiseStrongLocalMinimum L (w K.whole.left) (w K.whole.right) w →
    momentum L u K.left.right = momentum L v K.right.left ∧
    (L.value (graphPoint u K.left.right) -
      inner ℝ (momentum L u K.left.right) (u.velocity K.left.right)) =
    (L.value (graphPoint v K.right.left) -
      inner ℝ (momentum L v K.right.left) (v.velocity K.right.left))

end Specs.VariationalNotes.Classical.Corner
