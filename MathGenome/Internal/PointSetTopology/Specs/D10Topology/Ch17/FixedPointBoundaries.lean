import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

/-! Independent specifications for paper.tex, d10:17:fixed-point-boundaries.
The complex plane carries its usual Euclidean topology. The coordinate bridge
below explicitly identifies the circle and its rotations in real plane coordinates.
No fixed-point existence result is assumed. -/

open Set
noncomputable section
universe u

namespace Specs.D10Topology.Ch17.FixedPointBoundaries

def unitCircle : Set ℂ := {z | ‖z‖ = 1}

def circleRotation (a : ℂ) (ha : ‖a‖ = 1) : unitCircle → unitCircle :=
  fun z => ⟨a * z.1, by
    change ‖a * z.1‖ = 1
    rw [norm_mul, ha, one_mul]
    exact z.2⟩

def intervalMap : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1 :=
  fun x => ⟨(x.1 + 1) / 2, by
    constructor
    · exact div_pos (add_pos x.2.1 zero_lt_one) (by norm_num)
    · exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        (by simpa only [one_mul, one_add_one_eq_two, add_comm] using add_lt_add_right x.2.2 1)⟩

def unitCircleType := Set ℂ
def unitCircleValue : unitCircleType := {z | ‖z‖ = 1}
def circleRotationType := (a : ℂ) → ‖a‖ = 1 → unitCircle → unitCircle
def intervalMapType := Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1

def empty_no_fixed_point : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [IsEmpty X] (f : X → X),
    Continuous f ∧ ¬ ∃ x, f x = x

/-- The real-coordinate bridge includes the topology and the rotation matrix. -/
def circle_plane_coordinates : Prop :=
  IsHomeomorph (fun z : ℂ => (z.re, z.im)) ∧
  (∀ z : ℂ, z ∈ unitCircle ↔ z.re ^ 2 + z.im ^ 2 = 1) ∧
  ∀ (a : ℂ) (ha : ‖a‖ = 1) (z : unitCircle),
    ((circleRotation a ha z).1.re, (circleRotation a ha z).1.im) =
      (a.re * z.1.re - a.im * z.1.im, a.re * z.1.im + a.im * z.1.re)

def circle_geometry : Prop :=
  unitCircle.Nonempty ∧ IsCompact unitCircle ∧ ¬ Convex ℝ unitCircle

def rotation_properties : Prop :=
  ∀ (a : ℂ) (ha : ‖a‖ = 1), a ≠ 1 →
    Continuous (circleRotation a ha) ∧ ¬ ∃ z, circleRotation a ha z = z

def interval_geometry : Prop :=
  (Ioo (0 : ℝ) 1).Nonempty ∧ Convex ℝ (Ioo (0 : ℝ) 1) ∧
    Bornology.IsBounded (Ioo (0 : ℝ) 1) ∧ ¬ IsCompact (Ioo (0 : ℝ) 1)

def interval_properties : Prop :=
  Continuous intervalMap ∧ ¬ ∃ x, intervalMap x = x

/-- Nontrivial means that the set contains two distinct points. No interior or
full dimension is required. The identity also fails every strict contraction bound. -/
def identity_properties : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E),
    IsCompact K → Convex ℝ K → K.Nontrivial →
    Continuous (id : K → K) ∧ (∀ x : K, id x = x) ∧
      (∃ x y : K, x ≠ y ∧ id x = x ∧ id y = y) ∧
      ∀ q : ℝ, q < 1 →
        ¬ ∀ x y : K, dist (id x) (id y) ≤ q * dist x y

end Specs.D10Topology.Ch17.FixedPointBoundaries
