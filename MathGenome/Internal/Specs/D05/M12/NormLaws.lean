import MathGenome.Internal.Specs.D05.M12.Norm

/-!
Independent statements for K05.12.norm_laws, paper.tex:1915–1937.
All substantive laws start with the algebraic inner-product axioms on the given
module, and use the shared square-root norm and distance. No norm, topology,
finite dimension, or completeness is assumed. The final corollary records the
positive-real-multiple equality case in the complete source entry.
-/

namespace Specs.D05.M12.NormLaws

universe u v

def inducedNorm_add_sq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedNorm h (u + v) ^ 2 =
      _root_.D05.inducedNorm h u ^ 2 + 2 * RCLike.re (h u v) +
        _root_.D05.inducedNorm h v ^ 2

def inducedNorm_add_sq_le : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedNorm h (u + v) ^ 2 ≤
      (_root_.D05.inducedNorm h u + _root_.D05.inducedNorm h v) ^ 2

def inducedNorm_triangle : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedNorm h (u + v) ≤
      _root_.D05.inducedNorm h u + _root_.D05.inducedNorm h v

def inducedNorm_neg : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v,
    _root_.D05.inducedNorm h (-v) = _root_.D05.inducedNorm h v

/-- The complete norm axioms for this precise function and scalar action. -/
def norm_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    (∀ v, 0 ≤ _root_.D05.inducedNorm h v) ∧
    (∀ v, _root_.D05.inducedNorm h v = 0 ↔ v = 0) ∧
    (∀ (a : F) v, _root_.D05.inducedNorm h (a • v) = ‖a‖ * _root_.D05.inducedNorm h v) ∧
    (∀ u v, _root_.D05.inducedNorm h (u + v) ≤
      _root_.D05.inducedNorm h u + _root_.D05.inducedNorm h v)

def pythagoras : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    h u v = 0 → _root_.D05.inducedNorm h (u + v) ^ 2 =
      _root_.D05.inducedNorm h u ^ 2 + _root_.D05.inducedNorm h v ^ 2

def inducedDistance_symm : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedDistance h u v = _root_.D05.inducedDistance h v u

def inducedDistance_triangle : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v w,
    _root_.D05.inducedDistance h u w ≤
      _root_.D05.inducedDistance h u v + _root_.D05.inducedDistance h v w

/-- In particular, the given distance is a metric, including on a zero space. -/
def metric_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    (∀ u v, 0 ≤ _root_.D05.inducedDistance h u v) ∧
    (∀ u v, _root_.D05.inducedDistance h u v = 0 ↔ u = v) ∧
    (∀ u v, _root_.D05.inducedDistance h u v = _root_.D05.inducedDistance h v u) ∧
    (∀ u v w, _root_.D05.inducedDistance h u w ≤
      _root_.D05.inducedDistance h u v + _root_.D05.inducedDistance h v w)

/-- The Pythagorean conclusion in the shared Mathlib convention. -/
def firstInner_pythagoras : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    _root_.D05.firstInner (F := F) u v = 0 → ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2

/-- Triangle equality requires a positive real multiple, also over ℂ. -/
def triangle_equality : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    (_root_.D05.inducedNorm h (u + v) =
        _root_.D05.inducedNorm h u + _root_.D05.inducedNorm h v ↔
      u = 0 ∨ v = 0 ∨ ∃ t : ℝ, 0 < t ∧ v = (t : F) • u)

def triangle_equality_of_ne_zero : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v, u ≠ 0 →
    (_root_.D05.inducedNorm h (u + v) =
        _root_.D05.inducedNorm h u + _root_.D05.inducedNorm h v ↔
      ∃ t : ℝ, 0 ≤ t ∧ v = (t : F) • u)

def firstInner_triangle_equality : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    (‖u + v‖ = ‖u‖ + ‖v‖ ↔
      u = 0 ∨ v = 0 ∨ ∃ t : ℝ, 0 < t ∧ v = (t : F) • u)

end Specs.D05.M12.NormLaws
