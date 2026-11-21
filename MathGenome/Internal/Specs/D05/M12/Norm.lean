import MathGenome.Internal.Specs.D05.M12.InnerProduct

/-!
Independent specification for K05.12.norm, paper.tex:1895–1900.
The real part extracts the real diagonal value in either scalar field.
The substantive laws assume only the previously defined inner-product axioms
on an arbitrary module, without a given norm or any dimension restriction.
The final bridges use exactly the shared `D05.firstInner` convention.
-/

noncomputable section

namespace D05

/-- The nonnegative real square root of the diagonal of a form. -/
def inducedNorm {F V : Type*} [RCLike F] (h : V → V → F) (v : V) : ℝ :=
  Real.sqrt (RCLike.re (h v v))

/-- The distance induced by the same form and the given vector subtraction. -/
def inducedDistance {F V : Type*} [RCLike F] [Sub V]
    (h : V → V → F) (u v : V) : ℝ := inducedNorm h (u - v)

end D05

namespace Specs.D05.M12.Norm

universe u v

def inducedNorm_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → (V → V → F) → V → ℝ

def inducedNorm_value : inducedNorm_type.{u, v} :=
  fun h v => Real.sqrt (RCLike.re (h v v))

def inducedDistance_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [Sub V] →
    (V → V → F) → V → V → ℝ

def inducedDistance_value : inducedDistance_type.{u, v} :=
  fun h u v => Real.sqrt (RCLike.re (h (u - v) (u - v)))

/-- Diagonals are real and nonnegative, justifying the square root. -/
def diagonal_real_nonneg : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v,
    h v v = ((RCLike.re (h v v) : ℝ) : F) ∧ 0 ≤ RCLike.re (h v v)

def inducedNorm_nonneg : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] (h : V → V → F) (v : V),
    0 ≤ _root_.D05.inducedNorm h v

def inducedNorm_sq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v,
    _root_.D05.inducedNorm h v ^ 2 = RCLike.re (h v v)

/-- This is the scalar-valued interpretation of the paper's norm square. -/
def diagonal_eq_norm_sq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v,
    h v v = ((_root_.D05.inducedNorm h v ^ 2 : ℝ) : F)

def inducedNorm_eq_zero_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v,
    _root_.D05.inducedNorm h v = 0 ↔ v = 0

def inducedNorm_smul_sq : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ (a : F) (v : V),
    _root_.D05.inducedNorm h (a • v) ^ 2 = ‖a‖ ^ 2 * _root_.D05.inducedNorm h v ^ 2

def inducedNorm_smul : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ (a : F) (v : V),
    _root_.D05.inducedNorm h (a • v) = ‖a‖ * _root_.D05.inducedNorm h v

def inducedDistance_nonneg : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [Sub V]
    (h : V → V → F) (u v : V), 0 ≤ _root_.D05.inducedDistance h u v

def inducedDistance_eq_zero_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedDistance h u v = 0 ↔ u = v

/-- On a Mathlib inner-product space, this construction is its existing norm. -/
def inducedNorm_eq_norm : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (v : V),
    _root_.D05.inducedNorm (_root_.D05.firstInner (F := F)) v = ‖v‖

def inducedDistance_eq_dist : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    _root_.D05.inducedDistance (_root_.D05.firstInner (F := F)) u v = dist u v

end Specs.D05.M12.Norm
