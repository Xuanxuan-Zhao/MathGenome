import MathGenome.Internal.Specs.D05.M12.Norm

/-!
Independent statements for K05.12.parallelogram, paper.tex:1939–1954.
The primary statements use the shared algebraic axioms and the shared induced
norm, so no dimension, topology, or completeness assumption is imposed.
The final statements specialize to the canonical first-slot convention.
-/

namespace Specs.D05.M12.Parallelogram

universe u v

/-- The two expansions used in the paper's proof. -/
def norm_sq_expansions : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedNorm h (u + v) ^ 2 =
      _root_.D05.inducedNorm h u ^ 2 + _root_.D05.inducedNorm h v ^ 2 +
        2 * RCLike.re (h u v) ∧
    _root_.D05.inducedNorm h (u - v) ^ 2 =
      _root_.D05.inducedNorm h u ^ 2 + _root_.D05.inducedNorm h v ^ 2 -
        2 * RCLike.re (h u v)

def parallelogram : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    _root_.D05.inducedNorm h (u + v) ^ 2 + _root_.D05.inducedNorm h (u - v) ^ 2 =
      2 * _root_.D05.inducedNorm h u ^ 2 + 2 * _root_.D05.inducedNorm h v ^ 2

def real_polarization : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℝ V]
    (h : V → V → ℝ), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    h u v = (1 / 4 : ℝ) *
      (_root_.D05.inducedNorm h (u + v) ^ 2 - _root_.D05.inducedNorm h (u - v) ^ 2)

/-- The signs here are for linearity in the first slot. -/
def complex_polarization : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℂ V]
    (h : V → V → ℂ), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    h u v = (1 / 4 : ℂ) *
      (((_root_.D05.inducedNorm h (u + v) ^ 2 : ℝ) : ℂ) -
        ((_root_.D05.inducedNorm h (u - v) ^ 2 : ℝ) : ℂ) +
        Complex.I * ((_root_.D05.inducedNorm h (u + Complex.I • v) ^ 2 : ℝ) : ℂ) -
        Complex.I * ((_root_.D05.inducedNorm h (u - Complex.I • v) ^ 2 : ℝ) : ℂ))

def real_inner_determined_by_norm : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℝ V] (h k : V → V → ℝ),
    _root_.D05.IsFirstInnerProduct h → _root_.D05.IsFirstInnerProduct k →
    (∀ v, _root_.D05.inducedNorm h v = _root_.D05.inducedNorm k v) → h = k

def complex_inner_determined_by_norm : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (h k : V → V → ℂ),
    _root_.D05.IsFirstInnerProduct h → _root_.D05.IsFirstInnerProduct k →
    (∀ v, _root_.D05.inducedNorm h v = _root_.D05.inducedNorm k v) → h = k

def canonical_parallelogram : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2

def canonical_real_polarization : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V),
    _root_.D05.firstInner (F := ℝ) u v =
      (1 / 4 : ℝ) * (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2)

def canonical_complex_polarization : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u v : V),
    _root_.D05.firstInner (F := ℂ) u v = (1 / 4 : ℂ) *
      (((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u - v‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * ((‖u + Complex.I • v‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * ((‖u - Complex.I • v‖ ^ 2 : ℝ) : ℂ))

end Specs.D05.M12.Parallelogram
