import MathGenome.Internal.Specs.D05.M12.Norm
import MathGenome.Internal.Specs.D05.M02.Independence

/-!
Independent statements for the triangle-equality corollary, paper.tex:1929–1937.
The scalar parameter is real even when the vector space is complex. The first
two statements use the algebraic inner-product axioms and their induced norm;
the next two use the corresponding Mathlib structure. No dimension or
completeness hypothesis is imposed. The last two statements retain the source's
nonzero complex-phase counterexample, including dependence of the indexed pair.
-/

namespace Specs.D05.M12.NormLaws.TriangleEquality

universe u v

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

def firstInner_triangle_equality_of_ne_zero : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V), u ≠ 0 →
    (‖u + v‖ = ‖u‖ + ‖v‖ ↔ ∃ t : ℝ, 0 ≤ t ∧ v = (t : F) • u)

def complex_phase_counterexample : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module ℂ V]
    (h : V → V → ℂ), _root_.D05.IsFirstInnerProduct h → ∀ u : V, u ≠ 0 →
    Complex.I • u ≠ 0 ∧ ¬ LinearIndependent ℂ ![u, Complex.I • u] ∧
      _root_.D05.inducedNorm h (u + Complex.I • u) ≠
        _root_.D05.inducedNorm h u + _root_.D05.inducedNorm h (Complex.I • u)

def firstInner_complex_phase_counterexample : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u : V), u ≠ 0 →
    Complex.I • u ≠ 0 ∧ ¬ LinearIndependent ℂ ![u, Complex.I • u] ∧
      ‖u + Complex.I • u‖ ≠ ‖u‖ + ‖Complex.I • u‖

end Specs.D05.M12.NormLaws.TriangleEquality
