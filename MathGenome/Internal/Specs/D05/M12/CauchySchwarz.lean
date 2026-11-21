import MathGenome.Internal.Specs.D05.M12.Norm
import MathGenome.Internal.Specs.D05.M02.Independence

/-!
Independent statements for K05.12.cauchy_schwarz, paper.tex:1902–1913.
The main statements use precisely the shared algebraic inner-product axioms
and their induced norm. The final statements express the same conclusions in
Mathlib inner-product spaces, using the shared first-slot-linear convention.
The two-vector list is indexed by `Fin 2`, retaining zero and repeated entries.
No finite-dimensional or completeness hypothesis is imposed.
-/

namespace Specs.D05.M12.CauchySchwarz

universe u v

/-- Cauchy–Schwarz for a form satisfying the manuscript's inner-product axioms. -/
def cauchy_schwarz : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    ‖h u v‖ ≤ _root_.D05.inducedNorm h u * _root_.D05.inducedNorm h v

/-- Equality is exactly dependence of the indexed pair, including zero vectors. -/
def equality_iff_dependent : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v,
    (‖h u v‖ = _root_.D05.inducedNorm h u * _root_.D05.inducedNorm h v ↔
      ¬ LinearIndependent F ![u, v])

/-- The inequality for the shared convention `h u v = inner F v u`. -/
def firstInner_cauchy_schwarz : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    ‖_root_.D05.firstInner (F := F) u v‖ ≤ ‖u‖ * ‖v‖

/-- The exact equality case in a Mathlib inner-product space. -/
def firstInner_equality_iff_dependent : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    (‖_root_.D05.firstInner (F := F) u v‖ = ‖u‖ * ‖v‖ ↔
      ¬ LinearIndependent F ![u, v])

end Specs.D05.M12.CauchySchwarz
