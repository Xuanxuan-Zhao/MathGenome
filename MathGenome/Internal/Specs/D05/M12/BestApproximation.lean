import MathGenome.Internal.Specs.D05.M12.Projection
import MathGenome.Internal.Specs.D05.M12.NormLaws

/-!
Independent statements for K05.12.best_approximation, paper.tex:2033–2044.
Only U is finite dimensional; the ambient inner-product space is arbitrary.
The norm is the existing inner-product norm, identified with the manuscript's
square-root norm in K05.12.norm. Projection is the shared ambient endomorphism.
The minimization quantifies over every vector of U, including U = 0.
-/

namespace Specs.D05.M12.BestApproximation

universe u v

/-- Pythagoras for the residual and the error within the subspace. -/
def error_identity : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U]
    (v u : V), u ∈ U →
    ‖v - u‖ ^ 2 = ‖v - _root_.D05.orthogonalProjection U v‖ ^ 2 +
      ‖_root_.D05.orthogonalProjection U v - u‖ ^ 2

/-- The projection attains a distance no larger than any competitor in U. -/
def distance_le : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U]
    (v u : V), u ∈ U →
    ‖v - _root_.D05.orthogonalProjection U v‖ ≤ ‖v - u‖

/-- Equality of distances occurs precisely at the projection. -/
def distance_eq_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U]
    (v u : V), u ∈ U →
    (‖v - u‖ = ‖v - _root_.D05.orthogonalProjection U v‖ ↔
      u = _root_.D05.orthogonalProjection U v)

/-- Exact characterization of minimizers, with subspace membership explicit. -/
def minimizer_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U]
    (v u : V),
    (u ∈ U ∧ ∀ w ∈ U, ‖v - u‖ ≤ ‖v - w‖) ↔
      u = _root_.D05.orthogonalProjection U v

/-- Existence and uniqueness are both asserted, without assuming a minimizer. -/
def exists_unique_minimizer : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U]
    (v : V), ∃! u : V, u ∈ U ∧ ∀ w ∈ U, ‖v - u‖ ≤ ‖v - w‖

end Specs.D05.M12.BestApproximation
