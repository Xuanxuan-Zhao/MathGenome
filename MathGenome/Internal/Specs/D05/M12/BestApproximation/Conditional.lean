import MathGenome.Internal.Specs.D05.M12.NormLaws
import MathGenome.Internal.Specs.D05.M12.OrthogonalComplement

/-!
Independent statements for the conditional nearest-point theorem,
K05.12.best_approximation, paper.tex:2044–2054.

The norm is the existing inner-product norm, and `U.orthogonal` is the shared
complement defined by `D05.firstInner r z = inner F z r = 0` for every `z ∈ U`.
The criterion and uniqueness have no finite-dimensional, closedness, or
completeness premise. Only the final existence statement assumes that `U`
is finite dimensional; the ambient space remains arbitrary.
-/

namespace Specs.D05.M12.BestApproximation.Conditional

universe u v

/-- A point of an arbitrary subspace is nearest exactly when its residual is
orthogonal to the whole subspace. Minimality compares against every member. -/
def minimizes_iff_mem_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v u₀ : V), u₀ ∈ U →
      ((∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖) ↔ v - u₀ ∈ U.orthogonal)

/-- The same criterion written in the manuscript's first-slot-linear notation. -/
def minimizes_iff_firstInner_eq_zero : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v u₀ : V), u₀ ∈ U →
      ((∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖) ↔
        ∀ z ∈ U, _root_.D05.firstInner (F := F) (v - u₀) z = 0)

/-- Pythagoras for any orthogonal residual, including all zero cases. -/
def squared_distance_decomposition : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v u₀ : V), u₀ ∈ U →
      v - u₀ ∈ U.orthogonal → ∀ u ∈ U,
        ‖v - u‖ ^ 2 = ‖v - u₀‖ ^ 2 + ‖u₀ - u‖ ^ 2

/-- Any two minimizers in an arbitrary subspace coincide. -/
def minimizer_unique : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v u₀ u₁ : V),
      u₀ ∈ U → u₁ ∈ U →
      (∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖) →
      (∀ u ∈ U, ‖v - u₁‖ ≤ ‖v - u‖) → u₀ = u₁

/-- Existence, when given, entails existence of exactly one minimizer. -/
def existsUnique_of_exists : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) (v : V),
      (∃ u₀ ∈ U, ∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖) →
      ∃! u₀ : V, u₀ ∈ U ∧ ∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖

/-- A finite-dimensional subspace has a unique minimizer for every vector,
without any dimension or completeness assumption on the ambient space. -/
def finite_dimensional_existsUnique : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U] (v : V),
      ∃! u₀ : V, u₀ ∈ U ∧ ∀ u ∈ U, ‖v - u₀‖ ≤ ‖v - u‖

end Specs.D05.M12.BestApproximation.Conditional
