import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Basic

/-!
Independent statements of paper.tex, §v03-06, Theorem thm:stampacchia.
The algebraic bilinear form is unknown-first. Its specified bound M may
be any real number; in particular no positivity assumption on M excludes
the zero Hilbert space. The functional belongs to the continuous dual.
-/

universe u
namespace VariationalNotes.Existence.Specs

/-- Unique solvability of the source's unknown-first variational inequality. -/
def stampacchia_existsUnique : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (M α : ℝ),
      (∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖) →
      0 < α → (∀ v, α * ‖v‖ ^ 2 ≤ a v v) →
      ∀ ℓ : H →L[ℝ] ℝ,
        ∃! u : H, u ∈ C ∧ ∀ v ∈ C, ℓ (v - u) ≤ a u (v - u)

/-- At each feasible point, the symmetric inequality is equivalent to
being a global minimizer of the original quadratic energy on C. -/
def stampacchia_minimization_iff : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (M α : ℝ),
      (∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖) →
      0 < α → (∀ v, α * ‖v‖ ^ 2 ≤ a v v) →
      (∀ u v, a u v = a v u) →
      ∀ (ℓ : H →L[ℝ] ℝ) (u : H), u ∈ C →
        ((∀ v ∈ C, ℓ (v - u) ≤ a u (v - u)) ↔
          ∀ v ∈ C, a u u / 2 - ℓ u ≤ a v v / 2 - ℓ v)

end VariationalNotes.Existence.Specs
