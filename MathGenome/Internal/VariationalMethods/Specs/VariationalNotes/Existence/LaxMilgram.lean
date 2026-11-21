import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Independent statement of paper.tex, §v03-07 (lines 1651–1692), using the
conjugate-linear unknown / linear test convention fixed in the preamble.
Bundled continuous forms express bounded sesquilinear forms; over ℝ these
are continuous bilinear forms. No symmetry, nontriviality or dimension
assumption is imposed on solvability or its quantitative estimate.
-/
noncomputable section
open scoped ComplexConjugate
universe u v
namespace VariationalNotes.Existence.Specs

/-- The real energy; for a Hermitian form the diagonal itself is real. -/
def laxMilgramEnergy {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ℓ : H →L[𝕜] 𝕜) (w : H) : ℝ :=
  RCLike.re (a w w) / 2 - RCLike.re (ℓ w)

/-- Real and complex Lax–Milgram, including the norm estimate, and, under
symmetry, both directions of the energy characterization and uniqueness
among all global minimizers. The same statement includes the zero space. -/
def laxMilgram : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (α : ℝ),
    0 < α → (∀ w : H, α * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) →
    ∀ ℓ : H →L[𝕜] 𝕜,
      ∃ u : H, (∀ v : H, a u v = ℓ v) ∧ ‖u‖ ≤ ‖ℓ‖ / α ∧
        (∀ w : H, (∀ v : H, a w v = ℓ v) → w = u) ∧
        ((∀ x y : H, a x y = conj (a y x)) →
          (∀ v : H, a v v = (RCLike.re (a v v) : 𝕜)) ∧
          (∀ w : H, (∀ v : H, a w v = ℓ v) ↔
            ∀ v : H, laxMilgramEnergy a ℓ w ≤ laxMilgramEnergy a ℓ v) ∧
          ∃! w : H, ∀ v : H, laxMilgramEnergy a ℓ w ≤ laxMilgramEnergy a ℓ v)

end VariationalNotes.Existence.Specs
