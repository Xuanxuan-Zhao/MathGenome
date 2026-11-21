import Mathlib.Analysis.Normed.Affine.Isometry

/-!
Independent statements of Mazur--Ulam, paper.tex:6391–6396.
The spaces are real normed spaces, with no completeness, finite-dimensionality,
or nontriviality assumption. The hypotheses concern an arbitrary function.
Being affine (respectively linear) means agreeing everywhere with an affine
map (respectively a real linear map).
-/

namespace ExpandedFA.Supplements.MazurUlamSpec

universe u v

/-- Every surjective isometry of real normed spaces is affine. -/
def AffineConclusion : Prop :=
  ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E → F),
    Isometry T → Function.Surjective T →
      ∃ A : E →ᵃ[ℝ] F, ∀ x : E, A x = T x

/-- If the surjective isometry fixes zero, it is real linear. -/
def LinearConclusion : Prop :=
  ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E → F),
    Isometry T → Function.Surjective T → T 0 = 0 →
      ∃ L : E →ₗ[ℝ] F, ∀ x : E, L x = T x

end ExpandedFA.Supplements.MazurUlamSpec
