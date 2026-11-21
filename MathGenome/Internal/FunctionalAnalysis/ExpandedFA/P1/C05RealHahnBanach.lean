import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Sublinear
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05RealHahnBanach
import Mathlib.Analysis.Convex.Cone.Extension

/-!
Real analytic Hahn–Banach, `paper.tex:862–867`,
label `fa2:p1:c05:real-hahn-banach`.

Mathlib's algebraic extension theorem requires subadditivity and positive
homogeneity for strictly positive real scalars. The manuscript's homogeneity
for nonnegative scalars supplies this condition. A partial linear map packages
the given subspace and functional without changing either of them.
-/

universe u

namespace ExpandedFA.P1

/-- A real linear functional dominated by a finite sublinear function on an
arbitrary subspace extends to the whole space with the same domination. -/
theorem real_hahn_banach {E : Type u} [AddCommGroup E] [Module ℝ E]
    (M : Submodule ℝ E) (p : E → ℝ) (hp : IsSublinear p)
    (f : M →ₗ[ℝ] ℝ) (hf : ∀ m : M, f m ≤ p (m : E)) :
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ m : M, F (m : E) = f m) ∧ (∀ x : E, F x ≤ p x) := by
  exact exists_extension_of_le_sublinear (LinearPMap.mk M f) p
    (fun t ht x => hp.2 t ht.le x) hp.1 hf

end ExpandedFA.P1
