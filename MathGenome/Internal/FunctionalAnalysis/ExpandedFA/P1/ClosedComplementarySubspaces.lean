import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ClosedComplementarySubspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02TopologicalSum
import Mathlib.Analysis.Normed.Module.Complemented

/-!
Closed complementary subspaces of a Banach space, paper.tex 570–577.
The library theorem uses completeness of both closed summands and the bounded
inverse theorem for their addition map. Its conclusion is the same native
topological-complement predicate identified in the accepted Chapter 2 interface.
-/

namespace ExpandedFA.P1.ClosedComplementarySubspaces

universe u v

theorem closed_complementary_banach_subspaces : Spec.TopologicalSum.{u, v} := by
  intro 𝕜 E _ _ _ _ M N hM hN h
  exact Submodule.IsCompl.isTopCompl_of_isClosed h hM hN

theorem closed_complementary_coordinate_bounds : Spec.CoordinateBounds.{u, v} := by
  intro 𝕜 E _ _ _ _ M N hM hN h
  have htop := closed_complementary_banach_subspaces 𝕜 E M N hM hN h
  exact ExpandedFA.P1.C02TopologicalSum.coordinate_bounds 𝕜 E M N htop

theorem closed_complementary_addition_equivalence : Spec.AdditionEquivalence.{u, v} := by
  intro 𝕜 E _ _ _ _ M N hM hN h
  have htop := closed_complementary_banach_subspaces 𝕜 E M N hM hN h
  refine ⟨M.prodEquivOfIsTopCompl N htop, ?_, ?_⟩
  · intro z
    rfl
  · intro x
    exact Submodule.prodEquivOfIsCompl_symm_apply h x

end ExpandedFA.P1.ClosedComplementarySubspaces
