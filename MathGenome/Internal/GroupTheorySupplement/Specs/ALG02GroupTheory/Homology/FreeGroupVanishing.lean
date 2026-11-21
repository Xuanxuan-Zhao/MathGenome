import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.IntegralBar
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

universe u

namespace ALG02GroupTheory.IntegralBar.Spec

/-- A free discrete group on any basis has zero second integral homology. -/
def FreeGroupH2Vanishing : Prop :=
  ∀ (F : Type u) [Group F] [IsFreeGroup F], CategoryTheory.Limits.IsZero (homology F 2)

end ALG02GroupTheory.IntegralBar.Spec
