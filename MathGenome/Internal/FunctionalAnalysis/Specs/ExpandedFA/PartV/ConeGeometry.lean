import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic

/-! Independent statement of `paper.tex`, fa2:p5:cone-geometry.
The space is real Hilbert, with its given norm and topology. The separator
is required to be an actual point of D. No boundedness or dimensional
restriction is imposed on D or the space. -/

open scoped InnerProductSpace

namespace ExpandedFA.PartV.ConeGeometry.Spec
universe u

def InteriorPointSeparation : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (D : Set H) (x₀ : H), D.Nonempty → IsOpen D → Convex ℝ D → x₀ ∉ D →
    ∃ w₀ ∈ D, ∀ w ∈ D, 0 < ⟪w₀ - x₀, w - x₀⟫_ℝ

end ExpandedFA.PartV.ConeGeometry.Spec
