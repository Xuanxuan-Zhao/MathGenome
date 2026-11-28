import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.LoopAlgebra

/-! The short exact sequence and nonsplitting assertion in LO09. -/

noncomputable section

universe u

namespace Specs.RepTheorySurvey.Affine.NonSplitExtension

open _root_.RepTheorySurvey.Affine
open LieAlgebra Specs.RepTheorySurvey.Affine.LoopAlgebra

/-- The central scalar inclusion and loop projection form a central Lie extension. -/
def loopCentral_isCentralExtension_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    IsExtension (centralExtension_value B).incl (centralExtension_value B).proj ∧
      ∀ (k : ScalarLine G) (x : LoopCentral B),
        let z : LoopCentral B := (centralExtension_value B).incl k
        ⁅z, x⁆ = 0

/-- For an appropriate Cartan pair, every lift of the commuting loops in degrees
one and minus one has the same nonzero central bracket. -/
def cartanLoopLiftBracket_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G), B.IsNormalized H →
      ∃ h h' : H, B.form (h : G) (h' : G) ≠ 0 ∧
        ⁅loopVector_value 1 (h : G), loopVector_value (-1) (h' : G)⁆ = 0 ∧
        ∀ x y : LoopCentral B,
          (centralExtension_value B).proj x = loopVector_value 1 (h : G) →
          (centralExtension_value B).proj y = loopVector_value (-1) (h' : G) →
          ⁅x, y⁆ = B.form (h : G) (h' : G) • centralLineIncl_value B 1 ∧ ⁅x, y⁆ ≠ 0

/-- The projection of the central extension has no complex Lie algebra section. -/
def centralExtension_nonsplit_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
    [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G), B.IsNormalized H →
      ¬ ∃ s : Loop G →ₗ⁅ℂ⁆ LoopCentral B, ∀ f : Loop G, (centralExtension_value B).proj (s f) = f

end Specs.RepTheorySurvey.Affine.NonSplitExtension
