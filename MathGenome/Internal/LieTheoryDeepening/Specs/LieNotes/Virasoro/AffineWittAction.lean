import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroCocycle
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.LoopAlgebra
import Mathlib.Algebra.Lie.SemiDirect

/-! The Witt action on the loop-central extension in Proposition KM12. -/

noncomputable section

namespace LieNotes.Virasoro.AffineWittSpec

open RepTheorySurvey.Affine
open Specs.RepTheorySurvey.Affine.LoopAlgebra

universe u

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The lift of a homogeneous loop to the extension before adjoining the degree line. -/
abbrev homogeneous (B : InvariantForm G) (i : ℤ) (x : G) : LoopCentral B :=
  centralLoopIncl_value B (loopVector_value i x)

/-- The Witt action extends the Laurent vector fields and negates the LO09 degree operator
at index zero. -/
def WittActionLifts (B : InvariantForm G)
    (ρ : WittSpec.Witt →ₗ⁅ℂ⁆ LieDerivation ℂ (LoopCentral B) (LoopCentral B)) : Prop :=
  (∀ m i : ℤ, ∀ x : G, ρ (WittSpec.mode m) (homogeneous B i x) =
    (-(i : ℂ)) • homogeneous B (m + i) x) ∧
  (∀ D : WittSpec.Witt, ∀ k : ℂ, ρ D (centralLineIncl_value B k) = 0) ∧
  (ρ (WittSpec.mode 0)).toLinearMap = -degreeCentral_value B

/-- The lift and its semidirect product with the canonical Virasoro extension.
The construction works for all invariant symmetric forms, including every
normalized finite-dimensional simple loop model used in KM09. -/
def LiftToAffineCentralExtension : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    ∃ ρ : WittSpec.Witt →ₗ⁅ℂ⁆ LieDerivation ℂ (LoopCentral B) (LoopCentral B),
      WittActionLifts B ρ ∧
      ∃ r : LieRing VirasoroSpec.Vir, ∃ a : @LieAlgebra ℂ VirasoroSpec.Vir _ r,
        r.toAddCommGroup = (inferInstance : AddCommGroup VirasoroSpec.Vir) ∧
        HEq a.toModule (inferInstance : Module ℂ VirasoroSpec.Vir) ∧
        letI : LieRing VirasoroSpec.Vir := r
        letI : LieAlgebra ℂ VirasoroSpec.Vir := a
        ∃ p : VirasoroSpec.Vir →ₗ⁅ℂ⁆ WittSpec.Witt,
          (∀ v, p v = (VirasoroSpec.coordinates v).1) ∧
          (∀ v w : VirasoroSpec.Vir, ⁅v, w⁆ = VirasoroSpec.bracket v w) ∧
          ∃ ψ : VirasoroSpec.Vir →ₗ⁅ℂ⁆ LieDerivation ℂ (LoopCentral B) (LoopCentral B),
            ψ = ρ.comp p ∧
            ∀ U V : LieAlgebra.SemiDirectSum (LoopCentral B) VirasoroSpec.Vir ψ,
              ⁅U, V⁆ =
                ⟨⁅U.left, V.left⁆ + ρ (p U.right) V.left - ρ (p V.right) U.left,
                  VirasoroSpec.bracket U.right V.right⟩

end LieNotes.Virasoro.AffineWittSpec
