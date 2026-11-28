import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.NonSplitExtension

/-! The untwisted affine central extension does not split. -/

noncomputable section

universe u

namespace RepTheorySurvey.Affine

open LieAlgebra LieModule

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- The central scalar line is the kernel of the surjective Lie projection to loops. -/
theorem loopCentral_isCentralExtension (B : InvariantForm G) :
    IsExtension (centralExtension B).incl (centralExtension B).proj ∧
      ∀ (k : ScalarLine G) (x : LoopCentral B),
        let z : LoopCentral B := (centralExtension B).incl k
        ⁅z, x⁆ = 0 :=
  ⟨(centralExtension B).IsExtension, centralExtension_central B⟩

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
  (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]

/-- A pair of opposite-degree Cartan loops commutes in the loop algebra but has
a prescribed nonzero bracket in every pair of lifts. -/
theorem cartanLoopLiftBracket (B : InvariantForm G) (hB : B.IsNormalized H) :
    ∃ h h' : H, B.form (h : G) (h' : G) ≠ 0 ∧
      ⁅loopVector 1 (h : G), loopVector (-1) (h' : G)⁆ = 0 ∧
      ∀ x y : LoopCentral B,
        (centralExtension B).proj x = loopVector 1 (h : G) →
        (centralExtension B).proj y = loopVector (-1) (h' : G) →
        ⁅x, y⁆ = B.form (h : G) (h' : G) • centralLineIncl B 1 ∧ ⁅x, y⁆ ≠ 0 := by
  let : Nontrivial H := cartanNontrivial H
  let : IsLieAbelian H := cartanAbelian H
  obtain ⟨h, hh⟩ := exists_ne (0 : H)
  obtain ⟨h', hh'⟩ : ∃ h' : H, B.form (h : G) (h' : G) ≠ 0 := by
    by_contra! hzero
    exact hh ((cartanNondegenerate H B hB.1).1 h hzero)
  have hCartan : ⁅(h : G), (h' : G)⁆ = 0 :=
    congrArg Subtype.val (trivial_lie_zero H H h h')
  have hCanonical :
      ⁅centralLoopIncl B (loopVector 1 (h : G)),
        centralLoopIncl B (loopVector (-1) (h' : G))⁆ =
        B.form (h : G) (h' : G) • centralLineIncl B 1 := by
    rw [centralBracket, hCartan]
    simp
  have hGenerator : centralLineIncl B 1 ≠ 0 := by
    intro hz
    have hcoord := congrArg (fun z : LoopCentral B ↦ (centralCoordinates B z).2) hz
    change (centralCoordinates B ((centralCoordinates B).symm (0, 1))).2 =
      (centralCoordinates B 0).2 at hcoord
    exact one_ne_zero (by
      simpa only [LinearEquiv.apply_symm_apply, map_zero, Prod.snd_zero] using hcoord)
  refine ⟨h, h', hh', by simp [hCartan], ?_⟩
  intro x y hx hy
  have hBracket : ⁅x, y⁆ =
      ⁅centralLoopIncl B (loopVector 1 (h : G)),
        centralLoopIncl B (loopVector (-1) (h' : G))⁆ := by
    apply (centralCoordinates B).injective
    rw [centralExtension_proj_coordinates] at hx hy
    simp only [centralBracket_coordinates, centralLoopIncl_coordinates, hx, hy]
    rfl
  have hLift := hBracket.trans hCanonical
  refine ⟨hLift, ?_⟩
  rw [hLift]
  exact smul_ne_zero hh' hGenerator

/-- No section of the loop projection can preserve the Lie bracket. -/
theorem centralExtension_nonsplit (B : InvariantForm G) (hB : B.IsNormalized H) :
    ¬ ∃ s : Loop G →ₗ⁅ℂ⁆ LoopCentral B, ∀ f : Loop G, (centralExtension B).proj (s f) = f := by
  rintro ⟨s, hs⟩
  obtain ⟨h, h', _, hComm, hLifts⟩ := cartanLoopLiftBracket H B hB
  have hZero : ⁅s (loopVector 1 (h : G)), s (loopVector (-1) (h' : G))⁆ = 0 := by
    rw [← s.map_lie, hComm, map_zero]
  exact (hLifts _ _ (hs _) (hs _)).2 hZero

end RepTheorySurvey.Affine
