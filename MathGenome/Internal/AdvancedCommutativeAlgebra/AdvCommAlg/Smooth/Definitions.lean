import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions

/-! Smoothness (SM-01): finite presentation together with the square-zero
existence property of FL-01, with an explicit finite polynomial presentation.
-/
namespace AdvCommAlg.Smooth

universe u v w

/-- Smoothness over an arbitrary commutative base, using the canonical
Mathlib predicate. -/
abbrev Smooth : Specs.AdvCommAlg.Smooth.smoothType.{u,v} :=
  fun A B _ _ _ => Algebra.Smooth A B

theorem smooth_iff : Specs.AdvCommAlg.Smooth.smoothIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h
    exact ⟨h.finitePresentation, (FormalLifting.formallySmooth_iff A B).mpr h.formallySmooth⟩
  · rintro ⟨hfp, hfs⟩
    exact ⟨(FormalLifting.formallySmooth_iff A B).mp hfs, hfp⟩

theorem finitePresentation_iff_exists_presentation :
    Specs.AdvCommAlg.Smooth.finitePresentationIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h
    obtain ⟨n, I, e, hI⟩ := Algebra.FinitePresentation.iff.mp h
    obtain ⟨c, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
    refine ⟨n, c, f, ?_⟩
    change Ideal.span (Set.range f) = I at hf
    rw [hf]
    exact ⟨e.symm⟩
  · rintro ⟨n, c, f, ⟨e⟩⟩
    apply Algebra.FinitePresentation.iff.mpr
    exact ⟨n, Ideal.span (Set.range f), e.symm,
      Submodule.fg_iff_exists_fin_generating_family.mpr ⟨c, f, rfl⟩⟩

theorem smooth_iff_presentation_and_lifting :
    Specs.AdvCommAlg.Smooth.smoothPresentationIff.{u,v} := by
  intro A B _ _ _
  rw [smooth_iff A B, finitePresentation_iff_exists_presentation A B]
  rfl

theorem smooth_reduction_surjective :
    Specs.AdvCommAlg.Smooth.smoothReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  exact FormalLifting.smooth_reduction_surjective ((smooth_iff A B).mp h).2 N hN

end AdvCommAlg.Smooth
