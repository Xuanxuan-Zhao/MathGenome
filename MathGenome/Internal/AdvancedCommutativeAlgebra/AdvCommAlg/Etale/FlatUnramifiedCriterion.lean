import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.DifferentialCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Flatness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FlatUnramifiedCriterion
import Mathlib.RingTheory.Smooth.Fiber

/-! The flat unramified criterion (ET-12).
The converse uses Mathlib's flat, finitely presented, formally unramified
criterion, after identifying formal unramifiedness with vanishing of Ω.
-/
namespace AdvCommAlg.Etale

universe u v

/-- Over any commutative base, étaleness is equivalent to finite
presentation, flatness, and vanishing of relative Kähler differentials. -/
theorem etale_iff_finitePresentation_flat_subsingleton_omega :
    Specs.AdvCommAlg.Etale.etaleIffFinitePresentationFlatOmega.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h
    obtain ⟨hsm, hΩ⟩ := (etale_iff_smooth_and_subsingleton_omega A B).mp h
    exact ⟨((etale_iff A B).mp h).1, Smooth.flat A B hsm, hΩ⟩
  · rintro ⟨hfp, hflat, hΩ⟩
    letI : Algebra.FinitePresentation A B := hfp
    letI : Module.Flat A B := hflat
    have hunr : FormalLifting.FormallyUnramified A B :=
      (FormalLifting.formallyUnramified_iff_subsingleton_omega A B).mpr hΩ
    letI : Algebra.FormallyUnramified A B :=
      (FormalLifting.formallyUnramified_iff A B).mp hunr
    exact Algebra.Etale.of_formallyUnramified_of_flat (R := A) (S := B)

end AdvCommAlg.Etale
