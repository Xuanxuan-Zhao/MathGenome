import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.EtaleCriterion

/-! FL-11, first assertion: existence and uniqueness of square-zero lifts
are equivalent to existence and vanishing of relative differentials. -/
namespace AdvCommAlg.FormalLifting

universe u v

/-- The square-zero lifting criterion for formal étaleness, without any
finite presentation hypothesis. -/
theorem formallyEtale_iff_formallySmooth_and_subsingleton_omega
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    FormallyEtale A B ↔
      FormallySmooth A B ∧ Subsingleton (Differentials.Omega A B) := by
  constructor
  · intro h
    have hs : FormallySmooth A B := fun N hN => (h N hN).2
    have hu : FormallyUnramified A B := fun N hN => (h N hN).1
    exact ⟨hs, (formallyUnramified_iff_subsingleton_omega A B).mp hu⟩
  · rintro ⟨hs, hΩ⟩
    have hu : FormallyUnramified A B :=
      (formallyUnramified_iff_subsingleton_omega A B).mpr hΩ
    intro C _ _ N hN
    exact ⟨hu N hN, hs N hN⟩

end AdvCommAlg.FormalLifting
