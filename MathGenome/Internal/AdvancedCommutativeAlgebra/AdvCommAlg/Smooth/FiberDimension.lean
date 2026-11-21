import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.GeometricClosedPointRegularity
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.FiberDimension
import Mathlib.RingTheory.Ideal.Height

/-! Dimension of a nonzero standard smooth field fiber (SM-12).
The upstream closed-point calculation works over any field, so the global
dimension follows directly by bounding the heights of maximal ideals. -/
namespace AdvCommAlg.Smooth

universe u v w z
noncomputable section
open scoped TensorProduct

/-- A nonzero ring whose maximal local rings have constant dimension has
that global dimension. Nonzeroness supplies a maximal ideal for the lower bound.
-/
theorem ringKrullDim_eq_of_maximal_localizations
    {R : Type u} [CommRing R] [Nontrivial R] (d : WithBot ℕ∞)
    (h : ∀ (m : Ideal R) (hm : m.IsMaximal),
      letI : m.IsPrime := hm.isPrime
      ringKrullDim (Localization.AtPrime m) = d) :
    ringKrullDim R = d := by
  have height_eq (m : Ideal R) (hm : m.IsMaximal) :
      (m.height : WithBot ℕ∞) = d := by
    letI : m.IsPrime := hm.isPrime
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
    exact h m hm
  apply le_antisymm
  · exact (ringKrullDim_le_iff_isMaximal_height_le d).mpr
      (fun m hm => (height_eq m hm).le)
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal R
    rw [← height_eq m hm]
    exact m.height_le_ringKrullDim_of_ne_top hm.ne_top

theorem standard_smooth_fiber_dimension :
    Specs.AdvCommAlg.Smooth.standardSmoothFiberDimension.{u,v,w} := by
  intro A B F _ _ _ _ _ n c P hP hnonzero
  letI := hnonzero
  apply ringKrullDim_eq_of_maximal_localizations
  intro m hm
  exact (standard_smooth_closed_point_regularity (P.baseChange F)
    (base_change_presentation P hP).1 m hm).2

theorem standard_smooth_geometric_fiber :
    Specs.AdvCommAlg.Smooth.standardSmoothGeometricFiber.{u,v,w,z} := by
  exact @geometric_closed_point_regularity.{u,v,w,z}

end
end AdvCommAlg.Smooth
