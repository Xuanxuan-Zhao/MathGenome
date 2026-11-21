import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.FiniteCoverLocality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.TargetLocality
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-! Target locality of smoothness, SM-07 (first assertion).

First descend finite presentation by Mathlib's target-locality theorem,
which first descends finite type and then finite generation of the kernel
of a finite polynomial presentation. Only after this step do we invoke
FL-10 to descend the square-zero lifting property. Neither step assumes
that the cover is nonempty or that either ring is nonzero. -/
namespace AdvCommAlg.Smooth

universe u v

theorem smooth_of_finite_principal_cover :
    Specs.AdvCommAlg.Smooth.smoothTargetLocality.{u,v} := by
  intro A B _ _ _ n g hspan h
  have hfp : Algebra.FinitePresentation A B := by
    apply Algebra.FinitePresentation.of_span_eq_top_target (Set.range g) hspan
    rintro _ ⟨i, rfl⟩
    exact ((smooth_iff A (Localization.Away (g i))).mp (h i)).1
  let : Algebra.FinitePresentation A B := hfp
  apply (smooth_iff A B).mpr
  refine ⟨hfp, ?_⟩
  apply (FormalLifting.FiniteCoverLocality.formallySmooth_iff_finite_principal_cover
    A B n g hspan).mpr
  intro i
  exact ((smooth_iff A (Localization.Away (g i))).mp (h i)).2

end AdvCommAlg.Smooth
