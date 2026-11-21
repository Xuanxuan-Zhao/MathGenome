import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.TargetLocality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.FiniteProducts
import Mathlib.RingTheory.Smooth.Pi

/-! SM-14: smoothness of finite products, including the zero algebra. -/
namespace AdvCommAlg.Smooth

universe u v w

/-- Smoothness of a finite product is equivalent to smoothness of every factor. -/
theorem smooth_finite_products :
    Specs.AdvCommAlg.Smooth.smoothFiniteProducts.{u,v,w} := by
  intro A T B _ _ _ _
  classical
  constructor
  · intro h t
    let : Algebra.Smooth A (∀ t, B t) := h
    let : Algebra (∀ t, B t) (B t) := (Pi.evalAlgHom A B t).toAlgebra
    let : IsLocalization.Away (Pi.single t 1 : ∀ t, B t) (B t) := by
      refine IsLocalization.away_of_isIdempotentElem ?_
        (RingHom.ker_evalRingHom _ _) ((Pi.evalRingHom B t).surjective)
      simp [IsIdempotentElem, ← Pi.single_mul_left]
    exact smooth_target_localization A (∀ t, B t) (B t) (Pi.single t 1) h
  · intro h
    let (t : T) : Algebra.Smooth A (B t) := h t
    exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

/-- There is no nonemptiness hypothesis: in particular the empty product is smooth. -/
theorem smooth_empty_product :
    Specs.AdvCommAlg.Smooth.smoothEmptyProduct.{u,v,w} := by
  intro A T B _ _ _ _
  exact (smooth_finite_products A T B).mpr (fun t => isEmptyElim t)

/-- Every zero algebra is smooth, as follows from the empty principal cover. -/
theorem smooth_zero_algebra :
    Specs.AdvCommAlg.Smooth.smoothZeroAlgebra.{u,v} := by
  intro A B _ _ _ _
  apply smooth_of_finite_principal_cover A B 0 (fun i => Fin.elim0 i)
  · exact Subsingleton.elim _ _
  · intro i
    exact Fin.elim0 i

end AdvCommAlg.Smooth
