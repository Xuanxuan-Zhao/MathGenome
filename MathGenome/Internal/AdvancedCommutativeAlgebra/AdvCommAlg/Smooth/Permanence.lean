import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Permanence

/-! SM-06: composition, arbitrary base change, and principal localization
for smooth algebras. Smoothness is the canonical predicate identified with
finite presentation and square-zero lifting in SM-01.
-/
namespace AdvCommAlg.Smooth

universe u v w

open scoped TensorProduct
open Specs.AdvCommAlg.Smooth.Permanence

/-- The composite of two smooth algebra maps is smooth. -/
theorem smooth_composition : smoothComposition.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hAB hBC
  let : Algebra.Smooth A B := hAB
  let : Algebra.Smooth B C := hBC
  exact Algebra.Smooth.comp A B C

/-- Smoothness is preserved by arbitrary base change. -/
theorem smooth_base_change : smoothBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ hAB
  let : Algebra.Smooth A B := hAB
  exact Algebra.Smooth.baseChange A B A'

/-- Principal localization of a smooth algebra remains smooth. -/
theorem smooth_target_localization : smoothTargetLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ _ _ g _ hAB
  let : Algebra.Smooth A B := hAB
  let : Algebra.Smooth B L := Algebra.Smooth.of_isLocalization_Away g
  exact Algebra.Smooth.comp A B L

/-- A base element already invertible in the smooth algebra can be inverted
in the base, using the induced localized-base action. -/
theorem smooth_source_localization : smoothSourceLocalization.{u,v,w} := by
  intro A B L _ _ _ _ _ a _ ha
  let : Algebra L B := (IsLocalization.Away.lift (S := L) a ha).toAlgebra
  let : IsScalarTower A L B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp a ha).symm
  intro hAB
  let : Algebra.Smooth A B := hAB
  let : Algebra.Smooth A L := Algebra.Smooth.of_isLocalization_Away a
  let : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers a)
  exact
    { formallySmooth := Algebra.FormallySmooth.of_restrictScalars A L B
      finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
        A L B }

end AdvCommAlg.Smooth
