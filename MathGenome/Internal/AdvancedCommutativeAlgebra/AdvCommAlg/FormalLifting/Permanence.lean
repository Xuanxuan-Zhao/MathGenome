import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Permanence

/-! FL-09: composition, arbitrary base change, and the two intermediate-base
assertions for the square-zero lifting properties. The FL-01 equivalences
transport Mathlib's general permanence results to the lifting definitions.
-/
namespace AdvCommAlg.FormalLifting

universe u v w

open scoped TensorProduct

open Specs.AdvCommAlg.FormalLifting.Permanence

/-- Compatible composites of formally smooth maps are formally smooth. -/
theorem smooth_composition : smoothComposition.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hAB hBD
  let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp hAB
  let : Algebra.FormallySmooth B D := (formallySmooth_iff B D).mp hBD
  apply (formallySmooth_iff A D).mpr
  exact Algebra.FormallySmooth.comp A B D

/-- Compatible composites of formally unramified maps are formally unramified. -/
theorem unramified_composition : unramifiedComposition.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hAB hBD
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp hAB
  let : Algebra.FormallyUnramified B D := (formallyUnramified_iff B D).mp hBD
  apply (formallyUnramified_iff A D).mpr
  exact Algebra.FormallyUnramified.comp A B D

/-- Compatible composites of formally étale maps are formally étale. -/
theorem etale_composition : etaleComposition.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hAB hBD
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp hAB
  let : Algebra.FormallyEtale B D := (formallyEtale_iff B D).mp hBD
  apply (formallyEtale_iff A D).mpr
  exact Algebra.FormallyEtale.comp A B D

/-- Formal smoothness survives arbitrary extension of the base ring. -/
theorem smooth_base_change : smoothBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ hAB
  let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp hAB
  apply (formallySmooth_iff A' (A' ⊗[A] B)).mpr
  infer_instance

/-- Formal unramifiedness survives arbitrary extension of the base ring. -/
theorem unramified_base_change : unramifiedBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ hAB
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp hAB
  apply (formallyUnramified_iff A' (A' ⊗[A] B)).mpr
  infer_instance

/-- Formal étaleness survives arbitrary extension of the base ring. -/
theorem etale_base_change : etaleBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ hAB
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp hAB
  apply (formallyEtale_iff A' (A' ⊗[A] B)).mpr
  infer_instance

/-- A formally smooth composite is smooth over an unramified intermediate base. -/
theorem smooth_over_unramified : smoothOverUnramified.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hAB hAD
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp hAB
  let : Algebra.FormallySmooth A D := (formallySmooth_iff A D).mp hAD
  apply (formallySmooth_iff B D).mpr
  exact Algebra.FormallySmooth.of_restrictScalars A B D

/-- A formally unramified composite is unramified over any intermediate base. -/
theorem unramified_over_intermediate : unramifiedOverIntermediate.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ hAD
  let : Algebra.FormallyUnramified A D := (formallyUnramified_iff A D).mp hAD
  apply (formallyUnramified_iff B D).mpr
  exact Algebra.FormallyUnramified.of_restrictScalars A B D

end AdvCommAlg.FormalLifting
