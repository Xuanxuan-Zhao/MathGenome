import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedKModels

/-!
HA-R03. Mathlib's bounded-model theorems use strict support (zero terms outside
the bound) and termwise injectivity/projectivity. Their K-model classes mean
null-homotopy against every acyclic integer cochain complex. We identify these
classes with the explicit predicates, then translate the term bounds.
-/

open CategoryTheory CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.BoundedKModels

namespace AdvancedHomologicalAlgebra.BoundedKModels

def kInjective :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.kInjectiveType :=
  fun _A _ _ => KInjective

def kProjective :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.kProjectiveType :=
  fun _A _ _ => KProjective

theorem kInjective_iff :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.kInjective_iffType := by
  intro A _ _ I
  constructor
  · intro h
    exact ⟨fun {C} f hC => h C f hC⟩
  · intro h C f hC
    exact h.nonempty_homotopy_zero f hC

theorem kProjective_iff :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.kProjective_iffType := by
  intro A _ _ P
  constructor
  · intro h
    exact ⟨fun {C} f hC => h C f hC⟩
  · intro h C f hC
    exact h.nonempty_homotopy_zero f hC

theorem boundedBelow_injective :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.boundedBelow_injectiveType := by
  intro A _ _ I b hbound hinj
  let : I.IsStrictlyGE b := (I.isStrictlyGE_iff b).mpr hbound
  let : ∀ n : ℤ, Injective (I.X n) := hinj
  exact (kInjective_iff A I).mpr (CochainComplex.isKInjective_of_injective I b)

theorem boundedAbove_projective :
    Specs.AdvancedHomologicalAlgebra.BoundedKModels.boundedAbove_projectiveType := by
  intro A _ _ P b hbound hproj
  let : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).mpr hbound
  let : ∀ n : ℤ, Projective (P.X n) := hproj
  exact (kProjective_iff A P).mpr (CochainComplex.isKProjective_of_projective P b)

end AdvancedHomologicalAlgebra.BoundedKModels
