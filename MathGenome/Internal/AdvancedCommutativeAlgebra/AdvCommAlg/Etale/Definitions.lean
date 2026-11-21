import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions

/-! ET-01: étale and unramified algebras, with the finite presentation
and finite type conventions of the source. The canonical predicates are
reused definitionally, so their Mathlib instances remain available.
-/
namespace AdvCommAlg.Etale

universe u v w

open Specs.AdvCommAlg.FormalLifting (propertyType)
open Specs.AdvCommAlg.Etale

/-- Finitely presented and formally étale; the canonical Mathlib predicate. -/
abbrev Etale : propertyType.{u,v} := etaleValue

/-- Finite type and formally unramified; the canonical Mathlib predicate. -/
abbrev Unramified : propertyType.{u,v} := unramifiedValue

/-- Unramified with the additional requirement of finite presentation. -/
def FinitelyPresentedUnramified : propertyType.{u,v} := finitelyPresentedUnramifiedValue

theorem etale_iff : etaleIff.{u,v} := by
  intro A B _ _ _
  change Algebra.Etale A B ↔ _
  rw [Algebra.etale_iff, ← FormalLifting.formallyEtale_iff A B]
  exact and_comm

theorem unramified_iff : unramifiedIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h
    exact ⟨h.finiteType, (FormalLifting.formallyUnramified_iff A B).mpr
      h.formallyUnramified⟩
  · rintro ⟨hfin, hformal⟩
    exact ⟨(FormalLifting.formallyUnramified_iff A B).mp hformal, hfin⟩

theorem finitelyPresentedUnramified_iff : finitelyPresentedUnramifiedIff.{u,v} := by
  intro A B _ _ _
  constructor
  · rintro ⟨hfin, hunr⟩
    exact ⟨hfin, ((unramified_iff A B).mp hunr).2⟩
  · rintro ⟨hfin, hformal⟩
    let := hfin
    exact ⟨hfin, (unramified_iff A B).mpr ⟨inferInstance, hformal⟩⟩

theorem finitelyPresentedUnramified_implies_unramified :
    finitelyPresentedUnramifiedImpliesUnramified.{u,v} := by
  intro A B _ _ _ h
  exact h.2

theorem etale_reduction_bijective : etaleReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  exact FormalLifting.etale_reduction_bijective ((etale_iff A B).mp h).2 N hN

theorem unramified_reduction_injective : unramifiedReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  exact FormalLifting.unramified_reduction_injective ((unramified_iff A B).mp h).2 N hN

end AdvCommAlg.Etale
