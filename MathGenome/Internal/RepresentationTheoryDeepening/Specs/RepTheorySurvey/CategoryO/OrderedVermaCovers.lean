import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveFiltrations

/-! Projective covers of simples with ordered Verma flags in finite category O. -/

noncomputable section

open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open scoped Classical

namespace Specs.RepTheorySurvey.CategoryO.OrderedVermaCovers

open ComponentProjectors (component)
open ProjectiveCovers (IsComponentBound IsIndecomposable projectedModule
  projectiveCover_value simpleIndex)
open RepTheorySurvey.CategoryO.ProjectiveFiltrations (VermaFlag componentTerm)
open RepTheorySurvey.CategoryO.TruncatedProjectives (GroupedFiltration P)

universe u

/-- Each simple has a cover in the whole category O. Its flag refines the
images of the grouped truncated flag in the indicated component summand. -/
def ExistenceType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (μ : D.Weight),
    let k := simpleIndex D μ
    ∃ (Λ : D.Weight) (_ : IsComponentBound D k Λ) (_ : weightLE_value D μ Λ)
      (hP : DirectSum.IsInternal (component D (P D μ Λ)))
      (p₀ : projectedModule D k μ Λ →ₗ[U g] simpleQuotient_value D μ)
      (S T : Submodule (U g) (projectedModule D k μ Λ))
      (hST : IsCompl S T) (hS : objects_value D (ModuleCat.of (U g) S))
      (_ : objects_value D (simpleQuotient_value D μ))
      (F : GroupedFiltration D μ Λ) (r : Fin F.length → ℕ),
      IsIndecomposable (ModuleCat.of (U g) S) ∧
      projectiveCover_value (⟨ModuleCat.of (U g) S, hS⟩ : category_value.{u, u} D)
        (p₀.domRestrict S) ∧
      let term i := (componentTerm D F hP k i).map (S.projectionOnto T hST)
      let weights := (List.ofFn (fun i => List.replicate (r i) (F.weight i))).flatten
      Monotone term ∧ term 0 = ⊥ ∧ term (Fin.last F.length) = ⊤ ∧
      (∀ i, VermaFlag D (List.replicate (r i) (F.weight i)) (term i.castSucc) (term i.succ)) ∧
      VermaFlag D (X := S) weights ⊥ ⊤ ∧
      weights.Pairwise (fun ν ξ => weightLE_value D ν ξ → ν = ξ)

/-- Every cover of the same simple has a finite Verma flag with larger
comparable highest weights preceding smaller ones. -/
def FlagOfCoverType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (μ : D.Weight) (X : category_value.{u, u} D)
    (p : X.obj →ₗ[U g] simpleQuotient_value D μ),
    projectiveCover_value X p →
    ∃ weights : List D.Weight,
      VermaFlag D (X := X.obj) weights ⊥ ⊤ ∧
      weights.Pairwise (fun ν ξ => weightLE_value D ν ξ → ν = ξ)

end Specs.RepTheorySurvey.CategoryO.OrderedVermaCovers
