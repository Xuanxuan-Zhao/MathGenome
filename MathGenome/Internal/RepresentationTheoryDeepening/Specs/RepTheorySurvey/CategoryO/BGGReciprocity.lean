import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ProjectiveFiltrations
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RestrictedDual
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Dimension.Finite

/-! BGG reciprocity for the finite category O. -/

noncomputable section

open CategoryTheory
open scoped Classical ModuleCat.Algebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace Specs.RepTheorySurvey.CategoryO.BGGReciprocity

open RepTheorySurvey.CategoryO.ProjectiveFiltrations (Layer VermaFlag)
open ProjectiveCovers (projectiveCover_value)
open RestrictedDual (costandard_value)

universe u

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

/-- In a Verma flag with these labels, count the layers isomorphic to the
given Verma module. Each entry represents one successive quotient. -/
def vermaMultiplicity (D : Setup g) (lam : D.Weight) (weights : List D.Weight) : ℕ :=
  weights.countP (fun nu => decide (Nonempty (verma_value D nu ≃ₗ[U g] verma_value D lam)))

/-- Count the successive quotients isomorphic to the pinned simple
of highest weight `mu` in an ordinary enveloping-submodule series. -/
def compositionMultiplicity (D : Setup g) (mu : D.Weight) {X : ModuleCat.{u} (U g)}
    (s : CompositionSeries (Submodule (U g) X)) : ℕ :=
  (Finset.univ.filter fun i : Fin s.length =>
    Nonempty (Layer (s i.castSucc) (s i.succ) ≃ₗ[U g] simpleQuotient_value D mu)).card

/-- The multiplicity of the simple is independent of the complete
composition series of the Verma module. -/
def CompositionMultiplicityInvariantType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (mu lam : D.Weight)
    (s t : CompositionSeries (Submodule (U g) (verma_value D lam))),
    s.head = ⊥ → s.last = ⊤ → t.head = ⊥ → t.last = ⊤ →
    compositionMultiplicity D mu s = compositionMultiplicity D mu t

/-- Every projective cover of the pinned simple satisfies reciprocity for every
Verma flag and every complete composition series of the pinned Verma. The two
counts equal the complex dimension of Hom from the cover to the dual Verma. -/
def ReciprocityType : Prop :=
  ∀ {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
    (D : Setup g) (mu lam : D.Weight) (X : category_value.{u, u} D)
    (p : X.obj →ₗ[U g] simpleQuotient_value D mu),
    projectiveCover_value X p →
    let H := X.obj ⟶ costandard_value D lam
    FiniteDimensional ℂ H ∧
    (∀ weights : List D.Weight, VermaFlag D (X := X.obj) weights ⊥ ⊤ →
      vermaMultiplicity D lam weights = Module.finrank ℂ H) ∧
    (∀ s : CompositionSeries (Submodule (U g) (verma_value D lam)),
      s.head = ⊥ → s.last = ⊤ →
      compositionMultiplicity D mu s = Module.finrank ℂ H)

end Specs.RepTheorySurvey.CategoryO.BGGReciprocity
