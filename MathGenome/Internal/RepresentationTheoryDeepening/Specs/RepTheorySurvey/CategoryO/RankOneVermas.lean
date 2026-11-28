import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA

/-! The Verma-module calculation for the standard triangular decomposition of sl₂. -/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped ModuleCat.Algebra

namespace Specs.RepTheorySurvey.CategoryO.RankOneVermas

open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.Sl2Model

abbrev G := Model ℂ
abbrev e : G := E ℂ
abbrev f : G := F ℂ
abbrev h : G := H ℂ

/-- The diagonal Cartan, the upper and lower root lines, and the standard triple. -/
structure IsStandard (D : Setup G) : Prop where
  cartan : D.cartan = Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.cartan 1
  positive : D.nPlus.toSubmodule = ℂ ∙ e
  negative : D.nMinus.toSubmodule = ℂ ∙ f
  triple : ∀ i : D.Simple, D.e i = e ∧ D.f i = f ∧ (D.h i : G) = h

/-- The weight with scalar parameter `lam`, using the upper diagonal entry as the
coordinate on the Cartan. Its value at `h` is `lam`. -/
def weight (D : Setup G) (lam : ℂ) : D.Weight where
  toFun x := lam * x.val.val 0 0
  map_add' x y := mul_add lam _ _
  map_smul' c x := by
    change lam * (c * x.val.val 0 0) = c * (lam * x.val.val 0 0)
    rw [mul_left_comm]

abbrev Verma (D : Setup G) (lam : ℂ) := verma_value D (weight D lam)
abbrev Simple (D : Setup G) (lam : ℂ) := simpleQuotient_value D (weight D lam)

def highest (D : Setup G) (lam : ℂ) : Verma D lam :=
  highestVector_value D.cartan D.direction (character_value D (weight D lam))

def loweringPower (D : Setup G) (lam : ℂ) (j : ℕ) : Verma D lam :=
  (ι ℂ f : U G) ^ j • highest D lam

def standard_setup_type : Prop :=
  ∃ D : Setup G, IsStandard D

def weight_parameter_type : Prop :=
  ∀ (D : Setup G), IsStandard D → Function.Bijective (weight D) ∧
    ∀ x : D.cartan, (x : G) = h → ∀ lam : ℂ, weight D lam x = lam

def pbw_basis_type : Prop :=
  ∀ (D : Setup G), IsStandard D → ∀ lam : ℂ,
    (∃ b : Basis ℕ ℂ (Verma D lam), ∀ j, b j = loweringPower D lam j) ∧
    ∀ j : ℕ, loweringPower D lam j ∈
      weightSpace_value D.cartan (Verma D lam) (weight D (lam - 2 * j))

def simple_iff_type : Prop :=
  ∀ (D : Setup G), IsStandard D → ∀ lam : ℂ,
    IsSimpleModule (U G) (Verma D lam) ↔ ∀ m : ℕ, lam ≠ (m : ℂ)

def integral_submodule_type : Prop :=
  ∀ (D : Setup G), IsStandard D → ∀ m : ℕ,
    let S := Submodule.span (U G) ({loweringPower D m (m + 1)} : Set (Verma D m))
    S ≠ ⊥ ∧ S ≠ ⊤ ∧
    (∀ T : Submodule (U G) (Verma D m), T ≠ ⊥ → T ≠ ⊤ → T = S) ∧
    (∃! E : Verma D (-(m : ℂ) - 2) ≃ₗ[U G] S,
      ∀ j : ℕ, (E (loweringPower D (-(m : ℂ) - 2) j) : Verma D m) =
        loweringPower D m (j + (m + 1)))

/-- The submodule is the kernel of the canonical map to the pinned simple quotient. -/
def quotient_kernel_type : Prop :=
  ∀ (D : Setup G), IsStandard D →
    ∃ q : ∀ lam : ℂ, Verma D lam →ₗ[U G] Simple D lam,
      (∀ lam x, q lam x =
        Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.quotientMap D.cartan D.direction
          (character_value D (weight D lam)) x) ∧
      (∀ m : ℕ, (q m).ker = Submodule.span (U G)
        ({loweringPower D m (m + 1)} : Set (Verma D m))) ∧
      ∀ lam : ℂ, (∀ m : ℕ, lam ≠ (m : ℂ)) → Function.Bijective (q lam)

end Specs.RepTheorySurvey.CategoryO.RankOneVermas
