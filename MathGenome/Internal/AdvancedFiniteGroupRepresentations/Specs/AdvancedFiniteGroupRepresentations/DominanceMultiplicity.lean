import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! FR A06, original source lines 326–348. All shapes, including the empty
partition, use the upstream Specht subspace and ambient permutation action.
Equivariance is expressed through the inclusion of that subspace: whenever
`w.val = g • v.val`, the images satisfy the same equation. This formulation
needs no choice of, or assumed certificate for, an action on the subspace. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The vector space of actual equivariant complex linear maps. -/
def spechtHomSpace {n : ℕ} (p q : Partition n) :
    Submodule ℂ (SpechtModule p →ₗ[ℂ] PermutationModule q) where
  carrier := {f | ∀ (g : SymmetricGroup n) (v w : SpechtModule p),
    w.val = permutationRepresentation p g v.val →
      f w = permutationRepresentation q g (f v)}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh g v w hw
    simpa only [LinearMap.add_apply, map_add] using congrArg₂ (· + ·)
      (hf g v w hw) (hh g v w hw)
  smul_mem' := by
    intro a f hf g v w hw
    simpa only [LinearMap.smul_apply, map_smul] using congrArg (a • ·) (hf g v w hw)

abbrev SpechtHom {n : ℕ} (p q : Partition n) := ↥(spechtHomSpace p q)

/-- The diagonal map is the inclusion of the original Specht subspace. -/
def spechtInclusion {n : ℕ} (p : Partition n) : SpechtHom p p :=
  ⟨(spechtSpan p).subtype, by intro g v w hw; exact hw⟩

def spechtHomSpaceType := ∀ {n : ℕ} (p q : Partition n),
  Submodule ℂ (SpechtModule p →ₗ[ℂ] PermutationModule q)
def SpechtHomType := {n : ℕ} → Partition n → Partition n → Type
def spechtInclusionType := ∀ {n : ℕ} (p : Partition n), SpechtHom p p

def dominance_of_nonzero_homType : Prop :=
  ∀ {n : ℕ} (p q : Partition n), Nontrivial (SpechtHom p q) → dominates p q

def diagonal_hom_finrankType : Prop :=
  ∀ {n : ℕ} (p : Partition n), Module.finrank ℂ (SpechtHom p p) = 1

def spechtInclusion_ne_zeroType : Prop :=
  ∀ {n : ℕ} (p : Partition n), spechtInclusion p ≠ 0

end Specs.AdvancedFiniteGroupRepresentations
