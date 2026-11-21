import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import Mathlib.RepresentationTheory.Irreducible

/-! FR A05 (source lines 288–324). All shapes, including the empty shape,
use the upstream complex permutation module and first-linear Hermitian form.
Irreducibility is stated for every representation with the inherited action;
this avoids choosing an action using a theorem from the candidate module. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Orthogonal complement for the canonical tabloid Hermitian form. -/
def tabloidOrthogonal {n : ℕ} {p : Partition n}
    (W : Submodule ℂ (PermutationModule p)) : Submodule ℂ (PermutationModule p) where
  carrier := {x | ∀ y ∈ W, tabloidHermitian x y = 0}
  zero_mem' := by
    intro y _
    have hc : tabloidCoordinates (0 : PermutationModule p) = 0 := by
      ext q
      rfl
    simp [tabloidHermitian, hc]
  add_mem' := by
    intro x z hx hz y hy
    have hc : tabloidCoordinates (x + z) = tabloidCoordinates x + tabloidCoordinates z := by
      ext q
      simp [tabloidCoordinates]
    simp only [tabloidHermitian, hc, inner_add_right]
    change tabloidHermitian x y + tabloidHermitian z y = 0
    rw [hx y hy, hz y hy, add_zero]
  smul_mem' := by
    intro a x hx y hy
    have hc : tabloidCoordinates (a • x) = a • tabloidCoordinates x := by
      ext q
      simp [tabloidCoordinates]
    simp only [tabloidHermitian, hc, inner_smul_right]
    exact mul_eq_zero_of_right a (hx y hy)

def tabloidOrthogonalType := {n : ℕ} → {p : Partition n} →
  Submodule ℂ (PermutationModule p) → Submodule ℂ (PermutationModule p)

def submodule_rank_oneType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (t : Tableau p) (x : PermutationModule p),
    groupAlgebraAction p (columnAlternator t) x =
      tabloidHermitian x (polytabloid t) • polytabloid t

def submodule_theoremType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (U : Subrepresentation (permutationRepresentation p)),
    spechtSpan p ≤ U.toSubmodule ∨ U.toSubmodule ≤ tabloidOrthogonal (spechtSpan p)

def specht_invariant_subspaceType : Prop :=
  ∀ {n : ℕ} {p : Partition n} (U : Subrepresentation (permutationRepresentation p)),
    U.toSubmodule ≤ spechtSpan p → U.toSubmodule = ⊥ ∨ U.toSubmodule = spechtSpan p

def specht_irreducibleType : Prop :=
  ∀ {n : ℕ} (p : Partition n) (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    (∀ g v, (ρ g v).val = permutationRepresentation p g v.val) → ρ.IsIrreducible

def specht_nonzero_irreducibleType : Prop :=
  ∀ {n : ℕ} (p : Partition n),
    spechtSpan p ≠ ⊥ ∧
    ∃ ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
      (∀ g v, (ρ g v).val = permutationRepresentation p g v.val) ∧ ρ.IsIrreducible

end Specs.AdvancedFiniteGroupRepresentations
