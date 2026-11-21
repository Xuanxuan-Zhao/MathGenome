import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! LA-F03-Finite, notes/005 lines 2648–2698. Simplicity and the component
sum are allocated to LA-F03. We use joint ordinary eigenspaces for the
specified actual Cartan generators, with no finite-dimensionality assumption.
Cartan rows index coroots, so a root a has coordinate i equal to <a,b_i^∨>.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι]

/-- The joint h-weight space, for every complex-valued weight, including zero. -/
def weightSpace (A : Matrix ι ι ℤ) (χ : ι → ℂ) : Submodule ℂ (Algebra A) where
  carrier := {x | ∀ i, ⁅h A i, x⁆ = χ i • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [lie_add, hx i, hy i, smul_add]
  smul_mem' := by
    intro c x hx i
    rw [lie_smul, hx i, smul_smul, smul_smul, mul_comm c]

/-- Prescribed Euclidean roots as actual linear weights on the Cartan basis. -/
def rootWeight {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : ι → E) (a : E) : ι → ℂ := fun i => (rootCartan a (b i) : ℂ)

/-- Simple reflection on arbitrary complex weights, with the source's row convention. -/
def reflectWeight (A : Matrix ι ι ℤ) (i : ι) (χ : ι → ℂ) : ι → ℂ :=
  fun j => χ j - (A j i : ℂ) * χ i

/-- A finite-dimensional invariant space for the actual i-th adjoint triple. -/
def RankOneLocallyFinite (A : Matrix ι ι ℤ) : Prop := ∀ i (x : Algebra A),
  ∃ S : Submodule ℂ (Algebra A), Module.Finite ℂ S ∧ x ∈ S ∧
    ∀ y ∈ S, ⁅e A i, y⁆ ∈ S ∧ ⁅f A i, y⁆ ∈ S ∧ ⁅h A i, y⁆ ∈ S

/-- Terminating exponential applied to a vector, written with an explicit cutoff. -/
def expSum {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (x : L) (N : ℕ) (y : L) : L :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • iterBracket x n y

/-- Actual exponential automorphisms, rather than an assumed Weyl permutation
of a putative finite set of weights. All cutoffs are pointwise. -/
def ReflectionAutomorphisms (A : Matrix ι ι ℤ) : Prop :=
  ∀ i, ∃ (ep fm : Algebra A ≃ₗ⁅ℂ⁆ Algebra A),
    (∀ x, ∃ N, iterBracket (e A i) N x = 0 ∧
      ep x = expSum (e A i) N x) ∧
    (∀ x, ∃ N, iterBracket (-(f A i)) N x = 0 ∧
      fm x = expSum (-(f A i)) N x) ∧
    let n := (ep.trans fm).trans ep
    (∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i) ∧
    (∀ χ, (weightSpace A χ).map n.toLinearEquiv.toLinearMap =
      weightSpace A (reflectWeight A i χ))

end LieAlgebrasAndRepresentations.Serre

namespace Specs.LieAlgebrasAndRepresentations.SerreFiniteType
open _root_.LieAlgebrasAndRepresentations
open _root_.LieAlgebrasAndRepresentations.Serre
universe u v

/-- Local nilpotence on the entire quotient, without assuming finite type. -/
def locallyNilpotentExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ) (i : ι) (x : Algebra A),
    (∃ n, iterBracket (e A i) n x = 0) ∧
    (∃ n, iterBracket (f A i) n x = 0)

/-- Completed preliminary diagonalization assertion; it does not identify
which weights occur or assume the full finite-type conclusion. -/
def weightSpanExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ),
    (⨆ χ : ι → ℂ, weightSpace A χ) = ⊤

def cartanRankExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ) [Fintype ι],
    CartanConditions A → Module.finrank ℂ (cartan A) = Fintype.card ι

/-- The bridge applies to every complex weight, beyond the prescribed roots. -/
def reflectionTransportExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ) (i : ι), A i i = 2 →
  ∀ n : Algebra A ≃ₗ⁅ℂ⁆ Algebra A,
    (∀ j, n (h A j) = h A j - (A j i : ℂ) • h A i) →
    ∀ χ : ι → ℂ, (weightSpace A χ).map n.toLinearEquiv.toLinearMap =
      weightSpace A (reflectWeight A i χ)

/-- Local finiteness and actual reflection automorphisms are established before
finite-dimensionality; they exclude arbitrary additional complex weights. -/
def reflectionsExpected : Prop :=
  ∀ {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ), CartanConditions A →
    RankOneLocallyFinite A ∧ ReflectionAutomorphisms A

/-- The complete finite-type conclusion, including ordinary eigenspace
exhaustion, exact support, every multiplicity, the zero space and dimension.
The finite index type includes the empty root system. -/
def finiteTypeExpected : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (R : Set E), IsRootSystem R →
  ∀ z, RootRegular R z → ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
  ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) →
    Module.Finite ℂ (Algebra A) ∧
    (⨆ χ : ι → ℂ, weightSpace A χ) = ⊤ ∧
    (∀ χ : ι → ℂ, χ ≠ 0 →
      (weightSpace A χ ≠ ⊥ ↔ ∃ a ∈ R, χ = rootWeight b a)) ∧
    (∀ a ∈ R, Module.finrank ℂ (weightSpace A (rootWeight b a)) = 1) ∧
    weightSpace A 0 = cartan A ∧
    Module.finrank ℂ (cartan A) = Fintype.card ι ∧
    Module.finrank ℂ (Algebra A) = Fintype.card ι + Nat.card R

end Specs.LieAlgebrasAndRepresentations.SerreFiniteType
