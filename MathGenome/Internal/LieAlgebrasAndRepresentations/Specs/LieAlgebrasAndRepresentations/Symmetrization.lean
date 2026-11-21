import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PBWSpecialization
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

/-! LA-A05, characteristic-zero symmetrization, source lines 333–405.
The symmetric algebra and enveloping algebra below are the actual upstream
objects. No basis, rank bound, or finite-dimensionality is an added hypothesis.
The full conclusions are recorded separately from the proved auxiliary targets.
-/
namespace LieAlgebrasAndRepresentations.Symmetrization
open _root_.Shared.Lie _root_.Shared.Lie.PBW.Graded
universe u v
variable {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]

/-- Formula (1.2); the unique permutation of the empty tuple contributes 1. -/
noncomputable def average (n : ℕ) (y : Fin n → g) : U k g :=
  (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), word k g (List.ofFn (y ∘ σ))

/-- The symmetric-algebra filtration by total degree, including negative steps. -/
def symmetricFiltration (m : ℤ) : Submodule k (SymmetricAlgebra k g) :=
  Submodule.span k {a | ∃ xs : List g, (xs.length : ℤ) ≤ m ∧ symmetricWord xs = a}

def HasFormula (s : SymmetricAlgebra k g →ₗ[k] U k g) : Prop :=
  ∀ (n : ℕ) (y : Fin n → g), s (symmetricWord (List.ofFn y)) = average n y

/-- Equality of filtration steps specifies preservation by the map and inverse. -/
def IsFiltered (e : SymmetricAlgebra k g ≃ₗ[k] U k g) : Prop :=
  ∀ m : ℤ, Submodule.map e.toLinearMap (symmetricFiltration m) = filtration k g m

/-- Under PBW, the map on top symbols is the identity. This uses the actual
successive quotient, rather than an arbitrary abstract graded space. -/
def HasTopSymbol [Fact (Specs.Shared.Lie.filtrationType k g)]
    (s : SymmetricAlgebra k g →ₗ[k] U k g) : Prop :=
  ∀ (n : ℕ) (a : SymmetricAlgebra k g), a ∈ symmetricDegree n →
    ∃ h : s a ∈ filtration k g n,
      symbol k g n ⟨s a, h⟩ = canonicalMap (k := k) (g := g) a

/-- An actual adjoint representation by derivations on S(g), together with
intertwining on all elements. Its generator values specify the adjoint action. -/
def AdjointEquivariant (s : SymmetricAlgebra k g →ₗ[k] U k g) : Prop :=
  ∃ ρ : g →ₗ⁅k⁆ Derivation k (SymmetricAlgebra k g) (SymmetricAlgebra k g),
    (∀ x y : g, ρ x (SymmetricAlgebra.ι k g y) = SymmetricAlgebra.ι k g ⁅x, y⁆) ∧
    ∀ (x : g) (a : SymmetricAlgebra k g),
      s (ρ x a) = inclusion k g x * s a - s a * inclusion k g x

end LieAlgebrasAndRepresentations.Symmetrization

namespace Specs.LieAlgebrasAndRepresentations.Symmetrization
open _root_.Shared.Lie _root_.Shared.Lie.PBW.Graded
open _root_.LieAlgebrasAndRepresentations.Symmetrization
universe u v

/-- The complete positive assertion of LA-A05-Sym. -/
def symmetrizationExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g],
    ∃ e : SymmetricAlgebra k g ≃ₗ[k] U k g,
      HasFormula e.toLinearMap ∧ IsFiltered e ∧ AdjointEquivariant e.toLinearMap ∧
      ∃ hf : Specs.Shared.Lie.filtrationType k g,
        letI : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨hf⟩
        HasTopSymbol e.toLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A concrete characteristic-zero noncommutative example: gl₂(ℚ).
Every linear map with formula (1.2) fails multiplicativity. The positive
assertion above supplies existence of such a map; this is its obstruction. -/
def nonmultiplicativeExpected : Prop :=
  let g := Matrix (Fin 2) (Fin 2) ℚ
  (∃ x y : g, ⁅x, y⁆ ≠ 0) ∧
  ∀ s : SymmetricAlgebra ℚ g →ₗ[ℚ] U ℚ g, HasFormula s →
    ∃ a b : SymmetricAlgebra ℚ g, s (a*b) ≠ s a * s b

def averageMultilinearExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (n : ℕ),
    ∃ A : MultilinearMap k (fun _ : Fin n => g) (U k g),
      ∀ y, A y = average n y

def averageSymmetricExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (n : ℕ) (y : Fin n → g) (τ : Equiv.Perm (Fin n)),
    average n (y ∘ τ) = (average n y : U k g)

def averageFilteredExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (n : ℕ) (y : Fin n → g), average n y ∈ filtration k g n

def averageEmptyExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (y : Fin 0 → g), (average 0 y : U k g) = 1

def averageSingletonExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (y : Fin 1 → g), (average 1 y : U k g) = inclusion k g (y 0)

/-- The whole principal-symbol conclusion follows for any actual formula map. -/
def formulaTopSymbolExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    [Fact (Specs.Shared.Lie.filtrationType k g)]
    (s : SymmetricAlgebra k g →ₗ[k] U k g), HasFormula s → HasTopSymbol s

def formulaFilteredExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (s : SymmetricAlgebra k g →ₗ[k] U k g), HasFormula s →
      ∀ m : ℤ, symmetricFiltration m ≤ (filtration k g m).comap s

def formulaUniqueExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    (s t : SymmetricAlgebra k g →ₗ[k] U k g), HasFormula s → HasFormula t → s = t

end Specs.LieAlgebrasAndRepresentations.Symmetrization
