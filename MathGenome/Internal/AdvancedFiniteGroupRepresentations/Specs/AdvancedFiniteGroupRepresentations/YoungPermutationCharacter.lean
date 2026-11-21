import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PowerSumsAlternants
import Mathlib.RepresentationTheory.Character

/-! FR-C01, source lines 862–877. A vector on `Fin r` is the list of its
entries in order; no monotonicity or positivity of its entries is imposed.
A function from labels to row indices is exactly an ordered decomposition:
its fibers are disjoint, cover all labels, and retain every empty row. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The number of labels assigned to a specified row. -/
def rowSize {n r : ℕ} (f : Fin n → Fin r) (i : Fin r) : ℕ :=
  Nat.card {a : Fin n // f a = i}

abbrev RowDecomposition {n r : ℕ} (μ : Fin r → ℕ) :=
  {f : Fin n → Fin r // ∀ i, rowSize f i = μ i}

instance rowDecompositionFintype {n r} (μ : Fin r → ℕ) :
    Fintype (@RowDecomposition n r μ) := Fintype.ofFinite _

instance rowDecompositionAction {n r} (μ : Fin r → ℕ) :
    MulAction (SymmetricGroup n) (@RowDecomposition n r μ) where
  smul σ q := ⟨fun a => q.val (σ.symm a), fun i => by
    have h : rowSize (fun a => q.val (σ.symm a)) i = rowSize q.val i :=
      Nat.card_congr (Equiv.subtypeEquiv σ.symm (fun _ => Iff.rfl))
    exact h.trans (q.property i)⟩
  one_smul q := Subtype.ext rfl
  mul_smul σ τ q := Subtype.ext rfl

abbrev OrderedRowModule {n r} (μ : Fin r → ℕ) :=
  MonoidAlgebra ℂ (@RowDecomposition n r μ)

def orderedRowRepresentation {n r} (μ : Fin r → ℕ) :
    Representation ℂ (SymmetricGroup n) (@OrderedRowModule n r μ) :=
  Representation.ofMulAction ℂ (SymmetricGroup n) (@RowDecomposition n r μ)

instance orderedRowModuleFinite {n r} (μ : Fin r → ℕ) :
    FiniteDimensional ℂ (@OrderedRowModule n r μ) :=
  Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm

/-- The ordinary complex character, defined using the trace on the indicated
permutation representation, rather than by the coefficient formula. -/
def youngPermutationCharacter {n r} (μ : Fin r → ℕ) (σ : SymmetricGroup n) : ℂ :=
  (orderedRowRepresentation μ).character σ

def rowSizeType := {n r : ℕ} → (Fin n → Fin r) → Fin r → ℕ
def RowDecompositionType := {_n r : ℕ} → (Fin r → ℕ) → Type
def OrderedRowModuleType := {_n r : ℕ} → (Fin r → ℕ) → Type
def orderedRowRepresentationType := ∀ {n r} (μ : Fin r → ℕ),
  Representation ℂ (SymmetricGroup n) (@OrderedRowModule n r μ)
def youngPermutationCharacterType := {n r : ℕ} → (Fin r → ℕ) → SymmetricGroup n → ℂ

def young_permutation_characterType : Prop :=
  ∀ {n r} (μ : Fin r → ℕ), (∑ i, μ i) = n → ∀ (ν : Partition n)
    (σ : SymmetricGroup n), cyclePartition σ = ν →
    youngPermutationCharacter μ σ = naturalCoefficient μ (partitionPowerSum r ν)

end Specs.AdvancedFiniteGroupRepresentations
