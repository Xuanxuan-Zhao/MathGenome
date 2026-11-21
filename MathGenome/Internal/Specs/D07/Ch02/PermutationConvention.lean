import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.Fintype.Card

/-!
Independent specification of `K07.02.permutation_convention` (paper.tex:498–500).
Carriers are arbitrary types, with no finiteness or inhabitedness assumption.
`Fin n` is the model for the n labels; `FiniteLabels` identifies its labels
explicitly with the source's `{1, ..., n}`. Cycles have distinct entries.
Omitting singleton cycles does not remove their points from the ambient set.
-/

namespace Specs.D07.Ch02.PermutationConvention

universe u

def PermutationCarrierType : Type (u + 1) := Type u → Type u

def permutationCarrierValue : PermutationCarrierType.{u} := fun X => Equiv.Perm X

def SymmetricCarrierType : Type 1 := ℕ → Type

def symmetricCarrierValue : SymmetricCarrierType := fun n => Equiv.Perm (Fin n)

def CycleConstructorType : Type (u + 1) :=
  ∀ (X : Type u) (l : List X), l.Nodup → Equiv.Perm X

noncomputable def cycleConstructorValue : CycleConstructorType.{u} := by
  classical
  exact fun _ l _ => l.formPerm

def BijectionMembership : Prop :=
  ∀ (X : Type u) (f : X → X),
    Function.Bijective f ↔ ∃ σ : Equiv.Perm X, (σ : X → X) = f

def GroupOperations : Prop :=
  ∀ (X : Type u),
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue (Equiv.Perm X) (· * ·) 1 Inv.inv ∧
    (∀ x : X, (1 : Equiv.Perm X) x = x) ∧
    (∀ σ τ : Equiv.Perm X, ∀ x : X, (σ * τ) x = σ (τ x)) ∧
    (∀ σ : Equiv.Perm X, σ⁻¹ = σ.symm)

/-- The zero-based Lean model has precisely the one-based labels of the source. -/
def FiniteLabels : Prop :=
  ∀ n : ℕ, ∃ e : Fin n ≃ {k : ℕ // 1 ≤ k ∧ k ≤ n},
    ∀ i : Fin n, (e i).val = i.val + 1

def EmptySymmetricGroup : Prop :=
  ∀ σ : Equiv.Perm (Fin 0), σ = 1 ∧ σ⁻¹ = σ

/-- Every entry except the last is sent to the following entry. -/
def CycleSuccessor : Prop :=
  ∀ (X : Type u) (l : List X) (h : l.Nodup) (i : ℕ) (hi : i + 1 < l.length),
    cycleConstructorValue X l h (l[i]'(by omega)) = l[i + 1]

/-- The last entry is sent back to the first, including a singleton cycle. -/
def CycleWraparound : Prop :=
  ∀ (X : Type u) (a : X) (l : List X) (h : (a :: l).Nodup),
    cycleConstructorValue X (a :: l) h ((a :: l).getLast (List.cons_ne_nil a l)) = a

def CycleFixesOutside : Prop :=
  ∀ (X : Type u) (l : List X) (h : l.Nodup) (x : X),
    x ∉ l → cycleConstructorValue X l h x = x

def SingletonCycle : Prop :=
  ∀ (X : Type u) (x : X),
    cycleConstructorValue X [x] (by simp) = 1

/-- Recording a product without its singleton cycles gives the same permutation.
No existence or uniqueness of a cycle decomposition is assumed here. -/
def OmitOneCycles : Prop :=
  ∀ (X : Type u) (L : List {l : List X // l.Nodup}),
    ((L.filter (fun l => l.val.length != 1)).map
      (fun l => cycleConstructorValue X l.val l.property)).prod =
    (L.map (fun l => cycleConstructorValue X l.val l.property)).prod

/-- Fixed points still contribute one point each to the size of the ambient set,
even though their singleton cycles are omitted from the written product. -/
def FixedPointsCount : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (σ : Equiv.Perm X),
    Fintype.card X = σ.support.card +
      (Finset.univ.filter (fun x : X => σ x = x)).card

end Specs.D07.Ch02.PermutationConvention
