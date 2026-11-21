import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations
import Mathlib.Order.Atoms
import Mathlib.Data.Set.Finite.Powerset

/-! W72, forward flat-lattice assertion. Only the ground set is finite; the
ambient type can be infinite. Flats use the original matroid's closure.
The shared construction below supplies the lattice, without assuming any
rank, cover, atomisticity or semimodularity results. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u v
variable {α : Type u}

/-- Flats ordered by inclusion, including all loops. -/
abbrev Flat (M : _root_.Matroid α) := {F : Set α // M.IsFlat F}

def flatClosure (M : _root_.Matroid α) (A : Set α) : Flat M :=
  ⟨M.closure A, M.isFlat_closure A⟩

def flatGroundSet (M : _root_.Matroid α) (F : Flat M) : Iic M.E :=
  ⟨F.1, F.2.subset_ground⟩

/-- Closure and inclusion between ground subsets and flats. -/
def flatInsertion (M : _root_.Matroid α) :
    GaloisInsertion (fun A : Iic M.E => flatClosure M A.1) (flatGroundSet M) where
  choice A h := ⟨A.1, M.isFlat_iff_closure_eq.mpr
    (Set.Subset.antisymm h (M.subset_closure A.1 A.2))⟩
  gc A F := by
    change M.closure A.1 ⊆ F.1 ↔ A.1 ⊆ F.1
    constructor
    · exact (M.subset_closure A.1 A.2).trans
    · intro h
      exact (M.closure_subset_closure h).trans_eq F.2.closure
  le_l_u F := by
    change F.1 ⊆ M.closure F.1
    exact M.subset_closure F.1 F.2.subset_ground
  choice_eq A h := Subtype.ext (Set.Subset.antisymm
    (M.subset_closure A.1 A.2) h)

instance flatCompleteLattice (M : _root_.Matroid α) : CompleteLattice (Flat M) :=
  (flatInsertion M).liftCompleteLattice

/-- The exact convention in W72: finite, atom generated, and upper
semimodular in covering form. `sSup ∅ = ⊥` includes the empty join. -/
def GeometricLattice (L : Type v) [CompleteLattice L] : Prop :=
  Finite L ∧ (∀ x : L, sSup {a | IsAtom a ∧ a ≤ x} = x) ∧
    ∀ x y : L, (x ⊓ y) ⋖ x → y ⋖ (x ⊔ y)

namespace Expected

def flatCharacterization : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (F : Set α),
    M.IsFlat F ↔ F ⊆ M.E ∧ M.closure F = F

def flatFinite : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], Finite (Flat M)

def flatMeet : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (F G : Flat M),
    (F ⊓ G).1 = F.1 ∩ G.1

def flatJoin : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) (F G : Flat M),
    (F ⊔ G).1 = M.closure (F.1 ∪ G.1)

def flatBottom : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α),
    (⊥ : Flat M).1 = M.closure ∅

def flatCoverRank : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (F G : Flat M),
    F ⋖ G ↔ F < G ∧ rank M G.1 - rank M F.1 = 1

def flatAtom : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (F : Flat M),
    IsAtom F ↔ ∃ e, M.IsNonloop e ∧ F = flatClosure M {e}

def flatJoinNonloops : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (F : Flat M),
    sSup {A : Flat M | ∃ e ∈ F.1, M.IsNonloop e ∧ A = flatClosure M {e}} = F

def flatAtomistic : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (F : Flat M),
    sSup {A : Flat M | IsAtom A ∧ A ≤ F} = F

def flatSemimodular : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (F G : Flat M),
    (F ⊓ G) ⋖ F → G ⋖ (F ⊔ G)

def flatGeometric : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite], GeometricLattice (Flat M)

end Expected
end FiniteCombinatorics.Matroid
