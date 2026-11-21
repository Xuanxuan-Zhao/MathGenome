import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Partitions
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.GroupTheory.GroupAction.Basic
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionModels

/-! FR A02, with zero-based cells and labels as in the partition interface.
A row is specified by its ordered index; empty rows are retained as empty fibers.
Induction below is the shared noncommutative balanced left tensor product. -/
noncomputable section
open scoped MonoidAlgebra
namespace Specs.AdvancedFiniteGroupRepresentations

abbrev Tableau {n : ℕ} (p : Partition n) := Cell p ≃ Fin n

def canonicalTableau {n} (p : Partition n) : Tableau p :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact YoungDiagram.card_ofPartition p)

def labelRow {n} {p : Partition n} (t : Tableau p) (a : Fin n) : ℕ :=
  (t.symm a).val.1

def labelColumn {n} {p : Partition n} (t : Tableau p) (a : Fin n) : ℕ :=
  (t.symm a).val.2

def rowLabels {n} {p : Partition n} (t : Tableau p) (i : ℕ) : Set (Fin n) :=
  {a | labelRow t a = i}

def columnLabels {n} {p : Partition n} (t : Tableau p) (j : ℕ) : Set (Fin n) :=
  {a | labelColumn t a = j}

instance tableauAction {n} {p : Partition n} : MulAction (SymmetricGroup n) (Tableau p) where
  smul σ t := relabelLabeling σ t
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

def rowSetoid {n} (p : Partition n) : Setoid (Tableau p) :=
  { r := fun t u => labelRow t = labelRow u
    iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }

abbrev Tabloid {n} (p : Partition n) := Quotient (rowSetoid p)

def tabloid {n} {p : Partition n} (t : Tableau p) : Tabloid p := Quotient.mk _ t

instance tabloidAction {n} {p : Partition n} : MulAction (SymmetricGroup n) (Tabloid p) where
  smul σ := Quotient.map (σ • ·) (by
    intro t u h
    change labelRow t = labelRow u at h
    funext a
    exact congrFun h (σ.symm a))
  one_smul q := Quotient.inductionOn q (fun t => congrArg tabloid (one_smul _ t))
  mul_smul σ τ q := Quotient.inductionOn q (fun t => congrArg tabloid (mul_smul σ τ t))

instance tabloidFintype {n} {p : Partition n} : Fintype (Tabloid p) := Fintype.ofFinite _

instance tabloidNonempty {n} {p : Partition n} : Nonempty (Tabloid p) :=
  ⟨tabloid (canonicalTableau p)⟩

def emptyTableau : Tableau emptyPartition := canonicalTableau emptyPartition
def emptyTabloid : Tabloid emptyPartition := tabloid emptyTableau

/-- Permutations preserving every fiber of a function. -/
def fiberSubgroup {α ι : Type*} (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  one_mem' := fun _ => rfl
  mul_mem' hσ hτ a := (hσ _).trans (hτ a)
  inv_mem' {σ} hσ a := by simpa using (hσ (σ.symm a)).symm


abbrev rowSubgroup {n} {p : Partition n} (t : Tableau p) := fiberSubgroup (labelRow t)
abbrev columnSubgroup {n} {p : Partition n} (t : Tableau p) := fiberSubgroup (labelColumn t)

abbrev PermutationModule {n} (p : Partition n) := MonoidAlgebra ℂ (Tabloid p)

noncomputable def permutationRepresentation {n} (p : Partition n) :
    Representation ℂ (SymmetricGroup n) (PermutationModule p) :=
  Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid p)

abbrev InducedRow {n} {p : Partition n} (t : Tableau p) :=
  P103.Ch09.Induced (rowSubgroup t) (Representation.trivial ℂ (rowSubgroup t) ℂ)

attribute [local instance] P103.Ch09.rightSubgroupModule
  P103.Ch09.inducedAlgebraModule P103.Ch09.inducedScalarModule

noncomputable def inducedRepresentation {n} {p : Partition n} (t : Tableau p) :
    Representation ℂ (SymmetricGroup n) (InducedRow t) :=
  P103.Ch09.induction (rowSubgroup t) (Representation.trivial ℂ (rowSubgroup t) ℂ)

def rowTensor {n} {p : Partition n} (t : Tableau p) (g : SymmetricGroup n) (z : ℂ) :
    InducedRow t :=
  P103.Ch09.tensor (rowSubgroup t) (Representation.trivial ℂ (rowSubgroup t) ℂ)
    (MonoidAlgebra.single g 1) z

/-! Independent expected values are the definitions above; theorem contracts
are closed propositions and contain no assumed proof certificates. -/

def TableauType := {n : ℕ} → Partition n → Type

def canonicalTableauType := ∀ {n} (p : Partition n), Tableau p

def emptyTableauType := Tableau emptyPartition

def emptyTabloidType := Tabloid emptyPartition

def labelRowType := {n : ℕ} → {p : Partition n} → Tableau p → Fin n → ℕ

def labelColumnType := {n : ℕ} → {p : Partition n} → Tableau p → Fin n → ℕ

def rowLabelsType := {n : ℕ} → {p : Partition n} → Tableau p → ℕ → Set (Fin n)

def columnLabelsType := {n : ℕ} → {p : Partition n} → Tableau p → ℕ → Set (Fin n)

def TabloidType := {n : ℕ} → Partition n → Type

def tabloidType := {n : ℕ} → {p : Partition n} → Tableau p → Tabloid p

def tableauActionType := ∀ {n} {p : Partition n}, MulAction (SymmetricGroup n) (Tableau p)

def tabloidActionType := ∀ {n} {p : Partition n}, MulAction (SymmetricGroup n) (Tabloid p)

def rowSubgroupType := {n : ℕ} → {p : Partition n} → Tableau p → Subgroup (SymmetricGroup n)

def columnSubgroupType := {n : ℕ} → {p : Partition n} → Tableau p → Subgroup (SymmetricGroup n)

def PermutationModuleType := {n : ℕ} → Partition n → Type

def permutationRepresentationType := ∀ {n} (p : Partition n), Representation ℂ (SymmetricGroup n) (PermutationModule p)

def InducedRowType := {n : ℕ} → {p : Partition n} → Tableau p → Type

def inducedRepresentationType := ∀ {n} {p : Partition n} (t : Tableau p), Representation ℂ (SymmetricGroup n) (InducedRow t)

def rowTensorType := ∀ {n} {p : Partition n} (t : Tableau p), SymmetricGroup n → ℂ → InducedRow t

def tableau_smul_applyType : Prop :=
  ∀ {n} {p : Partition n} (g : SymmetricGroup n) (t : Tableau p) (c : Cell p), (g • t) c = g (t c)

def labelRow_smulType : Prop :=
  ∀ {n} {p : Partition n} (g : SymmetricGroup n) (t : Tableau p) (a : Fin n), labelRow (g • t) a = labelRow t (g.symm a)

def tabloid_smulType : Prop :=
  ∀ {n} {p : Partition n} (g : SymmetricGroup n) (t : Tableau p), g • tabloid t = tabloid (g • t)

def tableau_nonemptyType : Prop :=
  ∀ {n} (p : Partition n), Nonempty (Tableau p)

def tableau_existsUniqueType : Prop :=
  ∀ {n} {p : Partition n} (t u : Tableau p), ∃! g : SymmetricGroup n, g • t = u

def tabloid_eq_iffType : Prop :=
  ∀ {n} {p : Partition n} (t u : Tableau p), tabloid t = tabloid u ↔ ∀ i, rowLabels t i = rowLabels u i

def rowSubgroup_iffType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p) (g : SymmetricGroup n), g ∈ rowSubgroup t ↔ ∀ i a, g a ∈ rowLabels t i ↔ a ∈ rowLabels t i

def columnSubgroup_iffType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p) (g : SymmetricGroup n), g ∈ columnSubgroup t ↔ ∀ j a, g a ∈ columnLabels t j ↔ a ∈ columnLabels t j

def tabloid_stabilizerType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p), MulAction.stabilizer (SymmetricGroup n) (tabloid t) = rowSubgroup t

def row_column_infType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p), rowSubgroup t ⊓ columnSubgroup t = ⊥

def rowLabels_cardType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p) (i : ℕ), Nat.card (rowLabels t i) = rowLength p i

def rowSubgroup_productType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p), ∃ e : rowSubgroup t ≃* (∀ i : ℕ, Equiv.Perm (rowLabels t i)), ∀ g i a, ((e g) i a).val = g.val a

def rowSubgroup_product_finiteType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p),
    ∃ e : rowSubgroup t ≃* (∀ i : Fin (length p), Equiv.Perm (rowLabels t i)),
      ∀ g i a, ((e g) i a).val = g.val a

def permutationModule_finiteDimensionalType : Prop :=
  ∀ {n} (p : Partition n), FiniteDimensional ℂ (PermutationModule p)

def permutationRepresentation_basisType : Prop :=
  ∀ {n} {p : Partition n} (g : SymmetricGroup n) (q : Tabloid p) (z : ℂ), permutationRepresentation p g (MonoidAlgebra.single q z) = MonoidAlgebra.single (g • q) z

def empty_tableau_uniqueType : Prop :=
  ∀ t : Tableau emptyPartition, t = emptyTableau

def empty_tabloid_uniqueType : Prop :=
  ∀ q : Tabloid emptyPartition, q = emptyTabloid

def emptyModule_finrankType : Prop :=
  Module.finrank ℂ (PermutationModule emptyPartition) = 1

def emptyModule_trivialType : Prop :=
  ∀ (g : SymmetricGroup 0) (v : PermutationModule emptyPartition), permutationRepresentation emptyPartition g v = v

def induction_isomorphismType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p),
    ∃ e : InducedRow t ≃ₗ[ℂ] PermutationModule p,
      (∀ g z, e (rowTensor t g z) = MonoidAlgebra.single (tabloid (g • t)) z) ∧
      (∀ g v, e (inducedRepresentation t g v) = permutationRepresentation p g (e v))

def empty_module_isomorphismType : Prop :=
  ∃ e : PermutationModule emptyPartition ≃ₗ[ℂ] ℂ,
    ∀ z, e (MonoidAlgebra.single emptyTabloid z) = z

end Specs.AdvancedFiniteGroupRepresentations
