import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardTableaux

/-! FR-B02, the Garnir relation (source lines 505–535). All row and column
indices below are zero based. A left transversal is expressed by the unique
factorization g = π * h, with π a representative and h in H. -/
noncomputable section
open scoped BigOperators
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The symmetric group on U, extended by the identity on its complement. -/
def labelPermutations {n : ℕ} (U : Finset (Fin n)) : Subgroup (SymmetricGroup n) where
  carrier := {g | ∀ a, a ∉ U → g a = a}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh a ha
    change g (h a) = a
    rw [hh a ha, hg a ha]
  inv_mem' := by
    intro g hg a ha
    exact g.injective (by simpa using (hg a ha).symm)

/-- The tail of the left column beginning at row i. -/
def garnirA {n} {p : Partition n} (t : Tableau p) (i j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => labelColumn t a = j ∧ i ≤ labelRow t a)

/-- The head of the adjacent right column ending at row i. -/
def garnirB {n} {p : Partition n} (t : Tableau p) (i j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => labelColumn t a = j + 1 ∧ labelRow t a ≤ i)

/-- The product of the two symmetric groups on the disjoint belt parts,
viewed as the subgroup they generate in S_n. -/
def garnirSubgroup {n} {p : Partition n} (t : Tableau p) (i j : ℕ) :
    Subgroup (SymmetricGroup n) :=
  labelPermutations (garnirA t i j) ⊔ labelPermutations (garnirB t i j)

/-- Representatives of all left cosets of H inside G. In particular the
factor order is πh; this definition does not pick a preferred transversal. -/
def IsLeftTransversal {n} (G H : Subgroup (SymmetricGroup n))
    (P : Finset (SymmetricGroup n)) : Prop :=
  (∀ π ∈ P, π ∈ G) ∧
    ∀ g : G, ∃! x : {π // π ∈ P} × H, x.1.val * x.2.val = g.val

def labelPermutationsType := {n : ℕ} → Finset (Fin n) → Subgroup (SymmetricGroup n)
def garnirAType := {n : ℕ} → {p : Partition n} → Tableau p → ℕ → ℕ → Finset (Fin n)
def garnirBType := {n : ℕ} → {p : Partition n} → Tableau p → ℕ → ℕ → Finset (Fin n)
def garnirSubgroupType := {n : ℕ} → {p : Partition n} → Tableau p → ℕ → ℕ → Subgroup (SymmetricGroup n)
def IsLeftTransversalType := {n : ℕ} → Subgroup (SymmetricGroup n) →
  Subgroup (SymmetricGroup n) → Finset (SymmetricGroup n) → Prop

/-- The generated subgroup is the direct product in the source, with its
specified embedding by multiplication of the disjoint permutations. -/
def garnirSubgroup_productType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p) (i j : ℕ),
    ∃ e : (labelPermutations (garnirA t i j) × labelPermutations (garnirB t i j)) ≃*
        garnirSubgroup t i j,
      ∀ x, (e x).val = x.1.val * x.2.val

/-- The original relation for every permitted left transversal containing 1.
The two specified cells are the descent a_i > b_i. -/
def garnir_relationType : Prop :=
  ∀ {n} {p : Partition n} (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p),
    ColumnIncreasing t → t ⟨(i,j+1), hb⟩ < t ⟨(i,j), ha⟩ →
    ∀ P : Finset (SymmetricGroup n),
      IsLeftTransversal
        (labelPermutations (garnirA t i j ∪ garnirB t i j))
        (garnirSubgroup t i j) P →
      1 ∈ P → ∑ π ∈ P, permutationSign π • polytabloid (π • t) = 0

end Specs.AdvancedFiniteGroupRepresentations
