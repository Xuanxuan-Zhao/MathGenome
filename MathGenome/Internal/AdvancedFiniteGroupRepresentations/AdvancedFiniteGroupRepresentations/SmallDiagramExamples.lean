import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Branching
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.HookLength
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardRepresentation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SmallDiagramExamples

noncomputable section
open scoped BigOperators Classical
namespace AdvancedFiniteGroupRepresentations

abbrev partition22 := Specs.AdvancedFiniteGroupRepresentations.partition22
abbrev partition31 := Specs.AdvancedFiniteGroupRepresentations.partition31
abbrev partition211 := Specs.AdvancedFiniteGroupRepresentations.partition211
abbrev partition21 := Specs.AdvancedFiniteGroupRepresentations.partition21
abbrev partition3 := Specs.AdvancedFiniteGroupRepresentations.partition3

theorem small_diagram_parts : Specs.AdvancedFiniteGroupRepresentations.small_diagram_partsType := by
  refine ⟨?_, ?_, ?_, standardPartition_parts (by decide), ?_⟩
  all_goals
    change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens _ _).toPartition _)).rowLens = _
    rw [YoungDiagram.ofPartition_toPartition]
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    simp

@[simp] theorem parts_partition22 : parts partition22 = [2, 2] := small_diagram_parts.1
@[simp] theorem parts_partition31 : parts partition31 = [3, 1] := small_diagram_parts.2.1
@[simp] theorem parts_partition211 : parts partition211 = [2, 1, 1] := small_diagram_parts.2.2.1
@[simp] theorem parts_partition21 : parts partition21 = [2, 1] := small_diagram_parts.2.2.2.1
@[simp] theorem parts_partition3 : parts partition3 = [3] := small_diagram_parts.2.2.2.2

theorem cells_partition22 : cells partition22 = {(0,0), (0,1), (1,0), (1,1)} := by
  change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens _ _).toPartition _)).cells = _
  rw [YoungDiagram.ofPartition_toPartition]
  decide

theorem cells_partition31 : cells partition31 = {(0,0), (0,1), (0,2), (1,0)} := by
  change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens _ _).toPartition _)).cells = _
  rw [YoungDiagram.ofPartition_toPartition]
  decide

theorem cells_partition211 : cells partition211 = {(0,0), (0,1), (1,0), (2,0)} := by
  change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens _ _).toPartition _)).cells = _
  rw [YoungDiagram.ofPartition_toPartition]
  decide

theorem cells_partition21 : cells partition21 = {(0,0), (0,1), (1,0)} := by
  ext ⟨i,j⟩
  change (i,j) ∈ cells (standardPartition 3 (by decide)) ↔ _
  rw [standard_cell_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem cells_partition3 : cells partition3 = {(0,0), (0,1), (0,2)} := by
  change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens _ _).toPartition _)).cells = _
  rw [YoungDiagram.ofPartition_toPartition]
  decide

/-- Compute the actual hook product from its finite set of cells. -/
theorem hookProduct_cells {n : ℕ} (p : Partition n) :
    hookProduct p = ∏ c ∈ cells p, ((cells p).filter (fun d =>
      (d.1 = c.1 ∧ c.2 ≤ d.2) ∨ (d.2 = c.2 ∧ c.1 ≤ d.1))).card := by
  unfold hookProduct Specs.AdvancedFiniteGroupRepresentations.hookProduct
  change (∏ c : Cell p, ((cells p).filter (fun d =>
    (d.1 = c.val.1 ∧ c.val.2 ≤ d.2) ∨ (d.2 = c.val.2 ∧ c.val.1 ≤ d.1))).card) = _
  exact Finset.prod_coe_sort (cells p) (fun c : ℕ × ℕ =>
    ((cells p).filter (fun d =>
      (d.1 = c.1 ∧ c.2 ≤ d.2) ∨ (d.2 = c.2 ∧ c.1 ≤ d.1))).card)

theorem small_hook_products : hookProduct partition22 = 12 ∧
    hookProduct partition31 = 8 ∧ hookProduct partition211 = 8 := by
  simp only [hookProduct_cells, cells_partition22, cells_partition31, cells_partition211]
  decide

theorem small_diagram_dimensions : Specs.AdvancedFiniteGroupRepresentations.small_diagram_dimensionsType := by
  have h22 := (hookLength_formula_dimension partition22).2
  have h31 := (hookLength_formula_dimension partition31).2
  have h211 := (hookLength_formula_dimension partition211).2
  rw [small_hook_products.1] at h22
  rw [small_hook_products.2.1] at h31
  rw [small_hook_products.2.2] at h211
  norm_num at h22 h31 h211
  refine ⟨by exact_mod_cast h22, by exact_mod_cast h31, by exact_mod_cast h211,
    standard_S3.2, ?_⟩
  apply specht_finrank_singleRow
  change (parts partition3).length ≤ 1
  simp

theorem small_standard_point : Specs.AdvancedFiniteGroupRepresentations.small_standard_pointType :=
  ⟨standard_representation, point_coordinates, standard_S3⟩

/-- The square has one removable box. -/
theorem removable22_iff (c : ℕ × ℕ) : IsRemovable partition22 c ↔ c = (1,1) := by
  rcases c with ⟨i,j⟩
  rw [removable_iff_row_end]
  simp only [rowLength_eq_getD, parts_partition22]
  cases i with
  | zero => simp
  | succ i => cases i with
    | zero => simp
    | succ i => simp

theorem removable31_iff (c : ℕ × ℕ) :
    IsRemovable partition31 c ↔ c = (1,0) ∨ c = (0,2) := by
  rcases c with ⟨i,j⟩
  rw [removable_iff_row_end]
  simp only [rowLength_eq_getD, parts_partition31]
  cases i with
  | zero => simp
  | succ i => cases i with
    | zero => simp
    | succ i => simp

theorem addable21_iff (c : ℕ × ℕ) :
    IsAddable partition21 c ↔ c = (0,2) ∨ c = (1,1) ∨ c = (2,0) := by
  rcases c with ⟨i,j⟩
  rw [addable_iff_row_end]
  simp only [rowLength_eq_getD, parts_partition21]
  cases i with
  | zero => simp
  | succ i => cases i with
    | zero => simp
    | succ i => cases i with
      | zero => simp
      | succ i => simp

def squareCorner : RemovableCell partition22 :=
  ⟨(1,1), (removable22_iff _).mpr rfl⟩

def squareCornerEquiv : Unit ≃ RemovableCell partition22 :=
  Equiv.ofBijective (fun _ => squareCorner) ⟨by intro a b _; exact Subsingleton.elim _ _, by
    intro c
    refine ⟨(), Subtype.ext ?_⟩
    exact ((removable22_iff _).mp c.property).symm⟩

def corner31 (i : Fin 2) : RemovableCell partition31 :=
  ⟨if i = 0 then (1,0) else (0,2), by
    apply (removable31_iff _).mpr
    split_ifs <;> simp⟩

def corner31Equiv : Fin 2 ≃ RemovableCell partition31 :=
  Equiv.ofBijective corner31 ⟨by
    intro i j h
    have h' := congrArg Subtype.val h
    clear h
    fin_cases i <;> fin_cases j <;> simp_all [corner31], by
    rintro ⟨c,hc⟩
    rcases (removable31_iff c).mp hc with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩⟩

def added21 (i : Option (Fin 2)) : AddableCell partition21 :=
  ⟨match i with
    | none => (0,2)
    | some j => if j = 0 then (1,1) else (2,0), by
      apply (addable21_iff _).mpr
      cases i with
      | none => simp
      | some j => dsimp only; split_ifs <;> simp⟩

def added21Equiv : Option (Fin 2) ≃ AddableCell partition21 :=
  Equiv.ofBijective added21 ⟨by
    intro i j h
    have h' := congrArg Subtype.val h
    clear h
    cases i with
    | none => cases j with
      | none => rfl
      | some j => fin_cases j <;> simp_all [added21]
    | some i => cases j with
      | none => fin_cases i <;> simp_all [added21]
      | some j => fin_cases i <;> fin_cases j <;> simp_all [added21], by
    rintro ⟨c,hc⟩
    rcases (addable21_iff c).mp hc with rfl | rfl | rfl
    · exact ⟨none, rfl⟩
    · exact ⟨some 0, rfl⟩
    · exact ⟨some 1, rfl⟩⟩

def restriction31Shape (i : Fin 2) : Partition 3 :=
  if i = 0 then partition3 else partition21

def induction21Shape : Option (Fin 2) → Partition 4
  | none => partition31
  | some i => if i = 0 then partition22 else partition211

theorem square_deletion (i : Unit) :
    deleteCell partition22 (squareCornerEquiv i) = partition21 := by
  apply partition_eq_of_cells_eq
  rw [deleteCell_cells, cells_partition22, cells_partition21]
  change ({(0,0), (0,1), (1,0), (1,1)} : Finset (ℕ × ℕ)).erase (1,1) = _
  decide

@[simp] theorem corner31Equiv_val (i : Fin 2) :
    (corner31Equiv i).val = if i = 0 then (1,0) else (0,2) := rfl

@[simp] theorem added21Equiv_val (i : Option (Fin 2)) :
    (added21Equiv i).val = match i with
      | none => (0,2)
      | some j => if j = 0 then (1,1) else (2,0) := rfl

theorem deletion31 (i : Fin 2) :
    deleteCell partition31 (corner31Equiv i) = restriction31Shape i := by
  apply partition_eq_of_cells_eq
  fin_cases i <;>
    simp [deleteCell_cells, cells_partition31, restriction31Shape,
      cells_partition3, cells_partition21] <;> decide

theorem addition21 (i : Option (Fin 2)) :
    addCell partition21 (added21Equiv i) = induction21Shape i := by
  apply partition_eq_of_cells_eq
  cases i with
  | none =>
    simp [addCell_cells, cells_partition21, induction21Shape, cells_partition31,
      Finset.insert_comm]
  | some i =>
    fin_cases i <;>
      simp [addCell_cells, cells_partition21, induction21Shape,
        cells_partition22, cells_partition211, Finset.insert_comm] <;> decide

/-- Transport the inherited action along an equality of shapes. -/
def spechtEquivOfEq {n : ℕ} {p q : Partition n} (h : p = q) :
    (branchingSpecht p).Equiv (branchingSpecht q) := by
  subst q
  exact Representation.Equiv.refl _

/-- Any specified inherited action agrees with the canonical subspace action. -/
def spechtInheritedEquiv {n : ℕ} {p : Partition n}
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (h : InheritedSpechtAction p σ) : (branchingSpecht p).Equiv σ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (by
    intro g
    apply LinearMap.ext
    intro v
    exact Subtype.ext (h g v).symm)

/-- Reindex a product of representations. -/
def sumReindexEquiv {G I J : Type*} [Monoid G] {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (e : J ≃ I) :
    (branchingSumRepresentation ρ).Equiv (branchingSumRepresentation (fun j => ρ (e j))) :=
  Representation.Equiv.mk (LinearEquiv.piCongrLeft' ℂ V e.symm) (by
    intro g
    apply LinearMap.ext
    intro v
    rfl)

/-- Apply an equivariant equivalence in every coordinate. -/
def sumCoordinateEquiv {G I : Type*} [Monoid G] {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (σ : ∀ i, Representation ℂ G (W i))
    (e : ∀ i, (ρ i).Equiv (σ i)) :
    (branchingSumRepresentation ρ).Equiv (branchingSumRepresentation σ) :=
  Representation.Equiv.mk (LinearEquiv.piCongrRight (fun i => (e i).toLinearEquiv)) (by
    intro g
    apply LinearMap.ext
    intro v
    funext i
    exact Representation.IntertwiningMap.isIntertwining _ _ (e i).toIntertwiningMap g (v i))

/-- Coordinatewise equivalences also act on a binary direct sum. -/
def productRepresentationEquiv {G V₁ V₂ W₁ W₂ : Type*} [Monoid G]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ G W₁} {σ₂ : Representation ℂ G W₂}
    (e : ρ₁.Equiv σ₁) (f : ρ₂.Equiv σ₂) : (ρ₁.prod ρ₂).Equiv (σ₁.prod σ₂) :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v.1
    · exact Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g v.2)

def sumUnitSpechtEquiv {n : ℕ} (p : Partition n) :
    (branchingSumRepresentation (fun _ : Unit => branchingSpecht p)).Equiv (branchingSpecht p) :=
  Representation.Equiv.mk (LinearEquiv.funUnique Unit ℂ (SpechtModule p)) (by
    intro g
    apply LinearMap.ext
    intro v
    rfl)

def sumTwoSpechtEquiv {n : ℕ} (p : Fin 2 → Partition n) :
    (branchingSumRepresentation (fun i => branchingSpecht (p i))).Equiv
      ((branchingSpecht (p 0)).prod (branchingSpecht (p 1))) :=
  Representation.Equiv.mk (LinearEquiv.piFinTwo ℂ (fun i => SpechtModule (p i))) (by
    intro g
    apply LinearMap.ext
    intro v
    rfl)

def sumOptionSpechtEquiv {n : ℕ} (p : Option (Fin 2) → Partition n) :
    (branchingSumRepresentation (fun i => branchingSpecht (p i))).Equiv
      ((branchingSpecht (p none)).prod
        (branchingSumRepresentation (fun i => branchingSpecht (p (some i))))) :=
  Representation.Equiv.mk (LinearEquiv.piOptionEquivProd ℂ) (by
    intro g
    apply LinearMap.ext
    intro v
    rfl)

theorem restriction22 : Specs.AdvancedFiniteGroupRepresentations.restriction22Type := by
  intro σ τ hσ hτ
  obtain ⟨e⟩ := restriction_branching partition22 σ hσ
    (fun c => branchingSpecht (deleteCell partition22 c)) (fun _ _ _ => rfl)
  let e₁ := sumReindexEquiv (fun c => branchingSpecht (deleteCell partition22 c)) squareCornerEquiv
  let e₂ := sumCoordinateEquiv _ _ (fun i => spechtEquivOfEq (square_deletion i))
  exact ⟨e.trans (e₁.trans (e₂.trans ((sumUnitSpechtEquiv partition21).trans
    (spechtInheritedEquiv τ hτ))))⟩

theorem restriction31 : Specs.AdvancedFiniteGroupRepresentations.restriction31Type := by
  intro σ τ υ hσ hτ hυ
  obtain ⟨e⟩ := restriction_branching partition31 σ hσ
    (fun c => branchingSpecht (deleteCell partition31 c)) (fun _ _ _ => rfl)
  let e₁ := sumReindexEquiv (fun c => branchingSpecht (deleteCell partition31 c)) corner31Equiv
  let e₂ := sumCoordinateEquiv _ _ (fun i => spechtEquivOfEq (deletion31 i))
  let e₃ := sumTwoSpechtEquiv restriction31Shape
  have e₄ : ((branchingSpecht (restriction31Shape 0)).prod
      (branchingSpecht (restriction31Shape 1))).Equiv (τ.prod υ) := by
    change ((branchingSpecht partition3).prod (branchingSpecht partition21)).Equiv (τ.prod υ)
    exact productRepresentationEquiv (spechtInheritedEquiv τ hτ) (spechtInheritedEquiv υ hυ)
  exact ⟨e.trans (e₁.trans (e₂.trans (e₃.trans e₄)))⟩

theorem lastLabelSubgroup3_index : (lastLabelSubgroup 3).index = 4 := by
  rw [Subgroup.index_eq_card_div, ← Nat.card_congr (lastLabelEquiv 3).toEquiv]
  norm_num [Nat.card_eq_fintype_card, SymmetricGroup,
    Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup, Fintype.card_perm]

theorem small_induction_dimension_check :
    Specs.AdvancedFiniteGroupRepresentations.small_induction_dimension_checkType := by
  obtain ⟨h22,h31,h211,h21,h3⟩ := small_diagram_dimensions
  exact ⟨lastLabelSubgroup3_index, by simp [Module.finrank_prod, h22, h31, h211], by
    rw [h22, h31, h211, h21, lastLabelSubgroup3_index]⟩

attribute [local instance] P103.Ch09.rightSubgroupModule
  P103.Ch09.inducedAlgebraModule P103.Ch09.inducedScalarModule

/-- Reverse branching, with all three addable shapes and their full actions. -/
theorem induction21 : Specs.AdvancedFiniteGroupRepresentations.induction21Type := by
  intro σ τ υ ω hσ hτ hυ hω
  obtain ⟨E,hE,⟨e⟩⟩ := induction_branching partition21 σ hσ
    (fun c => branchingSpecht (addCell partition21 c)) (fun _ _ _ => rfl)
  let e₁ := sumReindexEquiv (fun c => branchingSpecht (addCell partition21 c)) added21Equiv
  let e₂ := sumCoordinateEquiv _ _ (fun i => spechtEquivOfEq (addition21 i))
  let e₃ := sumOptionSpechtEquiv induction21Shape
  let e₄ := productRepresentationEquiv (Representation.Equiv.refl (branchingSpecht partition31))
    (sumTwoSpechtEquiv (fun i => induction21Shape (some i)))
  have e₅ : ((branchingSpecht (induction21Shape none)).prod
      ((branchingSpecht (induction21Shape (some 0))).prod
        (branchingSpecht (induction21Shape (some 1))))).Equiv (τ.prod (υ.prod ω)) := by
    change ((branchingSpecht partition31).prod
      ((branchingSpecht partition22).prod (branchingSpecht partition211))).Equiv _
    exact productRepresentationEquiv (spechtInheritedEquiv τ hτ)
      (productRepresentationEquiv (spechtInheritedEquiv υ hυ) (spechtInheritedEquiv ω hω))
  have f : (P103.Ch09.induction (lastLabelSubgroup 3)
      (σ.comp E.symm.toMonoidHom)).Equiv (τ.prod (υ.prod ω)) :=
    e.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))))
  exact ⟨E, hE, ⟨f⟩, f.toLinearEquiv.finrank_eq.trans small_induction_dimension_check.2.1⟩

end AdvancedFiniteGroupRepresentations
