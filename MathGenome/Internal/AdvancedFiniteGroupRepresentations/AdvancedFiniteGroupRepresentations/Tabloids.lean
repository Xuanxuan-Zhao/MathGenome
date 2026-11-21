import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Partitions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Tabloids
import Mathlib.GroupTheory.Perm.DomMulAct
import MathGenome.Internal.AlgebraCore.P103.Ch09.InductionStages

noncomputable section
open scoped MonoidAlgebra
namespace AdvancedFiniteGroupRepresentations

abbrev tableauAction := @Specs.AdvancedFiniteGroupRepresentations.tableauAction
abbrev tabloidAction := @Specs.AdvancedFiniteGroupRepresentations.tabloidAction
abbrev Tableau := @Specs.AdvancedFiniteGroupRepresentations.Tableau
abbrev canonicalTableau := @Specs.AdvancedFiniteGroupRepresentations.canonicalTableau
abbrev emptyTableau := Specs.AdvancedFiniteGroupRepresentations.emptyTableau
abbrev emptyTabloid := Specs.AdvancedFiniteGroupRepresentations.emptyTabloid
abbrev labelRow := @Specs.AdvancedFiniteGroupRepresentations.labelRow
abbrev labelColumn := @Specs.AdvancedFiniteGroupRepresentations.labelColumn
abbrev rowLabels := @Specs.AdvancedFiniteGroupRepresentations.rowLabels
abbrev columnLabels := @Specs.AdvancedFiniteGroupRepresentations.columnLabels
abbrev Tabloid := @Specs.AdvancedFiniteGroupRepresentations.Tabloid
abbrev tabloid := @Specs.AdvancedFiniteGroupRepresentations.tabloid
abbrev rowSubgroup := @Specs.AdvancedFiniteGroupRepresentations.rowSubgroup
abbrev columnSubgroup := @Specs.AdvancedFiniteGroupRepresentations.columnSubgroup
abbrev PermutationModule := @Specs.AdvancedFiniteGroupRepresentations.PermutationModule
abbrev permutationRepresentation := @Specs.AdvancedFiniteGroupRepresentations.permutationRepresentation
abbrev InducedRow := @Specs.AdvancedFiniteGroupRepresentations.InducedRow
abbrev inducedRepresentation := @Specs.AdvancedFiniteGroupRepresentations.inducedRepresentation
abbrev rowTensor := @Specs.AdvancedFiniteGroupRepresentations.rowTensor

variable {n : ℕ} {p : Partition n}

@[simp] theorem tableau_smul_apply (g : SymmetricGroup n) (t : Tableau p) (c : Cell p) :
    (g • t) c = g (t c) := rfl

@[simp] theorem labelRow_smul (g : SymmetricGroup n) (t : Tableau p) (a : Fin n) :
    labelRow (g • t) a = labelRow t (g.symm a) := rfl

@[simp] theorem tabloid_smul (g : SymmetricGroup n) (t : Tableau p) :
    g • tabloid t = tabloid (g • t) := rfl

/-- Includes the empty diagram: a diagram has exactly n cells. -/
theorem tableau_nonempty (p : Partition n) : Nonempty (Tableau p) := by
  have h : Fintype.card (Cell p) = n := by
    change Fintype.card {c // c ∈ cells p} = n
    rw [Fintype.card_coe]
    exact diagram_card p
  exact ⟨Fintype.equivFinOfCardEq h⟩

/-- Relabeling is a free transitive left action. -/
theorem tableau_existsUnique (t u : Tableau p) : ∃! g : SymmetricGroup n, g • t = u := by
  refine ⟨t.symm.trans u, ?_, ?_⟩
  · ext c
    simp
  · intro g hg
    apply Equiv.ext
    intro a
    have h := congrArg (fun v : Tableau p => v (t.symm a)) hg
    simpa using h

theorem tabloid_eq_iff (t u : Tableau p) :
    tabloid t = tabloid u ↔ ∀ i, rowLabels t i = rowLabels u i := by
  change (Quotient.mk _ t = Quotient.mk _ u) ↔ _
  rw [Quotient.eq]
  change (labelRow t = labelRow u) ↔ _
  constructor
  · intro h i
    apply Set.ext
    intro a
    exact (congrArg (· = i) (congrFun h a)).to_iff
  · intro h
    funext a
    have := congrArg (fun s : Set (Fin n) => a ∈ s) (h (labelRow t a))
    exact (eq_iff_iff.mp this).mp rfl |>.symm

@[simp] theorem mem_rowSubgroup (t : Tableau p) (g : SymmetricGroup n) :
    g ∈ rowSubgroup t ↔ ∀ a, labelRow t (g a) = labelRow t a := Iff.rfl

@[simp] theorem mem_columnSubgroup (t : Tableau p) (g : SymmetricGroup n) :
    g ∈ columnSubgroup t ↔ ∀ a, labelColumn t (g a) = labelColumn t a := Iff.rfl

/-- Setwise preservation of every row set, in both directions. -/
theorem rowSubgroup_iff (t : Tableau p) (g : SymmetricGroup n) :
    g ∈ rowSubgroup t ↔ ∀ i a, g a ∈ rowLabels t i ↔ a ∈ rowLabels t i := by
  constructor
  · intro h i a
    change labelRow t (g a) = i ↔ labelRow t a = i
    exact (congrArg (· = i) (h a)).to_iff
  · intro h a
    exact (h (labelRow t a) a).mpr rfl

theorem columnSubgroup_iff (t : Tableau p) (g : SymmetricGroup n) :
    g ∈ columnSubgroup t ↔ ∀ j a, g a ∈ columnLabels t j ↔ a ∈ columnLabels t j := by
  constructor
  · intro h j a
    change labelColumn t (g a) = j ↔ labelColumn t a = j
    exact (congrArg (· = j) (h a)).to_iff
  · intro h a
    exact (h (labelColumn t a) a).mpr rfl

theorem tabloid_stabilizer (t : Tableau p) :
    MulAction.stabilizer (SymmetricGroup n) (tabloid t) = rowSubgroup t := by
  ext g
  rw [MulAction.mem_stabilizer_iff, tabloid_smul]
  change (Quotient.mk _ (g • t) = Quotient.mk _ t) ↔ _
  rw [Quotient.eq]
  change (labelRow (g • t) = labelRow t) ↔ _
  constructor
  · intro h a
    have hh := congrFun h (g a)
    simpa using hh.symm
  · intro h
    funext a
    exact (by simpa using (h (g.symm a)).symm)

theorem row_column_inf (t : Tableau p) : rowSubgroup t ⊓ columnSubgroup t = ⊥ := by
  apply le_antisymm
  · intro g hg
    change g = 1
    apply Equiv.ext
    intro a
    apply t.symm.injective
    apply Subtype.ext
    exact Prod.ext (hg.1 a) (hg.2 a)
  · exact bot_le

/-- A row's label set has precisely the original part size. -/
private def rowLabelsEquivFin (t : Tableau p) (i : ℕ) :
    rowLabels t i ≃ Fin (rowLength p i) where
  toFun a := ⟨(t.symm a.val).val.2, by
    have hc := (t.symm a.val).property
    have hr : (t.symm a.val).val.1 = i := a.property
    have h := (cell_iff p _ _).mp hc
    simpa only [hr] using h⟩
  invFun j := ⟨t ⟨(i, j.val), (cell_iff p i j.val).mpr j.isLt⟩, by
    change (t.symm (t _)).val.1 = i
    simp⟩
  left_inv a := by
    apply Subtype.ext
    apply t.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact a.property.symm
    · rfl
  right_inv j := by
    apply Fin.ext
    simp

theorem rowLabels_card (t : Tableau p) (i : ℕ) :
    Nat.card (rowLabels t i) = rowLength p i := by
  rw [Nat.card_congr (rowLabelsEquivFin t i), Nat.card_fin]

/-- Each factor permutes the labels in the indicated ordered row.
The factors for empty rows are trivial. -/
theorem rowSubgroup_product (t : Tableau p) :
    ∃ e : rowSubgroup t ≃* (∀ i : ℕ, Equiv.Perm (rowLabels t i)),
      ∀ g i a, ((e g) i a).val = g.val a := by
  let f := labelRow t
  let e : rowSubgroup t ≃* (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ f)ᵐᵒᵖ :=
    { toFun := fun g => MulOpposite.op ⟨DomMulAct.mk g.val, by
        rw [DomMulAct.mem_stabilizer_iff]
        exact funext g.property⟩
      invFun := fun g => ⟨DomMulAct.mk.symm g.unop.val, by
        have h := DomMulAct.mem_stabilizer_iff.mp g.unop.property
        exact congrFun h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨e.trans (DomMulAct.stabilizerMulEquiv f), ?_⟩
  intro g i a
  rfl


private theorem rowLabels_isEmpty (t : Tableau p) (i : ℕ) (hi : length p ≤ i) :
    IsEmpty (rowLabels t i) := by
  refine ⟨fun a => ?_⟩
  have hc := (cell_iff p _ _).mp (t.symm a.val).property
  have hr : (t.symm a.val).val.1 = i := a.property
  rw [hr, rowLength_zero_of_length_le p i hi] at hc
  exact Nat.not_lt_zero _ hc

/-- The product can be restricted to the finite set of nonempty rows. -/
theorem rowSubgroup_product_finite (t : Tableau p) :
    ∃ e : rowSubgroup t ≃* (∀ i : Fin (length p), Equiv.Perm (rowLabels t i)),
      ∀ g i a, ((e g) i a).val = g.val a := by
  classical
  obtain ⟨e, he⟩ := rowSubgroup_product t
  let restrictRows : (∀ i : ℕ, Equiv.Perm (rowLabels t i)) ≃*
      (∀ i : Fin (length p), Equiv.Perm (rowLabels t i)) :=
    { toFun := fun f i => f i
      invFun := fun f i => if h : i < length p then f ⟨i, h⟩ else 1
      left_inv := by
        intro f
        funext i
        dsimp
        split_ifs with hi
        · rfl
        · have := rowLabels_isEmpty t i (Nat.le_of_not_gt hi)
          exact Subsingleton.elim _ _
      right_inv := by
        intro f
        funext i
        dsimp
        simp only [ite_eq_left i.isLt]
      map_mul' := fun _ _ => rfl }
  exact ⟨e.trans restrictRows, fun g i a => he g i a⟩


attribute [local instance] P103.Ch09.rightSubgroupModule
  P103.Ch09.inducedAlgebraModule P103.Ch09.inducedScalarModule

private theorem rowTensor_eq (t : Tableau p) (g h : SymmetricGroup n) (z : ℂ)
    (heq : g • tabloid t = h • tabloid t) : rowTensor t g z = rowTensor t h z := by
  have hr : h⁻¹ * g ∈ rowSubgroup t := by
    rw [← tabloid_stabilizer, MulAction.mem_stabilizer_iff, mul_smul, heq]
    simp
  have hb := P103.Ch09.tensor_balance_group (rowSubgroup t)
    (Representation.trivial ℂ (rowSubgroup t) ℂ)
    (MonoidAlgebra.single h 1) ⟨h⁻¹ * g, hr⟩ z
  simp only [MonoidAlgebra.single_mul_single, mul_one, mul_inv_cancel_left] at hb
  exact hb

private def transportPermutation (t u : Tableau p) : SymmetricGroup n := t.symm.trans u

@[simp] private theorem transportPermutation_smul (t u : Tableau p) :
    transportPermutation t u • t = u := by
  ext c
  simp [transportPermutation]

private def tabloidTensor (t : Tableau p) (q : Tabloid p) : ℂ →ₗ[ℂ] InducedRow t :=
  Quotient.lift (fun u : Tableau p => P103.Ch09.tensorLinear (rowSubgroup t)
    (Representation.trivial ℂ (rowSubgroup t) ℂ)
      (MonoidAlgebra.single (transportPermutation t u) 1))
    (by
      intro u v huv
      apply LinearMap.ext
      intro z
      apply rowTensor_eq
      simp only [tabloid_smul, transportPermutation_smul]
      exact Quotient.sound huv) q

@[simp] private theorem tabloidTensor_tabloid (t u : Tableau p) (z : ℂ) :
    tabloidTensor t (tabloid u) z = rowTensor t (transportPermutation t u) z := rfl

private def inductionForward (t : Tableau p) : InducedRow t →ₗ[ℂ] PermutationModule p :=
  P103.Ch09.InductionStages.generatorLift (rowSubgroup t)
    (Representation.trivial ℂ (rowSubgroup t) ℂ)
    (fun g => (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      Finsupp.lsingle (tabloid (g • t)))
    (by
      intro g r z
      change MonoidAlgebra.single (tabloid ((g * r.val) • t)) z =
        MonoidAlgebra.single (tabloid (g • t)) z
      have hr : r.val • tabloid t = tabloid t := by
        rw [← MulAction.mem_stabilizer_iff, tabloid_stabilizer]
        exact r.property
      congr 1
      simp only [← tabloid_smul, mul_smul, hr])

@[simp] private theorem inductionForward_tensor (t : Tableau p) (g : SymmetricGroup n) (z : ℂ) :
    inductionForward t (rowTensor t g z) = MonoidAlgebra.single (tabloid (g • t)) z := by
  simp [rowTensor, Specs.AdvancedFiniteGroupRepresentations.rowTensor,
    inductionForward, P103.Ch09.InductionStages.generatorExtension]

private def inductionBackward (t : Tableau p) : PermutationModule p →ₗ[ℂ] InducedRow t :=
  (Finsupp.lsum ℂ (tabloidTensor t)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] private theorem inductionBackward_single (t : Tableau p) (q : Tabloid p) (z : ℂ) :
    inductionBackward t (MonoidAlgebra.single q z) = tabloidTensor t q z := by
  simp [inductionBackward]

private theorem inductionForward_backward (t : Tableau p) :
    inductionForward t ∘ₗ inductionBackward t = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn q (fun u => ?_)
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearMap.id_apply,
    inductionBackward_single]
  change inductionForward t (tabloidTensor t (tabloid u) z) = MonoidAlgebra.single (tabloid u) z
  simp

private theorem inductionBackward_forward (t : Tableau p) :
    inductionBackward t ∘ₗ inductionForward t = LinearMap.id := by
  apply P103.Ch09.induced_hom_ext (rowSubgroup t)
    (Representation.trivial ℂ (rowSubgroup t) ℂ)
  intro g z
  change inductionBackward t (inductionForward t (rowTensor t g z)) = rowTensor t g z
  simp only [inductionForward_tensor, inductionBackward_single, tabloidTensor_tabloid]
  apply rowTensor_eq
  simp

/-- The isomorphism from the source's left tensor induction model. -/
def inductionEquiv (t : Tableau p) : InducedRow t ≃ₗ[ℂ] PermutationModule p :=
  LinearEquiv.ofLinearMap (inductionForward t) (inductionBackward t)
    (inductionForward_backward t) (inductionBackward_forward t)

@[simp] theorem inductionEquiv_tensor (t : Tableau p) (g : SymmetricGroup n) (z : ℂ) :
    inductionEquiv t (rowTensor t g z) = MonoidAlgebra.single (tabloid (g • t)) z :=
  inductionForward_tensor t g z


/-- Intertwining for left multiplication on the tensor factor. -/
theorem inductionEquiv_equivariant (t : Tableau p) (g : SymmetricGroup n) (v : InducedRow t) :
    inductionEquiv t (inducedRepresentation t g v) =
      permutationRepresentation p g (inductionEquiv t v) := by
  have he : (inductionEquiv t).toLinearMap ∘ₗ inducedRepresentation t g =
      permutationRepresentation p g ∘ₗ (inductionEquiv t).toLinearMap := by
    apply P103.Ch09.induced_hom_ext (rowSubgroup t)
      (Representation.trivial ℂ (rowSubgroup t) ℂ)
    intro h z
    change inductionEquiv t (inducedRepresentation t g (rowTensor t h z)) =
      permutationRepresentation p g (inductionEquiv t (rowTensor t h z))
    change inductionEquiv t (P103.Ch09.tensor _ _
      (MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1) z) = _
    rw [MonoidAlgebra.single_mul_single, mul_one]
    change inductionEquiv t (rowTensor t (g * h) z) = _
    rw [inductionEquiv_tensor, inductionEquiv_tensor]
    change MonoidAlgebra.single (tabloid ((g * h) • t)) z =
      Representation.ofMulAction ℂ (SymmetricGroup n) (Tabloid p) g
        (MonoidAlgebra.single (tabloid (h • t)) z)
    rw [Representation.ofMulAction_single, tabloid_smul, mul_smul]
  exact congrArg (fun f : InducedRow t →ₗ[ℂ] PermutationModule p => f v) he

@[instance] theorem permutationModule_finiteDimensional (p : Partition n) :
    FiniteDimensional ℂ (PermutationModule p) := by
  exact Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm

theorem permutationRepresentation_basis (g : SymmetricGroup n) (q : Tabloid p) (z : ℂ) :
    permutationRepresentation p g (MonoidAlgebra.single q z) =
      MonoidAlgebra.single (g • q) z := Representation.ofMulAction_single g q z

theorem empty_tableau_unique (t : Tableau emptyPartition) : t = emptyTableau :=
  Subsingleton.elim _ _

theorem empty_tabloid_unique (q : Tabloid emptyPartition) : q = emptyTabloid :=
  Subsingleton.elim _ _

def emptyModuleEquiv : PermutationModule emptyPartition ≃ₗ[ℂ] ℂ := by
  letI : One (Tabloid emptyPartition) := ⟨emptyTabloid⟩
  exact MonoidAlgebra.uniqueLinearEquiv ℂ (Tabloid emptyPartition)

theorem emptyModule_finrank : Module.finrank ℂ (PermutationModule emptyPartition) = 1 := by
  rw [emptyModuleEquiv.finrank_eq]
  exact Module.finrank_self ℂ

theorem emptyModule_trivial (g : SymmetricGroup 0) (v : PermutationModule emptyPartition) :
    permutationRepresentation emptyPartition g v = v := by
  rw [zero_labels_trivial g, map_one]
  rfl


/-- The full source conclusion, including the normalization of the tensor map. -/
theorem induction_isomorphism (t : Tableau p) :
    ∃ e : InducedRow t ≃ₗ[ℂ] PermutationModule p,
      (∀ g z, e (rowTensor t g z) = MonoidAlgebra.single (tabloid (g • t)) z) ∧
      (∀ g v, e (inducedRepresentation t g v) = permutationRepresentation p g (e v)) :=
  ⟨inductionEquiv t, inductionEquiv_tensor t, inductionEquiv_equivariant t⟩

theorem empty_module_isomorphism :
    ∃ e : PermutationModule emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ z, e (MonoidAlgebra.single emptyTabloid z) = z := by
  refine ⟨emptyModuleEquiv, ?_⟩
  intro z
  change (MonoidAlgebra.single emptyTabloid z).coeff emptyTabloid = z
  simp

end AdvancedFiniteGroupRepresentations
