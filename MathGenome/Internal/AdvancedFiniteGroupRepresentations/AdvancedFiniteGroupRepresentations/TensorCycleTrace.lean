import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CycleTypes
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorCycleTrace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.GroupTheory.Perm.Cycle.Concrete

noncomputable section
open scoped BigOperators
universe u v
namespace AdvancedFiniteGroupRepresentations

abbrev cycleTraceProduct := @Specs.AdvancedFiniteGroupRepresentations.cycleTraceProduct

/-- Relabeling the positions preserves the matrix contraction. -/
theorem matrix_contraction_reindex {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α] [DecidableEq β]
    (M : Matrix ι ι ℂ) (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (e : α ≃ β) (h : ∀ j, e (σ j) = τ (e j)) :
    (∑ a : α → ι, ∏ j, M (a (σ j)) (a j)) =
      ∑ a : β → ι, ∏ j, M (a (τ j)) (a j) := by
  classical
  apply Fintype.sum_equiv (e.arrowCongr (Equiv.refl ι))
  intro a
  apply Fintype.prod_equiv e
  intro j
  change M (a (σ j)) (a j) = M (a (e.symm (τ (e j)))) (a (e.symm (e j)))
  rw [← h j, e.symm_apply_apply, e.symm_apply_apply]

/-- Independent position blocks give independent factors in the finite sum. -/
theorem cyclic_block_contraction_factor {κ ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι]
    (sizes : κ → ℕ) (M : Matrix ι ι ℂ) :
    (∑ a : (Σ i, Fin (sizes i)) → ι,
      ∏ j : (Σ i, Fin (sizes i)),
        M (a ⟨j.1, finRotate (sizes j.1) j.2⟩) (a j)) =
      ∏ i, ∑ a : Fin (sizes i) → ι,
        ∏ j, M (a (finRotate (sizes i) j)) (a j) := by
  classical
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piCurry (fun i (_ : Fin (sizes i)) => ι))
  intro a
  exact Fintype.prod_sigma _

/-- Convert any cyclic coordinate system into the desired contraction,
provided the contraction in disjoint cyclic blocks has been evaluated. -/
theorem matrix_contraction_of_cycle_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (n : ℕ) (σ : SymmetricGroup n) (l : List ℕ)
    (hl : (l : Multiset ℕ) = (cyclePartition σ).parts)
    (e : Fin n ≃ (Σ i : Fin l.length, Fin (l.get i)))
    (he : ∀ j, e (σ j) = ⟨(e j).1, finRotate (l.get (e j).1) (e j).2⟩)
    (hb : (∑ a : (Σ i : Fin l.length, Fin (l.get i)) → ι,
      ∏ j : (Σ i : Fin l.length, Fin (l.get i)),
        M (a ⟨j.1, finRotate (l.get j.1) j.2⟩) (a j)) =
      ((l : Multiset ℕ).map (fun k => Matrix.trace (M ^ k))).prod) :
    (∑ a : Fin n → ι, ∏ j, M (a (σ j)) (a j)) =
      ((cyclePartition σ).parts.map (fun k => Matrix.trace (M ^ k))).prod := by
  classical
  let τ : Equiv.Perm (Σ i : Fin l.length, Fin (l.get i)) :=
    Equiv.sigmaCongrRight (fun i => finRotate (l.get i))
  rw [matrix_contraction_reindex M σ τ e he]
  change (∑ a : (Σ i : Fin l.length, Fin (l.get i)) → ι,
    ∏ j : (Σ i : Fin l.length, Fin (l.get i)),
      M (a ⟨j.1, finRotate (l.get j.1) j.2⟩) (a j)) = _
  rw [hb, hl]


theorem sum_fin_cons {ι : Type*} [Fintype ι] (r : ℕ) (f : (Fin (r+1) → ι) → ℂ) :
    (∑ a, f a) = ∑ x, ∑ w : Fin r → ι, f (@Fin.cons r (fun _ => ι) x w) := by
  calc
    _ = ∑ p : ι × (Fin r → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ => ι)).symm _ _ (by intro a; simp)
    _ = _ := Fintype.sum_prod_type _

theorem matrix_power_paths {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (r : ℕ) (x y : ι) :
    (M^(r+1)) y x = ∑ w : Fin r → ι,
      (∏ j : Fin r, M ((@Fin.cons r (fun _ => ι) x w) j.succ) ((@Fin.cons r (fun _ => ι) x w) j.castSucc)) *
        M y ((@Fin.cons r (fun _ => ι) x w) (Fin.last r)) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Matrix.mul_apply, sum_fin_cons]
    simp_rw [ih, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro w _
    simp [Fin.prod_univ_succ, Fin.castSucc_succ, mul_comm, mul_left_comm]

theorem cyclic_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (k : ℕ) (hk : 0 < k) :
    (∑ a : Fin k → ι, ∏ j, M (a (finRotate k j)) (a j)) = Matrix.trace (M^k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [sum_fin_cons]
  change (∑ x : ι, ∑ w : Fin r → ι, ∏ j : Fin (r+1),
    M ((@Fin.cons r (fun _ => ι) x w) (finRotate (r+1) j))
      ((@Fin.cons r (fun _ => ι) x w) j)) = ∑ x : ι, (M^(r+1)) x x
  apply Finset.sum_congr rfl
  intro x _
  rw [matrix_power_paths]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fin.prod_univ_castSucc]
  simp only [finRotate_last, Fin.cons_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have h : finRotate (r+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  rw [h]

open Equiv.Perm

lemma list_get_rotate {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (i : Fin l.length) :
    l.get (finRotate l.length i) = l.next (l.get i) (List.get_mem ..) := by
  have : NeZero l.length := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  simp only [List.get_eq_getElem, List.next_getElem l hl, finRotate_apply,
    Fin.val_add, Fin.val_one', Nat.add_mod_mod]

def cycleStart {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) : α := hc.nonempty_support.choose

lemma cycleStart_mem {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) : cycleStart c hc ∈ c.support :=
  hc.nonempty_support.choose_spec

def cycleList {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) : List α := c.toList (cycleStart c hc)

lemma cycleList_length {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) : (cycleList c hc).length = c.support.card := by
  rw [cycleList, length_toList, hc.cycleOf_eq (mem_support.mp (cycleStart_mem c hc))]

lemma cycleList_nodup {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) : (cycleList c hc).Nodup := nodup_toList ..

lemma mem_cycleList {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) (x : α) : x ∈ cycleList c hc ↔ x ∈ c.support := by
  rw [cycleList, mem_toList_iff]
  constructor
  · intro h
    exact h.1.mem_support_iff.mp h.2
  · intro hx
    exact ⟨hc.sameCycle (mem_support.mp (cycleStart_mem c hc)) (mem_support.mp hx),
      cycleStart_mem c hc⟩

lemma cycleList_rotate {α : Type*} [Fintype α] [DecidableEq α]
    (c : Equiv.Perm α) (hc : c.IsCycle) (i : Fin (cycleList c hc).length) :
    (cycleList c hc).get (finRotate _ i) = c ((cycleList c hc).get i) := by
  rw [list_get_rotate _ (cycleList_nodup c hc)]
  exact next_toList_eq_apply ..

abbrev CycleIndex {n : ℕ} (σ : SymmetricGroup n) :=
  σ.cycleFactorsFinset ⊕ Function.fixedPoints σ

def cycleBlock {n : ℕ} (σ : SymmetricGroup n) : CycleIndex σ → List (Fin n)
  | Sum.inl c => cycleList c.val (mem_cycleFactorsFinset_iff.mp c.property).1
  | Sum.inr x => [x.val]

lemma cycleBlock_nodup {n : ℕ} (σ : SymmetricGroup n) (c : CycleIndex σ) :
    (cycleBlock σ c).Nodup := by
  cases c with
  | inl c => exact cycleList_nodup ..
  | inr x => exact List.nodup_singleton _

lemma cycleBlock_pos {n : ℕ} (σ : SymmetricGroup n) (c : CycleIndex σ) :
    0 < (cycleBlock σ c).length := by
  cases c with
  | inl c =>
    rw [cycleBlock, cycleList_length]
    exact lt_of_lt_of_le (by decide : 0 < 2)
      (mem_cycleFactorsFinset_iff.mp c.property).1.two_le_card_support
  | inr x => exact Nat.zero_lt_succ _

lemma cycleBlock_rotate {n : ℕ} (σ : SymmetricGroup n) (c : CycleIndex σ)
    (i : Fin (cycleBlock σ c).length) :
    (cycleBlock σ c).get (finRotate _ i) = σ ((cycleBlock σ c).get i) := by
  cases c with
  | inl c =>
    dsimp only [cycleBlock] at i
    change (cycleList c.val _).get (finRotate _ i) = σ ((cycleList c.val _).get i)
    rw [cycleList_rotate]
    apply (mem_cycleFactorsFinset_iff.mp c.property).2
    exact (mem_cycleList _ _ _).mp (List.get_mem ..)
  | inr x =>
    change Fin 1 at i
    change [x.val].get (finRotate _ i) = σ ([x.val].get i)
    have hi : i = (⟨0, by decide⟩ : Fin 1) := @Subsingleton.elim (Fin 1) _ _ _
    subst i
    exact x.property.symm

lemma cycleBlock_bijective {n : ℕ} (σ : SymmetricGroup n) :
    Function.Bijective (fun p : Σ c : CycleIndex σ, Fin (cycleBlock σ c).length =>
      (cycleBlock σ p.1).get p.2) := by
  constructor
  · rintro ⟨a, i⟩ ⟨b, j⟩ h
    dsimp only at h
    cases a with
    | inl a =>
      have hi : (cycleBlock σ (Sum.inl a)).get i ∈ a.val.support :=
        (mem_cycleList _ _ _).mp (List.get_mem ..)
      cases b with
      | inl b =>
        have hj : (cycleBlock σ (Sum.inl b)).get j ∈ b.val.support :=
          (mem_cycleList _ _ _).mp (List.get_mem ..)
        have hab : a = b := by
          apply Subtype.ext
          rw [cycle_is_cycleOf hi a.property, cycle_is_cycleOf hj b.property, h]
        subst b
        have hij : i = j := (List.nodup_iff_injective_get.mp (cycleBlock_nodup σ (Sum.inl a))) h
        subst j
        rfl
      | inr b =>
        have hb : (cycleBlock σ (Sum.inr b)).get j = b.val := by
          have hj : j = (⟨0, by decide⟩ : Fin 1) := @Subsingleton.elim (Fin 1) _ _ _
          subst j
          rfl
        have hn := mem_cycleFactorsFinset_support_le a.property hi
        rw [h, hb, mem_support] at hn
        exact (hn b.property).elim
    | inr a =>
      have ha : (cycleBlock σ (Sum.inr a)).get i = a.val := by
        have hi : i = (⟨0, by decide⟩ : Fin 1) := @Subsingleton.elim (Fin 1) _ _ _
        subst i
        rfl
      cases b with
      | inl b =>
        have hj : (cycleBlock σ (Sum.inl b)).get j ∈ b.val.support :=
          (mem_cycleList _ _ _).mp (List.get_mem ..)
        have hn := mem_cycleFactorsFinset_support_le b.property hj
        rw [← h, ha, mem_support] at hn
        exact (hn a.property).elim
      | inr b =>
        have hb : (cycleBlock σ (Sum.inr b)).get j = b.val := by
          have hj : j = (⟨0, by decide⟩ : Fin 1) := @Subsingleton.elim (Fin 1) _ _ _
          subst j
          rfl
        have hab : a = b := Subtype.ext (ha.symm.trans (h.trans hb))
        subst b
        have hij : i = j := @Subsingleton.elim (Fin 1) _ i j
        subst j
        rfl
  · intro x
    by_cases hx : σ x = x
    · exact ⟨⟨Sum.inr ⟨x, hx⟩, ⟨0, by change 0 < 1; decide⟩⟩, rfl⟩
    · let c : σ.cycleFactorsFinset := ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr
        (mem_support.mpr hx)⟩
      have hxc : x ∈ c.val.support := by
        dsimp [c]
        simpa only [mem_support, cycleOf_apply_self] using hx
      have hxl : x ∈ cycleBlock σ (Sum.inl c) := (mem_cycleList _ _ _).mpr hxc
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxl
      exact ⟨⟨Sum.inl c, i⟩, hi⟩


theorem cycleBlock_product {n : ℕ} (σ : SymmetricGroup n) (f : ℕ → ℂ) :
    (∏ c : CycleIndex σ, f (cycleBlock σ c).length) =
      ((cyclePartition σ).parts.map f).prod := by
  classical
  rw [Fintype.prod_sum_type]
  simp only [cycleBlock, cycleList_length, List.length_singleton, Finset.prod_const,
    Finset.card_univ]
  rw [cyclePartition_parts, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    Fintype.card_fin]
  congr 1
  rw [Finset.prod_coe_sort σ.cycleFactorsFinset (fun c => f c.support.card),
    Finset.prod_eq_multiset_prod, Equiv.Perm.cycleType_def,
    Multiset.map_map]
  rfl

/-- The finite matrix contraction factors over all cycles, including fixed points. -/
theorem matrix_contraction_cycles {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (n : ℕ) (σ : SymmetricGroup n) :
    (∑ a : Fin n → ι, ∏ j, M (a (σ j)) (a j)) =
      ((cyclePartition σ).parts.map (fun k => Matrix.trace (M ^ k))).prod := by
  classical
  let sizes : CycleIndex σ → ℕ := fun c => (cycleBlock σ c).length
  let τ : Equiv.Perm (Σ c : CycleIndex σ, Fin (sizes c)) :=
    Equiv.sigmaCongrRight (fun c => finRotate (sizes c))
  let e : (Σ c : CycleIndex σ, Fin (sizes c)) ≃ Fin n :=
    Equiv.ofBijective (fun p => (cycleBlock σ p.1).get p.2) (cycleBlock_bijective σ)
  have he : ∀ j, e (τ j) = σ (e j) := by
    intro ⟨c, i⟩
    exact cycleBlock_rotate σ c i
  rw [← matrix_contraction_reindex M τ σ e he]
  change (∑ a : (Σ c : CycleIndex σ, Fin (sizes c)) → ι,
    ∏ j : (Σ c : CycleIndex σ, Fin (sizes c)),
      M (a ⟨j.1, finRotate (sizes j.1) j.2⟩) (a j)) = _
  rw [cyclic_block_contraction_factor]
  calc
    _ = ∏ c : CycleIndex σ, Matrix.trace (M ^ sizes c) := by
      apply Finset.prod_congr rfl
      intro c _
      exact cyclic_contraction M _ (cycleBlock_pos σ c)
    _ = _ := cycleBlock_product σ (fun k => Matrix.trace (M^k))

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- All matrix coefficients of the product action in the tensor basis.
The permutation convention is output `σ j`, input `j`. -/
theorem tensor_action_matrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V)
    (a c : Fin n → ι) :
    LinearMap.toMatrix (Basis.piTensorProduct (fun _ : Fin n => b))
      (Basis.piTensorProduct (fun _ : Fin n => b))
      (slotOperator V n σ * diagonalOperator V n g) a c =
      ∏ j, LinearMap.toMatrix b b g.toLinearMap (a (σ j)) (c j) := by
  classical
  rw [LinearMap.toMatrix_apply, Basis.piTensorProduct_apply]
  change (Basis.piTensorProduct (fun _ : Fin n => b)).repr
    (slotOperator V n σ (diagonalOperator V n g (pureTensor V n (fun j => b (c j))))) a = _
  rw [diagonal_pureTensor, slot_pureTensor]
  change (Basis.piTensorProduct (fun _ : Fin n => b)).repr
    (PiTensorProduct.tprod ℂ (fun i => g (b (c (σ⁻¹ i))))) a = _
  rw [Basis.piTensorProduct_repr_tprod_apply]
  exact Fintype.prod_equiv σ.symm (fun j => b.repr (g (b (c (σ⁻¹ j)))) (a j))
    (fun j => LinearMap.toMatrix b b g.toLinearMap (a (σ j)) (c j))
    (by intro j; simp [LinearMap.toMatrix_apply])

/-- The tensor trace is the finite matrix contraction, without any
assumption on the Jordan form of `g`. -/
theorem tensor_trace_matrix_sum {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V) :
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) =
      ∑ a : Fin n → ι, ∏ j, LinearMap.toMatrix b b g.toLinearMap (a (σ j)) (a j) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.piTensorProduct (fun _ : Fin n => b))]
  unfold Matrix.trace
  exact Finset.sum_congr rfl (fun a _ => tensor_action_matrix V b n σ g a a)

theorem tensor_cycle_trace_zero [FiniteDimensional ℂ V]
    (σ : SymmetricGroup 0) (g : LinearGroup V) :
    LinearMap.trace ℂ (TensorPower V 0)
      (slotOperator V 0 σ * diagonalOperator V 0 g) = 1 ∧
      cycleTraceProduct V σ g = 1 := by
  constructor
  · rw [slot_zero, diagonal_zero, one_mul, LinearMap.trace_one]
    rw [(tensorPowerZeroEquiv V).finrank_eq]
    simp
  · simp [cycleTraceProduct, Specs.AdvancedFiniteGroupRepresentations.cycleTraceProduct,
      zero_cyclePartition, emptyPartition, Specs.AdvancedFiniteGroupRepresentations.emptyPartition]

theorem tensor_cycle_trace_zero_dimension [FiniteDimensional ℂ V]
    (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) :
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) = 0 ∧
      cycleTraceProduct V σ g = 0 := by
  let := tensorPower_zero_dimension V n hn hd
  let : Subsingleton V := (Module.finrank_zero_iff (R := ℂ) (M := V)).mp hd
  have ht (k : ℕ) : LinearMap.trace ℂ V (g.toLinearMap ^ k) = 0 := by
    have h : g.toLinearMap ^ k = 0 := Subsingleton.elim _ _
    rw [h, map_zero]
  constructor
  · have h : slotOperator V n σ * diagonalOperator V n g = 0 := Subsingleton.elim _ _
    rw [h, map_zero]
  · have hp : (cyclePartition σ).parts ≠ 0 := by
      intro h
      have hs := (cyclePartition σ).parts_sum
      rw [h, Multiset.sum_zero] at hs
      omega
    obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero hp
    apply Multiset.prod_eq_zero_iff.mpr
    exact Multiset.mem_map.mpr ⟨k, hk, ht k⟩

/-- Assembly of the tensor calculation from a finite matrix contraction identity.
This lemma also records the precise bridge between matrix powers and powers
of the original linear map. -/
theorem tensor_cycle_trace_of_matrix_contraction [FiniteDimensional ℂ V]
    (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V)
    (h : ∀ (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ),
      (∑ a : Fin n → Fin d, ∏ j, M (a (σ j)) (a j)) =
        ((cyclePartition σ).parts.map (fun k => Matrix.trace (M ^ k))).prod) :
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) = cycleTraceProduct V σ g := by
  classical
  let b := Module.finBasis ℂ V
  rw [tensor_trace_matrix_sum V b, h]
  change ((cyclePartition σ).parts.map (fun k =>
    Matrix.trace (LinearMap.toMatrix b b g.toLinearMap ^ k))).prod =
    ((cyclePartition σ).parts.map (fun k => LinearMap.trace ℂ V (g.toLinearMap ^ k))).prod
  congr 1
  apply Multiset.map_congr rfl
  intro k _
  rw [LinearMap.toMatrix_pow, LinearMap.trace_eq_matrix_trace ℂ b]

/-- FR-D07, first identity, for arbitrary invertible `g`. -/
theorem tensor_cycle_trace [FiniteDimensional ℂ V]
    (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V) :
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) = cycleTraceProduct V σ g := by
  apply tensor_cycle_trace_of_matrix_contraction V n σ g
  intro d M
  exact matrix_contraction_cycles M n σ

end AdvancedFiniteGroupRepresentations
