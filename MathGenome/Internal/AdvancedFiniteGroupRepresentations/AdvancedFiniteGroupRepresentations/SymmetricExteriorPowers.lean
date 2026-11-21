import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SymmetricExteriorPowers
import Mathlib.RepresentationTheory.Invariants
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.WeylDimension
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct DirectSum
universe u v
namespace AdvancedFiniteGroupRepresentations
abbrev tensorParity := @Specs.AdvancedFiniteGroupRepresentations.tensorParity
abbrev parityTensors := @Specs.AdvancedFiniteGroupRepresentations.parityTensors
abbrev parityRelations := @Specs.AdvancedFiniteGroupRepresentations.parityRelations
abbrev ParityPower := @Specs.AdvancedFiniteGroupRepresentations.ParityPower
abbrev SymmetricTensorPower := @Specs.AdvancedFiniteGroupRepresentations.SymmetricTensorPower
abbrev ExteriorTensorPower := @Specs.AdvancedFiniteGroupRepresentations.ExteriorTensorPower
abbrev parityPure := @Specs.AdvancedFiniteGroupRepresentations.parityPure
abbrev tensorAverage := @Specs.AdvancedFiniteGroupRepresentations.tensorAverage
abbrev parityPowerOperator := @Specs.AdvancedFiniteGroupRepresentations.parityPowerOperator

@[simp] theorem tensorParity_one (n : ℕ) (a : Bool) :
    tensorParity a (1 : SymmetricGroup n) = 1 := by
  cases a <;> simp [tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity]
@[simp] theorem tensorParity_mul {n : ℕ} (a : Bool) (s t : SymmetricGroup n) :
    tensorParity a (s * t) = tensorParity a s * tensorParity a t := by
  cases a <;> simp [tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity,
    permutationSign_mul]
@[simp] theorem tensorParity_sq {n : ℕ} (a : Bool) (s : SymmetricGroup n) :
    tensorParity a s * tensorParity a s = 1 := by
  cases a <;> simp [tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity,
    permutationSign_sq]

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

def paritySlotRepresentation (n : ℕ) (a : Bool) :
    Representation ℂ (SymmetricGroup n) (TensorPower V n) where
  toFun s := tensorParity a s • slotOperator V n s
  map_one' := by simp [slot_one]
  map_mul' s t := by simp [tensorParity_mul, slot_mul, smul_smul, mul_comm]

@[simp] theorem paritySlotRepresentation_apply (n : ℕ) (a : Bool)
    (s : SymmetricGroup n) (x : TensorPower V n) :
    paritySlotRepresentation V n a s x = tensorParity a s • slotOperator V n s x := rfl

theorem parityTensors_eq_invariants (n : ℕ) (a : Bool) :
    parityTensors V n a = (paritySlotRepresentation V n a).invariants := by
  ext x
  change (∀ s, slotOperator V n s x = tensorParity a s • x) ↔
    ∀ s, tensorParity a s • slotOperator V n s x = x
  constructor
  · intro h s
    rw [h s, smul_smul, tensorParity_sq, one_smul]
  · intro h s
    have hs := congrArg (tensorParity a s • ·) (h s)
    simpa only [smul_smul, tensorParity_sq, one_smul] using hs

theorem tensorAverage_eq_averageMap (n : ℕ) (a : Bool)
    [Invertible (Fintype.card (SymmetricGroup n) : ℂ)] :
    tensorAverage V n a = (paritySlotRepresentation V n a).averageMap := by
  have hc : Fintype.card (SymmetricGroup n) = n.factorial := by
    simp [SymmetricGroup, Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup,
      Fintype.card_perm]
  simp [tensorAverage, Specs.AdvancedFiniteGroupRepresentations.tensorAverage,
    Representation.averageMap, GroupAlgebra.average, map_sum, hc,
    paritySlotRepresentation, invOf_eq_inv]

theorem tensorAverage_mem (n : ℕ) (a : Bool) (x : TensorPower V n) :
    tensorAverage V n a x ∈ parityTensors V n a := by
  let : Invertible (Fintype.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  rw [parityTensors_eq_invariants, tensorAverage_eq_averageMap]
  exact Representation.averageMap_invariant _ x

theorem tensorAverage_id (n : ℕ) (a : Bool) (x : parityTensors V n a) :
    tensorAverage V n a x.val = x.val := by
  let : Invertible (Fintype.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  rw [tensorAverage_eq_averageMap]
  apply Representation.averageMap_id
  rw [← parityTensors_eq_invariants]
  exact x.property

theorem tensorAverage_paritySlot (n : ℕ) (a : Bool) (s : SymmetricGroup n)
    (x : TensorPower V n) :
    tensorAverage V n a (tensorParity a s • slotOperator V n s x) =
      tensorAverage V n a x := by
  let : Invertible (Fintype.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  rw [tensorAverage_eq_averageMap]
  let ρ := paritySlotRepresentation V n a
  change ρ.averageMap (ρ s x) = ρ.averageMap x
  change (ρ.asAlgebraHom (GroupAlgebra.average ℂ (SymmetricGroup n)) * ρ s) x = _
  rw [← Representation.asAlgebraHom_single_one, ← map_mul, GroupAlgebra.mul_average_right]
  rfl

theorem tensorAverage_kernel (n : ℕ) (a : Bool) :
    LinearMap.ker (tensorAverage V n a) = parityRelations V n a := by
  apply le_antisymm
  · intro x hx
    have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hc : Fintype.card (SymmetricGroup n) = n.factorial := by
      simp [SymmetricGroup, Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup,
        Fintype.card_perm]
    have hd : x - tensorAverage V n a x =
        (n.factorial : ℂ)⁻¹ • ∑ s : SymmetricGroup n,
          (x - tensorParity a s • slotOperator V n s x) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        hc, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne,
        one_smul, tensorAverage, Specs.AdvancedFiniteGroupRepresentations.tensorAverage,
        LinearMap.smul_apply, LinearMap.sum_apply]
    have hm : x - tensorAverage V n a x ∈ parityRelations V n a := by
      rw [hd]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro s _
      exact Submodule.subset_span ⟨s, x, rfl⟩
    simpa only [LinearMap.mem_ker.mp hx, sub_zero] using hm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, x, rfl⟩
    change tensorAverage V n a (x - tensorParity a s • slotOperator V n s x) = 0
    rw [map_sub, tensorAverage_paritySlot, sub_self]


/-- The averaging map, with precisely its natural codomain. -/
def tensorAverageToParity (n : ℕ) (a : Bool) :
    TensorPower V n →ₗ[ℂ] parityTensors V n a :=
  (tensorAverage V n a).codRestrict _ (tensorAverage_mem V n a)

def tensorAverageEquiv (n : ℕ) (a : Bool) :
    ParityPower V n a ≃ₗ[ℂ] parityTensors V n a where
  __ := (parityRelations V n a).liftQ (tensorAverageToParity V n a) (by
    intro x hx
    apply Subtype.ext
    exact (tensorAverage_kernel V n a ▸ hx : x ∈ LinearMap.ker (tensorAverage V n a)))
  invFun x := (parityRelations V n a).mkQ x.val
  left_inv q := by
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      change (parityRelations V n a).mkQ (tensorAverage V n a x) =
        (parityRelations V n a).mkQ x
      apply (Submodule.Quotient.eq _).mpr
      rw [← tensorAverage_kernel]
      change tensorAverage V n a (tensorAverage V n a x - x) = 0
      rw [map_sub, tensorAverage_id V n a ⟨_, tensorAverage_mem V n a x⟩, sub_self]
  right_inv x := by
    apply Subtype.ext
    exact tensorAverage_id V n a x

@[simp] theorem tensorAverageEquiv_mk (n : ℕ) (a : Bool) (x : TensorPower V n) :
    (tensorAverageEquiv V n a ((parityRelations V n a).mkQ x)).val =
      tensorAverage V n a x := rfl

theorem tensorAverage_diagonal (n : ℕ) (a : Bool) (g : LinearGroup V)
    (x : TensorPower V n) :
    tensorAverage V n a (diagonalOperator V n g x) =
      diagonalOperator V n g (tensorAverage V n a x) := by
  simp only [tensorAverage, Specs.AdvancedFiniteGroupRepresentations.tensorAverage,
    LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact DFunLike.congr_fun (tensor_actions_commute V n s g).eq x

theorem tensorAverageEquiv_diagonal (n : ℕ) (a : Bool) (g : LinearGroup V)
    (q : ParityPower V n a) :
    (tensorAverageEquiv V n a (parityPowerOperator V n a g q)).val =
      diagonalOperator V n g (tensorAverageEquiv V n a q).val := by
  induction q using Submodule.Quotient.induction_on with
  | _ x => exact tensorAverage_diagonal V n a g x

theorem tensorAverage_quotient :
    Specs.AdvancedFiniteGroupRepresentations.tensorAverage_quotientType.{u} := by
  intro V _ _ n a
  exact ⟨tensorAverage_kernel V n a, tensorAverage_mem V n a, tensorAverage_id V n a,
    tensorAverageEquiv V n a, tensorAverageEquiv_mk V n a,
    tensorAverageEquiv_diagonal V n a⟩

/-- Evaluation at the vector corresponding to 1 in a one-dimensional
Specht module. The inverse sends x to (v ↦ coordinate(v) • x). -/
def multiplicityEquivParity {n : ℕ} (p : Partition n) (a : Bool)
    (e : SpechtModule p ≃ₗ[ℂ] ℂ)
    (he : ∀ s v, e (canonicalSpechtRepresentation p s v) = tensorParity a s * e v) :
    TensorMultiplicity V p ≃ₗ[ℂ] parityTensors V n a where
  toFun f := ⟨f.val (e.symm 1), by
    intro s
    have hv : canonicalSpechtRepresentation p s (e.symm 1) =
        tensorParity a s • e.symm 1 := by
      apply e.injective
      simp [he]
    have hf := f.property s (e.symm 1) (canonicalSpechtRepresentation p s (e.symm 1)) rfl
    rw [hv, map_smul] at hf
    exact hf.symm⟩
  invFun x := ⟨e.toLinearMap.smulRight x.val, by
    intro s v w hw
    have hw' : w = canonicalSpechtRepresentation p s v := Subtype.ext hw
    change e w • x.val = slotOperator V n s (e v • x.val)
    rw [hw', he, map_smul, x.property s]
    simp only [smul_smul, mul_comm]⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change e v • f.val (e.symm 1) = f.val v
    rw [← map_smul]
    congr 1
    apply e.injective
    simp
  right_inv x := by apply Subtype.ext; change e (e.symm 1) • x.val = x.val; simp
  map_add' f h := rfl
  map_smul' c f := rfl

theorem multiplicityEquivParity_diagonal {n : ℕ} (p : Partition n) (a : Bool)
    (e : SpechtModule p ≃ₗ[ℂ] ℂ)
    (he : ∀ s v, e (canonicalSpechtRepresentation p s v) = tensorParity a s * e v)
    (g : LinearGroup V) (f : TensorMultiplicity V p) :
    (multiplicityEquivParity V p a e he (tensorMultiplicityOperator V p g f)).val =
      diagonalOperator V n g (multiplicityEquivParity V p a e he f).val := rfl

theorem multiplicity_parityPower :
    Specs.AdvancedFiniteGroupRepresentations.multiplicity_parityPowerType.{u} := by
  intro V _ _ _ n hn
  have aux {p : Partition n} {a : Bool} (e : SpechtModule p ≃ₗ[ℂ] ℂ)
      (he : ∀ s v, e (canonicalSpechtRepresentation p s v) = tensorParity a s * e v) :
      ∃ E : TensorMultiplicity V p ≃ₗ[ℂ] ParityPower V n a,
        ∀ g f, E (tensorMultiplicityOperator V p g f) = parityPowerOperator V n a g (E f) := by
    let E := (multiplicityEquivParity V p a e he).trans (tensorAverageEquiv V n a).symm
    refine ⟨E, ?_⟩
    intro g f
    apply (tensorAverageEquiv V n a).injective
    apply Subtype.ext
    rw [tensorAverageEquiv_diagonal]
    change ((tensorAverageEquiv V n a) ((tensorAverageEquiv V n a).symm _)).val =
      diagonalOperator V n g ((tensorAverageEquiv V n a) ((tensorAverageEquiv V n a).symm _)).val
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · obtain ⟨e, he⟩ := classification_row n hn (canonicalSpechtRepresentation _) (fun _ _ => rfl)
    exact aux e (by intro s v; simpa [tensorParity,
      Specs.AdvancedFiniteGroupRepresentations.tensorParity] using he s v)
  · obtain ⟨e, he⟩ := classification_column n hn (canonicalSpechtRepresentation _) (fun _ _ => rfl)
    exact aux e (by intro s v; exact he s v)


/-- The defining signed relation, on every tensor rather than only pure ones. -/
theorem parityMk_slot (n : ℕ) (a : Bool) (s : SymmetricGroup n) (x : TensorPower V n) :
    (parityRelations V n a).mkQ (slotOperator V n s x) =
      tensorParity a s • (parityRelations V n a).mkQ x := by
  have h : (parityRelations V n a).mkQ (x - tensorParity a s • slotOperator V n s x) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨s, x, rfl⟩)
  rw [map_sub, map_smul, sub_eq_zero] at h
  have hh := congrArg (tensorParity a s • ·) h
  simpa only [smul_smul, tensorParity_sq, one_smul] using hh.symm

theorem parityPure_perm (n : ℕ) (a : Bool) (s : SymmetricGroup n) (v : Fin n → V) :
    parityPure V n a ((fun i => v ((s⁻¹ : SymmetricGroup n) i))) = tensorParity a s • parityPure V n a v := by
  have h := parityMk_slot V n a s (pureTensor V n v)
  rw [slot_pureTensor] at h
  exact h

/-- A multilinear map with the specified permutation rule factors uniquely
through the signed tensor quotient. -/
theorem parityPower_lift_unique (n : ℕ) (a : Bool)
    (W : Type v) [AddCommGroup W] [Module ℂ W]
    (f : MultilinearMap ℂ (fun _ : Fin n => V) W)
    (hf : ∀ (s : SymmetricGroup n) v, f ((fun i => v ((s⁻¹ : SymmetricGroup n) i))) = tensorParity a s • f v) :
    ∃! l : ParityPower V n a →ₗ[ℂ] W, ∀ v, l (parityPure V n a v) = f v := by
  let F := PiTensorProduct.lift f
  have hF (s : SymmetricGroup n) (x : TensorPower V n) :
      F (slotOperator V n s x) = tensorParity a s • F x := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      change F (slotOperator V n s (c • pureTensor V n v)) = _
      rw [map_smul, map_smul, slot_pureTensor, map_smul]
      simp only [F, pureTensor, Specs.AdvancedFiniteGroupRepresentations.pureTensor,
        PiTensorProduct.lift.tprod]
      rw [hf, smul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hk : parityRelations V n a ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, x, rfl⟩
    change F (x - tensorParity a s • slotOperator V n s x) = 0
    rw [map_sub, map_smul, hF, smul_smul, tensorParity_sq, one_smul, sub_self]
  refine ⟨(parityRelations V n a).liftQ F hk, ?_, ?_⟩
  · intro v
    exact PiTensorProduct.lift.tprod (φ := f) v
  · intro l hl
    apply Submodule.linearMap_qext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    exact (hl v).trans (PiTensorProduct.lift.tprod (φ := f) v).symm

theorem symmetricTensorPower_universal :
    Specs.AdvancedFiniteGroupRepresentations.symmetricTensorPower_universalType.{u,v} := by
  intro V _ _ n
  constructor
  · intro s v
    simpa only [Function.comp_def, inv_inv, tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity,
      Bool.false_eq_true, ite_false, one_smul] using parityPure_perm V n false s⁻¹ v
  · intro W _ _ f hf
    apply parityPower_lift_unique V n false W f
    intro s v
    simpa only [Function.comp_def, tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity,
      Bool.false_eq_true, ite_false, one_smul] using hf s⁻¹ v

theorem exteriorTensorPower_universal :
    Specs.AdvancedFiniteGroupRepresentations.exteriorTensorPower_universalType.{u,v} := by
  intro V _ _ n
  constructor
  · intro v i j hv hij
    have hp : ((fun k => v (((Equiv.swap i j)⁻¹ : SymmetricGroup n) k))) = v := by
      simpa using funext (Equiv.apply_swap_eq_self hv)
    have he := parityPure_perm V n true (Equiv.swap i j) v
    have hs : tensorParity true (Equiv.swap i j) = -1 := by
      simp [tensorParity, Specs.AdvancedFiniteGroupRepresentations.tensorParity,
        Specs.AdvancedFiniteGroupRepresentations.permutationSign,
        Equiv.Perm.sign_swap hij]
    rw [hp, hs, neg_one_smul] at he
    have hz : (2 : ℂ) • parityPure V n true v = 0 := by
      simpa only [two_smul] using eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro W _ _ f
    apply parityPower_lift_unique V n true W f.toMultilinearMap
    intro s v
    have h := f.map_perm v s⁻¹
    simpa only [Function.comp_def, AlternatingMap.coe_multilinearMap, tensorParity,
      Specs.AdvancedFiniteGroupRepresentations.tensorParity, ite_true,
      permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
      Equiv.Perm.sign_inv, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ] using h


/-- All tensors of degree zero satisfy either character rule. -/
theorem parityTensors_zero_mem (a : Bool) (x : TensorPower V 0) :
    x ∈ parityTensors V 0 a := by
  intro s
  change slotOperator V 0 s x = tensorParity a s • x
  rw [zero_labels_trivial s, slot_one, tensorParity_one]
  exact (one_smul ℂ x).symm

def parityTensorsZeroEquiv (a : Bool) : parityTensors V 0 a ≃ₗ[ℂ] ℂ where
  toFun x := tensorPowerZeroEquiv V x.val
  invFun z := ⟨(tensorPowerZeroEquiv V).symm z, parityTensors_zero_mem V a _⟩
  left_inv x := Subtype.ext ((tensorPowerZeroEquiv V).symm_apply_apply x.val)
  right_inv z := (tensorPowerZeroEquiv V).apply_symm_apply z
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

theorem parityPower_zero :
    Specs.AdvancedFiniteGroupRepresentations.parityPower_zeroType.{u} := by
  intro V _ _
  refine ⟨?_, tensorMultiplicity_empty_line V⟩
  intro a
  let e := (tensorAverageEquiv V 0 a).trans (parityTensorsZeroEquiv V a)
  refine ⟨e, ?_, ?_⟩
  · intro v
    change tensorPowerZeroEquiv V (tensorAverage V 0 a (pureTensor V 0 v)) = 1
    rw [tensorAverage_id V 0 a ⟨_, parityTensors_zero_mem V a _⟩]
    exact tensorPowerZeroEquiv_pure V v
  · intro g q
    change tensorPowerZeroEquiv V (tensorAverageEquiv V 0 a
      (parityPowerOperator V 0 a g q)).val = _
    rw [tensorAverageEquiv_diagonal, diagonal_zero]
    rfl


namespace DegreeThree

def mixedShape : Partition 3 where
  parts := ([2, 1] : List ℕ)
  parts_pos := by intro i hi; simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  parts_sum := by decide

theorem mixed_parts : parts mixedShape = [2, 1] := by
  rw [parts_eq_sorted_multiset]
  change Multiset.sort (2 ::ₘ {1}) (· ≥ ·) = [2, 1]
  rw [Multiset.sort_cons 2 {1} (· ≥ ·) (by simp), Multiset.sort_singleton]

theorem row_parts : parts (Nat.Partition.indiscrete 3) = [3] := by
  rw [parts_eq_sorted_multiset, Nat.Partition.indiscrete_parts (by decide : 3 ≠ 0)]
  exact Multiset.sort_singleton 3 (· ≥ ·)

theorem partition_eq_of_parts_eq {n : ℕ} {p q : Partition n} (h : parts p = parts q) : p = q := by
  apply Nat.Partition.ext
  rw [parts_eq_sorted_multiset, parts_eq_sorted_multiset] at h
  have hh := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
  simpa only [Multiset.sort_eq] using hh

theorem mixed_ne_row : mixedShape ≠ Nat.Partition.indiscrete 3 := by
  intro h
  have hh := congrArg parts h
  rw [mixed_parts, row_parts] at hh
  contradiction

theorem length_le_two_iff (q : Partition 3) :
    length q ≤ 2 ↔ q = Nat.Partition.indiscrete 3 ∨ q = mixedShape := by
  have hsum := parts_sum q
  have hpos := parts_positive q
  have hsort := (parts_sorted q).pairwise
  constructor
  · intro hlen
    change (parts q).length ≤ 2 at hlen
    cases hl : parts q with
    | nil => simp [hl] at hsum
    | cons a t =>
      cases t with
      | nil =>
        have ha : a = 3 := by simpa [hl] using hsum
        left
        apply partition_eq_of_parts_eq
        rw [row_parts, hl, ha]
      | cons b t =>
        cases t with
        | nil =>
          have ha : 0 < a := hpos a (by simp [hl])
          have hb : 0 < b := hpos b (by simp [hl])
          have hab : b ≤ a := by simpa [hl] using hsort
          have hs : a + b = 3 := by simpa [hl] using hsum
          have ha' : a = 2 := by omega
          have hb' : b = 1 := by omega
          right
          apply partition_eq_of_parts_eq
          rw [mixed_parts, hl, ha', hb']
        | cons c t => simp [hl] at hlen
  · rintro (rfl | rfl) <;>
      simp [length, Specs.AdvancedFiniteGroupRepresentations.length, row_parts, mixed_parts]

theorem row_weyl : weylDimensionProduct (Nat.Partition.indiscrete 3) 2 = 4 := by
  norm_num [weylDimensionProduct, Specs.AdvancedFiniteGroupRepresentations.weylDimensionProduct,
    Fin.prod_univ_two, show Finset.Ioi (0 : Fin 2) = {1} by decide,
    show Finset.Ioi (1 : Fin 2) = ∅ by decide, rowLength_eq_getD, row_parts]

theorem mixed_weyl : weylDimensionProduct mixedShape 2 = 2 := by
  norm_num [weylDimensionProduct, Specs.AdvancedFiniteGroupRepresentations.weylDimensionProduct,
    Fin.prod_univ_two, show Finset.Ioi (0 : Fin 2) = {1} by decide,
    show Finset.Ioi (1 : Fin 2) = ∅ by decide, rowLength_eq_getD, mixed_parts]

end DegreeThree

theorem degreeThree_twoDimensional :
    Specs.AdvancedFiniteGroupRepresentations.degreeThree_twoDimensionalType.{u} := by
  intro V _ _ _ hd
  classical
  let r : Partition 3 := Nat.Partition.indiscrete 3
  let p := DegreeThree.mixedShape
  have hrp : r ≠ p := Ne.symm DegreeThree.mixed_ne_row
  have hrl : length r ≤ Module.finrank ℂ V := by
    simp [r, hd, length, Specs.AdvancedFiniteGroupRepresentations.length, DegreeThree.row_parts]
  have hpl : length p ≤ Module.finrank ℂ V := by
    simp [p, hd, length, Specs.AdvancedFiniteGroupRepresentations.length, DegreeThree.mixed_parts]
  have hR : Module.finrank ℂ (TensorMultiplicity V r) = 4 := by
    have h := schurWeyl_dimension_product V r hrl
    change (Module.finrank ℂ (TensorMultiplicity V r) : ℂ) = weylDimensionProduct r _ at h
    rw [hd] at h
    change (Module.finrank ℂ (TensorMultiplicity V r) : ℂ) = weylDimensionProduct (Nat.Partition.indiscrete 3) 2 at h
    rw [DegreeThree.row_weyl] at h
    exact_mod_cast h
  have hP : Module.finrank ℂ (TensorMultiplicity V p) = 2 := by
    have h := schurWeyl_dimension_product V p hpl
    change (Module.finrank ℂ (TensorMultiplicity V p) : ℂ) = weylDimensionProduct p _ at h
    rw [hd] at h
    change (Module.finrank ℂ (TensorMultiplicity V p) : ℂ) = weylDimensionProduct DegreeThree.mixedShape 2 at h
    rw [DegreeThree.mixed_weyl] at h
    exact_mod_cast h
  have hS : Module.finrank ℂ (SpechtModule r) = 1 := by
    obtain ⟨e, _⟩ := classification_row 3 (by decide) (canonicalSpechtRepresentation r) (fun _ _ => rfl)
    simpa using e.finrank_eq
  have hT : Module.finrank ℂ (TensorPower V 3) = 8 := by
    rw [Module.finrank_eq_card_basis (Basis.piTensorProduct (fun _ : Fin 3 => Module.finBasis ℂ V))]
    simp [hd]
  have hzero (q : Partition 3) (hqr : q ≠ r) (hqp : q ≠ p) :
      Module.finrank ℂ (TensorMultiplicity V q) = 0 := by
    apply schurWeyl_dimension_length_cutoff V q
    change Module.finrank ℂ V < length q
    rw [hd]
    have hn : ¬ length q ≤ 2 := by
      rw [DegreeThree.length_le_two_iff]
      exact not_or.mpr ⟨hqr, hqp⟩
    omega
  have hsum : (∑ q : Partition 3, Module.finrank ℂ (SpechtModule q) *
      Module.finrank ℂ (TensorMultiplicity V q)) = Module.finrank ℂ (TensorPower V 3) := by
    obtain ⟨e, _⟩ := tensorEvaluation_isomorphism V 3
    calc
      _ = Module.finrank ℂ (TensorEvaluationSum V 3) := by
        change _ = Module.finrank ℂ (⨁ q : Partition 3, SpechtModule q ⊗[ℂ] TensorMultiplicity V q)
        rw [Module.finrank_directSum]
        simp only [Module.finrank_tensorProduct]
      _ = _ := e.finrank_eq
  have hterm (q : Partition 3) :
      Module.finrank ℂ (SpechtModule q) * Module.finrank ℂ (TensorMultiplicity V q) =
      (if q = r then 4 else 0) +
        (if q = p then Module.finrank ℂ (SpechtModule p) * 2 else 0) := by
    by_cases hqr : q = r
    · subst q
      simp [hrp, hS, hR]
    · by_cases hqp : q = p
      · subst q
        simp [hqr, hP]
      · simp [hzero q hqr hqp, hqr, hqp]
  simp_rw [hterm] at hsum
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hT] at hsum
  have hSP : Module.finrank ℂ (SpechtModule p) = 2 := by omega
  have hcol : Module.finrank ℂ (TensorMultiplicity V (transpose r)) = 0 := by
    apply schurWeyl_dimension_length_cutoff V (transpose r)
    change Module.finrank ℂ V < length (transpose r)
    rw [hd, length_eq_columnLength_zero, transpose_columnLength, rowLength_eq_getD]
    norm_num [r, DegreeThree.row_parts]
  refine ⟨p, DegreeThree.mixed_parts, ?_, hS, hSP, hR, hP, hcol, hT, ?_⟩
  · intro q
    rw [tensorMultiplicity_nonzero_iff V q, hd, DegreeThree.length_le_two_iff]
  · rw [hT, hS, hSP, hR, hP]


/-- Extensionality on the pure tensors generating either quotient. -/
theorem parityPower_ext {n : ℕ} {a : Bool} {W : Type v} [AddCommGroup W] [Module ℂ W]
    {f h : ParityPower V n a →ₗ[ℂ] W}
    (he : ∀ v, f (parityPure V n a v) = h (parityPure V n a v)) : f = h := by
  apply Submodule.linearMap_qext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  exact he

theorem exteriorTensorPower_equiv :
    Specs.AdvancedFiniteGroupRepresentations.exteriorTensorPower_equivType.{u} := by
  intro V _ _ n
  obtain ⟨halt, huniv⟩ := exteriorTensorPower_universal V n
  let A : V [⋀^Fin n]→ₗ[ℂ] ExteriorTensorPower V n :=
    { toMultilinearMap := parityPure V n true
      map_eq_zero_of_eq' := fun v i j hv hij => halt v i j hv hij }
  obtain ⟨F, hF, _⟩ := huniv (⋀[ℂ]^n V) (exteriorPower.ιMulti ℂ n)
  let G := exteriorPower.alternatingMapLinearEquiv A
  have hG (v : Fin n → V) : G (exteriorPower.ιMulti ℂ n v) = parityPure V n true v :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti A v
  have hFG : F.comp G = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change F (G (exteriorPower.ιMulti ℂ n v)) = exteriorPower.ιMulti ℂ n v
    rw [hG, hF]
  have hGF : G.comp F = LinearMap.id := by
    apply parityPower_ext V
    intro v
    change G (F (parityPure V n true v)) = parityPure V n true v
    rw [hF, hG]
  let e : ExteriorTensorPower V n ≃ₗ[ℂ] (⋀[ℂ]^n V) :=
    LinearEquiv.ofLinearMap F G hFG hGF
  refine ⟨e, hF, ?_⟩
  intro g q
  have he : F.comp (parityPowerOperator V n true g) =
      (exteriorPower.map n g.toLinearMap).comp F := by
    apply parityPower_ext V
    intro v
    change F ((parityRelations V n true).mkQ
        (diagonalOperator V n g (pureTensor V n v))) =
      exteriorPower.map n g.toLinearMap (F (parityPure V n true v))
    rw [diagonal_pureTensor]
    change F (parityPure V n true (fun i => g (v i))) = _
    rw [hF, hF, exteriorPower.map_apply_ιMulti]
    rfl
  exact DFunLike.congr_fun he q


theorem symmetricExteriorPowers :
    Specs.AdvancedFiniteGroupRepresentations.symmetricExteriorPowersType.{u} := by
  intro V _ _ _ n hn
  obtain ⟨hr, ⟨F, hF⟩⟩ := multiplicity_parityPower V n hn
  obtain ⟨E, _, hE⟩ := exteriorTensorPower_equiv V n
  refine ⟨hr, F.trans E, ?_⟩
  intro g f
  change E (F (tensorMultiplicityOperator V _ g f)) = _
  rw [hF, hE]
  rfl

end AdvancedFiniteGroupRepresentations
