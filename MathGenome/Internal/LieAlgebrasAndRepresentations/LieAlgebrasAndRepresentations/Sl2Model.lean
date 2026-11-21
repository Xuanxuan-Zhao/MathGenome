import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Commutator
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

universe u

namespace LieAlgebrasAndRepresentations

open Specs.LieAlgebrasAndRepresentations.Sl2Model

abbrev sl2 (k : Type u) [Field k] : Type u := Model k
abbrev sl2_e (k : Type u) [Field k] : sl2 k := E k
abbrev sl2_f (k : Type u) [Field k] : sl2 k := F k
abbrev sl2_h (k : Type u) [Field k] : sl2 k := H k

variable (k : Type u) [Field k]

theorem sl2_matrices :
    (sl2_e k).val = !![0, 1; 0, 0] ∧
    (sl2_f k).val = !![0, 0; 1, 0] ∧
    (sl2_h k).val = !![1, 0; 0, -1] := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.single]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [F, Matrix.single]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [H, Matrix.single]

@[simp] theorem sl2_e_val : (sl2_e k).val = !![0, 1; 0, 0] := (sl2_matrices k).1
@[simp] theorem sl2_f_val : (sl2_f k).val = !![0, 0; 1, 0] := (sl2_matrices k).2.1
@[simp] theorem sl2_h_val : (sl2_h k).val = !![1, 0; 0, -1] := (sl2_matrices k).2.2

theorem sl2_relations :
    ⁅sl2_h k, sl2_e k⁆ = (2 : k) • sl2_e k ∧
    ⁅sl2_h k, sl2_f k⁆ = (-2 : k) • sl2_f k ∧
    ⁅sl2_e k, sl2_f k⁆ = sl2_h k := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply Subtype.ext <;>
    simp only [LieAlgebra.SpecialLinear.sl_bracket, SetLike.val_smul,
      sl2_e_val, sl2_f_val, sl2_h_val] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The trace equation determines the second diagonal entry. -/
theorem sl2_diagonal (x : sl2 k) : x.val 1 1 = -x.val 0 0 := by
  have hx : Matrix.trace x.val = 0 := x.property
  rw [Matrix.trace_fin_two] at hx
  exact eq_neg_of_add_eq_zero_right hx

/-- Explicit expansion in the displayed three matrix vectors. -/
theorem sl2_expansion (x : sl2 k) :
    x = x.val 0 1 • sl2_e k + x.val 1 0 • sl2_f k + x.val 0 0 • sl2_h k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SetLike.val_smul, sl2_e_val, sl2_f_val, sl2_h_val, sl2_diagonal]

/-- Coordinates in the order e, f, h. -/
def sl2Coordinates : sl2 k ≃ₗ[k] (Fin 3 → k) where
  toFun x := ![x.val 0 1, x.val 1 0, x.val 0 0]
  invFun c := c 0 • sl2_e k + c 1 • sl2_f k + c 2 • sl2_h k
  left_inv x := (sl2_expansion k x).symm
  right_inv c := by
    ext i
    fin_cases i <;> simp [SetLike.val_smul, sl2_e_val, sl2_f_val, sl2_h_val]
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' a x := by ext i; fin_cases i <;> rfl

@[simp] theorem sl2Coordinates_apply (x : sl2 k) :
    sl2Coordinates k x = ![x.val 0 1, x.val 1 0, x.val 0 0] := rfl

theorem sl2_basis :
    ∃ b : Module.Basis (Fin 3) k (sl2 k),
      b 0 = sl2_e k ∧ b 1 = sl2_f k ∧ b 2 = sl2_h k := by
  refine ⟨Module.Basis.ofEquivFun (sl2Coordinates k), ?_, ?_, ?_⟩ <;>
    rw [Module.Basis.coe_ofEquivFun] <;>
    apply (sl2Coordinates k).injective <;>
    simp only [LinearEquiv.apply_symm_apply] <;>
    ext i <;> fin_cases i <;>
    simp [sl2Coordinates_apply, sl2_e_val, sl2_f_val, sl2_h_val]

/-- Containing h forces an ideal to contain e and f as well. -/
theorem sl2_ideal_top_of_h [CharZero k] (I : LieIdeal k (sl2 k))
    (hh : sl2_h k ∈ I) : I = ⊤ := by
  have he' : ⁅sl2_e k, sl2_h k⁆ ∈ I := LieSubmodule.lie_mem I hh
  rw [← lie_skew (sl2_e k) (sl2_h k), (sl2_relations k).1, ← neg_smul] at he'
  have he : sl2_e k ∈ I :=
    (I.toSubmodule.smul_mem_iff (by norm_num : (-2 : k) ≠ 0)).mp he'
  have hf' : ⁅sl2_f k, sl2_h k⁆ ∈ I := LieSubmodule.lie_mem I hh
  rw [← lie_skew (sl2_f k) (sl2_h k), (sl2_relations k).2.1,
    ← neg_smul, neg_neg] at hf'
  have hf : sl2_f k ∈ I :=
    (I.toSubmodule.smul_mem_iff (by norm_num : (2 : k) ≠ 0)).mp hf'
  apply top_unique
  intro x _
  rw [sl2_expansion k x]
  exact I.add_mem (I.add_mem (I.smul_mem _ he) (I.smul_mem _ hf)) (I.smul_mem _ hh)

theorem sl2_ideal_top_of_e [CharZero k] (I : LieIdeal k (sl2 k))
    (he : sl2_e k ∈ I) : I = ⊤ := by
  apply sl2_ideal_top_of_h k I
  have hh : ⁅sl2_f k, sl2_e k⁆ ∈ I := LieSubmodule.lie_mem I he
  rw [← lie_skew (sl2_f k) (sl2_e k), (sl2_relations k).2.2] at hh
  simpa using I.neg_mem hh

theorem sl2_ideal_top_of_f [CharZero k] (I : LieIdeal k (sl2 k))
    (hf : sl2_f k ∈ I) : I = ⊤ := by
  apply sl2_ideal_top_of_h k I
  have hh : ⁅sl2_e k, sl2_f k⁆ ∈ I := LieSubmodule.lie_mem I hf
  rwa [(sl2_relations k).2.2] at hh

/-- Repeated brackets isolate the lower off-diagonal coefficient. -/
theorem sl2_double_e (x : sl2 k) :
    ⁅sl2_e k, ⁅sl2_e k, x⁆⁆ = (-2 * x.val 1 0) • sl2_e k := by
  apply Subtype.ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, SetLike.val_smul, sl2_e_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- Repeated brackets isolate the upper off-diagonal coefficient. -/
theorem sl2_double_f (x : sl2 k) :
    ⁅sl2_f k, ⁅sl2_f k, x⁆⁆ = (-2 * x.val 0 1) • sl2_f k := by
  apply Subtype.ext
  simp only [LieAlgebra.SpecialLinear.sl_bracket, SetLike.val_smul, sl2_f_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- Every nonzero ideal contains a displayed basis vector and is the whole algebra. -/
theorem sl2_ideal_eq_bot_or_top [CharZero k] (I : LieIdeal k (sl2 k)) :
    I = ⊥ ∨ I = ⊤ := by
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ x : sl2 k, x ∈ I ∧ x ≠ 0 := by
    by_contra! h
    exact hI ((LieSubmodule.eq_bot_iff I).mpr h)
  obtain ⟨x, hx, hx0⟩ := hex
  by_cases hc : x.val 1 0 = 0
  · by_cases hb : x.val 0 1 = 0
    · have ha : x.val 0 0 ≠ 0 := by
        intro ha
        apply hx0
        rw [sl2_expansion k x, ha, hb, hc]
        simp
      have hax : x = x.val 0 0 • sl2_h k := by
        rw [sl2_expansion k x, hb, hc]
        simp
      apply sl2_ideal_top_of_h k I
      apply (I.toSubmodule.smul_mem_iff ha).mp
      rwa [hax] at hx
    · have hfx : ⁅sl2_f k, ⁅sl2_f k, x⁆⁆ ∈ I :=
        LieSubmodule.lie_mem I (LieSubmodule.lie_mem I hx)
      rw [sl2_double_f k x] at hfx
      apply sl2_ideal_top_of_f k I
      exact (I.toSubmodule.smul_mem_iff
        (mul_ne_zero (by norm_num : (-2 : k) ≠ 0) hb)).mp hfx
  · have hex : ⁅sl2_e k, ⁅sl2_e k, x⁆⁆ ∈ I :=
      LieSubmodule.lie_mem I (LieSubmodule.lie_mem I hx)
    rw [sl2_double_e k x] at hex
    apply sl2_ideal_top_of_e k I
    exact (I.toSubmodule.smul_mem_iff
      (mul_ne_zero (by norm_num : (-2 : k) ≠ 0) hc)).mp hex

theorem sl2_nonabelian [CharZero k] : ¬IsLieAbelian (sl2 k) :=
  LieAlgebra.SpecialLinear.sl_non_abelian (Fin 2) k (by decide)

theorem sl2_simple [CharZero k] : LieAlgebra.IsSimple k (sl2 k) :=
  ⟨sl2_ideal_eq_bot_or_top k, sl2_nonabelian k⟩

end LieAlgebrasAndRepresentations
