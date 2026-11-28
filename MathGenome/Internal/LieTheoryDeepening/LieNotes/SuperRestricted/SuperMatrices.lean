import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.Supercommutator
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperMatrices
import Mathlib.Algebra.BigOperators.Fin

namespace LieNotes.SuperRestricted.SuperMatrices

open Module (Basis)
open Specs.LieNotes.SuperRestricted.SuperMatrices
  (Mat zValue hValue eValue fValue pieceValue gradingValue parity_cases
    generatorValue bracketTable supertraceValue)

variable (k : Type*) [Field k]

abbrev z : Mat k := zValue k
abbrev h : Mat k := hValue k
abbrev e : Mat k := eValue k
abbrev f : Mat k := fValue k

abbrev piece (i : ZMod 2) : Submodule k (Mat k) := pieceValue k i

abbrev grading : Grading k (Mat k) := gradingValue k

theorem mem_even {M : Mat k} : M ∈ (grading k).piece 0 ↔ M 0 1 = 0 ∧ M 1 0 = 0 :=
  Specs.LieNotes.SuperRestricted.SuperMatrices.mem_even k

theorem mem_odd {M : Mat k} : M ∈ (grading k).piece 1 ↔ M 0 0 = 0 ∧ M 1 1 = 0 :=
  Specs.LieNotes.SuperRestricted.SuperMatrices.mem_odd k

theorem mul_graded : Supercommutator.MulGraded (grading k) := by
  intro i j M N hM hN
  have odd_add_odd : (1 : ZMod 2) + 1 = 0 := by decide
  obtain rfl | rfl := parity_cases i <;>
    obtain rfl | rfl := parity_cases j <;>
    simp only [zero_add, add_zero, odd_add_odd, mem_even, mem_odd] at hM hN ⊢ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hM.1, hM.2, hN.1, hN.2]

noncomputable abbrev bracket : Mat k →ₗ[k] Mat k →ₗ[k] Mat k :=
  Supercommutator.bracket (grading k)

/-- The Lie superalgebra of one even and one odd coordinate. -/
noncomputable def gl [NeZero (2 : k)] : LieSuperalgebra k (Mat k) :=
  Supercommutator.toLieSuperalgebra (grading k) (mul_graded k)

@[simp] theorem gl_grading [NeZero (2 : k)] : (gl k).grading = grading k := rfl

@[simp] theorem gl_bracket [NeZero (2 : k)] : (gl k).bracket = bracket k := rfl

theorem exists_gl [NeZero (2 : k)] :
    ∃ L : LieSuperalgebra k (Mat k), L.grading = grading k ∧ L.bracket = bracket k :=
  ⟨gl k, rfl, rfl⟩

abbrev generator : Fin 4 → Mat k := generatorValue k

private def coordinates : Mat k ≃ₗ[k] (Fin 4 → k) where
  toFun M := ![M 1 1, M 0 0 - M 1 1, M 0 1, M 1 0]
  invFun v := Matrix.of ![![v 0 + v 1, v 2], ![v 3, v 0]]
  left_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv v := by
    funext i
    fin_cases i <;> simp
  map_add' M N := by
    funext i
    fin_cases i <;> simp [sub_add_sub_comm, Matrix.add_apply]
  map_smul' c M := by
    funext i
    fin_cases i <;> simp [Matrix.smul_apply, mul_sub]

/-- The ordered matrix basis (z, h, e, f). -/
noncomputable def basis : Basis (Fin 4) k (Mat k) :=
  Basis.ofEquivFun (coordinates k)

@[simp] theorem basis_apply (i : Fin 4) : basis k i = generator k i := by
  rw [basis, Basis.coe_ofEquivFun]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [coordinates, generatorValue, zValue, hValue, eValue, fValue, Matrix.single]

theorem exists_basis : ∃ B : Basis (Fin 4) k (Mat k), ∀ i, B i = generator k i :=
  ⟨basis k, basis_apply k⟩

theorem generator_mem (i : Fin 4) :
    generator k i ∈ (grading k).piece (if i < 2 then 0 else 1) := by
  fin_cases i <;>
    simp [generatorValue, mem_even, mem_odd, zValue, hValue, eValue, fValue, Matrix.single]

theorem bracket_table (i j : Fin 4) :
    bracket k (generator k i) (generator k j) = bracketTable k i j := by
  rw [Supercommutator.bracket_of_mem (grading k) (generator_mem k i) (generator_mem k j)]
  fin_cases i <;> fin_cases j <;>
    simp [generatorValue, bracketTable, zValue, hValue, eValue, fValue,
      add_mul, mul_add, add_comm]

@[simp] theorem bracket_h_e : bracket k (h k) (e k) = e k := bracket_table k 1 2

@[simp] theorem bracket_h_f : bracket k (h k) (f k) = -f k := bracket_table k 1 3

@[simp] theorem bracket_e_f : bracket k (e k) (f k) = z k := bracket_table k 2 3

@[simp] theorem bracket_e_e : bracket k (e k) (e k) = 0 := bracket_table k 2 2

@[simp] theorem bracket_f_f : bracket k (f k) (f k) = 0 := bracket_table k 3 3

theorem central (M : Mat k) : bracket k (z k) M = 0 ∧ bracket k M (z k) = 0 := by
  have left : bracket k (z k) = 0 := by
    apply (basis k).ext
    intro j
    rw [basis_apply]
    change bracket k (generator k 0) (generator k j) = 0
    rw [bracket_table]
    fin_cases j <;> rfl
  have right : (bracket k).flip (z k) = 0 := by
    apply (basis k).ext
    intro i
    rw [basis_apply]
    change bracket k (generator k i) (generator k 0) = 0
    rw [bracket_table]
    fin_cases i <;> rfl
  exact ⟨LinearMap.congr_fun left M, LinearMap.congr_fun right M⟩

/-- Supertrace, the even diagonal entry minus the odd diagonal entry. -/
abbrev supertrace : Mat k →ₗ[k] k := supertraceValue k

@[simp] theorem supertrace_apply (M : Mat k) : supertrace k M = M 0 0 - M 1 1 := rfl

@[simp] theorem supertrace_z : supertrace k (z k) = 0 := by
  simp [zValue, Matrix.single]

@[simp] theorem supertrace_e : supertrace k (e k) = 0 := by
  simp [eValue, Matrix.single]

@[simp] theorem supertrace_f : supertrace k (f k) = 0 := by
  simp [fValue, Matrix.single]

theorem supertrace_bracket (M N : Mat k) : supertrace k (bracket k M N) = 0 := by
  have hzero : (bracket k).compr₂ (supertrace k) = 0 := by
    apply (basis k).ext
    intro i
    apply (basis k).ext
    intro j
    rw [basis_apply, basis_apply]
    change supertrace k (bracket k (generator k i) (generator k j)) = 0
    rw [bracket_table]
    fin_cases i <;> fin_cases j <;> simp [bracketTable, -supertrace_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun hzero M) N

theorem supertrace_ker :
    (supertrace k).ker = Submodule.span k ({z k, e k, f k} : Set (Mat k)) := by
  let S := Submodule.span k ({z k, e k, f k} : Set (Mat k))
  apply le_antisymm
  · intro M hM
    have hdiag : M 0 0 = M 1 1 := sub_eq_zero.mp (LinearMap.mem_ker.mp hM)
    have hrepr : M = M 1 1 • z k + M 0 1 • e k + M 1 0 • f k := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [zValue, eValue, fValue, Matrix.single, hdiag]
    have hz : z k ∈ S := Submodule.subset_span (by simp)
    have he : e k ∈ S := Submodule.subset_span (by simp)
    have hf : f k ∈ S := Submodule.subset_span (by simp)
    rw [hrepr]
    exact S.add_mem (S.add_mem (S.smul_mem _ hz) (S.smul_mem _ he)) (S.smul_mem _ hf)
  · apply Submodule.span_le.mpr
    intro M hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl
    · exact LinearMap.mem_ker.mpr (supertrace_z k)
    · exact LinearMap.mem_ker.mpr (supertrace_e k)
    · exact LinearMap.mem_ker.mpr (supertrace_f k)

end LieNotes.SuperRestricted.SuperMatrices
