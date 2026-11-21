import MathGenome.Internal.D07.Ch02.CycleDecomposition
import MathGenome.Internal.Specs.D07.Ch02.TranspositionsParity
import Mathlib.Algebra.Ring.Parity

/-! Transposition factorizations and their integer-valued parity invariant. -/

namespace D07.Ch02.TranspositionsParity

universe u v

noncomputable def sign (X : Type u) [Fintype X] : Equiv.Perm X →* ℤˣ := by
  classical
  exact Equiv.Perm.sign

theorem transposition_factorization :
    Specs.D07.Ch02.TranspositionsParity.TranspositionFactorization.{u} := by
  classical
  intro X _ σ
  letI := Fintype.ofFinite X
  exact ⟨σ.truncSwapFactors.out.val, σ.truncSwapFactors.out.property⟩

theorem sign_factorization :
    Specs.D07.Ch02.TranspositionsParity.SignFactorization.{u} := by
  classical
  intro X _ L hL
  exact Equiv.Perm.sign_prod_list_swap hL

theorem parity_independent :
    Specs.D07.Ch02.TranspositionsParity.ParityIndependent.{u} := by
  classical
  intro X _ L M hL hM hprod
  letI := Fintype.ofFinite X
  have heq : (-1 : ℤˣ) ^ L.length = (-1 : ℤˣ) ^ M.length := by
    rw [← Equiv.Perm.sign_prod_list_swap hL, hprod,
      Equiv.Perm.sign_prod_list_swap hM]
  have heven : Even L.length ↔ Even M.length := by
    rw [← neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide),
      ← neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide), heq]
  have hzero : L.length % 2 = 0 ↔ M.length % 2 = 0 := by
    simpa only [Nat.even_iff] using heven
  omega

theorem sign_values : Specs.D07.Ch02.TranspositionsParity.SignValues.{u} := by
  refine ⟨Int.units_eq_one_or, by decide, ?_⟩
  intro X _ σ
  exact Int.units_eq_one_or _

theorem sign_homomorphism :
    Specs.D07.Ch02.TranspositionsParity.SignHomomorphism.{u} := by
  intro X _
  exact ⟨map_one _, map_mul _⟩

theorem transposition_sign :
    Specs.D07.Ch02.TranspositionsParity.TranspositionSign.{u} := by
  classical
  intro X _ x y hxy
  exact Equiv.Perm.sign_swap hxy

theorem self_swap_sign :
    Specs.D07.Ch02.TranspositionsParity.SelfSwapSign.{u} := by
  classical
  intro X _ x
  simp [Specs.D07.Ch02.TranspositionsParity.signValue]

/-- The accepted listed cycle is a product of length minus one adjacent swaps.
Distinct entries ensure that every swap occurring in this product is nontrivial. -/
theorem sign_formPerm {X : Type u} [Fintype X] [DecidableEq X]
    (l : List X) (h : l.Nodup) :
    Equiv.Perm.sign l.formPerm = (-1 : ℤˣ) ^ (l.length - 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hab : a ≠ b := fun heq => (List.nodup_cons.mp h).1 (by simp [heq])
      rw [List.formPerm_cons_cons, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
        ih (List.nodup_cons.mp h).2]
      simp [pow_succ, mul_comm]

theorem cycle_sign : Specs.D07.Ch02.TranspositionsParity.CycleSign.{u} := by
  classical
  intro X _ l h _
  exact sign_formPerm l h

theorem sign_relabeling :
    Specs.D07.Ch02.TranspositionsParity.SignRelabeling.{u, v} := by
  classical
  intro X Y _ _ b σ
  exact Equiv.Perm.sign_symm_trans_trans σ b

theorem empty_sign : Specs.D07.Ch02.TranspositionsParity.EmptySign.{u} := by
  intro X _ _ σ
  have h : σ = 1 := Equiv.ext (fun x => isEmptyElim x)
  rw [h]
  exact map_one _

theorem determinant_sign : Specs.D07.Ch02.TranspositionsParity.DeterminantSign.{u} := by
  classical
  intro X _ σ
  have hm : (fun i j : X => if i = σ j then (1 : ℚ) else 0) =
      (1 : Matrix X X ℚ).submatrix σ.symm id := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, Equiv.symm_apply_eq]
  rw [hm, Matrix.det_permute, Matrix.det_one, mul_one]
  simp [Specs.D07.Ch02.TranspositionsParity.signValue]

end D07.Ch02.TranspositionsParity
