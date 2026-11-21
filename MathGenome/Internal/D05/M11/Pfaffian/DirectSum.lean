import MathGenome.Internal.Specs.D05.M11.Pfaffian.DirectSum
import MathGenome.Internal.D05.M11.Pfaffian
import MathGenome.Internal.D05.M15.WedgeSign
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
namespace D05.M11.Pfaffian.DirectSum
open scoped BigOperators
open Specs.D05.M11.Pfaffian Specs.D05.M11.Pfaffian.DirectSum

/-- Sum over both orientations. This is twice the paper's two-form for a skew matrix. -/
def pairForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Fin n → V) (A : Matrix (Fin n) (Fin n) ℝ) : ExteriorAlgebra ℝ V :=
  ∑ i, ∑ j, A i j • (ExteriorAlgebra.ι ℝ (b i) * ExteriorAlgebra.ι ℝ (b j))

lemma pairForm_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Fin n → V) (A : Matrix (Fin n) (Fin n) ℝ) :
    pairForm b A ∈ ⋀[ℝ]^2 V := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ)) ^ 2
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

lemma map_pairForm {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {n : ℕ} (f : V →ₗ[ℝ] W)
    (b : Fin n → V) (A : Matrix (Fin n) (Fin n) ℝ) :
    ExteriorAlgebra.map f (pairForm b A) = pairForm (f ∘ b) A := by
  simp [pairForm, map_sum, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]

lemma pairForm_pow_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r k : ℕ) (b : Fin (2*r) → V) (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (hk : r < k) : pairForm b A ^ k = 0 := by
  let f := (coordinateBasis (2*r)).constr ℝ b
  have hmap : ExteriorAlgebra.map f (pairForm (coordinateBasis (2*r)) A) = pairForm b A := by
    rw [map_pairForm]
    congr 1
    funext i
    exact Module.Basis.constr_basis _ _ _ _
  rw [← hmap, ← map_pow]
  have hm := SetLike.pow_mem_graded k (pairForm_mem (coordinateBasis (2*r)) A)
  have hz := D05.M15.ExteriorBasis.above_dimension (2*r) (coordinateBasis (2*r)) (k*2)
    (by omega)
  have hzero : pairForm (coordinateBasis (2*r)) A ^ k = 0 := by
    apply (Submodule.mem_bot ℝ).mp
    rw [← hz]
    simpa [Specs.D05.M15.Exterior.homogeneousPart_value] using hm
  rw [hzero, map_zero]

lemma pairForm_power {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : ℕ) (b : Fin (2*r) → V) (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ) :
    pairForm b A ^ r = (2^r * (Nat.factorial r : ℝ) * pfaffian A) •
      ExteriorAlgebra.ιMulti ℝ (2*r) b := by
  rw [pairForm, full_pair_power_permutations]
  congr 1
  simp only [pfaffian, pfaffian_value]
  have hn : (2:ℝ)^r * (Nat.factorial r : ℝ) ≠ 0 := by positivity
  field_simp

/-- Only the term with r factors from the first block can survive. -/
lemma pairForm_binomial {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r s : ℕ) (a : Fin (2*r) → V) (b : Fin (2*s) → V)
    (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ) :
    (pairForm a A + pairForm b B)^(r+s) =
      ((r+s).choose r : ℝ) • (pairForm a A ^ r * pairForm b B ^ s) := by
  have hc : Commute (pairForm a A) (pairForm b B) := by
    show pairForm a A * pairForm b B = pairForm b B * pairForm a A
    have h := D05.M15.WedgeSign.graded_comm (K := ℝ) 2 2 _ _ (pairForm_mem a A) (pairForm_mem b B)
    norm_num at h
    exact h
  rw [hc.add_pow']
  rw [Finset.sum_eq_single (r,s)]
  · simp [Nat.cast_smul_eq_nsmul]
  · intro ij hij hne
    rcases ij with ⟨i,j⟩
    have he : i+j = r+s := Finset.mem_antidiagonal.mp hij
    by_cases hi : r < i
    · rw [pairForm_pow_zero r i a A hi, zero_mul, smul_zero]
    · have hj : s < j := by
        have hne' : ¬ (i = r ∧ j = s) := by simpa using hne
        omega
      rw [pairForm_pow_zero s j b B hj, mul_zero, smul_zero]
  · simp

lemma pairForm_block {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r s : ℕ) (b : Fin (2*(r+s)) → V)
    (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ) :
    pairForm b (blockMatrix A B) =
      pairForm (fun i => b (blockIndex r s (.inl i))) A +
      pairForm (fun j => b (blockIndex r s (.inr j))) B := by
  classical
  unfold pairForm
  rw [← (blockIndex r s).sum_comp]
  simp_rw [← (blockIndex r s).sum_comp]
  simp [blockMatrix, Fintype.sum_sum_type]

lemma block_volume {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r s : ℕ) (b : Fin (2*(r+s)) → V) :
    ExteriorAlgebra.ιMulti ℝ (2*r) (fun i => b (blockIndex r s (.inl i))) *
    ExteriorAlgebra.ιMulti ℝ (2*s) (fun j => b (blockIndex r s (.inr j))) =
    ExteriorAlgebra.ιMulti ℝ (2*(r+s)) b := by
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_congr (Nat.mul_add 2 r s).symm]
  congr 2
  funext i
  congr 1
  apply Fin.addCases (m := 2*r) (n := 2*s)
    (motive := fun j => Fin.append
      (fun k => b (blockIndex r s (.inl k)))
      (fun k => b (blockIndex r s (.inr k))) j = b (Fin.cast (Nat.mul_add 2 r s).symm j))
    ?_ ?_ (Fin.cast (Nat.mul_add 2 r s) i)
  · intro j
    simp [blockIndex, finSumFinEquiv]
  · intro j
    simp [blockIndex, finSumFinEquiv]

/-- Multiplicativity for the signed formula; skew-symmetry is not needed for
this stronger auxiliary identity, since the formula automatically alternates. -/
lemma pfaffian_block (r s : ℕ)
    (A : Matrix (Fin (2*r)) (Fin (2*r)) ℝ)
    (B : Matrix (Fin (2*s)) (Fin (2*s)) ℝ) :
    pfaffian (blockMatrix A B) = pfaffian A * pfaffian B := by
  let b := coordinateBasis (2*(r+s))
  have h : (2^(r+s) * (Nat.factorial (r+s) : ℝ) * pfaffian (blockMatrix A B)) •
      volume (r+s) =
      (((r+s).choose r : ℝ) *
        ((2^r * (Nat.factorial r : ℝ) * pfaffian A) *
         (2^s * (Nat.factorial s : ℝ) * pfaffian B))) • volume (r+s) := by
    calc
      _ = pairForm b (blockMatrix A B) ^ (r+s) := (pairForm_power (r+s) b _).symm
      _ = _ := by
        rw [pairForm_block, pairForm_binomial, pairForm_power, pairForm_power,
          smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, block_volume]
        simp only [mul_assoc, volume, volume_value, b]
  have he := smul_left_injective ℝ (volume_ne_zero (r+s)) h
  have hf : ((r+s).choose r : ℝ) * (Nat.factorial r : ℝ) *
      (Nat.factorial s : ℝ) = (Nat.factorial (r+s) : ℝ) := by
    exact_mod_cast (show (r+s).choose r * r.factorial * s.factorial = (r+s).factorial from by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right r s))
  have hc : ((r+s).choose r : ℝ) * (2^r * (Nat.factorial r : ℝ)) *
      (2^s * (Nat.factorial s : ℝ)) = 2^(r+s) * (Nat.factorial (r+s) : ℝ) := by
    calc
      _ = (2:ℝ)^r * 2^s *
          (((r+s).choose r : ℝ) * (Nat.factorial r : ℝ) * (Nat.factorial s : ℝ)) := by ring
      _ = _ := by rw [hf, pow_add]
  have hn : (2:ℝ)^(r+s) * (Nat.factorial (r+s) : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  calc
    _ = ((r+s).choose r : ℝ) *
        ((2^r * (Nat.factorial r : ℝ) * pfaffian A) *
         (2^s * (Nat.factorial s : ℝ) * pfaffian B)) := he
    _ = (((r+s).choose r : ℝ) * (2^r * (Nat.factorial r : ℝ)) *
        (2^s * (Nat.factorial s : ℝ))) * (pfaffian A * pfaffian B) := by ring
    _ = _ := by rw [hc]

/-- The source theorem, for arbitrary real skew-symmetric blocks. Its natural
number quantifiers include either or both empty blocks without special premises. -/
theorem direct_sum : Specs.D05.M11.Pfaffian.DirectSum.direct_sum := by
  intro r s A B _ _
  exact pfaffian_block r s A B

end D05.M11.Pfaffian.DirectSum
