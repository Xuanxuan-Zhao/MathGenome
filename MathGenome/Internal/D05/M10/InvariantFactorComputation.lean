import MathGenome.Internal.Specs.D05.M10.InvariantFactorComputation
import MathGenome.Internal.D05.M10.InvariantFactorComputation.Existence
import MathGenome.Internal.D05.M10.InvariantFactorComputation.MinorIdeals
import Mathlib.LinearAlgebra.Matrix.Transvection

noncomputable section
open scoped BigOperators
namespace D05.M10.InvariantFactorComputation
open D05.M10.Smith

variable {K : Type*} [Field K] {m n : ℕ}

/-- Each operation is left or right multiplication by a polynomial matrix.
Invertibility is subsequently supplied by its explicit inverse operation. -/
lemma operation_minorIdeal_le (op : Operation K m n)
    (M : Matrix (Fin m) (Fin n) (Polynomial K)) (k : ℕ) :
    minorIdeal (op.apply M) k ≤ minorIdeal M k := by
  classical
  cases op with
  | swapRows i j =>
    have heq : (Operation.swapRows i j).apply M =
        (1 : Matrix (Fin m) (Fin m) (Polynomial K)).submatrix (Equiv.swap i j) id * M := by
      ext a b
      simp [Operation.apply, Matrix.mul_apply, Matrix.one_apply]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_left_le _ _ k
  | swapCols i j =>
    have heq : (Operation.swapCols i j).apply M =
        M * (1 : Matrix (Fin n) (Fin n) (Polynomial K)).submatrix id (Equiv.swap i j) := by
      ext a b
      simp [Operation.apply, Matrix.mul_apply, Matrix.one_apply]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_right_le _ _ k
  | addRow i j h q =>
    have heq : (Operation.addRow i j h q).apply M = Matrix.transvection i j q * M := by
      ext a b
      by_cases ha : a = i
      · subst a; simp [Operation.apply]
      · simp [Operation.apply, ha]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_left_le _ _ k
  | addCol i j h q =>
    have heq : (Operation.addCol i j h q).apply M = M * Matrix.transvection j i q := by
      ext a b
      by_cases hb : b = i
      · subst b; simp [Operation.apply]
      · simp [Operation.apply, hb]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_right_le _ _ k
  | scaleRow i c =>
    have heq : (Operation.scaleRow i c).apply M =
        Matrix.diagonal (fun a => if a = i then Polynomial.C (c : K) else 1) * M := by
      ext a b
      by_cases ha : a = i <;> simp [Operation.apply, Matrix.diagonal_mul, ha]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_left_le _ _ k
  | scaleCol j c =>
    have heq : (Operation.scaleCol j c).apply M =
        M * Matrix.diagonal (fun b => if b = j then Polynomial.C (c : K) else 1) := by
      ext a b
      by_cases hb : b = j <;> simp [Operation.apply, Matrix.mul_diagonal, hb, mul_comm]
    rw [heq]
    exact MinorIdeals.minorIdeal_mul_right_le _ _ k

theorem operation_inverse : D05.Specs.InvariantFactorComputation.operation_inverse :=
  Existence.operationInverse

theorem elementary_invariance : D05.Specs.InvariantFactorComputation.elementary_invariance := by
  intro K _ m n k M op
  apply le_antisymm (operation_minorIdeal_le op M k)
  have h := operation_minorIdeal_le op.inverse (op.apply M) k
  rwa [Existence.Op.inverse_apply] at h

theorem run_invariance : D05.Specs.InvariantFactorComputation.run_invariance := by
  intro K _ m n k M ops
  induction ops generalizing M with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (op.apply M)).trans (elementary_invariance K m n k M op)

theorem reduction_computes : D05.Specs.InvariantFactorComputation.reduction_computes := by
  intro K _ m n M ops r d h
  have hg : ∀ k, minorGcd M k = minorGcd (rectDiagonal m n d) k := by
    intro k
    apply MinorIdeals.minorGcd_eq_of_ideal_eq
    rw [← h.2.2.2]
    exact (run_invariance K m n k M ops).symm
  obtain ⟨hs, hl, hz, hq⟩ := MinorIdeals.diagonal_gcd K m n r d h.1 h.2.1 h.2.2.1
  exact ⟨fun k hk => (hg k).trans (hs k hk),
    fun k hk => (hg k).trans (hl k hk), (hg 0).trans hz,
    fun i hi => by rw [hg, hg]; exact hq i hi⟩

theorem smith_computation : D05.Specs.InvariantFactorComputation.smith_computation := by
  intro K _ m n M
  obtain ⟨ops, r, d, hr, hmonic, hzero, hdiv, heq⟩ := Existence.smithReduction K m n M
  have hc : DiagonalChain d r := by
    apply (MinorIdeals.chain_iff_adjacent K d r).mpr
    exact ⟨fun i hi => (hmonic i hi).2, hzero, fun i _ => hdiv i⟩
  have h : SmithReduction M ops r d :=
    ⟨(Nat.le_min.mp hr).1, (Nat.le_min.mp hr).2, hc, Matrix.ext heq⟩
  exact ⟨ops, r, d, h, reduction_computes K m n M ops r d h⟩

/-- A normalized chain has a nonzero determinantal divisor exactly through r. -/
lemma gcd_ne_zero_of_le {M : Matrix (Fin m) (Fin n) (Polynomial K)}
    {r : ℕ} {d : ℕ → Polynomial K} (hc : DiagonalChain d r)
    (hg : ComputesMinors M r d) {k : ℕ} (hk : k ≤ r) : minorGcd M k ≠ 0 := by
  rw [hg.1 k hk]
  exact (MinorIdeals.prefixProduct_monic d hc.1 hk).ne_zero

theorem smith_unique : D05.Specs.InvariantFactorComputation.smith_unique := by
  intro K _ m n M ops ops' r s d e hd he
  have hgd := reduction_computes K m n M ops r d hd
  have hge := reduction_computes K m n M ops' s e he
  have hrs : r = s := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact (gcd_ne_zero_of_le he.2.2.1 hge (show r+1 ≤ s by omega))
        (hgd.2.1 (r+1) (by omega))
    · exact (gcd_ne_zero_of_le hd.2.2.1 hgd (show s+1 ≤ r by omega))
        (hge.2.1 (s+1) (by omega))
  refine ⟨hrs, funext fun i => ?_⟩
  by_cases hi : i < r
  · rw [hgd.2.2.2 i hi, hge.2.2.2 i (by omega)]
  · rw [hd.2.2.1.2.1 i (by omega), he.2.2.1.2.1 i (by omega)]

/-- The full-size determinantal ideal of a square matrix is its determinant ideal.
Arbitrary row/column words factor through square matrices selecting rows/columns,
so this proof also accounts for repeated indices. -/
lemma top_minorIdeal {R : Type*} [CommRing R] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R) : minorIdeal M n = Ideal.span {M.det} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨ρ, κ, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    have heq : M.submatrix ρ κ =
        ((1 : Matrix (Fin n) (Fin n) R).submatrix ρ id * M) *
          (1 : Matrix (Fin n) (Fin n) R).submatrix id κ := by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]
    rw [heq, Matrix.det_mul, Matrix.det_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa using MinorIdeals.minor_mem M id id

theorem nonsingular_rank : D05.Specs.InvariantFactorComputation.nonsingular_rank := by
  intro K _ n M ops r d hdet h
  have hg := reduction_computes K n n M ops r d h
  apply le_antisymm h.1
  by_contra hn
  have hz : minorGcd M n = 0 := hg.2.1 n (by omega)
  have hI := (MinorIdeals.minorGcd_eq_zero_iff M n).mp hz
  have hmem := MinorIdeals.minor_mem M id id
  rw [hI] at hmem
  exact hdet hmem

theorem characteristic_smith : D05.Specs.InvariantFactorComputation.characteristic_smith := by
  intro K _ n A
  have hm := Matrix.charpoly_monic A
  refine ⟨hm, hm.ne_zero, ?_, ?_⟩
  · simp [Matrix.charpoly_natDegree_eq_dim]
  · obtain ⟨ops, r, d, hred, hg⟩ := smith_computation K n n A.charmatrix
    have hr : r = n := nonsingular_rank K n A.charmatrix ops r d hm.ne_zero hred
    subst r
    have htop : minorGcd A.charmatrix n = A.charpoly :=
      MinorIdeals.minorGcd_eq_monic_generator _ n _ hm (top_minorIdeal n A.charmatrix)
    refine ⟨ops, d, hred, hg, htop, (hg.1 n le_rfl).symm.trans htop, ?_⟩
    intro i hi
    exact (hred.2.2.1.1 i hi).isUnit_iff

end D05.M10.InvariantFactorComputation
