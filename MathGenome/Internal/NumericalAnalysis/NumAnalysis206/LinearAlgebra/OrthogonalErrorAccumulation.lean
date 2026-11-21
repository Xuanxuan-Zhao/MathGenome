import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.OrthogonalErrorAccumulation
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.OrthogonalErrorAccumulation
open MatrixData OrthogonalErrorDefinitions

private theorem columns_add {K : Type*} [RCLike K] {m n : ℕ}
    (A B : Mat K m n) (i : Fin n) : columns (A + B) i = columns A i + columns B i := by
  rfl

private theorem columns_mul {K : Type*} [RCLike K] {m n l : ℕ}
    (A : Mat K m n) (B : Mat K n l) (i : Fin l) :
    columns (A * B) i = A.toEuclideanLin (columns B i) := by
  ext k
  rfl

private theorem norm_unitary {K : Type*} [RCLike K] {m : ℕ}
    (U : Mat K m m) (hU : U.conjTranspose * U = 1) (x : Vec K m) :
    ‖U.toEuclideanLin x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h : inner K (U.toEuclideanLin x) (U.toEuclideanLin x) = inner K x x := by
    rw [← LinearMap.adjoint_inner_right, ← toEuclidean_adjoint]
    change inner K x (((U.conjTranspose).toEuclideanLin ∘ₗ U.toEuclideanLin) x) = _
    rw [← toEuclidean_mul, hU]
    simp
  have hr := congrArg RCLike.re h
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hr

private theorem product_unitary {K : Type*} [RCLike K] {m : ℕ}
    (H : ℕ → Mat K m m) (N : ℕ)
    (hH : ∀ j < N, (H j).conjTranspose * H j = 1) :
    (forwardProduct H N).conjTranspose * forwardProduct H N = 1 := by
  induction N with
  | zero => simp [forwardProduct]
  | succ j ih =>
    have hP := ih (fun k hk => hH k (Nat.lt_succ_of_lt hk))
    rw [forwardProduct, Matrix.conjTranspose_mul]
    calc
      (forwardProduct H j).conjTranspose * (H j).conjTranspose *
          (H j * forwardProduct H j) =
          (forwardProduct H j).conjTranspose *
            (((H j).conjTranspose * H j) * forwardProduct H j) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hH j (Nat.lt_succ_self j), one_mul, hP]

/-- Column growth and backward perturbation for a finite orthogonal trace. -/
theorem columnwise_accumulation :
    Specs.NumAnalysis206.OrthogonalErrorAccumulation.columnwise_accumulation := by
  intro K _ m n N A H B F c hB hH hc hstep hF
  have hbds : ∀ j ≤ N, ∀ i,
      ‖columns (B j) i‖ ≤ (∏ k ∈ Finset.range j, (1 + c k)) * ‖columns A i‖ ∧
      ‖columns (B j - forwardProduct H j * A) i‖ ≤
        ((∏ k ∈ Finset.range j, (1 + c k)) - 1) * ‖columns A i‖ := by
    intro j hj
    induction j with
    | zero =>
      intro i
      simp [hB, forwardProduct, MatrixData.columns,
        Specs.NumAnalysis206.MatrixData.columns_value,
        MatrixDefinitions.columns, D05.QrCholesky.columns]
      rfl
    | succ j ih =>
      have hjN : j < N := Nat.lt_of_succ_le hj
      have hprev := ih (Nat.le_of_lt hjN)
      intro i
      have hnorm := norm_unitary (H j) (hH j hjN)
      have hlocal := hF j hjN i
      have hcj := hc j hjN
      have hgrowth : ‖columns (B (j + 1)) i‖ ≤
          (1 + c j) * ‖columns (B j) i‖ := by
        rw [hstep j hjN, columns_add, columns_mul]
        calc
          _ ≤ ‖(H j).toEuclideanLin (columns (B j) i)‖ + ‖columns (F j) i‖ :=
            norm_add_le _ _
          _ ≤ ‖columns (B j) i‖ + c j * ‖columns (B j) i‖ := by
            rw [hnorm]
            exact add_le_add_right hlocal _
          _ = _ := by ring
      have herr : B (j + 1) - forwardProduct H (j + 1) * A =
          H j * (B j - forwardProduct H j * A) + F j := by
        rw [hstep j hjN, forwardProduct, Matrix.mul_sub, Matrix.mul_assoc]
        abel
      constructor
      · calc
          _ ≤ (1 + c j) * ‖columns (B j) i‖ := hgrowth
          _ ≤ (1 + c j) *
              ((∏ k ∈ Finset.range j, (1 + c k)) * ‖columns A i‖) :=
            mul_le_mul_of_nonneg_left (hprev i).1 (by linarith)
          _ = _ := by rw [Finset.prod_range_succ]; ring
      · rw [herr, columns_add, columns_mul]
        calc
          _ ≤ ‖(H j).toEuclideanLin
                (columns (B j - forwardProduct H j * A) i)‖ + ‖columns (F j) i‖ :=
            norm_add_le _ _
          _ = ‖columns (B j - forwardProduct H j * A) i‖ + ‖columns (F j) i‖ := by
            rw [hnorm]
          _ ≤ ((∏ k ∈ Finset.range j, (1 + c k)) - 1) * ‖columns A i‖ +
              c j * ‖columns (B j) i‖ := add_le_add (hprev i).2 hlocal
          _ ≤ ((∏ k ∈ Finset.range j, (1 + c k)) - 1) * ‖columns A i‖ +
              c j * ((∏ k ∈ Finset.range j, (1 + c k)) * ‖columns A i‖) :=
            add_le_add_right (mul_le_mul_of_nonneg_left (hprev i).1 hcj) _
          _ = _ := by rw [Finset.prod_range_succ]; ring
  have hP := product_unitary H N hH
  have hP' : forwardProduct H N * (forwardProduct H N).conjTranspose = 1 :=
    mul_eq_one_comm.mp hP
  refine ⟨fun j hj i => (hbds j hj i).1, ⟨hP, hP'⟩, ?_, ?_⟩
  · intro i
    have hpull : (forwardProduct H N).conjTranspose * B N - A =
        (forwardProduct H N).conjTranspose * (B N - forwardProduct H N * A) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    change ‖columns ((forwardProduct H N).conjTranspose * B N - A) i‖ ≤ _
    rw [hpull, columns_mul, norm_unitary _ (by simpa using hP')]
    exact (hbds N le_rfl i).2
  · intro hN
    subst N
    simp [forwardProduct, hB]

end NumAnalysis206.OrthogonalErrorAccumulation
