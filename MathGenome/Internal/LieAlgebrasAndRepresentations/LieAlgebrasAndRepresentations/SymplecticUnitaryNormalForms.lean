import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic

/-! Quaternionic orthonormal frames for the compact symplectic normal forms. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms

open Matrix Module Submodule
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC (Mat)
open Specs.LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms
open scoped ComplexConjugate Matrix

local notation "⟪" x ", " y "⟫" => inner ℂ x y

private def paired {E : Type*} {ι : Type*} (j : E → E) (v : ι → E) : ι ⊕ ι → E :=
  Sum.elim v (j ∘ v)

section Frames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem orthonormal_sum {ι κ : Type*} {v : ι → E} {w : κ → E}
    (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (hvw : ∀ i k, ⟪v i, w k⟫ = 0) : Orthonormal ℂ (Sum.elim v w) := by
  classical
  rw [orthonormal_iff_ite] at hv hw ⊢
  rintro (i | k) (i' | k')
  · simpa using hv i i'
  · simp [hvw]
  · simpa using (inner_eq_zero_symm.mp (hvw i' k))
  · simpa using hw k k'

private theorem mem_orthogonal_range {ι : Type*} (v : ι → E) (x : E) :
    x ∈ (span ℂ (Set.range v))ᗮ ↔ ∀ i, ⟪v i, x⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · exact fun h i => h _ (subset_span (Set.mem_range_self i))
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; exact h i
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [inner_add_left, h₁, h₂]
    | smul c _ _ h => simp [inner_smul_left, h]

/-- Extend an orthonormal quaternionic frame by a unit vector perpendicular to it. -/
private theorem extend_frame (j : E →ₛₗ[starRingEnd ℂ] E)
    (hj : ∀ x y, ⟪j x, j y⟫ = ⟪y, x⟫) (hjj : ∀ x, j (j x) = -x)
    {m : ℕ} {v : Fin m → E} (hv : Orthonormal ℂ (paired j v))
    {x : E} (hx : ‖x‖ = 1)
    (hperp : x ∈ (span ℂ (Set.range (paired j v)))ᗮ) :
    Orthonormal ℂ
      (paired j ((Sum.elim v (fun _ : Fin 1 => x)) ∘ finSumFinEquiv.symm)) := by
  have hjx : ⟪x, j x⟫ = 0 := by
    have h := hj x (j x)
    rw [hjj, inner_neg_right, _root_.neg_eq_self] at h
    exact inner_eq_zero_symm.mp h
  have hpair : Orthonormal ℂ (paired j (fun _ : Fin 1 => x)) := by
    apply orthonormal_sum
    · simpa using hx
    · apply (orthonormal_subsingleton_iff).mpr
      intro _
      have he := hj x x
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hx] at he
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by exact_mod_cast he)
    · intro _ _
      exact hjx
  have ho := (mem_orthogonal_range _ _).mp hperp
  have hcross : ∀ i k, ⟪paired j v i, paired j (fun _ : Fin 1 => x) k⟫ = 0 := by
    rintro i (k | k)
    · exact ho i
    · cases i with
      | inl i =>
        have h := hj (j (v i)) x
        have hz : ⟪x, j (v i)⟫ = 0 := inner_eq_zero_symm.mp (ho (Sum.inr i))
        rw [hjj, inner_neg_left, hz, neg_eq_zero] at h
        exact h
      | inr i =>
        exact (hj (v i) x).trans (inner_eq_zero_symm.mp (ho (Sum.inl i)))
  let e : (Fin (m + 1) ⊕ Fin (m + 1)) ≃ (Fin m ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 1) :=
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
      (Equiv.sumSumSumComm _ _ _ _)
  have he := (orthonormal_sum hv hpair hcross).comp e e.injective
  convert he using 1
  funext i
  cases i with
  | inl i =>
    simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      paired, Function.comp_apply, Sum.elim_inl]
    cases finSumFinEquiv.symm i <;> rfl
  | inr i =>
    simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      paired, Function.comp_apply, Sum.elim_inr]
    cases finSumFinEquiv.symm i <;> rfl

/-- Build quaternionic pairs one at a time in the orthogonal complement of
the existing pairs. The selector specifies which eigenvalues may be used
for the first vector of a pair. -/
private theorem spectral_frame [FiniteDimensional ℂ E] (n : ℕ)
    (hdim : finrank ℂ E = n + n)
    (j : E →ₛₗ[starRingEnd ℂ] E)
    (hj : ∀ x y, ⟪j x, j y⟫ = ⟪y, x⟫) (hjj : ∀ x, j (j x) = -x)
    (T : E →ₗ[ℂ] E) (hT : ∀ x y, ⟪T x, T y⟫ = ⟪x, y⟫)
    (hcomm : ∀ x, T (j x) = j (T x))
    (P : ℂ → Prop)
    (select : ∀ K : Submodule ℂ E, K ≠ ⊥ →
      (∀ x ∈ K, j x ∈ K) → (∀ x ∈ K, T x ∈ K) →
      ∃ x ∈ K, x ≠ 0 ∧ ∃ c, P c ∧ T x = c • x) :
    ∃ (v : Fin n → E) (c : Fin n → ℂ),
      Orthonormal ℂ (paired j v) ∧ ∀ i, P (c i) ∧ T (v i) = c i • v i := by
  have build (m : ℕ) (hm : m ≤ n) :
      ∃ (v : Fin m → E) (c : Fin m → ℂ),
        Orthonormal ℂ (paired j v) ∧ ∀ i, P (c i) ∧ T (v i) = c i • v i := by
    induction m with
    | zero => exact ⟨Fin.elim0, Fin.elim0, Orthonormal.of_isEmpty _, fun i => i.elim0⟩
    | succ m ih =>
      obtain ⟨v, c, hv, hc⟩ := ih (Nat.le_of_succ_le hm)
      let W := span ℂ (Set.range (paired j v))
      have hW : Wᗮ ≠ ⊥ := by
        intro h
        have he : W = ⊤ := Submodule.orthogonal_eq_bot_iff.mp h
        have hcard := finrank_span_eq_card hv.linearIndependent
        change finrank ℂ W = _ at hcard
        rw [he, finrank_top, hdim, Fintype.card_sum, Fintype.card_fin] at hcard
        omega
      have hjW : ∀ y ∈ Wᗮ, j y ∈ Wᗮ := by
        intro y hy
        have hy' := (mem_orthogonal_range _ _).mp hy
        apply (mem_orthogonal_range _ _).mpr
        rintro (i | i)
        · have h := hj (j (v i)) y
          have hz : ⟪y, j (v i)⟫ = 0 := inner_eq_zero_symm.mp (hy' (Sum.inr i))
          rw [hjj, inner_neg_left, hz, neg_eq_zero] at h
          exact h
        · exact (hj (v i) y).trans (inner_eq_zero_symm.mp (hy' (Sum.inl i)))
      have heig (i : Fin m ⊕ Fin m) :
          ∃ d : ℂ, T (paired j v i) = d • paired j v i := by
        cases i with
        | inl i => exact ⟨c i, (hc i).2⟩
        | inr i =>
          refine ⟨conj (c i), ?_⟩
          change T (j (v i)) = _
          rw [hcomm, (hc i).2, map_smulₛₗ]
          rfl
      have hTW : ∀ y ∈ Wᗮ, T y ∈ Wᗮ := by
        intro y hy
        apply (mem_orthogonal_range _ _).mpr
        intro i
        obtain ⟨d, hd⟩ := heig i
        have hd₀ : d ≠ 0 := by
          intro he
          have hz := hT (paired j v i) (paired j v i)
          rw [hd, he, zero_smul, inner_zero_left, inner_self_eq_norm_sq_to_K,
            hv.norm_eq_one] at hz
          simp at hz
        have h := hT (paired j v i) y
        rw [hd, inner_smul_left, (mem_orthogonal_range _ _).mp hy i] at h
        exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr hd₀)
      obtain ⟨x, hx, hx₀, d, hdP, hd⟩ := select Wᗮ hW hjW hTW
      let z := ((‖x‖ : ℂ)⁻¹) • x
      have hz : ‖z‖ = 1 := norm_smul_inv_norm hx₀
      have hzd : T z = d • z := by
        dsimp [z]
        rw [map_smul, hd, smul_comm]
      refine ⟨(Sum.elim v (fun _ : Fin 1 => z)) ∘ finSumFinEquiv.symm,
        (Sum.elim c (fun _ : Fin 1 => d)) ∘ finSumFinEquiv.symm,
        extend_frame j hj hjj hv hz (Wᗮ.smul_mem _ hx), ?_⟩
      intro i
      dsimp [Function.comp_def]
      rcases finSumFinEquiv.symm i with k | k
      · exact hc k
      · exact ⟨hdP, hzd⟩
  exact build n le_rfl

end Frames


section Matrices

private abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n ⊕ Fin n)

private def quaternionic (n : ℕ) : V n →ₛₗ[starRingEnd ℂ] V n where
  toFun x := WithLp.toLp 2 (Sum.elim (fun i => -conj (x (Sum.inr i)))
    (fun i => conj (x (Sum.inl i))))
  map_add' x y := by
    ext (i | i) <;> simp [add_comm]
  map_smul' c x := by
    ext (i | i) <;> simp [map_mul, mul_neg]

private theorem quaternionic_mulVec {n : ℕ} (x : V n) :
    (quaternionic n x).ofLp = Matrix.J (Fin n) ℂ *ᵥ star x.ofLp := by
  funext i
  cases i <;> simp [quaternionic, Matrix.J, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec]

private theorem quaternionic_sq {n : ℕ} (x : V n) :
    quaternionic n (quaternionic n x) = -x := by
  ext (i | i) <;> simp [quaternionic]

private theorem quaternionic_inner {n : ℕ} (x y : V n) :
    ⟪quaternionic n x, quaternionic n y⟫ = ⟪y, x⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, quaternionic, mul_comm, add_comm]

private theorem unitary_inner {n : ℕ} {A : Mat n} (hA : Aᴴ * A = 1) (x y : V n) :
    ⟪A.toEuclideanLin x, A.toEuclideanLin y⟫ = ⟪x, y⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.star_mulVec]
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_vecMul, hA, vecMul_one, dotProduct_comm]

private theorem transpose_mul_conjugate {n : ℕ} {A : Mat n} (hA : Aᴴ * A = 1) :
    Aᵀ * A.map (starRingEnd ℂ) = 1 := by
  have he : Aᴴ.map (starRingEnd ℂ) = Aᵀ := by
    ext a b
    simp [conjTranspose_apply, Matrix.map_apply]
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), he] using
    congrArg (fun M : Mat n => M.map (starRingEnd ℂ)) hA

private theorem symplectic_comm_quaternionic {n : ℕ} {A : Mat n}
    (hA : A ∈ symplecticGroup (Fin n) ℂ) (hu : Aᴴ * A = 1) (x : V n) :
    A.toEuclideanLin (quaternionic n x) = quaternionic n (A.toEuclideanLin x) := by
  have hJ : A * Matrix.J (Fin n) ℂ = Matrix.J (Fin n) ℂ * A.map (starRingEnd ℂ) := by
    calc
      _ = (A * Matrix.J (Fin n) ℂ * Aᵀ) * A.map (starRingEnd ℂ) := by
        rw [Matrix.mul_assoc (_ * _), transpose_mul_conjugate hu, Matrix.mul_one]
      _ = _ := by rw [SymplecticGroup.mem_iff.mp hA]
  apply WithLp.ofLp_injective
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, quaternionic_mulVec, Matrix.mulVec_mulVec]
  rw [hJ, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.mulVec_transpose Aᴴ]
  rfl

private def columns {n : ℕ} (v : Fin n ⊕ Fin n → V n) : Mat n :=
  fun a b => v b a

private theorem paired_columns_unitary {n : ℕ} {v : Fin n → V n}
    (hv : Orthonormal ℂ (paired (quaternionic n) v)) :
    (columns (paired (quaternionic n) v))ᴴ * columns (paired (quaternionic n) v) = 1 := by
  ext a b
  rw [← inner_matrix_col_col]
  change ⟪paired (quaternionic n) v a, paired (quaternionic n) v b⟫ = _
  rw [orthonormal_iff_ite.mp hv]
  simp [Matrix.one_apply]

private theorem paired_columns_symplectic {n : ℕ} {v : Fin n → V n}
    (hv : Orthonormal ℂ (paired (quaternionic n) v)) :
    columns (paired (quaternionic n) v) ∈ symplecticGroup (Fin n) ℂ := by
  let M := columns (paired (quaternionic n) v)
  have hcomm : M * Matrix.J (Fin n) ℂ = Matrix.J (Fin n) ℂ * M.map (starRingEnd ℂ) := by
    have hr (a : Fin n ⊕ Fin n) :
        (M * Matrix.J (Fin n) ℂ) a = Sum.elim (fun i => M a (Sum.inr i))
          (fun i => -M a (Sum.inl i)) := by
      rw [Matrix.mul_apply_eq_vecMul, Matrix.J, Matrix.vecMul_fromBlocks]
      funext i
      cases i <;> simp [Matrix.vecMul_neg]
    have hc (b : Fin n ⊕ Fin n) (a : Fin n ⊕ Fin n) :
        (Matrix.J (Fin n) ℂ * M.map (starRingEnd ℂ)) a b =
          quaternionic n (paired (quaternionic n) v b) a := by
      have hx := congrFun (quaternionic_mulVec (paired (quaternionic n) v b)) a
      exact hx.symm
    ext a b
    rw [hc]
    rw [hr]
    cases b with
    | inl b => rfl
    | inr b =>
      change -(v b a) = quaternionic n (quaternionic n (v b)) a
      rw [quaternionic_sq]
      rfl
  have hu : Mᴴ * M = 1 := paired_columns_unitary hv
  have hinv : M.map (starRingEnd ℂ) * Mᵀ = 1 := mul_eq_one_comm.mp (transpose_mul_conjugate hu)
  rw [SymplecticGroup.mem_iff]
  change M * Matrix.J (Fin n) ℂ * Mᵀ = _
  rw [hcomm, Matrix.mul_assoc, hinv, Matrix.mul_one]

private theorem columns_eigen {n : ℕ} {A : Mat n} {v : Fin n → V n} {c : Fin n → ℂ}
    (ha : ∀ i, A.toEuclideanLin (v i) = c i • v i)
    (hcomm : ∀ x : V n, A.toEuclideanLin (quaternionic n x) =
      quaternionic n (A.toEuclideanLin x)) :
    A * columns (paired (quaternionic n) v) =
      columns (paired (quaternionic n) v) * diagonal (Sum.elim c (conj ∘ c)) := by
  have h (b : Fin n ⊕ Fin n) :
      A.toEuclideanLin (paired (quaternionic n) v b) =
        (Sum.elim c (conj ∘ c) b) • paired (quaternionic n) v b := by
    cases b with
    | inl i => exact ha i
    | inr i =>
      change A.toEuclideanLin (quaternionic n (v i)) = _
      rw [hcomm, ha, map_smulₛₗ]
      rfl
  ext a b
  rw [Matrix.mul_diagonal]
  exact congrArg (fun x : V n => x a) (h b) |>.trans (mul_comm _ _)

private theorem unitary_inv {n : ℕ} {A : Sp n} (hu : (A : Mat n)ᴴ * (A : Mat n) = 1) :
    ((A⁻¹ : Sp n) : Mat n) = (A : Mat n)ᴴ := by
  have h : (A : Mat n) * ((A⁻¹ : Sp n) : Mat n) = 1 :=
    congrArg Subtype.val (mul_inv_cancel A)
  calc
    _ = ((A : Mat n)ᴴ * (A : Mat n)) * ((A⁻¹ : Sp n) : Mat n) := by rw [hu, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

private theorem unitary_inv_mem {n : ℕ} {A : Sp n}
    (hu : (A : Mat n)ᴴ * (A : Mat n) = 1) :
    ((A⁻¹ : Sp n) : Mat n)ᴴ * ((A⁻¹ : Sp n) : Mat n) = 1 := by
  rw [unitary_inv hu, Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hu

private theorem unitary_mul_mem {n : ℕ} {A B : Sp n}
    (ha : (A : Mat n)ᴴ * (A : Mat n) = 1)
    (hb : (B : Mat n)ᴴ * (B : Mat n) = 1) :
    ((A * B : Sp n) : Mat n)ᴴ * ((A * B : Sp n) : Mat n) = 1 := by
  simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc (B : Mat n)ᴴ, ← Matrix.mul_assoc (A : Mat n)ᴴ, ha, Matrix.one_mul, hb]

private theorem eigen_conjugation {n : ℕ} {A B : Sp n} {D : Mat n}
    (h : (A : Mat n) * (B : Mat n) = (B : Mat n) * D) :
    ((B⁻¹ * A * B : Sp n) : Mat n) = D := by
  have hinv : ((B⁻¹ : Sp n) : Mat n) * (B : Mat n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel B)
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Matrices


section Eigenvalues

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- On a nonzero invariant subspace, a square root of a scalar has an
eigenvector of one of the two possible eigenvalues. -/
private theorem select_eigenvector (T : E →ₗ[ℂ] E) (c : ℂ)
    (hT : ∀ x, T (T x) = (c * c) • x)
    (K : Submodule ℂ E) (hK : K ≠ ⊥) (hTK : ∀ x ∈ K, T x ∈ K) :
    ∃ x ∈ K, x ≠ 0 ∧ (T x = c • x ∨ T x = (-c) • x) := by
  obtain ⟨x, hx, hx₀⟩ := (K.ne_bot_iff).mp hK
  by_cases h : T x + c • x = 0
  · refine ⟨x, hx, hx₀, Or.inr ?_⟩
    simpa only [neg_smul] using eq_neg_iff_add_eq_zero.mpr h
  · refine ⟨T x + c • x, K.add_mem (hTK x hx) (K.smul_mem c hx), h, Or.inl ?_⟩
    rw [map_add, hT, map_smul, smul_add, smul_smul, add_comm]

end Eigenvalues

private theorem signed_order {n : ℕ} (c : Fin n → ℂ) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    ∃ p : ℕ, p ≤ n ∧ ∃ e : Fin n ≃ Fin n,
      ∀ i, c (e i) = if i.val < p then 1 else -1 := by
  classical
  let P := {i : Fin n // c i = 1}
  let Q := {i : Fin n // c i ≠ 1}
  let p := Fintype.card P
  let q := Fintype.card Q
  let partition : P ⊕ Q ≃ Fin n := Equiv.sumCompl (fun i => c i = 1)
  have hcard : p + q = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr partition
  let f := (Equiv.sumCongr (Fintype.equivFin P).symm (Fintype.equivFin Q).symm).trans partition
  let g := finSumFinEquiv.trans (finCongr hcard)
  refine ⟨p, by omega, g.symm.trans f, ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := g.surjective i
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  cases j with
  | inl j =>
    have hi : (g (Sum.inl j)).val < p := by simp [g]
    rw [ite_eq_left hi]
    exact ((Fintype.equivFin P).symm j).property
  | inr j =>
    have hi : ¬ (g (Sum.inr j)).val < p := by simp [g]
    rw [ite_eq_right hi]
    exact (hc _).resolve_left ((Fintype.equivFin Q).symm j).property

private theorem signed_diagonal {n p : ℕ} {c : Fin n → ℂ}
    (hc : ∀ i, c i = if i.val < p then 1 else -1) :
    diagonal (Sum.elim c (conj ∘ c)) = signatureMatrix n p := by
  rw [signatureMatrix, signatureDiagonal, fromBlocks_diagonal]
  congr 1
  funext i
  cases i with
  | inl i => exact hc i
  | inr i => by_cases h : i.val < p <;> simp [hc, h]

/-- A compact symplectic involution is conjugate to the quaternionic
signature matrix, including both definite signatures. -/
theorem squareOne : squareOneType := by
  intro n _ A hu hs
  let M : Mat n := A
  let T := M.toEuclideanLin
  let j := quaternionic n
  have hcomm := symplectic_comm_quaternionic A.property hu
  have hT (x : V n) : T (T x) = ((1 : ℂ) * 1) • x := by
    simpa [T, M] using congrArg (fun B : Mat n => B.toEuclideanLin x) hs
  have hdim : finrank ℂ (V n) = n + n := by simp [V]
  obtain ⟨v, c, hv, hc⟩ :=
    spectral_frame n hdim j quaternionic_inner quaternionic_sq T (unitary_inner hu) hcomm
      (fun a => a = 1 ∨ a = -1) (by
        intro K hK _ hTK
        obtain ⟨x, hx, hx₀, he | he⟩ := select_eigenvector T 1 hT K hK hTK
        · exact ⟨x, hx, hx₀, 1, Or.inl rfl, he⟩
        · exact ⟨x, hx, hx₀, -1, Or.inr rfl, he⟩)
  obtain ⟨p, hp, e, he⟩ := signed_order c (fun i => (hc i).1)
  have hw : Orthonormal ℂ (paired j (v ∘ e)) := by
    have h := hv.comp (Equiv.sumCongr e e) (Equiv.sumCongr e e).injective
    convert h using 1
    funext i
    cases i <;> rfl
  let C : Sp n := ⟨columns (paired j (v ∘ e)), paired_columns_symplectic hw⟩
  have hC : (C : Mat n)ᴴ * (C : Mat n) = 1 := paired_columns_unitary hw
  have hAC : (A : Mat n) * (C : Mat n) = (C : Mat n) * signatureMatrix n p := by
    rw [← signed_diagonal he]
    exact columns_eigen (fun i => (hc (e i)).2) hcomm
  refine ⟨p, hp, C⁻¹, unitary_inv_mem hC, ?_⟩
  rw [inv_inv]
  exact eigen_conjugation hAC

private def imaginaryDiagonal (n : ℕ) : Mat n :=
  diagonal (Sum.elim (fun _ => Complex.I) (fun _ => -Complex.I))

private theorem imaginary_normal_form {n : ℕ} (A : Sp n)
    (hu : (A : Mat n)ᴴ * (A : Mat n) = 1)
    (hs : (A : Mat n) * (A : Mat n) = -1) :
    ∃ C : Sp n, (C : Mat n)ᴴ * (C : Mat n) = 1 ∧
      ((C⁻¹ * A * C : Sp n) : Mat n) = imaginaryDiagonal n := by
  let M : Mat n := A
  let T := M.toEuclideanLin
  let j := quaternionic n
  have hcomm := symplectic_comm_quaternionic A.property hu
  have hT (x : V n) : T (T x) = (Complex.I * Complex.I) • x := by
    simpa [T, M, Complex.I_mul_I] using congrArg (fun B : Mat n => B.toEuclideanLin x) hs
  have hdim : finrank ℂ (V n) = n + n := by simp [V]
  obtain ⟨v, c, hv, hc⟩ :=
    spectral_frame n hdim j quaternionic_inner quaternionic_sq T (unitary_inner hu) hcomm
      (fun a => a = Complex.I) (by
        intro K hK hjK hTK
        obtain ⟨x, hx, hx₀, he | he⟩ := select_eigenvector T Complex.I hT K hK hTK
        · exact ⟨x, hx, hx₀, Complex.I, rfl, he⟩
        · refine ⟨j x, hjK x hx, ?_, Complex.I, rfl, ?_⟩
          · intro h
            have hz := quaternionic_sq x
            change j (j x) = -x at hz
            rw [h, map_zero, zero_eq_neg] at hz
            exact hx₀ hz
          · change (A : Mat n).toEuclideanLin (j x) = _
            rw [hcomm]
            change j (T x) = _
            rw [he, map_smulₛₗ]
            simp)
  let C : Sp n := ⟨columns (paired j v), paired_columns_symplectic hv⟩
  have hAC : (A : Mat n) * (C : Mat n) = (C : Mat n) * imaginaryDiagonal n := by
    have hcI : c = fun _ => Complex.I := funext fun i => (hc i).1
    have h := columns_eigen (A := M) (fun i => (hc i).2) hcomm
    rw [hcI] at h
    simpa [C, M, imaginaryDiagonal, Function.comp_def] using h
  exact ⟨C, paired_columns_unitary hv, eigen_conjugation hAC⟩

/-- Every compact symplectic matrix of square `-1` is conjugate to the standard
symplectic matrix. Apply the imaginary diagonalization to both matrices. -/
theorem squareNegOne : squareNegOneType := by
  intro n _ A hu hs
  let J₀ := SymplecticGroup.symJ (Fin n) ℂ
  have hJs : Matrix.J (Fin n) ℂ * Matrix.J (Fin n) ℂ = -1 := Matrix.J_squared _ _
  have hJu : (J₀ : Mat n)ᴴ * (J₀ : Mat n) = 1 := by
    change (Matrix.J (Fin n) ℂ)ᴴ * Matrix.J (Fin n) ℂ = 1
    have h : (Matrix.J (Fin n) ℂ)ᴴ = -(Matrix.J (Fin n) ℂ) := by
      change ((Matrix.J (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = _
      rw [Matrix.map_J, Matrix.J_transpose]
    rw [h, Matrix.neg_mul, hJs, neg_neg]
  obtain ⟨C, hC, hc⟩ := imaginary_normal_form A hu hs
  obtain ⟨D, hD, hd⟩ := imaginary_normal_form J₀ hJu hJs
  have h : C⁻¹ * A * C = D⁻¹ * J₀ * D := Subtype.ext (hc.trans hd.symm)
  refine ⟨D * C⁻¹, unitary_mul_mem hD (unitary_inv_mem hC), ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  calc
    D * C⁻¹ * A * (C * D⁻¹) = D * (C⁻¹ * A * C) * D⁻¹ := by simp only [_root_.mul_assoc]
    _ = _ := by simp [h, ← _root_.mul_assoc, J₀]

end LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms
