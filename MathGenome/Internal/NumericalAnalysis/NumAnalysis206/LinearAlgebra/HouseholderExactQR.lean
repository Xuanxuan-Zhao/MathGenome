import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderExactQR
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderReflector
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix
namespace NumAnalysis206.HouseholderExactQR
open NumAnalysis206.MatrixDefinitions NumAnalysis206.HouseholderDefinitions
open NumAnalysis206.HouseholderQRDefinitions

lemma split_inl {m k : ℕ} (h : k ≤ m) (i : Fin k) :
    (split m k h (Sum.inl i)).val = i.val := by
  simp [split, finSumFinEquiv_apply_left]

lemma split_inr {m k : ℕ} (h : k ≤ m) (i : Fin (m-k)) :
    (split m k h (Sum.inr i)).val = k + i.val := by
  simp [split, finSumFinEquiv_apply_right]

lemma blockLift_orthogonal {m k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k))
    (hT : T.conjTranspose * T = 1) :
    (blockLift h T).conjTranspose * blockLift h T = 1 := by
  rw [blockLift, conjTranspose_submatrix, submatrix_mul_equiv, fromBlocks_conjTranspose]
  simp only [conjTranspose_one, conjTranspose_zero, fromBlocks_multiply,
    mul_one, hT]
  simp

lemma step_orthogonal {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    (step x).conjTranspose * step x = 1 := by
  by_cases hx : x = 0
  · simp [HouseholderDefinitions.step, hx]
  · simpa [HouseholderDefinitions.step, hx] using
      HouseholderReflector.reflector_orthogonal _ (HouseholderReflector.direction_ne_zero x hx)

lemma step_maps_below {d : ℕ} [NeZero d] (x : Vec ℝ d) (i : Fin d) (hi : i ≠ 0) :
    (step x *ᵥ ⇑x) i = 0 := by
  by_cases hx : x = 0
  · simp [hx, HouseholderDefinitions.step]
  · rw [show step x = reflector (direction x) by simp [HouseholderDefinitions.step, hx],
      HouseholderReflector.reflector_maps x hx]
    simp [HouseholderReflector.firstVector_apply, hi]

/-- The block extension acts on precisely the original tail coordinates. -/
lemma blockLift_mul {m n k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k))
    (B : Mat ℝ m n) :
    (blockLift h T * B).submatrix (split m k h) id =
      fromRows (B.submatrix (fun i => split m k h (Sum.inl i)) id)
        (T * B.submatrix (fun i => split m k h (Sum.inr i)) id) := by
  let e := split m k h
  have hB : B.submatrix e id =
      fromRows (B.submatrix (fun i => e (Sum.inl i)) id)
        (B.submatrix (fun i => e (Sum.inr i)) id) := by
    ext (i | i) j <;> rfl
  calc
    _ = (fromBlocks (1 : Mat ℝ k k) 0 0 T) * B.submatrix e id := by
      rw [← submatrix_mul_equiv _ _ e e id]
      congr 1
      ext i j
      simp [blockLift, e]
    _ = _ := by rw [hB, fromBlocks_mul_fromRows]; simp [e]

lemma blockLift_mul_inl {m n k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k))
    (B : Mat ℝ m n) (i : Fin k) (c : Fin n) :
    (blockLift h T * B) (split m k h (Sum.inl i)) c =
      B (split m k h (Sum.inl i)) c := by
  exact congrFun (congrFun (blockLift_mul h T B) (Sum.inl i)) c

lemma blockLift_mul_inr {m n k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k))
    (B : Mat ℝ m n) (i : Fin (m-k)) (c : Fin n) :
    (blockLift h T * B) (split m k h (Sum.inr i)) c =
      (T *ᵥ (fun a => B (split m k h (Sum.inr a)) c)) i := by
  exact congrFun (congrFun (blockLift_mul h T B) (Sum.inr i)) c

lemma update_orthogonal {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n) :
    (update B j h).conjTranspose * update B j h = 1 := by
  have : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  unfold update
  exact blockLift_orthogonal _ _ (step_orthogonal _)

lemma update_preserves {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (hc : Cleared B j.val) (c : Fin n) (hj : c.val < j.val) (i : Fin m) :
    (update B j h * B) i c = B i c := by
  obtain ⟨a, rfl⟩ := (split m j.val (by omega)).surjective i
  cases a with
  | inl a => exact blockLift_mul_inl _ _ B a c
  | inr a =>
    unfold update
    rw [blockLift_mul_inr]
    have hz (b : Fin (m-j.val)) : B (split m j.val (by omega) (Sum.inr b)) c = 0 := by
      apply hc c hj
      rw [split_inr]
      omega
    simp [Matrix.mulVec, dotProduct, hz]

lemma update_clears {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (i : Fin m) (hi : j.val < i.val) : (update B j h * B) i j = 0 := by
  let a : Fin (m-j.val) := ⟨i.val-j.val, by omega⟩
  have he : split m j.val (by omega) (Sum.inr a) = i := by
    apply Fin.ext
    rw [split_inr]
    dsimp [a]
    omega
  rw [← he]
  unfold update
  rw [blockLift_mul_inr]
  have : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  apply step_maps_below (tail B j h) a
  intro ha
  have hz := congrArg Fin.val ha
  change i.val - j.val = 0 at hz
  omega

theorem zero_tail : Specs.NumAnalysis206.HouseholderExactQR.zero_tail := by
  intro m n B h j hz
  simp [update, hz, HouseholderDefinitions.step, blockLift]

theorem one_step : Specs.NumAnalysis206.HouseholderExactQR.one_step := by
  intro m n B h j
  refine ⟨update_orthogonal B h j, fun hc => ⟨update_preserves B h j hc, ?_⟩⟩
  intro c hck i hci
  by_cases hcj : c.val < j.val
  · rw [update_preserves B h j hc c hcj i]
    exact hc c hcj i hci
  · have he : c = j := Fin.ext (by omega)
    subst c
    exact update_clears B h j i hci

theorem construction : Specs.NumAnalysis206.HouseholderExactQR.construction := by
  intro m n A h k hk
  induction k with
  | zero => simp [run, product, Cleared]
  | succ k ih =>
    obtain ⟨hr, hp, hc⟩ := ih (by omega)
    have hkn : k < n := by omega
    have hs := one_step (run A h k) h ⟨k,hkn⟩
    simp only [run, product, dite_eq_left hkn]
    refine ⟨?_, ?_, hs.2 hc |>.2⟩
    · simp only [hr, Matrix.mul_assoc]
    · rw [conjTranspose_mul]
      calc
        _ = (product A h k).conjTranspose *
            ((update (run A h k) ⟨k,hkn⟩ h).conjTranspose *
              update (run A h k) ⟨k,hkn⟩ h) * product A h k := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hs.1, mul_one, hp]

lemma split_inl_eq {m n : ℕ} (h : n ≤ m) (i : Fin n) :
    split m n h (Sum.inl i) = Fin.castLE h i := by
  exact Fin.ext (split_inl h i)

lemma reduced_factorization {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m)
    (P : Mat ℝ m m) (B : Mat ℝ m n)
    (hr : B = P * A) (hp : P.conjTranspose * P = 1) (hc : Cleared B n) :
    A = P.conjTranspose.submatrix id (Fin.castLE h) * B.submatrix (Fin.castLE h) id ∧
    (P.conjTranspose.submatrix id (Fin.castLE h)).conjTranspose *
      P.conjTranspose.submatrix id (Fin.castLE h) = 1 := by
  have hp' : P * P.conjTranspose = 1 := mul_eq_one_comm.mp hp
  have hB : B.submatrix (split m n h) id =
      fromRows (B.submatrix (Fin.castLE h) id) (0 : Mat ℝ (m-n) n) := by
    ext (i | i) j
    · simp [split_inl_eq]
    · apply hc j j.isLt
      rw [split_inr]
      omega
  have hP : P.conjTranspose.submatrix id (split m n h) =
      fromCols (P.conjTranspose.submatrix id (Fin.castLE h))
        (P.conjTranspose.submatrix id (fun i => split m n h (Sum.inr i))) := by
    ext i (j | j) <;> simp [split_inl_eq]
  constructor
  · calc
      A = P.conjTranspose * B := by rw [hr, ← Matrix.mul_assoc, hp, Matrix.one_mul]
      _ = P.conjTranspose.submatrix id (split m n h) * B.submatrix (split m n h) id := by
        rw [submatrix_mul_equiv]; rfl
      _ = _ := by rw [hB, hP, fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  · rw [conjTranspose_submatrix, conjTranspose_conjTranspose]
    calc
      _ = (P * P.conjTranspose).submatrix (Fin.castLE h) (Fin.castLE h) :=
        (submatrix_mul P P.conjTranspose (Fin.castLE h) id (Fin.castLE h)
          Function.bijective_id).symm
      _ = 1 := by rw [hp']; exact submatrix_one _ (Fin.castLE_injective h)

theorem exact_qr : Specs.NumAnalysis206.HouseholderExactQR.exact_qr := by
  intro m n A h
  obtain ⟨hr, hp, hc⟩ := construction A h n le_rfl
  obtain ⟨hqr, hq⟩ := reduced_factorization A h _ _ hr hp hc
  refine ⟨?_, hqr, hq, ?_⟩
  · intro i hi j
    exact hc j j.isLt i (by omega)
  · intro i j hji
    exact hc j j.isLt (Fin.castLE h i) hji

lemma signPlus_mul_self (t : ℝ) : signPlus t * signPlus t = 1 := by
  unfold HouseholderDefinitions.signPlus
  split_ifs <;> norm_num

lemma signs_self {n : ℕ} (R : Mat ℝ n n) : signs R * signs R = 1 := by
  unfold signs
  rw [diagonal_mul_diagonal]
  simp only [signPlus_mul_self, diagonal_one]

lemma signs_conjTranspose {n : ℕ} (R : Mat ℝ n n) : (signs R).conjTranspose = signs R := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [signs, conjTranspose_apply]
  · simp [signs, conjTranspose_apply, hij, Ne.symm hij]

lemma signPlus_mul_pos (t : ℝ) (ht : t ≠ 0) : 0 < signPlus t * t := by
  unfold HouseholderDefinitions.signPlus
  split_ifs with h
  · simpa using lt_of_le_of_ne h (Ne.symm ht)
  · simp only [neg_one_mul]
    linarith

/-- Full rank is used only here, after the unconditional construction. -/
lemma rFactor_diag_ne_zero {m n : ℕ} (A : Mat ℝ m n) (h : n ≤ m)
    (hA : FullColumnRank A) : ∀ i, rFactor A h i i ≠ 0 := by
  obtain ⟨_, hqr, _, htri⟩ := exact_qr A h
  have hAinj := (MatrixData.fullColumnRank_iff_injective A).mp hA
  have hRi : Function.Injective (rFactor A h).mulVec := by
    intro x y hxy
    have he : A.toEuclideanLin (WithLp.toLp 2 x) = A.toEuclideanLin (WithLp.toLp 2 y) := by
      ext i
      change (A *ᵥ x) i = (A *ᵥ y) i
      rw [hqr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
    have he' := hAinj he
    exact congrArg (fun v : Vec ℝ n => ⇑v) he'
  have hunit : IsUnit (rFactor A h) := mulVec_injective_iff_isUnit.mp hRi
  have hdet : (rFactor A h).det ≠ 0 := ((isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have ht : (rFactor A h).IsUpperTriangular := by
    intro i j hij
    exact htri i j hij
  exact ht.det_ne_zero_iff.mp hdet

theorem positive_diagonal : Specs.NumAnalysis206.HouseholderExactQR.positive_diagonal := by
  intro m n A h hA
  obtain ⟨_, hqr, hq, ht⟩ := exact_qr A h
  have hd := rFactor_diag_ne_zero A h hA
  change A = (qFactor A h * signs (rFactor A h)) * (signs (rFactor A h) * rFactor A h) ∧
    (qFactor A h * signs (rFactor A h)).conjTranspose *
      (qFactor A h * signs (rFactor A h)) = 1 ∧
    (signs (rFactor A h) * rFactor A h).IsUpperTriangular ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      A = qFactor A h * rFactor A h := hqr
      _ = _ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (signs _) (signs _), signs_self,
          Matrix.one_mul]
  · rw [conjTranspose_mul, signs_conjTranspose]
    calc
      _ = signs (rFactor A h) * ((qFactor A h).conjTranspose * qFactor A h) *
          signs (rFactor A h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hq, Matrix.mul_one, signs_self]
  · intro i j hij
    simp only [signs, diagonal_mul]
    rw [ht i j hij, mul_zero]
  · intro i
    refine ⟨signPlus (rFactor A h i i) * rFactor A h i i,
      signPlus_mul_pos _ (hd i), ?_⟩
    simp [positiveR, signs, diagonal_mul]

abbrev split : Specs.NumAnalysis206.HouseholderExactQR.split_type :=
  @NumAnalysis206.HouseholderQRDefinitions.split

abbrev blockLift : Specs.NumAnalysis206.HouseholderExactQR.blockLift_type :=
  @NumAnalysis206.HouseholderQRDefinitions.blockLift

abbrev tail : Specs.NumAnalysis206.HouseholderExactQR.tail_type :=
  @NumAnalysis206.HouseholderQRDefinitions.tail

abbrev update : Specs.NumAnalysis206.HouseholderExactQR.update_type :=
  @NumAnalysis206.HouseholderQRDefinitions.update

abbrev run : Specs.NumAnalysis206.HouseholderExactQR.run_type :=
  @NumAnalysis206.HouseholderQRDefinitions.run

abbrev product : Specs.NumAnalysis206.HouseholderExactQR.product_type :=
  @NumAnalysis206.HouseholderQRDefinitions.product

abbrev Cleared : Specs.NumAnalysis206.HouseholderExactQR.Cleared_type :=
  @NumAnalysis206.HouseholderQRDefinitions.Cleared

abbrev rFactor : Specs.NumAnalysis206.HouseholderExactQR.rFactor_type :=
  @NumAnalysis206.HouseholderQRDefinitions.rFactor

abbrev qFactor : Specs.NumAnalysis206.HouseholderExactQR.qFactor_type :=
  @NumAnalysis206.HouseholderQRDefinitions.qFactor

abbrev signs : Specs.NumAnalysis206.HouseholderExactQR.signs_type :=
  @NumAnalysis206.HouseholderQRDefinitions.signs

abbrev positiveQ : Specs.NumAnalysis206.HouseholderExactQR.positiveQ_type :=
  @NumAnalysis206.HouseholderQRDefinitions.positiveQ

abbrev positiveR : Specs.NumAnalysis206.HouseholderExactQR.positiveR_type :=
  @NumAnalysis206.HouseholderQRDefinitions.positiveR

end NumAnalysis206.HouseholderExactQR
