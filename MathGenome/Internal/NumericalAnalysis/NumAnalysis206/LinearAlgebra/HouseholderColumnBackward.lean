import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderColumnBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderExactQR
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderPivotStep
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderTrailingStep
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.OrthogonalErrorAccumulation

noncomputable section
open scoped BigOperators
open Matrix
namespace NumAnalysis206.HouseholderColumnBackward
open MatrixDefinitions HouseholderDefinitions
open HouseholderQRDefinitions (split blockLift Cleared)
open HouseholderColumnDefinitions

lemma splice_inl {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (z : Fin n → Vec ℝ (m-j.val)) (i : Fin j.val) (c : Fin n) :
    splice B h j z (split m j.val (by omega) (Sum.inl i)) c =
      B (split m j.val (by omega) (Sum.inl i)) c := by
  simp only [splice, submatrix_apply, Equiv.symm_apply_apply]
  rfl

lemma splice_inr {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (z : Fin n → Vec ℝ (m-j.val)) (i : Fin (m-j.val)) (c : Fin n) :
    splice B h j z (split m j.val (by omega) (Sum.inr i)) c = z c i := by
  simp only [splice, submatrix_apply, Equiv.symm_apply_apply]
  rfl

lemma splice_original {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (c : Fin n) (i : Fin m) :
    splice B h j (columnTail B h j) i c = B i c := by
  obtain ⟨a,rfl⟩ := (split m j.val (by omega)).surjective i
  cases a with
  | inl a => rw [splice_inl]
  | inr a => rw [splice_inr]; rfl

/-- The full column's squared norm splits into its prefix and active tail. -/
lemma norm_column_split {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n) :
    ‖columns B c‖ ^ 2 =
      (∑ i : Fin j.val, (B (split m j.val (by omega) (Sum.inl i)) c)^2) +
      ‖columnTail B h j c‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  rw [← (split m j.val (by omega)).sum_comp]
  rw [Fintype.sum_sum_type]
  rfl

lemma norm_tail_le {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n) :
    ‖columnTail B h j c‖ ≤ ‖columns B c‖ := by
  have hs := norm_column_split B h j c
  have hp : 0 ≤ ∑ i : Fin j.val, (B (split m j.val (by omega) (Sum.inl i)) c)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (columns B c), norm_nonneg (columnTail B h j c)]

lemma norm_zero_prefix {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n)
    (hz : ∀ i : Fin j.val, B (split m j.val (by omega) (Sum.inl i)) c = 0) :
    ‖columns B c‖ = ‖columnTail B h j c‖ := by
  have hs := norm_column_split B h j c
  simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, zero_add] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

lemma columnTail_lift {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n)
    (T : Mat ℝ (m-j.val) (m-j.val)) :
    columnTail (blockLift (by omega) T * B) h j c = T.toEuclideanLin (columnTail B h j c) := by
  ext i
  exact HouseholderExactQR.blockLift_mul_inr _ T B i c

lemma storedStep_preserves {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n)
    (h : n ≤ m) (j c : Fin n) (hc : c.val < j.val) (i : Fin m) :
    storedStep modes round B h j i c = B i c := by
  classical
  by_cases hx : columnTail B h j j = 0
  · simp [storedStep, hx]
  · simp only [storedStep, ite_eq_right hx]
    obtain ⟨a,rfl⟩ := (split m j.val (by omega)).surjective i
    cases a with
    | inl a => rw [splice_inl]
    | inr a => rw [splice_inr]; simp [newTail, hc, columnTail]

lemma storedStep_clears {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n)
    (h : n ≤ m) (j : Fin n) (i : Fin m) (hi : j.val < i.val) :
    storedStep modes round B h j i j = 0 := by
  classical
  let a : Fin (m-j.val) := ⟨i.val-j.val, by omega⟩
  have he : split m j.val (by omega) (Sum.inr a) = i := by
    apply Fin.ext
    rw [HouseholderExactQR.split_inr]
    dsimp [a]
    omega
  have : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  have ha : a ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    dsimp [a] at this
    omega
  by_cases hx : columnTail B h j j = 0
  · simp only [storedStep, ite_eq_left hx]
    have hz := congrArg (fun v : Vec ℝ (m-j.val) => v a) hx
    simpa only [columnTail, PiLp.toLp_apply, PiLp.zero_apply, he] using hz
  · rw [storedStep, ite_eq_right hx, ← he, splice_inr]
    simp [newTail, HouseholderReflector.firstVector_apply, ha]

lemma storedStep_cleared {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (B : Mat ℝ m n)
    (h : n ≤ m) (j : Fin n) (hc : Cleared B j.val) :
    Cleared (storedStep modes round B h j) (j.val+1) := by
  intro c hck i hci
  by_cases hcj : c.val < j.val
  · rw [storedStep_preserves modes round B h j c hcj i]
    exact hc c hcj i hci
  · have he : c = j := Fin.ext (by omega)
    subst c
    exact storedStep_clears modes round B h j i hci

lemma columnTail_sub {m n : ℕ} (B C : Mat ℝ m n) (h : n ≤ m) (j c : Fin n) :
    columnTail (B-C) h j c = columnTail B h j c - columnTail C h j c := rfl

lemma columnTail_splice {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n)
    (z : Fin n → Vec ℝ (m-j.val)) : columnTail (splice B h j z) h j c = z c := by
  ext i
  exact splice_inr B h j z i c

lemma tail_zero_of_cleared {m n : ℕ} (B : Mat ℝ m n) (h : n ≤ m) (j c : Fin n)
    (hc : Cleared B j.val) (hcj : c.val < j.val) : columnTail B h j c = 0 := by
  ext i
  apply hc c hcj
  rw [HouseholderExactQR.split_inr]
  omega

/-- Lift the two local error bounds to complete columns in the original row
order. Earlier cleared columns have identically zero local error. -/
lemma one_step {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n)
    (hm : Rounding.Specs.RelativeModelValue round u D)
    (hs : SafeStep modes round u D B h j) (hc : Cleared B j.val) :
    (exactUpdate modes round B h j).conjTranspose * exactUpdate modes round B h j = 1 ∧
    0 ≤ stepConstant u B h j ∧
    ∀ c, ‖columns (storedStep modes round B h j - exactUpdate modes round B h j * B) c‖ ≤
      stepConstant u B h j * ‖columns B c‖ := by
  classical
  by_cases hx : columnTail B h j j = 0
  · simp [exactUpdate, stepConstant, storedStep, hx]
    intro c
    rfl
  have : NeZero (m-j.val) := ⟨by have := j.isLt; omega⟩
  obtain ⟨hdu,hg,hps,hts⟩ := hs hx
  have hp := HouseholderPivotStep.pivot_step modes.pivot round (columnTail B h j j) u D
    hx hm hdu hg hps
  obtain ⟨hnu,hnerr,hw,hdir,hort,hpert,hpivot⟩ := hp
  have hxn : 0 < ‖columnTail B h j j‖ := norm_pos_iff.mpr hx
  have ha : 0 ≤ HouseholderPivotDefinitions.normError (m-j.val) u := by
    have := abs_nonneg (HouseholderPivotDefinitions.computedNorm modes.pivot round
      (columnTail B h j j) - ‖columnTail B h j j‖)
    nlinarith
  have hb : 0 ≤ HouseholderPivotDefinitions.directionError (m-j.val) u := by
    unfold HouseholderPivotDefinitions.directionError
    exact add_nonneg ha (mul_nonneg hm.1 (by linarith))
  have hC : 0 ≤ stepConstant u B h j := by
    simp only [stepConstant, ite_eq_right hx]
    exact le_trans (by positivity) (le_max_left _ _)
  refine ⟨?_, hC, ?_⟩
  · simp only [exactUpdate, ite_eq_right hx]
    exact HouseholderExactQR.blockLift_orthogonal _ _ hort
  · intro c
    have hn : ‖columns (storedStep modes round B h j - exactUpdate modes round B h j * B) c‖ =
        ‖columnTail (storedStep modes round B h j - exactUpdate modes round B h j * B) h j c‖ := by
      apply norm_zero_prefix
      intro i
      change storedStep modes round B h j (split m j.val (by omega) (Sum.inl i)) c -
        (exactUpdate modes round B h j * B) (split m j.val (by omega) (Sum.inl i)) c = 0
      simp only [storedStep, exactUpdate, ite_eq_right hx, splice_inl,
        HouseholderExactQR.blockLift_mul_inl, sub_self]
    rw [hn]
    have ht : columnTail (storedStep modes round B h j - exactUpdate modes round B h j * B) h j c =
        newTail modes round B h j c -
          (reflector (roundedW modes round B h j)).toEuclideanLin (columnTail B h j c) := by
      rw [columnTail_sub]
      simp only [storedStep, exactUpdate, ite_eq_right hx, columnTail_splice, columnTail_lift]
    rw [ht]
    have hl : ‖newTail modes round B h j c -
        (reflector (roundedW modes round B h j)).toEuclideanLin (columnTail B h j c)‖ ≤
        stepConstant u B h j * ‖columnTail B h j c‖ := by
      by_cases hcj : c.val < j.val
      · have hz := tail_zero_of_cleared B h j c hc hcj
        simp [newTail, hcj, hz]
      · by_cases he : c = j
        · subst c
          simp only [newTail, lt_self_iff_false, ↓reduceIte]
          exact hpivot.trans (mul_le_mul_of_nonneg_right
            (by simp only [stepConstant, ite_eq_right hx]; exact le_max_left _ _)
            (norm_nonneg _))
        · have hjc : j.val < c.val := by
            have hv : c.val ≠ j.val := fun hv => he (Fin.ext hv)
            omega
          have herr := (HouseholderTrailingStep.trailing_step modes.numerator modes.denominator round u D
            (roundedW modes round B h j) (columnTail B h j c) hw hm hdu hg (hts c hjc)).2
          simp only [newTail, ite_eq_right hcj, ite_eq_right he]
          exact herr.trans (mul_le_mul_of_nonneg_right
            (by simp only [stepConstant, ite_eq_right hx]; exact le_max_right _ _)
            (norm_nonneg _))
    exact hl.trans (mul_le_mul_of_nonneg_left (norm_tail_le B h j c) hC)

lemma run_cleared {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m)
    (k : ℕ) (hk : k ≤ n) : Cleared (run modes round A h k) k := by
  induction k with
  | zero => simp [Cleared]
  | succ k ih =>
    have hkn : k < n := by omega
    simp only [run, dite_eq_left hkn]
    exact storedStep_cleared modes round _ h ⟨k,hkn⟩ (ih (by omega))

lemma run_preserves {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ) (A : Mat ℝ m n) (h : n ≤ m)
    (j c : Fin n) (hc : c.val < j.val) (i : Fin m) :
    run modes round A h (j.val+1) i c = run modes round A h j.val i c := by
  rw [run, dite_eq_left j.isLt]
  exact storedStep_preserves modes round _ h j c hc i

lemma reflector_selfadjoint {d : ℕ} (w : Vec ℝ d) :
    (reflector w).conjTranspose = reflector w := by
  simp [reflector]

lemma blockLift_adjoint {m k : ℕ} (h : k ≤ m) (T : Mat ℝ (m-k) (m-k)) :
    (blockLift h T).conjTranspose = blockLift h T.conjTranspose := by
  unfold blockLift
  rw [conjTranspose_submatrix, fromBlocks_conjTranspose]
  simp only [conjTranspose_one, conjTranspose_zero]

lemma update_selfadjoint {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ)
    (B : Mat ℝ m n) (h : n ≤ m) (j : Fin n) :
    (exactUpdate modes round B h j).conjTranspose = exactUpdate modes round B h j := by
  classical
  unfold exactUpdate
  split_ifs
  · exact conjTranspose_one
  · rw [blockLift_adjoint, reflector_selfadjoint]

/-- The pullback used for the backward error is exactly the product of the
stored-direction reflectors, taken in inverse application order. -/
lemma implicitProduct_eq_adjoint {m n : ℕ} (modes : DotModes) (round : ℝ → ℝ)
    (A : Mat ℝ m n) (h : n ≤ m) (k : ℕ) :
    implicitProduct modes round A h k =
      (OrthogonalErrorDefinitions.forwardProduct (updates modes round A h) k).conjTranspose := by
  induction k with
  | zero => simp [implicitProduct, OrthogonalErrorDefinitions.forwardProduct]
  | succ k ih =>
    rw [implicitProduct, OrthogonalErrorDefinitions.forwardProduct, conjTranspose_mul, ih]
    congr 1
    unfold updates
    split_ifs
    · exact (update_selfadjoint modes round _ h _).symm
    · exact conjTranspose_one.symm

/-- Assemble the actual stored steps, rather than assuming a local-error
certificate for an unspecified QR algorithm. -/
theorem column_backward : Specs.NumAnalysis206.HouseholderColumnBackward.column_backward := by
  intro m n modes round u D A h hm hs
  let B := run modes round A h
  let H := updates modes round A h
  let c := constants modes round u A h
  let F : ℕ → Mat ℝ m n := fun k => B (k+1) - H k * B k
  have hlocal (k : ℕ) (hk : k < n) :
      (H k).conjTranspose * H k = 1 ∧ 0 ≤ c k ∧
      ∀ i, ‖columns (F k) i‖ ≤ c k * ‖columns (B k) i‖ := by
    have hh := one_step modes round u D (B k) h ⟨k,hk⟩ hm (hs ⟨k,hk⟩)
      (run_cleared modes round A h k (by omega))
    simpa only [H, c, F, B, updates, constants, run, dite_eq_left hk] using hh
  have hacc := OrthogonalErrorAccumulation.columnwise_accumulation n A H B F c
    (by rfl) (fun k hk => (hlocal k hk).1) (fun k hk => (hlocal k hk).2.1)
    (fun k hk => by dsimp [F]; abel) (fun k hk => (hlocal k hk).2.2)
  obtain ⟨hgrowth, ⟨hP,hP'⟩, herr, hempty⟩ := hacc
  have hclear : Cleared (B n) n := run_cleared modes round A h n le_rfl
  let P := OrthogonalErrorDefinitions.forwardProduct H n
  have hrep : B n = P * (P.conjTranspose * B n) := by
    rw [← Matrix.mul_assoc, hP', Matrix.one_mul]
  obtain ⟨hqr,hq⟩ := HouseholderExactQR.reduced_factorization
    (P.conjTranspose * B n) h P (B n) hrep hP hclear
  have hinv := implicitProduct_eq_adjoint modes round A h n
  have hqdef : qFactor modes round A h =
      P.conjTranspose.submatrix id (Fin.castLE h) := by
    unfold qFactor
    rw [hinv]
  refine ⟨run_cleared modes round A h, run_preserves modes round A h, hinv, hP, ?_, ?_,
    ?_, ?_, herr, hempty⟩
  · change A + (P.conjTranspose * B n - A) = _
    calc
      _ = P.conjTranspose * B n := by abel
      _ = _ := by rw [hqdef]; exact hqr
  · rw [hqdef]
    exact hq
  · intro i j hji
    exact hclear j j.isLt (Fin.castLE h i) hji
  · intro i hi j
    exact hclear j j.isLt i (by omega)

end NumAnalysis206.HouseholderColumnBackward
