import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.MatrixIndex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.ScalarIndex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.MatrixLoopHomotopy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.MeasurableSymbolCounterexample

/-! Matrix Toeplitz Fredholmness and the determinant winding formula from
`fa2:p2:matrix-toeplitz` (paper.tex:10466–10526). The operators are the canonical
finite Hilbert sums; the index is computed by their actual kernel and cokernel. -/

noncomputable section
open MeasureTheory
open scoped Real ENNReal Topology
set_option maxHeartbeats 800000
namespace ExpandedFA.Toeplitz.MatrixIndex
open ExpandedFA.Toeplitz.Definitions
open ExpandedFA.Toeplitz.HankelCompactness
open ExpandedFA.Toeplitz.MatrixLoops
open ExpandedFA.Fredholm
open Spec (entries operator)

@[simp] theorem entries_mul (n : ℕ) (Φ Ψ : C(_root_.Circle, MatrixGroup n)) :
    entries n (Φ * Ψ) = entries n Φ * entries n Ψ := by
  ext i j t
  simp [entries, Matrix.mul_apply]

@[simp] theorem entries_one (n : ℕ) :
    entries n (1 : C(_root_.Circle, MatrixGroup n)) = 1 := by
  ext i j t
  classical
  simp only [entries, ContinuousMap.coe_mk, ContinuousMap.one_apply, Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

@[simp] theorem toeplitz_zero : toeplitz (continuousSymbol (0 : C(Definitions.Spec.Circle, ℂ))) = 0 :=
  ScalarIndex.toeplitzSymbolMap.map_zero

@[simp] theorem matrix_toeplitz_one (d : ℕ) :
    matrixToeplitz (continuousMatrixSymbol (1 : Matrix (Fin d) (Fin d)
      C(Definitions.Spec.Circle, ℂ))) = ContinuousLinearMap.id ℂ (VectorH2 d) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [Definitions.Spec.matrixToeplitz, operatorMatrix_apply,
    Definitions.Spec.continuousMatrixSymbol, ContinuousLinearMap.id_apply]
  change (∑ j : Fin d, toeplitz (continuousSymbol
    ((1 : Matrix (Fin d) (Fin d) C(Definitions.Spec.Circle, ℂ)) i j)) (f j)) = f i
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp [ScalarIndex.toeplitz_one]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The actual inverse-symbol compression is a two-sided compact parametrix. -/
theorem fredholm_operator (n : ℕ) (Φ : C(_root_.Circle, MatrixGroup n)) :
    IsFredholm (operator n Φ) := by
  let Ψ : C(_root_.Circle, MatrixGroup n) := ⟨fun z => (Φ z)⁻¹, Φ.continuous.inv⟩
  have hleft : entries n Ψ * entries n Φ = 1 := by
    rw [← entries_mul]
    have h : Ψ * Φ = 1 := by
      apply ContinuousMap.ext
      intro z
      exact inv_mul_cancel (Φ z)
    rw [h, entries_one]
  have hright : entries n Φ * entries n Ψ = 1 := by
    rw [← entries_mul]
    have h : Φ * Ψ = 1 := by
      apply ContinuousMap.ext
      intro z
      exact mul_inv_cancel (Φ z)
    rw [h, entries_one]
  unfold operator
  apply isFredholm_of_compact_parametrix _ (operator n Ψ)
  · apply (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
    convert! (matrix_product_defect_compact (n+1) (entries n Ψ) (entries n Φ)) using 1
    simp only [operator, hleft, matrix_toeplitz_one]
    rfl
  · apply (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
    convert! (matrix_product_defect_compact (n+1) (entries n Φ) (entries n Ψ)) using 1
    simp only [operator, hright, matrix_toeplitz_one]
    rfl

/-- The scalar operator in the first summand, and the identity on the others. -/
def diagonalOperator (n : ℕ) (A : H2 →L[ℂ] H2) : VectorH2 (n+1) →L[ℂ] VectorH2 (n+1) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n+1) => H2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => if i = 0 then
      A.comp (PiLp.proj (p := 2) (fun _ : Fin (n+1) => H2) i)
      else PiLp.proj (p := 2) (fun _ : Fin (n+1) => H2) i)

@[simp] theorem diagonalOperator_apply (n : ℕ) (A : H2 →L[ℂ] H2)
    (f : VectorH2 (n+1)) (i : Fin (n+1)) :
    diagonalOperator n A f i = if i = 0 then A (f i) else f i := by
  classical
  simp only [diagonalOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- The diagonal block has exactly the scalar kernel. -/
def diagonalKernelMap (n : ℕ) (A : H2 →L[ℂ] H2) :
    (diagonalOperator n A).ker →ₗ[ℂ] A.ker where
  toFun f := ⟨f.val 0, by
    have h := congrArg (fun g : VectorH2 (n+1) => g 0) f.property
    change diagonalOperator n A f.val 0 = 0 at h
    change A (f.val 0) = 0
    simpa only [diagonalOperator_apply, ite_true] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem diagonalKernelMap_bijective (n : ℕ) (A : H2 →L[ℂ] H2) :
    Function.Bijective (diagonalKernelMap n A) := by
  classical
  constructor
  · intro f g h
    apply Subtype.ext
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      exact congrArg Subtype.val h
    · have hf := congrArg (fun v : VectorH2 (n+1) => v i) f.property
      have hg := congrArg (fun v : VectorH2 (n+1) => v i) g.property
      change diagonalOperator n A f.val i = 0 at hf
      change diagonalOperator n A g.val i = 0 at hg
      simpa only [diagonalOperator_apply, ite_eq_right hi] using hf.trans hg.symm
  · intro f
    refine ⟨⟨PiLp.single 2 0 f.val, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      apply PiLp.ext
      intro i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [hi]
    · apply Subtype.ext
      change (PiLp.single 2 0 f.val : VectorH2 (n+1)) 0 = f.val
      simp

/-- Membership in the actual range is tested solely on the first coordinate. -/
theorem mem_diagonal_range (n : ℕ) (A : H2 →L[ℂ] H2) (f : VectorH2 (n+1)) :
    f ∈ (diagonalOperator n A).range ↔ f 0 ∈ A.range := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g 0, by simp⟩
  · rintro ⟨g, hg⟩
    let v : VectorH2 (n+1) := WithLp.toLp 2 (fun i => if i = 0 then g else f i)
    refine ⟨v, ?_⟩
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simpa [v] using hg
    · simp [v, hi]

/-- The actual cokernel is the scalar cokernel, rather than a formal index. -/
def diagonalCokernelEquiv (n : ℕ) (A : H2 →L[ℂ] H2) :
    (VectorH2 (n+1) ⧸ (diagonalOperator n A).range) ≃ₗ[ℂ] (H2 ⧸ A.range) := by
  classical
  let q : VectorH2 (n+1) →ₗ[ℂ] (H2 ⧸ A.range) :=
    A.range.mkQ.comp (PiLp.proj (p := 2) (fun _ : Fin (n+1) => H2) 0).toLinearMap
  have hk : q.ker = (diagonalOperator n A).range := by
    ext f
    change A.range.mkQ (f 0) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_diagonal_range]
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨f, rfl⟩ := A.range.mkQ_surjective y
    exact ⟨PiLp.single 2 0 f, by simp [q]⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)

theorem diagonal_index (n : ℕ) (A : H2 →L[ℂ] H2)
    (hD : IsFredholm (diagonalOperator n A)) (hA : IsFredholm A) :
    fredholmIndex (diagonalOperator n A) hD = fredholmIndex A hA := by
  have hk := (LinearEquiv.ofBijective (diagonalKernelMap n A)
    (diagonalKernelMap_bijective n A)).finrank_eq
  have hc := (diagonalCokernelEquiv n A).finrank_eq
  change (Module.finrank ℂ _ : ℤ) - Module.finrank ℂ _ =
    (Module.finrank ℂ _ : ℤ) - Module.finrank ℂ _
  rw [hk, hc]

/-- The compact-open matrix homotopy induces an operator-norm continuous path. -/
theorem operator_homotopy_continuous (n : ℕ)
    {Φ Ψ : C(_root_.Circle, MatrixGroup n)} (H : Φ.Homotopy Ψ) :
    Continuous (fun s : unitInterval => operator n (H.curry s)) := by
  have he (i j : Fin (n+1)) :
      Continuous (fun s : unitInterval => entries n (H.curry s) i j) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : unitInterval × Definitions.Spec.Circle =>
      (H (p.1, AddCircle.homeomorphCircle' p.2)).val i j)
    exact (Units.continuous_val.comp (H.continuous.comp
      (continuous_fst.prodMk (AddCircle.homeomorphCircle'.continuous.comp continuous_snd)))).matrix_elem i j
  change Continuous (fun s : unitInterval => Definitions.Spec.operatorMatrix (n+1)
    (fun i j => ScalarIndex.toeplitzSymbolMap (entries n (H.curry s) i j)))
  simp only [operatorMatrix_decomposition]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.clm_comp ((ScalarIndex.toeplitzSymbolMap.continuous.comp
    (he i j)).clm_comp continuous_const)

/-- Local constancy of the native index on a path of invertible matrix symbols. -/
theorem homotopy_index (n : ℕ) {Φ Ψ : C(_root_.Circle, MatrixGroup n)}
    (h : Φ.Homotopic Ψ) (hΦ : IsFredholm (operator n Φ))
    (hΨ : IsFredholm (operator n Ψ)) :
    fredholmIndex (operator n Φ) hΦ = fredholmIndex (operator n Ψ) hΨ := by
  obtain ⟨H⟩ := h
  have hp := operator_homotopy_continuous n H
  have hi : Continuous (fun s : unitInterval => (operator n (H.curry s)).toLinearMap.index) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (fredholm_operator n (H.curry s)).to_native.index_continuousAt.comp
      (f := fun t : unitInterval => operator n (H.curry t))
      (x := s) hp.continuousAt
  have hc := isPreconnected_univ.constant hi.continuousOn (Set.mem_univ 0) (Set.mem_univ 1)
  change (operator n Φ).toLinearMap.index = (operator n Ψ).toLinearMap.index
  simpa only [ContinuousMap.Homotopy.curry_zero, ContinuousMap.Homotopy.curry_one] using hc

/-- The power loop agrees with the canonical positively oriented Fourier mode. -/
theorem powerLoop_pullback (k : ℤ) (t : Definitions.Spec.Circle) :
    ((powerLoop k (AddCircle.homeomorphCircle' t) : ℂˣ) : ℂ) =
      fourier (T := 2 * π) k t := by
  have he : AddCircle.homeomorphCircle' t = AddCircle.toCircle t := by
    induction t using QuotientAddGroup.induction_on
    simp [AddCircle.homeomorphCircle'_apply_mk, AddCircle.toCircle_apply_mk]
  change ((AddCircle.homeomorphCircle' t ^ k : _root_.Circle) : ℂ) = _
  rw [he, ← AddCircle.toCircle_zsmul]
  rfl

/-- Compression of the normal form is precisely a scalar Fourier block plus identities. -/
theorem normalForm_operator (n : ℕ) (k : ℤ) :
    operator n (normalForm n k) = diagonalOperator n
      (toeplitz (continuousSymbol (fourier (T := 2 * π) k))) := by
  classical
  have he (i j : Fin (n+1)) : entries n (normalForm n k) i j =
      if i = j then (if i = 0 then fourier (T := 2 * π) k else 1) else 0 := by
    ext t
    simp only [entries, ContinuousMap.coe_mk, normalForm, ContinuousMap.comp_apply,
      diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp_all [powerLoop_pullback]
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [operator, Definitions.Spec.matrixToeplitz, operatorMatrix_apply,
    Definitions.Spec.continuousMatrixSymbol]
  change (∑ j : Fin (n+1), toeplitz (continuousSymbol
    (entries n (normalForm n k) i j)) (f j)) = _
  simp only [he]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, diagonalOperator_apply]
    split_ifs <;> simp_all [ScalarIndex.toeplitz_one]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The only nonidentity block of the normal form has index minus its exponent. -/
theorem normalForm_index (n : ℕ) (k : ℤ)
    (h : IsFredholm (operator n (normalForm n k))) :
    fredholmIndex (operator n (normalForm n k)) h = -k := by
  have hs := ScalarIndex.fourier_symbol_fredholm k
  have hi : fredholmIndex
      (toeplitz (continuousSymbol (fourier (T := 2 * π) k))) hs = -k := by
    cases k with
    | ofNat m => exact (ScalarIndex.positive_shift m).choose_spec.2.2
    | negSucc m =>
      obtain ⟨hm, _, _, hi⟩ := ScalarIndex.negative_shift (m+1)
      change (Module.finrank ℂ _ : ℤ) - Module.finrank ℂ _ = _ at hi ⊢
      convert! hi using 1
  have hD : IsFredholm (diagonalOperator n
      (toeplitz (continuousSymbol (fourier (T := 2 * π) k)))) := by
    rw [← normalForm_operator]; exact h
  have hd := (diagonal_index n _ hD hs).trans hi
  have he := congrArg (fun A : VectorH2 (n+1) →L[ℂ] VectorH2 (n+1) =>
    A.toLinearMap.index) (normalForm_operator n k)
  exact he.trans hd

/-- Matrix Toeplitz Fredholmness and the determinant winding formula. -/
theorem matrix_index : Spec.MatrixIndex := by
  intro n Φ
  have hf := fredholm_operator n Φ
  let k := MatrixLoops.winding ((determinant n).comp Φ)
  have hn := fredholm_operator n (normalForm n k)
  exact ⟨hf, (homotopy_index n (classification n Φ) hf hn).trans
    (normalForm_index n k hn)⟩

/-- The previously established concrete scalar counterexample. -/
theorem discontinuous_counterexample : Spec.DiscontinuousCounterexample :=
  MeasurableSymbolCounterexample.counterexample

end ExpandedFA.Toeplitz.MatrixIndex
