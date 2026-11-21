import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries

/-!
The cofactor recurrence is obtained by isolating individual first-row entries.
Conjugating by a permutation that fixes the first row leaves each determinant
unchanged and makes all integrated tail contributions equal. After normalizing
by (-z)^n/n!, bounded linear functionals pass the absolutely convergent kernel
series through its integrals. Plain transposition yields the right identity.
Fubini and the same coefficient series prove the diagonal derivative formula;
the two operator identities then give the inverse by direct multiplication.
-/

open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities

open ClassicalDefinitions.Spec ClassicalEntireSeries.Spec.Data

noncomputable def resolventOperator : Spec.ResolventOperatorType.{u} :=
  @Spec.ResolventOperatorValue

theorem resolvent_formula : Spec.ResolventFormula.{u} := by
  intro Q _ _ _ _ μ _ k z f x
  change f x + (z / FredholmDeterminantValue μ k z) *
    (KernelOperatorValue μ (minorKernel μ k z) f) x = _
  rw [(ClassicalDefinitions.data_identification μ (minorKernel μ k z)).1]
  simp_rw [ClassicalEntireSeries.minor_kernel_identification μ k z]

/-- One term in the multilinear decomposition of the first row. -/
def firstRowPiece {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  A.updateRow 0 (fun l => if l = j then A 0 l else 0)

lemma det_firstRowPiece {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (j : Fin (n + 1)) :
    (firstRowPiece A j).det = (-1 : ℂ) ^ (j : ℕ) * A 0 j *
      (A.submatrix Fin.succ j.succAbove).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single j]
  · simp only [firstRowPiece, Matrix.updateRow_apply]
    congr 2
  · intro l _ hlj
    simp [firstRowPiece, Matrix.updateRow_apply, hlj]
  · simp

lemma det_eq_sum_firstRowPiece {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    A.det = ∑ j, (firstRowPiece A j).det := by
  rw [Matrix.det_succ_row_zero]
  exact Finset.sum_congr rfl fun j _ => (det_firstRowPiece A j).symm

lemma firstRowPiece_submatrix {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Equiv.Perm (Fin (n + 1))) (he : e 0 = 0) (j : Fin (n + 1)) :
    firstRowPiece (A.submatrix e e) j = (firstRowPiece A (e j)).submatrix e e := by
  ext i l
  have hei : e i = 0 ↔ i = 0 := by
    constructor
    · intro h
      exact e.injective (h.trans he.symm)
    · intro h
      simpa only [h] using he
  simp [firstRowPiece, Matrix.updateRow_apply, Matrix.submatrix_apply,
    hei, e.injective.eq_iff, he]

section
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q]
  [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ))

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
lemma augmentedMatrix_permute (n : ℕ) (x y : Q) (t : Fin n → Q)
    (σ : Equiv.Perm (Fin n)) :
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, σ)
    AugmentedMatrixValue k n x y (fun i => t (σ i)) =
      (AugmentedMatrixValue k n x y t).submatrix e e := by
  dsimp
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [AugmentedMatrixValue]

lemma integral_permute_nodes (n : ℕ) (σ : Equiv.Perm (Fin n)) (F : (Fin n → Q) → ℂ) :
    (∫ t, F (fun i => t (σ i)) ∂MeasurePowerValue μ n) =
      ∫ t, F t ∂MeasurePowerValue μ n := by
  have he := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ.symm).integral_comp' F
  simpa [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft'_symm, Equiv.piCongrLeft', MeasurePowerValue] using he

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
lemma continuous_firstRowPiece (n : ℕ) (x y : Q) (j : Fin (n + 1)) :
    Continuous (fun t : Fin n → Q => (firstRowPiece (AugmentedMatrixValue k n x y t) j).det) := by
  have hx : Continuous (fun t : Fin n → Q => Fin.cons (α := fun _ => Q) x t) :=
    continuous_const.finCons continuous_id
  have hy : Continuous (fun t : Fin n → Q => Fin.cons (α := fun _ => Q) y t) :=
    continuous_const.finCons continuous_id
  have hentry (i l : Fin (n + 1)) :
      Continuous (fun t => AugmentedMatrixValue k n x y t i l) :=
    k.continuous.comp (((continuous_apply i).comp hx).prodMk ((continuous_apply l).comp hy))
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro l
  by_cases hi : i = 0
  · by_cases hl : l = j
    · simpa [firstRowPiece, Matrix.updateRow_apply, hi, hl] using hentry 0 l
    · simpa [firstRowPiece, Matrix.updateRow_apply, hi, hl] using
        (continuous_const : Continuous (fun _ : Fin n → Q => (0 : ℂ)))
  · simpa [firstRowPiece, Matrix.updateRow_apply, hi] using hentry i l

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
lemma det_firstRowPiece_zero (n : ℕ) (x y : Q) (t : Fin n → Q) :
    (firstRowPiece (AugmentedMatrixValue k n x y t) 0).det =
      k (x, y) * (KernelMatrixValue k n t).det := by
  rw [det_firstRowPiece]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
lemma det_firstRowPiece_one (n : ℕ) (x y : Q) (t : Fin (n + 1) → Q) :
    (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) (Fin.succ 0)).det =
      -k (x, t 0) *
        (AugmentedMatrixValue k n (t 0) y (fun i => t i.succ)).det := by
  rw [det_firstRowPiece]
  simp only [Fin.val_succ, Fin.val_zero, zero_add, pow_one]
  have he : (AugmentedMatrixValue k (n + 1) x y t).submatrix Fin.succ
      (Fin.succ 0).succAbove = AugmentedMatrixValue k n (t 0) y (fun i => t i.succ) := by
    ext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [AugmentedMatrixValue, Fin.one_succAbove_succ]
  rw [he]
  simp [AugmentedMatrixValue]

lemma integral_nodes_succ (n : ℕ) (F : (Fin (n + 1) → Q) → ℂ) (hF : Continuous F) :
    (∫ t, F t ∂MeasurePowerValue μ (n + 1)) =
      ∫ x, ∫ t, F (Fin.cons (α := fun _ => Q) x t) ∂MeasurePowerValue μ n ∂μ := by
  let : IsFiniteMeasure (MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hi : Integrable (fun p : Q × (Fin n → Q) => F (Fin.cons p.1 p.2))
      (μ.prod (MeasurePowerValue μ n)) :=
    (hF.comp (continuous_fst.finCons continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq] at he
  change (∫ t, F t ∂Measure.pi (fun _ => μ)) = _
  rw [← he]
  exact integral_prod _ hi

lemma integral_firstRowPiece_one (n : ℕ) (x y : Q) :
    (∫ t : Fin (n + 1) → Q,
      (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) (Fin.succ 0)).det
      ∂MeasurePowerValue μ (n + 1)) =
      -(∫ t, k (x, t) * MinorIntegralValue μ k n t y ∂μ) := by
  rw [integral_nodes_succ μ _ _ (continuous_firstRowPiece k _ x y _)]
  simp_rw [det_firstRowPiece_one, Fin.cons_zero, Fin.cons_succ, neg_mul,
    integral_neg, integral_const_mul]
  rfl

lemma integral_firstRowPiece_eq (n : ℕ) (x y : Q) (j : Fin (n + 1)) :
    (∫ t : Fin (n + 1) → Q,
      (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) j.succ).det
      ∂MeasurePowerValue μ (n + 1)) =
    ∫ t : Fin (n + 1) → Q,
      (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) (Fin.succ 0)).det
      ∂MeasurePowerValue μ (n + 1) := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j
  let e : Equiv.Perm (Fin (n + 1 + 1)) := Equiv.Perm.decomposeFin.symm (0, σ)
  have he : e 0 = 0 := by simp [e]
  have hej : e (Fin.succ 0) = j.succ := by simp [e, σ]
  have hp (t : Fin (n + 1) → Q) :
      (firstRowPiece (AugmentedMatrixValue k (n + 1) x y (fun i => t (σ i)))
        (Fin.succ 0)).det =
      (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) j.succ).det := by
    rw [augmentedMatrix_permute, firstRowPiece_submatrix _ e he, hej,
      Matrix.det_submatrix_equiv_self]
  rw [← integral_permute_nodes μ (n + 1) σ
    (fun t => (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) (Fin.succ 0)).det)]
  simp_rw [hp]

/-- The unnormalized cofactor recurrence, before multiplying by (-z)^n/n!. -/
lemma minorIntegral_succ (n : ℕ) (x y : Q) :
    MinorIntegralValue μ k (n + 1) x y =
      k (x, y) * DeterminantIntegralValue μ k (n + 1) -
        (n + 1 : ℂ) * ∫ t, k (x, t) * MinorIntegralValue μ k n t y ∂μ := by
  let : IsFiniteMeasure (MeasurePowerValue μ (n + 1)) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin (n + 1) => μ)))
  have hi (j : Fin (n + 1 + 1)) :
      Integrable (fun t : Fin (n + 1) → Q =>
        (firstRowPiece (AugmentedMatrixValue k (n + 1) x y t) j).det)
        (MeasurePowerValue μ (n + 1)) :=
    (continuous_firstRowPiece k _ x y j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ t, (AugmentedMatrixValue k (n + 1) x y t).det
    ∂MeasurePowerValue μ (n + 1)) = _
  have hsum (t : Fin (n + 1) → Q) :=
    det_eq_sum_firstRowPiece (AugmentedMatrixValue k (n + 1) x y t)
  simp_rw [hsum]
  rw [integral_finsetSum _ (fun j _ => hi j), Fin.sum_univ_succ]
  simp_rw [det_firstRowPiece_zero, integral_const_mul,
    integral_firstRowPiece_eq μ k n x y, integral_firstRowPiece_one μ k n x y]
  simp [sub_eq_add_neg, DeterminantIntegralValue]

lemma minorTerm_succ (z : ℂ) (n : ℕ) (x y : Q) :
    MinorTermValue μ k x y z (n + 1) =
      DeterminantTermValue μ k z (n + 1) * k (x, y) +
        z * ∫ t, k (x, t) * MinorTermValue μ k t y z n ∂μ := by
  have he : (∫ t, k (x, t) * MinorTermValue μ k t y z n ∂μ) =
      ((-z) ^ n / (n.factorial : ℂ)) *
        ∫ t, k (x, t) * MinorIntegralValue μ k n t y ∂μ := by
    simp only [MinorTermValue]
    simp_rw [mul_left_comm (k (x, _)) ((-z) ^ n / (n.factorial : ℂ))]
    exact integral_const_mul _ _
  rw [he]
  unfold MinorTermValue DeterminantTermValue
  rw [minorIntegral_succ μ k n x y, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp
  ring

/-- Fubini in the diagonal slot identifies the (n+1)-determinant integral
with the diagonal integral of the nth augmented determinant. -/
lemma determinantIntegral_succ (n : ℕ) :
    DeterminantIntegralValue μ k (n + 1) =
      ∫ x, MinorIntegralValue μ k n x x ∂μ := by
  change (∫ t, (KernelMatrixValue k (n + 1) t).det ∂MeasurePowerValue μ (n + 1)) = _
  exact integral_nodes_succ μ n (fun t => (KernelMatrixValue k (n + 1) t).det)
    (ClassicalDefinitions.continuous_kernel_determinant k (n + 1))

lemma diagonal_integrable (b : C(Q × Q, ℂ)) : Integrable (fun t => b (t, t)) μ :=
  (b.continuous.comp (continuous_id.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The diagonal integral is a bounded linear functional on continuous kernels. -/
noncomputable def diagonalIntegral : C(Q × Q, ℂ) →L[ℂ] ℂ :=
  ( { toFun := fun b => ∫ t, b (t, t) ∂μ
      map_add' := fun b c => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (diagonal_integrable μ b) (diagonal_integrable μ c)
      map_smul' := fun a b => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul a _ } : C(Q × Q, ℂ) →ₗ[ℂ] ℂ).mkContinuous
    (μ.real Set.univ) (fun b => by
      change ‖∫ t, b (t, t) ∂μ‖ ≤ μ.real Set.univ * ‖b‖
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall fun t => b.norm_coe_le_norm (t, t)))

lemma diagonal_minorCoefficient (n : ℕ) :
    diagonalIntegral μ (minorCoefficient μ k n) = DeterminantIntegralValue μ k (n + 1) := by
  change (∫ t, minorCoefficient μ k n (t, t) ∂μ) = _
  simp_rw [(ClassicalEntireSeries.coefficient_identification μ k n).2.1]
  exact (determinantIntegral_succ μ k n).symm

lemma deriv_determinantTerm_succ (z : ℂ) (n : ℕ) :
    deriv (fun w => DeterminantTermValue μ k w (n + 1)) z =
      -diagonalIntegral μ (minorKernelTerm μ k z n) := by
  have h := (((hasDerivAt_id z).neg.pow (n + 1)).div_const
    ((n + 1).factorial : ℂ)).mul_const (DeterminantIntegralValue μ k (n + 1))
  change deriv (fun w => (-w) ^ (n + 1) / ((n + 1).factorial : ℂ) *
    DeterminantIntegralValue μ k (n + 1)) z = _
  have hd := h.deriv
  change deriv (fun w => (-w) ^ (n + 1) / ((n + 1).factorial : ℂ) *
    DeterminantIntegralValue μ k (n + 1)) z = _ at hd
  rw [hd]
  simp only [minorKernelTerm, map_smul, smul_eq_mul, diagonal_minorCoefficient,
    Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Pi.neg_apply, id_eq]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

lemma diagonal_minor_sum (z : ℂ) :
    HasSum (fun n => diagonalIntegral μ (minorKernelTerm μ k z n))
      (∫ t, FredholmMinorValue μ k t t z ∂μ) := by
  have hs := ((ClassicalEntireSeries.absolute_convergence μ k z).2.of_norm.hasSum).mapL (diagonalIntegral μ)
  change HasSum _ (diagonalIntegral μ (minorKernel μ k z)) at hs
  change HasSum _ (∫ t, minorKernel μ k z (t, t) ∂μ) at hs
  simpa only [ClassicalEntireSeries.minor_kernel_identification μ k z] using hs

lemma kernelOperator_apply (b : C(Q × Q, ℂ)) (f : C(Q, ℂ)) (x : Q) :
    KernelOperatorValue μ b f x = ∫ y, b (x, y) * f y ∂μ :=
  (ClassicalDefinitions.data_identification μ b).1 f x

lemma kernelOperator_comp_apply (a b : C(Q × Q, ℂ)) (f : C(Q, ℂ)) (x : Q) :
    (KernelOperatorValue μ a).comp (KernelOperatorValue μ b) f x =
      ∫ y, (∫ t, a (x, t) * b (t, y) ∂μ) * f y ∂μ := by
  have hi : Integrable (fun p : Q × Q => a (x, p.1) * (b (p.1, p.2) * f p.2))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (a.continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (b.continuous.mul (f.continuous.comp continuous_snd))
  change KernelOperatorValue μ a (KernelOperatorValue μ b f) x = _
  simp_rw [kernelOperator_apply, ← integral_const_mul]
  rw [integral_integral_swap hi]
  simp_rw [← mul_assoc, integral_mul_const]

/-- Passing a pointwise kernel identity through integration preserves its
operator meaning; Fubini establishes the composition term. -/
lemma operator_identity_of_kernel_identity (a b c : C(Q × Q, ℂ)) (D z : ℂ)
    (h : ∀ x y, c (x, y) = D * k (x, y) + z * ∫ t, a (x, t) * b (t, y) ∂μ) :
    KernelOperatorValue μ c = D • KernelOperatorValue μ k +
      z • (KernelOperatorValue μ a).comp (KernelOperatorValue μ b) := by
  ext f x
  change KernelOperatorValue μ c f x =
    D * KernelOperatorValue μ k f x +
      z * ((KernelOperatorValue μ a).comp (KernelOperatorValue μ b) f) x
  have hi (d : C(Q × Q, ℂ)) : Integrable (fun y => d (x, y) * f y) μ :=
    ExpandedFA.PartV.ContinuousKernel.Spec.kernel_integrable_section μ d f x
  have he : (fun y => c (x, y) * f y - D * (k (x, y) * f y)) =
      fun y => z * ((∫ t, a (x, t) * b (t, y) ∂μ) * f y) := by
    funext y
    rw [h x y]
    ring
  have hei := congrArg (fun g : Q → ℂ => ∫ y, g y ∂μ) he
  rw [integral_sub (hi c) ((hi k).const_mul D), integral_const_mul,
    integral_const_mul, ← kernelOperator_comp_apply] at hei
  simp_rw [← kernelOperator_apply] at hei
  linear_combination hei

/-- Integration against one fixed row of k and one fixed column of a varying
kernel is a continuous linear functional for the supremum norm. -/
noncomputable def leftConvolutionAt (x y : Q) : C(Q × Q, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x).comp ((KernelOperatorValue μ k).comp
    (ContinuousMap.compCLM ℂ ℂ ⟨fun t => (t, y), continuous_id.prodMk continuous_const⟩))

lemma leftConvolutionAt_apply (x y : Q) (b : C(Q × Q, ℂ)) :
    leftConvolutionAt μ k x y b = ∫ t, k (x, t) * b (t, y) ∂μ := by
  exact kernelOperator_apply μ k _ _

lemma minor_hasSum (z : ℂ) (x y : Q) :
    HasSum (fun n => MinorTermValue μ k x y z n) (FredholmMinorValue μ k x y z) := by
  have hs := ((ClassicalEntireSeries.absolute_convergence μ k z).2.of_norm.hasSum).mapL
    (ContinuousMap.evalCLM ℂ (x, y))
  change HasSum (fun n => minorKernelTerm μ k z n (x, y)) (minorKernel μ k z (x, y)) at hs
  simpa only [(ClassicalEntireSeries.coefficient_identification μ k _).2.2,
    ClassicalEntireSeries.minor_kernel_identification μ k z] using hs

lemma left_convolution_hasSum (z : ℂ) (x y : Q) :
    HasSum (fun n => ∫ t, k (x, t) * MinorTermValue μ k t y z n ∂μ)
      (∫ t, k (x, t) * FredholmMinorValue μ k t y z ∂μ) := by
  have hs := ((ClassicalEntireSeries.absolute_convergence μ k z).2.of_norm.hasSum).mapL
    (leftConvolutionAt μ k x y)
  change HasSum _ (leftConvolutionAt μ k x y (minorKernel μ k z)) at hs
  simp only [leftConvolutionAt_apply] at hs
  simpa only [(ClassicalEntireSeries.coefficient_identification μ k _).2.2,
    ClassicalEntireSeries.minor_kernel_identification μ k z] using hs

lemma left_kernel_identity (z : ℂ) (x y : Q) :
    FredholmMinorValue μ k x y z = FredholmDeterminantValue μ k z * k (x, y) +
      z * ∫ t, k (x, t) * FredholmMinorValue μ k t y z ∂μ := by
  have hsD := (ClassicalEntireSeries.absolute_convergence μ k z).1.of_norm.hasSum
  change HasSum (fun n => DeterminantTermValue μ k z n) (FredholmDeterminantValue μ k z) at hsD
  have hsDs : HasSum (fun n => DeterminantTermValue μ k z (n + 1))
      (FredholmDeterminantValue μ k z - 1) := by
    simpa only [Finset.sum_range_one, (ClassicalDefinitions.zeroth_terms μ k).2.2.1] using
      (hasSum_nat_add_iff' 1).mpr hsD
  have hsBs : HasSum (fun n => MinorTermValue μ k x y z (n + 1))
      (FredholmMinorValue μ k x y z - k (x, y)) := by
    simpa only [Finset.sum_range_one, (ClassicalDefinitions.zeroth_terms μ k).2.2.2.2.2] using
      (hasSum_nat_add_iff' 1).mpr (minor_hasSum μ k z x y)
  have hs := (hsDs.mul_right (k (x, y))).add ((left_convolution_hasSum μ k z x y).mul_left z)
  have he := hsBs.unique (by simpa only [minorTerm_succ μ k z] using hs)
  linear_combination he

/-- Plain transposition, with no complex conjugation. -/
noncomputable def transposeKernel : C(Q × Q, ℂ) := k.comp ⟨Prod.swap, continuous_swap⟩

omit [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] in
lemma transposeKernel_apply (x y : Q) : transposeKernel k (x, y) = k (y, x) := rfl

omit [CompactSpace Q] [BorelSpace Q] [IsFiniteMeasure μ] in
lemma determinant_transpose (z : ℂ) :
    FredholmDeterminantValue μ (transposeKernel k) z = FredholmDeterminantValue μ k z := by
  have he (n : ℕ) (t : Fin n → Q) :
      KernelMatrixValue (transposeKernel k) n t = (KernelMatrixValue k n t).transpose := rfl
  simp only [FredholmDeterminantValue, DeterminantTermValue, DeterminantIntegralValue,
    he, Matrix.det_transpose]

omit [CompactSpace Q] [BorelSpace Q] [IsFiniteMeasure μ] in
lemma minor_transpose (z : ℂ) (x y : Q) :
    FredholmMinorValue μ (transposeKernel k) x y z = FredholmMinorValue μ k y x z := by
  have he (n : ℕ) (t : Fin n → Q) :
      AugmentedMatrixValue (transposeKernel k) n x y t =
        (AugmentedMatrixValue k n y x t).transpose := rfl
  simp only [FredholmMinorValue, MinorTermValue, MinorIntegralValue, he, Matrix.det_transpose]

lemma right_kernel_identity (z : ℂ) (x y : Q) :
    FredholmMinorValue μ k x y z = FredholmDeterminantValue μ k z * k (x, y) +
      z * ∫ t, FredholmMinorValue μ k x t z * k (t, y) ∂μ := by
  have h := left_kernel_identity μ (transposeKernel k) z y x
  simp only [minor_transpose, determinant_transpose, transposeKernel_apply] at h
  simpa only [mul_comm (k (_, y))] using h

end

theorem kernel_identities : Spec.KernelIdentities.{u} := by
  intro Q _ _ _ _ μ _ k z x y
  exact ⟨left_kernel_identity μ k z x y, right_kernel_identity μ k z x y⟩

/-- Pure algebra after the two kernel identities have been lifted to operators. -/
lemma inverse_of_operator_identities {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K B : E →L[ℂ] E) (D z : ℂ) (hD : D ≠ 0)
    (hL : B = D • K + z • K.comp B) (hR : B = D • K + z • B.comp K) :
    (1 - z • K).comp (1 + (z / D) • B) = 1 ∧
      (1 + (z / D) • B).comp (1 - z • K) = 1 := by
  have hc : z / D * D = z := div_mul_cancel₀ z hD
  have hl : (z / D) • B = z • K + (z * (z / D)) • K.comp B := by
    conv_lhs => rw [hL]
    rw [smul_add, smul_smul, smul_smul, hc, mul_comm (z / D) z]
  have hr : (z / D) • B = z • K + (z * (z / D)) • B.comp K := by
    conv_lhs => rw [hR]
    rw [smul_add, smul_smul, smul_smul, hc, mul_comm (z / D) z]
  constructor
  · simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
      smul_sub, smul_smul]
    rw [mul_comm (z / D) z, hl]
    abel
  · simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
      smul_add, smul_smul]
    rw [hr]
    abel

/-- Assembly lemma with the exact two identities as its explicit hypotheses.
The pointwise equations provide all hypotheses; no inverse certificate is assumed. -/
lemma two_sided_inverse_of_kernel_identities (h : Spec.KernelIdentities.{u}) :
    Spec.TwoSidedInverse.{u} := by
  intro Q _ _ _ _ μ _ k z hD
  let b := minorKernel μ k z
  have hi (x y : Q) := h μ k z x y
  simp_rw [← ClassicalEntireSeries.minor_kernel_identification μ k z] at hi
  have hl := operator_identity_of_kernel_identity μ k k b b
    (FredholmDeterminantValue μ k z) z (fun x y => (hi x y).1)
  have hr := operator_identity_of_kernel_identity μ k b k b
    (FredholmDeterminantValue μ k z) z (fun x y => (hi x y).2)
  exact inverse_of_operator_identities _ _ _ _ hD hl hr

theorem two_sided_inverse : Spec.TwoSidedInverse.{u} :=
  two_sided_inverse_of_kernel_identities kernel_identities

theorem diagonal_derivative : Spec.DiagonalDerivative.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hd := (ClassicalEntireSeries.termwise_differentiation μ k z).1
  have hz : deriv (fun w => DeterminantTermValue μ k w 0) z = 0 := by
    have he : (fun w => DeterminantTermValue μ k w 0) = fun _ : ℂ => 1 := by
      funext w
      exact (ClassicalDefinitions.zeroth_terms μ k).2.2.1 w
    rw [he, deriv_const]
  have hds : HasSum (fun n => deriv (fun w => DeterminantTermValue μ k w (n + 1)) z)
      (deriv (FredholmDeterminantValue μ k) z) := by
    simpa only [Finset.sum_range_one, hz, sub_zero] using
      (hasSum_nat_add_iff' 1).mpr hd
  simp_rw [deriv_determinantTerm_succ μ k z] at hds
  exact hds.unique (diagonal_minor_sum μ k z).neg

end ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities
