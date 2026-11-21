import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.HolderDeterminantBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalDefinitions
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Finset Module
open scoped Matrix
namespace ExpandedFA.FredholmDeterminant.HolderDeterminantBound

/-- Hadamard's inequality over ℂ, proved by Gram--Schmidt. -/
lemma norm_basis_det_le {n : ℕ} (v : Fin n → EuclideanSpace ℂ (Fin n))
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    ‖e.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n)) v
  have hchange : e.toBasis.det v = e.toBasis.det b * b.toBasis.det v := by
    rw [Basis.det_apply, Basis.det_apply, Basis.det_apply, ← Matrix.det_mul]
    exact congrArg Matrix.det (e.toBasis.toMatrix_mul_toMatrix b.toBasis v).symm
  rw [hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  simpa only [b.norm_eq_one, one_mul] using norm_inner_le_norm (b i) (v i)

lemma norm_det_le_column_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j) (hA : ∀ i j, ‖A i j‖ ≤ c j) :
    ‖A.det‖ ≤ (Real.sqrt n) ^ n * ∏ j, c j := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have he : e.toBasis.det v = A.det := by
    rw [Basis.det_apply]
    rfl
  have hnorm (j : Fin n) : ‖v j‖ ≤ Real.sqrt n * c j := by
    rw [EuclideanSpace.norm_eq]
    calc
      Real.sqrt (∑ i, ‖v j i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, (c j) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = Real.sqrt n * c j := by simp [Real.sqrt_mul, Real.sqrt_sq (hc j)]
  calc
    ‖A.det‖ = ‖e.toBasis.det v‖ := congrArg norm he.symm
    _ ≤ ∏ j, ‖v j‖ := norm_basis_det_le v e
    _ ≤ ∏ j, (Real.sqrt n * c j) := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hnorm j)
    _ = _ := by simp [prod_mul_distrib]

/-- Simultaneous successive column differences preserve the determinant. -/
lemma det_successive_differences {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    (Matrix.of (fun i => Fin.snoc (fun j : Fin m => A i j.castSucc - A i j.succ)
      (A i (Fin.last m)))).det = A.det := by
  classical
  let S : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
    fun i j => if i.val = j.val + 1 then 1 else 0
  have hS (i j : Fin (m+1)) : S i j = if i.val = j.val + 1 then 1 else 0 := rfl
  have htri : (1 - S).IsLowerTriangular := by
    intro i j hij
    have hlt : i < j := hij
    have hne : i ≠ j := ne_of_lt hlt
    have hval : i.val ≠ j.val + 1 := by omega
    simp [Matrix.sub_apply, hne, hS, hval]
  have hdet : (1 - S).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    have hdiag (i : Fin (m+1)) : (1 - S) i i = 1 := by
      simp [Matrix.sub_apply, hS]
    simp_rw [hdiag]
    simp
  have hmul : A * (1 - S) = Matrix.of (fun i =>
      Fin.snoc (fun j : Fin m => A i j.castSucc - A i j.succ) (A i (Fin.last m))) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    ext i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have hz (k : Fin (m+1)) : S k (Fin.last m) = 0 := by
        have hk : k.val ≠ m+1 := by omega
        simp [hS, hk]
      simp [Matrix.sub_apply, Matrix.mul_apply, hz]
    · have hsum : (A * S) i j.castSucc = A i j.succ := by
        rw [Matrix.mul_apply, sum_eq_single j.succ]
        · simp [hS]
        · intro k _ hkj
          have : k.val ≠ j.val + 1 := by
            intro hk
            apply hkj
            exact Fin.ext hk
          simp [hS, this]
        · simp
      simp [Matrix.sub_apply, hsum]
  rw [← hmul, Matrix.det_mul, hdet, mul_one]

/-- AM--GM in the form needed for the possibly zero consecutive gaps. -/
lemma gap_product_bound {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ)
    (hg : ∀ j, 0 ≤ g j) (L α : ℝ) (hα : 0 ≤ α) (hsum : ∑ j, g j ≤ L) :
    (∏ j, g j ^ α) ≤ (L / (m : ℝ)) ^ (α * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgm := Real.geom_mean_le_arith_mean univ (fun _ : Fin m => (1 : ℝ)) g
    (by simp) (by simpa using hmR) (by simpa using hg)
  simp only [Real.rpow_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at hgm
  have hle : (∏ j, g j) ^ (m : ℝ)⁻¹ ≤ L / m :=
    hgm.trans (div_le_div_of_nonneg_right hsum hmR.le)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg fun j _ => hg j) _) hle
    (mul_nonneg hα hmR.le)
  rw [← Real.rpow_mul (prod_nonneg fun j _ => hg j)] at hh
  have hexp : (m : ℝ)⁻¹ * (α * m) = α := by field_simp
  rw [hexp, ← Real.finsetProd_rpow _ _ (fun j _ => hg j)] at hh
  exact hh

lemma sum_successive_gaps {m : ℕ} (y : Fin (m+1) → ℝ) :
    (∑ j : Fin m, (y j.succ - y j.castSucc)) = y (Fin.last m) - y 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun j => y j.succ)
    simp only [Fin.succ_last, Fin.succ_zero_eq_one] at h
    have heq : (∑ j : Fin m, (y j.succ.succ - y j.succ.castSucc)) =
        ∑ j : Fin m, (y j.succ.succ - y j.castSucc.succ) := by
      rfl
    rw [heq, h]
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
    ring

lemma constants_nonneg {a b M H α : ℝ} (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, ℂ))
    (hM : Spec.Bounded k M) (hH : Spec.HolderSecond k H α) : 0 ≤ M ∧ 0 ≤ H := by
  let x : Spec.Interval a b := ⟨a, le_rfl, hab.le⟩
  let y : Spec.Interval a b := ⟨b, hab.le, le_rfl⟩
  have hM0 := (norm_nonneg (k (x,x))).trans (hM x x)
  have hH0 := (norm_nonneg (k (x,x) - k (x,y))).trans (hH x x y)
  have hp : 0 < |a-b| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hab.ne)) α
  dsimp [x,y] at hH0
  exact ⟨hM0, by nlinarith⟩

lemma sqrt_pow (n : ℕ) : (Real.sqrt (n : ℝ)) ^ n = (n : ℝ) ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  ring

lemma sorted_determinant_bound {a b M H α : ℝ} (hab : a < b)
    (k : C(Spec.Interval a b × Spec.Interval a b, ℂ))
    (hα : 0 ≤ α) (hM : Spec.Bounded k M) (hH : Spec.HolderSecond k H α)
    (m : ℕ) (hm : 0 < m) (x y : Fin (m+1) → Spec.Interval a b)
    (hy : Monotone (fun j => (y j : ℝ))) :
    ‖(Matrix.of (fun i j => k (x i,y j))).det‖ ≤ Spec.bound a b M H α (m+1) := by
  obtain ⟨hM0,hH0⟩ := constants_nonneg hab k hM hH
  let g : Fin m → ℝ := fun j => (y j.succ : ℝ) - (y j.castSucc : ℝ)
  have hg (j : Fin m) : 0 ≤ g j := sub_nonneg.mpr (hy (Fin.castSucc_le_succ j))
  have hsum : (∑ j, g j) ≤ b-a := by
    rw [show (∑ j, g j) = (y (Fin.last m) : ℝ) - (y 0 : ℝ) from
      sum_successive_gaps (fun j => (y j : ℝ))]
    linarith [(y (Fin.last m)).property.2, (y 0).property.1]
  have hgap := gap_product_bound hm g hg (b-a) α hα hsum
  let A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j => k (x i,y j)
  let D : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i =>
    Fin.snoc (fun j : Fin m => A i j.castSucc - A i j.succ) (A i (Fin.last m))
  let c : Fin (m+1) → ℝ := Fin.snoc (fun j : Fin m => H * g j ^ α) M
  have hc (j : Fin (m+1)) : 0 ≤ c j := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [c] using hM0
    · simpa [c] using mul_nonneg hH0 (Real.rpow_nonneg (hg j) α)
  have hD (i j : Fin (m+1)) : ‖D i j‖ ≤ c j := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [D,c,A] using hM (x i) (y (Fin.last m))
    · have h := hH (x i) (y j.castSucc) (y j.succ)
      have habs : |(y j.castSucc : ℝ) - (y j.succ : ℝ)| = g j := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (hg j)
      simpa only [D, A, c, Fin.snoc_castSucc, habs] using h
  have hprod : (∏ j, c j) = (H ^ m * ∏ j, g j ^ α) * M := by
    simp [c, prod_mul_distrib]
  calc
    ‖(Matrix.of (fun i j => k (x i,y j))).det‖ = ‖D.det‖ :=
      congrArg norm (det_successive_differences A).symm
    _ ≤ Real.sqrt (m+1) ^ (m+1) * ∏ j, c j := by
      simpa only [Nat.cast_add, Nat.cast_one] using norm_det_le_column_bounds D c hc hD
    _ = Real.sqrt (m+1) ^ (m+1) * ((H ^ m * ∏ j, g j ^ α) * M) := by rw [hprod]
    _ ≤ Real.sqrt (m+1) ^ (m+1) * ((H ^ m * ((b-a)/(m : ℝ)) ^ (α*m)) * M) := by
      gcongr
    _ = Spec.bound a b M H α (m+1) := by
      rw [show (m : ℝ) + 1 = ((m+1 : ℕ) : ℝ) by simp, sqrt_pow]
      simp only [Spec.bound, Nat.add_sub_cancel]
      ring

theorem second_variable_bound : Spec.SecondVariableBound := by
  intro a b hab k M H α hα _hα1 hM hH n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro x y
  let σ := Tuple.sort (fun j => (y j : ℝ))
  have hsorted := sorted_determinant_bound hab k hα.le hM hH m (by omega) x
    (y ∘ σ) (Tuple.monotone_sort (fun j => (y j : ℝ)))
  have heq : ‖(Matrix.of (fun i j => k (x i, y (σ j)))).det‖ =
      ‖(Matrix.of (fun i j => k (x i,y j))).det‖ := by
    change ‖((Matrix.of (fun i j => k (x i,y j))).submatrix id σ).det‖ = _
    rw [Matrix.det_permute', norm_mul, Complex.norm_intCast, abs_unit_intCast, one_mul]
  exact heq ▸ hsorted

theorem first_variable_bound : Spec.FirstVariableBound := by
  intro a b hab k M H α hα hα1 hM hH n hn x y
  let kt : C(Spec.Interval a b × Spec.Interval a b, ℂ) :=
    ⟨fun p => k (p.2,p.1), k.continuous.comp continuous_swap⟩
  have hMt : Spec.Bounded kt M := fun x y => hM y x
  have hHt : Spec.HolderSecond kt H α := fun x y z => hH y z x
  have ht := second_variable_bound a b hab kt M H α hα hα1 hMt hHt n hn y x
  have heq : (Matrix.of (fun i j => kt (y i,x j))).det =
      (Matrix.of (fun i j => k (x i,y j))).det := by
    rw [← Matrix.det_transpose]
    rfl
  rwa [heq] at ht

theorem coefficient_identification : Spec.CoefficientIdentification := by
  intro a b μ k z n
  change (-z)^n / (n.factorial : ℂ) * _ =
    z^n * ((-1 : ℂ)^n / (n.factorial : ℂ) * _)
  rw [show -z = (-1 : ℂ) * z by ring, mul_pow]
  ring

theorem coefficient_bound : Spec.CoefficientBound := by
  intro a b hab μ _ k M H α hα hα1 hM hH n hn
  let B := Spec.bound a b M H α n
  have hb (t : Fin n → Spec.Interval a b) :
      ‖(ClassicalDefinitions.Spec.KernelMatrixValue k n t).det‖ ≤ B := by
    rcases hH with hH | hH
    · exact second_variable_bound a b hab k M H α hα hα1 hM hH n hn t t
    · exact first_variable_bound a b hab k M H α hα hα1 hM hH n hn t t
  have hmass : (ClassicalDefinitions.Spec.MeasurePowerValue μ n).real Set.univ =
      (μ.real Set.univ) ^ n := by
    simp [measureReal_def, ClassicalDefinitions.Spec.MeasurePowerValue, Measure.pi_univ]
  have : IsFiniteMeasure (ClassicalDefinitions.Spec.MeasurePowerValue μ n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Fin n => μ)))
  have hint : ‖ClassicalDefinitions.Spec.DeterminantIntegralValue μ k n‖ ≤
      B * (μ.real Set.univ) ^ n := by
    unfold ClassicalDefinitions.Spec.DeterminantIntegralValue
    have h := norm_integral_le_of_norm_le_const
      (μ := ClassicalDefinitions.Spec.MeasurePowerValue μ n) (Filter.Eventually.of_forall hb)
    rwa [hmass] at h
  calc
    ‖ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n‖ =
        ‖ClassicalDefinitions.Spec.DeterminantIntegralValue μ k n‖ / (n.factorial : ℝ) := by
      simp [ClassicalDefinitions.Spec.DeterminantTermValue, norm_pow,
        div_eq_mul_inv, mul_comm]
    _ ≤ (B * (μ.real Set.univ) ^ n) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right hint (Nat.cast_nonneg _)
    _ = (μ.real Set.univ) ^ n / (n.factorial : ℝ) * Spec.bound a b M H α n := by ring

end ExpandedFA.FredholmDeterminant.HolderDeterminantBound
