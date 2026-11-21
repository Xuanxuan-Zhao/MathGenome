import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000

noncomputable section
open scoped SchwartzMap FourierTransform ContDiff NNReal
open MeasureTheory LineDeriv
namespace P102.U3

/-- Standard Euclidean coordinates, shared with the independent specification. -/
abbrev Euclidean (d : ℕ) := P102.Specs.U3.Euclidean d
/-- Complex Schwartz functions on the standard Euclidean model. -/
abbrev Test (d : ℕ) := P102.Specs.U3.Test d
/-- The continuous complex-linear dual, with bounded convergence topology. -/
abbrev Tempered (d : ℕ) := P102.Specs.U3.Tempered d
/-- Continuous complex-linear functionals with pointwise testing topology. -/
abbrev WeakTempered (d : ℕ) := P102.Specs.U3.WeakTempered d

def fourier (d : ℕ) : Test d →L[ℂ] Test d := FourierTransform.fourierCLM ℂ (Test d)
def check (d : ℕ) : Test d →L[ℂ] Test d := FourierTransform.fourierInvCLM ℂ (Test d)

@[simp] theorem coordinatePartial_apply {d n : ℕ} (β : Fin n → Fin d) (f : Test d) (x : Euclidean d) :
    coordinatePartial β f x = iteratedFDeriv ℝ n f x (coordinateVector ∘ β) :=
  SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

@[simp] theorem coordinateMul_apply {d : ℕ} (j : Fin d) (f : Test d) (x : Euclidean d) :
    coordinateMul j f x = (x j : ℂ) * f x := by
  unfold coordinateMul
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [coordinateVector, EuclideanSpace.inner_basisFun_real, smul_eq_mul]

 theorem coordinateMul_eq_real {d : ℕ} (j : Fin d) (f : Test d) :
    coordinateMul j f = SchwartzMap.smulLeftCLM ℂ (inner ℝ · (coordinateVector j)) f := by
  ext x
  rw [coordinateMul_apply, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [coordinateVector, EuclideanSpace.inner_basisFun_real, Complex.real_smul]

@[simp] theorem polynomialMul_apply {d n : ℕ} (c : ℂ) (β : Fin n → Fin d)
    (f : Test d) (x : Euclidean d) :
    polynomialMul c β f x = (∏ i, c * (x (β i) : ℂ)) * f x := by
  induction n with
  | zero => simp [polynomialMul]
  | succ n ih =>
    simp [polynomialMul, ih, Fin.prod_univ_succ, mul_assoc, Fin.tail_def]

 theorem fourier_integral {d : ℕ} (f : Test d) (ξ : Euclidean d) :
    fourier d f ξ = ∫ x : Euclidean d,
      Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) * f x := by
  exact Real.fourier_eq' (f : Euclidean d → ℂ) ξ

 theorem check_integral {d : ℕ} (f : Test d) (x : Euclidean d) :
    check d f x = ∫ ξ : Euclidean d,
      Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I) * f ξ := by
  change (𝓕⁻ f) x = _
  rw [SchwartzMap.fourierInv_coe]
  exact Real.fourierInv_eq' (f : Euclidean d → ℂ) x

 theorem fourier_continuous (d : ℕ) : Continuous (fourier d) := (fourier d).continuous
 theorem check_continuous (d : ℕ) : Continuous (check d) := (check d).continuous

 theorem partial_fourier {d n : ℕ} (β : Fin n → Fin d) (f : Test d) :
    coordinatePartial β (fourier d f) = fourier d (polynomialMul (-(2 * Real.pi * Complex.I)) β f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change ∂_{coordinateVector (β 0)} (coordinatePartial (Fin.tail β) (fourier d f)) = _
    rw [ih]
    change ∂_{coordinateVector (β 0)} (𝓕 (polynomialMul (-(2 * Real.pi * Complex.I)) (Fin.tail β) f)) = _
    rw [SchwartzMap.lineDerivOp_fourier_eq]
    simp only [polynomialMul, ContinuousLinearMap.comp_apply, smul_apply,
      coordinateMul_eq_real]
    rfl

 theorem fourier_partial {d n : ℕ} (β : Fin n → Fin d) (f : Test d) :
    fourier d (coordinatePartial β f) = polynomialMul (2 * Real.pi * Complex.I) β (fourier d f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change 𝓕 (∂_{coordinateVector (β 0)} (coordinatePartial (Fin.tail β) f)) = _
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    rw [show 𝓕 (coordinatePartial (Fin.tail β) f) =
      polynomialMul (2 * Real.pi * Complex.I) (Fin.tail β) (fourier d f) from ih _ f]
    simp only [polynomialMul, ContinuousLinearMap.comp_apply, smul_apply,
      coordinateMul_eq_real]

 theorem partial_check {d n : ℕ} (β : Fin n → Fin d) (f : Test d) :
    coordinatePartial β (check d f) = check d (polynomialMul (2 * Real.pi * Complex.I) β f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change ∂_{coordinateVector (β 0)} (coordinatePartial (Fin.tail β) (check d f)) = _
    rw [ih]
    change ∂_{coordinateVector (β 0)} (𝓕⁻ (polynomialMul (2 * Real.pi * Complex.I) (Fin.tail β) f)) = _
    rw [SchwartzMap.lineDerivOp_fourierInv_eq]
    simp only [polynomialMul, ContinuousLinearMap.comp_apply, smul_apply,
      coordinateMul_eq_real]
    rfl

 theorem check_partial {d n : ℕ} (β : Fin n → Fin d) (f : Test d) :
    check d (coordinatePartial β f) = polynomialMul (-(2 * Real.pi * Complex.I)) β (check d f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change 𝓕⁻ (∂_{coordinateVector (β 0)} (coordinatePartial (Fin.tail β) f)) = _
    rw [SchwartzMap.fourierInv_lineDerivOp_eq]
    rw [show 𝓕⁻ (coordinatePartial (Fin.tail β) f) =
      polynomialMul (-(2 * Real.pi * Complex.I)) (Fin.tail β) (check d f) from ih _ f]
    simp only [polynomialMul, ContinuousLinearMap.comp_apply, smul_apply,
      coordinateMul_eq_real]

 theorem norm_coordinateVector {d : ℕ} (j : Fin d) : ‖coordinateVector j‖ = 1 := by
  exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one j

 theorem coordinate_eval_le_norm {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ)
    (β : Fin n → Fin d) : ‖A (coordinateVector ∘ β)‖ ≤ ‖A‖ := by
  simpa using A.le_opNorm_mul_prod_of_le (m := coordinateVector ∘ β)
    (b := fun _ => (1 : ℝ)) (fun i => (norm_coordinateVector (β i)).le)

 theorem multilinear_norm_le_coordinate_sum {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ) :
    ‖A‖ ≤ ∑ β : Fin n → Fin d, ‖A (coordinateVector ∘ β)‖ := by
  classical
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hrep (i : Fin n) : ∑ j : Fin d, (v i) j • coordinateVector j = v i :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v i)
  calc
    ‖A v‖ = ‖A (fun i => ∑ j : Fin d, (v i) j • coordinateVector j)‖ := by
      simp only [hrep]
    _ = ‖∑ β : Fin n → Fin d,
        (∏ i, (v i) (β i)) • A (coordinateVector ∘ β)‖ := by
      rw [A.map_sum]
      simp_rw [A.map_smul_univ]
      rfl
    _ ≤ ∑ β : Fin n → Fin d, ‖(∏ i, (v i) (β i)) • A (coordinateVector ∘ β)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ β : Fin n → Fin d, (∏ i, ‖v i‖) * ‖A (coordinateVector ∘ β)‖ := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul, norm_prod]
      gcongr with i
      exact PiLp.norm_apply_le (v i) (β i)
    _ = (∑ β : Fin n → Fin d, ‖A (coordinateVector ∘ β)‖) * ∏ i, ‖v i‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro β _
      exact mul_comm _ _

 theorem multilinear_norm_le_coordinate_bound {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ) {C : ℝ}
    (hC : ∀ β : Fin n → Fin d, ‖A (coordinateVector ∘ β)‖ ≤ C) :
    ‖A‖ ≤ (d : ℝ) ^ n * C := by
  apply (multilinear_norm_le_coordinate_sum A).trans
  calc
    _ ≤ ∑ _ : Fin n → Fin d, C := Finset.sum_le_sum fun β _ => hC β
    _ = _ := by simp

@[simp] theorem radialPoint_apply {d n : ℕ} (N : ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) (f : Test d) :
    radialPoint N β x f = (1 + ‖x‖) ^ N * ‖coordinatePartial β f x‖ := by
  change (Real.toNNReal ((1 + ‖x‖) ^ N) : ℝ) * ‖coordinatePartial β f x‖ = _
  rw [Real.coe_toNNReal _ (by positivity)]

 theorem radialPoint_le_native {d k : ℕ} (N : ℕ) (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d) :
    radialPoint N β x ≤ (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) := by
  intro f
  rw [radialPoint_apply, coordinatePartial_apply]
  change (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n.val f x (coordinateVector ∘ β)‖ ≤
    2 ^ N * ((Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)) f
  exact (mul_le_mul_of_nonneg_left (coordinate_eval_le_norm _ β) (by positivity)).trans
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N,k)) le_rfl
      (Nat.le_of_lt_succ n.isLt) f x)

private theorem seminorm_iSup_le {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : ι → Seminorm ℂ E) (q : Seminorm ℂ E) (h : ∀ i, p i ≤ q) : (⨆ i, p i) ≤ q := by
  rw [← sSup_range]
  by_cases hi : Nonempty ι
  · let := hi
    exact csSup_le (Set.range_nonempty p) (fun _ ⟨i, hi⟩ => hi ▸ h i)
  · have : IsEmpty ι := not_nonempty_iff.mp hi
    have he : Set.range p = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (by rintro a ⟨i, _⟩; exact isEmptyElim i)
    rw [he, Seminorm.sSup_empty]
    exact bot_le

 theorem manuscriptSeminorm_le_native {d : ℕ} (N k : ℕ) :
    manuscriptSeminorm (d := d) N k ≤ (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) := by
  apply seminorm_iSup_le
  intro n
  apply seminorm_iSup_le
  intro β
  exact seminorm_iSup_le _ _ (fun x => radialPoint_le_native N n β x)

 theorem radialPoint_le_manuscript {d : ℕ} (N k : ℕ) (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d) :
    radialPoint N β x ≤ manuscriptSeminorm N k := by
  let q := (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)
  have h (n : Fin (k+1)) (β : Fin n.val → Fin d) (x : Euclidean d) :
      radialPoint N β x ≤ q := radialPoint_le_native N n β x
  calc
    radialPoint N β x ≤ ⨆ y, radialPoint N β y :=
      le_ciSup ⟨q, by rintro _ ⟨y, rfl⟩; exact h n β y⟩ x
    _ ≤ ⨆ (γ : Fin n.val → Fin d) (y : Euclidean d), radialPoint N γ y :=
      le_ciSup ⟨q, by rintro _ ⟨γ, rfl⟩; exact seminorm_iSup_le _ _ (h n γ)⟩ β
    _ ≤ manuscriptSeminorm N k :=
      le_ciSup ⟨q, by
        rintro _ ⟨m, rfl⟩
        exact seminorm_iSup_le _ _ (fun γ => seminorm_iSup_le _ _ (h m γ))⟩ n

 theorem nativeSeminorm_le_manuscript {d : ℕ} (N n : ℕ) :
    SchwartzMap.seminorm ℂ N n ≤ (d : ℝ≥0) ^ n • manuscriptSeminorm (d := d) N n := by
  intro f
  change SchwartzMap.seminorm ℂ N n f ≤ (d : ℝ) ^ n * manuscriptSeminorm N n f
  apply SchwartzMap.seminorm_le_bound ℂ N n f (by positivity)
  intro x
  have hb (β : Fin n → Fin d) :
      ‖((‖x‖ ^ N : ℝ) • iteratedFDeriv ℝ n f x) (coordinateVector ∘ β)‖ ≤
        manuscriptSeminorm N n f := by
    simp only [smul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    calc
      _ ≤ (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n f x (coordinateVector ∘ β)‖ := by
        gcongr
        linarith [norm_nonneg x]
      _ ≤ _ := by
        simpa only [radialPoint_apply, coordinatePartial_apply] using
          radialPoint_le_manuscript N n ⟨n, Nat.lt_succ_self n⟩ β x f
  simpa only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg x) N)] using
    multilinear_norm_le_coordinate_bound ((‖x‖ ^ N : ℝ) • iteratedFDeriv ℝ n f x) hb

 theorem manuscript_withSeminorms (d : ℕ) : WithSeminorms (manuscriptFamily d) := by
  apply (schwartz_withSeminorms ℂ (Euclidean d) ℂ).congr
  · rintro ⟨N,k⟩
    exact ⟨Finset.Iic (N,k), (2 : ℝ≥0) ^ N, manuscriptSeminorm_le_native N k⟩
  · rintro ⟨N,n⟩
    refine ⟨{(N,n)}, (d : ℝ≥0) ^ n, ?_⟩
    simpa only [Finset.sup_singleton, Seminorm.comp_id, manuscriptFamily,
      schwartzSeminormFamily] using nativeSeminorm_le_manuscript (d := d) N n

 theorem schwartz_is_manuscript {d : ℕ} (f : Test d) : ManuscriptSchwartz (f : Euclidean d → ℂ) := by
  refine ⟨f.smooth _, fun N k => ⟨manuscriptSeminorm N k f, ?_⟩⟩
  intro n β x
  simpa only [radialPoint_apply, coordinatePartial_apply] using radialPoint_le_manuscript N k n β x f

 theorem manuscript_iff_exists_schwartz {d : ℕ} (f : Euclidean d → ℂ) :
    ManuscriptSchwartz f ↔ ∃ φ : Test d, (φ : Euclidean d → ℂ) = f := by
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨⟨f, hs, ?_⟩, rfl⟩
    intro N n
    obtain ⟨C,hC⟩ := hb N n
    refine ⟨(d : ℝ)^n * C, fun x => ?_⟩
    have hβ (β : Fin n → Fin d) :
        ‖((‖x‖ ^ N : ℝ) • iteratedFDeriv ℝ n f x) (coordinateVector ∘ β)‖ ≤ C := by
      simp only [smul_apply, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      calc
        _ ≤ (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n f x (coordinateVector ∘ β)‖ := by
          gcongr
          linarith [norm_nonneg x]
        _ ≤ C := hC ⟨n, Nat.lt_succ_self n⟩ β x
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg x) N)] using
      multilinear_norm_le_coordinate_bound ((‖x‖ ^ N : ℝ) • iteratedFDeriv ℝ n f x) hβ
  · rintro ⟨φ, rfl⟩
    exact schwartz_is_manuscript φ

 theorem coordinateMonomial_bound {d : ℕ} (α : Fin d → ℕ) (x : Euclidean d) :
    |coordinateMonomial α x| ≤ (1 + ‖x‖) ^ (∑ j, α j) := by
  classical
  rw [coordinateMonomial, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro j _
  rw [abs_pow]
  gcongr
  calc
    |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    _ ≤ 1 + ‖x‖ := by linarith

@[simp] theorem monomialPoint_apply {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) (f : Test d) :
    monomialPoint α β x f = |coordinateMonomial α x| * ‖coordinatePartial β f x‖ := by
  change (Real.toNNReal |coordinateMonomial α x| : ℝ) * ‖coordinatePartial β f x‖ = _
  rw [Real.coe_toNNReal _ (abs_nonneg _)]

 theorem monomialPoint_le_radialPoint {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) : monomialPoint α β x ≤ radialPoint (∑ j, α j) β x := by
  intro f
  simp only [monomialPoint_apply, radialPoint_apply]
  exact mul_le_mul_of_nonneg_right (coordinateMonomial_bound α x) (norm_nonneg _)

 theorem monomialSeminorm_le_manuscript {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d) :
    monomialSeminorm α β ≤ manuscriptSeminorm (∑ j, α j) n :=
  seminorm_iSup_le _ _ fun x => (monomialPoint_le_radialPoint α β x).trans
    (radialPoint_le_manuscript _ n ⟨n, Nat.lt_succ_self n⟩ β x)

 theorem monomialPoint_le_monomialSeminorm {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) : monomialPoint α β x ≤ monomialSeminorm α β :=
  le_ciSup ⟨manuscriptSeminorm (∑ j, α j) n, by
    rintro _ ⟨y, rfl⟩
    exact (monomialPoint_le_radialPoint α β y).trans
      (radialPoint_le_manuscript _ n ⟨n, Nat.lt_succ_self n⟩ β y)⟩ x

/-- In an expansion of (1+∑|x_j|)^N, count the choices of each coordinate. -/
private def expansionExponent {d N : ℕ} (a : Fin N → Option (Fin d)) (j : Fin d) : ℕ :=
  ∑ i, if a i = some j then 1 else 0

private theorem expansion_monomial {d N : ℕ} (a : Fin N → Option (Fin d)) (x : Euclidean d) :
    (∏ i, (a i).elim 1 (fun j => |x j|)) = |coordinateMonomial (expansionExponent a) x| := by
  classical
  induction N with
  | zero => simp [coordinateMonomial, expansionExponent]
  | succ N ih =>
    rw [Fin.prod_univ_succ, ih]
    simp only [coordinateMonomial, Finset.abs_prod, abs_pow, expansionExponent, Fin.sum_univ_succ, pow_add, abs_mul, abs_pow]
    rw [Finset.prod_mul_distrib]
    congr 1
    cases a 0 with
    | none => simp
    | some j => simp [eq_comm]

private theorem norm_le_coordinate_abs_sum {d : ℕ} (x : Euclidean d) :
    ‖x‖ ≤ ∑ j : Fin d, |x j| := by
  calc
    ‖x‖ = ‖∑ j : Fin d, x j • coordinateVector j‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x).symm
    _ ≤ ∑ j : Fin d, ‖x j • coordinateVector j‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, norm_coordinateVector, Real.norm_eq_abs]

private abbrev ExpansionIndex (d N k : ℕ) :=
  (Fin N → Option (Fin d)) × (Σ n : Fin (k + 1), Fin n.val → Fin d)

private def expansionIndexMap {d N k : ℕ} (i : ExpansionIndex d N k) : MonomialIndex d :=
  (expansionExponent i.1, ⟨i.2.1.val, i.2.2⟩)

private def monomialControl (d N k : ℕ) : Finset (MonomialIndex d) :=
  Finset.univ.image (expansionIndexMap (d := d) (N := N) (k := k))

private theorem radialPoint_le_monomialControl {d : ℕ} (N k : ℕ) (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d) :
    radialPoint N β x ≤ ((d : ℝ≥0) + 1) ^ N •
      (monomialControl d N k).sup (monomialFamily d) := by
  classical
  intro f
  rw [radialPoint_apply]
  change (1 + ‖x‖) ^ N * ‖coordinatePartial β f x‖ ≤
    ((d : ℝ) + 1) ^ N * ((monomialControl d N k).sup (monomialFamily d)) f
  calc
    _ ≤ (∑ j : Option (Fin d), j.elim 1 (fun j => |x j|)) ^ N * ‖coordinatePartial β f x‖ := by
      gcongr
      simpa [Fintype.sum_option] using add_le_add_left (norm_le_coordinate_abs_sum x) 1
    _ = ∑ a : Fin N → Option (Fin d), monomialPoint (expansionExponent a) β x f := by
      rw [Fintype.sum_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [monomialPoint_apply, expansion_monomial]
    _ ≤ ∑ _a : Fin N → Option (Fin d),
        ((monomialControl d N k).sup (monomialFamily d)) f := by
      apply Finset.sum_le_sum
      intro a _
      apply (monomialPoint_le_monomialSeminorm (expansionExponent a) β x f).trans
      have hmem : expansionIndexMap (d := d) (N := N) (k := k) (a, ⟨n,β⟩) ∈
          monomialControl d N k :=
        Finset.mem_image.mpr ⟨(a, ⟨n, β⟩), Finset.mem_univ _, rfl⟩
      exact (Finset.le_sup (f := monomialFamily d) hmem) f
    _ = _ := by simp [Fintype.card_option]

private theorem manuscriptSeminorm_le_monomialControl {d : ℕ} (N k : ℕ) :
    manuscriptSeminorm (d := d) N k ≤ ((d : ℝ≥0) + 1) ^ N •
      (monomialControl d N k).sup (monomialFamily d) := by
  apply seminorm_iSup_le
  intro n
  apply seminorm_iSup_le
  intro β
  exact seminorm_iSup_le _ _ fun x => radialPoint_le_monomialControl N k n β x

 theorem monomial_withSeminorms (d : ℕ) : WithSeminorms (monomialFamily d) := by
  apply (manuscript_withSeminorms d).congr
  · rintro ⟨α,n,β⟩
    refine ⟨{(∑ j, α j, n)}, 1, ?_⟩
    simpa only [Finset.sup_singleton, one_smul, Seminorm.comp_id, monomialFamily,
      manuscriptFamily] using monomialSeminorm_le_manuscript α β
  · rintro ⟨N,k⟩
    exact ⟨monomialControl d N k, ((d : ℝ≥0) + 1) ^ N,
      manuscriptSeminorm_le_monomialControl N k⟩

 theorem fourier_zero_dimension (f : Test 0) : fourier 0 f = f := by
  ext x
  rw [fourier_integral]
  rw [volume_euclideanSpace_eq_dirac]
  simp only [integral_dirac, inner_zero_left, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul]
  exact congrArg f (Subsingleton.elim _ _)

 theorem check_zero_dimension (f : Test 0) : check 0 f = f := by
  ext x
  rw [check_integral]
  rw [volume_euclideanSpace_eq_dirac]
  simp only [integral_dirac, inner_zero_left, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul]
  exact congrArg f (Subsingleton.elim _ _)

/-- No conjugation appears in either variable of the test pairing. -/
 theorem test_pairing_bilinear {d : ℕ} (U V : Tempered d) (f g : Test d) (a b : ℂ) :
    (U + V) (f + g) = U f + U g + V f + V g ∧ (a • U) (b • f) = a * b * U f := by
  constructor
  · simp only [add_apply, map_add]
    ring
  · simp only [smul_apply, map_smul, smul_eq_mul]
    ring

 theorem weak_dual_pointwise {d : ℕ} {ι : Type*} (l : Filter ι)
    (U : ι → WeakTempered d) (V : WeakTempered d) :
    Filter.Tendsto U l (nhds V) ↔ ∀ f : Test d, Filter.Tendsto (fun i => U i f) l (nhds (V f)) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto

 theorem strong_dual_bounded_basis (d : ℕ) :
    (nhds (0 : Tempered d)).HasBasis
      (fun BV : Set (Test d) × Set ℂ => Bornology.IsVonNBounded ℂ BV.1 ∧ BV.2 ∈ nhds (0 : ℂ))
      (fun BV => {U : Tempered d | ∀ f ∈ BV.1, U f ∈ BV.2}) :=
  ContinuousLinearMap.hasBasis_nhds_zero

 theorem strong_to_weak_continuous (d : ℕ) :
    Continuous (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Test d) ℂ) :=
  (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Test d) ℂ).continuous

/-- Orthonormal changes of coordinates preserve volume and the inner product. -/
 theorem orthonormal_coordinates {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d) :
    MeasurePreserving A ∧ ∀ v w : V, inner ℝ (A v) (A w) = inner ℝ v w :=
  ⟨A.measurePreserving, A.inner_map_map⟩

 theorem orthonormal_fourier {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d) (f : Test d) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (fourier d f) := by
  ext v
  exact Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) v

 theorem orthonormal_check {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d) (f : Test d) :
    𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (check d f) := by
  ext v
  rw [SchwartzMap.fourierInv_coe]
  change 𝓕⁻ ((f : Euclidean d → ℂ) ∘ A) v = check d f (A v)
  rw [Real.fourierInv_comp_linearIsometry]
  exact congrFun (SchwartzMap.fourierInv_coe f).symm (A v)

 theorem coordinatePartial_permutation {d n : ℕ} (β : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (f : Test d) :
    coordinatePartial (β ∘ σ) f = coordinatePartial β f := by
  apply (FourierTransform.fourierCLE ℂ (Test d)).injective
  change fourier d (coordinatePartial (β ∘ σ) f) = fourier d (coordinatePartial β f)
  rw [fourier_partial, fourier_partial]
  ext x
  simp only [polynomialMul_apply, Function.comp_apply]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

 theorem manuscriptSeminorm_apply {d : ℕ} (N k : ℕ) (f : Test d) :
    manuscriptSeminorm N k f = ⨆ (n : Fin (k + 1)) (β : Fin n.val → Fin d) (x : Euclidean d),
      (1 + ‖x‖) ^ N * ‖coordinatePartial β f x‖ := by
  let q := (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)
  have h (n : Fin (k+1)) (β : Fin n.val → Fin d) (x : Euclidean d) :
      radialPoint N β x ≤ q := radialPoint_le_native N n β x
  unfold manuscriptSeminorm
  rw [Seminorm.iSup_apply ⟨q, by
    rintro _ ⟨n,rfl⟩
    exact seminorm_iSup_le _ _ (fun β => seminorm_iSup_le _ _ (h n β))⟩]
  congr 1
  funext n
  rw [Seminorm.iSup_apply ⟨q, by
    rintro _ ⟨β,rfl⟩
    exact seminorm_iSup_le _ _ (h n β)⟩]
  congr 1
  funext β
  rw [Seminorm.iSup_apply ⟨q, by rintro _ ⟨x,rfl⟩; exact h n β x⟩]
  simp only [radialPoint_apply]

 theorem monomialSeminorm_apply {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d) (f : Test d) :
    monomialSeminorm α β f = ⨆ x : Euclidean d,
      |coordinateMonomial α x| * ‖coordinatePartial β f x‖ := by
  unfold monomialSeminorm
  rw [Seminorm.iSup_apply ⟨manuscriptSeminorm (∑ j, α j) n, by
    rintro _ ⟨x,rfl⟩
    exact (monomialPoint_le_radialPoint α β x).trans
      (radialPoint_le_manuscript _ n ⟨n, Nat.lt_succ_self n⟩ β x)⟩]
  simp only [monomialPoint_apply]

 theorem test_integrable {d : ℕ} (f : Test d) :
    Integrable (f : Euclidean d → ℂ) ∧ Integrable (fourier d f : Euclidean d → ℂ) ∧
      Integrable (check d f : Euclidean d → ℂ) :=
  ⟨f.integrable, (fourier d f).integrable, (check d f).integrable⟩

end P102.U3
