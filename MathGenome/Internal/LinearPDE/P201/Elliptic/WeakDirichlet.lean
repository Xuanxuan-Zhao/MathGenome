import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeakDirichlet
import Mathlib.MeasureTheory.Function.Holder
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201.Common.ExactTrace
import MathGenome.Internal.FourierSobolev.P102.U4.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.LaxMilgram
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace P201.Dirichlet
open P201Specs.Dirichlet
open P102.U4.SlabPoincareData P102.U4.SlabPoincareProof

/-- The accepted full-H¹ closure is exactly the library W₀ closure. -/
def zeroToW {n : ℕ} (Ω : Domain n) : H10 ℝ Ω →ₗ[ℝ] P102.U4.SobolevZero ℝ Ω 1 2 where
  toFun u := ⟨hToW ℝ Ω 1 u.val, by
    exact (hZeroClosureBridge ℝ Ω).le u.property⟩
  map_add' u v := by apply Subtype.ext; exact map_add (hToW ℝ Ω 1) _ _
  map_smul' c u := by apply Subtype.ext; exact map_smul (hToW ℝ Ω 1) _ _

/-- No gradient is replaced by a formal symbol: these L² classes coincide. -/
theorem gradient_toW {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    sobolevGradient (hToW ℝ Ω 1 u) = hGradient u := rfl

/-- Continuous gradient for the full norm, obtained by preserving all coordinates. -/
def gradientCLM {n : ℕ} (Ω : Domain n) :
    H ℝ Ω 1 →L[ℝ] MeasureTheory.Lp (Space n) 2 (domainMeasure Ω) :=
  (sobolevGradientCLM (𝕜 := ℝ) (Ω := Ω) (p := 2)).comp
    (hToW ℝ Ω 1).toContinuousLinearMap

@[simp] theorem gradientCLM_apply {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    gradientCLM Ω u = hGradient u := by
  exact sobolevGradientCLM_apply _

/-- Norm transfer from the sum-norm W¹,² to the actual full Hilbert norm. -/
theorem full_norm_le_sum_norm {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    ‖u‖ ≤ ‖(hToW ℝ Ω 1).symm.toContinuousLinearMap‖ * ‖hToW ℝ Ω 1 u‖ := by
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
    (hToW ℝ Ω 1).symm.toContinuousLinearMap.le_opNorm (hToW ℝ Ω 1 u)

/-- The slab inequality, transported through the actual closure interface.
The imported slab theorem proves its estimate by zero extension of tests. -/
theorem full_norm_le_gradient_in_slab {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (e : Space n) (a b : ℝ) (he : ‖e‖ = 1) (hab : a < b)
    (hs : InSlab Ω e a b) (u : H10 ℝ Ω) :
    ‖u‖ ≤ (‖(hToW ℝ Ω 1).symm.toContinuousLinearMap‖ * (b - a + (n : ℝ))) *
      ‖hGradient u.val‖ := by
  have h := (P102.U4.slab_norm_equivalence hn Ω 2 (by norm_num) e a b he hab hs (zeroToW Ω u)).2
  change ‖hToW ℝ Ω 1 u.val‖ ≤ (b - a + (n : ℝ)) * ‖hGradient u.val‖ at h
  exact (full_norm_le_sum_norm Ω u.val).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
      (norm_nonneg (hToW ℝ Ω 1).symm.toContinuousLinearMap))

/-- A bounded open set fits in a slab in a fixed Euclidean unit direction. -/
theorem bounded_in_slab {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) :
    ∃ (e : Space n) (a b : ℝ), ‖e‖ = 1 ∧ a < b ∧ InSlab Ω e a b := by
  obtain ⟨R, hR, hball⟩ := hΩ.subset_ball_lt 0 (0 : Space n)
  let e : Space n := EuclideanSpace.basisFun (Fin n) ℝ ⟨0, hn⟩
  have he : ‖e‖ = 1 := by simp [e]
  refine ⟨e, -R, R, he, by linarith, fun x hx => ?_⟩
  have hxR : ‖x‖ < R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hball hx
  have hxe : |inner ℝ x e| < R := by
    exact (abs_real_inner_le_norm x e).trans_lt (by simpa [he] using hxR)
  exact abs_lt.mp hxe

/-- Positive norm-equivalence constant depending only on Ω and its dimension. -/
theorem full_norm_le_gradient {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H10 ℝ Ω, ‖u‖ ≤ C * ‖hGradient u.val‖ := by
  obtain ⟨e, a, b, he, hab, hs⟩ := bounded_in_slab hn Ω hΩ
  let K := ‖(hToW ℝ Ω 1).symm.toContinuousLinearMap‖ * (b - a + (n : ℝ))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun u => ?_⟩
  exact (full_norm_le_gradient_in_slab hn Ω e a b he hab hs u).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 K) (norm_nonneg _))

/-- Each weak derivative is a continuous coordinate projection in the full norm. -/
def derivativeCLM {n : ℕ} (Ω : Domain n) (j : Fin n) :
    H ℝ Ω 1 →L[ℝ] P201.Lp ℝ Ω 2 :=
  (PiLp.proj 2 _ ⟨{j}, by simp⟩).comp (P201Specs.hilbertSubmodule ℝ Ω 1).subtypeL

@[simp] theorem derivativeCLM_apply {n : ℕ} (Ω : Domain n) (j : Fin n)
    (u : H ℝ Ω 1) : derivativeCLM Ω j u = hFirstDerivative u j := rfl

theorem derivative_norm_le {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (j : Fin n) :
    ‖hFirstDerivative u j‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u.val ⟨{j}, by simp⟩

/-- Continuous coordinate evaluation in the standard finite product topology. -/
def entryCLM {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) i)

/-- The coefficient's L∞ coordinate, retaining its actual a.e. representative. -/
def entryLp {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) :
    P201.Lp ℝ Ω ∞ := (entryCLM i j).compLp (hA.toLp A)

theorem entryLp_ae {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) :
    (entryLp Ω A hA i j : Space n → ℝ) =ᵐ[domainMeasure Ω] fun x => A x i j := by
  filter_upwards [(entryCLM i j).coeFn_compLp (hA.toLp A), hA.coeFn_toLp] with x hx hy
  exact hx.trans (congrArg (fun M => M i j) hy)

/-- Each matrix entry is bounded by the Euclidean operator norm. -/
theorem matrix_entry_le_operator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ‖M i j‖ ≤ ‖matrixOperator M‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ j
  have he : ‖e‖ = 1 := by simp [e]
  have hij : (matrixOperator M e) i = M i j := by
    simp [matrixOperator, e, Matrix.toEuclideanLin, Matrix.toLpLin,
      EuclideanSpace.basisFun_apply]
  calc
    ‖M i j‖ = ‖(matrixOperator M e) i‖ := congrArg norm hij.symm
    _ ≤ ‖matrixOperator M e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖matrixOperator M‖ * ‖e‖ := (matrixOperator M).le_opNorm e
    _ = _ := by rw [he, mul_one]

theorem entryLp_norm_le {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) :
    ‖entryLp Ω A hA i j‖ ≤ CoefficientNorm Ω A := by
  have hop : MemLp (fun x => matrixOperator (A x)) ∞ (domainMeasure Ω) :=
    matrixOperator.comp_memLp' hA
  calc
    _ ≤ ‖hop.toLp (fun x => matrixOperator (A x))‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [entryLp_ae Ω A hA i j, hop.coeFn_toLp] with x hx hy
      rw [hx, hy]
      exact matrix_entry_le_operator (A x) i j
    _ = _ := Lp.norm_toLp _ hop

/-- Multiplication by one coefficient from L∞ to L². -/
def weightedDerivative {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) :
    H ℝ Ω 1 →L[ℝ] P201.Lp ℝ Ω 2 :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure Ω) ∞ 2 2
    (entryLp Ω A hA i j)).comp (derivativeCLM Ω j)

theorem weightedDerivative_ae {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) (u : H ℝ Ω 1) :
    (weightedDerivative Ω A hA i j u : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => A x i j * hFirstDerivative u j x := by
  exact ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (entryLp Ω A hA i j) (hFirstDerivative u j)).trans
      ((entryLp_ae Ω A hA i j).mul Filter.EventuallyEq.rfl)

/-- The matrix integral as a genuine bounded bilinear form on H¹. -/
def form {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) :
    H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (innerSL ℝ).bilinearComp (weightedDerivative Ω A hA i j) (derivativeCLM Ω i)

theorem summand_integrable {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) (i j : Fin n) :
    Integrable (fun x => A x i j * hFirstDerivative u j x * hFirstDerivative v i x)
      (domainMeasure Ω) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (weightedDerivative Ω A hA i j u)
    (hFirstDerivative v i)).congr
  filter_upwards [weightedDerivative_ae Ω A hA i j u] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem integrand_integrable {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    Integrable (fun x => ∑ i, ∑ j, A x i j * hFirstDerivative u j x * hFirstDerivative v i x)
      (domainMeasure Ω) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => summand_integrable Ω A hA u v i j))

/-- The bundled form is exactly the manuscript's matrix-coefficient integral. -/
theorem form_apply {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    form Ω A hA u v = ellipticEnergyForm Ω A u v := by
  simp only [form, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    derivativeCLM_apply]
  change (∑ i, ∑ j, inner ℝ (weightedDerivative Ω A hA i j u) (hFirstDerivative v i)) =
    ∫ x, ∑ i, ∑ j, A x i j * hFirstDerivative u j x * star (hFirstDerivative v i x) ∂domainMeasure Ω
  simp only [star_trivial]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => summand_integrable Ω A hA u v i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => summand_integrable Ω A hA u v i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedDerivative_ae Ω A hA i j u] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem weightedDerivative_norm_le {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (i j : Fin n) (u : H ℝ Ω 1) :
    ‖weightedDerivative Ω A hA i j u‖ ≤ CoefficientNorm Ω A * ‖u‖ := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le
    (r := 2) (entryLp Ω A hA i j) (hFirstDerivative u j)
  have hm := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  change ‖weightedDerivative Ω A hA i j u‖ ≤ _ at h
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖entryLp Ω A hA i j‖ * ‖hFirstDerivative u j‖ := h
    _ ≤ 1 * CoefficientNorm Ω A * ‖u‖ := by
      apply mul_le_mul
      · exact mul_le_mul hm (entryLp_norm_le Ω A hA i j)
          (norm_nonneg _) zero_le_one
      · exact derivative_norm_le Ω u j
      · exact norm_nonneg _
      · exact mul_nonneg zero_le_one ENNReal.toReal_nonneg
    _ = _ := by ring

theorem form_bound {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (u v : H ℝ Ω 1) :
    ‖form Ω A hA u v‖ ≤ (n : ℝ) ^ 2 * CoefficientNorm Ω A * ‖u‖ * ‖v‖ := by
  simp only [form, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    derivativeCLM_apply]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖inner ℝ (weightedDerivative Ω A hA i j u) (hFirstDerivative v i)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, CoefficientNorm Ω A * ‖u‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_inner_le_norm _ _).trans (mul_le_mul
        (weightedDerivative_norm_le Ω A hA i j u) (derivative_norm_le Ω v i)
        (norm_nonneg _) (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)))
    _ = _ := by simp; ring

/-- The bundled gradient has the expected weak coordinate representative. -/
theorem gradient_ae {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    (hGradient u : Space n → Space n) =ᵐ[domainMeasure Ω]
      fun x => WithLp.toLp 2 (fun j => hFirstDerivative u j x) :=
  MemLp.coeFn_toLp _

/-- Pointwise ellipticity yields the coercivity integral on actual Sobolev classes. -/
theorem form_gradient_coercive {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (lam : ℝ) (hEll : Elliptic Ω A lam)
    (u : H ℝ Ω 1) : lam * ‖hGradient u‖ ^ 2 ≤ form Ω A hA u u := by
  have hg : Integrable (fun x => ‖hGradient u x‖ ^ 2) (domainMeasure Ω) := by
    simpa only [real_inner_self_eq_norm_sq] using
      L2.integrable_inner (𝕜 := ℝ) (hGradient u) (hGradient u)
  have heq : (∫ x, ‖hGradient u x‖ ^ 2 ∂domainMeasure Ω) = ‖hGradient u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [form_apply]
  change _ ≤ ∫ x, ∑ i, ∑ j,
    A x i j * hFirstDerivative u j x * star (hFirstDerivative u i x) ∂domainMeasure Ω
  simp only [star_trivial]
  rw [← heq, ← integral_const_mul]
  apply integral_mono_ae (hg.const_mul _) (integrand_integrable Ω A hA u u)
  filter_upwards [hEll, gradient_ae Ω u] with x hx hxu
  simpa only [hxu, PiLp.toLp_apply] using hx (hGradient u x)

/-- The entire concrete bridge has constants fixed before choosing A or lam. -/
theorem form_bridge : P201Specs.Dirichlet.FormBridgeStatement := by
  intro n hn Ω hΩ
  obtain ⟨K, hK, hbound⟩ := full_norm_le_gradient hn Ω hΩ
  let C : ℝ := max K ((n : ℝ) ^ 2 + 1)
  have hKC : K ≤ C := le_max_left _ _
  have hnC : (n : ℝ) ^ 2 ≤ C := (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le hK hKC
  have hnorm (u : H10 ℝ Ω) : ‖u‖ ≤ C * ‖hGradient u.val‖ :=
    (hbound u).trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _))
  refine ⟨C, hC, hnorm, fun A hA => ⟨form Ω A hA, form_apply Ω A hA, ?_, ?_⟩⟩
  · intro u v
    exact (form_bound Ω A hA u v).trans (by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      exact mul_le_mul_of_nonneg_right hnC ENNReal.toReal_nonneg)
  · intro lam hlam hEll u
    have hn2 : ‖u‖ ^ 2 ≤ C ^ 2 * ‖hGradient u.val‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg u) (hnorm u) 2
    calc
      _ ≤ (lam / C ^ 2) * (C ^ 2 * ‖hGradient u.val‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ = lam * ‖hGradient u.val‖ ^ 2 := by field_simp
      _ ≤ _ := form_gradient_coercive Ω A hA lam hEll u.val

/-- Nonsymmetric Lax–Milgram on the actual closed Hilbert subspace, with the
norm-conversion constant kept visible. -/
theorem solve_zero_form {n : ℕ} (Ω : Domain n)
    (B : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ)
    (C lam : ℝ) (hC : 0 < C) (hlam : 0 < lam)
    (hc : ∀ u : H10 ℝ Ω, (lam / C ^ 2) * ‖u‖ ^ 2 ≤ B u.val u.val)
    (f : Hminus1 ℝ Ω) :
    ∃ u : H10 ℝ Ω, (∀ v : H10 ℝ Ω, B u.val v.val = f v) ∧
      ‖u‖ ≤ C ^ 2 * lam⁻¹ * ‖f‖ ∧
      ∀ w : H10 ℝ Ω, (∀ v : H10 ℝ Ω, B w.val v.val = f v) → w = u := by
  let a₀ := B.bilinearComp (zeroInclusion Ω) (zeroInclusion Ω)
  let a : H10 ℝ Ω →L⋆[ℝ] H10 ℝ Ω →L[ℝ] ℝ :=
    { toFun := a₀
      map_add' := a₀.map_add
      map_smul' := by intro c u; simp
      cont := a₀.continuous }

  have hpos : 0 < lam / C ^ 2 := by positivity
  obtain ⟨u, hu, hnorm, huniq, _⟩ :=
    VariationalNotes.Existence.laxMilgram ℝ (H10 ℝ Ω) a (lam / C ^ 2) hpos (fun u => hc u) f
  refine ⟨u, hu, hnorm.trans_eq ?_, huniq⟩
  field_simp

theorem homogeneous : P201Specs.Dirichlet.HomogeneousStatement := by
  intro n hn Ω hΩ
  obtain ⟨C, hC, _, hform⟩ := form_bridge hn Ω hΩ
  refine ⟨C ^ 2, by positivity, fun A hA lam hlam hEll f => ?_⟩
  obtain ⟨B, hB, _, hc⟩ := hform A hA
  obtain ⟨u, hu, hnorm, huniq⟩ := solve_zero_form Ω B C lam hC hlam (hc lam hlam hEll) f
  exact ⟨u, fun v => (hB _ _).symm.trans (hu v), hnorm,
    fun w hw => huniq w (fun v => (hB _ _).trans (hw v))⟩

/-- A source in H⁻¹ can be shifted by an H¹ lift because only its tests
belong to H₀¹. -/
def shiftedLoad {n : ℕ} (Ω : Domain n)
    (B : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) : Hminus1 ℝ Ω :=
  f - (B w).comp (zeroInclusion Ω)

theorem shiftedLoad_bound {n : ℕ} (Ω : Domain n)
    (B : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ u v, ‖B u v‖ ≤ M * ‖u‖ * ‖v‖)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) :
    ‖shiftedLoad Ω B f w‖ ≤ ‖f‖ + M * ‖w‖ := by
  have hbw : ‖(B w).comp (zeroInclusion Ω)‖ ≤ M * ‖w‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg _))
    intro v
    exact hB w v.val
  exact (norm_sub_le f ((B w).comp (zeroInclusion Ω))).trans (add_le_add_right hbw _)

/-- Abstract affine step, with its explicit bound and uniqueness. -/
theorem solve_affine_form {n : ℕ} (Ω : Domain n)
    (B : H ℝ Ω 1 →L[ℝ] H ℝ Ω 1 →L[ℝ] ℝ)
    (C lam M : ℝ) (hC : 0 < C) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hB : ∀ u v, ‖B u v‖ ≤ M * ‖u‖ * ‖v‖)
    (hc : ∀ u : H10 ℝ Ω, (lam / C ^ 2) * ‖u‖ ^ 2 ≤ B u.val u.val)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) :
    ∃ z : H10 ℝ Ω,
      (∀ v : H10 ℝ Ω, B (w + z.val) v.val = f v) ∧
      ‖w + z.val‖ ≤ ‖w‖ + C ^ 2 * lam⁻¹ * (‖f‖ + M * ‖w‖) ∧
      ∀ y : H10 ℝ Ω, (∀ v : H10 ℝ Ω, B (w + y.val) v.val = f v) → y = z := by
  obtain ⟨z, hz, hznorm, huniq⟩ := solve_zero_form Ω B C lam hC hlam hc (shiftedLoad Ω B f w)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro v
    have h := hz v
    change B z.val v.val = f v - B w v.val at h
    simp only [map_add, add_apply, h, add_sub_cancel]
  · exact (norm_add_le _ _).trans (add_le_add_right
      (hznorm.trans (mul_le_mul_of_nonneg_left (shiftedLoad_bound Ω B M hM hB f w)
        (by positivity))) _)
  · intro y hy
    apply huniq y
    intro v
    change B y.val v.val = f v - B w v.val
    have h := hy v
    simp only [map_add, add_apply] at h
    linarith

/-- The boundedness built into the accepted Lipschitz geometry is transported
back through its fixed Euclidean isometry. -/
theorem lipschitz_isBounded {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) : Bornology.IsBounded (Ω : Set (Space (m + 1))) := by
  have h := (graphFrame m).lipschitzWith.isBounded_image hΩ.2.1
  change Bornology.IsBounded ((graphFrame m) '' ((graphFrame m) ⁻¹' (Ω : Set (Space (m + 1))))) at h
  rwa [Set.image_preimage_eq _ (graphFrame m).surjective] at h

/-- A trace difference is a member of the actual closed test subspace. -/
theorem trace_difference_mem {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] P201.Hhalf Ω hΩ)
    (hker : T.ker = P201Specs.hZeroSubmodule ℝ Ω)
    (u w : H ℝ Ω 1) (huw : T u = T w) : u - w ∈ P201Specs.hZeroSubmodule ℝ Ω := by
  rw [← hker]
  change T (u - w) = 0
  rw [map_sub, huw, sub_self]

/-- Scalar estimate used for the lifting bound. The resulting constant depends
only on the domain's form constant and the norm of its fixed lifting. -/
theorem lifting_bound (C L p q g w U : ℝ) (hC : 0 < C) (hL : 0 ≤ L)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hg : 0 ≤ g)
    (hw : w ≤ L * g)
    (hU : U ≤ w + C ^ 2 * (p + C * q * w)) :
    U ≤ ((1 + C ^ 2 + C ^ 3) * (1 + L)) * (p + (1 + q) * g) := by
  let D := (1 + C ^ 2 + C ^ 3) * (1 + L)
  have hD1 : L ≤ D := by dsimp [D]; nlinarith [sq_nonneg C, pow_pos hC 3]
  have hD2 : C ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg C) hL,
      mul_nonneg (le_of_lt (pow_pos hC 3)) hL, pow_pos hC 3]
  have hD3 : C ^ 3 * L ≤ D := by dsimp [D]; nlinarith [mul_nonneg (sq_nonneg C) hL, pow_pos hC 3]
  have hb : (1 + C ^ 3 * q) * L ≤ D * (1 + q) := by
    nlinarith [mul_le_mul_of_nonneg_right hD3 hq]
  calc
    U ≤ C ^ 2 * p + (1 + C ^ 3 * q) * w := by nlinarith [hU]
    _ ≤ C ^ 2 * p + (1 + C ^ 3 * q) * (L * g) := by
      gcongr
    _ = C ^ 2 * p + ((1 + C ^ 3 * q) * L) * g := by ring
    _ ≤ D * p + (D * (1 + q)) * g := add_le_add
      (mul_le_mul_of_nonneg_right hD2 hp) (mul_le_mul_of_nonneg_right hb hg)
    _ = _ := by dsimp [D]; ring

/-- The full trace-prescribed theorem, including the endpoint case inherited
from the accepted exact trace result. -/
theorem nonhomogeneous : P201Specs.Dirichlet.NonhomogeneousStatement := by
  intro m Ω hΩ
  obtain ⟨T, L, hsm, _, hright, hker⟩ := P201.Trace.exact_trace m Ω hΩ
  obtain ⟨C, hC, _, hform⟩ := form_bridge (by omega : 1 ≤ m + 1) Ω (lipschitz_isBounded Ω hΩ)
  refine ⟨T, L, (1 + C ^ 2 + C ^ 3) * (1 + ‖L‖), hsm, hright, hker, by positivity,
    fun A hA lam hlam hEll f g => ?_⟩
  obtain ⟨B, hB, hb, hc⟩ := hform A hA
  have hM : 0 ≤ C * CoefficientNorm Ω A := mul_nonneg hC.le ENNReal.toReal_nonneg
  have hb' : ∀ u v, ‖B u v‖ ≤ (C * CoefficientNorm Ω A) * ‖u‖ * ‖v‖ := hb
  obtain ⟨z, hz, hnorm, huniq⟩ := solve_affine_form Ω B C lam (C * CoefficientNorm Ω A)
    hC hlam hM hb' (hc lam hlam hEll) f (L g)
  have hz0 : T z.val = 0 := hker.symm.le z.property
  have htrace : T (L g + z.val) = g := by simp [hz0, hright]
  refine ⟨L g + z.val, ⟨htrace, fun v => (hB _ _).symm.trans (hz v)⟩, ?_, ?_⟩
  · apply lifting_bound C ‖L‖ (lam⁻¹ * ‖f‖) (lam⁻¹ * CoefficientNorm Ω A)
      ‖g‖ ‖L g‖ ‖L g + z.val‖ hC (by positivity) (by positivity)
      (by exact mul_nonneg (inv_nonneg.mpr hlam.le) ENNReal.toReal_nonneg)
      (norm_nonneg _) (L.le_opNorm g)
    convert hnorm using 1; ring
  · intro v hv
    let y : H10 ℝ Ω := ⟨v - L g, trace_difference_mem Ω hΩ T hker v (L g)
      (hv.1.trans (hright g).symm)⟩
    have hy : L g + y.val = v := by dsimp [y]; abel
    have hyz : y = z := huniq y (by
      intro t
      rw [hy]
      exact (hB _ _).trans (hv.2 t))
    calc
      v = L g + y.val := hy.symm
      _ = L g + z.val := congrArg (fun a : H10 ℝ Ω => L g + a.val) hyz

/-- Symmetric coefficients give a symmetric form; no symmetry has been used
in either solvability theorem. -/
theorem form_symmetric {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (hsym : Symmetric Ω A)
    (u v : H ℝ Ω 1) : form Ω A hA u v = form Ω A hA v u := by
  rw [form_apply, form_apply]
  apply integral_congr_ae
  filter_upwards [hsym] with x hx
  simp only [star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hx j i]
  ring

/-- A change of lift adds precisely the constant f(q). -/
theorem affine_energy_change_lift {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) (q z : H10 ℝ Ω) :
    AffineEnergy Ω A f (w + q.val) (z - q) = AffineEnergy Ω A f w z + f q := by
  have he : w + q.val + (z - q).val = w + z.val := by simp
  have hf : f (z - q) = f z - f q := f.map_sub z q
  unfold AffineEnergy
  rw [he, hf]
  ring

/-- Exact increment in the affine functional, proved by bilinear expansion. -/
theorem affine_energy_increment {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (hA : MemLp A ∞ (domainMeasure Ω)) (hsym : Symmetric Ω A)
    (f : Hminus1 ℝ Ω) (w : H ℝ Ω 1) (z : H10 ℝ Ω)
    (hz : Solves Ω A f (w + z.val)) (v : H10 ℝ Ω) :
    AffineEnergy Ω A f w (z + v) - AffineEnergy Ω A f w z =
      (1 / 2 : ℝ) * ellipticEnergyForm Ω A v.val v.val := by
  have hadd : w + (z + v).val = (w + z.val) + v.val := by simp; abel
  simp only [AffineEnergy, hadd, map_add, ← form_apply Ω A hA]
  have hsol : form Ω A hA (w + z.val) v.val = f v := (form_apply _ _ _ _ _).trans (hz v)
  have hsym' := form_symmetric Ω A hA hsym v.val (w + z.val)
  simp only [map_add, add_apply] at hsol hsym' ⊢
  linarith

/-- Unique affine energy minimizer, retaining the source's full H⁻¹ data. -/
theorem symmetric_energy : P201Specs.Dirichlet.SymmetricEnergyStatement := by
  intro n hn Ω hΩ A hA lam hlam hEll hsym f w
  refine ⟨affine_energy_change_lift Ω A f w, ?_⟩
  obtain ⟨C, hC, _, hform⟩ := form_bridge hn Ω hΩ
  obtain ⟨B, hB, hb, hc⟩ := hform A hA
  obtain ⟨z, hz, _, _⟩ := solve_affine_form Ω B C lam (C * CoefficientNorm Ω A)
    hC hlam (mul_nonneg hC.le ENNReal.toReal_nonneg) hb (hc lam hlam hEll) f w
  have hsol : Solves Ω A f (w + z.val) := fun v => (hB _ _).symm.trans (hz v)
  have hinc := affine_energy_increment Ω A hA hsym f w z hsol
  have hnonneg (v : H10 ℝ Ω) : 0 ≤ ellipticEnergyForm Ω A v.val v.val := by
    exact ((mul_nonneg (by positivity : 0 ≤ lam / C ^ 2) (sq_nonneg ‖v‖)).trans
      (hc lam hlam hEll v)).trans_eq (hB v.val v.val)
  have hmin (y : H10 ℝ Ω) : AffineEnergy Ω A f w z ≤ AffineEnergy Ω A f w y := by
    have h := hinc (y - z)
    have hyz : z + (y - z) = y := by abel
    rw [hyz] at h
    linarith [hnonneg (y - z)]
  refine ⟨z, hsol, hinc, hmin, ?_⟩
  intro y hy
  have h := hinc (y - z)
  have hyz : z + (y - z) = y := by abel
  rw [hyz] at h
  have hupper := hy z
  have hco := hc lam hlam hEll (y - z)
  have hco' : (lam / C ^ 2) * ‖y - z‖ ^ 2 ≤
      ellipticEnergyForm Ω A (y - z).val (y - z).val := hco.trans_eq (hB _ _)
  have hp : 0 < lam / C ^ 2 := by positivity
  have hsq : ‖y - z‖ ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right (hco'.trans (show ellipticEnergyForm Ω A (y - z).val (y - z).val ≤ 0 by linarith)) hp
  have hnzero : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)

end P201.Dirichlet
