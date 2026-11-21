import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.FourierFourPointSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace FourierTransform SchwartzMap
namespace ExpandedFA.Models.FourierFourPointSpectrum
open ExpandedFA.Fourier

lemma fourier_apply (f : H) : fourier f = l2Fourier 1 f := rfl

lemma root_pow_four (j : Fin 4) : root j ^ 4 = 1 := by
  fin_cases j <;> norm_num [root, Complex.I_sq, pow_succ]

lemma root_ne_zero (j : Fin 4) : root j ≠ 0 := by
  have := root_pow_four j
  intro h
  simp [h] at this

lemma roots_distinct : Function.Injective root := by
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first | rfl | norm_num [root, Complex.ext_iff] at h

lemma schwartz_fourth (φ : Schwartz ℂ 1) :
    schwartzFourier (schwartzFourier (schwartzFourier (schwartzFourier φ))) = φ := by
  ext x
  rw [Inversion.fourier_square, Inversion.fourier_square, neg_neg]

theorem fourth_power : Spec.FourthPower := by
  change fourier ^ 4 = 1
  apply DFunLike.coe_injective
  apply (SchwartzMap.denseRange_toLpCLM (E := Euclidean 1)
    (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).equalizer
    (fourier ^ 4).continuous (1 : H →L[ℂ] H).continuous
  funext φ
  change fourier (fourier (fourier (fourier (φ.toLp 2)))) = φ.toLp 2
  change 𝓕 (𝓕 (𝓕 (𝓕 (φ.toLp 2)))) = φ.toLp 2
  simp only [SchwartzMap.toLp_fourier_eq]
  exact congrArg (fun ψ : Schwartz ℂ 1 => ψ.toLp 2) (schwartz_fourth φ)

lemma projection_expansion (j : Fin 4) :
    projection j = (1 / 4 : ℂ) • (1 + (root j)⁻¹ • fourier +
      (root j)⁻¹ ^ 2 • fourier ^ 2 + (root j)⁻¹ ^ 3 • fourier ^ 3) := by
  simp [projection, Finset.sum_range_succ, add_assoc]

lemma fourier_projection (j : Fin 4) :
    fourier * projection j = root j • projection j := by
  apply ContinuousLinearMap.ext
  intro x
  have h2 : fourier (fourier x) = (fourier ^ 2) x := rfl
  have h3 : fourier ((fourier ^ 2) x) = (fourier ^ 3) x := rfl
  have h4 : fourier ((fourier ^ 3) x) = x := by
    change (fourier ^ 4) x = x
    rw [fourth_power]; rfl
  simp only [mul_apply_eq_comp, smul_apply, projection_expansion, add_apply,
    one_apply_eq_self, map_smul, map_add, h2, h3, h4, smul_smul]
  fin_cases j <;> norm_num [root, Complex.inv_I, pow_succ] <;>
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma sum_projections : (∑ j : Fin 4, projection j) = 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp [projection_expansion, root, Complex.inv_I, pow_succ]
  module

lemma projection_on_eigenvector (j k : Fin 4) (x : H)
    (hx : fourier x = root k • x) :
    projection j x = if j = k then x else 0 := by
  have hpow (n : ℕ) : (fourier ^ n) x = root k ^ n • x := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ', ih, hx, smul_smul, mul_comm]
  rw [projection_expansion]
  simp only [smul_apply, add_apply,
    one_apply_eq_self, hpow, hx, smul_smul]
  fin_cases j <;> fin_cases k <;>
    norm_num [root, Complex.inv_I, Complex.I_sq, pow_succ] <;> module

lemma projection_mem (j : Fin 4) (x : H) : projection j x ∈ eigenspace j := by
  apply Module.End.mem_eigenspace_iff.mpr
  exact congrArg (fun T : H →L[ℂ] H => T x) (fourier_projection j)

lemma projection_product (j k : Fin 4) :
    projection j * projection k = if j = k then projection k else 0 := by
  apply ContinuousLinearMap.ext
  intro x
  by_cases h : j = k <;>
    simpa [h] using projection_on_eigenvector j k _
      (Module.End.mem_eigenspace_iff.mp (projection_mem k x))

lemma eigenvectors_orthogonal (j k : Fin 4) (hjk : j ≠ k)
    (x : H) (hx : x ∈ eigenspace j) (y : H) (hy : y ∈ eigenspace k) :
    inner ℂ x y = 0 := by
  have hu := (l2Fourier 1).inner_map_map x y
  change inner ℂ (fourier x) (fourier y) = inner ℂ x y at hu
  have hx' : fourier x = root j • x := Module.End.mem_eigenspace_iff.mp hx
  have hy' : fourier y = root k • y := Module.End.mem_eigenspace_iff.mp hy
  rw [hx', hy', inner_smul_left, inner_smul_right] at hu
  have hc : star (root j) * root k - 1 ≠ 0 := by
    fin_cases j <;> fin_cases k <;>
      first | exact False.elim (hjk rfl) | norm_num [root, Complex.ext_iff]
  apply (mul_eq_zero.mp (show (star (root j) * root k - 1) * inner ℂ x y = 0 by
    simpa only [starRingEnd_apply] using (show
      ((starRingEnd ℂ) (root j) * root k - 1) * inner ℂ x y = 0 by linear_combination hu))).resolve_left hc

lemma sum_projection_apply (x : H) : (∑ j : Fin 4, projection j x) = x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) sum_projections
  simpa using h

lemma projection_inner (j : Fin 4) (x y : H) :
    inner ℂ (projection j x) y = inner ℂ (projection j x) (projection j y) := by
  conv_lhs => rw [← sum_projection_apply y, inner_sum]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    exact eigenvectors_orthogonal j k (Ne.symm hkj) _ (projection_mem j x) _
      (projection_mem k y)
  · simp

lemma projection_selfAdjoint (j : Fin 4) : IsSelfAdjoint (projection j) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (projection j x) y = inner ℂ x (projection j y)
  calc
    _ = inner ℂ (projection j x) (projection j y) := projection_inner j x y
    _ = star (inner ℂ (projection j y) (projection j x)) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ (projection j y) x) := congrArg star (projection_inner j y x).symm
    _ = _ := inner_conj_symm _ _

lemma projection_range (j : Fin 4) :
    LinearMap.range (projection j).toLinearMap = eigenspace j := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact projection_mem j x
  · intro x hx
    refine ⟨x, ?_⟩
    simpa using (projection_on_eigenvector j j x (Module.End.mem_eigenspace_iff.mp hx))

theorem projection_identities : Spec.ProjectionIdentities := by
  refine ⟨sum_projections, fourier_projection, ?_, ?_, projection_selfAdjoint,
    projection_range⟩
  · intro j
    simp [projection_product]
  · intro j k hjk
    simp [projection_product, hjk]

theorem orthogonal_decomposition : Spec.OrthogonalDecomposition := by
  refine ⟨?_, eigenvectors_orthogonal, ?_⟩
  · intro j
    exact ContinuousLinearMap.isClosed_eigenspace fourier (root j)
  · intro f
    refine ⟨fun j => projection_mem j f, sum_projection_apply f, ?_⟩
    intro v hv hsum j
    rw [← hsum, map_sum]
    symm
    rw [Finset.sum_eq_single j]
    · simpa using projection_on_eigenvector j j (v j)
        (Module.End.mem_eigenspace_iff.mp (hv j))
    · intro k hk hkj
      simpa [Ne.symm hkj] using projection_on_eigenvector j k (v k)
        (Module.End.mem_eigenspace_iff.mp (hv k))
    · simp

lemma fourth_roots {z : ℂ} (hz : z ^ 4 = 1) :
    z ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ) := by
  have hprod : (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) = 0 := by
    calc
      _ = z ^ 4 - 1 := by ring_nf; simp [Complex.I_sq]; ring
      _ = 0 := by rw [hz]; ring
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · simp [sub_eq_zero.mp h]
      · simp [eq_neg_of_add_eq_zero_left h]
    · simp [sub_eq_zero.mp h]
  · simp [eq_neg_of_add_eq_zero_left h]

lemma spectrum_subset : spectrum ℂ fourier ⊆ {1, -1, Complex.I, -Complex.I} := by
  intro z hz
  apply fourth_roots
  have h := spectrum.pow_mem_pow fourier 4 hz
  rw [fourth_power] at h
  cases subsingleton_or_nontrivial (H →L[ℂ] H) with
  | inl hs => simp [spectrum.of_subsingleton] at h
  | inr hn => simpa using h

/-! A translated Gaussian has a nonzero component in each eigenspace. -/
private def gauss (a : Euclidean 1) (x : Euclidean 1) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (‖x - a‖ : ℂ) ^ 2)

private def modGauss (a : Euclidean 1) (x : Euclidean 1) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (‖x‖ : ℂ) ^ 2 +
    2 * (Real.pi : ℂ) * Complex.I * (inner ℝ a x : ℝ))

private lemma gaussian_integrable (b : ℝ) (hb : 0 < b) (a : Euclidean 1) :
    Integrable (fun x : Euclidean 1 => Complex.exp (-(b : ℂ) * (‖x-a‖ : ℂ)^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean 1) (b := (b : ℂ)) (by simpa using hb) 0 0
  simpa [sub_eq_add_neg] using h.comp_add_right (-a)

private lemma gauss_integrable (a : Euclidean 1) : Integrable (gauss a) :=
  gaussian_integrable Real.pi Real.pi_pos a

private lemma gauss_memLp (a : Euclidean 1) : MemLp (gauss a) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold gauss; fun_prop)).mpr
  have hi := (gaussian_integrable (2 * Real.pi) (by positivity) a).norm
  convert hi using 1
  ext x
  simp only [gauss, Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

private lemma modGauss_norm (a x : Euclidean 1) : ‖modGauss a x‖ = ‖gauss 0 x‖ := by
  simp [modGauss, gauss, Complex.norm_exp, Complex.mul_re]

private lemma modGauss_memLp (a : Euclidean 1) : MemLp (modGauss a) 2 := by
  exact (memLp_congr_norm (by unfold modGauss; fun_prop)
    (gauss_memLp 0).aestronglyMeasurable
    (Filter.Eventually.of_forall (modGauss_norm a))).mpr (gauss_memLp 0)

private lemma modGauss_integrable (a : Euclidean 1) : Integrable (modGauss a) := by
  exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean 1) (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
    (2 * (Real.pi : ℂ) * Complex.I) a

private lemma transform_modGauss (a x : Euclidean 1) :
    𝓕 (modGauss a) x = gauss a x := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := fourier_gaussian_innerProductSpace' (V := Euclidean 1)
    (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) a x
  change 𝓕 (modGauss a) x = _ at h
  rw [div_self hp, Complex.one_cpow, one_mul, norm_sub_rev a x] at h
  rw [h]
  unfold gauss
  congr 1
  field_simp

private lemma transform_gauss (a x : Euclidean 1) :
    𝓕 (gauss a) x = modGauss (-a) x := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (Euclidean 1)) (gauss 0) (-a)) x
  change 𝓕 (gauss 0 ∘ fun v => v + -a) x = _ at ht
  have heq : (gauss 0 ∘ fun v => v + -a) = gauss a := by
    ext v; simp [gauss, sub_eq_add_neg]
  rw [heq] at ht
  rw [ht]
  have hzero : gauss 0 = modGauss 0 := by ext v; simp [gauss, modGauss]
  change Real.fourierChar (inner ℝ (-a) x) • 𝓕 (gauss 0) x = _
  rw [hzero, transform_modGauss]
  simp only [modGauss, gauss, sub_zero, inner_neg_left,
    Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private def gaussianVector (a : Euclidean 1) : H := (gauss_memLp a).toLp (gauss a)
private def modulatedVector (a : Euclidean 1) : H := (modGauss_memLp a).toLp (modGauss a)

private lemma fourier_gaussianVector (a : Euclidean 1) :
    fourier (gaussianVector a) = modulatedVector (-a) := by
  apply Lp.ext
  filter_upwards [Plancherel.integral_agreement_native (gauss a) (gauss_integrable a)
    (gauss_memLp a), (modGauss_memLp (-a)).coeFn_toLp] with x hx hy
  exact hx.trans ((transform_gauss a x).trans hy.symm)

private lemma fourier_modulatedVector (a : Euclidean 1) :
    fourier (modulatedVector a) = gaussianVector a := by
  apply Lp.ext
  filter_upwards [Plancherel.integral_agreement_native (modGauss a) (modGauss_integrable a)
    (modGauss_memLp a), (gauss_memLp a).coeFn_toLp] with x hx hy
  exact hx.trans ((transform_modGauss a x).trans hy.symm)

private def component (j : Fin 4) (a x : Euclidean 1) : ℂ :=
  (1 / 4 : ℂ) * (gauss a x + (root j)⁻¹ * modGauss (-a) x +
    (root j)⁻¹ ^ 2 * gauss (-a) x + (root j)⁻¹ ^ 3 * modGauss a x)

private lemma ae_add {u v : H} {f g : Euclidean 1 → ℂ}
    (hu : (u : Euclidean 1 → ℂ) =ᵐ[volume] f)
    (hv : (v : Euclidean 1 → ℂ) =ᵐ[volume] g) :
    (↑(u + v) : Euclidean 1 → ℂ) =ᵐ[volume] fun x => f x + g x :=
  (Lp.coeFn_add u v).trans (hu.add hv)

private lemma ae_smul (c : ℂ) {u : H} {f : Euclidean 1 → ℂ}
    (hu : (u : Euclidean 1 → ℂ) =ᵐ[volume] f) :
    (↑(c • u) : Euclidean 1 → ℂ) =ᵐ[volume] fun x => c * f x := by
  exact (Lp.coeFn_smul c u).trans (hu.const_smul c)

private lemma component_ae (j : Fin 4) (a : Euclidean 1) :
    (projection j (gaussianVector a) : Euclidean 1 → ℂ) =ᵐ[volume] component j a := by
  have hd : projection j (gaussianVector a) = (1 / 4 : ℂ) •
      (gaussianVector a + (root j)⁻¹ • modulatedVector (-a) +
        (root j)⁻¹ ^ 2 • gaussianVector (-a) + (root j)⁻¹ ^ 3 • modulatedVector a) := by
    simp [projection_expansion, pow_succ', fourier_gaussianVector, fourier_modulatedVector]
  rw [hd]
  exact ae_smul _ (ae_add (ae_add (ae_add (gauss_memLp a).coeFn_toLp
    (ae_smul _ (modGauss_memLp (-a)).coeFn_toLp))
    (ae_smul _ (gauss_memLp (-a)).coeFn_toLp))
    (ae_smul _ (modGauss_memLp a).coeFn_toLp))

private def axis (t : ℝ) : Euclidean 1 := EuclideanSpace.single 0 t

private lemma norm_axis (t : ℝ) : ‖axis t‖ = |t| := by simp [axis]

private lemma inner_axis (s t : ℝ) : inner ℝ (axis s) (axis t) = s * t := by
  simp [axis, EuclideanSpace.inner_single_left]

private lemma sub_axis (s t : ℝ) : axis s - axis t = axis (s-t) := by
  ext i
  fin_cases i
  simp [axis]

private lemma neg_axis (t : ℝ) : -axis t = axis (-t) := by
  ext i
  fin_cases i
  simp [axis]

private lemma gauss_axis (s t : ℝ) : gauss (axis s) (axis t) =
    (Real.exp (-Real.pi * (t-s)^2) : ℂ) := by
  unfold gauss
  rw [sub_axis, norm_axis, ← Complex.ofReal_pow, sq_abs,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]

private lemma modGauss_axis_zero (s : ℝ) : modGauss (axis s) (axis 0) = 1 := by
  simp [modGauss, norm_axis, inner_axis]

private lemma modGauss_axis_half (s : ℝ) (hs : s = 1 ∨ s = -1) :
    modGauss (axis s) (axis (1/2)) = -(Real.exp (-Real.pi / 4) : ℂ) := by
  unfold modGauss
  rw [norm_axis, inner_axis, Complex.exp_add]
  have h : -(Real.pi : ℂ) * (↑|(1 / 2 : ℝ)| : ℂ)^2 = (-Real.pi / 4 : ℝ) := by
    push_cast
    norm_num
    ring
  rw [h, Complex.ofReal_exp]
  have he : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s * (1/2) : ℝ)) = -1 := by
    rcases hs with rfl | rfl
    · convert Complex.exp_pi_mul_I using 1
      push_cast
      ring
    · rw [show 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℝ) * (1/2) : ℝ) =
        -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  rw [he]
  ring

private lemma component_nonzero (j : Fin 4) : ∃ x, component j (axis 1) x ≠ 0 := by
  have hpos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hlt : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hdiff : Real.exp (-(Real.pi * (1/4))) ≠ Real.exp (-(Real.pi * (9/4))) := by
    intro hh
    have hh' := Real.exp_injective hh
    nlinarith [Real.pi_pos]
  fin_cases j
  · refine ⟨axis 0, ?_⟩
    unfold component
    simp only [neg_axis, gauss_axis, modGauss_axis_zero]
    norm_num [root]
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [Complex.exp_re] at hr
    linarith
  · refine ⟨axis 0, ?_⟩
    unfold component
    simp only [neg_axis, gauss_axis, modGauss_axis_zero]
    norm_num [root]
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [Complex.exp_re] at hr
    linarith
  · refine ⟨axis (1/2), ?_⟩
    unfold component
    rw [neg_axis, gauss_axis, gauss_axis, modGauss_axis_half (-1) (Or.inr rfl),
      modGauss_axis_half 1 (Or.inl rfl)]
    norm_num [root, Complex.inv_I, pow_succ]
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [Complex.exp_re] at hr
    apply hdiff
    linarith
  · refine ⟨axis (1/2), ?_⟩
    unfold component
    rw [neg_axis, gauss_axis, gauss_axis, modGauss_axis_half (-1) (Or.inr rfl),
      modGauss_axis_half 1 (Or.inl rfl)]
    norm_num [root, Complex.inv_I, pow_succ]
    intro hh
    have hr := congrArg Complex.re hh
    norm_num [Complex.exp_re] at hr
    apply hdiff
    linarith

lemma projection_gaussian_ne_zero (j : Fin 4) : projection j (gaussianVector (axis 1)) ≠ 0 := by
  intro hz
  have hae := (component_ae j (axis 1)).symm
  rw [hz] at hae
  have hcont : Continuous (component j (axis 1)) := by
    unfold component gauss modGauss
    fun_prop
  have heq : component j (axis 1) = 0 := MeasureTheory.Measure.eq_of_ae_eq
    (hae.trans (Lp.coeFn_zero _ _ _)) hcont continuous_const
  obtain ⟨x, hx⟩ := component_nonzero j
  exact hx (congrFun heq x)

theorem nonzero_eigenspaces : Spec.NonzeroEigenspaces := by
  intro j
  refine ⟨projection j (gaussianVector (axis 1)), projection_gaussian_ne_zero j, ?_⟩
  exact Module.End.mem_eigenspace_iff.mp (projection_mem j _)

theorem exact_spectrum : Spec.ExactSpectrum := by
  apply Set.Subset.antisymm spectrum_subset
  intro z hz
  have hrange : z ∈ Set.range root := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff, root, Fin.exists_fin_succ, eq_comm] using hz
  obtain ⟨j, rfl⟩ := hrange
  obtain ⟨x, hx, hfx⟩ := nonzero_eigenspaces j
  have hm : Module.End.HasEigenvalue fourier.toLinearMap (root j) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hfx, hx⟩
  rw [ContinuousLinearMap.spectrum_eq]
  exact hm.mem_spectrum

private def coordinateIsometry : ℝ ≃ₗᵢ[ℝ] Euclidean 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

private def coordinateLpIsometry : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ coordinateIsometry.symm coordinateIsometry.symm.measurePreserving)
    (by
      intro g
      refine ⟨Lp.compMeasurePreserving coordinateIsometry coordinateIsometry.measurePreserving g, ?_⟩
      change Lp.compMeasurePreserving coordinateIsometry.symm _
        (Lp.compMeasurePreserving coordinateIsometry _ g) = g
      rw [← Lp.compMeasurePreserving_comp_apply]
      have hid : (coordinateIsometry : ℝ → Euclidean 1) ∘ coordinateIsometry.symm = id := by
        funext x; exact coordinateIsometry.apply_symm_apply x
      simp [hid])

private lemma coordinateLp_toLp (φ : SchwartzMap ℝ ℂ) :
    coordinateLpIsometry (φ.toLp 2) =
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      coordinateIsometry.symm.toContinuousLinearEquiv φ).toLp 2 := by
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving (φ.toLp 2) coordinateIsometry.symm.measurePreserving
  have hφ := coordinateIsometry.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (φ.memLp 2 volume).coeFn_toLp
  filter_upwards [h, hφ,
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      coordinateIsometry.symm.toContinuousLinearEquiv φ).memLp 2 volume |>.coeFn_toLp]
    with x hx hφx hψx
  exact hx.trans (hφx.trans hψx.symm)

theorem real_coordinate_bridge : Spec.RealCoordinateBridge := by
  refine ⟨coordinateIsometry, coordinateLpIsometry, ?_, ?_⟩
  · intro f
    exact Lp.coeFn_compMeasurePreserving f coordinateIsometry.symm.measurePreserving
  · have heq : (fun f => coordinateLpIsometry (Lp.fourierTransformₗᵢ ℝ ℂ f)) =
        fun f => fourier (coordinateLpIsometry f) := by
      apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) ENNReal.ofNat_ne_top).equalizer
        (coordinateLpIsometry.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
        (fourier.continuous.comp coordinateLpIsometry.continuous)
      funext φ
      change coordinateLpIsometry (𝓕 (φ.toLp 2)) =
        fourier (coordinateLpIsometry (φ.toLp 2))
      rw [SchwartzMap.toLp_fourier_eq, coordinateLp_toLp, coordinateLp_toLp]
      change _ = 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        coordinateIsometry.symm.toContinuousLinearEquiv φ).toLp 2)
      rw [SchwartzMap.toLp_fourier_eq]
      congr 1
      ext x
      change (𝓕 φ : SchwartzMap ℝ ℂ) (coordinateIsometry.symm x) = _
      simp only [SchwartzMap.fourier_coe]
      exact (Real.fourier_comp_linearIsometry coordinateIsometry.symm φ x).symm
    intro f
    exact congrFun heq f

end ExpandedFA.Models.FourierFourPointSpectrum
