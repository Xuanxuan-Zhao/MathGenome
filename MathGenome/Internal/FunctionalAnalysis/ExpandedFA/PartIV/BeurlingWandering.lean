import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BeurlingWandering
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal NNReal Topology ComplexConjugate
namespace ExpandedFA.PartIV.BeurlingWandering
open HardyDisk BeurlingWanderingSpec

/-- The image of a complete subspace under the shift is complete. -/
theorem shift_closed : ShiftClosed := by
  intro M hM
  exact ((LinearIsometry.isComplete_map_iff HardyDiskSpec.shift).mpr hM.isComplete).isClosed

theorem shiftRange_le {M : Submodule ℂ H2} (hM : ShiftInvariant M) : shiftRange M ≤ M := by
  rintro _ ⟨f, hf, rfl⟩
  exact hM f hf

/-- Surjectivity of the shift on a subspace forces every Taylor coefficient to vanish. -/
theorem eq_bot_of_shiftRange_eq {M : Submodule ℂ H2} (hM : shiftRange M = M) : M = ⊥ := by
  have hz : ∀ n : ℕ, ∀ f ∈ M, f n = 0 := by
    intro n
    induction n with
    | zero =>
      intro f hf
      obtain ⟨g, hg, he⟩ := (show f ∈ shiftRange M by rwa [hM])
      rw [← he]
      exact shift_zero g
    | succ n ih =>
      intro f hf
      obtain ⟨g, hg, he⟩ := (show f ∈ shiftRange M by rwa [hM])
      rw [← he]
      change shift g (n + 1) = 0
      rw [shift_succ]
      exact ih g hg
  apply le_antisymm _ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  apply lp.ext
  funext n
  exact hz n f hf

theorem shift_proper : ShiftProper := by
  intro M hne hM
  exact lt_of_le_of_ne (shiftRange_le hM) (fun he => hne (eq_bot_of_shiftRange_eq he))

theorem wandering_ne_bot {M : Submodule ℂ H2} (hclosed : IsClosed (M : Set H2))
    (hne : M ≠ ⊥) (hM : ShiftInvariant M) : wandering M ≠ ⊥ := by
  let : CompleteSpace (shiftRange M) := (shift_closed M hclosed).completeSpace_coe
  have hs := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (shiftRange_le hM)
  intro he
  have he' : (shiftRange M)ᗮ ⊓ M = ⊥ := by simpa [wandering, inf_comm] using he
  rw [he', sup_bot_eq] at hs
  exact (ne_of_lt (shift_proper M hne hM)) hs

theorem wandering_unit : WanderingUnit := by
  intro M hclosed hne hM
  obtain ⟨f, hf, hfn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (wandering_ne_bot hclosed hne hM)
  refine ⟨(‖f‖⁻¹ : ℂ) • f, (wandering M).smul_mem _ hf, ?_⟩
  simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hfn)]

/-- Multiplication of a circle L² function by an actual exponential character. -/
def modulation (n : ℤ) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL AddCircle.haarAddCircle ∞ 2 2
    (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ (fourier n))

theorem modulation_coe (n : ℤ) (g : BoundaryL2) :
    (modulation n g : HardyDisk.Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun t => fourier n t * g t := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ (fourier n)) g
  filter_upwards [h, ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := ∞)
    AddCircle.haarAddCircle (fourier (T := 2 * π) n)] with t ht hm
  exact ht.trans (by simp only [ContinuousLinearMap.mul_apply', hm])

theorem modulation_mode (n k : ℤ) :
    modulation n (fourierLp (T := 2 * π) 2 k) = fourierLp 2 (n + k) := by
  apply Lp.ext
  filter_upwards [modulation_coe n (fourierLp 2 k),
    coeFn_fourierLp (T := 2 * π) 2 k,
    coeFn_fourierLp (T := 2 * π) 2 (n + k)] with t ht hk hnk
  rw [ht, hk, hnk, fourier_add]

theorem boundary_single (n : ℕ) (c : ℂ) :
    boundary (lp.single (E := fun _ : ℕ => ℂ) 2 n c) =
      c • fourierLp (T := 2 * π) 2 (n : ℤ) := by
  exact HardyDiskSpec.modes_orthonormal.orthogonalFamily.linearIsometry_apply_single c

theorem boundary_shift (f : H2) : boundary (shift f) = modulation 1 (boundary f) := by
  have h₁ := boundary.toContinuousLinearMap.hasSum (shift_series f)
  have h₂ := (modulation 1).hasSum (boundary_series f)
  simp only [map_smul, LinearIsometry.coe_toContinuousLinearMap, boundary_single, one_smul] at h₁
  simp only [map_smul, modulation_mode] at h₂
  simp only [add_comm (1 : ℤ)] at h₂
  exact h₁.unique h₂

theorem boundary_shift_coe (f : H2) :
    (boundary (shift f) : HardyDisk.Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun t => fourier (T := 2 * π) 1 t * boundary f t := by
  rw [boundary_shift]
  exact modulation_coe 1 (boundary f)

/-- Iterating the coefficient shift has the usual pointwise boundary action. -/
theorem boundary_iterate_coe (n : ℕ) (f : H2) :
    (boundary ((shift^[n]) f) : HardyDisk.Circle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun t => fourier (T := 2 * π) (n : ℤ) t * boundary f t := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (by intro t; simp)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    filter_upwards [boundary_shift_coe ((shift^[n]) f), ih] with t ht hn
    rw [ht, hn, Nat.cast_add, Nat.cast_one, fourier_add]
    ring

/-- Products of Hardy boundary vectors are genuinely integrable. -/
theorem boundary_product_integrable (f g : H2) :
    Integrable (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t)
      AddCircle.haarAddCircle := by
  simpa only [RCLike.inner_apply'] using
    L2.integrable_inner (𝕜 := ℂ) (boundary f) (boundary g)

/-- Nonnegative coefficients of the boundary product are shifted inner products. -/
theorem boundary_product_coefficient (f g : H2) (n : ℕ) :
    fourierCoeff (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t) (n : ℤ) =
      inner ℂ ((shift^[n]) f) g := by
  rw [← boundary.inner_map_map, L2.inner_def, fourierCoeff]
  apply integral_congr_ae
  filter_upwards [boundary_iterate_coe n f] with t ht
  rw [ht]
  simp only [RCLike.inner_apply', map_mul, ← fourier_neg, smul_eq_mul]
  ring

/-- Reversing the factors reverses and conjugates the Fourier coefficient. -/
theorem boundary_product_coefficient_neg (f g : H2) (n : ℤ) :
    fourierCoeff (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t) (-n) =
      conj (fourierCoeff (fun t : HardyDisk.Circle => conj (boundary g t) * boundary f t) n) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    simp only [neg_neg, smul_eq_mul, map_mul, starRingEnd_self_apply, ← fourier_neg]
    ring

theorem iterate_mem {M : Submodule ℂ H2} (hM : ShiftInvariant M)
    {f : H2} (hf : f ∈ M) (n : ℕ) : (shift^[n]) f ∈ M := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hM _ ih

theorem positive_iterate_mem_shiftRange {M : Submodule ℂ H2} (hM : ShiftInvariant M)
    {f : H2} (hf : f ∈ M) {n : ℕ} (hn : 0 < n) : (shift^[n]) f ∈ shiftRange M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  exact ⟨(shift^[k]) f, iterate_mem hM hf k, rfl⟩

theorem wandering_product_coefficient_zero {M : Submodule ℂ H2} (hM : ShiftInvariant M)
    {f g : H2} (hf : f ∈ wandering M) (hg : g ∈ wandering M) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeff (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t) n = 0 := by
  have hpos {f g : H2} (hf : f ∈ wandering M) (hg : g ∈ wandering M)
      (k : ℕ) (hk : 0 < k) :
      fourierCoeff (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t) (k : ℤ) = 0 := by
    rw [boundary_product_coefficient]
    exact hg.2 _ (positive_iterate_mem_shiftRange hM hf.1 hk)
  rcases lt_or_gt_of_ne hn with hneg | hpos'
  · have h := hpos hg hf (-n).toNat (by omega)
    have he : n = -(((-n).toNat : ℕ) : ℤ) := by omega
    rw [he, boundary_product_coefficient_neg, h, map_zero]
  · have he : n = (n.toNat : ℤ) := by omega
    rw [he]
    exact hpos hf hg n.toNat (by omega)

/-- Both signs of the Fourier coefficients are used here; positive coefficients
alone would not imply that the product is constant. -/
theorem wandering_boundary_product {M : Submodule ℂ H2} (hM : ShiftInvariant M)
    {f g : H2} (hf : f ∈ wandering M) (hg : g ∈ wandering M) :
    (fun t : HardyDisk.Circle => conj (boundary f t) * boundary g t) =ᵐ[AddCircle.haarAddCircle]
      (fun _ => inner ℂ f g) := by
  apply ExpandedFA.Fourier.TorusFourierBasis.l1_unique (2 * π) _ _
    (boundary_product_integrable f g) (integrable_const _)
  intro n
  have hc : fourierCoeff (fun _ : HardyDisk.Circle => inner ℂ f g) n =
      inner ℂ f g * (if n = 0 then 1 else 0) := by
    have h := fourierCoeff.const_mul (fourier (T := 2 * π) 0) (inner ℂ f g) n
    simpa [fourier_zero, fourierCoeff_fourier, Pi.single_apply, eq_comm] using h
  rw [hc]
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, ite_true, mul_one, Function.iterate_zero_apply] using
      boundary_product_coefficient f g 0
  · rw [wandering_product_coefficient_zero hM hf hg hn, ite_eq_right hn, mul_zero]

theorem wandering_boundary_unit : WanderingBoundaryUnit := by
  intro M _ _ hM θ hθ hnorm
  have h := wandering_boundary_product hM hθ hθ
  have hi : inner ℂ θ θ = 1 := by simp [inner_self_eq_norm_sq_to_K, hnorm]
  rw [hi] at h
  filter_upwards [h] with t ht
  have hn := congrArg norm ht
  simp only [norm_mul, RCLike.norm_conj, norm_one] at hn
  nlinarith [norm_nonneg (boundary θ t)]

/-- A unit wandering vector spans the whole wandering space, with the actual
Hilbert inner product as the coefficient. -/
theorem wandering_eq_smul {M : Submodule ℂ H2} (hclosed : IsClosed (M : Set H2))
    (hne : M ≠ ⊥) (hM : ShiftInvariant M) {θ h : H2}
    (hθ : θ ∈ wandering M) (hθnorm : ‖θ‖ = 1) (hh : h ∈ wandering M) :
    h = inner ℂ θ h • θ := by
  apply boundary.injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [wandering_boundary_unit M hclosed hne hM θ hθ hθnorm,
    wandering_boundary_product hM hθ hh,
    Lp.coeFn_smul (inner ℂ θ h) (boundary θ)] with t ht hp hc
  rw [hc, Pi.smul_apply, smul_eq_mul]
  have hi : boundary θ t * conj (boundary θ t) = 1 := by
    simp [RCLike.mul_conj, ht]
  calc
    boundary h t = (boundary θ t * conj (boundary θ t)) * boundary h t := by rw [hi, one_mul]
    _ = inner ℂ θ h * boundary θ t := by rw [mul_assoc, hp, mul_comm]

theorem wandering_dimension : WanderingDimension := by
  intro M hclosed hne hM
  obtain ⟨θ, hθ, hnorm⟩ := wandering_unit M hclosed hne hM
  apply rank_eq_one (⟨θ, hθ⟩ : wandering M)
  · intro he
    have hz : θ = 0 := congrArg Subtype.val he
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  · intro h
    refine ⟨inner ℂ θ h.val, Subtype.ext ?_⟩
    exact (wandering_eq_smul hclosed hne hM hθ hnorm h.property).symm

/-- The real nonnegative normalized Poisson kernel, on the angular circle. -/
def poissonWeight (z : Disk) (t : HardyDisk.Circle) : ℝ :=
  (1 - ‖z.val‖ ^ 2) / ‖fourier (T := 2 * π) 1 t - z.val‖ ^ 2

theorem poissonWeight_nonneg (z : Disk) (t : HardyDisk.Circle) : 0 ≤ poissonWeight z t := by
  have hz : ‖z.val‖ < 1 := by
    simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z.val]

theorem poissonWeight_integrable (z : Disk) : Integrable (poissonWeight z) AddCircle.haarAddCircle := by
  have h := (memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) AddCircle.haarAddCircle ℂ (poissonKernelMap z))).re
  exact h.congr (Filter.Eventually.of_forall fun _ => rfl)

theorem poissonWeight_integral (z : Disk) :
    (∫ t : HardyDisk.Circle, poissonWeight z t ∂AddCircle.haarAddCircle) = 1 := by
  let e : H2 := lp.single 2 0 1
  have he : (boundary e : HardyDisk.Circle → ℂ) =ᵐ[AddCircle.haarAddCircle] (fun _ => 1) := by
    rw [show boundary e = fourierLp (T := 2 * π) 2 0 by
      simpa only [e, Nat.cast_zero, one_smul] using boundary_single 0 1]
    filter_upwards [coeFn_fourierLp (T := 2 * π) 2 0] with t ht
    simpa only [fourier_zero] using ht
  have hi : Complex.ofReal (∫ t : HardyDisk.Circle, poissonWeight z t ∂AddCircle.haarAddCircle) = 1 := by
    calc
      _ = ∫ t : HardyDisk.Circle, (poissonWeight z t : ℂ) ∂AddCircle.haarAddCircle :=
        (integral_ofReal (𝕜 := ℂ) (μ := AddCircle.haarAddCircle) (f := poissonWeight z)).symm
      _ = poissonExtension e z := by
        change _ = ∫ t : HardyDisk.Circle, poissonWeight z t • boundary e t ∂AddCircle.haarAddCircle
        apply integral_congr_ae
        filter_upwards [he] with t ht
        simp only [ht, Complex.real_smul, mul_one]
      _ = eval e z := poisson_evaluation e z z.property
      _ = 1 := by
        simpa only [pow_zero, mul_one] using monomial_evaluation 0 1 z.val
  exact_mod_cast hi

/-- Poisson majorization of the norm, obtained from the actual Poisson formula
and the triangle inequality for the Bochner integral. -/
theorem poisson_norm_majorization (f : H2) (z : Disk) :
    ‖eval f z‖ ≤ ∫ t : HardyDisk.Circle, poissonWeight z t * ‖boundary f t‖
      ∂AddCircle.haarAddCircle := by
  change ‖HardyDiskSpec.eval f z.val‖ ≤ _
  rw [← poisson_evaluation f z z.property]
  change ‖∫ t : HardyDisk.Circle, poissonWeight z t • boundary f t ∂AddCircle.haarAddCircle‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change ‖poissonWeight z t • boundary f t‖ = poissonWeight z t * ‖boundary f t‖
    exact (norm_smul _ _).trans (congrArg (fun r => r * ‖boundary f t‖)
      (Real.norm_of_nonneg (poissonWeight_nonneg z t)))

/-- An essentially bounded boundary function controls its analytic Poisson
extension with the same sharp bound. -/
theorem disk_bound_of_boundary {f : H2}
    (hf : ∀ᵐ t ∂AddCircle.haarAddCircle, ‖boundary f t‖ ≤ 1)
    (z : Disk) : ‖eval f z‖ ≤ 1 := by
  apply (poisson_norm_majorization f z).trans
  calc
    _ ≤ ∫ t : HardyDisk.Circle, poissonWeight z t ∂AddCircle.haarAddCircle := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => mul_nonneg (poissonWeight_nonneg z t) (norm_nonneg _))
        (poissonWeight_integrable z)
      filter_upwards [hf] with t ht
      exact mul_le_of_le_one_right (poissonWeight_nonneg z t) ht
    _ = 1 := poissonWeight_integral z

theorem wandering_disk_bound : WanderingDiskBound := by
  intro M hclosed hne hM θ hθ hnorm z hz
  apply disk_bound_of_boundary (z := ⟨z, hz⟩)
  exact (wandering_boundary_unit M hclosed hne hM θ hθ hnorm).mono (fun _ h => h.le)

theorem wandering_inner : WanderingInner := by
  intro M hclosed hne hM θ hθ hnorm
  exact ⟨⟨1, wandering_disk_bound M hclosed hne hM θ hθ hnorm⟩,
    wandering_boundary_unit M hclosed hne hM θ hθ hnorm⟩

end ExpandedFA.PartIV.BeurlingWandering
