import MathGenome.Internal.FourierSobolev.P102.Periodic.OscillatoryDecay
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Localization
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ComplexConjugate

namespace P102.Periodic

variable (T : ℝ) [Fact (0 < T)]

theorem continuous_dirichletKernel (N : ℕ) : Continuous (dirichletKernel T N) := by
  unfold dirichletKernel
  fun_prop

theorem dirichletKernel_zero (N : ℕ) :
    dirichletKernel T N 0 = (2 * N + 1 : ℂ) := by
  have hcard : (frequencies N).card = 2 * N + 1 := by
    simp only [frequencies, Int.card_Icc]
    omega
  simp only [dirichletKernel, mode, fourier_eval_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hcard]
  push_cast
  rfl

theorem dirichletKernel_continuous_extension (N : ℕ) :
    Continuous (dirichletKernel T N) ∧
    Tendsto (fun t : ℝ => dirichletKernel T N (t : Circle T))
      (𝓝 0) (𝓝 (2 * N + 1 : ℂ)) := by
  refine ⟨continuous_dirichletKernel T N, ?_⟩
  have h := ((continuous_dirichletKernel T N).comp
    (show Continuous (fun t : ℝ => (t : Circle T)) from continuous_quotient_mk')).tendsto 0
  simpa only [Function.comp_def, QuotientAddGroup.mk_zero, dirichletKernel_zero] using h

theorem integrable_mul_mode (f : Circle T → ℂ) (hf : Integrable f (haar T)) (k : ℤ) :
    Integrable (fun y => f y * mode T k y) (haar T) := by
  apply hf.mul_bdd (mode T k).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun y => le_of_eq (Circle.norm_coe _))

theorem dirichlet_convolution_exists (f : Circle T → ℂ) (hf : Integrable f (haar T))
    (N : ℕ) (x : Circle T) :
    ConvolutionExistsAt T f (dirichletKernel T N) x := by
  have hfx : Integrable (fun y => f (x - y)) (haar T) :=
    hf.comp_sub_left x
  unfold ConvolutionExistsAt dirichletKernel
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun k _ => integrable_mul_mode T _ hfx k)

theorem mode_sub (k : ℤ) (x y : Circle T) :
    mode T k (x - y) = mode T k x * conj (mode T k y) := by
  simp only [mode, fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

theorem partialSum_eq_convolution (f : Circle T → ℂ) (hf : Integrable f (haar T))
    (N : ℕ) (x : Circle T) :
    partialSum T N f x = convolution T f (dirichletKernel T N) x := by
  have hfx : Integrable (fun y => f (x - y)) (haar T) :=
    hf.comp_sub_left x
  unfold partialSum convolution dirichletKernel
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => integrable_mul_mode T _ hfx k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← integral_sub_left_eq_self (fun y => f (x - y) * mode T k y) (haar T) x]
  simp only [sub_sub_cancel, mode_sub]
  rw [coefficient, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

theorem dirichletKernel_succ (N : ℕ) (x : Circle T) :
    dirichletKernel T (N + 1) x =
      mode T (N + 1) x + mode T (-(N + 1)) x + dirichletKernel T N x := by
  simpa only [dirichletKernel, frequencies, Nat.cast_add, Nat.cast_one] using
    (Finset.sum_Icc_succ_eq_add_endpoints (fun k => mode T k x) (N := N))

/-- Multiplication by one minus the first character telescopes the finite sum.
This identity holds at the singular point too. -/
theorem dirichletKernel_mul_mode_sub_one (N : ℕ) (x : Circle T) :
    dirichletKernel T N x * (mode T 1 x - 1) =
      mode T (N + 1) x - mode T (-(N : ℤ)) x := by
  have hshift (k : ℤ) : mode T k x * mode T 1 x = mode T (k + 1) x :=
    fourier_add.symm
  induction N with
  | zero => simp [dirichletKernel, frequencies, mode]
  | succ N ih =>
    rw [dirichletKernel_succ]
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    calc
      _ = (mode T (↑N + 1) x * mode T 1 x - mode T (-(↑N + 1)) x) +
          (mode T (-(↑N + 1)) x * mode T 1 x - mode T (-(↑N)) x) := by
        rw [add_mul, add_mul, ih]
        ring
      _ = _ := by
        rw [hshift, hshift, show -(↑N + 1 : ℤ) + 1 = -↑N by ring]
        ring

theorem dirichletKernel_sine_quotient (N : ℕ) (v : ℝ)
    (hv₁ : -Real.pi ≤ v) (hv₂ : v ≤ Real.pi) (hv : v ≠ 0) :
    dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
      ((Real.sin (((N : ℝ) + 1 / 2) * v) / Real.sin (v / 2) : ℝ) : ℂ) := by
  let E : ℝ → ℂ := fun a => Complex.exp (Complex.I * a)
  have hmul (a b : ℝ) : E a * E b = E (a + b) := by
    dsimp [E]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsin (a : ℝ) : E a - E (-a) = 2 * Complex.I * (Real.sin a : ℂ) := by
    dsimp [E]
    rw [show Complex.I * (a : ℂ) = (a : ℂ) * Complex.I by ring,
      show Complex.I * ((-a : ℝ) : ℂ) = -(a : ℂ) * Complex.I by push_cast; ring,
      ← Complex.cos_add_sin_I, ← Complex.cos_sub_sin_I, Complex.ofReal_sin]
    ring
  have hm (k : ℤ) : mode (2 * Real.pi) k (v : Circle (2 * Real.pi)) = E (k * v) := by
    rw [angular_mode]
    dsimp [E]
    congr 1
    push_cast
    ring
  have hg := dirichletKernel_mul_mode_sub_one (2 * Real.pi) N
    (v : Circle (2 * Real.pi))
  simp only [hm, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, one_mul] at hg
  have hh : dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) *
      (E (v / 2) - E (-(v / 2))) =
      E (((N : ℝ) + 1 / 2) * v) - E (-(((N : ℝ) + 1 / 2) * v)) := by
    calc
      _ = (dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) *
          (E v - 1)) * E (-(v / 2)) := by
        rw [mul_assoc, sub_mul, hmul, one_mul,
          show v + -(v / 2) = v / 2 by ring]
      _ = (E (((N : ℝ) + 1) * v) - E (-(N : ℝ) * v)) * E (-(v / 2)) := by rw [hg]
      _ = _ := by
        rw [sub_mul, hmul, hmul]
        congr 2 <;> ring
  rw [hsin, hsin] at hh
  have hd : dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) *
      (Real.sin (v / 2) : ℂ) = (Real.sin (((N : ℝ) + 1 / 2) * v) : ℂ) := by
    apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) Complex.I_ne_zero)
    calc
      _ = dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) *
          (2 * Complex.I * (Real.sin (v / 2) : ℂ)) := by ring
      _ = _ := hh
  have hne : Real.sin (v / 2) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos] : -Real.pi < v / 2)
      (by linarith [Real.pi_pos] : v / 2 < Real.pi)]
    exact div_ne_zero hv two_ne_zero
  rw [Complex.ofReal_div]
  exact (eq_div_iff (Complex.ofReal_ne_zero.mpr hne)).mpr hd

/-- Division by the first-character difference is integrable when its numerator
vanishes almost everywhere near the only zero of that difference. -/
theorem integrable_div_mode_sub_one (h : Circle T → ℂ) (hh : Integrable h (haar T))
    (V : Set (Circle T)) (hV : IsOpen V) (h0 : 0 ∈ V)
    (hz : h =ᵐ[(haar T).restrict V] 0) :
    Integrable (fun y => h y / (mode T 1 y - 1)) (haar T) := by
  have hne (y : Circle T) (hy : y ∈ Vᶜ) : mode T 1 y - 1 ≠ 0 := by
    intro he
    have hy0 : y = 0 := by
      apply AddCircle.injective_toCircle (Fact.out : 0 < T).ne'
      apply Subtype.ext
      simpa [mode] using sub_eq_zero.mp he
    exact hy (hy0 ▸ h0)
  have hc : ContinuousOn (fun y : Circle T => (mode T 1 y - 1)⁻¹) Vᶜ :=
    ((mode T 1).continuous.sub continuous_const).continuousOn.inv₀ hne
  obtain ⟨C, hC⟩ := hV.isClosed_compl.isCompact.exists_bound_of_continuousOn hc
  let b : Circle T → ℂ := Vᶜ.indicator (fun y => (mode T 1 y - 1)⁻¹)
  have hb : AEStronglyMeasurable b (haar T) :=
    (((mode T 1).continuous.measurable.sub measurable_const).inv.indicator
      hV.measurableSet.compl).aestronglyMeasurable
  have hbnd : ∀ᵐ y ∂haar T, ‖b y‖ ≤ max C 0 := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ Vᶜ
    · apply le_trans ?_ (le_max_left C 0)
      simpa only [b, indicator_of_mem hy] using hC y hy
    · simp [b, indicator_of_notMem hy]
  have hi := hh.mul_bdd hb hbnd
  apply hi.congr
  have hz' : ∀ᵐ y ∂haar T, y ∈ V → h y = 0 := (ae_restrict_iff' hV.measurableSet).mp hz
  filter_upwards [hz'] with y hy
  by_cases hyV : y ∈ V
  · simp [hy hyV]
  · simp [b, hyV, div_eq_mul_inv]

theorem mode_one_eq_one_iff (y : Circle T) : mode T 1 y = 1 ↔ y = 0 := by
  constructor
  · intro hy
    apply AddCircle.injective_toCircle (Fact.out : 0 < T).ne'
    apply Subtype.ext
    simpa [mode] using hy
  · rintro rfl
    simp [mode]

theorem integral_mul_mode_eq_coefficient (h : Circle T → ℂ) (k : ℤ) :
    (∫ y, h y * mode T k y ∂haar T) = coefficient T h (-k) := by
  simp [coefficient, mode]

/-- Riemann localization for arbitrary integrable representatives. -/
theorem partialSum_localization (f g : Circle T → ℂ)
    (hf : Integrable f (haar T)) (hg : Integrable g (haar T))
    (x : Circle T) (U : Set (Circle T)) (hU : IsOpen U) (hx : x ∈ U)
    (hfg : f =ᵐ[(haar T).restrict U] g) :
    Tendsto (fun N : ℕ => partialSum T N f x - partialSum T N g x) atTop (𝓝 0) := by
  let h : Circle T → ℂ := fun y => f (x - y) - g (x - y)
  let V : Set (Circle T) := (fun y => x - y) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.sub continuous_id)
  have h0 : (0 : Circle T) ∈ V := by simpa [V] using hx
  have hh : Integrable h (haar T) := (hf.comp_sub_left x).sub (hg.comp_sub_left x)
  have hz' : ∀ᵐ y ∂haar T, y ∈ V → h y = 0 := by
    have H := ((haar T).measurePreserving_sub_left x).quasiMeasurePreserving.ae
      ((ae_restrict_iff' hU.measurableSet).mp hfg)
    filter_upwards [H] with y hy
    exact fun hyV => sub_eq_zero.mpr (hy hyV)
  have hz : h =ᵐ[(haar T).restrict V] 0 := (ae_restrict_iff' hV.measurableSet).mpr hz'
  let q : Circle T → ℂ := fun y => h y / (mode T 1 y - 1)
  have hq : Integrable q (haar T) := integrable_div_mode_sub_one T h hh V hV h0 hz
  have hfactor : h =ᵐ[haar T] fun y => q y * (mode T 1 y - 1) := by
    filter_upwards [hz'] with y hy
    by_cases hyV : y ∈ V
    · simp [q, hy hyV]
    · have hne : mode T 1 y - 1 ≠ 0 := by
        rw [sub_ne_zero, ne_eq, mode_one_eq_one_iff, ← ne_eq]
        exact fun hy0 => hyV (hy0 ▸ h0)
      exact (div_mul_cancel₀ (h y) hne).symm
  have heq (N : ℕ) : partialSum T N f x - partialSum T N g x =
      coefficient T q (-(↑N + 1)) - coefficient T q (N : ℤ) := by
    calc
      _ = ∫ y, h y * dirichletKernel T N y ∂haar T := by
        rw [partialSum_eq_convolution T f hf, partialSum_eq_convolution T g hg]
        unfold convolution
        rw [← integral_sub (dirichlet_convolution_exists T f hf N x)
          (dirichlet_convolution_exists T g hg N x)]
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by dsimp [h]; ring)
      _ = ∫ y, q y * (mode T (↑N + 1) y - mode T (-↑N) y) ∂haar T := by
        apply integral_congr_ae
        filter_upwards [hfactor] with y hy
        rw [hy, mul_assoc, mul_comm (mode T 1 y - 1), dirichletKernel_mul_mode_sub_one]
      _ = _ := by
        simp_rw [mul_sub]
        rw [integral_sub (integrable_mul_mode T q hq _) (integrable_mul_mode T q hq _),
          integral_mul_mode_eq_coefficient, integral_mul_mode_eq_coefficient, neg_neg]
  have hp : Tendsto (fun N : ℕ => -((N : ℤ) + 1)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    have hinj : Function.Injective (fun N : ℕ => -((N : ℤ) + 1)) := by
      intro a b hab
      simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab
      exact hab
    exact hinj.tendsto_cofinite
  have hn : Tendsto (fun N : ℕ => (N : ℤ)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact (Nat.cast_injective : Function.Injective (fun N : ℕ => (N : ℤ))).tendsto_cofinite
  have hd := coefficient_decay T q hq
  have H := (hd.comp hp).sub (hd.comp hn)
  simp only [sub_self] at H
  exact H.congr' (Eventually.of_forall fun N => (heq N).symm)

/-- The same fixed-point conclusion on the canonical L¹ quotient. -/
theorem partialSum_localizationL1 (f g : L1 T) (x : Circle T) (U : Set (Circle T))
    (hU : IsOpen U) (hx : x ∈ U)
    (hfg : (f : Circle T → ℂ) =ᵐ[(haar T).restrict U] (g : Circle T → ℂ)) :
    Tendsto (fun N : ℕ => partialSum T N f x - partialSum T N g x) atTop (𝓝 0) :=
  partialSum_localization T f g (MeasureTheory.L1.integrable_coeFn f)
    (MeasureTheory.L1.integrable_coeFn g) x U hU hx hfg

end P102.Periodic
