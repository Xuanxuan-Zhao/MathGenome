import MathGenome.Internal.LinearPDE.P201Specs.Common.BackwardHeat
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ENNReal
namespace P201.Common.BackwardHeat
open P201Specs.Common.BackwardHeat
open ExpandedFA.Sobolev.PeriodicHilbertScale

lemma cosine_coe (j : ℕ) (x : ℝ) :
    cosine j (x : UnitCircle) = Real.cos (2 * π * j * x) := by
  rw [cosine, fourier_coe_apply]
  have he : (2 * (π : ℂ) * Complex.I * (j : ℤ) * x) =
      ((2 * π * j * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he]
  simpa only [Complex.ofReal_one, div_one] using
    Complex.exp_ofReal_mul_I_re (2 * π * j * x)

theorem formula : FormulaStatement := by
  intro T t x j
  simp only [solution, eigenvalue, cosine_coe]
  congr 2 <;> ring

lemma time_derivative (T t x : ℝ) (j : ℕ) :
    HasDerivAt (fun r => solution T j r (x : UnitCircle))
      (eigenvalue j * solution T j t (x : UnitCircle)) t := by
  unfold solution
  convert (((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul
    (-eigenvalue j)).exp.mul_const (cosine j (x : UnitCircle)) using 1 <;> simp only [Pi.sub_apply, id_eq] <;> ring

lemma space_derivative (T t x : ℝ) (j : ℕ) :
    HasDerivAt (fun y : ℝ => solution T j t (y : UnitCircle))
      (Real.exp (-eigenvalue j * (T - t)) *
        (-Real.sin (2 * π * j * x) * (2 * π * j))) x := by
  simp only [solution, cosine_coe]
  convert (((hasDerivAt_id x).const_mul (2 * π * j)).cos).const_mul
    (Real.exp (-eigenvalue j * (T - t))) using 1 <;> simp only [Pi.sub_apply, id_eq] <;> ring

theorem smooth_pde : SmoothPDEStatement := by
  intro T j
  constructor
  · simp only [solution, cosine_coe]
    apply ContDiff.mul
    · exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => -eigenvalue j)).mul
        (contDiff_const.sub contDiff_fst)).exp
    · exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => 2 * π * j)).mul contDiff_snd).cos
  · intro t x
    rw [(time_derivative T t x j).deriv]
    have hd : deriv (fun y : ℝ => solution T j t (y : UnitCircle)) =
        fun y => Real.exp (-eigenvalue j * (T - t)) *
          (-Real.sin (2 * π * j * y) * (2 * π * j)) :=
      funext (fun y => (space_derivative T t y j).deriv)
    rw [hd]
    have hdd := (((((hasDerivAt_id x).const_mul (2 * π * j)).sin).neg).mul_const
      (2 * π * j)).const_mul (Real.exp (-eigenvalue j * (T - t)))
    simp only [id_eq, Pi.neg_apply] at hdd
    rw [hdd.deriv]
    simp only [solution, cosine_coe, eigenvalue]
    ring

lemma terminal_ae (j : ℕ) :
    (terminal j : UnitCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun q => (cosine j q : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ)
    (fourierLp 2 (j : ℤ) + fourierLp 2 (-(j : ℤ))),
    Lp.coeFn_add (fourierLp 2 (j : ℤ)) (fourierLp 2 (-(j : ℤ))),
    coeFn_fourierLp (T := 1) 2 (j : ℤ),
    coeFn_fourierLp (T := 1) 2 (-(j : ℤ))] with q h₁ h₂ h₃ h₄
  change ((1 / 2 : ℂ) • (fourierLp 2 (j : ℤ) + fourierLp 2 (-(j : ℤ))) : L2) q = _
  rw [h₁]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h₂]
  simp only [Pi.add_apply]
  rw [h₃, h₄, fourier_neg]
  apply Complex.ext <;> simp [cosine, Complex.mul_re, Complex.mul_im] <;> ring

theorem terminal_value : TerminalStatement := by
  intro T j
  simpa only [solution, sub_self, mul_zero, Real.exp_zero, one_mul] using terminal_ae j

lemma fourier_inner (m n : ℤ) :
    inner ℂ (fourierLp (T := 1) 2 m) (fourierLp 2 n) = if m = n then 1 else 0 :=
  orthonormal_iff_ite.mp (orthonormal_fourier (T := 1)) m n

lemma terminal_inner (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    inner ℂ (terminal j) (terminal k) = if j = k then 1 / 2 else 0 := by
  have hjk : (j : ℤ) ≠ -(k : ℤ) := by omega
  have hkj : -(j : ℤ) ≠ (k : ℤ) := by omega
  simp only [terminal, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, fourier_inner]
  by_cases h : j = k
  · subst k
    norm_num [hjk, hkj, map_ofNat]
  · have h' : (j : ℤ) ≠ (k : ℤ) := by exact_mod_cast h
    simp [h, h', hjk, hkj]

lemma terminal_norm_sq (j : ℕ) (hj : 1 ≤ j) : ‖terminal j‖ ^ 2 = 1 / 2 := by
  have h := terminal_inner j j hj hj
  rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem terminal_norm : TerminalNormStatement := by
  intro j hj
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hn := terminal_norm_sq j hj
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 1 / Real.sqrt 2)).mp
  rw [hn, div_pow, hs]
  norm_num

theorem terminal_separation : TerminalSeparationStatement := by
  intro j k hj hk hne
  have hi : inner ℂ (terminal j) (terminal k) = 0 := by
    simpa [hne] using terminal_inner j k hj hk
  refine ⟨hi, ?_⟩
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [norm_sub_sq (𝕜 := ℂ), hi, terminal_norm_sq j hj, terminal_norm_sq k hk]
  norm_num

lemma cosine_complex (j : ℕ) (q : UnitCircle) :
    (cosine j q : ℂ) = (1 / 2 : ℂ) * (fourier (j : ℤ) q + fourier (-(j : ℤ)) q) := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [cosine] <;> ring

lemma cosine_coefficient (j : ℕ) (n : ℤ) :
    fourierCoeff (fun q => (cosine j q : ℂ)) n =
      (1 / 2 : ℂ) * ((Pi.single (j : ℤ) 1 : ℤ → ℂ) n + (Pi.single (-(j : ℤ)) 1 : ℤ → ℂ) n) := by
  have hi (k : ℤ) : Integrable (fourier (T := 1) k) AddCircle.haarAddCircle :=
    (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [cosine_complex]
  rw [fourierCoeff.const_mul]
  have ha := congrFun (fourierCoeff.add (hi (j : ℤ)) (hi (-(j : ℤ)))) n
  simp only [Pi.add_apply] at ha
  change fourierCoeff (fun q => fourier (j : ℤ) q + fourier (-(j : ℤ)) q) n = _ at ha
  rw [ha, fourierCoeff_fourier, fourierCoeff_fourier]

lemma cosineHs_coefficient (s : ℝ) (j : ℕ) (n : ℤ) :
    cosineHs s j n =
      (1 / 2 : ℂ) * ((Pi.single (j : ℤ) 1 : ℤ → ℂ) n + (Pi.single (-(j : ℤ)) 1 : ℤ → ℂ) n) := by
  have hw (k : ℤ) : (weight s k : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s k).ne'
  change (weight s (j : ℤ) : ℂ) *
      (((1 / 2 : ℂ) • (lp.single 2 (j : ℤ) 1 + lp.single 2 (-(j : ℤ)) 1) : lp (fun _ : ℤ => ℂ) 2) n /
        (weight s n : ℂ)) = _
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add,
    Pi.add_apply, lp.single_apply]
  by_cases hn : n = (j : ℤ)
  · subst n
    field_simp [hw]
  · by_cases hn' : n = -(j : ℤ)
    · subst n
      rw [show weight s (-(j : ℤ)) = weight s (j : ℤ) by simp [weight, frequencyWeight]]
      field_simp [hw]
    · simp [hn, hn']

theorem initial_value : InitialStatement := by
  intro s T j n
  change (Real.exp (-eigenvalue j * T) : ℂ) * cosineHs s j n = _
  simp only [solution, sub_zero, Complex.ofReal_mul]
  rw [fourierCoeff.const_mul, cosineHs_coefficient, cosine_coefficient]

lemma cosineHs_norm_le (s : ℝ) (j : ℕ) : ‖cosineHs s j‖ ≤ weight s (j : ℤ) := by
  rw [cosineHs, norm_smul, LinearIsometryEquiv.norm_map, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos s _)]
  have hs : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (j : ℤ) 1 +
      lp.single 2 (-(j : ℤ)) 1‖ ≤ 2 := by
    simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one,
      one_add_one_eq_two] using
      norm_add_le (lp.single (E := fun _ : ℤ => ℂ) 2 (j : ℤ) 1)
        (lp.single 2 (-(j : ℤ)) 1)
  norm_num only [norm_div, norm_one, Complex.norm_ofNat] at *
  nlinarith [weight_pos s (j : ℤ)]

lemma initial_norm_le (s T : ℝ) (j : ℕ) :
    ‖initial s T j‖ ≤ weight s (j : ℤ) * Real.exp (-eigenvalue j * T) := by
  rw [initial, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (cosineHs_norm_le s j) (Real.exp_pos (-eigenvalue j * T)).le

lemma eigenvalue_tendsto : Tendsto (fun n : ℕ => eigenvalue (n + 1)) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)) atTop atTop := by
    simpa only [Real.rpow_two, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hn
  exact hp.const_mul_atTop (by positivity : 0 < 4 * π ^ 2)

lemma weighted_decay (s T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => weight s ((n + 1 : ℕ) : ℤ) *
      Real.exp (-eigenvalue (n + 1) * T)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 1 + eigenvalue (n + 1)) atTop atTop :=
    tendsto_const_nhds.add_atTop eigenvalue_tendsto
  have hd := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / 2) T hT).comp hb).mul_const
    (Real.exp T)
  simpa only [zero_mul] using hd.congr (fun n => by
    simp only [Function.comp_apply, mul_assoc, ← Real.exp_add,
      weight, frequencyWeight, Int.cast_natCast]
    congr 2 <;> unfold eigenvalue <;> ring)

theorem initial_convergence : InitialConvergenceStatement := by
  intro s T hT
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => initial_norm_le s T (n + 1))
    (weighted_decay s T hT)

theorem no_terminal_limit : NoTerminalLimitStatement := by
  rintro ⟨b, hb⟩
  rcases Metric.cauchySeq_iff.mp hb.cauchySeq 1 (by norm_num) with ⟨N, hN⟩
  have hh := hN N le_rfl (N + 1) (by omega)
  rw [(terminal_separation (N + 1) (N + 1 + 1) (by omega) (by omega) (by omega)).2] at hh
  exact lt_irrefl 1 hh

theorem no_extension : NoExtensionStatement := by
  intro s T hT D hD F hF
  rintro ⟨E, hE, hc⟩
  let a (n : ℕ) : ↥(insert (0 : PeriodicHs s) D) :=
    ⟨initial s T (n + 1), mem_insert_of_mem 0 (hD (n + 1) (by omega))⟩
  have ha : Tendsto a atTop (𝓝 ⟨0, mem_insert 0 D⟩) :=
    tendsto_subtype_rng.mpr (initial_convergence s T hT)
  have he (n : ℕ) : E (a n) = terminal (n + 1) :=
    (hE ⟨initial s T (n + 1), hD (n + 1) (by omega)⟩).trans (hF (n + 1) (by omega))
  exact no_terminal_limit ⟨E ⟨0, mem_insert 0 D⟩, (hc.tendsto.comp ha).congr he⟩

theorem class_no_extension : ClassNoExtensionStatement := by
  intro s T hT S hS F hF
  have hD (j : ℕ) (hj : 1 ≤ j) : initial s T j ∈ dataSet s S :=
    ⟨solution T j, hS j hj, initial_value s T j⟩
  apply no_extension s T hT (dataSet s S) hD F
  intro j hj
  apply Lp.ext
  exact (hF (solution T j) (hS j hj) ⟨initial s T j, hD j hj⟩
    (initial_value s T j)).trans (terminal_value T j).symm

lemma zero_initial (s : ℝ) : HasInitial s (0 : Solution) (0 : PeriodicHs s) := by
  intro n
  change (0 : ℂ) = fourierCoeff (fun _ : UnitCircle => (0 : ℂ)) n
  simp [fourierCoeff]

theorem class_discontinuity : ClassDiscontinuityStatement := by
  intro s T hT S hS hzero F hF
  have hz : (0 : PeriodicHs s) ∈ dataSet s S := ⟨0, hzero, zero_initial s⟩
  refine ⟨hz, ?_⟩
  intro hz' hc
  let i : ↥(insert (0 : PeriodicHs s) (dataSet s S)) → ↥(dataSet s S) :=
    fun a => ⟨a.val, by
      rcases a.property with h | h
      · simpa only [h] using hz
      · exact h⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  apply class_no_extension s T hT S hS F hF
  refine ⟨F ∘ i, ?_, ?_⟩
  · intro a
    rfl
  · exact hc.comp hi.continuousAt

theorem complexification_norm : ComplexificationStatement := by
  intro f
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) f] with q hq
  simp only [complexify, hq, Complex.ofRealCLM_apply, Complex.norm_real]

lemma real_terminal_ae (T : ℝ) (j : ℕ) :
    (realTerminal j : UnitCircle → ℝ) =ᵐ[AddCircle.haarAddCircle] solution T j T := by
  filter_upwards [Complex.reCLM.coeFn_compLpL (p := 2) (terminal j), terminal_value T j]
    with q hq hq'
  change (Complex.reCLM.compLpL 2 AddCircle.haarAddCircle (terminal j)) q = _
  rw [hq, Complex.reCLM_apply, hq', Complex.ofReal_re]

lemma complexify_real_terminal (j : ℕ) : complexify (realTerminal j) = terminal j := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (realTerminal j),
    real_terminal_ae 1 j, terminal_value 1 j] with q hq hr ht
  change (Complex.ofRealCLM.compLpL 2 AddCircle.haarAddCircle (realTerminal j)) q = _
  rw [hq, Complex.ofRealCLM_apply, hr, ht]

theorem real_terminal : RealTerminalStatement := by
  refine ⟨real_terminal_ae, ?_, ?_⟩
  · intro j hj
    rw [← complexification_norm, complexify_real_terminal]
    exact terminal_norm j hj
  · intro j k hj hk hne
    rw [dist_eq_norm, ← complexification_norm, map_sub,
      complexify_real_terminal, complexify_real_terminal, ← dist_eq_norm]
    exact (terminal_separation j k hj hk hne).2

lemma complexify_terminal_map (s T : ℝ) (S : Set Solution)
    (F : ↥(dataSet s S) → RealL2) (hF : IsRealTerminalMap s T S F) :
    IsTerminalMap s T S (fun a => complexify (F a)) := by
  intro u hu a ha
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2) (F a), hF u hu a ha] with q hq hq'
  change (Complex.ofRealCLM.compLpL 2 AddCircle.haarAddCircle (F a)) q = _
  rw [hq, Complex.ofRealCLM_apply, hq']

theorem real_class_no_extension : RealClassNoExtensionStatement := by
  intro s T hT S hS F hF
  rintro ⟨E, hE, hc⟩
  apply class_no_extension s T hT S hS (fun a => complexify (F a))
    (complexify_terminal_map s T S F hF)
  refine ⟨fun a => complexify (E a), ?_, complexify.continuous.continuousAt.comp hc⟩
  intro a
  exact congrArg complexify (hE a)

theorem real_class_discontinuity : RealClassDiscontinuityStatement := by
  intro s T hT S hS hzero F hF
  have h := class_discontinuity s T hT S hS hzero (fun a => complexify (F a))
    (complexify_terminal_map s T S F hF)
  refine ⟨h.1, fun hz hc => ?_⟩
  exact h.2 hz (complexify.continuous.continuousAt.comp hc)

abbrev solution : SolutionType := P201Specs.Common.BackwardHeat.solution
abbrev initial : InitialType := P201Specs.Common.BackwardHeat.initial
abbrev terminal : TerminalType := P201Specs.Common.BackwardHeat.terminal

end P201.Common.BackwardHeat
