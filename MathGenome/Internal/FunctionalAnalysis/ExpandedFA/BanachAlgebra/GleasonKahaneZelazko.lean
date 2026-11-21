import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NonemptySpectrum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.GleasonKahaneZelazko
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ExpandedFA.BanachAlgebra

universe u

/-- The invertibility condition puts each scalar value in the spectrum.
This step uses no continuity of the given linear functional. -/
theorem gkz_mem_spectrum {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : φ a ∈ spectrum ℂ a := by
  change ¬ IsUnit (algebraMap ℂ A (φ a) - a)
  intro h
  apply hunit _ h
  simp [Algebra.algebraMap_eq_smul_one, map_sub, h1]

/-- Automatic contractivity, before any multiplicativity is known. -/
theorem gkz_norm_le {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : ‖φ a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (gkz_mem_spectrum φ h1 hunit a)

/-- The purely algebraic last step of GKZ: preserving squares forces
multiplicativity, even when the algebra is not commutative. -/
theorem gkz_multiplicative_of_squares {A : Type u} [Ring A] [Algebra ℂ A]
    (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hsq : ∀ a : A, φ (a ^ 2) = (φ a) ^ 2) :
    ∀ a b : A, φ (a * b) = φ a * φ b := by
  have jordan (a b : A) : φ (a * b) + φ (b * a) = 2 * φ a * φ b := by
    have he : (a + b) ^ 2 = a ^ 2 + (a * b + b * a) + b ^ 2 := by noncomm_ring
    have h := hsq (a + b)
    rw [he, map_add, map_add, map_add, map_add, hsq, hsq] at h
    linear_combination h
  have kernel_mul (x y : A) (hx : φ x = 0) : φ (x * y) = 0 := by
    have hj := jordan x y
    rw [hx] at hj
    have hid : x * (y * x * y) + (y * x * y) * x = (x * y) ^ 2 + (y * x) ^ 2 := by
      noncomm_ring
    have hk := jordan x (y * x * y)
    rw [← map_add, hid, map_add, hsq, hsq, hx] at hk
    have hneg : φ (y * x) = -φ (x * y) := by linear_combination hj
    rw [hneg] at hk
    have hz : (φ (x * y)) ^ 2 = 0 := by linear_combination (1 / 2 : ℂ) * hk
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz
  intro a b
  have hx : φ (a - φ a • (1 : A)) = 0 := by simp [h1]
  have h := kernel_mul (a - φ a • (1 : A)) b hx
  exact sub_eq_zero.mp (by simpa [sub_mul, smul_mul_assoc, h1] using h)

open Metric Set in
/-- An entire function vanishing at zero whose real part grows at most linearly
has bounded derivative. Borel–Carathéodory controls the full norm, then Cauchy's
estimate on a circle of radius `‖c‖ + 1` gives a bound independent of its center. -/
theorem gkz_bounded_derivative {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (h0 : h 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z, (h z).re ≤ C * ‖z‖) :
    Bornology.IsBounded (Set.range (deriv h)) := by
  have hnorm (z : ℂ) : ‖h z‖ ≤ 4 * (C + 1) * ‖z‖ := by
    by_cases hz : z = 0
    · simp [hz, h0]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hb := Complex.borelCaratheodory_zero
      (f := h) (z := z) (M := (C + 1) * (2 * ‖z‖)) (R := 2 * ‖z‖)
      (by positivity) hd.differentiableOn (fun w hw => ?_)
      (by positivity) (by rw [mem_ball_zero_iff]; linarith) h0
    · calc ‖h z‖ ≤ 2 * ((C + 1) * (2 * ‖z‖)) * ‖z‖ / (2 * ‖z‖ - ‖z‖) := hb
        _ = 4 * (C + 1) * ‖z‖ := by field_simp; ring
    · have hw' : ‖w‖ < 2 * ‖z‖ := mem_ball_zero_iff.mp hw
      change (h w).re ≤ (C + 1) * (2 * ‖z‖)
      exact (hgrowth w).trans (by nlinarith [norm_nonneg w])
  rw [isBounded_iff_forall_norm_le]
  refine ⟨8 * (C + 1), ?_⟩
  rintro _ ⟨c, rfl⟩
  have hr : 0 < ‖c‖ + 1 := by positivity
  calc ‖deriv h c‖ ≤ (8 * (C + 1) * (‖c‖ + 1)) / (‖c‖ + 1) := by
        apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd.diffContOnCl
        intro z hz
        have hz' : ‖z‖ ≤ (‖c‖ + 1) + ‖c‖ := by
          calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
               _ = (‖c‖ + 1) + ‖c‖ := by rw [mem_sphere_iff_norm.mp hz]
        exact (hnorm z).trans (by nlinarith)
       _ = 8 * (C + 1) := mul_div_cancel_right₀ _ hr.ne'

/-- The analytic lemma used by GKZ. Nonvanishing and exponential type are
hypotheses here only on the auxiliary scalar entire function, and will be
proved from the original invertibility assumption in the application. -/
theorem gkz_entire_second_deriv {F : ℂ → ℂ} (hd : Differentiable ℂ F)
    (h0 : F 0 = 1) (hne : ∀ z, F z ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z, ‖F z‖ ≤ Real.exp (C * ‖z‖)) :
    deriv (deriv F) 0 = (deriv F 0) ^ 2 := by
  obtain ⟨h, hc, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (U := Set.univ) (by
      let := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
      exact SimplyConnectedSpace.ofContractible _) isOpen_univ hd.continuous.continuousOn
    (by simpa only [Set.image_univ, Set.mem_range, not_exists] using hne)
  have hc' : Continuous h := continuousOn_univ.mp hc
  have he' (z : ℂ) : Complex.exp (h z) = F z := he (Set.mem_univ z)
  have hh : Differentiable ℂ h := by
    intro z
    exact ((Complex.hasDerivAt_exp (h z)).of_comp_left hc'.continuousAt
      (hd z).hasDerivAt (Complex.exp_ne_zero _) (Filter.Eventually.of_forall he')).differentiableAt
  let g : ℂ → ℂ := fun z => h z - h 0
  have hg : Differentiable ℂ g := hh.sub_const _
  have hg0 : g 0 = 0 := sub_self _
  have heg (z : ℂ) : Complex.exp (g z) = F z := by
    dsimp [g]
    rw [Complex.exp_sub, he', he', h0, div_one]
  have hgre (z : ℂ) : (g z).re ≤ C * ‖z‖ := by
    apply Real.exp_le_exp.mp
    rw [← Complex.norm_exp, heg]
    exact hgrowth z
  have hconst (z : ℂ) : deriv g z = deriv g 0 :=
    hg.deriv.apply_eq_apply_of_bounded (gkz_bounded_derivative hg hg0 hC hgre) z 0
  have hderiv : deriv F = fun z => F z * deriv g 0 := by
    ext z
    have hp := (hg z).hasDerivAt.cexp
    have heq : (fun w => Complex.exp (g w)) = F := funext heg
    rw [heq, heg, hconst] at hp
    exact hp.deriv
  have hc0 : deriv F 0 = deriv g 0 := by simp [hderiv, h0]
  calc deriv (deriv F) 0 = deriv F 0 * deriv g 0 := by
         conv_lhs => rw [hderiv]
         exact ((hd 0).hasDerivAt.mul_const _).deriv
       _ = (deriv F 0) ^ 2 := by rw [← hc0]; ring

/-- The exponential norm bound, obtained by comparing the defining series
with the scalar real exponential series. -/
theorem gkz_norm_exp_le {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  apply tsum_of_norm_bounded
    (show HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * ‖x‖ ^ n) (Real.exp ‖x‖) from ?_)
  · intro n
    simp only [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)
  · simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)

/-- GKZ's analytic stage: applying the functional to `exp (z • a)` gives a
nonvanishing entire function of exponential type. Comparing its derivatives
at zero proves preservation of squares. -/
theorem gkz_preserves_squares {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (φ : A →ₗ[ℂ] ℂ) (h1 : φ 1 = 1)
    (hunit : ∀ a : A, IsUnit a → φ a ≠ 0) (a : A) : φ (a ^ 2) = (φ a) ^ 2 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let ψ : A →L[ℂ] ℂ := φ.mkContinuous 1 (fun x => by simpa using gkz_norm_le φ h1 hunit x)
  let F : ℂ → ℂ := fun z => ψ (NormedSpace.exp (z • a))
  have hd : Differentiable ℂ F :=
    ψ.differentiable.comp (differentiable_exp_smul_const ℂ a)
  have h0 : F 0 = 1 := by simpa [F, ψ] using h1
  have hne (z : ℂ) : F z ≠ 0 := hunit _ (NormedSpace.isUnit_exp _)
  have hgrowth (z : ℂ) : ‖F z‖ ≤ Real.exp (‖a‖ * ‖z‖) := by
    calc ‖F z‖ ≤ ‖NormedSpace.exp (z • a)‖ := gkz_norm_le φ h1 hunit _
         _ ≤ Real.exp ‖z • a‖ := gkz_norm_exp_le _
         _ = Real.exp (‖a‖ * ‖z‖) := by rw [norm_smul, mul_comm]
  have hdF (z : ℂ) : HasDerivAt F (ψ (NormedSpace.exp (z • a) * a)) z :=
    ψ.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_exp_smul_const a z)
  have hdFeq : deriv F = fun z => ψ (NormedSpace.exp (z • a) * a) :=
    funext (fun z => (hdF z).deriv)
  have hfirst : deriv F 0 = φ a := by simpa [ψ] using (hdF 0).deriv
  have hsecond : deriv (deriv F) 0 = φ (a ^ 2) := by
    rw [hdFeq]
    have hh := ψ.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_exp_smul_const a (0 : ℂ)).mul_const a)
    simpa [ψ, pow_two, Function.comp_def] using hh.deriv
  have h := gkz_entire_second_deriv hd h0 hne (norm_nonneg a) hgrowth
  rwa [hfirst, hsecond] at h

/-- Gleason–Kahane–Żelazko, with continuity and the algebraic character
property both conclusions, for arbitrary noncommutative unital Banach algebras. -/
theorem gleason_kahane_zelazko :
    Specs.ExpandedFA.BanachAlgebra.GleasonKahaneZelazko.GleasonKahaneZelazko.{u} := by
  intro A _ _ hA φ h1 hunit
  let : CompleteSpace A := hA.1
  let : NormOneClass A := hA.2.2
  refine ⟨(φ.mkContinuous 1 (fun x => by simpa using gkz_norm_le φ h1 hunit x)).continuous,
    ?_, gkz_multiplicative_of_squares φ h1 (gkz_preserves_squares φ h1 hunit)⟩
  intro hz
  have h := congrArg (fun f : A →ₗ[ℂ] ℂ => f 1) hz
  simp [h1] at h

end ExpandedFA.BanachAlgebra
