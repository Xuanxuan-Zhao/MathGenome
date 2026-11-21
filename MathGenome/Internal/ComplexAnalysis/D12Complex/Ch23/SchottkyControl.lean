import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.SchottkyControl
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.OmittedValuesTransform
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.AuxiliaryDerivativeBound
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Schottky control with the explicit source constant (paper.tex:4213–4245).
The two logarithms are normalized at the center before bounding the
auxiliary transform. Its already proved radial estimate then controls
f, and reflection f ↦ 1-f covers small center values.
-/
noncomputable section

namespace D12Complex.SchottkyControl
open Metric Set

def Astar (A : ℝ) : ℝ := max 2 A

def C0 (A : ℝ) : ℝ := 1 + Real.log (Astar A) / (2 * Real.pi)

def K (A : ℝ) : ℝ := Real.sqrt (C0 A) + Real.sqrt (C0 A + 1)

def C (A r : ℝ) : ℝ :=
  1 + Real.exp (Real.pi * Real.exp
    (2 * (Real.log (K A) + Real.pi + 128 * r / (1 - r))))


lemma normalize_holomorphic_log {Ω : Set ℂ} {f L : ℂ → ℂ} {a : ℂ}
    (ha : a ∈ Ω) (hfzero : f a ≠ 0)
    (hL : HolomorphicOn Ω L)
    (hLexp : ∀ z ∈ Ω, Complex.exp (L z) = f z) :
    ∃ t : ℂ → ℂ, HolomorphicOn Ω t ∧
      (∀ z ∈ Ω, Complex.exp (t z) = f z) ∧
      t a = Complex.log (f a) := by
  refine ⟨fun z => L z + (Complex.log (f a) - L a),
    ⟨hL.1, fun z hz => (hL.2 z hz).add_const _⟩, ?_, ?_⟩
  · intro z hz
    rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log hfzero,
      hLexp a ha, hLexp z hz, div_self hfzero, mul_one]
  · ring

lemma exists_centered_log (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ)
    (hΩ : IsDomain Ω) (hsc : IsSimplyConnected Ω) (ha : a ∈ Ω)
    (hf : HolomorphicOn Ω f) (hzero : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ t : ℂ → ℂ, HolomorphicOn Ω t ∧
      (∀ z ∈ Ω, Complex.exp (t z) = f z) ∧ t a = Complex.log (f a) := by
  obtain ⟨L, hL, hLexp⟩ :=
    SimplyConnectedCalculus.exists_logarithm Ω f hΩ hsc hf hzero
  have hLexp' : ∀ z ∈ Ω, Complex.exp (L z) = f z := by
    intro z hz
    exact (congrFun Exponential.E_eq_exp (L z)).symm.trans (hLexp z hz)
  exact normalize_holomorphic_log ha (hzero a ha) hL hLexp'

lemma exists_centered_transform (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ)
    (hΩ : IsDomain Ω) (hsc : IsSimplyConnected Ω) (ha : a ∈ Ω)
    (hf : HolomorphicOn Ω f) (hzero : ∀ z ∈ Ω, f z ≠ 0)
    (hone : ∀ z ∈ Ω, f z ≠ 1) :
    ∃ t F A B g : ℂ → ℂ,
      HolomorphicOn Ω g ∧
      (∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
        Complex.cosh (2 * g z))) ∧
      t a = Complex.log (f a) ∧ g a = Complex.log (A a - B a) ∧
      (∀ z ∈ Ω, Complex.exp (t z) = f z) ∧
      (∀ z ∈ Ω, F z = t z / (2 * (Real.pi : ℂ) * Complex.I)) ∧
      (∀ z ∈ Ω, A z ^ 2 = F z) ∧
      (∀ z ∈ Ω, B z ^ 2 = F z - 1) ∧
      (∀ z ∈ Ω, Complex.exp (g z) = A z - B z) := by
  obtain ⟨t, ht, hexpt, hta⟩ := exists_centered_log Ω f a hΩ hsc ha hf hzero
  let F : ℂ → ℂ := fun z => t z / (2 * (Real.pi : ℂ) * Complex.I)
  have hF : HolomorphicOn Ω F :=
    ⟨ht.1, fun z hz => (ht.2 z hz).div_const _⟩
  have hFint : ∀ z ∈ Ω, ∀ k : ℤ, F z ≠ (k : ℂ) := by
    intro z hz k hk
    apply hone z hz
    rw [← hexpt z hz]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨k, ?_⟩
    exact (div_eq_iff OmittedValuesTransform.two_pi_I_ne_zero).mp hk
  have hFzero : ∀ z ∈ Ω, F z ≠ 0 := by
    intro z hz
    simpa only [Int.cast_zero] using hFint z hz 0
  have hFone : ∀ z ∈ Ω, F z - 1 ≠ 0 := by
    intro z hz h
    exact hFint z hz 1 (by simpa using sub_eq_zero.mp h)
  obtain ⟨A, hA, hAsq⟩ :=
    SimplyConnectedCalculus.exists_root Ω F hΩ hsc hF hFzero 2 (by norm_num)
  have hFm : HolomorphicOn Ω (fun z => F z - 1) :=
    ⟨hF.1, fun z hz => (hF.2 z hz).sub_const _⟩
  obtain ⟨B, hB, hBsq⟩ :=
    SimplyConnectedCalculus.exists_root Ω _ hΩ hsc hFm hFone 2 (by norm_num)
  let H : ℂ → ℂ := fun z => A z - B z
  have hH : HolomorphicOn Ω H :=
    ⟨hA.1, fun z hz => (hA.2 z hz).sub (hB.2 z hz)⟩
  have hprod : ∀ z ∈ Ω, H z * (A z + B z) = 1 := by
    intro z hz
    exact OmittedValuesTransform.roots_product (hAsq z hz) (hBsq z hz)
  have hHzero : ∀ z ∈ Ω, H z ≠ 0 := by
    intro z hz h
    have := hprod z hz
    simp [h] at this
  obtain ⟨g, hg, hexpg, hga⟩ := exists_centered_log Ω H a hΩ hsc ha hH hHzero
  refine ⟨t, F, A, B, g, hg, ?_, hta, hga, hexpt,
    (fun _ _ => rfl), hAsq, hBsq, hexpg⟩
  intro z hz
  exact OmittedValuesTransform.transform_identity (hexpt z hz) rfl
    (OmittedValuesTransform.cosh_of_roots (hAsq z hz) (hBsq z hz) (hexpg z hz))

lemma abs_log_norm_le {A : ℝ} {w : ℂ}
    (hlow : (1 / 2 : ℝ) ≤ ‖w‖) (hup : ‖w‖ ≤ max 2 A) :
    |Real.log ‖w‖| ≤ Real.log (max 2 A) := by
  have hwpos : 0 < ‖w‖ := by linarith
  have htwo : Real.log 2 ≤ Real.log (max 2 A) :=
    Real.log_le_log (by norm_num) (le_max_left _ _)
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlow
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at hlo
  exact abs_le.mpr ⟨by linarith, Real.log_le_log hwpos hup⟩

lemma center_F_bound {A : ℝ} {w t : ℂ}
    (hlow : (1 / 2 : ℝ) ≤ ‖w‖) (hup : ‖w‖ ≤ max 2 A)
    (ht : Complex.exp t = w) (htim : |t.im| ≤ Real.pi) :
    ‖t / (2 * (Real.pi : ℂ) * Complex.I)‖ ≤
      1 + Real.log (max 2 A) / (2 * Real.pi) := by
  have htre : t.re = Real.log ‖w‖ := by
    rw [← ht, Complex.norm_exp, Real.log_exp]
  have htbound : ‖t‖ ≤ Real.log (max 2 A) + Real.pi := by
    have hn := Complex.norm_le_abs_re_add_abs_im t
    rw [htre] at hn
    linarith [abs_log_norm_le hlow hup]
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp
  rw [norm_div, hden]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  have hcancel : (1 + Real.log (max 2 A) / (2 * Real.pi)) * (2 * Real.pi) =
      2 * Real.pi + Real.log (max 2 A) := by
    field_simp
  rw [hcancel]
  linarith [Real.pi_pos]

lemma roots_norm_bounds {C : ℝ} {a b F : ℂ}
    (hC : 0 ≤ C) (hF : ‖F‖ ≤ C) (ha : a ^ 2 = F) (hb : b ^ 2 = F - 1) :
    ‖a - b‖ ≤ Real.sqrt C + Real.sqrt (C + 1) ∧
    ‖a + b‖ ≤ Real.sqrt C + Real.sqrt (C + 1) := by
  have haNorm : ‖a‖ ≤ Real.sqrt C := by
    apply (Real.le_sqrt (norm_nonneg _) hC).mpr
    rw [← norm_pow, ha]
    exact hF
  have hbNorm : ‖b‖ ≤ Real.sqrt (C + 1) := by
    apply (Real.le_sqrt (norm_nonneg _) (by linarith)).mpr
    rw [← norm_pow, hb]
    simpa using (norm_sub_le F 1).trans (by simpa using add_le_add_right hF 1)
  exact ⟨(norm_sub_le _ _).trans (add_le_add haNorm hbNorm),
    (norm_add_le _ _).trans (add_le_add haNorm hbNorm)⟩

lemma logarithm_bound_of_roots {K : ℝ} {a b F g : ℂ}
    (hK : 0 < K) (ha : a ^ 2 = F) (hb : b ^ 2 = F - 1)
    (hminus : ‖a - b‖ ≤ K) (hplus : ‖a + b‖ ≤ K)
    (hg : Complex.exp g = a - b) (hgim : |g.im| ≤ Real.pi) :
    ‖g‖ ≤ Real.log K + Real.pi := by
  have hprod : (a - b) * (a + b) = 1 := by
    linear_combination ha - hb
  have he : Complex.exp (-g) = a + b := by
    apply (mul_left_cancel₀ (Complex.exp_ne_zero g))
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, hg, hprod]
  have hre : g.re ≤ Real.log K := (Real.le_log_iff_exp_le hK).mpr (by
    rw [← Complex.norm_exp, hg]
    exact hminus)
  have hre' : -g.re ≤ Real.log K := (Real.le_log_iff_exp_le hK).mpr (by
    rw [← Complex.neg_re, ← Complex.norm_exp, he]
    exact hplus)
  have habs : |g.re| ≤ Real.log K := abs_le.mpr ⟨by linarith, hre⟩
  exact (Complex.norm_le_abs_re_add_abs_im g).trans (add_le_add habs hgim)

lemma center_auxiliary_bound {A : ℝ} {w t F a b g : ℂ}
    (hlow : (1 / 2 : ℝ) ≤ ‖w‖) (hup : ‖w‖ ≤ max 2 A)
    (ht : Complex.exp t = w) (htim : |t.im| ≤ Real.pi)
    (hF : F = t / (2 * (Real.pi : ℂ) * Complex.I))
    (ha : a ^ 2 = F) (hb : b ^ 2 = F - 1)
    (hg : Complex.exp g = a - b) (hgim : |g.im| ≤ Real.pi) :
    ‖g‖ ≤ Real.log
      (Real.sqrt (1 + Real.log (max 2 A) / (2 * Real.pi)) +
       Real.sqrt ((1 + Real.log (max 2 A) / (2 * Real.pi)) + 1)) + Real.pi := by
  let C : ℝ := 1 + Real.log (max 2 A) / (2 * Real.pi)
  have hlog : 0 ≤ Real.log (max 2 A) := Real.log_nonneg (by linarith [le_max_left (2:ℝ) A])
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [div_nonneg hlog (by positivity : 0 ≤ 2 * Real.pi)]
  have hK : 0 < Real.sqrt C + Real.sqrt (C + 1) :=
    add_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
  have hFnorm : ‖F‖ ≤ C := by
    rw [hF]
    exact center_F_bound hlow hup ht htim
  obtain ⟨hm, hp⟩ := roots_norm_bounds (by linarith : 0 ≤ C) hFnorm ha hb
  exact logarithm_bound_of_roots hK ha hb hm hp hg hgim

lemma abs_log_im_le_pi (w : ℂ) : |(Complex.log w).im| ≤ Real.pi := by
  simpa only [Complex.log_im] using Complex.abs_arg_le_pi w

lemma reflected_center_bound {A : ℝ} {w : ℂ} (hw : ‖w‖ < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖1 - w‖ ∧ ‖1 - w‖ ≤ max 2 A := by
  have hl := norm_le_norm_sub_add (1 : ℂ) w
  have hu := norm_sub_le (1 : ℂ) w
  norm_num at hl hu
  constructor
  · linarith
  · have hm := le_max_left (2 : ℝ) A
    linarith

lemma norm_cosh_le_exp_norm (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.cosh, norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have h₁ := Complex.norm_exp_le_exp_norm w
  have h₂ := Complex.norm_exp_le_exp_norm (-w)
  rw [norm_neg] at h₂
  linarith [norm_add_le (Complex.exp w) (Complex.exp (-w))]

lemma norm_transform_le (g : ℂ) :
    ‖-Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g))‖ ≤
      Real.exp (Real.pi * Real.exp (2 * ‖g‖)) := by
  rw [norm_neg]
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  calc
    ‖(Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g)‖ =
      Real.pi * ‖Complex.cosh (2 * g)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
          Complex.norm_I, mul_one]
    _ ≤ Real.pi * Real.exp ‖(2 : ℂ) * g‖ :=
      mul_le_mul_of_nonneg_left (norm_cosh_le_exp_norm _) Real.pi_pos.le
    _ = Real.pi * Real.exp (2 * ‖g‖) := by rw [norm_mul]; norm_num

lemma bound_on_disk_of_unit_bound {A C r : ℝ}
    (hunit : ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
      (∀ w ∈ ball (0 : ℂ) 1, f w ≠ 0) →
      (∀ w ∈ ball (0 : ℂ) 1, f w ≠ 1) → ‖f 0‖ ≤ A →
      ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ C)
    (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (hR : 0 < R)
    (hf : HolomorphicOn (ball a R) f)
    (hzero : ∀ z ∈ ball a R, f z ≠ 0)
    (hone : ∀ z ∈ ball a R, f z ≠ 1) (hcenter : ‖f a‖ ≤ A)
    (z : ℂ) (hz : ‖z - a‖ ≤ r * R) : ‖f z‖ ≤ C := by
  let F : ℂ → ℂ := fun w => f (a + (R : ℂ) * w)
  have hmap : ∀ w ∈ ball (0 : ℂ) 1, a + (R : ℂ) * w ∈ ball a R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
    nlinarith
  have hF : HolomorphicOn (ball 0 1) F := by
    refine ⟨isOpen_ball, fun w hw => ?_⟩
    exact (hf.2 _ (hmap w hw)).comp w
      ((differentiableAt_const a).add ((differentiableAt_const (R : ℂ)).mul
        differentiableAt_id))
  have hbound := hunit F hF (fun w hw => hzero _ (hmap w hw))
    (fun w hw => hone _ (hmap w hw)) (by simpa [F] using hcenter)
    ((z - a) / (R : ℂ)) (by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
      exact (div_le_iff₀ hR).mpr hz)
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hid : a + (R : ℂ) * ((z - a) / (R : ℂ)) = z := by
    rw [mul_div_cancel₀ _ hRc]
    exact add_sub_cancel _ _
  simpa [F, hid] using hbound

/-- The source constant is a finite real number, and is larger than one. -/
theorem constant_gt_one : ∀ A r : ℝ, 1 < C A r := by
  intro A r
  exact lt_add_of_pos_right 1 (Real.exp_pos _)

/-- Choose both global logarithms with principal values at the center. -/
lemma exists_bounded_transform (A : ℝ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (ball 0 1) f)
    (hzero : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (hone : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hlow : (1 / 2 : ℝ) ≤ ‖f 0‖) (hup : ‖f 0‖ ≤ Astar A) :
    ∃ g : ℂ → ℂ, HolomorphicOn (ball 0 1) g ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        f z = -Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g z))) ∧
      ‖g 0‖ ≤ Real.log (K A) + Real.pi := by
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hne : (ball (0 : ℂ) 1).Nonempty := ⟨0, h0⟩
  have hΩ : IsDomain (ball (0 : ℂ) 1) :=
    ⟨hne, isOpen_ball, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  let : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace hne
  have hsc : IsSimplyConnected (ball (0 : ℂ) 1) := by
    change SimplyConnectedSpace (ball (0 : ℂ) 1)
    infer_instance
  obtain ⟨t, F, U, V, g, hg, hfg, ht0, hg0, ht, hF, hU, hV, hexpg⟩ :=
    exists_centered_transform (ball 0 1) f 0 hΩ hsc h0 hf hzero hone
  refine ⟨g, hg, hfg, ?_⟩
  have htim : |(t 0).im| ≤ Real.pi := by
    rw [ht0]
    exact abs_log_im_le_pi _
  have hgim : |(g 0).im| ≤ Real.pi := by
    rw [hg0]
    exact abs_log_im_le_pi _
  simpa only [K, C0, Astar] using
    center_auxiliary_bound hlow hup (ht 0 h0) htim (hF 0 h0)
      (hU 0 h0) (hV 0 h0) (hexpg 0 h0) hgim

/-- The estimate before reflection, with no harmless extra one. -/
lemma bound_of_center_lower (A r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (f : ℂ → ℂ) (hf : HolomorphicOn (ball 0 1) f)
    (hzero : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0)
    (hone : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    (hlow : (1 / 2 : ℝ) ≤ ‖f 0‖) (hup : ‖f 0‖ ≤ Astar A)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ Real.exp (Real.pi * Real.exp
      (2 * (Real.log (K A) + Real.pi + 128 * r / (1 - r)))) := by
  obtain ⟨g, hg, hfg, hg0⟩ := exists_bounded_transform A f hf hzero hone hlow hup
  have hzD : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt hr1)
  have hgrowth := AuxiliaryDerivativeBound.radial_bound f g hf hzero hone hg hfg
    r hr hr1 z hz
  have hgb : ‖g z‖ ≤ Real.log (K A) + Real.pi + 128 * r / (1 - r) := by
    linarith
  rw [hfg z hzD]
  apply (norm_transform_le (g z)).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgb (by norm_num))

theorem unit_disk :
    ∀ (A r : ℝ), 0 < A → 0 ≤ r → r < 1 →
      ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
        (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
        (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
        ‖f 0‖ ≤ A → ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ C A r := by
  intro A r _hA hr hr1 f hf hzero hone hcenter z hz
  by_cases hlow : (1 / 2 : ℝ) ≤ ‖f 0‖
  · have hb := bound_of_center_lower A r hr hr1 f hf hzero hone hlow
      (hcenter.trans (le_max_right _ _)) z hz
    exact hb.trans (by dsimp [C]; linarith)
  · let F : ℂ → ℂ := fun w => 1 - f w
    have hF : HolomorphicOn (ball 0 1) F :=
      ⟨isOpen_ball, fun w hw => (hf.2 w hw).const_sub 1⟩
    have hFzero : ∀ w ∈ ball (0 : ℂ) 1, F w ≠ 0 := by
      intro w hw heq
      exact hone w hw (sub_eq_zero.mp heq).symm
    have hFone : ∀ w ∈ ball (0 : ℂ) 1, F w ≠ 1 := by
      intro w hw heq
      apply hzero w hw
      dsimp [F] at heq
      linear_combination -heq
    obtain ⟨hFlow, hFup⟩ := reflected_center_bound (A := A) (lt_of_not_ge hlow)
    have hb := bound_of_center_lower A r hr hr1 F hF hFzero hFone hFlow hFup z hz
    have htri : ‖f z‖ ≤ 1 + ‖F z‖ := by
      have heq : f z = 1 - F z := by dsimp [F]; ring
      rw [heq]
      simpa using norm_sub_le (1 : ℂ) (F z)
    exact htri.trans (by dsimp [C]; linarith)

theorem scaled :
    ∀ (a : ℂ) (R A r : ℝ), 0 < R → 0 < A → 0 ≤ r → r < 1 →
      ∀ f : ℂ → ℂ, HolomorphicOn (ball a R) f →
        (∀ z ∈ ball a R, f z ≠ 0) →
        (∀ z ∈ ball a R, f z ≠ 1) →
        ‖f a‖ ≤ A → ∀ z : ℂ, ‖z - a‖ ≤ r * R → ‖f z‖ ≤ C A r := by
  intro a R A r hR hA hr hr1 f hf hzero hone hcenter z hz
  exact bound_on_disk_of_unit_bound (unit_disk A r hA hr hr1)
    a R f hR hf hzero hone hcenter z hz

end D12Complex.SchottkyControl
