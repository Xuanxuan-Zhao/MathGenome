import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.OmittedValuesTransform
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.SimplyConnectedCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The global logarithm–square-root construction in d12:23:auxiliary.
Only zero-free functions are passed to the simply-connected logarithm and
root theorems. The final identity follows from exp(-g)=A+B and the
exponential formula for cosh. -/
noncomputable section

namespace D12Complex.OmittedValuesTransform

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- The two roots give inverse nonzero factors without choosing their signs. -/
lemma roots_product {a b F : ℂ} (ha : a ^ 2 = F) (hb : b ^ 2 = F - 1) :
    (a - b) * (a + b) = 1 := by
  linear_combination ha - hb

/-- The exponential of the negative logarithm is the other root factor. -/
lemma cosh_of_roots {a b F g : ℂ} (ha : a ^ 2 = F) (hb : b ^ 2 = F - 1)
    (hg : Complex.exp g = a - b) : Complex.cosh (2 * g) = 2 * F - 1 := by
  have hp := roots_product ha hb
  have he : Complex.exp (-g) = a + b := by
    apply (mul_left_cancel₀ (Complex.exp_ne_zero g))
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, hg, hp]
  rw [Complex.cosh, show -(2 * g) = 2 * (-g) by ring,
    show Complex.exp (2 * g) = Complex.exp g ^ 2 from Complex.exp_nat_mul g 2,
    show Complex.exp (2 * (-g)) = Complex.exp (-g) ^ 2 from
      Complex.exp_nat_mul (-g) 2, hg, he]
  linear_combination ha + hb

lemma transform_identity {t F g f : ℂ}
    (ht : Complex.exp t = f) (hF : F = t / (2 * (Real.pi : ℂ) * Complex.I))
    (hc : Complex.cosh (2 * g) = 2 * F - 1) :
    f = -Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g)) := by
  have harg : (Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g) =
      t - (Real.pi : ℂ) * Complex.I := by
    rw [hc, hF]
    field_simp
  rw [harg, Complex.exp_sub, Complex.exp_pi_mul_I, ht]
  ring

theorem exists_transform_construction :
    Specs.D12Complex.Ch23.OmittedValuesTransform.exists_transform_construction_type := by
  intro Ω f hΩ hsc hf hzero hone
  obtain ⟨t, ht, hexpt⟩ := SimplyConnectedCalculus.exists_logarithm Ω f hΩ hsc hf hzero
  have hexpt' : ∀ z ∈ Ω, Complex.exp (t z) = f z := by
    intro z hz
    exact (congrFun Exponential.E_eq_exp (t z)).symm.trans (hexpt z hz)
  let F : ℂ → ℂ := fun z => t z / (2 * (Real.pi : ℂ) * Complex.I)
  have hF : HolomorphicOn Ω F :=
    ⟨ht.1, fun z hz => (ht.2 z hz).div_const _⟩
  have hFint : ∀ z ∈ Ω, ∀ k : ℤ, F z ≠ (k : ℂ) := by
    intro z hz k hk
    apply hone z hz
    rw [← hexpt' z hz]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨k, ?_⟩
    exact (div_eq_iff two_pi_I_ne_zero).mp hk
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
    exact roots_product (hAsq z hz) (hBsq z hz)
  have hHzero : ∀ z ∈ Ω, H z ≠ 0 := by
    intro z hz h
    have := hprod z hz
    simp [h] at this
  obtain ⟨g, hg, hexpg⟩ :=
    SimplyConnectedCalculus.exists_logarithm Ω H hΩ hsc hH hHzero
  have hexpg' : ∀ z ∈ Ω, Complex.exp (g z) = H z := by
    intro z hz
    exact (congrFun Exponential.E_eq_exp (g z)).symm.trans (hexpg z hz)
  have hcosh : ∀ z ∈ Ω, Complex.cosh (2 * g z) = 2 * F z - 1 := by
    intro z hz
    exact cosh_of_roots (hAsq z hz) (hBsq z hz) (hexpg' z hz)
  refine ⟨t, F, A, B, H, g, ht, hF, hA, hB, hH, hg, hexpt',
    (fun _ _ => rfl), hFint, hAsq, hBsq, (fun _ _ => rfl),
    hprod, hHzero, hexpg', hcosh, ?_⟩
  intro z hz
  exact transform_identity (hexpt' z hz) rfl (hcosh z hz)

theorem exists_transform :
    Specs.D12Complex.Ch23.OmittedValuesTransform.exists_transform_type := by
  intro Ω f hΩ hsc hf hzero hone
  obtain ⟨t, F, A, B, H, g, _, _, _, _, _, hg, _, _, _, _, _, _, _, _, _, _, hfg⟩ :=
    exists_transform_construction Ω f hΩ hsc hf hzero hone
  exact ⟨g, hg, hfg⟩

end D12Complex.OmittedValuesTransform
