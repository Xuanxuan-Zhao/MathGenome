import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.BoundedUnivalent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.OpenMapping
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace D12Complex.BoundedUnivalent

/-- Taking a square root of a translated identity gives an injection whose
image cannot contain both a value and its negative. -/
private theorem root_properties {Ω : Set ℂ} {a : ℂ} (ha : a ∉ Ω)
    {g : ℂ → ℂ} (hsq : ∀ z ∈ Ω, (g z) ^ 2 = z - a) :
    InjOn g Ω ∧ (∀ z ∈ Ω, g z ≠ 0) ∧
    ∀ z ∈ Ω, ∀ w ∈ Ω, g z ≠ -g w := by
  have hinj : InjOn g Ω := by
    intro z hz w hw heq
    have := (hsq z hz).symm.trans ((congrArg (fun u : ℂ => u ^ 2) heq).trans (hsq w hw))
    exact sub_left_injective this
  have hnz : ∀ z ∈ Ω, g z ≠ 0 := by
    intro z hz heq
    have hza : z = a := sub_eq_zero.mp (by simpa [heq] using (hsq z hz).symm)
    exact ha (hza ▸ hz)
  refine ⟨hinj, hnz, ?_⟩
  intro z hz w hw heq
  have hzw : z = w := by
    apply sub_left_injective (b := a)
    change z - a = w - a
    rw [← hsq z hz, ← hsq w hw, heq, neg_sq]
  have hzero : g w = 0 := by
    rw [hzw] at heq
    have : 2 * g w = 0 := by linear_combination heq
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  exact hnz w hw hzero

/-- The derivative of the square-root injection cannot vanish, directly by
differentiating its square on the open domain. -/
private theorem root_deriv_ne_zero {Ω : Set ℂ} {a z₀ : ℂ} {g : ℂ → ℂ}
    (hg : HolomorphicOn Ω g) (hz₀ : z₀ ∈ Ω)
    (hsq : ∀ z ∈ Ω, (g z) ^ 2 = z - a) : deriv g z₀ ≠ 0 := by
  have hd := ((hg.2 z₀ hz₀).hasDerivAt.pow 2)
  have hid : HasDerivAt (fun z : ℂ => z - a) 1 z₀ := by
    simpa using (hasDerivAt_id z₀).sub_const a
  have hid' := hid.congr_of_eventuallyEq
    (show (fun z => (g z) ^ 2) =ᶠ[𝓝 z₀] (fun z => z - a) from
      Filter.mem_of_superset (hg.1.mem_nhds hz₀) (fun z hz => hsq z hz))
  have heq := hd.unique hid'
  intro hzero
  simp [hzero] at heq

/-- Rotate a bounded injection after translating and shrinking it. -/
private theorem normalize {Ω : Set ℂ} {q : ℂ → ℂ} {z₀ : ℂ} {M : ℝ}
    (hq : HolomorphicOn Ω q) (hinj : InjOn q Ω) (hz₀ : z₀ ∈ Ω)
    (hM : 0 < M) (hbound : ∀ z ∈ Ω, ‖q z‖ ≤ M)
    (hd : deriv q z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, HolomorphicOn Ω h ∧ InjOn h Ω ∧
      MapsTo h Ω (Metric.ball 0 1) ∧ h z₀ = 0 ∧
      ∃ t : ℝ, 0 < t ∧ deriv h z₀ = (t : ℂ) := by
  let d := deriv q z₀
  let c : ℂ := (‖d‖ : ℂ) / d
  let k : ℝ := 1 / (4 * M)
  have hd' : d ≠ 0 := hd
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd'
  have hc : ‖c‖ = 1 := by
    simp [c, Complex.norm_real, ne_of_gt hdn]
  have hcn : c ≠ 0 := by
    intro hzero
    simp [hzero] at hc
  have hk : 0 < k := one_div_pos.mpr (mul_pos (by norm_num) hM)
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hk)
  let h : ℂ → ℂ := fun z => c * ((k : ℂ) * (q z - q z₀))
  have hder : HasDerivAt h ((k * ‖d‖ : ℝ) : ℂ) z₀ := by
    have hh := (((hq.2 z₀ hz₀).hasDerivAt.sub_const (q z₀)).const_mul
      (k : ℂ)).const_mul c
    have hcanc : c * ((k : ℂ) * deriv q z₀) = ((k * ‖d‖ : ℝ) : ℂ) := by
      dsimp [c, d]
      push_cast
      field_simp
    exact hcanc ▸ hh
  refine ⟨h, ⟨hq.1, ?_⟩, ?_, ?_, ?_, k * ‖d‖, mul_pos hk hdn, hder.deriv⟩
  · intro z hz
    exact ((((hq.2 z hz).sub_const (q z₀)).const_mul (k : ℂ)).const_mul c)
  · intro z hz w hw heq
    apply hinj hz hw
    have heq' := mul_left_cancel₀ hcn heq
    have heq'' := mul_left_cancel₀ hkc heq'
    exact sub_left_injective heq''
  · intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hdiff : ‖q z - q z₀‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [hbound z hz, hbound z₀ hz₀])
    have hnorm : ‖h z‖ = k * ‖q z - q z₀‖ := by
      simp only [h, norm_mul, hc, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk]
    rw [hnorm]
    calc
      k * ‖q z - q z₀‖ ≤ k * (2 * M) := mul_le_mul_of_nonneg_left hdiff hk.le
      _ = 1 / 2 := by
        dsimp [k]
        field_simp [ne_of_gt hM]
        norm_num
      _ < 1 := by norm_num
  · simp [h]

/-- The bounded univalent class exists under precisely the universal
square-root premise, before any extremal or simple-connectivity argument. -/
theorem bounded_univalent :
    Specs.D12Complex.Ch12.BoundedUnivalent.bounded_univalent_type := by
  intro Ω hΩ hproper hroot z₀ hz₀
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a ∉ Ω := by
    by_contra h
    apply hproper
    exact Set.eq_univ_of_forall (by simpa using h)
  have hlin : HolomorphicOn Ω (fun z : ℂ => z - a) :=
    ⟨hΩ.2.1, fun z _ => (differentiableAt_id.sub_const a)⟩
  have hnz : ∀ z ∈ Ω, z - a ≠ 0 := by
    intro z hz heq
    exact ha (sub_eq_zero.mp heq ▸ hz)
  obtain ⟨g, hg, hsq⟩ := hroot (fun z => z - a) hlin hnz
  obtain ⟨hginj, hgnz, hneg⟩ := root_properties ha hsq
  have hnc : ¬ ∃ c : ℂ, ∀ z ∈ Ω, g z = c := by
    rintro ⟨c, hc⟩
    have hderzero : HasDerivAt g 0 z₀ :=
      (hasDerivAt_const z₀ c).congr_of_eventuallyEq
        (Filter.mem_of_superset (hg.1.mem_nhds hz₀) (fun z hz => hc z hz))
    exact root_deriv_ne_zero hg hz₀ hsq hderzero.deriv
  obtain ⟨r, hr, hball⟩ := OpenMapping.exists_image_ball_of_nonconstant
    Ω g hΩ hg hnc Ω hg.1 Subset.rfl z₀ hz₀
  let b := g z₀
  have hden : ∀ z ∈ Ω, g z + b ≠ 0 := by
    intro z hz heq
    exact hneg z hz z₀ hz₀ (add_eq_zero_iff_eq_neg.mp heq)
  have hdist : ∀ z ∈ Ω, r ≤ ‖g z + b‖ := by
    intro z hz
    by_contra h
    have hmem : -g z ∈ Metric.ball (g z₀) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa only [sub_eq_add_neg, ← neg_add, norm_neg] using lt_of_not_ge h
    obtain ⟨w, hw, hweq⟩ := hball hmem
    exact hneg w hw z hz hweq
  let q : ℂ → ℂ := fun z => (g z + b)⁻¹
  have hq : HolomorphicOn Ω q :=
    ⟨hg.1, fun z hz => ((hg.2 z hz).add_const b).inv (hden z hz)⟩
  have hqinj : InjOn q Ω := by
    intro z hz w hw heq
    exact hginj hz hw (add_right_cancel (inv_injective heq))
  have hqbound : ∀ z ∈ Ω, ‖q z‖ ≤ 1 / r := by
    intro z hz
    simpa only [q, norm_inv, one_div] using inv_anti₀ hr (hdist z hz)
  have hqd : deriv q z₀ ≠ 0 := by
    have hder := (((hg.2 z₀ hz₀).hasDerivAt).add_const b).inv (hden z₀ hz₀)
    have heq : deriv q z₀ = -deriv g z₀ / (g z₀ + b) ^ 2 := hder.deriv
    rw [heq]
    exact div_ne_zero (neg_ne_zero.mpr (root_deriv_ne_zero hg hz₀ hsq))
      (pow_ne_zero 2 (hden z₀ hz₀))
  exact normalize hq hqinj hz₀ (one_div_pos.mpr hr) hqbound hqd

end D12Complex.BoundedUnivalent
