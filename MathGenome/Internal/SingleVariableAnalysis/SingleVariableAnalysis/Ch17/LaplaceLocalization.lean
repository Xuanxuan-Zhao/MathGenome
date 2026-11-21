import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.Peano
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Fermat
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ExtremeValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace SingleVariableAnalysis
open Set Filter Asymptotics
open scoped Topology
namespace LaplaceLocalization

theorem stationary : Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.stationary := by
  intro φ a b x₀ hφ hx hmin
  have hn : Icc a b ∈ 𝓝 x₀ := Icc_mem_nhds hx.1 hx.2
  have hm : IsMinOn φ (Icc a b) x₀ := by
    intro x hxi
    by_cases he : x = x₀
    · subst x; change φ x₀ ≤ φ x₀; exact le_rfl
    · exact (hmin x hxi he).le
  exact (hm.isLocalMin hn).hasDerivAt_eq_zero
    ((hφ.contDiffAt hn).differentiableAt (by norm_num)).hasDerivAt

theorem quadraticPeano : Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.quadraticPeano := by
  intro φ a b x₀ hφ hx hmin
  have ho := (ckOn_iff_contDiffOn 2 φ (Ioo a b) isOpen_Ioo).mpr
    (hφ.mono Ioo_subset_Icc_self)
  have hn : ∃ U ∈ 𝓝 x₀, KTimesDifferentiableOn (2-1) φ U := by
    refine ⟨Ioo a b, isOpen_Ioo.mem_nhds hx, ?_⟩
    intro j hj x hxi
    exact ho.1 j (by omega) x hxi
  have ht := taylor_peano φ 2 x₀ (by norm_num) hn (ho.1 1 (by norm_num) x₀ hx)
  have hs := stationary φ a b x₀ hφ hx hmin
  simp [Finset.sum_range_succ, RealIteratedDerivative,
    iteratedDeriv_succ, hs] at ht
  convert ht using 1
  ext h
  ring


theorem localLower : Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.localLower := by
  intro φ a b x₀ hφ hx hmin hd
  have he := (quadraticPeano φ a b x₀ hφ hx hmin).def (div_pos hd (by norm_num : (0:ℝ)<4))
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhdsWithin_iff.mp he
  let r := min (δ/2) (min ((x₀-a)/2) ((b-x₀)/2))
  have hr : 0 < r := lt_min (half_pos hδ)
    (lt_min (half_pos (sub_pos.mpr hx.1)) (half_pos (sub_pos.mpr hx.2)))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hra : r ≤ (x₀-a)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ (b-x₀)/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, by linarith [hx.1], by linarith [hx.2], ?_⟩
  intro h hh
  by_cases hz : h = 0
  · simp [hz]
  have hi : h ∈ Metric.ball 0 δ ∩ ({0} : Set ℝ)ᶜ := by
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hh.trans_lt hrδ, by simpa⟩
  have ht := hb hi
  change ‖φ (x₀+h) - φ x₀ - deriv (deriv φ) x₀ * h^2 / 2‖ ≤
    deriv (deriv φ) x₀ / 4 * ‖h^2‖ at ht
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)] at ht
  have ht' := (abs_le.mp ht).1
  nlinarith

theorem exteriorGap : Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.exteriorGap := by
  intro φ a b x₀ hφ hx hmin r hr
  let E : Set ℝ := Icc a b ∩ {x : ℝ | r ≤ |x-x₀|}
  have hE : IsCompact E := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  by_cases hne : E.Nonempty
  · obtain ⟨y, hy, hmy⟩ := hE.exists_isMinOn hne (hφ.mono inter_subset_left)
    have hyne : y ≠ x₀ := by
      intro heq
      have := hy.2
      simp [heq] at this
      linarith
    refine ⟨φ y - φ x₀, sub_pos.mpr (hmin y hy.1 hyne), ?_⟩
    intro x hxi hxr
    have hm : φ y ≤ φ x := hmy (show x ∈ E from ⟨hxi, hxr⟩)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hxi hxr
    exact False.elim (hne ⟨x, hxi, hxr⟩)


open Riemann
local notation "S" => Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.scalarRCLike

/-- Continuity implies Darboux integrability for the two canonical scalars. -/
theorem scalar_continuous_integrable (k : ScalarKind) :
    letI := S k
    ∀ (f : ℝ → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k)
      (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) → Integrable k f a b := by
  cases k with
  | real =>
    change ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) → RealIntegrable f a b
    intro f a b hab hf
    apply real_continuous_integrable f hab
    intro x hx
    exact (relativeContinuousAt_within_iff f (Icc a b) x).mpr (hf x hx)
  | complex =>
    change ∀ (f : ℝ → ℂ) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) → ComplexIntegrable f a b
    intro f a b hab hf
    apply complex_continuous_integrable f hab
    intro x hx
    exact (relativeContinuousAt_within_iff f (Icc a b) x).mpr (hf x hx)

/-- The same length-times-bound estimate in both scalar fields. -/
theorem scalar_integral_norm_le (k : ScalarKind) :
    letI := S k
    ∀ (f : ℝ → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k)
      {a b M : ℝ} (hf : Integrable k f a b),
      (∀ x ∈ Icc a b, ‖f x‖ ≤ M) → ‖integral k f hf‖ ≤ (b-a)*M := by
  cases k with
  | real =>
    intro f a b M hf hM
    obtain ⟨hn, he, _⟩ := real_norm_estimate f hf
    exact he.trans (realIntegral_le_mul_bound hn hM)
  | complex =>
    intro f a b M hf hM
    obtain ⟨hn, he, _⟩ := complex_norm_estimate f hf
    exact he.trans (realIntegral_le_mul_bound hn hM)

/-- A polynomial square-root factor is dominated by any positive exponential rate. -/
theorem sqrt_mul_exp_decay (η : ℝ) (hη : 0 < η) (C : ℝ) :
    Tendsto (fun t : ℝ => Real.sqrt t * C * Real.exp (-t*η)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) η hη).mul_const C
  simpa only [← Real.sqrt_eq_rpow, zero_mul, mul_zero, neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using ht


/-- The two exterior integrals have the source's exponentially small bound.
All integral values below are the proper Darboux values. -/
theorem exteriorDecay : Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization.exteriorDecay := by
  intro k
  let := S k
  intro φ g a b x₀ hφ hg hx hmin r hr hra hrb
  obtain ⟨η, hη, hgap⟩ := exteriorGap φ a b x₀ hφ hx hmin r hr
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨x₀, hx.1.le, hx.2.le⟩) hg.norm
  let M := ‖g y‖
  have hM : 0 ≤ M := norm_nonneg _
  have hgb : ∀ x ∈ Icc a b, ‖g x‖ ≤ M := fun x hxi => hmax hxi
  let f := fun t x => Real.exp (-t * φ x) • g x
  have hfc (t : ℝ) : ContinuousOn (f t) (Icc a b) :=
    ((hφ.const_mul (-t)).rexp).smul hg
  have hsubL : Icc a (x₀-r) ⊆ Icc a b :=
    Icc_subset_Icc le_rfl (by linarith [hx.2])
  have hsubR : Icc (x₀+r) b ⊆ Icc a b :=
    Icc_subset_Icc (by linarith [hx.1]) le_rfl
  let hL := fun t => scalar_continuous_integrable k (f t) a (x₀-r)
    hra.le ((hfc t).mono hsubL)
  let hR := fun t => scalar_continuous_integrable k (f t) (x₀+r) b
    hrb.le ((hfc t).mono hsubR)
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(Real.sqrt t * Real.exp (t*φ x₀)) •
        (integral k (f t) (hL t) + integral k (f t) (hR t))‖ ≤
        Real.sqrt t * M * (b-a) * Real.exp (-t*η) := by
    intro t ht
    have hpoint (x : ℝ) (hxi : x ∈ Icc a b) (hxr : r ≤ |x-x₀|) :
        ‖f t x‖ ≤ Real.exp (-t * (φ x₀+η)) * M := by
      have he : Real.exp (-t * φ x) ≤ Real.exp (-t * (φ x₀+η)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hgap x hxi hxr) (neg_nonpos.mpr ht))
      calc
        ‖f t x‖ = Real.exp (-t * φ x) * ‖g x‖ := by
          simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-t * (φ x₀+η)) * M :=
          mul_le_mul he (hgb x hxi) (norm_nonneg _) (Real.exp_pos _).le
    have hleft : ‖integral k (f t) (hL t)‖ ≤
        (x₀-r-a) * (Real.exp (-t*(φ x₀+η))*M) := by
      apply scalar_integral_norm_le k (f t) (hL t)
      intro x hxi
      apply hpoint x (hsubL hxi)
      rw [abs_of_nonpos (by linarith [hxi.2] : x-x₀ ≤ 0)]
      linarith [hxi.2]
    have hright : ‖integral k (f t) (hR t)‖ ≤
        (b-(x₀+r)) * (Real.exp (-t*(φ x₀+η))*M) := by
      apply scalar_integral_norm_le k (f t) (hR t)
      intro x hxi
      apply hpoint x (hsubR hxi)
      rw [abs_of_nonneg (by linarith [hxi.1] : 0 ≤ x-x₀)]
      linarith [hxi.1]
    have hsum : ‖integral k (f t) (hL t) + integral k (f t) (hR t)‖ ≤
        (b-a) * (Real.exp (-t*(φ x₀+η))*M) := by
      calc
        _ ≤ ‖integral k (f t) (hL t)‖ + ‖integral k (f t) (hR t)‖ := norm_add_le _ _
        _ ≤ (x₀-r-a) * (Real.exp (-t*(φ x₀+η))*M) +
              (b-(x₀+r)) * (Real.exp (-t*(φ x₀+η))*M) := add_le_add hleft hright
        _ ≤ (b-a) * (Real.exp (-t*(φ x₀+η))*M) := by
          have hp : 0 ≤ Real.exp (-t*(φ x₀+η))*M := mul_nonneg (Real.exp_pos _).le hM
          nlinarith
    have hcancel : Real.exp (t*φ x₀) * Real.exp (-t*(φ x₀+η)) =
        Real.exp (-t*η) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.sqrt t * Real.exp (t*φ x₀)) *
          ‖integral k (f t) (hL t) + integral k (f t) (hR t)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (Real.sqrt t * Real.exp (t*φ x₀)) *
          ((b-a) * (Real.exp (-t*(φ x₀+η))*M)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.sqrt t * M * (b-a) * Real.exp (-t*η) := by
        calc
          _ = Real.sqrt t * M * (b-a) *
              (Real.exp (t*φ x₀) * Real.exp (-t*(φ x₀+η))) := by ring
          _ = _ := by rw [hcancel]
  refine ⟨η, M, hη, hM, hgb, hL, hR, hbound, ?_⟩
  apply squeeze_zero_norm' (eventually_ge_atTop (0 : ℝ) |>.mono fun t ht => hbound t ht)
  simpa only [mul_assoc] using sqrt_mul_exp_decay η hη (M*(b-a))

end LaplaceLocalization
end SingleVariableAnalysis
