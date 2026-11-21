import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.ConditionalHoeffding
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.AzumaHoeffding
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal
universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Integration turns an a.s. conditional moment bound into a moment bound. -/
lemma subGaussian_of_conditional_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ m) (Y : Ω → ℝ) (c : ℝ≥0)
    (h : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) μ ∧
      μ[(fun ω => Real.exp (s * Y ω)) | 𝒢] ≤ᵐ[μ]
        (fun _ => Real.exp ((c : ℝ) * s ^ 2 / 2))) :
    HasSubgaussianMGF Y c μ where
  integrable_exp_mul s := (h s).1
  mgf_le s := by
    rw [mgf, ← integral_condExp h𝒢]
    exact (integral_mono_ae integrable_condExp (integrable_const _) (h s).2).trans_eq
      (by simp)

/-- Adding a conditionally sub-Gaussian increment on an arbitrary probability
space. Unlike the kernel API, this requires no standard Borel hypothesis. -/
lemma subGaussian_add_conditional (μ : Measure Ω) [IsProbabilityMeasure μ]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ m) {X Y : Ω → ℝ} {c d : ℝ≥0}
    (hXm : Measurable[𝒢] X) (hX : HasSubgaussianMGF X c μ)
    (hY : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) μ ∧
      μ[(fun ω => Real.exp (s * Y ω)) | 𝒢] ≤ᵐ[μ]
        (fun _ => Real.exp ((d : ℝ) * s ^ 2 / 2))) :
    HasSubgaussianMGF (fun ω => X ω + Y ω) (c + d) μ := by
  have hY' := @subGaussian_of_conditional_bound Ω m μ _ 𝒢 h𝒢 Y d hY
  have hint (s : ℝ) : Integrable
      (fun ω => Real.exp (s * X ω) * Real.exp (s * Y ω)) μ := by
    exact MemLp.integrable_mul (p := 2) (q := 2)
      (hX.memLp_exp_mul s 2) (hY'.memLp_exp_mul s 2)
  refine ⟨fun s => by simpa only [mul_add, Real.exp_add] using hint s, fun s => ?_⟩
  have hce := condExp_mul_of_stronglyMeasurable_left
    (f := fun ω => Real.exp (s * X ω)) (g := fun ω => Real.exp (s * Y ω))
    (by exact (hXm.const_mul s).exp.stronglyMeasurable) (hint s) (hY s).1
  calc
    mgf (fun ω => X ω + Y ω) μ s
        = ∫ ω, Real.exp (s * X ω) * Real.exp (s * Y ω) ∂μ := by
            simp only [mgf, mul_add, Real.exp_add]
    _ = ∫ ω, μ[(fun ω => Real.exp (s * X ω) * Real.exp (s * Y ω)) | 𝒢] ω ∂μ :=
      (integral_condExp h𝒢).symm
    _ = ∫ ω, Real.exp (s * X ω) * μ[(fun ω => Real.exp (s * Y ω)) | 𝒢] ω ∂μ :=
      integral_congr_ae hce
    _ ≤ ∫ ω, Real.exp (s * X ω) * Real.exp ((d : ℝ) * s ^ 2 / 2) ∂μ := by
      apply integral_mono_ae
        (integrable_condExp.congr hce) ((hX.integrable_exp_mul s).mul_const _)
      filter_upwards [(hY s).2] with ω hω
      exact mul_le_mul_of_nonneg_left hω (Real.exp_nonneg _)
    _ = mgf X μ s * Real.exp ((d : ℝ) * s ^ 2 / 2) := integral_mul_const _ _
    _ ≤ Real.exp ((c : ℝ) * s ^ 2 / 2) * Real.exp ((d : ℝ) * s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (hX.mgf_le s) (Real.exp_nonneg _)
    _ = Real.exp ((↑(c + d) : ℝ) * s ^ 2 / 2) := by
      rw [← Real.exp_add, NNReal.coe_add]
      congr 1
      ring

/-- Exponential-moment control for a finite martingale, centered at its actual
(possibly random and unbounded) initial value. -/
theorem azuma_subGaussian (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ k ≤ n, Measurable[ℱ k] (M k))
    (hi : ∀ k ≤ n, Integrable (M k) μ)
    (hs : ∀ k < n, μ[M (k + 1) | ℱ k] =ᵐ[μ] M k)
    (hb : ∀ k < n, ∀ᵐ ω ∂μ,
      a k ≤ M (k + 1) ω - M k ω ∧ M (k + 1) ω - M k ω ≤ b k) :
    HasSubgaussianMGF (fun ω => M n ω - M 0 ω)
      (NNReal.mk ((∑ k ∈ Finset.range n, (b k - a k) ^ 2) / 4)
        (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num))) μ := by
  induction n with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, zero_div, sub_self, NNReal.mk_zero] using
      (HasSubgaussianMGF.fun_zero (μ := μ))
  | succ n ih =>
    have hp := ih (fun k hk => ha k (by omega)) (fun k hk => hi k (by omega))
      (fun k hk => hs k (by omega)) (fun k hk => hb k (by omega))
    have hz : μ[(fun ω => M (n + 1) ω - M n ω) | ℱ n] =ᵐ[μ] (fun _ => 0) := by
      have hsub := condExp_sub (hi (n + 1) le_rfl) (hi n (by omega)) (ℱ n)
      have hself := condExp_of_stronglyMeasurable (ℱ.le n)
        (ha n (by omega)).stronglyMeasurable (hi n (by omega))
      filter_upwards [hsub, hs n (by omega)] with ω hω hn
      change μ[M (n + 1) - M n | ℱ n] ω = 0
      rw [hω]
      change μ[M (n + 1) | ℱ n] ω - μ[M n | ℱ n] ω = 0
      rw [hself, hn, sub_self]
    have hY : ∀ s : ℝ,
        Integrable (fun ω => Real.exp (s * (M (n + 1) ω - M n ω))) μ ∧
        μ[(fun ω => Real.exp (s * (M (n + 1) ω - M n ω))) | ℱ n] ≤ᵐ[μ]
          (fun _ => Real.exp (((b n - a n) ^ 2 / 4) * s ^ 2 / 2)) := by
      intro s
      have hh := conditional_hoeffding_of_condExp_zero μ (ℱ.le n) _
        ((hi (n + 1) le_rfl).sub (hi n (by omega))) hz (a n) (b n) (hb n (by omega)) s
      have he : s ^ 2 * (b n - a n) ^ 2 / 8 = (b n - a n) ^ 2 / 4 * s ^ 2 / 2 := by ring
      simpa only [Pi.sub_apply, he] using hh
    have hXm : Measurable[ℱ n] (fun ω => M n ω - M 0 ω) :=
      (ha n (by omega)).sub ((ha 0 (by omega)).mono (ℱ.mono (Nat.zero_le n)) le_rfl)
    have hadd := subGaussian_add_conditional μ (ℱ.le n) hXm hp
      (d := NNReal.mk ((b n - a n) ^ 2 / 4) (by positivity)) hY
    have heq : (fun ω => (M n ω - M 0 ω) + (M (n + 1) ω - M n ω)) =
        (fun ω => M (n + 1) ω - M 0 ω) := by funext ω; ring
    rw [heq] at hadd
    have hc : NNReal.mk ((∑ k ∈ Finset.range n, (b k - a k) ^ 2) / 4)
        (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)) +
        NNReal.mk ((b n - a n) ^ 2 / 4) (by positivity) =
        NNReal.mk ((∑ k ∈ Finset.range (n + 1), (b k - a k) ^ 2) / 4)
        (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)) := by
      apply NNReal.eq
      simp only [NNReal.coe_add, NNReal.coe_mk, Finset.sum_range_succ]
      ring
    rw [hc] at hadd
    exact hadd

/-- Azuma--Hoeffding, with both tails and the degenerate variance case.
Only the finite segment through `n` is assumed to be a martingale. -/
theorem azuma_hoeffding : AzumaHoeffdingSpec.azuma_hoeffding.{u} := by
  intro Ω m μ _ ℱ M n a b ha hi hs hb
  dsimp only
  intro t ht
  let V : ℝ := ∑ k ∈ Finset.range n, (b k - a k) ^ 2
  have hG := azuma_subGaussian μ ℱ M n a b ha hi hs hb
  constructor
  · intro hV
    have hexp : -t ^ 2 / (2 * (V / 4)) = -2 * t ^ 2 / V := by
      field_simp; ring
    have hu : μ.real {ω | t ≤ M n ω - M 0 ω} ≤ Real.exp (-2 * t ^ 2 / V) := by
      have hh := hG.measure_ge_le ht.le
      change μ.real {ω | t ≤ M n ω - M 0 ω} ≤ Real.exp (-t ^ 2 / (2 * (V / 4))) at hh
      rwa [hexp] at hh
    have hl : μ.real {ω | M n ω - M 0 ω ≤ -t} ≤ Real.exp (-2 * t ^ 2 / V) := by
      have hh := hG.neg.measure_ge_le ht.le
      change μ.real {ω | t ≤ -(M n ω - M 0 ω)} ≤ Real.exp (-t ^ 2 / (2 * (V / 4))) at hh
      have hevent : {ω | t ≤ -(M n ω - M 0 ω)} = {ω | M n ω - M 0 ω ≤ -t} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro h <;> linarith
      rwa [hevent, hexp] at hh
    refine ⟨hu, hl, ?_⟩
    have hevent : {ω | t ≤ |M n ω - M 0 ω|} =
        {ω | t ≤ M n ω - M 0 ω} ∪ {ω | M n ω - M 0 ω ≤ -t} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      rcases le_total 0 (M n ω - M 0 ω) with h | h
      · rw [abs_of_nonneg h]
        constructor
        · exact Or.inl
        · intro hh
          rcases hh with hh | hh <;> linarith
      · rw [abs_of_nonpos h]
        constructor
        · intro hh; right; linarith
        · intro hh
          rcases hh with hh | hh <;> linarith
    rw [hevent]
    exact (measureReal_union_le _ _).trans (by linarith)
  · intro hV
    change V = 0 at hV
    have hc : NNReal.mk (V / 4)
        (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)) = 0 := by
      apply NNReal.eq
      simp only [NNReal.coe_mk, NNReal.coe_zero, hV, zero_div]
    have hG0 : HasSubgaussianMGF (fun ω => M n ω - M 0 ω) 0 μ := by
      change HasSubgaussianMGF (fun ω => M n ω - M 0 ω)
        (NNReal.mk (V / 4) _) μ at hG
      rwa [hc] at hG
    have hz := HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero hG0
    constructor
    · rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
      filter_upwards [hz] with ω hω
      change M n ω - M 0 ω = 0 at hω
      linarith
    · rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
      filter_upwards [hz] with ω hω
      change M n ω - M 0 ω = 0 at hω
      linarith

end P207
