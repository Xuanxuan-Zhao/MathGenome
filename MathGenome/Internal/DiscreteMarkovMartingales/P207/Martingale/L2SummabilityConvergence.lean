import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.L2SummabilityConvergence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.L2OrthogonalIncrements
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.LpConvergence

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.L2SummabilityConvergence

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The finite energy identity turns bounded energies into a convergent
nonnegative series, with no convention about divergent real sums. -/
theorem l2_bounded_iff_summable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) :
    (∃ C : ℝ, ∀ n, (∫ ω, M n ω ^ 2 ∂μ) ≤ C) ↔
      Summable (fun k => ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) := by
  have hnonneg (k : ℕ) : 0 ≤ ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  constructor
  · rintro ⟨C, hC⟩
    apply summable_of_sum_range_le hnonneg (c := C - ∫ ω, M 0 ω ^ 2 ∂μ)
    intro n
    have he := L2OrthogonalIncrements.energy_identity μ ℱ M hM hL n
    linarith [hC n]
  · intro hs
    refine ⟨(∫ ω, M 0 ω ^ 2 ∂μ) + ∑' k, ∫ ω,
      (M (k + 1) ω - M k ω) ^ 2 ∂μ, fun n => ?_⟩
    rw [L2OrthogonalIncrements.energy_identity μ ℱ M hM hL n]
    linarith [hs.sum_le_tsum (Finset.range n) (fun k _ => hnonneg k)]

/-- Identify the usual Hilbert norm with the genuine second moment. -/
theorem norm_toLp_sq (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, Real.norm_eq_abs, sq_abs]

/-- The extended-seminorm definition of L² convergence gives convergence
in the Hilbert space of almost-everywhere equivalence classes. -/
theorem tendsto_toLp (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa only [Lp.dist_edist, Lp.edist_toLp_toLp, ENNReal.toReal_zero, Function.comp_def] using ht

/-- Continuity of the second moment along an L²-convergent sequence. -/
theorem tendsto_integral_sq (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, g ω ^ 2 ∂μ)) := by
  simpa only [norm_toLp_sq] using (tendsto_toLp μ f g hf hg h).norm.pow 2

/-- The finite tail identity, retaining a possibly random value at time n. -/
theorem finite_tail_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (n j : ℕ) :
    (∫ ω, (M (n + j) ω - M n ω) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range j, ∫ ω, (M (n + k + 1) ω - M (n + k) ω) ^ 2 ∂μ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd := L2OrthogonalIncrements.increment_memLp μ M hL (n + j)
    have hf := (hL (n + j)).sub (hL n)
    have hp := hf.integrable_mul hd
    have horth : (∫ ω, (M (n + j) ω - M n ω) *
        (M (n + j + 1) ω - M (n + j) ω) ∂μ) = 0 := by
      simp_rw [sub_mul]
      rw [integral_sub
        (f := fun ω => M (n + j) ω * (M (n + j + 1) ω - M (n + j) ω))
        (g := fun ω => M n ω * (M (n + j + 1) ω - M (n + j) ω))
        ((hL (n + j)).integrable_mul hd) ((hL n).integrable_mul hd),
        L2OrthogonalIncrements.past_value_increment_orthogonal μ ℱ M hM hL
          (n + j) (n + j) le_rfl,
        L2OrthogonalIncrements.past_value_increment_orthogonal μ ℱ M hM hL
          n (n + j) (Nat.le_add_right n j)]
      simp
    have hstep : (∫ ω, (M (n + j + 1) ω - M n ω) ^ 2 ∂μ) =
        (∫ ω, (M (n + j) ω - M n ω) ^ 2 ∂μ) +
          ∫ ω, (M (n + j + 1) ω - M (n + j) ω) ^ 2 ∂μ := by
      calc
        _ = ∫ ω, ((M (n + j) ω - M n ω) ^ 2 +
            (M (n + j + 1) ω - M (n + j) ω) ^ 2) +
            2 * ((M (n + j) ω - M n ω) *
              (M (n + j + 1) ω - M (n + j) ω)) ∂μ := by
          congr 1
          funext ω
          ring
        _ = _ := by
          rw [integral_add
            (f := fun ω => (M (n + j) ω - M n ω) ^ 2 +
              (M (n + j + 1) ω - M (n + j) ω) ^ 2)
            (g := fun ω => 2 * ((M (n + j) ω - M n ω) *
              (M (n + j + 1) ω - M (n + j) ω)))
            (hf.integrable_sq.add hd.integrable_sq) (hp.const_mul 2),
            integral_add
              (f := fun ω => (M (n + j) ω - M n ω) ^ 2)
              (g := fun ω => (M (n + j + 1) ω - M (n + j) ω) ^ 2)
              hf.integrable_sq hd.integrable_sq, integral_const_mul, horth]
          simp
    simpa only [Nat.add_assoc, Finset.sum_range_succ, ih] using hstep

/-- Summable increment energies give the canonical integrable terminal,
almost-sure and L² convergence, and both full limiting energy identities. -/
theorem convergence_and_energy :
    P207.L2SummabilityConvergenceSpec.convergence_and_energy.{u} := by
  intro Ω m μ _ ℱ M hM hL hs
  obtain ⟨C, hC⟩ := (l2_bounded_iff_summable μ ℱ M hM hL).mpr hs
  have hpow (n : ℕ) : Integrable (fun ω => |M n ω| ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, sq_abs] using (hL n).integrable_sq
  have hbound (n : ℕ) : (∫ ω, |M n ω| ^ (2 : ℝ) ∂μ) ≤ C := by
    simpa only [Real.rpow_two, sq_abs] using hC n
  obtain ⟨hmeas, hlim, hae, hconv, hterminal⟩ :=
    lp_martingale_convergence μ ℱ M hM 2 (by norm_num) hpow C hbound
  have hlim2 : MemLp (ℱ.limitProcess M μ) 2 μ := by simpa using hlim
  have hconv2 : Tendsto (fun n => eLpNorm (M n - ℱ.limitProcess M μ) 2 μ)
      atTop (𝓝 0) := by simpa using hconv
  refine ⟨hmeas, hlim2, hlim2.integrable (by norm_num), hae, hconv2, hterminal, ?_, ?_⟩
  · have he : Tendsto (fun n => ∫ ω, M n ω ^ 2 ∂μ) atTop
        (𝓝 ((∫ ω, M 0 ω ^ 2 ∂μ) +
          ∑' k, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ)) := by
      have hsum : Tendsto
          (fun n => (∫ ω, M 0 ω ^ 2 ∂μ) +
            ∑ k ∈ Finset.range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) atTop
          (𝓝 ((∫ ω, M 0 ω ^ 2 ∂μ) +
            ∑' k, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ)) :=
        tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
      exact hsum.congr fun n => (L2OrthogonalIncrements.energy_identity μ ℱ M hM hL n).symm
    exact tendsto_nhds_unique (tendsto_integral_sq μ M _ hL hlim2 hconv2) he
  · intro n
    have htail : Summable (fun k => ∫ ω,
        (M (n + k + 1) ω - M (n + k) ω) ^ 2 ∂μ) := by
      simpa only [Nat.add_comm n] using (summable_nat_add_iff n).mpr hs
    refine ⟨htail, ?_⟩
    have ht := (tendsto_toLp μ M _ hL hlim2 hconv2).comp (tendsto_add_atTop_nat n)
    have hdiff := (ht.sub_const ((hL n).toLp (M n))).norm.pow 2
    have hleft : Tendsto (fun j => ∫ ω, (M (n + j) ω - M n ω) ^ 2 ∂μ) atTop
        (𝓝 (∫ ω, (ℱ.limitProcess M μ ω - M n ω) ^ 2 ∂μ)) := by
      simpa only [Function.comp_def, ← MemLp.toLp_sub, norm_toLp_sq,
        Pi.sub_apply, Nat.add_comm n] using hdiff
    have hright : Tendsto (fun j => ∫ ω, (M (n + j) ω - M n ω) ^ 2 ∂μ) atTop
        (𝓝 (∑' k, ∫ ω, (M (n + k + 1) ω - M (n + k) ω) ^ 2 ∂μ)) := by
      exact htail.hasSum.tendsto_sum_nat.congr fun j =>
        (finite_tail_energy μ ℱ M hM hL n j).symm
    exact tendsto_nhds_unique hleft hright

end P207.L2SummabilityConvergence
