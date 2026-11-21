import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TrajectoryErgodic
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.Stationarity
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RegenerativeExcursions
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical
universe u v
namespace P207.Markov
noncomputable section

/-- A monotone cumulative reward can be interpolated between successive renewal
indices whose asymptotic spacing is linear. This concludes convergence at every
integer time, including the unfinished excursion. -/
theorem tendsto_monotone_reward_of_linear_epochs
    (r : ℕ → ℕ) (U : ℕ → ℝ) {ell a : ℝ}
    (hr : StrictMono r) (hell : 0 < ell) (hU : Monotone U)
    (hlin : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 ell))
    (hrew : Tendsto (fun n : ℕ => U (r n) / n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => U n / n) atTop (𝓝 (a / ell)) := by
  have hnext : Tendsto (fun n : ℕ => (r (n + 1) : ℝ) / n) atTop (𝓝 ell) := by
    have h := ((tendsto_add_atTop_iff_nat 1).2 hlin).mul
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1 (d := 1) one_ne_zero)
    simp only [one_mul, zero_add, div_one, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div U (a / ell) hU
  intro b hb
  refine ⟨r, ?_, hr.tendsto_atTop, ?_⟩
  · have hlt : ell < b * ell := by nlinarith
    have he := (tendsto_order.1 (hnext.sub (hlin.const_mul b))).2 0 (by linarith)
    filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hn' : (r (n + 1) : ℝ) / n ≤ b * ((r n : ℝ) / n) := by linarith
    have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
    exact (div_le_div_iff_of_pos_right hnpos').mp
      (show (r (n + 1) : ℝ) / n ≤ (b * r n) / n by simpa [mul_div_assoc] using hn')
  · apply (hrew.div hlin hell.ne').congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    dsimp
    exact div_div_div_cancel_right₀ hn' _ _

/-- The sum of consecutive block rewards, including a finite initial prefix. -/
theorem sum_range_epochs (r : ℕ → ℕ) (hr : Monotone r) (g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (r n), g k) =
      (∑ k ∈ Finset.range (r 0), g k) +
        ∑ s ∈ Finset.range n, ∑ k ∈ Finset.Ico (r s) (r (s + 1)), g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    exact (Finset.sum_range_add_sum_Ico g (hr (Nat.le_succ n))).symm

/-- A finite initial prefix does not affect the reward per excursion. -/
theorem tendsto_reward_along_epochs (r : ℕ → ℕ) (hr : Monotone r)
    (g : ℕ → ℝ) {a : ℝ}
    (h : Tendsto (fun n : ℕ =>
      (∑ s ∈ Finset.range n, ∑ k ∈ Finset.Ico (r s) (r (s + 1)), g k) / n)
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (r n), g k) / n) atTop (𝓝 a) := by
  have h' :=
    (tendsto_const_div_atTop_nhds_zero_nat (∑ k ∈ Finset.range (r 0), g k)).add h
  rw [zero_add] at h'
  apply h'.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [sum_range_epochs r hr g n, add_div]

/-- Deterministic renewal-reward passage for an arbitrary real reward. The
absolute reward hypothesis controls oscillations inside each unfinished block.
No bound on the pointwise reward or on the initial prefix is required. -/
theorem tendsto_signed_reward_of_linear_epochs
    (r : ℕ → ℕ) (g : ℕ → ℝ) {ell b c : ℝ}
    (hr : StrictMono r) (hell : 0 < ell)
    (hlin : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 ell))
    (hb : Tendsto (fun n : ℕ =>
      (∑ s ∈ Finset.range n, ∑ k ∈ Finset.Ico (r s) (r (s + 1)), g k) / n)
      atTop (𝓝 b))
    (hc : Tendsto (fun n : ℕ =>
      (∑ s ∈ Finset.range n, ∑ k ∈ Finset.Ico (r s) (r (s + 1)), |g k|) / n)
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, g k) / n) atTop (𝓝 (b / ell)) := by
  have hb' := tendsto_reward_along_epochs r hr.monotone g hb
  have hc' := tendsto_reward_along_epochs r hr.monotone (fun k => |g k|) hc
  have hmabs : Monotone (fun n => ∑ k ∈ Finset.range n, |g k|) := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hmplus : Monotone (fun n => ∑ k ∈ Finset.range n, (|g k| + g k)) := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (by linarith [neg_abs_le (g n)])
  have hplus : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range (r n), (|g k| + g k)) / n) atTop (𝓝 (c + b)) := by
    simpa only [Finset.sum_add_distrib, add_div] using hc'.add hb'
  have h₁ := tendsto_monotone_reward_of_linear_epochs r _ hr hell hmplus hlin hplus
  have h₂ := tendsto_monotone_reward_of_linear_epochs r _ hr hell hmabs hlin hc'
  convert h₁.sub h₂ using 1
  · ext n
    simp only [Finset.sum_add_distrib, add_div]
    ring
  · congr 1
    ring

/-- Finitely valued successive return epochs are strictly increasing. -/
theorem strictMono_returnEpoch_untop {S : Type u} {Ω : Type v}
    (X : ℕ → Ω → S) (i : S) (ω : Ω)
    (hfin : ∀ s, returnEpoch X i s ω < ⊤) :
    StrictMono (fun s => (returnEpoch X i s ω).untopA) := by
  apply strictMono_nat_of_lt_succ
  intro s
  have he : returnEpoch X i (s + 1) ω =
      hittingAfter X {i} ((returnEpoch X i s ω).untopA + 1) ω := by
    simp only [returnEpoch, ite_eq_right (hfin s).ne]
  have h := le_hittingAfter (u := X) (s := {i})
    (n := (returnEpoch X i s ω).untopA + 1) ω
  rw [← he] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self _)
    ((WithTop.le_untopA_iff (hfin (s + 1)).ne).mpr h)

/-- Lengths telescope even when the first return epoch is positive. -/
theorem epoch_eq_initial_add_lengths (r : ℕ → ℕ) (hr : Monotone r) (n : ℕ) :
    (r n : ℝ) = (r 0 : ℝ) +
      ∑ s ∈ Finset.range n, ((r (s + 1) - r s : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih,
      Nat.cast_sub (hr (Nat.le_succ n))]
    ring

/-- Real-coordinate strong law for independent vectors sharing one law. -/
theorem strong_law_coordinate {Ω : Type v} [MeasurableSpace Ω]
    {E : Type u} [MeasurableSpace E] {μ : Measure Ω}
    (V : ℕ → Ω → E) (hI : iIndepFun V μ)
    (hID : ∀ n, IdentDistrib (V n) (V 0) μ μ)
    (q : E → ℝ) (hq : Measurable q)
    (hint : Integrable (fun ω => q (V 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ s ∈ Finset.range n, q (V s ω)) / n)
      atTop (𝓝 (∫ ω, q (V 0 ω) ∂μ)) := by
  apply strong_law_ae_real _ hint
  · intro s t hst
    exact (hI.indepFun hst).comp hq hq
  · intro n
    exact (hID n).comp hq

/-- Conditional derivation of W19. Its five premises are the complete frozen
upstream propositions, in the contract's order, and are not accepted facts. -/
theorem trajectory_ergodic_conditional
    (_hMeas : RegenerativeExcursionsSpec.measurable_excursionVector.{u,v})
    (_hSingle : RegenerativeExcursionsSpec.measurable_singleExcursionVector.{u})
    (hRegen : RegenerativeExcursionsSpec.regenerative_excursions.{u,v})
    (_hFinite : RegenerativeExcursionsSpec.returnEpoch_finite.{u,v})
    (_hStop : RegenerativeExcursionsSpec.returnEpoch_isStoppingTime.{u,v}) :
    TrajectoryErgodicSpec.trajectory_ergodic.{u,v} := by
  intro S _ _ _ _ Ω _ P π ν X ℱ μ _ hP hπ hX f hf
  let i : S := Classical.choice inferInstance
  obtain ⟨hfinite, hmeas, hind, hdist, hmom⟩ :=
    hRegen P π ν X ℱ μ hP hπ hX i f hf
  have hident (n : ℕ) : IdentDistrib (excursionVector X i f n)
      (excursionVector X i f 0) μ μ := (hdist n).trans (hdist 0).symm
  have hL := strong_law_coordinate _ hind hident
    (fun z : ℝ × ℝ × ℝ => z.1) measurable_fst (hmom 0).1
  have hB := strong_law_coordinate _ hind hident
    (fun z : ℝ × ℝ × ℝ => z.2.1) (measurable_fst.comp measurable_snd) (hmom 0).2.1
  have hC := strong_law_coordinate _ hind hident
    (fun z : ℝ × ℝ × ℝ => z.2.2) (measurable_snd.comp measurable_snd) (hmom 0).2.2.1
  have hpi : 0 < (π i).toReal :=
    ENNReal.toReal_pos (stationary_positive P π hP hπ i).ne' (π.apply_ne_top i)
  have hquot : (∑' j, ((π j).toReal / (π i).toReal) * f j) /
      (1 / (π i).toReal) = ∑' j, (π j).toReal * f j := by
    simp_rw [div_mul_eq_mul_div, tsum_div_const]
    field_simp
  filter_upwards [hfinite, hL, hB, hC] with ω hfin hLω hBω hCω
  rw [(hmom 0).2.2.2.1] at hLω
  rw [(hmom 0).2.2.2.2.1] at hBω
  rw [(hmom 0).2.2.2.2.2] at hCω
  let r : ℕ → ℕ := fun s => (returnEpoch X i s ω).untopA
  have hr : StrictMono r := strictMono_returnEpoch_untop X i ω hfin
  have hv (s : ℕ) : excursionVector X i f s ω =
      (((r (s + 1) - r s : ℕ) : ℝ),
        ∑ k ∈ Finset.Ico (r s) (r (s + 1)), f (X k ω),
        ∑ k ∈ Finset.Ico (r s) (r (s + 1)), |f (X k ω)|) := by
    simp only [excursionVector, (hfin s).ne, (hfin (s + 1)).ne,
      false_or, ite_false]
    rfl
  simp only [hv] at hLω hBω hCω
  have hlin : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop
      (𝓝 (1 / (π i).toReal)) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (r 0 : ℝ)).add hLω
    rw [zero_add] at h
    apply h.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [epoch_eq_initial_add_lengths r hr.monotone n, add_div]
  rw [← hquot]
  exact tendsto_signed_reward_of_linear_epochs r (fun k => f (X k ω))
    hr (one_div_pos.mpr hpi) hlin hBω hCω

end
end P207.Markov

universe v8_closure_b713a530ad8db738_u0 v8_closure_b713a530ad8db738_u1
theorem _root_.«P207».«Markov».«trajectory_ergodic» : _root_.«P207».«Markov».«TrajectoryErgodicSpec».«trajectory_ergodic».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1} :=
  @_root_.«P207».«Markov».«trajectory_ergodic_conditional».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1} (@_root_.«P207».«Markov».«measurable_excursionVector».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1}) (@_root_.«P207».«Markov».«measurable_singleExcursionVector».{v8_closure_b713a530ad8db738_u0}) (@_root_.«P207».«Markov».«regenerative_excursions».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1}) (@_root_.«P207».«Markov».«returnEpoch_finite».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1}) (@_root_.«P207».«Markov».«returnEpoch_isStoppingTime».{v8_closure_b713a530ad8db738_u0, v8_closure_b713a530ad8db738_u1})
