import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalDominatedConvergence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalLpContraction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalMonotoneConvergence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.IntegralConvergence
import Mathlib.Tactic.Linarith

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityFoundations.Ch03

universe u

set_option maxHeartbeats 800000

/-- Tail suprema of a bounded nonnegative null sequence tend to zero. -/
private lemma tailSup_tendsto_zero {f : ℕ → ℝ} (hpos : ∀ n, 0 ≤ f n)
    (hbdd : BddAbove (Set.range f)) (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => ⨆ k, f (n + k)) atTop (𝓝 0) := by
  have hb (n : ℕ) : BddAbove (Set.range (fun k => f (n + k))) := by
    rcases hbdd with ⟨C, hC⟩
    exact ⟨C, by rintro _ ⟨k, rfl⟩; exact hC (Set.mem_range_self _)⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le
      ((hpos (n + 0)).trans (le_ciSup (hb n) 0))
  · intro b hbpos
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hbpos)))
    filter_upwards [eventually_ge_atTop N] with n hn
    apply lt_of_le_of_lt (ciSup_le fun k => (hN (n + k) (by omega)).le)
    linarith

/-- Conditional dominated convergence, both almost surely and in L¹. -/
theorem realConditionalExpectation_dominated_convergence :
    Specs.ProbabilityFoundations.Ch03.ConditionalDominatedConvergence.dominatedConvergenceType := by
  intro Ω G F P _ hGF Xn X Y hXn hX hY hYpos hYi hbound hlim
  have hdom := Ch01.dominated_convergence P Xn X Y hXn hX hY hYpos hYi
    (fun n => by simpa only [Real.norm_eq_abs] using hbound n) hlim
  have hXi : Integrable X P := hdom.1
  have hXni : ∀ n, Integrable (Xn n) P := hdom.2.1
  have hXbound : ∀ᵐ ω ∂P, |X ω| ≤ Y ω := by
    filter_upwards [ae_all_iff.mpr hbound, hlim] with ω hb hl
    exact le_of_tendsto' hl.abs hb
  let H : ℕ → Ω → ℝ := fun n ω => ⨆ k, |Xn (n + k) ω - X ω|
  have hHm : ∀ n, Measurable (H n) := fun n =>
    Measurable.iSup fun k => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hXn (n + k)).sub hX).norm
  have herr : ∀ᵐ ω ∂P, ∀ n, |Xn n ω - X ω| ≤ 2 * Y ω := by
    filter_upwards [ae_all_iff.mpr hbound, hXbound] with ω hb hx n
    exact (abs_sub (Xn n ω) (X ω)).trans (by linarith [hb n])
  have hHb : ∀ᵐ ω ∂P, ∀ n,
      BddAbove (Set.range (fun k => |Xn (n + k) ω - X ω|)) := by
    filter_upwards [herr] with ω he n
    exact ⟨2 * Y ω, by rintro _ ⟨k, rfl⟩; exact he (n + k)⟩
  have hHpos : ∀ᵐ ω ∂P, ∀ n, 0 ≤ H n ω := by
    filter_upwards [hHb] with ω hb n
    exact (abs_nonneg _).trans (le_ciSup (hb n) 0)
  have hHbound : ∀ᵐ ω ∂P, ∀ n, H n ω ≤ 2 * Y ω := by
    filter_upwards [herr] with ω he n
    exact ciSup_le fun k => he (n + k)
  have hHi : ∀ n, Integrable (H n) P := by
    intro n
    apply (hYi.const_mul 2).mono' (hHm n).aestronglyMeasurable
    filter_upwards [hHpos, hHbound] with ω hp hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hp n)] using hb n
  have hHanti : ∀ᵐ ω ∂P, Antitone (fun n => H n ω) := by
    filter_upwards [hHb] with ω hb i j hij
    apply ciSup_le
    intro k
    have heq : j + k = i + (j - i + k) := by omega
    rw [heq]
    exact le_ciSup (hb i) (j - i + k)
  have hHlim : ∀ᵐ ω ∂P, Tendsto (fun n => H n ω) atTop (𝓝 0) := by
    filter_upwards [herr, hlim] with ω he hl
    exact tailSup_tendsto_zero (fun n => abs_nonneg _)
      ⟨2 * Y ω, by rintro _ ⟨n, rfl⟩; exact he n⟩
      (by simpa using (hl.sub_const (X ω)).abs)
  have hHint : Tendsto (fun n => ∫ ω, H n ω ∂P) atTop (𝓝 0) := by
    simpa using integral_tendsto_of_tendsto_of_antitone hHi (integrable_zero Ω ℝ P)
      hHanti hHlim
  have hCHanti : ∀ᵐ ω ∂P, Antitone (fun n => realConditionalExpectation G P (H n) ω) := by
    have hs : ∀ n, realConditionalExpectation G P (H (n + 1)) ≤ᵐ[P]
        realConditionalExpectation G P (H n) := fun n =>
      condExp_mono (hHi (n + 1)) (hHi n) (hHanti.mono fun ω hω => hω (Nat.le_succ n))
    filter_upwards [ae_all_iff.mpr hs] with ω hω
    exact antitone_nat_of_succ_le hω
  have hCHpos : ∀ᵐ ω ∂P, ∀ n, 0 ≤ realConditionalExpectation G P (H n) ω :=
    ae_all_iff.mpr fun n => condExp_nonneg (hHpos.mono fun ω hω => hω n)
  have hCHint : Tendsto (fun n => ∫ ω, realConditionalExpectation G P (H n) ω ∂P)
      atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    simpa only [integral_realConditionalExpectation G P hGF _ (hHi _), integral_zero] using hHint
  have hCHlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => realConditionalExpectation G P (H n) ω) atTop (𝓝 0) :=
    tendsto_of_integral_tendsto_of_antitone (fun _ => integrable_condExp)
      (integrable_zero Ω ℝ P) hCHint hCHanti hCHpos
  have hcontrol : ∀ n, ∀ᵐ ω ∂P,
      |realConditionalExpectation G P (Xn n) ω - realConditionalExpectation G P X ω| ≤
        realConditionalExpectation G P (H n) ω := by
    intro n
    have herror : (fun ω => |Xn n ω - X ω|) ≤ᵐ[P] H n := by
      filter_upwards [hHb] with ω hb
      simpa only [Nat.add_zero] using le_ciSup (hb n) 0
    filter_upwards [condExp_sub (hXni n) hXi G,
      realConditionalExpectation_abs_le G P hGF (fun ω => Xn n ω - X ω) ((hXni n).sub hXi),
      condExp_mono ((hXni n).sub hXi).abs (hHi n) herror] with ω he ha hm
    change realConditionalExpectation G P (fun ω => Xn n ω - X ω) ω = _ at he
    rw [he] at ha
    exact ha.trans hm
  refine ⟨hXi, hXni, ?_, ?_⟩
  · change ∀ᵐ ω ∂P, Tendsto (fun n => realConditionalExpectation G P (Xn n) ω)
      atTop (𝓝 (realConditionalExpectation G P X ω))
    filter_upwards [hCHlim, ae_all_iff.mpr hcontrol] with ω hl hc
    have hz : Tendsto (fun n => |realConditionalExpectation G P (Xn n) ω -
        realConditionalExpectation G P X ω|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _) hc hl
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hz)
  · have hL1bound : ∀ n, (∫ ω, |realConditionalExpectation G P (Xn n) ω -
        realConditionalExpectation G P X ω| ∂P) ≤ ∫ ω, |Xn n ω - X ω| ∂P := by
      intro n
      calc
        _ = ∫ ω, |realConditionalExpectation G P (fun ω => Xn n ω - X ω) ω| ∂P := by
          apply integral_congr_ae
          filter_upwards [condExp_sub (hXni n) hXi G] with ω he
          exact congrArg abs he.symm
        _ ≤ _ := integral_abs_condExp_le (m := G) (fun ω => Xn n ω - X ω)
    exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hL1bound
      (by simpa only [Real.norm_eq_abs] using hdom.2.2.1)

end ProbabilityFoundations.Ch03
