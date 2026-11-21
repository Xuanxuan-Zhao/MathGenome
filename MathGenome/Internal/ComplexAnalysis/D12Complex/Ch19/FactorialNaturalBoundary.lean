import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.FactorialNaturalBoundary
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Filter Finset
open scoped Topology

namespace D12Complex.FactorialNaturalBoundary

/-- The source series, starting at factorial 1. Outside its convergence set
the total `tsum` value is immaterial to the conclusions below. -/
def series (z : ℂ) : ℂ := ∑' n : ℕ, z ^ (n+1).factorial

lemma term_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) : ‖z^(n+1).factorial‖ ≤ r^n := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) hz _).trans
    (pow_le_pow_of_le_one hr hr1 ((Nat.le_succ n).trans (Nat.self_le_factorial _)))

lemma summable_terms {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z^(n+1).factorial) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz)
  intro n
  exact term_bound (norm_nonneg z) hz.le n le_rfl

theorem normal_convergence :
    Specs.D12Complex.Ch19.FactorialNaturalBoundary.normal_convergence_type := by
  intro r hr hr1
  have hs := summable_geometric_of_lt_one hr hr1
  have hb : ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) r,
      ‖z^(n+1).factorial‖ ≤ r^n := by
    intro n z hz
    apply term_bound hr hr1.le n
    simpa using hz
  exact ⟨hs, hb, tendstoUniformlyOn_tsum_nat hs hb⟩

theorem holomorphic : Specs.D12Complex.Ch19.FactorialNaturalBoundary.holomorphic_type := by
  refine ⟨isOpen_ball, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  obtain ⟨r, hzr, hr1⟩ := exists_between hz1
  have hr : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hd : DifferentiableOn ℂ series (ball (0 : ℂ) r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (summable_geometric_of_lt_one hr hr1)
      (fun n => (differentiable_id.pow _).differentiableOn) isOpen_ball
    intro n w hw
    apply term_bound hr hr1.le n
    exact (show ‖w‖ < r by simpa using hw).le
  exact hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hzr))

/-- Once the factorial contains the root's order, the angular part disappears. -/
lemma root_factorial {ξ : ℂ} {q : ℕ} (hq : 0 < q) (hξ : ξ^q = 1)
    (n : ℕ) : ξ ^ (n+q+1).factorial = 1 := by
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hq (show q ≤ n+q+1 by omega)
  rw [hk, pow_mul, hξ, one_pow]

/-- Any finite block of the positive real tail gives a lower bound; the
finitely many preceding complex terms cost at most q. -/
lemma real_part_lower_bound {ξ : ℂ} {q : ℕ} (hq : 0 < q) (hξ : ξ^q = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    (∑ n ∈ range L, r ^ (n+q+1).factorial) - q ≤ (series ((r:ℂ)*ξ)).re := by
  have hnorm : ‖ξ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hξ hq.ne'
  have hnormr : ‖(r:ℂ)*ξ‖ = r := by
    simp [hnorm, Complex.norm_real, Real.norm_of_nonneg hr]
  have hs := summable_terms (hnormr ▸ hr1)
  have hsr := (Complex.hasSum_re hs.hasSum).summable
  have htail : Summable (fun n : ℕ => (((r:ℂ)*ξ) ^ (n+q+1).factorial).re) :=
    hsr.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hterm (n : ℕ) : (((r:ℂ)*ξ) ^ (n+q+1).factorial).re =
      r^(n+q+1).factorial := by
    rw [mul_pow, root_factorial hq hξ n, mul_one, ← Complex.ofReal_pow, Complex.ofReal_re]
  have ht : Summable (fun n : ℕ => r^(n+q+1).factorial) := by
    simpa only [hterm] using htail
  have hle := ht.sum_le_tsum (range L) (fun n _ => pow_nonneg hr _)
  have hhead : -(q : ℝ) ≤ ∑ n ∈ range q, (((r:ℂ)*ξ) ^ (n+1).factorial).re := by
    calc
      -(q : ℝ) = ∑ n ∈ range q, (-1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        have hb : ‖((r:ℂ)*ξ) ^ (n+1).factorial‖ ≤ 1 := by
          rw [norm_pow, hnormr]
          exact pow_le_one₀ hr hr1.le
        have ha := (abs_le.mp (Complex.abs_re_le_norm (((r:ℂ)*ξ) ^ (n+1).factorial))).1
        linarith
  have heq := hsr.sum_add_tsum_nat_add q
  rw [← Complex.re_tsum hs] at heq
  simp only [hterm] at heq
  change _ ≤ (∑' n : ℕ, ((r:ℂ)*ξ) ^ (n+1).factorial).re
  linarith

theorem radial_unbounded :
    Specs.D12Complex.Ch19.FactorialNaturalBoundary.radial_unbounded_type := by
  rintro ξ ⟨q, hq, hξ⟩
  change Tendsto (fun r : ℝ => ‖series ((r : ℂ) * ξ)‖) (𝓝[<] (1 : ℝ)) atTop
  apply Filter.tendsto_atTop.2
  intro M
  obtain ⟨L, hL⟩ := exists_nat_gt (M + (q : ℝ))
  have hlim : Tendsto (fun r : ℝ => ∑ n ∈ range L, r ^ (n+q+1).factorial)
      (𝓝[<] (1 : ℝ)) (𝓝 (L : ℝ)) := by
    simpa using (tendsto_finsetSum (range L) (fun n _ =>
      ((continuous_id.pow (n+q+1).factorial).tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds))
  have hlarge := hlim.eventually (eventually_gt_nhds hL)
  filter_upwards [hlarge, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hlarge hr
  have hl := real_part_lower_bound hq hξ hr.1.le hr.2 L
  have hn := Complex.re_le_norm (series ((r:ℂ)*ξ))
  linarith

/-- Density of roots of unity, obtained from density of rational angles. -/
lemma exists_root_mem_open {ξ : ℂ} (hξ : ‖ξ‖ = 1) {U : Set ℂ}
    (hU : IsOpen U) (hmem : ξ ∈ U) :
    ∃ η ∈ U, ∃ q : ℕ, 0 < q ∧ η^q = 1 := by
  let p : ℝ → ℂ := fun t => Complex.exp ((t:ℂ) * (2 * Real.pi * Complex.I))
  have hp : Continuous p := Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul_const _)
  have honto : p (ξ.arg / (2 * Real.pi)) = ξ := by
    have he : ((ξ.arg / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
        ξ.arg * Complex.I := by
      push_cast
      field_simp
    change Complex.exp _ = ξ
    rw [he]
    simpa only [hξ, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I ξ
  obtain ⟨a, ha⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open
    (hU.preimage hp) ⟨ξ.arg / (2 * Real.pi), by simpa [honto]⟩
  refine ⟨p a, ha, a.den, a.den_pos, ?_⟩
  change Complex.exp _ ^ a.den = 1
  rw [← Complex.exp_nat_mul]
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨a.num, ?_⟩
  have hrat : (a.den:ℂ) * (a:ℂ) = (a.num:ℂ) := by
    exact_mod_cast a.den_mul_eq_num
  calc
    _ = ((a.den:ℂ) * (a:ℂ)) * (2 * Real.pi * Complex.I) := by push_cast; ring
    _ = _ := by rw [hrat]

theorem natural_boundary :
    Specs.D12Complex.Ch19.FactorialNaturalBoundary.natural_boundary_type := by
  intro ξ hξ
  rintro ⟨U, g, hU, hmem, hg, heq⟩
  obtain ⟨η, hη, q, hq, hpow⟩ := exists_root_mem_open hξ hU hmem
  have hηnorm : ‖η‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hq.ne'
  have hpath : Tendsto (fun r : ℝ => (r:ℂ)*η) (𝓝[<] (1 : ℝ)) (𝓝 η) := by
    simpa only [Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.mul_const η).tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hg_lim := ((hg.2 η hη).continuousAt.norm.tendsto).comp hpath
  have hevent : (fun r : ℝ => ‖g ((r:ℂ)*η)‖) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ => ‖series ((r:ℂ)*η)‖) := by
    filter_upwards [hpath.eventually (hU.mem_nhds hη),
      Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hrU hr
    apply congrArg norm
    apply heq
    refine ⟨hrU, ?_⟩
    simpa [mem_ball, dist_zero_right, norm_mul, hηnorm,
      Complex.norm_real, Real.norm_of_nonneg hr.1.le] using hr.2
  exact not_tendsto_nhds_of_tendsto_atTop
    (radial_unbounded η ⟨q, hq, hpow⟩) ‖g η‖ (hg_lim.congr' hevent)

end D12Complex.FactorialNaturalBoundary
