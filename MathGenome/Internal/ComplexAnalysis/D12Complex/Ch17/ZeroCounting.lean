import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ZeroCounting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.OrderDivisorDefinitions
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Filter Set Metric MeromorphicOn
open scoped Topology Classical
namespace D12Complex.ZeroCounting
open OrderDivisorDefinitions

def zeroCount : Specs.D12Complex.Ch17.ZeroCounting.zeroCount_type :=
  Specs.D12Complex.Ch17.ZeroCounting.zeroCount_value

lemma entire_analytic {f : ℂ → ℂ} (hf : HolomorphicOn univ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  (LocalZeroFactorization.holomorphicNear_iff_analyticAt f z).mp ⟨univ, mem_univ _, hf⟩

lemma divisor_eq_count_summand (f : NonzeroEntireFunction) (r : ℝ) (z : ℂ) :
    divisor f.toFun (closedBall 0 r) z =
      ((if ‖z‖ ≤ r then (analyticOrderAt f.toFun z).toNat else 0 : ℕ) : ℤ) := by
  have ha : AnalyticOnNhd ℂ f.toFun (closedBall 0 r) := fun z _ => entire_analytic f.holomorphic z
  by_cases hz : ‖z‖ ≤ r
  · rw [ha.divisor_apply (by simpa using hz), ite_eq_left hz]
    have ho := ENat.natCast_toNat (zero_multiplicity_finite f z)
    rw [← ho]
    simp
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by simpa using hz), ite_eq_right hz]
    rfl

theorem count_support_finite : Specs.D12Complex.Ch17.ZeroCounting.count_support_finite_type := by
  intro f r
  apply ((divisor f.toFun (closedBall 0 r)).finiteSupport (isCompact_closedBall 0 r)).subset
  intro z hz
  rw [Function.mem_support, divisor_eq_count_summand]
  exact_mod_cast hz

lemma count_cast_eq_divisor (f : NonzeroEntireFunction) (r : ℝ) :
    (zeroCount f.toFun r : ℤ) = ∑ᶠ z : ℂ, divisor f.toFun (closedBall 0 r) z := by
  change ((∑ᶠ z : ℂ, if ‖z‖ ≤ r then (analyticOrderAt f.toFun z).toNat else 0 : ℕ) : ℤ) = _
  exact ((Nat.castAddMonoidHom ℤ).map_finsum (count_support_finite f r)).trans
    (finsum_congr (fun z => (divisor_eq_count_summand f r z).symm))

lemma one_le_maximumModulus {f : ℂ → ℂ} (hf : HolomorphicOn univ f)
    (h0 : f 0 = 1) {R : ℝ} (hR : 0 < R) : 1 ≤ maximumModulus f R := by
  have hd : Differentiable ℂ f := fun z => hf.2 z (mem_univ _)
  obtain ⟨_, _, _, hb⟩ := maximumModulus_attained f hd.continuous R hR
  have hm := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := (0 : ℂ)) (r := R)) hd.diffContOnCl
    (U := ball (0 : ℂ) R) (C := maximumModulus f R)
    (by simpa only [maximumModulus, frontier_ball (0 : ℂ) hR.ne'] using hb)
    (z := 0) (by rw [closure_ball 0 hR.ne']; exact mem_closedBall_self hR.le)
  simpa only [h0, norm_one] using hm

theorem counting_zeros : Specs.D12Complex.Ch17.ZeroCounting.counting_zeros_type := by
  intro f hf h0 r hr
  let F : NonzeroEntireFunction := ⟨f, hf, ⟨0, by simp [h0]⟩⟩
  have h2r : 0 < 2 * r := by positivity
  have ha : AnalyticOnNhd ℂ f (closedBall 0 |2 * r|) := fun z _ => entire_analytic hf z
  have hb := (maximumModulus_attained f
    (show Differentiable ℂ f from fun z => hf.2 z (mem_univ _)).continuous
      (2 * r) h2r).choose_spec.2.2
  have h := ha.sum_divisor_le (r := r) (R := 2 * r) (M := maximumModulus f (2 * r))
    (by simpa [abs_of_pos hr] using hr)
    (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith)
    (one_le_maximumModulus hf h0 h2r) (by simp [h0])
    (by simpa only [maximumModulus, abs_of_pos h2r] using hb)
  rw [abs_of_pos hr] at h
  have hc := count_cast_eq_divisor F r
  change (zeroCount f r : ℤ) = _ at hc
  rw [← hc] at h
  have hratio : 2 * r / r = 2 := by field_simp
  rw [h0, norm_one, div_one, hratio] at h
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h

/-- A center factor is extended to the whole plane by the ordinary quotient
away from zero. Analyticity at zero is supplied by local factorization. -/
lemma entire_center_factor (f : NonzeroEntireFunction) :
    ∃ (m : ℕ) (q : ℂ → ℂ), analyticOrderAt f.toFun 0 = (m : ℕ∞) ∧
      HolomorphicOn univ q ∧ q 0 ≠ 0 ∧ ∀ z, f.toFun z = z ^ m * q z := by
  let m := (analyticOrderAt f.toFun 0).toNat
  have hm : analyticOrderAt f.toFun 0 = (m : ℕ∞) :=
    (ENat.natCast_toNat (zero_multiplicity_finite f 0)).symm
  obtain ⟨u, hu, hu0, he⟩ := (entire_analytic f.holomorphic 0).analyticOrderAt_eq_natCast.mp hm
  let q : ℂ → ℂ := fun z => if z = 0 then u 0 else f.toFun z / z ^ m
  have hnear : u =ᶠ[𝓝 0] q := by
    filter_upwards [he] with z hz
    dsimp [q]
    split_ifs with h
    · subst z; rfl
    · simp only [sub_zero, smul_eq_mul] at hz
      rw [hz]
      exact (mul_div_cancel_left₀ (u z) (pow_ne_zero m h)).symm
  have hq0 : AnalyticAt ℂ q 0 := hu.congr hnear
  have hq : HolomorphicOn univ q := by
    refine ⟨isOpen_univ, fun z _ => ?_⟩
    by_cases hz : z = 0
    · subst z; exact hq0.differentiableAt
    · have hn : q =ᶠ[𝓝 z] (fun w => f.toFun w / w ^ m) := by
        filter_upwards [continuousAt_id.eventually_ne hz] with w hw
        simp [q, show w ≠ 0 from hw]
      exact (((f.holomorphic.2 z (mem_univ _)).div
        (differentiableAt_id.pow m) (pow_ne_zero m hz)).congr_of_eventuallyEq hn)
  refine ⟨m, q, hm, hq, by simpa [q] using hu0, fun z => ?_⟩
  by_cases hz : z = 0
  · subst z
    simpa [q, smul_eq_mul] using he.self_of_nhds
  · dsimp [q]
    rw [ite_eq_right hz]
    exact (mul_div_cancel₀ (f.toFun z) (pow_ne_zero m hz)).symm

lemma counts_split_center (f g : NonzeroEntireFunction) (m : ℕ)
    (hm : analyticOrderAt f.toFun 0 = (m : ℕ∞)) (hg0 : g.toFun 0 ≠ 0)
    (he : ∀ z, z ≠ 0 → analyticOrderAt f.toFun z = analyticOrderAt g.toFun z)
    (r : ℝ) (hr : 0 ≤ r) : zeroCount f.toFun r = m + zeroCount g.toFun r := by
  let a : ℂ → ℕ := fun z => if z = 0 then m else 0
  have ha : Function.HasFiniteSupport a := by
    apply (finite_singleton (0 : ℂ)).subset
    intro z hz
    by_contra hn
    exact hz (by simp [a, show z ≠ 0 from hn] )
  have hg : analyticOrderAt g.toFun 0 = 0 :=
    (entire_analytic g.holomorphic 0).analyticOrderAt_eq_zero.mpr hg0
  change (∑ᶠ z : ℂ, if ‖z‖ ≤ r then (analyticOrderAt f.toFun z).toNat else 0) = _
  calc
    _ = ∑ᶠ z : ℂ, (a z + if ‖z‖ ≤ r then (analyticOrderAt g.toFun z).toNat else 0) := by
      apply finsum_congr
      intro z
      by_cases hz : z = 0
      · subst z; simp [a, hm, hg, hr]
      · simp [a, hz, he z hz]
    _ = (∑ᶠ z, a z) + zeroCount g.toFun r :=
      finsum_add_distrib ha (count_support_finite g r)
    _ = m + zeroCount g.toFun r := by
      rw [finsum_eq_single a 0 (by intro z hz; simp [a, hz])]
      simp [a]

theorem center_reduction : Specs.D12Complex.Ch17.ZeroCounting.center_reduction_type := by
  intro f
  obtain ⟨m, q, hm, hq, hq0, he⟩ := entire_center_factor f
  let c : ℂ := q 0
  let g : ℂ → ℂ := fun z => q z / c
  have hc : c ≠ 0 := hq0
  have hg : HolomorphicOn univ g :=
    ⟨isOpen_univ, fun z _ => (hq.2 z (mem_univ _)).div_const c⟩
  have hg0 : g 0 = 1 := div_self hc
  have hqg (z : ℂ) : q z = c * g z := by
    dsimp [g]
    exact (mul_div_cancel₀ (q z) hc).symm
  have hfg (z : ℂ) : f.toFun z = z ^ m * (c * g z) := by rw [he, hqg]
  have hord (z : ℂ) (hz : z ≠ 0) : analyticOrderAt f.toFun z = analyticOrderAt g z := by
    have hfun : f.toFun = (fun w : ℂ => w ^ m * c) * g := by
      funext w
      simpa only [Pi.mul_apply, mul_assoc] using hfg w
    rw [hfun, analyticOrderAt_mul (by fun_prop) (entire_analytic hg z)]
    have hp : analyticOrderAt (fun w : ℂ => w ^ m * c) z = 0 :=
      (show AnalyticAt ℂ (fun w : ℂ => w ^ m * c) z by fun_prop).analyticOrderAt_eq_zero.mpr
        (mul_ne_zero (pow_ne_zero m hz) hc)
    rw [hp, zero_add]
  let G : NonzeroEntireFunction := ⟨g, hg, ⟨0, by simp [hg0]⟩⟩
  refine ⟨m, c, g, hm, hc, hg, hg0, hfg, hord, ?_, ?_⟩
  · intro r hr
    exact counts_split_center f G m hm (by simp [G, hg0]) hord r hr
  · exact counting_zeros g hg hg0

end D12Complex.ZeroCounting
