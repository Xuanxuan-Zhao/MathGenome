import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Resonance
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.Frobenius
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.ReductionOrder
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section

namespace D13Unified.Ch09.Resonance
open Specs.D13Unified.Ch09.Indicial
open Specs.D13Unified.Ch09.Frobenius
open Specs.D13Unified.Ch09.Resonance
open scoped Topology

lemma indicial_factorization (E : Equation) (r₁ r₂ : ℂ)
    (hr : AreIndicialRoots E r₁ r₂) (z : ℂ) :
    indicialValue E z = (z - r₁) * (z - r₂) := by
  rw [indicialValue, hr.1, hr.2]
  ring

lemma larger_root_nonresonant (E : Equation) (r₁ r₂ : ℂ) (m : ℕ)
    (hr : AreIndicialRoots E r₁ r₂) (hm : r₁ - r₂ = (m : ℂ)) :
    Nonresonant E r₁ := by
  intro n hn
  rw [indicial_factorization E r₁ r₂ hr]
  have hnm : r₁ + (n : ℂ) - r₂ = ((m + n : ℕ) : ℂ) := by
    push_cast
    linear_combination hm
  rw [add_sub_cancel_left, hnm]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))

theorem firstSolution : firstSolutionType := by
  intro E L r₁ r₂ m hr hm
  have hroot : indicialValue E r₁ = 0 := by
    rw [indicial_factorization E r₁ r₂ hr]; simp
  obtain ⟨s, hs, _⟩ := Frobenius.frobenius E L r₁ hroot
    (larger_root_nonresonant E r₁ r₂ m hr hm)
  exact ⟨series s, hs.2.1.1, hs.2.1.2.2.1, hs.2.2⟩

/-- Removing successively the Taylor coefficients gives a holomorphic
remainder. Its primitive, together with a finite pole part and one logarithm,
constructs the actual primitive needed in resonant reduction of order. -/
lemma pole_primitive (E : Equation) (L : LogBranch E.radius) (m : ℕ)
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h (Metric.ball 0 E.radius)) :
    ∃ B : ℂ → ℂ, ∃ c : ℂ,
      DifferentiableOn ℂ B (Metric.ball 0 E.radius) ∧
      (m = 0 → c = h 0) ∧ (m ≠ 0 → B 0 = -h 0 / (m : ℂ)) ∧
      ∀ z ∈ slitDiscValue E.radius L.angle,
        HasDerivAt (fun w => B w / w ^ m + c * L.log w)
          (h z / z ^ (m + 1)) z := by
  induction m generalizing h with
  | zero =>
    have hg : DifferentiableOn ℂ (dslope h 0) (Metric.ball 0 E.radius) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self E.radius_pos))).mpr hh
    have hsc : IsSimplyConnected (Metric.ball (0 : ℂ) E.radius) :=
      @SimplyConnectedSpace.ofContractible _ _
        ((convex_ball (0 : ℂ) E.radius).contractibleSpace
          ⟨0, Metric.mem_ball_self E.radius_pos⟩)
    obtain ⟨P, hP0, hP⟩ := ReductionOrder.normalized_holomorphic_primitive
      (t₀ := 0) Metric.isOpen_ball hsc hg
    refine ⟨P, h 0, (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt),
      (fun _ => rfl), (fun hn => (hn rfl).elim), ?_⟩
    intro z hz
    have hgeom := Indicial.setup.2.2.1 E.radius L.angle E.radius_pos
    have hz0 := hgeom.2.2.2 z hz
    convert (hP z (hgeom.2.2.1 hz)).add
      ((Frobenius.hasDerivAt_branchLog E L hz).const_mul (h 0)) using 1
    · ext w; simp
    · rw [dslope_of_ne h hz0]
      simp only [slope, sub_zero, smul_eq_mul, inv_mul_eq_div, vsub_eq_sub]
      field_simp
      ring
  | succ m ih =>
    let g := dslope h 0
    have hg : DifferentiableOn ℂ g (Metric.ball 0 E.radius) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self E.radius_pos))).mpr hh
    obtain ⟨B, c, hB, _hc, _hB0, hd⟩ := ih g hg
    let C : ℂ := -h 0 / (m + 1 : ℂ)
    let Bnew : ℂ → ℂ := fun z => C + z * B z
    refine ⟨Bnew, c, (differentiableOn_const C).add (differentiableOn_id.mul hB),
      (fun he => (Nat.succ_ne_zero m he).elim), ?_, ?_⟩
    · intro _
      simp [Bnew, C, Nat.cast_add, Nat.cast_one]
    · intro z hz
      have hgeom := Indicial.setup.2.2.1 E.radius L.angle E.radius_pos
      have hz0 := hgeom.2.2.2 z hz
      have hpow := (hasDerivAt_const z C).div
        ((hasDerivAt_id z).pow (m + 1)) (pow_ne_zero _ hz0)
      have hsum := hpow.add (hd z hz)
      have heq : (fun w => C / w ^ (m + 1) + (B w / w ^ m + c * L.log w)) =ᶠ[𝓝 z]
          (fun w => Bnew w / w ^ (m + 1) + c * L.log w) := by
        filter_upwards [eventually_ne_nhds hz0] with w hw
        dsimp [Bnew]
        field_simp
        ring
      convert hsum.congr_of_eventuallyEq heq.symm using 1
      dsimp [C, g]
      rw [dslope_of_ne h hz0]
      simp only [slope, sub_zero, smul_eq_mul, inv_mul_eq_div, vsub_eq_sub]
      push_cast
      field_simp
      ring

lemma power_add {R : ℝ} (L : LogBranch R) (r s z : ℂ) :
    powerValue L (r + s) z = powerValue L r z * powerValue L s z := by
  simp only [powerValue, add_mul, Complex.exp_add]

lemma power_nat {R : ℝ} (L : LogBranch R) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitDiscValue R L.angle) : powerValue L (n : ℂ) z = z ^ n := by
  induction n with
  | zero => simp [powerValue]
  | succ n ih =>
    rw [Nat.cast_succ, power_add, ih]
    simp [powerValue, L.exp_log z hz, pow_succ]

lemma solution_congr (E : Equation) (L : LogBranch E.radius) {y v : ℂ → ℂ}
    (h : Set.EqOn y v (slitDiscValue E.radius L.angle))
    (hy : solutionValue E L y) : solutionValue E L v := by
  have hgeom := Indicial.setup.2.2.1 E.radius L.angle E.radius_pos
  have heq (z : ℂ) (hz : z ∈ slitDiscValue E.radius L.angle) : y =ᶠ[𝓝 z] v :=
    Filter.eventuallyEq_of_mem (hgeom.1.mem_nhds hz) h
  have hd : Set.EqOn (deriv y) (deriv v) (slitDiscValue E.radius L.angle) :=
    fun z hz => (heq z hz).deriv_eq
  refine ⟨hy.1.congr h.symm, hy.2.1.congr hd.symm, ?_⟩
  intro z hz
  have hdd : deriv (deriv y) z = deriv (deriv v) z :=
    (Filter.eventuallyEq_of_mem (hgeom.1.mem_nhds hz) hd).deriv_eq
  rw [← hdd, ← hd hz, ← h hz]
  exact hy.2.2 z hz

lemma solution_const_mul (E : Equation) (L : LogBranch E.radius) {y : ℂ → ℂ}
    (hy : solutionValue E L y) (c : ℂ) :
    solutionValue E L (fun z => c * y z) := by
  refine ⟨hy.1.const_mul c, ?_, ?_⟩
  · rw [deriv_const_mul_field']
    exact hy.2.1.const_mul c
  · intro z hz
    rw [deriv_const_mul_field', deriv_const_mul_field]
    linear_combination c * hy.2.2 z hz

lemma reduction_pair (E : Equation) (L : LogBranch E.radius) (y e v : ℂ → ℂ)
    (hy : solutionValue E L y)
    (hne : ∀ z ∈ slitDiscValue E.radius L.angle, y z ≠ 0)
    (he : ∀ z ∈ slitDiscValue E.radius L.angle,
      HasDerivAt e (-(E.p z / z) * e z) z)
    (he0 : ∀ z ∈ slitDiscValue E.radius L.angle, e z ≠ 0)
    (hv : ∀ z ∈ slitDiscValue E.radius L.angle,
      HasDerivAt v (e z / y z ^ 2) z) :
    solutionValue E L (fun z => y z * v z) ∧
      independentValue L y (fun z => y z * v z) := by
  let D := slitDiscValue E.radius L.angle
  have hgeom := Indicial.setup.2.2.1 E.radius L.angle E.radius_pos
  have hp : DifferentiableOn ℂ (fun z => E.p z / z) D :=
    (E.p_holomorphic.mono hgeom.2.2.1).div differentiableOn_id hgeom.2.2.2
  have hq : DifferentiableOn ℂ (fun z => E.q z / z ^ 2) D :=
    (E.q_holomorphic.mono hgeom.2.2.1).div (differentiableOn_id.pow 2)
      (fun z hz => pow_ne_zero _ (hgeom.2.2.2 z hz))
  have hS : ReductionOrder.IsSecondOrderSolutionOn D
      (fun z => E.p z / z) (fun z => E.q z / z ^ 2) y (deriv y) (deriv (deriv y)) := by
    refine ⟨hy.1.continuousOn, hy.2.1.continuousOn,
      (hy.2.1.deriv hgeom.1).continuousOn, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hy.1 z hz).differentiableAt (hgeom.1.mem_nhds hz)).hasDerivAt.hasDerivWithinAt
    · intro z hz
      exact ((hy.2.1 z hz).differentiableAt (hgeom.1.mem_nhds hz)).hasDerivAt.hasDerivWithinAt
    · intro z hz
      have hz0 := hgeom.2.2.2 z hz
      field_simp
      linear_combination hy.2.2 z hz
  obtain ⟨dy, ddy, hs, hW⟩ := ReductionOrder.reduction_from_primitives
    hp.continuousOn hq.continuousOn hS hne
    (fun z hz => (he z hz).hasDerivWithinAt) (fun z hz => (hv z hz).hasDerivWithinAt)
  have hd (z : ℂ) (hz : z ∈ D) : deriv (fun w => y w * v w) z = dy z :=
    ((hs.2.2.2.1 z hz).hasDerivAt (hgeom.1.mem_nhds hz)).deriv
  have hdd (z : ℂ) (hz : z ∈ D) : deriv (deriv (fun w => y w * v w)) z = ddy z := by
    have hd' := (hs.2.2.2.2.1 z hz).hasDerivAt (hgeom.1.mem_nhds hz)
    exact (hd'.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
      (hgeom.1.mem_nhds hz) hd)).deriv
  constructor
  · refine ⟨(fun z hz => ((hs.2.2.2.1 z hz).hasDerivAt
        (hgeom.1.mem_nhds hz)).differentiableAt.differentiableWithinAt), ?_, ?_⟩
    · have hdhol : DifferentiableOn ℂ dy D := fun z hz =>
        ((hs.2.2.2.2.1 z hz).hasDerivAt (hgeom.1.mem_nhds hz)).differentiableAt.differentiableWithinAt
      exact hdhol.congr (fun z hz => hd z hz)
    · intro z hz
      rw [hd z hz, hdd z hz]
      have hh := hs.2.2.2.2.2 z hz
      have hz0 := hgeom.2.2.2 z hz
      field_simp at hh
      linear_combination hh
  · obtain ⟨z, hz, _⟩ := Frobenius.exists_slitDisc_near_zero E L E.radius_pos
    exact ReductionOrder.independentOn_of_wronskian hz (hgeom.1.uniqueDiffOn z hz)
      (hS.2.2.2.1 z hz) (hs.2.2.2.1 z hz) (by rw [hW z hz]; exact he0 z hz)

lemma independent_scaled_congr (E : Equation) (L : LogBranch E.radius)
    {y v w : ℂ → ℂ} (h : independentValue L y v) {k : ℂ} (hk : k ≠ 0)
    (heq : Set.EqOn (fun z => k * v z) w (slitDiscValue E.radius L.angle)) :
    independentValue L y w := by
  intro a b hab
  have hh := h a (b * k) (fun z hz => by
    have ht := hab z hz
    rw [← heq hz] at ht
    convert ht using 1
    ring)
  exact ⟨hh.1, (mul_eq_zero.mp hh.2).resolve_right hk⟩

/-- The local construction once the first analytic multiplier is nonvanishing.
No assumption about a second solution or a logarithmic obstruction is used. -/
lemma second_of_nonvanishing (E : Equation) (L : LogBranch E.radius)
    (r₁ r₂ : ℂ) (m : ℕ) (hr : AreIndicialRoots E r₁ r₂)
    (hm : r₁ - r₂ = (m : ℂ)) (a : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a (Metric.ball 0 E.radius)) (ha0 : a 0 = 1)
    (han : ∀ z ∈ Metric.ball 0 E.radius, a z ≠ 0)
    (hy : solutionValue E L (fun z => powerValue L r₁ z * a z)) :
    ∃ b : ℂ → ℂ, ∃ c : ℂ,
      DifferentiableOn ℂ b (Metric.ball 0 E.radius) ∧ (m ≠ 0 → b 0 = 1) ∧
      solutionValue E L (secondFunction E L r₁ r₂ m a b c) ∧
      independentValue L (fun z => powerValue L r₁ z * a z)
        (secondFunction E L r₁ r₂ m a b c) := by
  have hgeom := Indicial.setup.2.2.1 E.radius L.angle E.radius_pos
  have hg : DifferentiableOn ℂ (dslope E.p 0) (Metric.ball 0 E.radius) :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self E.radius_pos))).mpr E.p_holomorphic
  have hsc : IsSimplyConnected (Metric.ball (0 : ℂ) E.radius) :=
    @SimplyConnectedSpace.ofContractible _ _
      ((convex_ball (0 : ℂ) E.radius).contractibleSpace
        ⟨0, Metric.mem_ball_self E.radius_pos⟩)
  obtain ⟨P, hP0, hP⟩ := ReductionOrder.normalized_holomorphic_primitive
    (t₀ := 0) Metric.isOpen_ball hsc hg
  have hPhol : DifferentiableOn ℂ P (Metric.ball 0 E.radius) :=
    fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  let h : ℂ → ℂ := fun z => Complex.exp (-P z) / a z ^ 2
  have hh : DifferentiableOn ℂ h (Metric.ball 0 E.radius) :=
    (Complex.differentiable_exp.comp_differentiableOn hPhol.neg).div (ha.pow 2)
      (fun z hz => pow_ne_zero _ (han z hz))
  have hh0 : h 0 = 1 := by simp [h, hP0, ha0]
  let e : ℂ → ℂ := fun z => powerValue L (-pZeroValue E) z * Complex.exp (-P z)
  let y : ℂ → ℂ := fun z => powerValue L r₁ z * a z
  have he0 : ∀ z ∈ slitDiscValue E.radius L.angle, e z ≠ 0 :=
    fun z _ => mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have he : ∀ z ∈ slitDiscValue E.radius L.angle,
      HasDerivAt e (-(E.p z / z) * e z) z := by
    intro z hz
    have hz0 := hgeom.2.2.2 z hz
    have hp0 := (Indicial.setup.1 E).1
    convert (Frobenius.hasDerivAt_branchPower E L (-pZeroValue E) hz).mul
      ((hP z (hgeom.2.2.1 hz)).neg.cexp) using 1
    dsimp [e]
    rw [dslope_of_ne E.p hz0]
    simp only [slope, sub_zero, smul_eq_mul, inv_mul_eq_div, vsub_eq_sub]
    rw [hp0]
    field_simp
    ring
  have forcing (z : ℂ) (hz : z ∈ slitDiscValue E.radius L.angle) :
      e z / y z ^ 2 = h z / z ^ (m + 1) := by
    have hz0 := hgeom.2.2.2 z hz
    have ha' := han z (hgeom.2.2.1 hz)
    have hp : powerValue L r₁ z ^ 2 = powerValue L (-pZeroValue E) z * z ^ (m + 1) := by
      calc
        _ = powerValue L (r₁ + r₁) z := by rw [power_add]; ring
        _ = powerValue L (-pZeroValue E + ((m + 1 : ℕ) : ℂ)) z := by
          congr 1
          push_cast
          linear_combination hr.1 + hm
        _ = _ := by rw [power_add, power_nat L (m + 1) hz]
    dsimp [e, y, h]
    rw [mul_pow, hp]
    have hpn : powerValue L (-pZeroValue E) z ≠ 0 := Complex.exp_ne_zero _
    field_simp
  obtain ⟨B, c, hB, hc, hB0, hV⟩ := pole_primitive E L m h hh
  let V : ℂ → ℂ := fun z => B z / z ^ m + c * L.log z
  have hv : ∀ z ∈ slitDiscValue E.radius L.angle, HasDerivAt V (e z / y z ^ 2) z := by
    intro z hz
    rw [forcing z hz]
    exact hV z hz
  have hyn : ∀ z ∈ slitDiscValue E.radius L.angle, y z ≠ 0 :=
    fun z hz => mul_ne_zero (Complex.exp_ne_zero _) (han z (hgeom.2.2.1 hz))
  obtain ⟨hsol, hind⟩ := reduction_pair E L y e V hy hyn he he0 hv
  by_cases hm0 : m = 0
  · subst m
    have hc1 : c = 1 := (hc rfl).trans hh0
    let b : ℂ → ℂ := fun z => a z * B z
    have heq : Set.EqOn (fun z => y z * V z)
        (secondFunction E L r₁ r₂ 0 a b 0) (slitDiscValue E.radius L.angle) := by
      intro z _
      dsimp [secondFunction, y, V, b]
      simp only [pow_zero, div_one, hc1, one_mul]
      ring
    refine ⟨b, 0, ha.mul hB, (fun hn => (hn rfl).elim),
      solution_congr E L heq hsol, ?_⟩
    apply independent_scaled_congr E L hind (k := 1) one_ne_zero
    intro z hz
    simpa only [one_mul] using heq hz
  · let b : ℂ → ℂ := fun z => -(m : ℂ) * a z * B z
    let cnew : ℂ := -(m : ℂ) * c
    have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    have hb0 : b 0 = 1 := by
      dsimp [b]
      rw [ha0, hB0 hm0, hh0]
      field_simp
    have heq : Set.EqOn (fun z => -(m : ℂ) * (y z * V z))
        (secondFunction E L r₁ r₂ m a b cnew) (slitDiscValue E.radius L.angle) := by
      intro z hz
      have hp : powerValue L r₁ z = powerValue L r₂ z * z ^ m := by
        calc
          _ = powerValue L (r₂ + (m : ℂ)) z := by congr 1; linear_combination hm
          _ = _ := by rw [power_add, power_nat L m hz]
      dsimp [secondFunction, y, V, b, cnew]
      rw [ite_eq_right (by exact hm0), hp]
      have hz0 := hgeom.2.2.2 z hz
      field_simp
      ring
    exact ⟨b, cnew, (ha.const_mul _).mul hB, (fun _ => hb0),
      solution_congr E L heq (solution_const_mul E L hsol _),
      independent_scaled_congr E L hind (neg_ne_zero.mpr hmne) heq⟩

/-- The complete repeated/resonant Frobenius theorem, on a restricted domain
carrying the original branch without a new choice of logarithm. -/
theorem resonance : resonanceType := by
  intro E L r₁ r₂ m hr hm
  obtain ⟨a, ha⟩ := firstSolution E L r₁ r₂ m hr hm
  have h0 : (0 : ℂ) ∈ Metric.ball 0 E.radius := Metric.mem_ball_self E.radius_pos
  have hc : ContinuousAt a 0 := ha.1.continuousOn.continuousAt
    (Metric.isOpen_ball.mem_nhds h0)
  obtain ⟨ε, hε, hεa⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.eventually_ne (by rw [ha.2.1]; exact one_ne_zero))
  let ρ := min ε E.radius / 2
  have hρ : 0 < ρ := half_pos (lt_min hε E.radius_pos)
  have hρmin : ρ < min ε E.radius := half_lt_self (lt_min hε E.radius_pos)
  have hR : ρ < E.radius := hρmin.trans_le (min_le_right _ _)
  let E' := restrictEquation E ρ hρ hR.le
  let L' := restrictBranch E L ρ hρ hR.le
  have ha' : DifferentiableOn ℂ a (Metric.ball 0 E'.radius) :=
    ha.1.mono (Metric.ball_subset_ball hR.le)
  have han : ∀ z ∈ Metric.ball 0 E'.radius, a z ≠ 0 := by
    intro z hz
    exact hεa z (Metric.ball_subset_ball (hρmin.le.trans (min_le_left ε E.radius)) hz)
  have hy' : solutionValue E' L' (fun z => powerValue L' r₁ z * a z) :=
    ⟨ha.2.2.1.mono (slitDisc_mono hR.le), ha.2.2.2.1.mono (slitDisc_mono hR.le),
      fun z hz => ha.2.2.2.2 z (slitDisc_mono hR.le hz)⟩
  obtain ⟨b, c, hb, hb0, hsol, hind⟩ := second_of_nonvanishing E' L'
    r₁ r₂ m hr hm a ha' ha.2.1 han hy'
  exact ⟨a, ha, ρ, hρ, hR, b, c, hb, hb0, hsol, hind⟩

end D13Unified.Ch09.Resonance
