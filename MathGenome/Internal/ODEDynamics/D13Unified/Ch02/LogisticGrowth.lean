import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.LogisticGrowth
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter Metric
open scoped Topology
open Specs.D13Unified.Ch01.SolutionConcepts
open D13Unified.Logistic

namespace D13Unified.Ch02.LogisticGrowth

@[simp] lemma field_eval (r K t x : ℝ) :
    (field r K).eval t x = r * x * (1 - x / K) := by
  rw [ODE.eval_of_mem (field r K) (by trivial)]; rfl

@[simp] lemma exponentialField_eval (r t x : ℝ) :
    (exponentialField r).eval t x = r * x := by
  rw [ODE.eval_of_mem (exponentialField r) (by trivial)]; rfl

lemma exp_deriv (r s t : ℝ) :
    HasDerivAt (fun t => Real.exp (r * (t - s)))
      (Real.exp (r * (t - s)) * r) t := by
  simpa using (((hasDerivAt_id t).sub_const s).const_mul r).exp

lemma denominator_deriv (r K s ξ t : ℝ) :
    HasDerivAt (denominator r K s ξ)
      (ξ * Real.exp (r * (t - s)) * r) t := by
  convert! (((exp_deriv r s t).sub_const 1).const_mul ξ).const_add K using 1
  ring

lemma denominator_continuous (r K s ξ : ℝ) : Continuous (denominator r K s ξ) :=
  continuous_iff_continuousAt.mpr fun t => (denominator_deriv r K s ξ t).continuousAt

lemma curve_initial (r K s ξ : ℝ) (hK : K ≠ 0) : curve r K s ξ s = ξ := by
  simp [curve, denominator, hK]

lemma curve_deriv (r K s ξ t : ℝ) (hK : K ≠ 0)
    (hD : denominator r K s ξ t ≠ 0) :
    HasDerivAt (curve r K s ξ)
      (r * curve r K s ξ t * (1 - curve r K s ξ t / K)) t := by
  have h := ((exp_deriv r s t).const_mul (K * ξ)).div
    (denominator_deriv r K s ξ t) hD
  convert! h using 1
  dsimp [curve, denominator]
  dsimp [denominator] at hD
  field_simp [hK, hD]

/-- No sign restriction on the initial state is used in local uniqueness. -/
lemma field_locallyLipschitz (r K : ℝ) : (field r K).LocallyLipschitzInState := by
  intro s ξ _
  let B := |ξ| + 1
  let L := |r| + |r / K| * (2 * B)
  refine ⟨1, 1, L, by norm_num, by norm_num, by dsimp [L, B]; positivity,
    fun _ _ => trivial, ?_⟩
  intro t _ x hx y hy
  have hb (z : ℝ) (hz : z ∈ ball ξ 1) : |z| ≤ B := by
    have hz' : |z - ξ| < 1 := by simpa [Real.dist_eq] using hz
    have := abs_sub_abs_le_abs_sub z ξ
    dsimp [B]
    linarith
  have hxB := hb x hx
  have hyB := hb y hy
  have hcoef : |r - r / K * (x + y)| ≤ L := by
    calc
      _ ≤ |r| + |r / K * (x + y)| := abs_sub _ _
      _ = |r| + |r / K| * |x + y| := by rw [abs_mul]
      _ ≤ |r| + |r / K| * (2 * B) := by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left ((abs_add_le x y).trans (by linarith)) (abs_nonneg _)
  have halg : r * x * (1 - x / K) - r * y * (1 - y / K) =
      (r - r / K * (x + y)) * (x - y) := by ring
  simp only [field_eval, Real.norm_eq_abs, halg, abs_mul]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

lemma pole_exp (r K s ξ : ℝ) (hr : r ≠ 0) (hp : 0 < 1 - K / ξ) :
    Real.exp (r * (pole r K s ξ - s)) = 1 - K / ξ := by
  have h : r * (pole r K s ξ - s) = Real.log (1 - K / ξ) := by
    dsimp [pole]; field_simp; ring
  rw [h, Real.exp_log hp]

lemma outside_data {K ξ : ℝ} (hK : 0 < K) (h : ξ < 0 ∨ K < ξ) :
    ξ ≠ 0 ∧ 0 < 1 - K / ξ := by
  rcases h with h | h
  · exact ⟨ne_of_lt h, by have := div_neg_of_pos_of_neg hK h; linarith⟩
  · have hξ : 0 < ξ := hK.trans h
    exact ⟨ne_of_gt hξ, by have := (div_lt_one hξ).mpr h; linarith⟩

lemma denominator_zero_iff (r K s ξ t : ℝ) (hr : r ≠ 0)
    (hξ : ξ ≠ 0) (hp : 0 < 1 - K / ξ) :
    denominator r K s ξ t = 0 ↔ t = pole r K s ξ := by
  have hval := pole_exp r K s ξ hr hp
  constructor
  · intro hd
    have he : Real.exp (r * (t - s)) = Real.exp (r * (pole r K s ξ - s)) := by
      rw [hval]
      dsimp [denominator] at hd
      apply (eq_sub_iff_add_eq).mpr
      field_simp
      nlinarith
    have he' := Real.exp_injective he
    have he'' : t - s = pole r K s ξ - s := mul_left_cancel₀ hr he'
    linarith
  · rintro rfl
    dsimp [denominator]
    rw [hval]
    field_simp
    ring

lemma denominator_pos_middle (r K s ξ t : ℝ) (hξ : 0 < ξ) (hξK : ξ < K) :
    0 < denominator r K s ξ t := by
  have := mul_pos hξ (Real.exp_pos (r * (t - s)))
  dsimp [denominator]
  linarith

lemma pole_before (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K) (hξ : K < ξ) :
    pole r K s ξ < s := by
  have hξp : 0 < ξ := hK.trans hξ
  have hp : 0 < 1 - K / ξ := (outside_data hK (Or.inr hξ)).2
  have hlog : Real.log (1 - K / ξ) < 0 :=
    Real.log_neg hp (by have := div_pos hK hξp; linarith)
  dsimp [pole]
  have := mul_neg_of_pos_of_neg (inv_pos.mpr hr) hlog
  linarith

lemma pole_after (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K) (hξ : ξ < 0) :
    s < pole r K s ξ := by
  have hlog : 0 < Real.log (1 - K / ξ) :=
    Real.log_pos (by have := div_neg_of_pos_of_neg hK hξ; linarith)
  dsimp [pole]
  have := mul_pos (inv_pos.mpr hr) hlog
  linarith

lemma denominator_ne_on_domain (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K)
    {t : ℝ} (ht : t ∈ domain r K s ξ) : denominator r K s ξ t ≠ 0 := by
  by_cases hξ : ξ < 0
  · have ht' : t < pole r K s ξ := by simpa [domain, hξ] using ht
    exact fun hz => ht'.ne ((denominator_zero_iff r K s ξ t hr.ne'
      (outside_data hK (Or.inl hξ)).1 (outside_data hK (Or.inl hξ)).2).mp hz)
  by_cases hξK : K < ξ
  · have ht' : pole r K s ξ < t := by simpa [domain, hξ, hξK] using ht
    exact fun hz => ht'.ne' ((denominator_zero_iff r K s ξ t hr.ne'
      (outside_data hK (Or.inr hξK)).1 (outside_data hK (Or.inr hξK)).2).mp hz)
  have hξ0 : 0 ≤ ξ := le_of_not_gt hξ
  have hξK' : ξ ≤ K := le_of_not_gt hξK
  have hexp := Real.exp_pos (r * (t - s))
  by_cases heq : ξ = 0
  · simpa [denominator, heq] using hK.ne'
  have hpos : 0 < ξ := lt_of_le_of_ne hξ0 (Ne.symm heq)
  have hmul := mul_pos hpos hexp
  dsimp [denominator]
  linarith


/-- The zero is simple and the numerator does not vanish there. Inversion of
this zero forces blow-up on both sides, independently of totalized values. -/
theorem logistic_poles : Specs.D13Unified.Ch02.LogisticGrowth.logisticPolesExpected := by
  intro r K hr hK s ξ hout
  obtain ⟨hξ, hp⟩ := outside_data hK hout
  let p := pole r K s ξ
  have hzero : denominator r K s ξ p = 0 :=
    (denominator_zero_iff r K s ξ p hr.ne' hξ hp).mpr rfl
  have hnum : K * ξ * Real.exp (r * (p - s)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hK.ne' hξ) (Real.exp_ne_zero _)
  refine ⟨hzero, denominator_deriv r K s ξ p,
    mul_ne_zero (mul_ne_zero hξ (Real.exp_ne_zero _)) hr.ne', hnum, ?_⟩
  have hDlim : Tendsto (denominator r K s ξ) (𝓝[≠] p) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [hzero] using
        ((denominator_continuous r K s ξ).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[≠] p ≤ 𝓝 p))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun hz => ht ((denominator_zero_iff r K s ξ t hr.ne' hξ hp).mp hz)
  have hinv := tendsto_norm_inv_nhdsNE_zero_atTop.comp hDlim
  have hNlim := (((exp_deriv r s p).const_mul (K * ξ)).continuousAt.norm.tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] p ≤ 𝓝 p)
  simpa only [curve, div_eq_mul_inv, norm_mul, Function.comp_apply, p] using
    hNlim.pos_mul_atTop (norm_pos_iff.mpr hnum) hinv

lemma curve_alternative (r K s ξ t : ℝ) :
    curve r K s ξ t = K * ξ / (ξ + (K - ξ) / Real.exp (r * (t - s))) := by
  have hd : ξ + (K - ξ) / Real.exp (r * (t - s)) =
      denominator r K s ξ t / Real.exp (r * (t - s)) := by
    dsimp [denominator]
    field_simp
    ring
  rw [hd]
  simp only [curve, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem logistic_dynamics : Specs.D13Unified.Ch02.LogisticGrowth.logisticDynamicsExpected := by
  intro r K hr hK s
  refine ⟨⟨by simp [domain, not_lt.mpr hK.le], fun t => by simp [curve]⟩,
    ⟨by simp [domain, not_lt.mpr hK.le], ?_⟩, ?_⟩
  · intro t
    have hD : denominator r K s K t = K * Real.exp (r * (t - s)) := by
      dsimp [denominator]; ring
    rw [curve, hD]
    field_simp
  intro ξ hξ hξK
  have hd (t : ℝ) := denominator_pos_middle r K s ξ t hξ hξK
  have hcpos (t : ℝ) : 0 < curve r K s ξ t :=
    div_pos (mul_pos (mul_pos hK hξ) (Real.exp_pos _)) (hd t)
  have hclt (t : ℝ) : curve r K s ξ t < K := by
    apply (div_lt_iff₀ (hd t)).mpr
    dsimp [denominator]
    nlinarith
  refine ⟨by simp [domain, not_lt.mpr hξ.le, not_lt.mpr hξK.le], hd, ?_, ?_, ?_⟩
  · apply strictMono_of_hasDerivAt_pos
      (fun t => curve_deriv r K s ξ t hK.ne' (hd t).ne')
    intro t
    exact mul_pos (mul_pos hr (hcpos t))
      (sub_pos.mpr ((div_lt_one hK).mpr (hclt t)))
  · have ht : Tendsto (fun t : ℝ => r * (t - s)) atBot atBot := by
      simpa only [sub_eq_add_neg, id_eq] using
        (((tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).atBot_add
          (tendsto_const_nhds (x := -s))).const_mul_atBot hr)
    have he : Tendsto (fun t => Real.exp (r * (t - s))) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ht
    have hn : Tendsto (fun t => K * ξ * Real.exp (r * (t - s))) atBot (𝓝 0) := by
      simpa using he.const_mul (K * ξ)
    have hden : Tendsto (denominator r K s ξ) atBot (𝓝 (K - ξ)) := by
      convert! ((he.sub_const 1).const_mul ξ).const_add K using 1
      simp [sub_eq_add_neg]
    convert! hn.div hden (sub_pos.mpr hξK).ne' using 1
    simp
  · have ht : Tendsto (fun t : ℝ => r * (t - s)) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        (((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_add
          (tendsto_const_nhds (x := -s))).const_mul_atTop hr)
    have he : Tendsto (fun t => Real.exp (r * (t - s))) atTop atTop :=
      Real.tendsto_exp_atTop.comp ht
    have hden := (he.const_div_atTop (K - ξ)).const_add ξ
    have hh := (tendsto_const_nhds (x := K * ξ)).div hden (by simpa using hξ.ne')
    have hval : K * ξ / (ξ + 0) = K := by simp [hξ.ne']
    rw [hval] at hh
    exact hh.congr (fun t => (curve_alternative r K s ξ t).symm)


/-- A classical curve which contains and agrees with every competitor has no
extension to a strictly larger open interval. -/
lemma maximalFormula_of_restrictions (F : ODE ℝ) (I : OpenTimeInterval)
    (g : ℝ → ℝ) (s ξ : ℝ) (hx : IsClassicalIVPOn F I g s ξ)
    (hall : ∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
      IsClassicalIVPOn F J y s ξ → J.carrier ⊆ I.carrier ∧ EqOn g y J.carrier) :
    MaximalFormula F I.carrier g s ξ := by
  have hmax : maximalValue (⟨I, g, hx.1⟩ : Solution F) := by
    rintro ⟨y, hext, hstrict⟩
    have hy : IsClassicalIVPOn F y.interval y.representative s ξ :=
      ⟨y.isSolution, hext.1 hx.2.1, (hext.2 hx.2.1).trans hx.2.2⟩
    exact hstrict.ne (Subset.antisymm hext.1 (hall y.interval y.representative hy).1)
  refine ⟨I, hx.1, rfl, hx.2.1, hx.2.2, hmax, hall, ?_⟩
  intro y hs hyξ hymax
  obtain ⟨hsub, heq⟩ := hall y.interval y.representative ⟨y.isSolution, hs, hyξ⟩
  have hrev : I.carrier ⊆ y.interval.carrier := by
    by_contra h
    exact hymax ⟨⟨I, g, hx.1⟩, ⟨hsub, heq⟩, ⟨hsub, h⟩⟩
  exact ⟨Subset.antisymm hsub hrev, heq.symm⟩

/-- A continuous function cannot agree with a curve whose norm diverges at an
interior point of its domain, even if agreement is required from only one side. -/
lemma excludes_blowup_point {g y : ℝ → ℝ} (p : ℝ) (S J : Set ℝ)
    [NeBot (𝓝[S] p)] (hS : S ⊆ {p}ᶜ) (hJ : J ∈ 𝓝 p)
    (heq : EqOn g y (S ∩ J)) (hy : ContinuousAt y p)
    (hblow : Tendsto (fun t => ‖g t‖) (𝓝[≠] p) atTop) : False := by
  have heq' : (fun t => ‖g t‖) =ᶠ[𝓝[S] p] (fun t => ‖y t‖) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hJ] with t ht hJt
    exact congrArg norm (heq ⟨ht, hJt⟩)
  have hInf := (hblow.mono_left (nhdsWithin_mono p hS)).congr' heq'
  exact not_tendsto_atTop_of_tendsto_nhds (hy.norm.tendsto.mono_left nhdsWithin_le_nhds) hInf

def solutionInterval (r K s ξ : ℝ) : OpenTimeInterval :=
  if ξ < 0 then OpenTimeInterval.leftRay (pole r K s ξ)
  else if K < ξ then OpenTimeInterval.rightRay (pole r K s ξ)
  else OpenTimeInterval.whole

lemma solutionInterval_carrier (r K s ξ : ℝ) :
    (solutionInterval r K s ξ).carrier = domain r K s ξ := by
  unfold solutionInterval domain
  split_ifs <;> rfl

lemma solutionInterval_initial (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K) :
    s ∈ (solutionInterval r K s ξ).carrier := by
  rw [solutionInterval_carrier]
  by_cases hξ : ξ < 0
  · simpa [domain, hξ] using pole_after r K s ξ hr hK hξ
  by_cases hξK : K < ξ
  · simpa [domain, hξ, hξK] using pole_before r K s ξ hr hK hξK
  simp [domain, hξ, hξK]

lemma curve_isIVP (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K) :
    IsClassicalIVPOn (field r K) (solutionInterval r K s ξ) (curve r K s ξ) s ξ := by
  let I := solutionInterval r K s ξ
  have hd (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (curve r K s ξ) ((field r K).eval t (curve r K s ξ t)) t := by
    rw [field_eval]
    exact curve_deriv r K s ξ t hK.ne' (denominator_ne_on_domain r K s ξ hr hK
      (by rwa [← solutionInterval_carrier]))
  refine ⟨(classical_iff_solutionOn (field r K) I (curve r K s ξ)).mpr ?_,
    solutionInterval_initial r K s ξ hr hK, curve_initial r K s ξ hK.ne'⟩
  exact ⟨fun t ht => (hd t ht).continuousAt.continuousWithinAt,
    fun _ _ => trivial, fun t ht => (hd t ht).hasDerivWithinAt⟩

lemma pole_not_in_competitor (r K s ξ : ℝ) (hr : 0 < r) (hK : 0 < K)
    (hout : ξ < 0 ∨ K < ξ) (J : OpenTimeInterval) (y : ℝ → ℝ)
    (hy : IsClassicalIVPOn (field r K) J y s ξ) : pole r K s ξ ∉ J.carrier := by
  intro hp
  let p := pole r K s ξ
  have heq := Ch03.LocalExistenceUniqueness.overlap_uniqueness (field r K)
    (field_locallyLipschitz r K) (solutionInterval r K s ξ) J (curve r K s ξ) y s ξ
    (curve_isIVP r K s ξ hr hK) hy
  have hblow := (logistic_poles r K hr hK s ξ hout).2.2.2.2
  have hcont := (hy.1.2.2 p hp).continuousAt
  rcases hout with hξ | hξK
  · apply excludes_blowup_point p (Iio p) J.carrier (fun t ht => ne_of_lt ht)
      (J.isOpen.mem_nhds hp) ?_ hcont hblow
    intro t ht
    apply heq
    exact ⟨by simpa [solutionInterval_carrier, domain, hξ, p] using ht.1, ht.2⟩
  · have hn : ¬ ξ < 0 := by linarith
    apply excludes_blowup_point p (Ioi p) J.carrier (fun t ht => ne_of_gt ht)
      (J.isOpen.mem_nhds hp) ?_ hcont hblow
    intro t ht
    apply heq
    exact ⟨by simpa [solutionInterval_carrier, domain, hn, hξK, p] using ht.1, ht.2⟩

/-- The displayed interval is the largest interval of any solution through the
specified datum. A pole cannot be crossed by any real classical solution. -/
theorem logistic_solution : Specs.D13Unified.Ch02.LogisticGrowth.logisticSolutionExpected := by
  intro r K hr hK s ξ
  rw [← solutionInterval_carrier r K s ξ]
  apply maximalFormula_of_restrictions (field r K) (solutionInterval r K s ξ)
    (curve r K s ξ) s ξ (curve_isIVP r K s ξ hr hK)
  intro J y hy
  have hsub : J.carrier ⊆ (solutionInterval r K s ξ).carrier := by
    intro t ht
    rw [solutionInterval_carrier]
    by_cases hξ : ξ < 0
    · have hn := pole_not_in_competitor r K s ξ hr hK (Or.inl hξ) J y hy
      have hts : t < pole r K s ξ := by
        by_contra h
        exact hn (J.ordConnected.out hy.2.1 ht
          ⟨(pole_after r K s ξ hr hK hξ).le, le_of_not_gt h⟩)
      simpa [domain, hξ] using hts
    by_cases hξK : K < ξ
    · have hn := pole_not_in_competitor r K s ξ hr hK (Or.inr hξK) J y hy
      have hts : pole r K s ξ < t := by
        by_contra h
        exact hn (J.ordConnected.out ht hy.2.1
          ⟨le_of_not_gt h, (pole_before r K s ξ hr hK hξK).le⟩)
      simpa [domain, hξ, hξK] using hts
    simp [domain, hξ, hξK]
  have heq := Ch03.LocalExistenceUniqueness.overlap_uniqueness (field r K)
    (field_locallyLipschitz r K) (solutionInterval r K s ξ) J (curve r K s ξ) y s ξ
    (curve_isIVP r K s ξ hr hK) hy
  exact ⟨hsub, fun t ht => heq ⟨hsub ht, ht⟩⟩

lemma exponentialField_locallyLipschitz (r : ℝ) :
    (exponentialField r).LocallyLipschitzInState := by
  intro s ξ _
  refine ⟨1, 1, |r|, by norm_num, by norm_num, abs_nonneg _,
    fun _ _ => trivial, ?_⟩
  intro t _ x _ y _
  simp only [exponentialField_eval, ← mul_sub, norm_mul, Real.norm_eq_abs, le_refl]

/-- The unrestricted linear equation has no finite endpoint in either direction,
for any real growth rate or real initial value. -/
theorem exponential_growth : Specs.D13Unified.Ch02.LogisticGrowth.exponentialGrowthExpected := by
  intro r s ξ
  have hd (t : ℝ) : HasDerivAt (exponential r s ξ)
      ((exponentialField r).eval t (exponential r s ξ t)) t := by
    rw [exponentialField_eval]
    convert! (exp_deriv r s t).const_mul ξ using 1
    dsimp [exponential]; ring
  have hx : IsClassicalIVPOn (exponentialField r) OpenTimeInterval.whole
      (exponential r s ξ) s ξ := by
    refine ⟨(classical_iff_solutionOn _ _ _).mpr ?_, mem_univ _, ?_⟩
    · exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun _ _ => trivial,
        fun t _ => (hd t).hasDerivWithinAt⟩
    · simp [exponential]
  apply maximalFormula_of_restrictions (exponentialField r) OpenTimeInterval.whole
    (exponential r s ξ) s ξ hx
  intro J y hy
  have heq := Ch03.LocalExistenceUniqueness.overlap_uniqueness (exponentialField r)
    (exponentialField_locallyLipschitz r) OpenTimeInterval.whole J (exponential r s ξ) y s ξ hx hy
  exact ⟨subset_univ _, fun t ht => heq ⟨mem_univ _, ht⟩⟩

end D13Unified.Ch02.LogisticGrowth
