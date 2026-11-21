import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.HarmonicOscillator
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.HigherOrderReduction
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace D13Unified.HarmonicOscillator

lemma IsOscillatorOn.hasDerivAt {ω : ℝ} {I : OpenTimeInterval} {y : ℝ → ℝ}
    (h : IsOscillatorOn ω I y) {t : ℝ} (ht : t ∈ I.carrier) :
    HasDerivAt y (deriv y t) t :=
  ((h.1.differentiableOn (by norm_num) t ht).differentiableAt
    (I.isOpen.mem_nhds ht)).hasDerivAt

lemma constant_on_interval (I : OpenTimeInterval) {f : ℝ → ℝ}
    (hf : ∀ t ∈ I.carrier, HasDerivAt f 0 t) {s t : ℝ}
    (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) : f t = f s := by
  exact I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun x hx => (hf x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hf x hx).deriv) ht hs

lemma energy_hasDerivAt {ω : ℝ} {I : OpenTimeInterval} {y : ℝ → ℝ}
    (h : IsOscillatorOn ω I y) {t : ℝ} (ht : t ∈ I.carrier) :
    HasDerivAt (energy ω y) 0 t := by
  have hd := (((h.2 t ht).pow 2).add
    (((h.hasDerivAt ht).pow 2).const_mul (ω ^ 2))).div_const 2
  convert hd using 1 <;> first | rfl | ring

theorem energy_constant : Specs.D13Unified.Ch02.HarmonicOscillator.energyExpected := by
  intro ω I y hy s hs t ht
  exact constant_on_interval I (fun _ hu => energy_hasDerivAt hy hu) hs ht

/-- Any pair satisfying the position-velocity equations has constant quadratic energy. -/
lemma pair_energy_constant (ω : ℝ) (I : OpenTimeInterval) (q p : ℝ → ℝ)
    (hq : ∀ t ∈ I.carrier, HasDerivAt q (p t) t)
    (hp : ∀ t ∈ I.carrier, HasDerivAt p (-(ω ^ 2 * q t)) t)
    {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    (p t) ^ 2 + ω ^ 2 * (q t) ^ 2 = (p s) ^ 2 + ω ^ 2 * (q s) ^ 2 := by
  apply constant_on_interval I (s := s) (t := t) _ hs ht
  intro u hu
  have hd := ((hp u hu).pow 2).add (((hq u hu).pow 2).const_mul (ω ^ 2))
  convert hd using 1
  ring

/-- The nonnegative energy of a difference with zero initial data forces equality. -/
lemma unique_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) (I : OpenTimeInterval)
    {y z : ℝ → ℝ} (hy : IsOscillatorOn ω I y) (hz : IsOscillatorOn ω I z)
    {s : ℝ} (hs : s ∈ I.carrier) (hpos : y s = z s) (hvel : deriv y s = deriv z s) :
    EqOn y z I.carrier := by
  intro t ht
  have he := pair_energy_constant ω I (fun u => y u - z u)
    (fun u => deriv y u - deriv z u)
    (fun u hu => (hy.hasDerivAt hu).sub (hz.hasDerivAt hu))
    (fun u hu => by
      convert (hy.2 u hu).sub (hz.2 u hu) using 1
      ring) hs ht
  rw [hpos, hvel, sub_self, sub_self] at he
  have hw : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
  have he0 : ω ^ 2 * (y t - z t) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (deriv y t - deriv z t)]
  have hsq : (y t - z t) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right he0 hw
  have : y t - z t = 0 := by nlinarith [sq_nonneg (y t - z t)]
  exact sub_eq_zero.mp this

lemma formula_hasDerivAt (ω s a b t : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (formula ω s a b)
      (-a * ω * Real.sin (ω * (t - s)) + b * Real.cos (ω * (t - s))) t := by
  have hθ := ((hasDerivAt_id t).sub_const s).const_mul ω
  have hd := ((hθ.cos).const_mul a).add ((hθ.sin).const_mul (b / ω))
  convert hd using 1
  · rfl
  · simp only [id_eq]
    field_simp [hω]

lemma formula_deriv (ω s a b : ℝ) (hω : ω ≠ 0) :
    deriv (formula ω s a b) = fun t =>
      -a * ω * Real.sin (ω * (t - s)) + b * Real.cos (ω * (t - s)) := by
  funext t
  exact (formula_hasDerivAt ω s a b t hω).deriv

lemma formula_second (ω s a b t : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (deriv (formula ω s a b)) (-(ω ^ 2 * formula ω s a b t)) t := by
  rw [formula_deriv ω s a b hω]
  have hθ := ((hasDerivAt_id t).sub_const s).const_mul ω
  have hd := ((hθ.sin).const_mul (-a * ω)).add ((hθ.cos).const_mul b)
  convert hd using 1
  · rfl
  · simp only [formula, id_eq]
    field_simp [hω]
    ring

lemma formula_contDiff (ω s a b : ℝ) : ContDiff ℝ 2 (formula ω s a b) := by
  unfold formula
  fun_prop

lemma affine_hasDerivAt (s a b t : ℝ) : HasDerivAt (affine s a b) b t := by
  have hd := (((hasDerivAt_id t).sub_const s).const_mul b).const_add a
  convert hd using 1
  · funext u
    simp only [affine, id_eq]
  · ring

lemma affine_deriv (s a b : ℝ) : deriv (affine s a b) = fun _ => b := by
  funext t
  exact (affine_hasDerivAt s a b t).deriv

lemma affine_contDiff (s a b : ℝ) : ContDiff ℝ 2 (affine s a b) := by
  unfold affine
  fun_prop

lemma companion_eval (ω t : ℝ) (X : Fin 2 → ℝ) :
    (equation ω).toODE.eval t X = ![X 1, -(ω ^ 2 * X 0)] := by
  funext j
  fin_cases j <;> simp [ODE.eval, HigherOrder.Equation.toODE, equation]

theorem companion_iff : Specs.D13Unified.Ch02.HarmonicOscillator.companionExpected := by
  intro ω I y
  constructor
  · intro hy
    refine ⟨?_, ?_, ?_⟩
    · apply contDiffOn_pi.mpr
      intro j
      fin_cases j
      · simpa using hy.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      · simpa using hy.1.deriv_of_isOpen I.isOpen (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    · intro t ht
      trivial
    · intro t ht
      rw [companion_eval]
      apply hasDerivAt_pi.mpr
      intro j
      fin_cases j
      · simpa using hy.hasDerivAt ht
      · simpa using hy.2 t ht
  · intro hY
    have hr := HigherOrder.system_first_contDiff (equation ω) I
      (fun t => ![y t, deriv y t]) hY
    refine ⟨by simpa using hr, ?_⟩
    intro t ht
    have hd := hasDerivAt_pi.mp (hY.2.2 t ht) 1
    rw [companion_eval] at hd
    simpa using hd

/-- The formula is a solution on every specified open interval. -/
lemma formula_isOscillatorOn (ω s a b : ℝ) (hω : ω ≠ 0) (I : OpenTimeInterval) :
    IsOscillatorOn ω I (formula ω s a b) :=
  ⟨(formula_contDiff ω s a b).contDiffOn,
    fun t _ => formula_second ω s a b t hω⟩

@[simp] lemma formula_initial (ω s a b : ℝ) : formula ω s a b s = a := by
  simp [formula]

lemma formula_initial_deriv (ω s a b : ℝ) (hω : ω ≠ 0) :
    deriv (formula ω s a b) s = b := by
  rw [formula_deriv ω s a b hω]
  simp

theorem positive : Specs.D13Unified.Ch02.HarmonicOscillator.positiveExpected := by
  intro ω hω s a b
  refine ⟨⟨formula_contDiff ω s a b, fun t => formula_second ω s a b t hω.ne'⟩,
    formula_initial ω s a b, formula_initial_deriv ω s a b hω.ne', ?_, ?_⟩
  · intro I y hs hy ha hb
    exact unique_of_ne_zero hω.ne' I hy (formula_isOscillatorOn ω s a b hω.ne' I)
      hs (ha.trans (formula_initial ω s a b).symm)
      (hb.trans (formula_initial_deriv ω s a b hω.ne').symm)
  · intro t
    have he := energy_constant ω OpenTimeInterval.whole (formula ω s a b)
      (formula_isOscillatorOn ω s a b hω.ne' OpenTimeInterval.whole)
      s (mem_univ s) t (mem_univ t)
    simpa only [energy, formula_initial, formula_initial_deriv ω s a b hω.ne'] using he

/-- Zero acceleration makes velocity constant and position affine on the entire interval. -/
lemma zero_unique (I : OpenTimeInterval) {y : ℝ → ℝ} (hy : IsOscillatorOn 0 I y)
    {s a b : ℝ} (hs : s ∈ I.carrier) (ha : y s = a) (hb : deriv y s = b) :
    EqOn y (affine s a b) I.carrier := by
  have hv : ∀ t ∈ I.carrier, deriv y t = b := by
    intro t ht
    rw [← hb]
    apply constant_on_interval I _ hs ht
    intro u hu
    simpa using hy.2 u hu
  apply I.isOpen.eqOn_of_deriv_eq I.ordConnected.isPreconnected
    (fun t ht => (hy.hasDerivAt ht).differentiableAt.differentiableWithinAt)
    ((affine_contDiff s a b).differentiable (by norm_num)).differentiableOn
    (fun t ht => by rw [hv t ht, affine_deriv]) hs
  simpa [affine] using ha

theorem zero : Specs.D13Unified.Ch02.HarmonicOscillator.zeroExpected := by
  intro s a b
  refine ⟨⟨affine_contDiff s a b, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [affine_deriv]
    exact hasDerivAt_const t b
  · simp [affine]
  · rw [affine_deriv]
  · intro I y hs hy ha hb
    exact zero_unique I hy hs ha hb
  · intro t
    simp [energy, affine_deriv]

/-- Mean-value constancy with within derivatives requires no open endpoints. -/
lemma within_constant_on_interval (I : TimeInterval) {f : ℝ → ℝ}
    (hf : ∀ t ∈ I.carrier, HasDerivWithinAt f 0 I.carrier t)
    {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) : f t = f s := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf
    (C := 0) (by simp) I.ordConnected.convex hs ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hb

/-- Position and velocity are uniquely determined even at included endpoints. -/
lemma within_pair_unique (ω : ℝ) (I : TimeInterval) (q p r v : ℝ → ℝ)
    (hq : ∀ t ∈ I.carrier, HasDerivWithinAt q (p t) I.carrier t)
    (hp : ∀ t ∈ I.carrier, HasDerivWithinAt p (-(ω ^ 2 * q t)) I.carrier t)
    (hr : ∀ t ∈ I.carrier, HasDerivWithinAt r (v t) I.carrier t)
    (hv : ∀ t ∈ I.carrier, HasDerivWithinAt v (-(ω ^ 2 * r t)) I.carrier t)
    {s : ℝ} (hs : s ∈ I.carrier) (hqs : q s = r s) (hps : p s = v s) :
    ∀ t ∈ I.carrier, q t = r t ∧ p t = v t := by
  have hQ (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivWithinAt (fun u => q u - r u) (p t - v t) I.carrier t :=
    (hq t ht).sub (hr t ht)
  have hP (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivWithinAt (fun u => p u - v u) (-(ω ^ 2 * (q t - r t))) I.carrier t := by
    convert (hp t ht).sub (hv t ht) using 1
    ring
  by_cases hω : ω = 0
  · subst ω
    have hpv : ∀ t ∈ I.carrier, p t = v t := by
      intro t ht
      have hc := within_constant_on_interval I (fun u hu => by simpa using hP u hu) hs ht
      simpa only [hps, sub_self, sub_eq_zero] using hc
    intro t ht
    refine ⟨?_, hpv t ht⟩
    have hc := within_constant_on_interval I
      (fun u hu => by simpa only [hpv u hu, sub_self] using hQ u hu) hs ht
    simpa only [hqs, sub_self, sub_eq_zero] using hc
  · intro t ht
    have he := within_constant_on_interval I (f := fun u =>
      (p u - v u) ^ 2 + ω ^ 2 * (q u - r u) ^ 2) (fun u hu => by
        have hd := ((hP u hu).pow 2).add (((hQ u hu).pow 2).const_mul (ω ^ 2))
        convert hd using 1
        ring) hs ht
    rw [hqs, hps, sub_self, sub_self] at he
    have hw : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
    have he0 : ω ^ 2 * (q t - r t) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (p t - v t)]
    have hsq : (q t - r t) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right he0 hw
    constructor
    · apply sub_eq_zero.mp
      nlinarith [sq_nonneg (q t - r t)]
    · apply sub_eq_zero.mp
      nlinarith [sq_nonneg (q t - r t), sq_nonneg (p t - v t)]

lemma interval_coordinates (ω : ℝ) (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ))
    (hY : IsSolutionOn (equation ω).toODE I Y) :
    (∀ t ∈ I.carrier, HasDerivWithinAt (fun u => Y u 0) (Y t 1) I.carrier t) ∧
    (∀ t ∈ I.carrier,
      HasDerivWithinAt (fun u => Y u 1) (-(ω ^ 2 * Y t 0)) I.carrier t) := by
  have hd (t : ℝ) (ht : t ∈ I.carrier) (j : Fin 2) :=
    hasDerivWithinAt_pi.mp (hY.2.2 t ht) j
  constructor
  · intro t ht
    simpa [companion_eval] using hd t ht 0
  · intro t ht
    simpa [companion_eval] using hd t ht 1

theorem interval_uniqueness :
    Specs.D13Unified.Ch02.HarmonicOscillator.intervalUniquenessExpected := by
  constructor
  · intro ω hω s a b I Y hs hY hinit t ht
    have hc := interval_coordinates ω I Y hY
    have he := within_pair_unique ω I (fun u => Y u 0) (fun u => Y u 1)
      (formula ω s a b) (deriv (formula ω s a b)) hc.1 hc.2
      (fun u _ => (formula_hasDerivAt ω s a b u hω.ne').hasDerivWithinAt.congr_deriv
        ((formula_hasDerivAt ω s a b u hω.ne').deriv.symm))
      (fun u _ => (formula_second ω s a b u hω.ne').hasDerivWithinAt) hs
      (by simpa using congrFun hinit 0)
      (by simpa [formula_initial_deriv ω s a b hω.ne']
        using congrFun hinit 1) t ht
    funext j
    fin_cases j <;> simp [he.1, he.2]
  · intro s a b I Y hs hY hinit t ht
    have hc := interval_coordinates 0 I Y hY
    have he := within_pair_unique 0 I (fun u => Y u 0) (fun u => Y u 1)
      (affine s a b) (fun _ => b) hc.1 hc.2
      (fun u _ => (affine_hasDerivAt s a b u).hasDerivWithinAt)
      (fun u _ => by simpa using (hasDerivAt_const u b).hasDerivWithinAt (s := I.carrier)) hs
      (by simpa [affine] using congrFun hinit 0)
      (by simpa using congrFun hinit 1) t ht
    funext j
    fin_cases j <;> simp [he.1, he.2]

end D13Unified.HarmonicOscillator
