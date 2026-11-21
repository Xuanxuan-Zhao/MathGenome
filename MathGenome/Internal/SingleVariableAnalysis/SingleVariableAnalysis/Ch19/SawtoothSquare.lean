import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.SawtoothSquare
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Jordan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

noncomputable section
namespace SingleVariableAnalysis.Fourier.Examples
open Set Filter Riemann BV
open scoped Topology BigOperators
open Specs.SingleVariableAnalysis.Ch19.SawtoothSquare

abbrev sawtooth : ℝ → ℝ := sawtoothValue
abbrev squareWave : ℝ → ℝ := squareWaveValue

theorem sawtooth_periodic : Function.Periodic sawtooth (2 * Real.pi) := by
  intro x
  dsimp [sawtooth, sawtoothValue]
  rw [toIcoMod_periodic (show 0 < 2*Real.pi by positivity) (-Real.pi) x]

theorem sawtooth_interior {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    sawtooth x = x := by
  have hm : toIcoMod (show 0 < 2*Real.pi by positivity) (-Real.pi) x = x :=
    (toIcoMod_eq_self _).mpr ⟨hx.1.le, by linarith [hx.2]⟩
  simp only [sawtooth, sawtoothValue, hm, ne_of_gt hx.1, ↓reduceIte]

theorem sawtooth_left : sawtooth (-Real.pi) = 0 := by
  simp [sawtooth, sawtoothValue]

theorem sawtooth_right : sawtooth Real.pi = 0 := by
  have he : Real.pi = -Real.pi + 2*Real.pi := by ring
  rw [he, sawtooth_periodic, sawtooth_left]

theorem sawtooth_profile : sawtoothProfile := by
  refine ⟨sawtooth_periodic, fun x hx => sawtooth_interior hx, ?_⟩
  intro k
  change sawtooth ((2*(k:ℝ)+1)*Real.pi) = 0
  have he : (2*(k:ℝ)+1)*Real.pi = -Real.pi + (k+1 : ℤ) • (2*Real.pi) := by
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]; ring
  rw [he, sawtooth_periodic.zsmul (k+1), sawtooth_left]

theorem squareWave_periodic : Function.Periodic squareWave (2*Real.pi) :=
  Real.sin_periodic.comp Real.sign

theorem squareWave_positive {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) : squareWave x = 1 :=
  Real.sign_of_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)

theorem squareWave_negative {x : ℝ} (hx : x ∈ Ioo (-Real.pi) 0) : squareWave x = -1 := by
  have h := Real.sin_pos_of_pos_of_lt_pi (show 0 < -x by linarith [hx.2])
    (show -x < Real.pi by linarith [hx.1])
  rw [Real.sin_neg] at h
  exact Real.sign_of_neg (by linarith)

theorem squareWave_at_int_pi (k : ℤ) : squareWave ((k:ℝ)*Real.pi) = 0 := by
  simp [squareWave, squareWaveValue, Real.sin_int_mul_pi]

theorem squareWave_profile : squareWaveProfile :=
  ⟨squareWave_periodic, fun x hx => squareWave_positive hx,
    fun x hx => squareWave_negative hx, squareWave_at_int_pi⟩


/-- Endpoint spikes are monotone on a closed interval. This retains, rather
than discards, the values assigned to the two ends. -/
theorem endpoint_spikes_bv {a b z : ℝ} (hab : a ≤ b) (hz : 0 ≤ z) :
    HasBoundedVariation (fun x => if x = a then z else 0) a b ∧
    HasBoundedVariation (fun x => if x = b then -z else 0) a b := by
  constructor
  · apply (hasBoundedVariation_of_monotone _ hab (Or.inr ?_)).1
    intro x hx y hy hxy
    by_cases hya : y = a
    · have hxa : x = a := le_antisymm (hya ▸ hxy) hx.1
      simp only [hxa, hya, ↓reduceIte, le_refl]
    · simp only [hya, ↓reduceIte]
      split_ifs <;> linarith
  · apply (hasBoundedVariation_of_monotone _ hab (Or.inr ?_)).1
    intro x hx y hy hxy
    by_cases hxb : x = b
    · have hyb : y = b := le_antisymm hy.2 (hxb ▸ hxy)
      simp only [hxb, hyb, ↓reduceIte, le_refl]
    · simp only [hxb, ↓reduceIte]
      split_ifs <;> linarith

theorem sawtooth_bv : sawtoothBV := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hid := (hasBoundedVariation_of_monotone id hab
    (Or.inl (monotone_id.monotoneOn _))).1
  obtain ⟨hl, hr⟩ := endpoint_spikes_bv hab Real.pi_pos.le
  have hv := hasBoundedVariation_add hab (hasBoundedVariation_add hab hid hl) hr
  have he : EqOn sawtooth
      (fun x => (x + if x = -Real.pi then Real.pi else 0) +
        if x = Real.pi then -Real.pi else 0) (Icc (-Real.pi) Real.pi) := by
    intro x hx
    by_cases hl : x = -Real.pi
    · subst x
      simp [sawtooth_left, ne_of_lt (show -Real.pi < Real.pi by linarith [Real.pi_pos])]
    by_cases hr : x = Real.pi
    · subst x
      simp [sawtooth_right, ne_of_gt (show -Real.pi < Real.pi by linarith [Real.pi_pos])]
    · rw [sawtooth_interior ⟨lt_of_le_of_ne hx.1 (Ne.symm hl), lt_of_le_of_ne hx.2 hr⟩]
      simp [hl, hr]
  change totalVariation sawtooth (-Real.pi) Real.pi < ⊤
  exact (interval_congruence he).trans_lt hv

theorem squareWave_zero : squareWave 0 = 0 := by
  simp [squareWave, squareWaveValue]

theorem squareWave_left : squareWave (-Real.pi) = 0 := by
  simpa using squareWave_at_int_pi (-1)

theorem squareWave_right : squareWave Real.pi = 0 := by
  simpa using squareWave_at_int_pi 1

theorem squareWave_bv : squareWaveBV := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hs : Monotone (Real.sign) := by
    intro x y hxy
    unfold Real.sign
    split_ifs <;> linarith
  have hv0 := (hasBoundedVariation_of_monotone Real.sign hab
    (Or.inl (hs.monotoneOn _))).1
  obtain ⟨hl, hr⟩ := endpoint_spikes_bv hab (show (0:ℝ) ≤ 1 by norm_num)
  have hv := hasBoundedVariation_add hab (hasBoundedVariation_add hab hv0 hl) hr
  have he : EqOn squareWave
      (fun x => (Real.sign x + if x = -Real.pi then 1 else 0) +
        if x = Real.pi then -1 else 0) (Icc (-Real.pi) Real.pi) := by
    intro x hx
    by_cases hl : x = -Real.pi
    · subst x
      simp [squareWave_left, Real.sign_of_neg (neg_neg_of_pos Real.pi_pos),
        ne_of_lt (show -Real.pi < Real.pi by linarith [Real.pi_pos])]
    by_cases hr : x = Real.pi
    · subst x
      simp [squareWave_right, Real.sign_of_pos Real.pi_pos,
        ne_of_gt (show -Real.pi < Real.pi by linarith [Real.pi_pos])]
    · simp only [hl, hr, ↓reduceIte, add_zero]
      rcases lt_trichotomy x 0 with h | rfl | h
      · rw [squareWave_negative ⟨lt_of_le_of_ne hx.1 (Ne.symm hl), h⟩,
          Real.sign_of_neg h]
      · simp [squareWave_zero]
      · rw [squareWave_positive ⟨h, lt_of_le_of_ne hx.2 hr⟩, Real.sign_of_pos h]
  change totalVariation squareWave (-Real.pi) Real.pi < ⊤
  exact (interval_congruence he).trans_lt hv


theorem sin_frequency_deriv (n x : ℝ) :
    HasDerivAt (fun t => Real.sin (n*t)) (n*Real.cos (n*x)) x := by
  convert (Real.hasDerivAt_sin (n*x)).comp x ((hasDerivAt_id x).const_mul n) using 1 <;>
    simp [Function.comp_def, mul_comm]

theorem cos_frequency_deriv (n x : ℝ) :
    HasDerivAt (fun t => Real.cos (n*t)) (-n*Real.sin (n*x)) x := by
  convert (Real.hasDerivAt_cos (n*x)).comp x ((hasDerivAt_id x).const_mul n) using 1 <;>
    simp [Function.comp_def] <;> ring

theorem primitive_x_cos {n : ℝ} (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => t*Real.sin (n*t)/n + Real.cos (n*t)/n^2)
      (x*Real.cos (n*x)) x := by
  convert (((hasDerivAt_id x).mul (sin_frequency_deriv n x)).div_const n).add
    ((cos_frequency_deriv n x).div_const (n^2)) using 1
  · ext t; simp [div_eq_mul_inv] <;> ring
  · dsimp; field_simp [hn]; ring

theorem primitive_x_sin {n : ℝ} (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun t => -(t*Real.cos (n*t)/n) + Real.sin (n*t)/n^2)
      (x*Real.sin (n*x)) x := by
  convert (((hasDerivAt_id x).mul (cos_frequency_deriv n x)).div_const n).neg.add
    ((sin_frequency_deriv n x).div_const (n^2)) using 1
  · ext t; simp [div_eq_mul_inv] <;> ring
  · dsimp; field_simp [hn]; ring

theorem sawtooth_integral_zero (hf : RealIntegrable sawtooth (-Real.pi) Real.pi) :
    realIntegral _ hf = 0 := by
  have he := real_ftc_second (fun x : ℝ => x^2/2) sawtooth (-Real.pi) Real.pi
    (by linarith [Real.pi_pos]) (by fun_prop) (fun x hx => ?_) hf
  · simpa using he
  · rw [sawtooth_interior hx]
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> simp [div_eq_mul_inv] <;> ring

theorem sawtooth_cos_integral (n : ℕ+)
    (hi : RealIntegrable (fun x => sawtooth x * Real.cos ((n:ℝ)*x)) (-Real.pi) Real.pi) :
    realIntegral _ hi = 0 := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  have he := real_ftc_second
    (fun t => t*Real.sin ((n:ℝ)*t)/(n:ℝ) + Real.cos ((n:ℝ)*t)/(n:ℝ)^2)
    (fun x => sawtooth x * Real.cos ((n:ℝ)*x)) (-Real.pi) Real.pi
    (by linarith [Real.pi_pos]) (by fun_prop)
    (fun x hx => by rw [sawtooth_interior hx]; exact primitive_x_cos hn x) hi
  simpa only [mul_neg, Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, neg_zero, mul_zero, zero_div, zero_add, sub_self] using he

theorem sawtooth_sin_integral (n : ℕ+)
    (hi : RealIntegrable (fun x => sawtooth x * Real.sin ((n:ℝ)*x)) (-Real.pi) Real.pi) :
    realIntegral _ hi = 2*Real.pi*(-1:ℝ)^((n:ℕ)+1)/(n:ℝ) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  have he := real_ftc_second
    (fun t => -(t*Real.cos ((n:ℝ)*t)/(n:ℝ)) + Real.sin ((n:ℝ)*t)/(n:ℝ)^2)
    (fun x => sawtooth x * Real.sin ((n:ℝ)*x)) (-Real.pi) Real.pi
    (by linarith [Real.pi_pos]) (by fun_prop)
    (fun x hx => by rw [sawtooth_interior hx]; exact primitive_x_sin hn x) hi
  change realIntegral _ hi = _ at he
  rw [he]
  simp only [mul_neg, Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, neg_zero, zero_div, add_zero, pow_succ]
  ring

theorem sawtooth_coefficients : sawtoothCoefficients := by
  let hf := (real_bv_riemann sawtooth (by linarith [Real.pi_pos]) sawtooth_bv).2.2
  let ha := fourierCosCoeff_integrable sawtooth hf
  let hb := fourierSinCoeff_integrable sawtooth hf
  refine ⟨hf, ha, hb, ?_, fun n => ⟨?_, ?_⟩⟩
  · change (1/Real.pi)*realIntegral _ hf = 0
    rw [sawtooth_integral_zero, mul_zero]
  · change (1/Real.pi)*realIntegral _ (ha n) = 0
    rw [sawtooth_cos_integral, mul_zero]
  · change (1/Real.pi)*realIntegral _ (hb n) = _
    rw [sawtooth_sin_integral]
    field_simp

/-- Splitting at the jump at zero computes the square-wave integral without
changing its assigned value at that jump or either seam. -/
theorem squareWave_integral_zero (hf : RealIntegrable squareWave (-Real.pi) Real.pi) :
    realIntegral _ hf = 0 := by
  have hπ := Real.pi_pos
  let hl := hf.subinterval le_rfl (by linarith) hπ.le
  let hr := hf.subinterval (by linarith) hπ.le le_rfl
  have hL := real_ftc_second (fun x : ℝ => -x) squareWave (-Real.pi) 0
    (by linarith) (by fun_prop)
    (fun x hx => by rw [squareWave_negative hx]; exact (hasDerivAt_id x).neg) hl
  have hR := real_ftc_second id squareWave 0 Real.pi hπ.le continuousOn_id
    (fun x hx => by rw [squareWave_positive hx]; exact hasDerivAt_id x) hr
  have hsplit := (real_split squareWave (by linarith) hπ.le hf.bounded).2 hf hl hr
  change realIntegral _ hf = realIntegral _ hl + realIntegral _ hr at hsplit
  change realIntegral _ hl = _ at hL
  change realIntegral _ hr = _ at hR
  rw [hsplit, hL, hR]
  simp

theorem squareWave_cos_integral (n : ℕ+)
    (hi : RealIntegrable (fun x => squareWave x * Real.cos ((n:ℝ)*x)) (-Real.pi) Real.pi) :
    realIntegral _ hi = 0 := by
  have hπ := Real.pi_pos
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  let hl := hi.subinterval le_rfl (by linarith) hπ.le
  let hr := hi.subinterval (by linarith) hπ.le le_rfl
  have hL := real_ftc_second (fun x => -Real.sin ((n:ℝ)*x)/(n:ℝ)) _ (-Real.pi) 0
    (by linarith) (by fun_prop)
    (fun x hx => by
      rw [squareWave_negative hx, neg_one_mul]
      convert (sin_frequency_deriv (n:ℝ) x).neg.div_const (n:ℝ) using 1 <;>
        field_simp [hn] <;> ring) hl
  have hR := real_ftc_second (fun x => Real.sin ((n:ℝ)*x)/(n:ℝ)) _ 0 Real.pi hπ.le
    (by fun_prop) (fun x hx => by
      rw [squareWave_positive hx, one_mul]
      convert (sin_frequency_deriv (n:ℝ) x).div_const (n:ℝ) using 1 <;>
        field_simp [hn] <;> ring) hr
  have hsplit := (real_split _ (by linarith) hπ.le hi.bounded).2 hi hl hr
  change realIntegral _ hi = realIntegral _ hl + realIntegral _ hr at hsplit
  change realIntegral _ hl = _ at hL
  change realIntegral _ hr = _ at hR
  rw [hsplit, hL, hR]
  simp [Real.sin_nat_mul_pi]

theorem squareWave_sin_integral (n : ℕ+)
    (hi : RealIntegrable (fun x => squareWave x * Real.sin ((n:ℝ)*x)) (-Real.pi) Real.pi) :
    realIntegral _ hi = 2*(1-(-1:ℝ)^(n:ℕ))/(n:ℝ) := by
  have hπ := Real.pi_pos
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  let hl := hi.subinterval le_rfl (by linarith) hπ.le
  let hr := hi.subinterval (by linarith) hπ.le le_rfl
  have hL := real_ftc_second (fun x => Real.cos ((n:ℝ)*x)/(n:ℝ)) _ (-Real.pi) 0
    (by linarith) (by fun_prop) (fun x hx => by
      rw [squareWave_negative hx, neg_one_mul]
      convert (cos_frequency_deriv (n:ℝ) x).div_const (n:ℝ) using 1 <;>
        field_simp [hn] <;> ring) hl
  have hR := real_ftc_second (fun x => -Real.cos ((n:ℝ)*x)/(n:ℝ)) _ 0 Real.pi hπ.le
    (by fun_prop) (fun x hx => by
      rw [squareWave_positive hx, one_mul]
      convert (cos_frequency_deriv (n:ℝ) x).neg.div_const (n:ℝ) using 1 <;>
        field_simp [hn] <;> ring) hr
  have hsplit := (real_split _ (by linarith) hπ.le hi.bounded).2 hi hl hr
  change realIntegral _ hi = realIntegral _ hl + realIntegral _ hr at hsplit
  change realIntegral _ hl = _ at hL
  change realIntegral _ hr = _ at hR
  rw [hsplit, hL, hR]
  simp only [mul_zero, Real.cos_zero, mul_neg, Real.cos_neg, Real.cos_nat_mul_pi]
  ring

theorem squareWave_coefficients : squareWaveCoefficients := by
  let hf := (real_bv_riemann squareWave (by linarith [Real.pi_pos]) squareWave_bv).2.2
  let ha := fourierCosCoeff_integrable squareWave hf
  let hb := fourierSinCoeff_integrable squareWave hf
  refine ⟨hf, ha, hb, ?_, fun n => ⟨?_, ?_⟩⟩
  · change (1/Real.pi)*realIntegral _ hf = 0
    rw [squareWave_integral_zero, mul_zero]
  · change (1/Real.pi)*realIntegral _ (ha n) = 0
    rw [squareWave_cos_integral, mul_zero]
  · change (1/Real.pi)*realIntegral _ (hb n) = _
    rw [squareWave_sin_integral]
    split_ifs with he
    · rw [he.neg_one_pow]
      ring
    · have ho : Odd (n:ℕ) := Nat.not_even_iff_odd.mp he
      rw [ho.neg_one_pow]
      ring


/-- Exact local symmetry about the assigned midpoint value. -/
def HasLocalMidpoint (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → f (x+t) + f (x-t) = 2*f x

theorem HasLocalMidpoint.translate {f : ℝ → ℝ} {T x r : ℝ}
    (hp : Function.Periodic f T) (k : ℤ) (hx : x = r + k • T)
    (hm : HasLocalMidpoint f r) : HasLocalMidpoint f x := by
  obtain ⟨δ, hδ, hsym⟩ := hm
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  have hp' := hp.zsmul k
  have hplus : x+t = (r+t)+k•T := by rw [hx]; abel
  have hminus : x-t = (r-t)+k•T := by rw [hx]; abel
  rw [hplus, hminus, hp', hp', hx, hp']
  exact hsym t ht htd

theorem sawtooth_local_midpoint (x : ℝ) : HasLocalMidpoint sawtooth x := by
  let hT : 0 < 2*Real.pi := by positivity
  let r := toIcoMod hT (-Real.pi) x
  let k := toIcoDiv hT (-Real.pi) x
  have hr : r ∈ Ico (-Real.pi) Real.pi := by
    have h := toIcoMod_mem_Ico hT (-Real.pi) x
    dsimp [r]
    constructor
    · exact h.1
    · linarith [h.2]
  have hx : x = r + k • (2*Real.pi) := (toIcoMod_add_toIcoDiv_zsmul hT (-Real.pi) x).symm
  apply HasLocalMidpoint.translate sawtooth_periodic k hx
  by_cases he : r = -Real.pi
  · rw [he]
    refine ⟨Real.pi, Real.pi_pos, fun t ht htπ => ?_⟩
    have hplus : -Real.pi+t ∈ Ioo (-Real.pi) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have hminus : -Real.pi-t+2*Real.pi ∈ Ioo (-Real.pi) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    rw [← sawtooth_periodic (-Real.pi-t), sawtooth_interior hplus,
      sawtooth_interior hminus, sawtooth_left]
    ring
  · have hrl : -Real.pi < r := lt_of_le_of_ne hr.1 (Ne.symm he)
    refine ⟨min (r+Real.pi) (Real.pi-r), lt_min (by linarith) (by linarith [hr.2]),
      fun t ht htd => ?_⟩
    have ha : t < r+Real.pi := lt_of_lt_of_le htd (min_le_left _ _)
    have hb : t < Real.pi-r := lt_of_lt_of_le htd (min_le_right _ _)
    rw [sawtooth_interior (show r+t ∈ Ioo (-Real.pi) Real.pi by constructor <;> linarith [hr.2]),
      sawtooth_interior (show r-t ∈ Ioo (-Real.pi) Real.pi by constructor <;> linarith [hr.2]),
      sawtooth_interior ⟨hrl, hr.2⟩]
    ring

theorem squareWave_local_midpoint (x : ℝ) : HasLocalMidpoint squareWave x := by
  by_cases hz : Real.sin x = 0
  · refine ⟨1, by norm_num, fun t _ _ => ?_⟩
    have hs : Real.sin (x+t) = -Real.sin (x-t) := by
      rw [Real.sin_add, Real.sin_sub, hz]
      ring
    change Real.sign (Real.sin (x+t)) + Real.sign (Real.sin (x-t)) =
      2*Real.sign (Real.sin x)
    rw [hs, Real.sign_neg, hz, Real.sign_zero]
    ring
  · have he : ∀ᶠ y in 𝓝 x, squareWave y = squareWave x := by
      rcases lt_or_gt_of_ne hz with hn | hp
      · filter_upwards [Real.continuous_sin.continuousAt.eventually (gt_mem_nhds hn)] with y hy
        exact (Real.sign_of_neg hy).trans (Real.sign_of_neg hn).symm
      · filter_upwards [Real.continuous_sin.continuousAt.eventually (lt_mem_nhds hp)] with y hy
        exact (Real.sign_of_pos hy).trans (Real.sign_of_pos hp).symm
    obtain ⟨δ, hδ, he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨δ, hδ, fun t ht htd => ?_⟩
    have hplus : dist (x+t) x < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htd
    have hminus : dist (x-t) x < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htd
    rw [he hplus, he hminus]
    ring

/-- Dirichlet–Jordan plus exact local symmetry identifies the limit with the
actual assigned value, including jumps. No limit is assumed as a hypothesis. -/
theorem fourier_converges_of_local_midpoint {f : ℝ → ℝ}
    (hp : Function.Periodic f (2*Real.pi))
    (hb : HasBoundedVariation f (-Real.pi) Real.pi) (x : ℝ)
    (hmid : HasLocalMidpoint f x)
    (H : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights
      (fun y => (f y : ℂ))) :
    Tendsto (fun N : ℕ => (fourierPartialSum (fun y => (f y : ℂ)) H N x).re)
      atTop (𝓝 (f x)) := by
  have hb' : HasBoundedVariation f (-Real.pi) (-Real.pi+2*Real.pi) := by
    convert hb using 1 <;> ring
  obtain ⟨_, hJ⟩ := dirichlet_jordan_real f (-Real.pi) hp hb'
  obtain ⟨Lm, Lp, hm, hpl, hS⟩ := hJ x
  have hlim := translated_halves_right_limit hm hpl
  obtain ⟨_, hlim⟩ := (rightRelativeLimit_iff _ _ _ _).mp hlim
  have hsum : Lp+Lm = 2*f x := by
    by_contra hne
    have hε : 0 < dist (2*f x) (Lp+Lm) := dist_pos.mpr (Ne.symm hne)
    obtain ⟨δ, hδ, hclose⟩ := hlim _ hε
    obtain ⟨η, hη, hsym⟩ := hmid
    let t := min (min δ η) Real.pi / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htδ : t < δ := by
      have := min_le_left (min δ η) Real.pi
      have := min_le_left δ η
      dsimp [t]; linarith
    have htη : t < η := by
      have := min_le_left (min δ η) Real.pi
      have := min_le_right δ η
      dsimp [t]; linarith
    have htπ : t < Real.pi := by
      have := min_le_right (min δ η) Real.pi
      dsimp [t]; linarith [Real.pi_pos]
    have hc := hclose t ⟨ht.le, htπ.le⟩ ht (by linarith)
    rw [hsym t ht htη] at hc
    exact lt_irrefl _ hc
  have he : (Lm+Lp)/2 = f x := by linarith
  have hs := hS H
  rw [he] at hs
  convert Complex.continuous_re.continuousAt.tendsto.comp hs using 1 <;> rfl


/-- A real Fourier sum with zero constant and cosine coefficients contains
exactly its positive sine terms. -/
theorem real_partialSum_sine_only (f : ℝ → ℝ)
    (hp : Function.Periodic f (2*Real.pi))
    (hf : RealIntegrable f (-Real.pi) Real.pi)
    (H : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights (fun t => (f t:ℂ)))
    (ha : Specs.SingleVariableAnalysis.Ch19.Representation.CosineWeights f)
    (hb : Specs.SingleVariableAnalysis.Ch19.Representation.SineWeights f)
    (hz : fourierAZero f hf = 0)
    (hc : ∀ n : ℕ+, fourierCosCoeff f n (ha n) = 0)
    (N : ℕ) (x : ℝ) :
    (fourierPartialSum (fun t => (f t:ℂ)) H N x).re =
      ∑ k ∈ Finset.range N, fourierSinCoeff f ⟨k+1, Nat.succ_pos k⟩ (hb _) *
        Real.sin (((k+1:ℕ):ℝ)*x) := by
  have he := congrArg Complex.re (fourierPartialSum_real f ⟨hp, hf⟩ H ha hb N x)
  change (fourierPartialSum (fun t => (f t:ℂ)) H N x).re =
    fourierAZero f hf / 2 + ∑ k ∈ Finset.range N,
      (fourierCosCoeff f ⟨k+1, Nat.succ_pos k⟩ (ha _) * Real.cos (((k+1:ℕ):ℝ)*x) +
      fourierSinCoeff f ⟨k+1, Nat.succ_pos k⟩ (hb _) * Real.sin (((k+1:ℕ):ℝ)*x)) at he
  rw [hz, zero_div, zero_add] at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro k _
  have hk := hc ⟨k+1, Nat.succ_pos k⟩
  have hh := congrArg (fun z : ℝ => z * Real.cos (((k+1:ℕ):ℝ)*x) +
    fourierSinCoeff f ⟨k+1, Nat.succ_pos k⟩ (hb _) * Real.sin (((k+1:ℕ):ℝ)*x)) hk
  simpa only [zero_mul, zero_add] using hh

theorem sawtooth_series : sawtoothSeries := by
  intro x
  obtain ⟨hf, ha, hb, hz, hcoeff⟩ := sawtooth_coefficients
  let H := fourierCoeff_integrable (fun t => (sawtooth t : ℂ))
    (fourierRealEmbedding_integrable sawtooth hf)
  have hs := fourier_converges_of_local_midpoint sawtooth_periodic sawtooth_bv x
    (sawtooth_local_midpoint x) H
  apply hs.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [real_partialSum_sine_only sawtooth sawtooth_periodic hf H ha hb hz
    (fun n => (hcoeff n).1)]
  apply Finset.sum_congr rfl
  intro k _
  have he := (hcoeff ⟨k+1, Nat.succ_pos k⟩).2
  change fourierSinCoeff sawtooth ⟨k+1, Nat.succ_pos k⟩ (hb _) = _ at he
  rw [he]
  rfl

/-- Pair consecutive positive frequencies, retaining the ordered partial sums. -/
theorem sum_range_pairs (u : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (2*N), u k =
      ∑ j ∈ Finset.range N, (u (2*j) + u (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1) = (2*N+1)+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem squareWave_partialSum (hf : RealIntegrable squareWave (-Real.pi) Real.pi)
    (H : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights
      (fun t => (squareWave t:ℂ)))
    (ha : Specs.SingleVariableAnalysis.Ch19.Representation.CosineWeights squareWave)
    (hb : Specs.SingleVariableAnalysis.Ch19.Representation.SineWeights squareWave)
    (hz : fourierAZero squareWave hf = 0)
    (hcoeff : ∀ n : ℕ+, fourierCosCoeff squareWave n (ha n) = 0 ∧
      fourierSinCoeff squareWave n (hb n) =
        if Even (n:ℕ) then 0 else 4/(Real.pi*(n:ℝ))) (N : ℕ) (x : ℝ) :
    (fourierPartialSum (fun t => (squareWave t:ℂ)) H (2*N) x).re =
      (4/Real.pi)*∑ j ∈ Finset.range N,
        Real.sin (((2*j+1:ℕ):ℝ)*x)/((2*j+1:ℕ):ℝ) := by
  rw [real_partialSum_sine_only squareWave squareWave_periodic hf H ha hb hz
    (fun n => (hcoeff n).1), sum_range_pairs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hcoeff ⟨2*j+1, by omega⟩).2, (hcoeff ⟨2*j+1+1, by omega⟩).2]
  have hodd : ¬Even (2*j+1) := Nat.not_even_iff_odd.mpr ⟨j, by omega⟩
  have heven : Even (2*j+1+1) := ⟨j+1, by omega⟩
  change (if Even (2*j+1) then 0 else 4/(Real.pi*((2*j+1:ℕ):ℝ))) *
      Real.sin (((2*j+1:ℕ):ℝ)*x) +
    (if Even (2*j+1+1) then 0 else 4/(Real.pi*((2*j+1+1:ℕ):ℝ))) *
      Real.sin (((2*j+1+1:ℕ):ℝ)*x) = _
  simp only [hodd, heven, ↓reduceIte, zero_mul, add_zero]
  ring

theorem squareWave_series : squareWaveSeries := by
  intro x
  obtain ⟨hf, ha, hb, hz, hcoeff⟩ := squareWave_coefficients
  let H := fourierCoeff_integrable (fun t => (squareWave t:ℂ))
    (fourierRealEmbedding_integrable squareWave hf)
  have hs := fourier_converges_of_local_midpoint squareWave_periodic squareWave_bv x
    (squareWave_local_midpoint x) H
  have hseq : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hv := hs.comp hseq
  apply hv.congr'
  exact Eventually.of_forall (fun N => squareWave_partialSum hf H ha hb hz hcoeff N x)

theorem leibniz_pi : leibnizPi := by
  unfold leibnizPi
  have hsin (j : ℕ) : Real.sin (((2*j+1:ℕ):ℝ)*(Real.pi/2)) = (-1:ℝ)^j := by
    have he : ((2*j+1:ℕ):ℝ)*(Real.pi/2) = Real.pi/2 + (j:ℝ)*Real.pi := by
      push_cast; ring
    rw [he, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]
  have hs := squareWave_series (Real.pi/2)
  have hval : squareWave (Real.pi/2) = 1 :=
    squareWave_positive ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩
  change Tendsto (fun N : ℕ => (4/Real.pi)*∑ j ∈ Finset.range N,
    Real.sin (((2*j+1:ℕ):ℝ)*(Real.pi/2))/((2*j+1:ℕ):ℝ)) atTop
    (𝓝 (squareWave (Real.pi/2))) at hs
  simp only [hsin, hval] at hs
  have ht := hs.const_mul (Real.pi/4)
  have he : (Real.pi/4)*(4/Real.pi) = 1 := by field_simp
  simpa only [← mul_assoc, he, one_mul, mul_one] using ht

end SingleVariableAnalysis.Fourier.Examples
