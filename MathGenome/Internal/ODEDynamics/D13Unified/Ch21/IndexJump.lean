import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.IndexJump
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.IndexProperties
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.LinearCombination

namespace D13Unified.Ch21.IndexJump
noncomputable section
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch21.Collar
open D13Unified.Ch21.IndexProperties

/-- The integer index is continuous on the complement of the trace. -/
theorem index_continuousOn_complement (α : Loop) :
    ContinuousOn (index α) (range α)ᶜ := by
  intro p hp
  have ha : Avoids α p := by
    intro t ht
    exact hp ⟨t, ht⟩
  obtain ⟨ε, hε, hloc⟩ := index_locally_constant α p ha
  have heq : (index α) =ᶠ[𝓝 p] (fun _ => index α p) := by
    filter_upwards [Metric.ball_mem_nhds p hε] with q hq
    exact (hloc q hq).2
  exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt

/-- Constancy uses connectedness only, with no separation conclusion. -/
theorem index_constant_on_preconnected (α : Loop) (S : Set ℂ)
    (hS : IsPreconnected S) (havoid : S ⊆ (range α)ᶜ)
    (p : ℂ) (hp : p ∈ S) (q : ℂ) (hq : q ∈ S) :
    index α p = index α q :=
  hS.constant ((index_continuousOn_complement α).mono havoid) hp hq

/-- Each side of an actual collar has a single index value. -/
theorem collar_side_index_constant (γ : C(Circle, ℂ)) (v : Circle → ℂ)
    (a : ℝ) (hc : IsCollar γ v a) :
    (∀ p ∈ positiveSide γ v a, ∀ q ∈ positiveSide γ v a,
      index (circleLoop γ) p = index (circleLoop γ) q) ∧
    (∀ p ∈ negativeSide γ v a, ∀ q ∈ negativeSide γ v a,
      index (circleLoop γ) p = index (circleLoop γ) q) := by
  obtain ⟨_, _, _, e, _, _, _, _, _, _, hpos, hneg, hposAvoid, hnegAvoid⟩ := hc
  have hpos' : positiveSide γ v a ⊆ (range (circleLoop γ))ᶜ := by
    simpa only [circle_trace] using hposAvoid
  have hneg' : negativeSide γ v a ⊆ (range (circleLoop γ))ᶜ := by
    simpa only [circle_trace] using hnegAvoid
  exact ⟨index_constant_on_preconnected (circleLoop γ) _ hpos.isConnected.isPreconnected hpos',
    index_constant_on_preconnected (circleLoop γ) _ hneg.isConnected.isPreconnected hneg'⟩

/-- Reduction to a single local pair, rather than an assumed jump certificate. -/
theorem index_jump_of_one_pair (γ : C(Circle, ℂ)) (v : Circle → ℂ)
    (a : ℝ) (hc : IsCollar γ v a)
    (xPlus : ℂ) (hxPlus : xPlus ∈ positiveSide γ v a)
    (xMinus : ℂ) (hxMinus : xMinus ∈ negativeSide γ v a)
    (hjump : index (circleLoop γ) xPlus - index (circleLoop γ) xMinus = 1)
    (pPlus : ℂ) (hpPlus : pPlus ∈ positiveSide γ v a)
    (pMinus : ℂ) (hpMinus : pMinus ∈ negativeSide γ v a) :
    index (circleLoop γ) pPlus - index (circleLoop γ) pMinus = 1 := by
  obtain ⟨hpos, hneg⟩ := collar_side_index_constant γ v a hc
  rw [hpos pPlus hpPlus xPlus hxPlus, hneg pMinus hpMinus xMinus hxMinus]
  exact hjump

open Specs.D13Unified.Ch21.IndexJump (upperReferenceLog lowerReferenceLog)

/-- The two rotated logarithms have the same exponential. -/
theorem exp_upperReferenceLog {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (upperReferenceLog z) = z := by
  rw [upperReferenceLog, Complex.exp_sub, Complex.exp_log (mul_ne_zero Complex.I_ne_zero hz),
    Complex.exp_log Complex.I_ne_zero]
  field_simp

theorem exp_lowerReferenceLog {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (lowerReferenceLog z) = z := by
  rw [lowerReferenceLog, Complex.exp_sub,
    Complex.exp_log (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz),
    Complex.exp_log (neg_ne_zero.mpr Complex.I_ne_zero)]
  field_simp

/-- On the right the two charts coincide. -/
theorem referenceLog_sub_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    upperReferenceLog z - lowerReferenceLog z = 0 := by
  have he : -Complex.I * z = -(Complex.I * z) := by ring
  have hi : 0 < (Complex.I * z).im := by simpa using hz
  apply Complex.ext
  · simp [upperReferenceLog, lowerReferenceLog, Complex.log_re]
  · simp only [upperReferenceLog, lowerReferenceLog, Complex.sub_im, Complex.log_im,
      he, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi, Complex.arg_I, Complex.arg_neg_I, Complex.zero_im]
    ring

/-- On the left the upper-reference chart is lower by exactly one period. -/
theorem referenceLog_sub_of_re_neg {z : ℂ} (hz : z.re < 0) :
    upperReferenceLog z - lowerReferenceLog z = -period := by
  have he : -Complex.I * z = -(Complex.I * z) := by ring
  have hi : (Complex.I * z).im < 0 := by simpa using hz
  apply Complex.ext
  · simp [upperReferenceLog, lowerReferenceLog, Complex.log_re,
      period, Specs.D13Unified.Ch21.IndexProperties.period]
  · simp only [upperReferenceLog, lowerReferenceLog, Complex.sub_im, Complex.log_im,
      he, Complex.arg_neg_eq_arg_add_pi_of_im_neg hi, Complex.arg_I, Complex.arg_neg_I]
    simp [period, Specs.D13Unified.Ch21.IndexProperties.period]
    ring

/-- Away from the vertical axis both rotated log charts are continuous. -/
theorem continuousAt_upperReferenceLog {z : ℂ} (hz : z.re ≠ 0) :
    ContinuousAt upperReferenceLog z := by
  apply ((continuousAt_clog ?_).comp
    (continuous_const.mul continuous_id).continuousAt).sub continuousAt_const
  apply Complex.mem_slitPlane_iff.mpr
  right
  simpa using hz

theorem continuousAt_lowerReferenceLog {z : ℂ} (hz : z.re ≠ 0) :
    ContinuousAt lowerReferenceLog z := by
  apply ((continuousAt_clog ?_).comp
    (continuous_const.mul continuous_id).continuousAt).sub continuousAt_const
  apply Complex.mem_slitPlane_iff.mpr
  right
  simpa using hz

/-- The local angular change for the upper reference point minus that for the
lower reference point tends to the positive period. No separation result or
integral limit at the singular point enters this calculation. -/
theorem local_log_increment_limit (zLeft zRight : ℂ)
    (hLeft : zLeft.re < 0) (hRight : 0 < zRight.re) :
    Tendsto (fun ε : ℝ =>
      (upperReferenceLog (zRight - (ε : ℂ) * Complex.I) -
        upperReferenceLog (zLeft - (ε : ℂ) * Complex.I)) -
      (lowerReferenceLog (zRight + (ε : ℂ) * Complex.I) -
        lowerReferenceLog (zLeft + (ε : ℂ) * Complex.I)))
      (𝓝 0) (𝓝 period) := by
  have hc : ContinuousAt (fun ε : ℝ =>
      (upperReferenceLog (zRight - (ε : ℂ) * Complex.I) -
        upperReferenceLog (zLeft - (ε : ℂ) * Complex.I)) -
      (lowerReferenceLog (zRight + (ε : ℂ) * Complex.I) -
        lowerReferenceLog (zLeft + (ε : ℂ) * Complex.I))) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.sub
      · apply ContinuousAt.comp (g := upperReferenceLog) (f := fun ε : ℝ => zRight - (ε : ℂ) * Complex.I)
        · simpa using continuousAt_upperReferenceLog hRight.ne'
        · fun_prop
      · apply ContinuousAt.comp (g := upperReferenceLog) (f := fun ε : ℝ => zLeft - (ε : ℂ) * Complex.I)
        · simpa using continuousAt_upperReferenceLog hLeft.ne
        · fun_prop
    · apply ContinuousAt.sub
      · apply ContinuousAt.comp (g := lowerReferenceLog) (f := fun ε : ℝ => zRight + (ε : ℂ) * Complex.I)
        · simpa using continuousAt_lowerReferenceLog hRight.ne'
        · fun_prop
      · apply ContinuousAt.comp (g := lowerReferenceLog) (f := fun ε : ℝ => zLeft + (ε : ℂ) * Complex.I)
        · simpa using continuousAt_lowerReferenceLog hLeft.ne
        · fun_prop
  convert hc.tendsto using 1
  congr 1
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero]
  have hR := referenceLog_sub_of_re_pos hRight
  have hL := referenceLog_sub_of_re_neg hLeft
  linear_combination -hR + hL

/-- Two continuous logarithmic lifts have identical increments on any
preconnected set. This version does not require a closed path. -/
theorem log_increment_eq {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {A B : X → ℂ}
    (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hexp : ∀ t ∈ S, Complex.exp (A t) = Complex.exp (B t))
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    A y - A x = B y - B x := by
  have he := Complex.isCoveringMap_exp.constOn_of_comp hS (hA.sub hB) (by
    intro t ht u hu
    apply Subtype.ext
    change Complex.exp (A t - B t) = Complex.exp (A u - B u)
    simp only [Complex.exp_sub, hexp t ht, hexp u hu,
      div_self (Complex.exp_ne_zero _)]) hx hy
  change A x - B x = A y - B y at he
  linear_combination -he

/-- The rotated log charts really are continuous through the local arc.
The only point of that arc on the imaginary axis is its zero. -/
theorem local_referenceLogs_continuousOn {X : Type*} [TopologicalSpace X]
    {S : Set X} {g : X → ℂ} {c : X}
    (hg : ContinuousOn g S) (hzero : g c = 0)
    (haxis : ∀ t ∈ S, (g t).re = 0 → t = c)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t => upperReferenceLog (g t - (ε : ℂ) * Complex.I)) S ∧
    ContinuousOn (fun t => lowerReferenceLog (g t + (ε : ℂ) * Complex.I)) S := by
  constructor
  · apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.clog (continuousOn_const.mul (hg.sub continuousOn_const))
    intro t ht
    apply Complex.mem_slitPlane_iff.mpr
    dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    by_cases hz : (g t).re = 0
    · left
      rw [haxis t ht hz, hzero]
      simpa using hε
    · right
      simpa using hz
  · apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.clog (continuousOn_const.mul (hg.add continuousOn_const))
    intro t ht
    apply Complex.mem_slitPlane_iff.mpr
    dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    by_cases hz : (g t).re = 0
    · left
      rw [haxis t ht hz, hzero]
      simpa using hε
    · right
      simpa using hz

open unitInterval

/-- On a compact part of the path missing zero, the displacement ratio
admits a single principal logarithm for all small reference displacements. -/
theorem eventually_ratio_in_slitPlane (α : Loop) (S : Set I)
    (hS : IsCompact S) (havoid : ∀ t ∈ S, α t ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ t ∈ S,
      α t - (ε : ℂ) * Complex.I ≠ 0 ∧
      α t + (ε : ℂ) * Complex.I ≠ 0 ∧
      (α t - (ε : ℂ) * Complex.I) /
        (α t + (ε : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  have hm : Continuous (fun z : ℝ × I => α z.2 - (z.1 : ℂ) * Complex.I) := by fun_prop
  have hp : Continuous (fun z : ℝ × I => α z.2 + (z.1 : ℂ) * Complex.I) := by fun_prop
  apply hS.eventually_forall_of_forall_eventually
  intro t ht
  have hm' := (hm.continuousAt (x := (0, t))).ne_iff_eventually_ne
    (continuousAt_const (y := (0 : ℂ))) |>.mp (by simpa using havoid t ht)
  have hp' := (hp.continuousAt (x := (0, t))).ne_iff_eventually_ne
    (continuousAt_const (y := (0 : ℂ))) |>.mp (by simpa using havoid t ht)
  have hq := (hm.continuousAt (x := (0, t))).div hp.continuousAt
    (by simpa using havoid t ht)
  have hs := hq.eventually (show Complex.slitPlane ∈ 𝓝
      ((α t - ((0 : ℝ) : ℂ) * Complex.I) /
        (α t + ((0 : ℝ) : ℂ) * Complex.I)) from by
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero, div_self (havoid t ht)]
    exact Complex.isOpen_slitPlane.mem_nhds (by simp))
  filter_upwards [hm', hp', hs] with z hz₁ hz₂ hz₃
  exact ⟨hz₁, hz₂, hz₃⟩

/-- Exact gluing identity for the local logarithms and the two remaining
pieces of a closed loop. The latter pieces are measured by one ratio log. -/
theorem index_difference_gluing (α : Loop) (l r : I) (hlr : l ≤ r)
    (ε : ℝ)
    (hplus : Avoids α ((ε : ℂ) * Complex.I))
    (hminus : Avoids α (-((ε : ℂ) * Complex.I)))
    (hlocal :
      ContinuousOn (fun t => upperReferenceLog (α t - (ε : ℂ) * Complex.I)) (Icc l r) ∧
      ContinuousOn (fun t => lowerReferenceLog (α t + (ε : ℂ) * Complex.I)) (Icc l r))
    (hrest : ∀ t : I, t ≤ l ∨ r ≤ t →
      (α t - (ε : ℂ) * Complex.I) /
        (α t + (ε : ℂ) * Complex.I) ∈ Complex.slitPlane) :
    ((index α ((ε : ℂ) * Complex.I) -
        index α (-((ε : ℂ) * Complex.I)) : ℤ) : ℂ) * period =
      ((upperReferenceLog (α r - (ε : ℂ) * Complex.I) -
        upperReferenceLog (α l - (ε : ℂ) * Complex.I)) -
      (lowerReferenceLog (α r + (ε : ℂ) * Complex.I) -
        lowerReferenceLog (α l + (ε : ℂ) * Complex.I))) -
      (Complex.log ((α r - (ε : ℂ) * Complex.I) /
          (α r + (ε : ℂ) * Complex.I)) -
        Complex.log ((α l - (ε : ℂ) * Complex.I) /
          (α l + (ε : ℂ) * Complex.I))) := by
  obtain ⟨Lp, hLp, hpEnd⟩ := (index_characterization α _ hplus (index α _)).mpr rfl
  obtain ⟨Lm, hLm, hmEnd⟩ := (index_characterization α _ hminus (index α _)).mpr rfl
  have hnePlus (t : I) : α t - (ε : ℂ) * Complex.I ≠ 0 :=
    sub_ne_zero.mpr (hplus t)
  have hneMinus (t : I) : α t + (ε : ℂ) * Complex.I ≠ 0 := by
    simpa only [sub_neg_eq_add] using sub_ne_zero.mpr (hminus t)
  let D : I → ℂ := fun t => Lp t - Lm t
  let B : I → ℂ := fun t =>
    upperReferenceLog (α t - (ε : ℂ) * Complex.I) -
      lowerReferenceLog (α t + (ε : ℂ) * Complex.I)
  let R : I → ℂ := fun t =>
    (α t - (ε : ℂ) * Complex.I) / (α t + (ε : ℂ) * Complex.I)
  let Q : I → ℂ := fun t => Complex.log (R t)
  have hDc : Continuous D := Lp.continuous.sub Lm.continuous
  have hRc : Continuous R := (α.map.continuous.sub continuous_const).div
    (α.map.continuous.add continuous_const) hneMinus
  have hDexp (t : I) : Complex.exp (D t) = R t := by
    simp only [D, Complex.exp_sub, hLp t, hLm t, sub_neg_eq_add, R]
  have hBexp (t : I) : Complex.exp (B t) = R t := by
    dsimp only [B]
    rw [Complex.exp_sub, exp_upperReferenceLog (hnePlus t),
      exp_lowerReferenceLog (hneMinus t)]
  have hQexp (t : I) (ht : t ≤ l ∨ r ≤ t) : Complex.exp (Q t) = R t :=
    Complex.exp_log (Complex.slitPlane_ne_zero (hrest t ht))
  have hlocalInc : D r - D l = B r - B l :=
    log_increment_eq (ordConnected_Icc.isPreconnected)
      hDc.continuousOn (hlocal.1.sub hlocal.2)
      (fun t _ => (hDexp t).trans (hBexp t).symm)
      (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr)
  have hleftQc : ContinuousOn Q (Icc 0 l) :=
    hRc.continuousOn.clog (fun t ht => hrest t (Or.inl ht.2))
  have hrightQc : ContinuousOn Q (Icc r 1) :=
    hRc.continuousOn.clog (fun t ht => hrest t (Or.inr ht.1))
  have hleftInc : D l - D 0 = Q l - Q 0 :=
    log_increment_eq (ordConnected_Icc.isPreconnected) hDc.continuousOn hleftQc
      (fun t ht => (hDexp t).trans (hQexp t (Or.inl ht.2)).symm)
      (left_mem_Icc.mpr (unitInterval.nonneg l))
      (right_mem_Icc.mpr (unitInterval.nonneg l))
  have hrightInc : D 1 - D r = Q 1 - Q r :=
    log_increment_eq (ordConnected_Icc.isPreconnected) hDc.continuousOn hrightQc
      (fun t ht => (hDexp t).trans (hQexp t (Or.inr ht.1)).symm)
      (left_mem_Icc.mpr (unitInterval.le_one r))
      (right_mem_Icc.mpr (unitInterval.le_one r))
  have hQclosed : Q 0 = Q 1 := by dsimp [Q, R]; rw [α.closed]
  have hDEnd : D 1 - D 0 =
      ((index α ((ε : ℂ) * Complex.I) -
        index α (-((ε : ℂ) * Complex.I)) : ℤ) : ℂ) * period := by
    dsimp [D]
    rw [Int.cast_sub]
    linear_combination hpEnd - hmEnd
  dsimp only [B] at hlocalInc
  dsimp only [Q, R] at hleftInc hrightInc hQclosed
  linear_combination -hDEnd + hlocalInc + hleftInc + hrightInc - hQclosed

/-- On the local arc, a nonzero normal displacement misses the curve. -/
theorem local_avoids_normal_references {X : Type*} {S : Set X} {g : X → ℂ} {c : X}
    (hzero : g c = 0) (haxis : ∀ t ∈ S, (g t).re = 0 → t = c)
    {ε : ℝ} (hε : 0 < ε) : ∀ t ∈ S,
      g t - (ε : ℂ) * Complex.I ≠ 0 ∧ g t + (ε : ℂ) * Complex.I ≠ 0 := by
  intro t ht
  have hne : (ε : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hε.ne') Complex.I_ne_zero
  constructor
  · intro he
    have hr : (g t).re = 0 := by
      have hh := congrArg Complex.re (sub_eq_zero.mp he)
      simpa using hh
    rw [haxis t ht hr, hzero, zero_sub] at he
    exact (neg_ne_zero.mpr hne) he
  · intro he
    have hr : (g t).re = 0 := by
      have hh := congrArg Complex.re he
      simpa using hh
    rw [haxis t ht hr, hzero, zero_add] at he
    exact hne he

/-- The rest of the loop contributes a difference tending to zero. -/
theorem log_ratio_tendsto_zero {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun ε : ℝ => Complex.log
      ((z - (ε : ℂ) * Complex.I) / (z + (ε : ℂ) * Complex.I))) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun ε : ℝ =>
      (z - (ε : ℂ) * Complex.I) / (z + (ε : ℂ) * Complex.I)) 0 :=
    (by fun_prop : ContinuousAt (fun ε : ℝ => z - (ε : ℂ) * Complex.I) 0).div
      (by fun_prop) (by simpa using hz)
  have hlog := hc.clog (by simp [hz])
  simpa [hz] using hlog.tendsto

/-- Analytic local jump without a separation theorem: a continuous loop with
an isolated zero, crossing the vertical axis once from left to right near that
zero, has the positive unit jump in its winding index. The period formulation
keeps the index defined by the upstream logarithmic lift. -/
theorem local_index_difference_limit (α : Loop) (l c r : I)
    (hlc : l < c) (hcr : c < r) (hzero : α c = 0)
    (hunique : ∀ t : I, α t = 0 → t = c)
    (haxis : ∀ t ∈ Icc l r, (α t).re = 0 → t = c)
    (hLeft : (α l).re < 0) (hRight : 0 < (α r).re) :
    Tendsto (fun ε : ℝ =>
      ((index α ((ε : ℂ) * Complex.I) -
        index α (-((ε : ℂ) * Complex.I)) : ℤ) : ℂ) * period)
      (𝓝[>] 0) (𝓝 period) := by
  let S : Set I := Icc 0 l ∪ Icc r 1
  have hS : IsCompact S := isCompact_Icc.union isCompact_Icc
  have hSavoid : ∀ t ∈ S, α t ≠ 0 := by
    intro t ht he
    have htc := hunique t he
    subst t
    rcases ht with ht | ht
    · exact (not_le.mpr hlc) ht.2
    · exact (not_le.mpr hcr) ht.1
  have hrest := (eventually_ratio_in_slitPlane α S hS hSavoid).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  let R : ℝ → ℂ := fun ε =>
    ((upperReferenceLog (α r - (ε : ℂ) * Complex.I) -
      upperReferenceLog (α l - (ε : ℂ) * Complex.I)) -
    (lowerReferenceLog (α r + (ε : ℂ) * Complex.I) -
      lowerReferenceLog (α l + (ε : ℂ) * Complex.I))) -
    (Complex.log ((α r - (ε : ℂ) * Complex.I) / (α r + (ε : ℂ) * Complex.I)) -
      Complex.log ((α l - (ε : ℂ) * Complex.I) / (α l + (ε : ℂ) * Complex.I)))
  have heq : (fun ε : ℝ =>
      ((index α ((ε : ℂ) * Complex.I) -
        index α (-((ε : ℂ) * Complex.I)) : ℤ) : ℂ) * period) =ᶠ[𝓝[>] 0] R := by
    filter_upwards [hrest, self_mem_nhdsWithin] with ε hεrest hε
    have hεpos : 0 < ε := hε
    have havoids : ∀ t : I,
        α t - (ε : ℂ) * Complex.I ≠ 0 ∧ α t + (ε : ℂ) * Complex.I ≠ 0 := by
      intro t
      by_cases ht : t ∈ Icc l r
      · exact local_avoids_normal_references hzero haxis hεpos t ht
      · have htS : t ∈ S := by
          by_cases htl : t ≤ l
          · exact Or.inl ⟨unitInterval.nonneg t, htl⟩
          · right
            exact ⟨le_of_not_ge (fun htr => ht ⟨(not_le.mp htl).le, htr⟩), unitInterval.le_one t⟩
        exact ⟨(hεrest t htS).1, (hεrest t htS).2.1⟩
    have hp : Avoids α ((ε : ℂ) * Complex.I) := fun t => sub_ne_zero.mp (havoids t).1
    have hm : Avoids α (-((ε : ℂ) * Complex.I)) := by
      intro t
      apply sub_ne_zero.mp
      simpa only [sub_neg_eq_add] using (havoids t).2
    apply index_difference_gluing α l r (le_of_lt (lt_trans hlc hcr)) ε hp hm
      (local_referenceLogs_continuousOn α.map.continuous.continuousOn hzero haxis hεpos)
    intro t ht
    exact (hεrest t (by
      rcases ht with ht | ht
      · exact Or.inl ⟨unitInterval.nonneg t, ht⟩
      · exact Or.inr ⟨ht, unitInterval.le_one t⟩)).2.2
  have hlne : α l ≠ 0 := by intro he; simp [he] at hLeft
  have hrne : α r ≠ 0 := by intro he; simp [he] at hRight
  have hlim := (local_log_increment_limit (α l) (α r) hLeft hRight).sub
    ((log_ratio_tendsto_zero hrne).sub (log_ratio_tendsto_zero hlne))
  have hR : Tendsto R (𝓝[>] 0) (𝓝 period) := by
    simpa only [sub_self, sub_zero] using hlim.mono_left nhdsWithin_le_nhds
  exact (tendsto_congr' heq).mpr hR

/-- Complex multiplication and translation preserve the winding convention.
This compares the actual displacement paths, with no geometric assumptions. -/
theorem index_eq_of_scaled_displacement (α β : Loop) (p q C : ℂ)
    (hC : C ≠ 0) (hβ : Avoids β q)
    (he : ∀ t, α t - p = C * (β t - q)) : index α p = index β q := by
  have hα : Avoids α p := by
    intro t ht
    have hz : α t - p = 0 := sub_eq_zero.mpr ht
    rw [he] at hz
    exact sub_ne_zero.mpr (hβ t) ((mul_eq_zero.mp hz).resolve_left hC)
  obtain ⟨L, hL, hend⟩ := (index_characterization β q hβ (index β q)).mpr rfl
  symm
  apply (index_characterization α p hα (index β q)).mp
  refine ⟨⟨fun t => Complex.log C + L t, continuous_const.add L.continuous⟩, ?_, ?_⟩
  · intro t
    change Complex.exp (Complex.log C + L t) = α t - p
    rw [Complex.exp_add, Complex.exp_log hC, hL t, he t]
  · change (Complex.log C + L 1) - (Complex.log C + L 0) = _
    rw [← hend]
    ring

/-- A positive real derivative of a C¹ function supplies a genuine crossing
interval, including the closed endpoints and uniqueness of the axis meeting. -/
theorem crossing_interval {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ)
    (hc : 0 < c ∧ c < 1) (hzero : f c = 0) (hpos : 0 < deriv f c) :
    ∃ l r : ℝ, 0 ≤ l ∧ l < c ∧ c < r ∧ r ≤ 1 ∧
      f l < 0 ∧ 0 < f r ∧ ∀ t ∈ Icc l r, f t = 0 → t = c := by
  have hp := hf.continuous_deriv_one.continuousAt.eventually (Ioi_mem_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hp
  let d : ℝ := min (δ / 2) (min (c / 2) ((1 - c) / 2))
  have hd : 0 < d := lt_min (half_pos hδ) (lt_min (half_pos hc.1) (half_pos (sub_pos.mpr hc.2)))
  have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
  have hdl : d ≤ c / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdr : d ≤ (1 - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hder : ∀ t ∈ Icc (c - d) (c + d), 0 < deriv f t := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hm : StrictMonoOn f (Icc (c - d) (c + d)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuous.continuousOn
      (fun t ht => hder t (interior_subset ht))
  have hcl : c - d < c := by linarith
  have hcr : c < c + d := by linarith
  have hcc : c ∈ Icc (c - d) (c + d) := ⟨hcl.le, hcr.le⟩
  refine ⟨c - d, c + d, by linarith, hcl, hcr, by linarith, ?_, ?_, ?_⟩
  · simpa only [hzero] using hm (left_mem_Icc.mpr (by linarith)) hcc hcl
  · simpa only [hzero] using hm hcc (right_mem_Icc.mpr (by linarith)) hcr
  · intro t ht he
    exact hm.injOn ht hcc (he.trans hzero.symm)

/-- The normalization sending the chosen positive collar direction to i has
positive horizontal tangent precisely because the collar determinant is positive. -/
theorem normalized_tangent_re_pos {d w : ℂ}
    (hdet : 0 < Specs.D13Unified.Ch21.Collar.det d w) :
    w ≠ 0 ∧ 0 < ((Complex.I / w) * d).re := by
  have hw : w ≠ 0 := by
    intro he
    simp [he, Specs.D13Unified.Ch21.Collar.det] at hdet
  refine ⟨hw, ?_⟩
  rw [div_mul_eq_mul_div, Complex.div_re, ← add_div]
  apply div_pos
  · simpa [Specs.D13Unified.Ch21.Collar.det, Complex.mul_re,
      Complex.mul_im, mul_comm, mul_left_comm] using hdet
  · exact Complex.normSq_pos.mpr hw

/-- Full local index jump for the positively oriented collar of a regular C¹
embedded loop. Normalizing one fiber avoids any appeal to planar separation. -/
theorem index_jump (γ : C(Circle, ℂ)) (hγ : RegularEmbeddedLoop γ)
    (v : Circle → ℂ) (a : ℝ) (hc : IsCollar γ v a)
    (pPlus : ℂ) (hpPlus : pPlus ∈ positiveSide γ v a)
    (pMinus : ℂ) (hpMinus : pMinus ∈ negativeSide γ v a) :
    index (circleLoop γ) pPlus - index (circleLoop γ) pMinus = 1 := by
  let c : I := ⟨1 / 2, by constructor <;> norm_num⟩
  let center : ℂ := γ (q (1 / 2))
  let w : ℂ := v (q (1 / 2))
  let C : ℂ := Complex.I / w
  have hdet : 0 < det (deriv (realLift γ) (1 / 2)) w := hc.2.2.1 (1 / 2)
  obtain ⟨hw, hpositive⟩ := normalized_tangent_re_pos hdet
  have hC : C ≠ 0 := div_ne_zero Complex.I_ne_zero hw
  have hCw : C * w = Complex.I := div_mul_cancel₀ _ hw
  let g : ℝ → ℂ := fun t => C * (realLift γ t - center)
  let α : Loop :=
    ⟨⟨fun t => C * (circleLoop γ t - center),
      continuous_const.mul ((circleLoop γ).map.continuous.sub continuous_const)⟩,
      by change C * (circleLoop γ 0 - center) = C * (circleLoop γ 1 - center)
         rw [(circleLoop γ).closed]⟩
  have hα (t : I) : α t = g t := rfl
  have hzero : α c = 0 := by simp [α, c, circleLoop,
    Specs.D13Unified.Ch21.IndexProperties.circleLoop, center]
  have hunique : ∀ t : I, α t = 0 → t = c := by
    intro t ht
    have htcenter : γ (q t) = γ (q (1 / 2)) := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp ht).resolve_left hC
    have htq := hγ.2.1 htcenter
    obtain ⟨k, hk⟩ := (Ch15.CircleLift.quotientMap_eq_iff (t : ℝ) (1 / 2)).mp htq
    have hkLower : (-1 : ℤ) < k := by
      exact_mod_cast (show (-1 : ℝ) < (k : ℝ) by linarith [t.property.1])
    have hkUpper : k < (1 : ℤ) := by
      exact_mod_cast (show (k : ℝ) < (1 : ℝ) by linarith [t.property.2])
    have hkZero : k = 0 := by omega
    apply Subtype.ext
    change (t : ℝ) = 1 / 2
    simp only [hkZero, Int.cast_zero, add_zero] at hk
    exact hk
  have hgc : ContDiff ℝ 1 g := contDiff_const.mul (hγ.1.sub contDiff_const)
  have hgd : HasDerivAt g (C * deriv (realLift γ) (1 / 2)) (1 / 2) :=
    (((hγ.1.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub_const center).const_mul C
  have hfd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (1 / 2) hgd
  have hfpos : 0 < deriv (fun t => (g t).re) (1 / 2) := by
    change 0 < deriv (Complex.reCLM ∘ g) (1 / 2)
    rw [hfd.deriv]
    exact hpositive
  have hfzero : (g (1 / 2)).re = 0 := by simp [g, realLift, center]
  obtain ⟨l, r, hl0, hlc, hcr, hr1, hLeft, hRight, haxis⟩ :=
    crossing_interval (Complex.reCLM.contDiff.comp hgc) (1 / 2)
      (by constructor <;> norm_num) hfzero hfpos
  let lI : I := ⟨l, hl0, by linarith⟩
  let rI : I := ⟨r, by linarith, hr1⟩
  have hlocal := local_index_difference_limit α lI c rI hlc hcr hzero hunique
    (fun t ht he => Subtype.ext (haxis t ⟨ht.1, ht.2⟩ he)) hLeft hRight
  obtain ⟨hposConst, hnegConst⟩ := collar_side_index_constant γ v a hc
  have havoidSides : positiveSide γ v a ⊆ (range γ)ᶜ ∧
      negativeSide γ v a ⊆ (range γ)ᶜ := by
    obtain ⟨_, _, _, e, _, _, _, _, _, _, _, _, hp, hm⟩ := hc
    exact ⟨hp, hm⟩
  let K : ℤ := index (circleLoop γ) pPlus - index (circleLoop γ) pMinus
  have heq : (fun ε : ℝ =>
      ((index α ((ε : ℂ) * Complex.I) -
        index α (-((ε : ℂ) * Complex.I)) : ℤ) : ℂ) * period) =ᶠ[𝓝[>] 0]
      (fun _ => (K : ℂ) * period) := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ ε : ℝ in 𝓝 0, ε < a from Iio_mem_nhds hc.1).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))] with ε hε hεa
    have hεpos : 0 < ε := hε
    change ε < a at hεa
    have hxPlus : center + ε • w ∈ positiveSide γ v a :=
      ⟨(q (1 / 2), ε), ⟨mem_univ _, hεpos, hεa⟩, rfl⟩
    have hxMinus : center + (-ε) • w ∈ negativeSide γ v a :=
      ⟨(q (1 / 2), -ε), ⟨mem_univ _, neg_lt_neg hεa, neg_neg_of_pos hεpos⟩, rfl⟩
    have hap : Avoids (circleLoop γ) (center + ε • w) :=
      (circle_avoids γ _).mpr (by
        intro x hx
        have hcomp := havoidSides.1 hxPlus
        exact hcomp ⟨x, hx⟩)
    have ham : Avoids (circleLoop γ) (center + (-ε) • w) :=
      (circle_avoids γ _).mpr (by
        intro x hx
        have hcomp := havoidSides.2 hxMinus
        exact hcomp ⟨x, hx⟩)
    have hpIndex : index α ((ε : ℂ) * Complex.I) = index (circleLoop γ) (center + ε • w) := by
      apply index_eq_of_scaled_displacement α (circleLoop γ) _ _ C hC hap
      intro t
      change C * (circleLoop γ t - center) - (ε : ℂ) * Complex.I =
        C * (circleLoop γ t - (center + ε • w))
      rw [Complex.real_smul, ← hCw]
      ring
    have hmIndex : index α (-((ε : ℂ) * Complex.I)) = index (circleLoop γ) (center + (-ε) • w) := by
      apply index_eq_of_scaled_displacement α (circleLoop γ) _ _ C hC ham
      intro t
      change C * (circleLoop γ t - center) - -((ε : ℂ) * Complex.I) =
        C * (circleLoop γ t - (center + (-ε) • w))
      rw [Complex.real_smul, Complex.ofReal_neg, ← hCw]
      ring
    rw [hpIndex, hmIndex, hposConst _ hxPlus _ hpPlus, hnegConst _ hxMinus _ hpMinus]
  have hconstant : Tendsto (fun _ : ℝ => (K : ℂ) * period) (𝓝[>] 0) (𝓝 period) :=
    hlocal.congr' heq
  have hperiod : (K : ℂ) * period = period :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  have hK : (K : ℂ) = 1 := mul_right_cancel₀ period_ne_zero (by simpa using hperiod)
  exact_mod_cast hK

end
end D13Unified.Ch21.IndexJump
