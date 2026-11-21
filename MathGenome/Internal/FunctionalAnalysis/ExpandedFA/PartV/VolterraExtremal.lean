import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraExtremal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.NonlinearCompactExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.NonlinearCounterexamples
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV.VolterraExtremal
open NonlinearCompactExistence

lemma monotone_compact_converges {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : ℕ → C(X, ℝ)) (hm : Monotone x)
    {K : Set C(X, ℝ)} (hc : IsCompact K) (hx : ∀ n, x n ∈ K) :
    ∃ a ∈ K, Tendsto x atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hc.tendsto_subseq hx
  refine ⟨a, ha, ContinuousMap.tendsto_of_monotone_of_pointwise hm ?_⟩
  intro t
  apply (tendsto_iff_tendsto_subseq_of_monotone
    (fun i j hij => hm hij t) hφ.tendsto_atTop).mpr
  exact (continuous_eval_const t).continuousAt.tendsto.comp hlim

lemma antitone_compact_converges {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (x : ℕ → C(X, ℝ)) (hm : Antitone x)
    {K : Set C(X, ℝ)} (hc : IsCompact K) (hx : ∀ n, x n ∈ K) :
    ∃ a ∈ K, Tendsto x atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hc.tendsto_subseq hx
  refine ⟨a, ha, ContinuousMap.tendsto_of_antitone_of_pointwise hm ?_⟩
  intro t
  apply (tendsto_iff_tendsto_subseq_of_antitone
    (fun i j hij => hm hij t) hφ.tendsto_atTop).mpr
  exact (continuous_eval_const t).continuousAt.tendsto.comp hlim

/-- Compact monotone iteration in a closed interval of continuous functions. -/
lemma extremal_of_compact {T : ℝ} {ℓ v : RealCurve T} (hlv : ℓ ≤ v)
    (V : Icc ℓ v → RealCurve T) (hV : Continuous V)
    (hc : IsCompact (closure (range V)))
    (hm : Monotone V) (hinv : ∀ u, V u ∈ Icc ℓ v)
    (rhs : RealCurve T → Time T → ℝ) (hformula : ∀ u t, V u t = rhs u.val t) :
    ExtremalConclusion ℓ v rhs := by
  let W : Icc ℓ v → Icc ℓ v := fun u => ⟨V u, hinv u⟩
  have hW : Monotone W := fun _ _ h => hm h
  let a : Icc ℓ v := ⟨ℓ, le_rfl, hlv⟩
  let b : Icc ℓ v := ⟨v, hlv, le_rfl⟩
  let x : ℕ → RealCurve T := fun n => (W^[n] a).val
  let y : ℕ → RealCurve T := fun n => (W^[n] b).val
  have hxrec (n) : x (n+1) = V (W^[n] a) := by
    simp only [x, Function.iterate_succ_apply', W]
  have hyrec (n) : y (n+1) = V (W^[n] b) := by
    simp only [y, Function.iterate_succ_apply', W]
  have hxD (n) : x n ∈ Icc ℓ v := (W^[n] a).property
  have hyD (n) : y n ∈ Icc ℓ v := (W^[n] b).property
  have hxm : Monotone x := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hW.iterate n) (show a ≤ W a from (hinv a).1)
  have hym : Antitone y := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hW.iterate n) (show W b ≤ b from (hinv b).2)
  have hxK (n) : x n ∈ insert ℓ (closure (range V)) := by
    cases n with
    | zero => exact mem_insert _ _
    | succ n => rw [hxrec]; exact mem_insert_of_mem _ (subset_closure (mem_range_self _))
  have hyK (n) : y n ∈ insert v (closure (range V)) := by
    cases n with
    | zero => exact mem_insert _ _
    | succ n => rw [hyrec]; exact mem_insert_of_mem _ (subset_closure (mem_range_self _))
  obtain ⟨L, _, hxlim⟩ := monotone_compact_converges x hxm (hc.insert ℓ) hxK
  obtain ⟨U, _, hylim⟩ := antitone_compact_converges y hym (hc.insert v) hyK
  have hLD : L ∈ Icc ℓ v := by
    constructor <;> intro t
    · exact ge_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hxlim)
        (Eventually.of_forall (fun n => (hxD n).1 t))
    · exact le_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hxlim)
        (Eventually.of_forall (fun n => (hxD n).2 t))
  have hUD : U ∈ Icc ℓ v := by
    constructor <;> intro t
    · exact ge_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hylim)
        (Eventually.of_forall (fun n => (hyD n).1 t))
    · exact le_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hylim)
        (Eventually.of_forall (fun n => (hyD n).2 t))
  have hxlift : Tendsto (fun n => W^[n] a) atTop (𝓝 (⟨L, hLD⟩ : Icc ℓ v)) :=
    tendsto_subtype_rng.mpr hxlim
  have hylift : Tendsto (fun n => W^[n] b) atTop (𝓝 (⟨U, hUD⟩ : Icc ℓ v)) :=
    tendsto_subtype_rng.mpr hylim
  have hLF : V ⟨L, hLD⟩ = L := by
    apply tendsto_nhds_unique (hV.continuousAt.tendsto.comp hxlift)
    simpa only [Function.comp_def, hxrec] using hxlim.comp (tendsto_add_atTop_nat 1)
  have hUF : V ⟨U, hUD⟩ = U := by
    apply tendsto_nhds_unique (hV.continuousAt.tendsto.comp hylift)
    simpa only [Function.comp_def, hyrec] using hylim.comp (tendsto_add_atTop_nat 1)
  refine ⟨x, y, L, U, rfl, rfl, ?_, ?_, hxm, hym,
    fun n => ⟨hxD n, hyD n⟩, hxlim, hylim, hLD, hUD, ?_, ?_, ?_⟩
  · intro n t; rw [hxrec]; exact hformula _ _
  · intro n t; rw [hyrec]; exact hformula _ _
  · intro t; exact (congrArg (fun g => g t) hLF).symm.trans (hformula _ _)
  · intro t; exact (congrArg (fun g => g t) hUF).symm.trans (hformula _ _)
  · intro u hu huf
    let z : Icc ℓ v := ⟨u, hu⟩
    have hz : W z = z := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      exact (hformula z t).trans (huf t).symm
    have hxle (n) : x n ≤ u := by
      have h := (hW.iterate n) (show a ≤ z from hu.1)
      exact show (W^[n] a).val ≤ z.val from (show W^[n] a ≤ z by simpa only [Function.iterate_fixed hz] using h)
    have hyle (n) : u ≤ y n := by
      have h := (hW.iterate n) (show z ≤ b from hu.2)
      exact show z.val ≤ (W^[n] b).val from (show z ≤ W^[n] b by simpa only [Function.iterate_fixed hz] using h)
    constructor <;> intro t
    · exact le_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hxlim)
        (Eventually.of_forall (fun n => hxle n t))
    · exact ge_of_tendsto ((continuous_eval_const t).continuousAt.tendsto.comp hylim)
        (Eventually.of_forall (fun n => hyle n t))


lemma continuous_timeOf {T : ℝ} : Continuous (timeOf (T := T)) :=
  (continuous_subtype_val.snd).subtype_mk _

lemma continuous_stripPoint {T : ℝ} {ℓ v : RealCurve T} (hlv : ℓ ≤ v) :
    Continuous (fun q : Triangle T × ℝ => stripPoint hlv q.1 q.2) := by
  apply Continuous.subtype_mk
  apply continuous_fst.prodMk
  exact ((ℓ.continuous.comp continuous_timeOf).comp continuous_fst).max
    (((v.continuous.comp continuous_timeOf).comp continuous_fst).min continuous_snd)

/-- Extension by clipping the state to the original variable order interval. -/
def extendedKernel {T : ℝ} {ℓ v : RealCurve T} (hlv : ℓ ≤ v)
    (G : OrderKernel ℓ v) : Kernel ℝ T (‖ℓ‖ + ‖v‖) :=
  ⟨fun q => G (stripPoint hlv q.1 q.2.val),
    G.continuous.comp ((continuous_stripPoint hlv).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩

lemma interval_norm_bound {T : ℝ} {ℓ v u : RealCurve T} (hu : u ∈ Icc ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ + ‖v‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro t
  rw [Real.norm_eq_abs, abs_le]
  have hl := ℓ.norm_coe_le_norm t
  have hv := v.norm_coe_le_norm t
  rw [Real.norm_eq_abs] at hl hv
  have hlt := (abs_le.mp hl).1
  have hvt := (abs_le.mp hv).2
  have hu0 : ℓ t ≤ u t := hu.1 t
  have hu1 : u t ≤ v t := hu.2 t
  constructor
  · linarith only [hu0, hlt, norm_nonneg v]
  · linarith only [hu1, hvt, norm_nonneg ℓ]

def intervalToBall {T : ℝ} {ℓ v : RealCurve T} (u : Icc ℓ v) :
    Ball ℝ T (‖ℓ‖ + ‖v‖) :=
  ⟨u.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using interval_norm_bound u.property⟩

lemma continuous_intervalToBall {T : ℝ} {ℓ v : RealCurve T} :
    Continuous (intervalToBall (ℓ := ℓ) (v := v)) :=
  continuous_subtype_val.subtype_mk _

lemma extended_integrand {T : ℝ} (hT : 0 ≤ T) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (G : OrderKernel ℓ v) (u : Icc ℓ v) (t : Time T) (s : ℝ) :
    integrand hT (extendedKernel hlv G) (intervalToBall u) t s =
      orderIntegrand hT hlv G u.val t s := rfl

def singularIntervalMap {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    {ℓ v : RealCurve T} (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v)
    (u : Icc ℓ v) : RealCurve T :=
  fractionalMap hT hα f (extendedKernel hlv G) (intervalToBall u)

lemma singularIntervalMap_formula {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    {ℓ v : RealCurve T} (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v)
    (u : Icc ℓ v) (t : Time T) :
    singularIntervalMap hT hα hlv f G u t = singularRhs hT α hlv f G u.val t := rfl

lemma continuous_singularIntervalMap {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    {ℓ v : RealCurve T} (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v) :
    Continuous (singularIntervalMap hT hα hlv f G) :=
  (continuous_fractionalMap hT hα f (extendedKernel hlv G)).comp continuous_intervalToBall

lemma compact_singularIntervalMap {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    {ℓ v : RealCurve T} (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v) :
    IsCompact (closure (range (singularIntervalMap hT hα hlv f G))) := by
  apply (compact_closure_fractionalMap hT hα f (extendedKernel hlv G)).of_isClosed_subset
    isClosed_closure
  apply closure_mono
  rintro g ⟨u, rfl⟩
  exact mem_range_self (intervalToBall u)

lemma orderIntegrand_mono {T : ℝ} (hT : 0 ≤ T) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (G : OrderKernel ℓ v) (hG : KernelMonotone G)
    {u w : RealCurve T} (huw : u ≤ w) (t : Time T) (s : ℝ) :
    orderIntegrand hT hlv G u t s ≤ orderIntegrand hT hlv G w t s := by
  unfold orderIntegrand
  let p := trianglePoint t (projIcc 0 T hT s)
  let a := stripPoint hlv p (u (projIcc 0 T hT s))
  let b := stripPoint hlv p (w (projIcc 0 T hT s))
  exact hG p a.val.2 b.val.2 a.property b.property
    (max_le_max le_rfl (min_le_min le_rfl (huw _)))

lemma monotone_singularIntervalMap {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    {ℓ v : RealCurve T} (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v)
    (hG : KernelMonotone G) : Monotone (singularIntervalMap hT hα hlv f G) := by
  intro u w huw t
  change f t + _ ≤ f t + _
  apply add_le_add_right
  apply intervalIntegral.integral_mono_on t.property.1
    (intervalIntegrable_fractional hT hα (extendedKernel hlv G) (intervalToBall u) t)
    (intervalIntegrable_fractional hT hα (extendedKernel hlv G) (intervalToBall w) t)
  intro s hs
  exact mul_le_mul_of_nonneg_left (orderIntegrand_mono hT hlv G hG huw t s)
    (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

/-- Extremal solutions and monotone uniform convergence, including singular kernels. -/
theorem singular_extremal : Spec.SingularExtremal := by
  intro T hT α hα ℓ v hlv f G hG hsub hsup
  let V := singularIntervalMap hT hα hlv f G
  have hm : Monotone V := monotone_singularIntervalMap hT hα hlv f G hG
  have hinv (u : Icc ℓ v) : V u ∈ Icc ℓ v := by
    constructor
    · exact le_trans hsub (hm (show (⟨ℓ, le_rfl, hlv⟩ : Icc ℓ v) ≤ u from u.property.1))
    · exact le_trans (hm (show u ≤ (⟨v, hlv, le_rfl⟩ : Icc ℓ v) from u.property.2)) hsup
  exact extremal_of_compact hlv V (continuous_singularIntervalMap hT hα hlv f G)
    (compact_singularIntervalMap hT hα hlv f G) hm hinv
    (singularRhs hT α hlv f G) (singularIntervalMap_formula hT hα hlv f G)

lemma singularRhs_one {T : ℝ} (hT : 0 ≤ T) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v) :
    singularRhs hT 1 hlv f G = ordinaryRhs hT hlv f G := by
  funext u t
  simp [singularRhs, ordinaryRhs]

theorem ordinary_extremal : Spec.OrdinaryExtremal := by
  intro T hT ℓ v hlv f G hG hsub hsup
  have h := singular_extremal T hT 1 zero_lt_one ℓ v hlv f G hG
  rw [singularRhs_one] at h
  exact h hsub hsup


/-- On the integration triangle, clipping fixes every curve in the interval.
Thus the equations above are the equations for the original strip kernel. -/
lemma orderIntegrand_restriction {T : ℝ} (hT : 0 ≤ T) {ℓ v u : RealCurve T}
    (hlv : ℓ ≤ v) (G : OrderKernel ℓ v) (hu : u ∈ Icc ℓ v)
    (t : Time T) (s : ℝ) (hs : s ∈ Icc 0 t.val) :
    orderIntegrand hT hlv G u t s =
      G ⟨(⟨(t.val, s), hs.1, hs.2, t.property.2⟩,
          u ⟨s, hs.1, hs.2.trans t.property.2⟩),
        hu.1 ⟨s, hs.1, hs.2.trans t.property.2⟩,
        hu.2 ⟨s, hs.1, hs.2.trans t.property.2⟩⟩ := by
  unfold orderIntegrand
  rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans t.property.2⟩]
  apply congrArg G
  apply Subtype.ext
  have hp : trianglePoint t s =
      (⟨(t.val, s), hs.1, hs.2, t.property.2⟩ : Triangle T) := by
    apply Subtype.ext
    change (t.val, max 0 (min t.val s)) = (t.val, s)
    rw [min_eq_right hs.2, max_eq_right hs.1]
  dsimp only [stripPoint]
  rw [hp]
  refine Prod.ext rfl ?_
  let q : Time T := ⟨s, hs.1, hs.2.trans t.property.2⟩
  change max (ℓ q) (min (v q) (u q)) = u q
  rw [min_eq_right (show u q ≤ v q from hu.2 q),
    max_eq_right (show ℓ q ≤ u q from hu.1 q)]

lemma waiting_isMax {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c) :
    IsMaxWaitingSolution T (NonlinearCounterexamples.waiting c) := by
  have h := (NonlinearCounterexamples.waiting_family T hT c hc).1
  refine ⟨h.1, ?_⟩
  intro t ht
  rw [h.2 t ht]
  apply intervalIntegral.integral_congr
  intro s _
  have hs : 0 ≤ NonlinearCounterexamples.waiting c s := sq_nonneg _
  dsimp only
  rw [max_eq_left hs, abs_of_nonneg hs]

/-- The least and greatest bracketed solutions and the strict intermediate family. -/
theorem waiting_extremes : Spec.WaitingExtremes := by
  intro T hT
  have hsq : IsMaxWaitingSolution T (fun t => t^2) := by
    refine ⟨(continuous_id.pow 2).continuousOn, ?_⟩
    intro t ht
    have heq (s : ℝ) (hs : 0 ≤ s) : NonlinearCounterexamples.waiting 0 s = s^2 := by
      rw [NonlinearCounterexamples.waiting_of_ge hs, sub_zero]
    dsimp only
    rw [← heq t ht.1, (waiting_isMax hT le_rfl).2 t ht]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [heq s hs.1]
  have hz : (0 : RealCurve T) ∈ waitingCurveSet hT := by
    constructor
    · intro t; exact ⟨le_rfl, sq_nonneg _⟩
    · intro t; simp
  have hv : squareCurve T ∈ waitingCurveSet hT := by
    constructor
    · intro t; exact ⟨sq_nonneg _, le_rfl⟩
    · intro t
      change t.val^2 = _
      calc
        t.val^2 = ∫ s in 0..t.val, 2 * Real.sqrt (max (s^2) 0) := hsq.2 t.val t.property
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le t.property.1] at hs
          dsimp only
          rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans t.property.2⟩]
          rfl
  refine ⟨⟨hz, ?_⟩, ⟨hv, ?_⟩, ?_, ?_⟩
  · intro u hu t; exact (hu.1 t).1
  · intro u hu t; exact (hu.1 t).2
  · intro c hc
    exact ⟨waiting_isMax hT hc, (NonlinearCounterexamples.waiting_family T hT c hc).2.2.2⟩
  · intro c hc hcT
    refine ⟨NonlinearCounterexamples.waiting_of_le le_rfl, ?_, ?_⟩
    · rw [NonlinearCounterexamples.waiting_of_ge hcT.le]
      nlinarith [mul_pos hc (show 0 < 2*T-c by linarith)]
    · rw [NonlinearCounterexamples.waiting_of_ge hcT.le]
      exact sq_pos_of_pos (sub_pos.mpr hcT)

end ExpandedFA.PartV.VolterraExtremal
