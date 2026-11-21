import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricWellPosed
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.SymmetricApproximation

/-! Strong Sobolev well-posedness for the whole-space symmetric system. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace P201.Hyperbolic.SymmetricWellPosed
open P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricApproximation
open P201Specs.Hyperbolic.SymmetricWellPosed
open P201.Hyperbolic.SymmetricSobolevEnergy

/-- A Sobolev realization at a fixed order is determined by its L² class. -/
theorem sameSection_injective {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : WholeH n m 𝕜 a} {u v : WholeH n m 𝕜 b}
    (hU : SameSection U u) (hV : SameSection V v) (h : u = v) : U = V := by
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ a
  exact (hU i).trans (h ▸ (hV i).symm)

/-- The exact source range is covered by the q+2 indexing used in the Specs.
This helper retains the supplied full order premise rather than a special case. -/
theorem source_order_index
    (horder : P201Specs.Hyperbolic.SymmetricApproximation.OrderStatement)
    (n s : ℕ) (hn : 1 ≤ n) (hs : n + 2 < 2 * s) :
    ∃ q : ℕ, s = q + 2 ∧ n + 2 < 2 * (q + 2) := by
  have h := horder n s hn hs
  exact ⟨s - 2, h.2.symm, h.2 ▸ hs⟩

/-- A strong solution is a legitimate regular solution for the proved
H^(s-1) energy estimate. Its forcing is lowered by the canonical contraction,
and its high-order lift is the actual H^s path, not a supplied certificate. -/
theorem strong_isRegular {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f U : ℝ → WholeH n m 𝕜 (q + 2)}
    {u du : ℝ → WholeH n m 𝕜 (q + 1)}
    (hf : ContinuousOn f (Icc 0 T)) (h : IsStrongSolution T A B f U u du) :
    IsRegularSolution T A B u du (fun t => lowerOrderCLM (f t)) U := by
  rcases h with ⟨_, hu, hdu, hl, hd, he⟩
  refine ⟨hu, hdu, lowerOrderCLM.continuous.comp_continuousOn hf, ?_, hl, ?_⟩
  · intro t ht
    exact HasDerivWithinAt.hasDerivAt (𝕜 := ℝ) (F := WholeH n m 𝕜 (q + 1))
      (hd t (Ioo_subset_Icc_self ht)) (Icc_mem_nhds ht.1 ht.2)
  · intro t ht
    filter_upwards [underlyingSection_sub (du t) (lowerOrderCLM (f t)), he t ht]
      with x hx heq
    change underlyingSection (du t - lowerOrderCLM (f t)) x = _
    rw [hx]
    simp only [Pi.sub_apply, lowerOrderCLM_underlying]
    rw [heq]
    exact add_sub_cancel_right _ _

/-- The existing evolution theorem gives stability in H^(s-1) for every
pair of strong solutions. This is useful for uniqueness but is not the
required full H^s stability bound. -/
theorem lower_difference_estimate (n q : ℕ) (hn : 1 ≤ n)
    (hs : n + 2 < 2 * (q + 2)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T (q + 2) K A B →
      ∀ (f g U V : ℝ → WholeH n m 𝕜 (q + 2))
        (u du v dv : ℝ → WholeH n m 𝕜 (q + 1)),
        ContinuousOn f (Icc 0 T) → ContinuousOn g (Icc 0 T) →
        IsStrongSolution T A B f U u du → IsStrongSolution T A B g V v dv →
        ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤ Real.exp (C * t) *
          (‖u 0 - v 0‖ + ∫ r in (0 : ℝ)..t,
            ‖lowerOrderCLM (f r) - lowerOrderCLM (g r)‖) := by
  obtain ⟨C, hC, hE⟩ := evolution_estimate n (q + 2) hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB f g U V u du v dv hf hg hu hv
  exact (hE T hT A B hAB (q + 1) (by omega)).2
    u du (fun t => lowerOrderCLM (f t)) v dv (fun t => lowerOrderCLM (g t)) U V
    (strong_isRegular hf hu) (strong_isRegular hg hv)

/-- Uniqueness of strong solutions, by the lower-order energy estimate. -/
theorem uniqueness :
    P201Specs.Hyperbolic.SymmetricWellPosed.UniquenessStatement := by
  intro n q hn hs K hK m 𝕜 _ T hT A B hAB f hf U V u du v dv hU hV h0
  obtain ⟨C, _, hC⟩ := lower_difference_estimate n q hn hs K hK
  have hl0 : u 0 = v 0 :=
    sameSection_injective
      (fun i => (hU.2.2.2.1 0 ⟨le_rfl, hT⟩ i).symm)
      (fun i => (hV.2.2.2.1 0 ⟨le_rfl, hT⟩ i).symm) h0
  intro t ht
  have hb := hC T hT A B hAB f f U V u du v dv hf hf hU hV t ht
  have hz : ‖u t - v t‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hl0, sub_self, norm_zero, intervalIntegral.integral_zero,
      add_zero, mul_zero] using hb
  exact sameSection_injective (hU.2.2.2.1 t ht) (hV.2.2.2.1 t ht)
    (sub_eq_zero.mp (norm_eq_zero.mp hz))

/-- The Hilbert-space step in the source's restarting argument. Weak
continuity alone is insufficient: the separate upper bound must converge
to the norm at the base point. No compact Sobolev embedding is used. -/
theorem continuousWithinAt_of_weak_and_upper_bound
    {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] [TopologicalSpace Y]
    {S : Set Y} {τ : Y} {U : Y → X} {b : Y → ℝ}
    (hweak : ∀ L : X →L[𝕜] 𝕜,
      ContinuousWithinAt (fun t => L (U t)) S τ)
    (hb : Tendsto b (𝓝[S] τ) (𝓝 ‖U τ‖))
    (hbound : ∀ᶠ t in 𝓝[S] τ, ‖U t‖ ≤ b t) :
    ContinuousWithinAt U S τ := by
  have hi : Tendsto (fun t => RCLike.re (inner 𝕜 (U τ) (U t)))
      (𝓝[S] τ) (𝓝 (‖U τ‖ ^ 2)) := by
    simpa only [Function.comp_def, innerSL_apply_apply, inner_self_eq_norm_sq,
      RCLike.ofReal_re] using
      RCLike.continuous_re.continuousAt.tendsto.comp (hweak (innerSL 𝕜 (U τ)))
  have hR : Tendsto
      (fun t => b t ^ 2 - 2 * RCLike.re (inner 𝕜 (U τ) (U t)) + ‖U τ‖ ^ 2)
      (𝓝[S] τ) (𝓝 0) := by
    have hr : ‖U τ‖ ^ 2 - 2 * ‖U τ‖ ^ 2 + ‖U τ‖ ^ 2 = 0 := by ring
    have hh : Tendsto
        (fun t => b t ^ 2 - 2 * RCLike.re (inner 𝕜 (U τ) (U t)) + ‖U τ‖ ^ 2)
        (𝓝[S] τ) (𝓝 (‖U τ‖ ^ 2 - 2 * ‖U τ‖ ^ 2 + ‖U τ‖ ^ 2)) :=
      ((hb.pow 2).sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hi)).add
        (tendsto_const_nhds (x := ‖U τ‖ ^ 2))
    rw [hr] at hh
    exact hh
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp hR).2 (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [he, hbound] with t he ht
  rw [dist_eq_norm]
  have hs : ‖U t‖ ^ 2 ≤ b t ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans ht)).mpr ht
  have hd : ‖U t - U τ‖ ^ 2 ≤
      b t ^ 2 - 2 * RCLike.re (inner 𝕜 (U τ) (U t)) + ‖U τ‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), inner_re_symm]
    linarith
  nlinarith [norm_nonneg (U t - U τ)]

/-- Strong continuity follows once restarting has actually supplied the
two-sided energy bound. This lemma is only the Hilbert-space implication;
it does not assert existence of restarted solutions or assume them as data
of a PDE solution. The absolute interval integral gives both time directions. -/
theorem continuousOn_of_restart_bound
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    {T C : ℝ} (hT : 0 ≤ T) (U F : ℝ → X)
    (hweak : ∀ L : X →L[𝕜] 𝕜, ContinuousOn (fun t => L (U t)) (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T))
    (hb : ∀ τ ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖U t‖ ≤ Real.exp (C * |t - τ|) *
        (‖U τ‖ + |∫ r in τ..t, ‖F r‖|)) :
    ContinuousOn U (Icc 0 T) := by
  intro τ hτ
  apply continuousWithinAt_of_weak_and_upper_bound (𝕜 := 𝕜)
      (b := fun t => Real.exp (C * |t - τ|) *
        (‖U τ‖ + |∫ r in τ..t, ‖F r‖|))
      (fun L => hweak L τ hτ)
  · have hFi : IntervalIntegrable (fun r => ‖F r‖) volume 0 T :=
      hF.norm.intervalIntegrable_of_Icc hT
    have hI : ContinuousOn (fun t => ∫ r in τ..t, ‖F r‖) (Icc 0 T) := by
      simpa only [uIcc_of_le hT] using
        intervalIntegral.continuousOn_primitive_interval' hFi
          (by simpa only [uIcc_of_le hT] using hτ)
    have hbcont : ContinuousWithinAt
        (fun t => Real.exp (C * |t - τ|) *
          (‖U τ‖ + |∫ r in τ..t, ‖F r‖|)) (Icc 0 T) τ :=
      (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_id.sub continuous_const).abs))).continuousWithinAt.mul
        ((continuousWithinAt_const (b := ‖U τ‖)).add (hI τ hτ).abs)
    simpa [ContinuousWithinAt] using hbcont
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hb τ hτ t ht

/-- Uniformly bounded operator families that are continuous on fixed vectors
also act continuously on a continuously varying vector. Norm continuity of
the operator family is not required. -/
theorem continuousOn_apply_of_uniform_bound
    {𝕜 E F Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace Y]
    {S : Set Y} {C : ℝ} (Q : Y → E →L[𝕜] F) (U : Y → E)
    (hQ : ∀ v, ContinuousOn (fun t => Q t v) S)
    (hbound : ∀ t ∈ S, ‖Q t‖ ≤ C) (hU : ContinuousOn U S) :
    ContinuousOn (fun t => Q t (U t)) S := by
  exact P201.Hyperbolic.SymmetricApproximation.continuousOn_apply_of_strongly_continuous
    Q S C hbound hQ U hU

/-- A derivative known after a continuous injective embedding lifts to the
original Banach space when its proposed lift is continuous. The proof uses
the Bochner integral and injectivity, not an invalid inverse norm estimate. -/
theorem hasDerivWithinAt_of_injective_embedding
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (hL : Function.Injective L)
    {T : ℝ} (_hT : 0 ≤ T) (u d : ℝ → X)
    (hu : ContinuousOn u (Icc 0 T)) (hd : ContinuousOn d (Icc 0 T))
    (hderiv : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun r => L (u r)) (L (d t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt u (d t) (Icc 0 T) t := by
  have hint (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable d volume 0 t :=
    (hd.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have heq : ∀ t ∈ Icc 0 T, u t = u 0 + ∫ r in (0 : ℝ)..t, d r := by
    intro t ht
    apply hL
    rw [map_add, ← L.intervalIntegral_comp_comm (hint t ht)]
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (L.continuous.comp_continuousOn (hu.mono (Icc_subset_Icc_right ht.2)))
      (fun r hr => HasDerivWithinAt.hasDerivAt (𝕜 := ℝ) (F := Y)
        (hderiv r ⟨hr.1.le, hr.2.le.trans ht.2⟩)
        (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
      ((L.continuous.comp_continuousOn
        (hd.mono (Icc_subset_Icc_right ht.2))).intervalIntegrable_of_Icc ht.1)
    rw [hf]
    simp only [Function.comp_apply]
    abel
  intro t ht
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hi := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T) (hint t ht)
    (hd.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hd t ht)
  have hh := hi.const_add (u 0)
  exact hh.congr_of_mem heq ht

/-- Adjacent realizations are given by the already constructed canonical
order-lowering map. Equality here is equality of Sobolev elements. -/
theorem lowerOrder_eq_of_sameSection {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U : WholeH n m 𝕜 (k + 1)} {u : WholeH n m 𝕜 k}
    (h : SameSection U u) : lowerOrderCLM U = u := by
  apply PiLp.ext
  intro i
  apply P201.hilbertUnderlyingInjective ⊤ k
  exact (lowerOrderCLM_realizes U i).symm.trans (h i)

theorem lowerOrder_injective {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    Function.Injective (lowerOrderCLM (n := n) (m := m) (k := k) (𝕜 := 𝕜)) := by
  intro U V h
  exact sameSection_injective (lowerOrderCLM_realizes U) (lowerOrderCLM_realizes V) h

/-- Derivatives of a lower-order realization are the same canonical weak
derivatives. This is stronger than an a.e. assertion because the L² coordinates
of the weak derivative graph are definitionally the same elements. -/
theorem derivativeSection_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : WholeH n m 𝕜 (k + 1)) (α : P102.U4.SobolevIndex n k) :
    derivativeSection (lowerOrderCLM U) α =
      derivativeSection U ⟨α.val, α.property.trans (Nat.le_succ k)⟩ := by
  exact P201.Hyperbolic.SymmetricApproximation.TopOperator.derivativeSection_lowerOrder U α

theorem pSection_lowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → P201Specs.Space n → Operator m 𝕜)
    (B : P201Specs.Space n → Operator m 𝕜) (U : WholeH n m 𝕜 (k + 2)) :
    pSection A B (lowerOrderCLM U) = pSection A B U := by
  exact P201.Hyperbolic.SymmetricApproximation.TopOperator.pSection_lowerOrder A B U

/-- After strong H^s continuity has been proved, the intermediate PDE
solution has a continuous strong H^(s-1) derivative, including endpoints.
This proves the last regularity upgrade in the source. The assumption of
high-order continuity is explicit; this lemma does not claim to derive it. -/
theorem strong_of_intermediate {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 1 ≤ n) (hs : n + 2 < 2 * (q + 2)) (K : ℝ) (hK : 0 ≤ K)
    {T : ℝ} (hT : 0 ≤ T) {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (hAB : CoefficientHypotheses T (q + 2) K A B)
    {f U : ℝ → WholeH n m 𝕜 (q + 2)}
    {u : ℝ → WholeH n m 𝕜 (q + 1)} {w du : ℝ → WholeH n m 𝕜 q}
    (hf : ContinuousOn f (Icc 0 T)) (hU : ContinuousOn U (Icc 0 T))
    (hsection : ∀ t ∈ Icc 0 T, SameSection (U t) (u t))
    (h : IsIntermediateSolution T A B f u w du) :
    ∃ d : ℝ → WholeH n m 𝕜 (q + 1), IsStrongSolution T A B f U u d := by
  obtain ⟨C, _, hOp⟩ := operator_family n (q + 2) hn hs K hK
  obtain ⟨Q, hQ, hQc⟩ := hOp (m := m) (𝕜 := 𝕜) T hT A B hAB (q + 1) (by omega)
  let d : ℝ → WholeH n m 𝕜 (q + 1) :=
    fun t => Q t (U t) + lowerOrderCLM (f t)
  have hQU : ContinuousOn (fun t => Q t (U t)) (Icc 0 T) := by
    letI : NormedSpace 𝕜 (WholeH n m 𝕜 (q + 2)) :=
      PiLp.normedSpace 2 𝕜 _
    letI : NormedSpace 𝕜 (WholeH n m 𝕜 (q + 1)) :=
      PiLp.normedSpace 2 𝕜 _
    exact continuousOn_apply_of_uniform_bound (𝕜 := 𝕜)
      (E := WholeH n m 𝕜 (q + 2)) (F := WholeH n m 𝕜 (q + 1))
      Q U hQc (fun t ht => (hQ t ht).2) hU
  have hdc : ContinuousOn d (Icc 0 T) :=
    hQU.add (lowerOrderCLM.continuous.comp_continuousOn hf)
  have hdP : ∀ t ∈ Icc 0 T, underlyingSection (d t) =ᵐ[volume]
      fun x => pSection (fun j => A j t) (B t) (U t) x + underlyingSection (f t) x := by
    intro t ht
    filter_upwards [underlyingSection_add (Q t (U t)) (lowerOrderCLM (f t)),
      (hQ t ht).1 (U t)] with x hadd hp
    change underlyingSection (Q t (U t) + lowerOrderCLM (f t)) x = _
    rw [hadd]
    change underlyingSection (Q t (U t)) x + underlyingSection (lowerOrderCLM (f t)) x = _
    rw [hp, lowerOrderCLM_underlying]
  rcases h with ⟨hu, _hw, _hdu, huw, hdw, he⟩
  have hdL : ∀ t ∈ Icc 0 T, lowerOrderCLM (d t) = du t := by
    intro t ht
    have hp : pSection (fun j => A j t) (B t) (u t) =
        pSection (fun j => A j t) (B t) (U t) := by
      rw [← lowerOrder_eq_of_sameSection (hsection t ht)]
      exact pSection_lowerOrder _ _ _
    apply underlying_injective
    rw [lowerOrderCLM_underlying]
    exact (hdP t ht).trans (by simpa only [hp] using (he t ht).symm)
  have hdiff : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt u (d t) (Icc 0 T) t := by
    letI : NormedSpace ℝ (WholeH n m 𝕜 (q + 1)) := PiLp.normedSpace 2 ℝ _
    letI : NormedSpace ℝ (WholeH n m 𝕜 q) := PiLp.normedSpace 2 ℝ _
    let L : WholeH n m 𝕜 (q + 1) →L[ℝ] WholeH n m 𝕜 q :=
      (lowerOrderCLM (n := n) (m := m) (k := q) (𝕜 := 𝕜)).restrictScalars ℝ
    have hL : Function.Injective L := lowerOrder_injective (n := n) (m := m) (k := q) (𝕜 := 𝕜)
    apply hasDerivWithinAt_of_injective_embedding
      L hL hT u d hu hdc
    intro t ht
    have hdt : HasDerivWithinAt w (lowerOrderCLM (d t)) (Icc 0 T) t := by
      rw [hdL t ht]
      exact hdw t ht
    exact hdt.congr_of_mem (fun r hr => lowerOrder_eq_of_sameSection (huw r hr)) ht
  exact ⟨d, hU, hu, hdc, hsection, hdiff, hdP⟩


open scoped ContDiff

/-- A smooth change of the time variable preserves exactly the spatial bounds. -/
theorem boundedSmoothCoefficient_comp_time {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T D K : ℝ} {a : LowerOrder n m 𝕜} {φ : ℝ → ℝ}
    (ha : BoundedSmoothCoefficient T s K a) (hφ : ContDiff ℝ ∞ φ)
    (hmap : MapsTo φ (Icc 0 D) (Icc 0 T)) :
    BoundedSmoothCoefficient D s K (fun r => a (φ r)) := by
  refine ⟨?_, fun α hα r hr x => ha.2 α hα (φ r) (hmap hr) x⟩
  exact ha.1.comp ((hφ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨hmap hz.1, hz.2⟩)

/-- Negating the operator, as in backward time, preserves the same bound. -/
theorem boundedSmoothCoefficient_neg {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {a : LowerOrder n m 𝕜}
    (ha : BoundedSmoothCoefficient T s K a) :
    BoundedSmoothCoefficient T s K (fun r x => -a r x) := by
  refine ⟨ha.1.neg, ?_⟩
  intro α hα t ht x
  change ‖spatialWord (fun x => -a t x) (α.sort (· ≤ ·)) x‖ ≤ K
  rw [spatialWord_neg (coefficient_slice_contDiff ha.1 ht), norm_neg]
  exact ha.2 α hα t ht x

theorem coefficientHypotheses_comp_time {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T D K : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜} {φ : ℝ → ℝ}
    (hAB : CoefficientHypotheses T s K A B) (hφ : ContDiff ℝ ∞ φ)
    (hmap : MapsTo φ (Icc 0 D) (Icc 0 T)) :
    CoefficientHypotheses D s K (fun j r => A j (φ r)) (fun r => B (φ r)) :=
  ⟨fun j => boundedSmoothCoefficient_comp_time (hAB.1 j) hφ hmap,
    boundedSmoothCoefficient_comp_time hAB.2.1 hφ hmap,
    fun j r hr x => hAB.2.2 j (φ r) (hmap hr) x⟩

theorem coefficientHypotheses_neg {n m s : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T K : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    (hAB : CoefficientHypotheses T s K A B) :
    CoefficientHypotheses T s K (fun j r x => -A j r x) (fun r x => -B r x) :=
  ⟨fun j => boundedSmoothCoefficient_neg (hAB.1 j),
    boundedSmoothCoefficient_neg hAB.2.1,
    fun j r hr x => IsSelfAdjoint.neg (R := Operator m 𝕜) (hAB.2.2 j r hr x)⟩

/-- Restriction and translation of an intermediate solution, including its
one-sided derivatives. -/
theorem intermediate_shift {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T D τ : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f : ℝ → WholeH n m 𝕜 (q+2)} {u : ℝ → WholeH n m 𝕜 (q+1)}
    {w du : ℝ → WholeH n m 𝕜 q}
    (h : IsIntermediateSolution T A B f u w du)
    (hmap : MapsTo (fun r => τ + r) (Icc 0 D) (Icc 0 T)) :
    IsIntermediateSolution D (fun j r => A j (τ+r)) (fun r => B (τ+r))
      (fun r => f (τ+r)) (fun r => u (τ+r))
      (fun r => w (τ+r)) (fun r => du (τ+r)) := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) := PiLp.normedSpace 2 ℝ _
  rcases h with ⟨hu, hw, hdu, hsame, hd, he⟩
  have hc : ContinuousOn (fun r : ℝ => τ+r) (Icc 0 D) :=
    (continuous_const.add continuous_id).continuousOn
  refine ⟨hu.comp hc hmap, hw.comp hc hmap, hdu.comp hc hmap,
    fun r hr => hsame _ (hmap hr), ?_, fun r hr => he _ (hmap hr)⟩
  intro r hr
  have hc' : HasDerivWithinAt (fun r : ℝ => τ+r) 1 (Icc 0 D) r := by
    simpa using ((hasDerivAt_id r).const_add τ).hasDerivWithinAt (s := Icc 0 D)
  convert! (hd _ (hmap hr)).scomp r hc' hmap using 1
  simp only [one_smul]

/-- The canonical PDE section changes sign when the coefficients do. -/
theorem pSection_neg_coefficients {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → P201Specs.Space n → Operator m 𝕜)
    (B : P201Specs.Space n → Operator m 𝕜) (u : WholeH n m 𝕜 (k+1)) :
    pSection (fun j x => -A j x) (fun x => -B x) u = -pSection A B u := by
  funext x
  simp only [pSection, ContinuousLinearMap.neg_apply, Finset.sum_neg_distrib, Pi.neg_apply]
  abel

/-- Reverse time in the actual PDE and in its strong lower derivative. -/
theorem intermediate_reverse {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T D τ : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f : ℝ → WholeH n m 𝕜 (q+2)} {u : ℝ → WholeH n m 𝕜 (q+1)}
    {w du : ℝ → WholeH n m 𝕜 q}
    (h : IsIntermediateSolution T A B f u w du)
    (hmap : MapsTo (fun r => τ-r) (Icc 0 D) (Icc 0 T)) :
    IsIntermediateSolution D (fun j r x => -A j (τ-r) x) (fun r x => -B (τ-r) x)
      (fun r => -f (τ-r)) (fun r => u (τ-r))
      (fun r => w (τ-r)) (fun r => -du (τ-r)) := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 q) := PiLp.normedSpace 2 ℝ _
  rcases h with ⟨hu, hw, hdu, hsame, hd, he⟩
  have hc : ContinuousOn (fun r : ℝ => τ-r) (Icc 0 D) :=
    (continuous_const.sub continuous_id).continuousOn
  refine ⟨hu.comp hc hmap, hw.comp hc hmap, (hdu.comp hc hmap).neg,
    fun r hr => hsame _ (hmap hr), ?_, ?_⟩
  · intro r hr
    have hc' : HasDerivWithinAt (fun r : ℝ => τ-r) (-1) (Icc 0 D) r := by
      simpa using ((hasDerivAt_id r).const_sub τ).hasDerivWithinAt (s := Icc 0 D)
    convert! (hd _ (hmap hr)).scomp r hc' hmap using 1
    simp only [neg_one_smul]
  · intro r hr
    filter_upwards [underlyingSection_neg (du (τ-r)), underlyingSection_neg (f (τ-r)),
      he _ (hmap hr)] with x hdu hf heq
    rw [hdu, hf]
    simp only [Pi.neg_apply, pSection_neg_coefficients]
    rw [heq]
    abel


/-- Two-sided restarting in the intermediate class. Intermediate uniqueness
identifies each new construction with the given solution, so no strong
high-order continuity is assumed in obtaining this estimate. -/
theorem restart_bound (n q : ℕ) (hn : 1 ≤ n)
    (hs : n + 2 < 2 * (q+2)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
      (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T (q+2) K A B →
      ∀ (f U : ℝ → WholeH n m 𝕜 (q+2))
        (u : ℝ → WholeH n m 𝕜 (q+1)) (w du : ℝ → WholeH n m 𝕜 q),
      ContinuousOn f (Icc 0 T) → IsIntermediateSolution T A B f u w du →
      (∀ r ∈ Icc 0 T, SameSection (U r) (u r)) →
      ∀ τ ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖U t‖ ≤ Real.exp (C * |t-τ|) * (‖U τ‖ + |∫ r in τ..t, ‖f r‖|) := by
  obtain ⟨C, hC, hE⟩ := P201.Hyperbolic.SymmetricApproximation.existence n q hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB f U u w du hf hsol hsame τ hτ t ht
  rcases le_total τ t with hforward | hbackward
  · let D := t-τ
    have hD : 0 ≤ D := sub_nonneg.mpr hforward
    have hmap : MapsTo (fun r => τ+r) (Icc 0 D) (Icc 0 T) := by
      intro r hr
      dsimp [D] at hr ⊢
      constructor <;> linarith [hr.1, hr.2, hτ.1, ht.2]
    have hφ : ContDiff ℝ ∞ (fun r : ℝ => τ+r) := contDiff_const.add contDiff_id
    have hAB' := coefficientHypotheses_comp_time hAB hφ hmap
    have hf' := hf.comp (continuous_const.add continuous_id).continuousOn hmap
    obtain ⟨V, v, z, dz, hv, hVv, hV0, _, hb⟩ :=
      hE D hD _ _ hAB' (U τ) (fun r => f (τ+r)) hf'
    have hinit : v 0 = u (τ+0) := by
      apply sameSection_injective (fun i => (hVv 0 ⟨le_rfl,hD⟩ i).symm)
        (fun i => (hsame (τ+0) (hmap ⟨le_rfl,hD⟩) i).symm)
      simpa using hV0
    have heq := P201.Hyperbolic.SymmetricApproximation.uniqueness n q hn hs K hK
      D hD _ _ hAB' _ hf' v (fun r => u (τ+r)) z dz
      (fun r => w (τ+r)) (fun r => du (τ+r))
      hv (intermediate_shift hsol hmap) hinit ⟨hD,le_rfl⟩
    have hτD : τ+D = t := by dsimp [D]; ring
    have hVU : V D = U t := by
      apply sameSection_injective (hVv D ⟨hD,le_rfl⟩) (hsame t ht)
      simpa only [hτD] using heq
    have hI : (∫ r in (0:ℝ)..D, ‖f (τ+r)‖) = ∫ r in τ..t, ‖f r‖ := by
      rw [intervalIntegral.integral_comp_add_left (fun r => ‖f r‖) τ]
      simp only [add_zero, hτD]
    have hpos : 0 ≤ ∫ r in τ..t, ‖f r‖ :=
      intervalIntegral.integral_nonneg hforward (fun r _ => norm_nonneg _)
    simpa only [hVU, hI, abs_of_nonneg (sub_nonneg.mpr hforward),
      abs_of_nonneg hpos, D] using hb D ⟨hD,le_rfl⟩
  · let D := τ-t
    have hD : 0 ≤ D := sub_nonneg.mpr hbackward
    have hmap : MapsTo (fun r => τ-r) (Icc 0 D) (Icc 0 T) := by
      intro r hr
      dsimp [D] at hr ⊢
      constructor <;> linarith [hr.1, hr.2, ht.1,hτ.2]
    have hφ : ContDiff ℝ ∞ (fun r : ℝ => τ-r) := contDiff_const.sub contDiff_id
    have hAB' := coefficientHypotheses_neg (coefficientHypotheses_comp_time hAB hφ hmap)
    have hf' := (hf.comp (continuous_const.sub continuous_id).continuousOn hmap).neg
    obtain ⟨V, v, z, dz, hv, hVv, hV0, _, hb⟩ :=
      hE D hD _ _ hAB' (U τ) (fun r => -f (τ-r)) hf'
    have hinit : v 0 = u (τ-0) := by
      apply sameSection_injective (fun i => (hVv 0 ⟨le_rfl,hD⟩ i).symm)
        (fun i => (hsame (τ-0) (hmap ⟨le_rfl,hD⟩) i).symm)
      simpa using hV0
    have heq := P201.Hyperbolic.SymmetricApproximation.uniqueness n q hn hs K hK
      D hD _ _ hAB' _ hf' v (fun r => u (τ-r)) z dz
      (fun r => w (τ-r)) (fun r => -du (τ-r))
      hv (intermediate_reverse hsol hmap) hinit ⟨hD,le_rfl⟩
    have hτD : τ-D = t := by dsimp [D]; ring
    have hVU : V D = U t := by
      apply sameSection_injective (hVv D ⟨hD,le_rfl⟩) (hsame t ht)
      simpa only [hτD] using heq
    have hI : (∫ r in (0:ℝ)..D, ‖-f (τ-r)‖) = ∫ r in t..τ, ‖f r‖ := by
      simp only [norm_neg]
      rw [intervalIntegral.integral_comp_sub_left (fun r => ‖f r‖) τ]
      simp only [sub_zero, hτD]
    have hpos : 0 ≤ ∫ r in t..τ, ‖f r‖ :=
      intervalIntegral.integral_nonneg hbackward (fun r _ => norm_nonneg _)
    have hIabs : |∫ r in τ..t, ‖f r‖| = ∫ r in t..τ, ‖f r‖ := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hpos]
    have habs : |t-τ| = D := by rw [abs_of_nonpos (sub_nonpos.mpr hbackward)]; dsimp [D]; ring
    simpa only [hVU, hI, habs, hIabs] using hb D ⟨hD,le_rfl⟩

/-- Full strong existence, with the quantitative bound from the actual
Friedrichs limit, followed by two-sided restarting and the derivative upgrade. -/
theorem existence : P201Specs.Hyperbolic.SymmetricWellPosed.ExistenceStatement := by
  intro n q hn hs K hK
  obtain ⟨C, hC, hE⟩ := P201.Hyperbolic.SymmetricApproximation.existence n q hn hs K hK
  obtain ⟨R, _, hR⟩ := restart_bound n q hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB g f hf
  obtain ⟨U,u,w,du,hsol,hsame,h0,hweak,hbound⟩ := hE T hT A B hAB g f hf
  have hUc : ContinuousOn U (Icc 0 T) :=
    continuousOn_of_restart_bound (𝕜 := 𝕜) hT U f hweak hf
      (hR T hT A B hAB f U u w du hf hsol hsame)
  obtain ⟨d, hd⟩ := strong_of_intermediate hn hs K hK hT hAB hf hUc hsame hsol
  exact ⟨U,u,d,hd,h0,hbound⟩

/-- Subtraction preserves the strong solution class when Q realizes the
actual differential operator; equalities of chosen sections remain a.e. -/
theorem strong_sub_of_realizesP {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {T : ℝ} {A : Principal n m 𝕜} {B : LowerOrder n m 𝕜}
    {f g U V : ℝ → WholeH n m 𝕜 (q + 2)}
    {u du v dv : ℝ → WholeH n m 𝕜 (q + 1)}
    (Q : ℝ → WholeH n m 𝕜 (q + 2) →L[𝕜] WholeH n m 𝕜 (q + 1))
    (hQ : ∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t))
    (hU : IsStrongSolution T A B f U u du)
    (hV : IsStrongSolution T A B g V v dv) :
    IsStrongSolution T A B (fun t => f t - g t) (fun t => U t - V t)
      (fun t => u t - v t) (fun t => du t - dv t) := by
  letI : NormedSpace ℝ (WholeH n m 𝕜 (q + 1)) := PiLp.normedSpace 2 ℝ _
  rcases hU with ⟨hUc, huc, hduc, hUu, hdu, hUE⟩
  rcases hV with ⟨hVc, hvc, hdvc, hVv, hdv, hVE⟩
  refine ⟨hUc.sub hVc, huc.sub hvc, hduc.sub hdvc,
    fun t ht => isLowerOrder_sub (hUu t ht) (hVv t ht),
    fun t ht => (hdu t ht).sub (hdv t ht), ?_⟩
  intro t ht
  filter_upwards [underlyingSection_sub (du t) (dv t),
    underlyingSection_sub (f t) (g t), hUE t ht, hVE t ht,
    hQ t ht (U t), hQ t ht (V t), hQ t ht (U t - V t),
    underlyingSection_sub (Q t (U t)) (Q t (V t))]
    with x hder hf heU heV hpU hpV hpD hpS
  rw [hder, hf]
  simp only [Pi.sub_apply]
  rw [heU, heV, ← hpD, map_sub, hpS]
  simp only [Pi.sub_apply]
  rw [hpU, hpV]
  abel

/-- Full H^s stability follows from strong existence and uniqueness by
solving once for the difference data. The constant is exactly the one
provided by existence, with the same uniform parameter dependence. -/
theorem existence_to_difference
    (hExist : P201Specs.Hyperbolic.SymmetricWellPosed.ExistenceStatement) :
    P201Specs.Hyperbolic.SymmetricWellPosed.DifferenceStatement := by
  intro n q hn hs K hK
  obtain ⟨C, hC, hE⟩ := hExist n q hn hs K hK
  obtain ⟨_, _, hOp⟩ := operator_family n (q + 2) hn hs K hK
  refine ⟨C, hC, ?_⟩
  intro m 𝕜 _ T hT A B hAB f g U V u du v dv hf hg hU hV t ht
  obtain ⟨Q, hQ, _⟩ := hOp (m := m) (𝕜 := 𝕜) T hT A B hAB (q + 1) (by omega)
  obtain ⟨W, w, dw, hW, hW0, hb⟩ :=
    hE T hT A B hAB (U 0 - V 0) (fun r => f r - g r) (hf.sub hg)
  have hDiff := strong_sub_of_realizesP Q (fun r hr => (hQ r hr).1) hU hV
  have heq := uniqueness n q hn hs K hK T hT A B hAB
    (fun r => f r - g r) (hf.sub hg) (fun r => U r - V r) W
    (fun r => u r - v r) (fun r => du r - dv r) w dw hDiff hW hW0.symm
  simpa only [← heq ht] using hb t ht

/-- The source H^s difference estimate, hence continuous dependence. -/
theorem difference_estimate :
    P201Specs.Hyperbolic.SymmetricWellPosed.DifferenceStatement :=
  existence_to_difference existence

end P201.Hyperbolic.SymmetricWellPosed
