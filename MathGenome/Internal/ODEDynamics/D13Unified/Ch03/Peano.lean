import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.Peano
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.RestrictionPasting
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology Interval NNReal

namespace D13Unified.Ch03
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compactness closes integral equations evaluated at nearby times.
All sample points stay in the original box. The shifts in both time and state
vanish, so dominated convergence passes the sampled equations to the limit. -/
theorem exists_solution_of_sampled_integral_curves
    (f : ℝ × E → E) (s h b M : ℝ) (ξ : E) (hh : 0 ≤ h)
    (hf : ContinuousOn f (Icc s (s+h) ×ˢ closedBall ξ b))
    (hbound : ∀ p ∈ Icc s (s+h) ×ˢ closedBall ξ b, ‖f p‖ ≤ M)
    (u : ℕ → ℝ → E)
    (hu : ∀ k, ContinuousOn (u k) (Icc s (s+h)))
    (hub : ∀ k t, t ∈ Icc s (s+h) → u k t ∈ closedBall ξ b)
    (hequi : Equicontinuous (fun k (t : Icc s (s+h)) => u k t))
    (σ : ℕ → ℝ → ℝ)
    (hσ : ∀ k, ContinuousOn (σ k) (Icc s (s+h)))
    (hσmap : ∀ k, MapsTo (σ k) (Icc s (s+h)) (Icc s (s+h)))
    (hσlim : ∀ t ∈ Icc s (s+h), Tendsto (fun k => σ k t) atTop (𝓝 t))
    (hmove : ∀ t ∈ Icc s (s+h),
      Tendsto (fun k => u k (σ k t) - u k t) atTop (𝓝 0))
    (heq : ∀ k t, t ∈ Icc s (s+h) →
      u k t = ξ + ∫ r in s..t, f (σ k r, u k (σ k r))) :
    ∃ x : ℝ → E, ContinuousOn x (Icc s (s+h)) ∧ x s = ξ ∧
      (∀ t ∈ Icc s (s+h), x t ∈ closedBall ξ b) ∧
      ∀ t ∈ Icc s (s+h), HasDerivWithinAt x (f (t, x t)) (Icc s (s+h)) t := by
  let J := Icc s (s+h)
  let U : ℕ → BoundedContinuousFunction J E := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨fun t => u k t, (hu k).domRestrict⟩
  have hUequi : Equicontinuous ((↑) : Set.range U → J → E) := by
    intro x V hV
    filter_upwards [hequi x V hV] with y hy
    rintro ⟨v, k, rfl⟩
    exact hy k
  have hc : IsCompact (closure (Set.range U)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall ξ b)
      (isCompact_closedBall ξ b) (Set.range U)
      (by intro v t hv; obtain ⟨k, rfl⟩ := hv; exact hub k t t.property) hUequi
  obtain ⟨v, _, φ, hφ, hlim⟩ :=
    hc.tendsto_subseq (fun k => subset_closure (Set.mem_range_self k))
  have hlim' : TendstoUniformly (fun k (t : J) => u (φ k) t) v atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let x : ℝ → E := fun t => if ht : t ∈ J then v ⟨t, ht⟩ else ξ
  have hxeq (t : J) : x t = v t := by simp [x, t.property]
  have hx : ContinuousOn x J := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert v.continuous using 1
    ext t
    exact hxeq t
  have hxlim (t : ℝ) (ht : t ∈ J) :
      Tendsto (fun k => u (φ k) t) atTop (𝓝 (x t)) := by
    simpa only [hxeq ⟨t, ht⟩] using hlim'.tendsto_at ⟨t, ht⟩
  have hxb (t : ℝ) (ht : t ∈ J) : x t ∈ closedBall ξ b :=
    isClosed_closedBall.mem_of_tendsto (hxlim t ht)
      (Eventually.of_forall fun k => hub (φ k) t ht)
  have hg : ContinuousOn (fun r => f (r, x r)) J :=
    hf.comp (continuousOn_id.prodMk hx) (fun t ht => ⟨ht, hxb t ht⟩)
  have hi (t : ℝ) (ht : t ∈ J) : x t = ξ + ∫ r in s..t, f (r, x r) := by
    have hst : s ≤ t := ht.1
    have hsub : Ι s t ⊆ J := by
      rw [uIoc_of_le hst]
      intro r hr
      exact ⟨hr.1.le, hr.2.trans ht.2⟩
    have hint : Tendsto (fun k => ∫ r in s..t, f (σ (φ k) r, u (φ k) (σ (φ k) r))) atTop
        (𝓝 (∫ r in s..t, f (r, x r))) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      · apply Eventually.of_forall
        intro k
        have hcont : ContinuousOn (fun r => f (σ (φ k) r, u (φ k) (σ (φ k) r))) J :=
          hf.comp ((hσ (φ k)).prodMk ((hu (φ k)).comp (hσ (φ k)) (hσmap (φ k))))
            (fun r hr => ⟨hσmap (φ k) hr, hub (φ k) _ (hσmap (φ k) hr)⟩)
        exact (hcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
      · exact Eventually.of_forall fun k => ae_of_all _ fun r hr =>
          hbound _ ⟨hσmap (φ k) (hsub hr), hub (φ k) _ (hσmap (φ k) (hsub hr))⟩
      · exact intervalIntegrable_const
      · apply ae_of_all
        intro r hr
        have hshift : Tendsto (fun k => u (φ k) (σ (φ k) r)) atTop (𝓝 (x r)) := by
          have hv := ((hmove r (hsub hr)).comp hφ.tendsto_atTop).add (hxlim r (hsub hr))
          simpa only [Function.comp_def, sub_add_cancel, zero_add] using hv
        exact (hf (r, x r) ⟨hsub hr, hxb r (hsub hr)⟩).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr
            ⟨((hσlim r (hsub hr)).comp hφ.tendsto_atTop).prodMk_nhds hshift,
            Eventually.of_forall fun k =>
              ⟨hσmap (φ k) (hsub hr), hub (φ k) _ (hσmap (φ k) (hsub hr))⟩⟩)
    exact tendsto_nhds_unique (hxlim t ht)
      ((tendsto_const_nhds.add hint).congr (fun k => (heq (φ k) t ht).symm))
  have hs : s ∈ J := ⟨le_rfl, by linarith⟩
  refine ⟨x, hx, ?_, hxb, ?_⟩
  · simpa using hi s hs
  · intro t ht
    have hd := (D13Unified.hasDerivWithinAt_integral_on_interval ordConnected_Icc hg hs ht).const_add ξ
    exact hd.congr_of_mem (fun r hr => hi r hr) ht

omit [FiniteDimensional ℝ E] in
/-- The zero-bound case includes zero-radius state balls. -/
theorem peano_right_zero (f : ℝ × E → E) (s a b h : ℝ) (ξ : E)
    (hbound : ∀ p ∈ Icc s (s+a) ×ˢ closedBall ξ b, ‖f p‖ ≤ 0)
    (_hh : 0 < h) (ha : h ≤ a) (hb : 0 ≤ b) :
    ∃ x : ℝ → E, ContinuousOn x (Icc s (s+h)) ∧ x s = ξ ∧
      (∀ t ∈ Icc s (s+h), x t ∈ closedBall ξ b) ∧
      ∀ t ∈ Icc s (s+h), HasDerivWithinAt x (f (t, x t)) (Icc s (s+h)) t := by
  refine ⟨fun _ => ξ, continuousOn_const, rfl, fun _ _ => mem_closedBall_self hb, ?_⟩
  intro t ht
  have hf : f (t, ξ) = 0 := norm_le_zero_iff.mp
    (hbound (t, ξ) ⟨⟨ht.1, ht.2.trans (by linarith)⟩, mem_closedBall_self hb⟩)
  rw [hf]
  exact (hasDerivAt_const t ξ).hasDerivWithinAt

/-- A continuous delayed Picard construction. After `n` steps, later iterates
agree on the first `n` delay lengths. This avoids jumps in polygonal slopes. -/
def delayedPicard (f : ℝ × E → E) (s δ : ℝ) (ξ : E) : ℕ → ℝ → E
  | 0 => fun _ => ξ
  | n+1 => fun t => ξ + ∫ r in s..t, f (max s (r-δ), delayedPicard f s δ ξ n (max s (r-δ)))

/-- Each delayed iterate stays in the same ball, and its velocity is bounded
by the original field bound. No Lipschitz condition on the field is used. -/
theorem delayedPicard_properties (f : ℝ × E → E) (s h b M δ : ℝ) (ξ : E)
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hb : M*h ≤ b)
    (hf : ContinuousOn f (Icc s (s+h) ×ˢ closedBall ξ b))
    (hbound : ∀ p ∈ Icc s (s+h) ×ˢ closedBall ξ b, ‖f p‖ ≤ M) :
    ∀ n, ContinuousOn (delayedPicard f s δ ξ n) (Icc s (s+h)) ∧
      (∀ t ∈ Icc s (s+h), delayedPicard f s δ ξ n t ∈ closedBall ξ b) ∧
      (∀ t ∈ Icc s (s+h), ‖delayedPicard f s δ ξ n t - ξ‖ ≤ M*(t-s)) ∧
      LipschitzOnWith ⟨M, hM⟩ (delayedPicard f s δ ξ n) (Icc s (s+h)) := by
  let J := Icc s (s+h)
  let d : ℝ → ℝ := fun r => max s (r-δ)
  have hd : Continuous d := continuous_const.max (continuous_id.sub continuous_const)
  have hdJ : MapsTo d J J := by
    intro t ht
    exact ⟨le_max_left _ _, max_le (by linarith) (by linarith [ht.2])⟩
  have hs : s ∈ J := ⟨le_rfl, by linarith⟩
  have hb0 : 0 ≤ b := (mul_nonneg hM hh).trans hb
  intro n
  induction n with
  | zero =>
    refine ⟨continuousOn_const, fun _ _ => mem_closedBall_self hb0, ?_, ?_⟩
    · intro t ht
      simpa [delayedPicard] using mul_nonneg hM (sub_nonneg.mpr ht.1)
    · exact ((LipschitzWith.const ξ).weaken (show (0 : ℝ≥0) ≤ ⟨M, hM⟩ from bot_le)).lipschitzOnWith
  | succ n ih =>
    let g : ℝ → E := fun r => f (d r, delayedPicard f s δ ξ n (d r))
    have hg : ContinuousOn g J := hf.comp
      (hd.continuousOn.prodMk (ih.1.comp hd.continuousOn hdJ))
      (fun r hr => ⟨hdJ hr, ih.2.1 _ (hdJ hr)⟩)
    have hgM : ∀ r ∈ J, ‖g r‖ ≤ M :=
      fun r hr => hbound _ ⟨hdJ hr, ih.2.1 _ (hdJ hr)⟩
    have hder : ∀ t ∈ J, HasDerivWithinAt (delayedPicard f s δ ξ (n+1)) (g t) J t := by
      intro t ht
      exact (hasDerivWithinAt_integral_on_interval ordConnected_Icc hg hs ht).const_add ξ
    have hnorm : ∀ t ∈ J, ‖delayedPicard f s δ ξ (n+1) t - ξ‖ ≤ M*(t-s) := by
      intro t ht
      simp only [delayedPicard, add_sub_cancel_left]
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
        (fun r hr => hgM r (by
          rw [uIoc_of_le ht.1] at hr
          exact ⟨hr.1.le, hr.2.trans ht.2⟩))
      simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hi
    refine ⟨HasDerivWithinAt.continuousOn hder, ?_, hnorm, ?_⟩
    · intro t ht
      rw [mem_closedBall, dist_eq_norm]
      exact (hnorm t ht).trans ((mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM).trans hb)
    · exact (convex_Icc s (s+h)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hder
        (fun t ht => by exact_mod_cast hgM t ht)

omit [FiniteDimensional ℝ E] in
/-- Successive delayed iterates agree before the delay has propagated from
its initial value. -/
theorem delayedPicard_stable (f : ℝ × E → E) (s h δ : ℝ) (ξ : E)
    (hδ : 0 ≤ δ) :
    ∀ (n : ℕ) t, t ∈ Icc s (s+h) → t ≤ s + (n:ℝ)*δ →
      delayedPicard f s δ ξ (n+1) t = delayedPicard f s δ ξ n t := by
  intro n
  induction n with
  | zero =>
    intro t ht htn
    have : t = s := le_antisymm (by simpa using htn) ht.1
    subst t
    simp [delayedPicard]
  | succ n ih =>
    intro t ht htn
    change ξ + (∫ r in s..t, f (max s (r-δ), delayedPicard f s δ ξ (n+1) (max s (r-δ)))) =
      ξ + (∫ r in s..t, f (max s (r-δ), delayedPicard f s δ ξ n (max s (r-δ))))
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc s t := by simpa [uIcc_of_le ht.1] using hr
    have hd : max s (r-δ) ∈ Icc s (s+h) :=
      ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (by linarith [hr'.2, ht.2])⟩
    exact congrArg (fun z => f (max s (r-δ), z))
      (ih _ hd (by push_cast at htn; apply max_le <;> nlinarith [Nat.cast_nonneg (α := ℝ) n, hr'.2]))

/-- Peano existence on the right, with its complete quantitative lifespan. -/
theorem peano_right : Specs.D13Unified.Ch03.Peano.rightExpected := by
  intro E _ _ _ f s a b M h ξ hf hbound hM hh ha hb
  by_cases hM0 : M = 0
  · subst M
    exact peano_right_zero f s a b h ξ hbound hh ha (by simpa using hb)
  · let J := Icc s (s+h)
    have hf' : ContinuousOn f (J ×ˢ closedBall ξ b) := hf.mono (by
      rintro ⟨t,z⟩ ⟨ht,hz⟩
      exact ⟨⟨ht.1, ht.2.trans (by linarith)⟩,hz⟩)
    have hbound' : ∀ p ∈ J ×ˢ closedBall ξ b, ‖f p‖ ≤ M := by
      rintro ⟨t,z⟩ ⟨ht,hz⟩
      exact hbound _ ⟨⟨ht.1, ht.2.trans (by linarith)⟩,hz⟩
    let δ : ℕ → ℝ := fun k => h / ((k:ℝ)+1)
    have hδpos (k : ℕ) : 0 < δ k := div_pos hh (by positivity)
    have hδeq (k : ℕ) : ((k:ℝ)+1)*δ k = h := by
      dsimp [δ]
      field_simp
    have hδlim : Tendsto δ atTop (𝓝 0) := by
      have hv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul h
      simpa only [mul_one_div, mul_zero] using hv
    let u : ℕ → ℝ → E := fun k => delayedPicard f s (δ k) ξ (k+1)
    have hu (k : ℕ) := delayedPicard_properties f s h b M (δ k) ξ hh.le
      (hδpos k).le hM hb hf' hbound' (k+1)
    let σ : ℕ → ℝ → ℝ := fun k t => max s (t-δ k)
    have hσmap (k : ℕ) : MapsTo (σ k) J J := by
      intro t ht
      exact ⟨le_max_left _ _, max_le (by linarith [ht.1, ht.2])
        (by have := hδpos k; linarith [ht.2])⟩
    have hσdist (k : ℕ) (t : ℝ) (ht : t ∈ J) : |σ k t - t| ≤ δ k := by
      rw [abs_le]
      constructor
      · have hx := le_max_right s (t-δ k)
        dsimp [σ]
        linarith
      · have hx : max s (t-δ k) ≤ t := max_le ht.1 (by have := hδpos k; linarith)
        dsimp [σ]
        have := hδpos k
        linarith
    have hequi : Equicontinuous (fun k (t : J) => u k t) := by
      apply Metric.equicontinuous_of_continuity_modulus (fun r => M*r)
        (by simpa using (tendsto_id.const_mul M : Tendsto (fun r : ℝ => M*r) (𝓝 0) (𝓝 (M*0))))
      intro t r k
      exact (hu k).2.2.2.dist_le_mul t t.property r r.property
    apply exists_solution_of_sampled_integral_curves f s h b M ξ hh.le hf' hbound' u
      (fun k => (hu k).1) (fun k => (hu k).2.1) hequi σ
      (fun k => (continuous_const.max (continuous_id.sub continuous_const)).continuousOn)
      hσmap
    · intro t ht
      have hv : Tendsto (fun k => max s (t-δ k)) atTop (𝓝 (max s (t-0))) :=
        tendsto_const_nhds.max (tendsto_const_nhds.sub hδlim)
      simpa only [sub_zero, max_eq_right ht.1] using hv
    · intro t ht
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun k => norm_nonneg _)
        (fun k => ?_) (by simpa only [mul_zero] using hδlim.const_mul M)
      have hle := (hu k).2.2.2.dist_le_mul (σ k t) (hσmap k ht) t ht
      convert hle.trans (mul_le_mul_of_nonneg_left (hσdist k t ht) hM) using 1
      · exact (dist_eq_norm _ _).symm
      · rfl
    · intro k t ht
      change ξ + (∫ r in s..t, f (σ k r, delayedPicard f s (δ k) ξ k (σ k r))) =
        ξ + (∫ r in s..t, f (σ k r, delayedPicard f s (δ k) ξ (k+1) (σ k r)))
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ J := by
        rw [uIcc_of_le ht.1] at hr
        exact ⟨hr.1, hr.2.trans ht.2⟩
      have hσle : σ k r ≤ s + (k:ℝ)*δ k := by
        apply max_le
        · have hn : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
          have hd := (hδpos k).le
          nlinarith
        · have he := hδeq k
          nlinarith [hr'.2]
      exact congrArg (fun z => f (σ k r, z))
        (delayedPicard_stable f s h (δ k) ξ (hδpos k).le k _ (hσmap k hr') hσle).symm

/-- The left-hand box theorem by reversing time. -/
theorem peano_left : Specs.D13Unified.Ch03.Peano.leftExpected := by
  intro E _ _ _ f s a b M h ξ hf hbound hM hh ha hb
  let g : ℝ × E → E := fun p => -f (-p.1, p.2)
  have hmap : MapsTo (fun p : ℝ × E => (-p.1, p.2))
      (Icc (-s) (-s+a) ×ˢ closedBall ξ b)
      (Icc (s-a) s ×ˢ closedBall ξ b) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨⟨by dsimp at ht ⊢; linarith [ht.2], by dsimp at ht ⊢; linarith [ht.1]⟩, hy⟩
  have hg : ContinuousOn g (Icc (-s) (-s+a) ×ˢ closedBall ξ b) :=
    (hf.comp (continuousOn_fst.neg.prodMk continuousOn_snd) hmap).neg
  obtain ⟨y, hy, hys, hyb, hyd⟩ := peano_right g (-s) a b M h ξ hg
    (fun p hp => by simpa [g] using hbound _ (hmap hp)) hM hh ha hb
  have hmapt : MapsTo (fun t : ℝ => -t) (Icc (s-h) s) (Icc (-s) (-s+h)) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨fun t => y (-t), hy.comp continuousOn_id.neg hmapt, ?_,
    fun t ht => hyb _ (hmapt ht), ?_⟩
  · exact hys
  · intro t ht
    have hd := (hyd (-t) (hmapt ht)).scomp t
      ((hasDerivAt_id t).neg.hasDerivWithinAt) hmapt
    simpa [g, Function.comp_def] using hd

/-- Right-hand Peano existence using the shared endpoint-aware IVP predicate. -/
theorem peano_right_ivp : Specs.D13Unified.Ch03.Peano.rightODEExpected := by
  intro E _ _ _ F s a b M h ξ hbox hbound hM hh ha hb
  obtain ⟨x, hx, hxs, hxb, hxd⟩ := peano_right (fun p => F.eval p.1 p.2) s a b M h ξ
    (F.continuousOn_eval.mono hbox) hbound hM hh ha hb
  refine ⟨x, ⟨⟨hx, ?_, hxd⟩, ⟨le_rfl, by linarith⟩, hxs⟩, hxb⟩
  intro t ht
  exact hbox ⟨⟨ht.1, ht.2.trans (by linarith)⟩, hxb t ht⟩

/-- Left-hand Peano existence using the same IVP and endpoint conventions. -/
theorem peano_left_ivp : Specs.D13Unified.Ch03.Peano.leftODEExpected := by
  intro E _ _ _ F s a b M h ξ hbox hbound hM hh ha hb
  obtain ⟨x, hx, hxs, hxb, hxd⟩ := peano_left (fun p => F.eval p.1 p.2) s a b M h ξ
    (F.continuousOn_eval.mono hbox) hbound hM hh ha hb
  refine ⟨x, ⟨⟨hx, ?_, hxd⟩, ⟨by linarith, le_rfl⟩, hxs⟩, hxb⟩
  intro t ht
  exact hbox ⟨⟨by linarith [ht.1], ht.2⟩, hxb t ht⟩

/-- Two-sided classical existence in an arbitrary open box. -/
theorem peano_local : Specs.D13Unified.Ch03.Peano.localExpected := by
  intro E _ _ _ F s ξ hp
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (F.isOpen_domain.mem_nhds hp)
  let a := δ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  let Q := Icc (s-a) (s+a) ×ˢ closedBall ξ a
  have hQ : Q ⊆ F.domain := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    apply hδU
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq, abs_lt]
      dsimp [a] at ht
      constructor <;> linarith [ht.1, ht.2]
    · exact lt_of_le_of_lt hz (by dsimp [a]; linarith)
  let f : ℝ × E → E := fun p => F.eval p.1 p.2
  have hf : ContinuousOn f Q := F.continuousOn_eval.mono hQ
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall ξ a)).exists_bound_of_continuousOn hf
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMp : 0 < M+1 := by linarith
  let h := min a (a / (M+1))
  have hh : 0 < h := lt_min ha (div_pos ha hMp)
  have hha : h ≤ a := min_le_left _ _
  have hhb : M*h ≤ a := by
    have hmul : h*(M+1) ≤ a := (le_div_iff₀ hMp).mp (min_le_right _ _)
    nlinarith
  have hright : Icc s (s+a) ×ˢ closedBall ξ a ⊆ Q := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    exact ⟨⟨by linarith [ht.1], ht.2⟩,hz⟩
  have hleft : Icc (s-a) s ×ˢ closedBall ξ a ⊆ Q := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    exact ⟨⟨ht.1, by linarith [ht.2]⟩,hz⟩
  have hbound : ∀ p ∈ Q, ‖f p‖ ≤ M := fun p hp => (hC p hp).trans (le_max_left _ _)
  obtain ⟨x, hx, hxs, hxb, hxd⟩ := peano_left f s a a M h ξ
    (hf.mono hleft) (fun p hp => hbound p (hleft hp)) hM hh hha hhb
  obtain ⟨y, hy, hys, hyb, hyd⟩ := peano_right f s a a M h ξ
    (hf.mono hright) (fun p hp => hbound p (hright hp)) hM hh hha hhb
  let L := TimeInterval.closed (s-h) s (by linarith)
  let R := TimeInterval.closed s (s+h) (by linarith)
  have hsL : s ∈ L.carrier := ⟨by linarith, le_rfl⟩
  have hsR : s ∈ R.carrier := ⟨le_rfl, by linarith⟩
  have hxF : IsSolutionOn F L x := by
    refine ⟨hx, ?_, hxd⟩
    intro t ht
    apply hQ
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hxb t ht⟩
  have hyF : IsSolutionOn F R y := by
    refine ⟨hy, ?_, hyd⟩
    intro t ht
    apply hQ
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hyb t ht⟩
  have hxy : EqOn x y (L.carrier ∩ R.carrier) := by
    intro t ht
    have hts : t = s := le_antisymm ht.1.2 ht.2.1
    rw [hts, hxs, hys]
  obtain ⟨hz, hzx, _⟩ := compatible_pasting F L R x y ⟨s, hsL, hsR⟩ hxF hyF hxy
  refine ⟨h, hh, pasteCurves L.carrier x y, ?_⟩
  refine ⟨?_, ⟨by linarith, by linarith⟩, (hzx hsL).trans hxs⟩
  apply (classical_iff_solutionOn F _ _).mpr
  apply solutionOn_restrict F (L.union R ⟨s, hsL, hsR⟩) _ _ _ hz
  intro t ht
  rcases le_total t s with hts | hst
  · exact Or.inl ⟨ht.1.le, hts⟩
  · exact Or.inr ⟨hst, ht.2.le⟩

end D13Unified.Ch03
