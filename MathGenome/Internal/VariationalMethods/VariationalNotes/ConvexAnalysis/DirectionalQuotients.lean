import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.LocalLipschitz
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.DirectionalQuotients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis

def directionalQuotient {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) (t : ℝ) : EReal := Specs.directionalQuotient f x d t

def directionalDerivative {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) : EReal := Specs.directionalDerivative f x d

def realDirectionalDerivative {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) : ℝ := Specs.realDirectionalDerivative f x d

private lemma finite_eq {r : WithTop ℝ} (hr : r < ⊤) :
    r = ((r.untopD 0 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hr)
  rw [← hs, WithTop.untopD_coe]

lemma directionalQuotient_of_finite {E : Type u} [AddCommGroup E] [Module ℝ E]
    {f : E → WithTop ℝ} {x d : E} {t : ℝ} (h : f (x + t • d) < ⊤) :
    directionalQuotient f x d t =
      ((((f (x + t • d)).untopD 0 - (f x).untopD 0) / t : ℝ) : EReal) := by
  simp [directionalQuotient, Specs.directionalQuotient, ne_of_lt h]

theorem directionalQuotient_eq : Specs.directionalQuotient_eq.{u} := by
  intro E _ _ f x d hx t ht
  change directionalQuotient f x d t = _
  rw [finite_eq hx]
  by_cases h : f (x + t • d) = ⊤
  · change directionalQuotient f x d t =
      (Specs.toEReal (f (x + t • d)) - (((f x).untopD 0 : ℝ) : EReal)) * (t⁻¹ : ℝ)
    simp only [directionalQuotient, Specs.directionalQuotient, h]
    change ⊤ = (⊤ - (((f x).untopD 0 : ℝ) : EReal)) * (t⁻¹ : ℝ)
    rw [EReal.top_sub_coe, EReal.top_mul_coe_of_pos (inv_pos.mpr ht)]
  · have hfin : f (x + t • d) < ⊤ := lt_top_iff_ne_top.mpr h
    rw [directionalQuotient_of_finite hfin]
    rw [finite_eq hfin]
    rfl

theorem directionalQuotient_monotone : Specs.directionalQuotient_monotone.{u} := by
  intro E _ _ f _ hf x hx d t ht s hs hts
  change 0 < t at ht
  change 0 < s at hs
  change directionalQuotient f x d t ≤ directionalQuotient f x d s
  by_cases hsf : f (x + s • d) = ⊤
  · simp [directionalQuotient, Specs.directionalQuotient, hsf]
  have hsf' : f (x + s • d) < ⊤ := lt_top_iff_ne_top.mpr hsf
  have ha : 0 ≤ 1 - t / s := sub_nonneg.mpr ((div_le_one hs).mpr hts)
  have hb : 0 ≤ t / s := div_nonneg ht.le hs.le
  have hp : (1 - t / s) • x + (t / s) • (x + s • d) = x + t • d := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ (ne_of_gt hs)]
    module
  have h := convex_upper_bound hf (finite_eq hx).le (finite_eq hsf').le ha hb (by ring)
  rw [hp] at h
  have htf : f (x + t • d) < ⊤ := lt_of_le_of_lt h (WithTop.coe_lt_top _)
  rw [directionalQuotient_of_finite htf, directionalQuotient_of_finite hsf']
  apply EReal.coe_le_coe_iff.mpr
  have hv : (f (x + t • d)).untopD 0 ≤
      (1 - t / s) * (f x).untopD 0 + t / s * (f (x + s • d)).untopD 0 :=
    WithTop.coe_le_coe.mp ((WithTop.coe_untopD_le _ _).trans h)
  apply (div_le_div_iff₀ ht hs).mpr
  have hv' := mul_le_mul_of_nonneg_right hv hs.le
  have he : ((1 - t / s) * (f x).untopD 0 + t / s *
      (f (x + s • d)).untopD 0) * s =
      (s - t) * (f x).untopD 0 + t * (f (x + s • d)).untopD 0 := by
    field_simp [ne_of_gt hs]
  rw [he] at hv'
  nlinarith

theorem directionalQuotient_tendsto : Specs.directionalQuotient_tendsto.{u} := by
  intro E _ _ f hf hc x hx d
  have hm := directionalQuotient_monotone f hf hc x hx d
  change Tendsto (directionalQuotient f x d) (𝓝[>] 0)
    (𝓝 (⨅ t : {t : ℝ // 0 < t}, directionalQuotient f x d t))
  have heq : (⨅ t : {t : ℝ // 0 < t}, directionalQuotient f x d t) =
      sInf (directionalQuotient f x d '' Ioi 0) := by
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨t, ht, rfl⟩
      exact iInf_le (fun t : {t : ℝ // 0 < t} => directionalQuotient f x d t) ⟨t, ht⟩
    · apply le_iInf
      intro t
      exact sInf_le ⟨t, t.property, rfl⟩
  rw [heq]
  exact hm.tendsto_nhdsGT (OrderBot.bddBelow _)

/-- Real quotient; used only at finite points of the ray. -/
def realDirectionalQuotient {E : Type u} [AddCommGroup E] [Module ℝ E]
    (f : E → WithTop ℝ) (x d : E) (t : ℝ) : ℝ :=
  ((f (x + t • d)).untopD 0 - (f x).untopD 0) / t

private lemma ray_eventually_mem {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {U : Set E} (hU : U ∈ 𝓝 x) (d : E) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • d ∈ U := by
  have hcont : Continuous (fun t : ℝ => x + t • d) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h' : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  exact (h'.mono_left nhdsWithin_le_nhds).eventually hU

private lemma quotient_difference_bound {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → WithTop ℝ} {x : E} {U : Set E} {K : NNReal}
    (hLip : LipschitzOnWith K (fun y => (f y).untopD 0) U)
    {d e : E} {t : ℝ} (ht : 0 < t) (hd : x + t • d ∈ U) (he : x + t • e ∈ U) :
    |realDirectionalQuotient f x d t - realDirectionalQuotient f x e t| ≤
      (K : ℝ) * ‖d - e‖ := by
  have h := hLip.dist_le_mul _ hd _ he
  rw [Real.dist_eq, dist_eq_norm] at h
  have hp : (x + t • d) - (x + t • e) = t • (d - e) := by module
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
  have hq : realDirectionalQuotient f x d t - realDirectionalQuotient f x e t =
      ((f (x + t • d)).untopD 0 - (f (x + t • e)).untopD 0) / t := by
    unfold realDirectionalQuotient
    ring
  rw [hq, abs_div, abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr (by nlinarith [h])

private lemma quotient_bound {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → WithTop ℝ} {x : E} {U : Set E} {K : NNReal}
    (hU : U ∈ 𝓝 x) (hLip : LipschitzOnWith K (fun y => (f y).untopD 0) U) (d : E) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, |realDirectionalQuotient f x d t| ≤ (K : ℝ) * ‖d‖ := by
  filter_upwards [ray_eventually_mem hU d, self_mem_nhdsWithin] with t hd ht
  have h := quotient_difference_bound hLip ht hd
    (show x + t • (0 : E) ∈ U by simpa using mem_of_mem_nhds hU)
  simpa [realDirectionalQuotient] using h

lemma directionalDerivative_finite_of_localLipschitz {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → WithTop ℝ} (hf : Proper f) (hc : IsConvex f)
    {x : E} {U : Set E} {K : NNReal} (hU : U ∈ 𝓝 x)
    (hfin : ∀ y ∈ U, f y < ⊤)
    (hLip : LipschitzOnWith K (fun y => (f y).untopD 0) U) (d : E) :
    directionalDerivative f x d = (realDirectionalDerivative f x d : EReal) := by
  have hx := hfin x (mem_of_mem_nhds hU)
  have hlim := directionalQuotient_tendsto f hf hc x hx d
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (((-(K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ directionalQuotient f x d t ∧
      directionalQuotient f x d t ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal) := by
    filter_upwards [quotient_bound hU hLip d, ray_eventually_mem hU d] with t ht htd
    rw [directionalQuotient_of_finite (hfin _ htd)]
    have h := abs_le.mp ht
    exact ⟨EReal.coe_le_coe_iff.mpr (by simpa [realDirectionalQuotient] using h.1),
      EReal.coe_le_coe_iff.mpr h.2⟩
  have hl := ge_of_tendsto hlim (hb.mono fun _ h => h.1)
  have hu := le_of_tendsto hlim (hb.mono fun _ h => h.2)
  exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hu)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl)).symm

lemma realDirectionalQuotient_tendsto {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → WithTop ℝ} (hf : Proper f) (hc : IsConvex f)
    {x : E} {U : Set E} {K : NNReal} (hU : U ∈ 𝓝 x)
    (hfin : ∀ y ∈ U, f y < ⊤)
    (hLip : LipschitzOnWith K (fun y => (f y).untopD 0) U) (d : E) :
    Tendsto (realDirectionalQuotient f x d) (𝓝[>] 0) (𝓝 (realDirectionalDerivative f x d)) := by
  have hlim := directionalQuotient_tendsto f hf hc x (hfin x (mem_of_mem_nhds hU)) d
  have heq := directionalDerivative_finite_of_localLipschitz hf hc hU hfin hLip d
  change Tendsto (directionalQuotient f x d) _ (𝓝 (directionalDerivative f x d)) at hlim
  rw [heq] at hlim
  apply EReal.tendsto_coe.mp
  apply hlim.congr'
  filter_upwards [ray_eventually_mem hU d] with t ht
  exact directionalQuotient_of_finite (hfin _ ht)

private lemma tendsto_positive_mul (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => a * t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun t : ℝ => a * t) (𝓝 0) (𝓝 (a * 0)) :=
      continuous_const.mul continuous_id |>.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ha ht

theorem directionalDerivative_of_localLipschitz :
    Specs.directionalDerivative_of_localLipschitz.{u} := by
  intro E _ _ f hf hc x U K hU hfin hLip
  have hlim := realDirectionalQuotient_tendsto hf hc hU hfin hLip
  have hzero : realDirectionalDerivative f x 0 = 0 := by
    apply tendsto_nhds_unique (hlim 0)
    have hz : realDirectionalQuotient f x (0 : E) = fun _ => 0 := by
      funext t
      simp [realDirectionalQuotient]
    rw [hz]
    exact tendsto_const_nhds
  have hlip : LipschitzWith K (realDirectionalDerivative f x) := by
    apply LipschitzWith.of_dist_le_mul
    intro d e
    rw [Real.dist_eq, dist_eq_norm]
    apply le_of_tendsto ((hlim d).sub (hlim e)).abs
    filter_upwards [ray_eventually_mem hU d, ray_eventually_mem hU e,
      self_mem_nhdsWithin] with t hd he ht
    exact quotient_difference_bound hLip ht hd he
  have hhom : ∀ a : ℝ, 0 ≤ a → ∀ d,
      realDirectionalDerivative f x (a • d) = a * realDirectionalDerivative f x d := by
    intro a ha d
    rcases eq_or_lt_of_le ha with rfl | ha
    · simp [hzero]
    apply tendsto_nhds_unique (hlim (a • d))
    have h : Tendsto (fun t : ℝ => a * realDirectionalQuotient f x d (a * t))
        (𝓝[>] 0) (𝓝 (a * realDirectionalDerivative f x d)) :=
      tendsto_const_nhds.mul ((hlim d).comp (tendsto_positive_mul a ha))
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    unfold realDirectionalQuotient
    rw [smul_smul, mul_comm t a]
    field_simp [ne_of_gt ha, ne_of_gt (show 0 < t from ht)]
  have hadd : ∀ d e,
      realDirectionalDerivative f x (d + e) ≤
        realDirectionalDerivative f x d + realDirectionalDerivative f x e := by
    intro d e
    have hsum := ((hlim d).comp (tendsto_positive_mul 2 (by norm_num))).add
      ((hlim e).comp (tendsto_positive_mul 2 (by norm_num)))
    apply le_of_tendsto_of_tendsto (hlim (d + e)) hsum
    have hd : ∀ᶠ t : ℝ in 𝓝[>] 0, x + (2 * t) • d ∈ U := by
      simpa [smul_smul, mul_comm] using ray_eventually_mem hU ((2 : ℝ) • d)
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, x + (2 * t) • e ∈ U := by
      simpa [smul_smul, mul_comm] using ray_eventually_mem hU ((2 : ℝ) • e)
    filter_upwards [hd, he, self_mem_nhdsWithin] with t hd he ht
    have hp : (1/2 : ℝ) • (x + (2*t) • d) + (1/2 : ℝ) • (x + (2*t) • e) =
        x + t • (d + e) := by module
    have hv := convex_upper_bound hc (finite_eq (hfin _ hd)).le (finite_eq (hfin _ he)).le
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
    rw [hp] at hv
    have hv' : (f (x + t • (d + e))).untopD 0 ≤
        1/2 * (f (x + (2*t) • d)).untopD 0 + 1/2 * (f (x + (2*t) • e)).untopD 0 :=
      WithTop.coe_le_coe.mp ((WithTop.coe_untopD_le _ _).trans hv)
    change 0 < t at ht
    dsimp only [Function.comp_def]
    unfold realDirectionalQuotient
    apply (div_le_iff₀ ht).mpr
    have hcancel : (((f (x + (2*t) • d)).untopD 0 - (f x).untopD 0) / (2*t) +
        ((f (x + (2*t) • e)).untopD 0 - (f x).untopD 0) / (2*t)) * t =
        1/2 * (f (x + (2*t) • d)).untopD 0 + 1/2 * (f (x + (2*t) • e)).untopD 0 -
          (f x).untopD 0 := by
      field_simp [ne_of_gt ht]
      ring
    rw [hcancel]
    linarith
  refine ⟨directionalDerivative_finite_of_localLipschitz hf hc hU hfin hLip,
    hlip, hzero, hhom, hadd, ?_⟩
  intro d
  have h := hlip.dist_le_mul d 0
  change |realDirectionalDerivative f x d| ≤ (K : ℝ) * ‖d‖
  simpa [Real.dist_eq, dist_eq_norm, hzero] using h

theorem directionalDerivative_continuous_sublinear :
    Specs.directionalDerivative_continuous_sublinear.{u} := by
  intro E _ _ f hf hc x hnear
  obtain ⟨V, hV, hfin, hcont⟩ := hnear
  have hxV := mem_of_mem_nhds hV
  have hct : ContinuousAt (fun y => (f y).untopD 0) x :=
    (hcont x hxV).continuousAt hV
  have hbound : ∀ᶠ y in 𝓝 x, (f y).untopD 0 < (f x).untopD 0 + 1 :=
    hct.eventually (Iio_mem_nhds (by linarith))
  have hM : ∃ M : ℝ, ∀ᶠ y in 𝓝 x, f y ≤ (M : WithTop ℝ) := by
    refine ⟨(f x).untopD 0 + 1, ?_⟩
    filter_upwards [hV, hbound] with y hy hb
    rw [finite_eq (hfin y hy)]
    exact WithTop.coe_le_coe.mpr hb.le
  obtain ⟨U, hU, K, hUfin, hLip⟩ := localLipschitz_of_boundedAbove f hf hc x hM
  have h := directionalDerivative_of_localLipschitz f hf hc x U K hU hUfin hLip
  exact ⟨h.1, h.2.1.continuous, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    U, hU, K, hUfin, hLip, h.2.2.2.2.2⟩

end VariationalNotes.ConvexAnalysis
