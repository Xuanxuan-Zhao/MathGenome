import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.MonotoneLimits

/-! One-sided bounds, finite interior limits, extended endpoint limits, jumps,
and countability for monotone functions (K03.03.monotone_limits). -/

namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

/-- The LUB of all values to the left is the relative left limit. This lemma
also applies to extended reals and to the order dual of the codomain. -/
theorem monotoneOn_tendsto_left_of_isLUB
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : ℝ → β} {I : Set ℝ} {a : ℝ} {L : β}
    (hf : MonotoneOn f I) (hL : IsLUB (f '' (I ∩ Iio a)) L) :
    Tendsto f (𝓝[I ∩ Iio a] a) (𝓝 L) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨_, ⟨t, ht, rfl⟩, hlt⟩ := (lt_isLUB_iff hL).mp hl
    have hn : ∀ᶠ z in 𝓝[I ∩ Iio a] a, t < z :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.2)
    filter_upwards [hn, self_mem_nhdsWithin] with z hz hIz
    exact hlt.trans_le (hf ht.1 hIz.1 hz.le)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hL.1 (mem_image_of_mem f hz)).trans_lt hu

/-- Right-hand counterpart, proved by the GLB approximation property. -/
theorem monotoneOn_tendsto_right_of_isGLB
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : ℝ → β} {I : Set ℝ} {a : ℝ} {L : β}
    (hf : MonotoneOn f I) (hL : IsGLB (f '' (I ∩ Ioi a)) L) :
    Tendsto f (𝓝[I ∩ Ioi a] a) (𝓝 L) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hl.trans_le (hL.1 (mem_image_of_mem f hz))
  · obtain ⟨_, ⟨t, ht, rfl⟩, htu⟩ := (isGLB_lt_iff hL).mp hu
    have hn : ∀ᶠ z in 𝓝[I ∩ Ioi a] a, z < t :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)
    filter_upwards [hn, self_mem_nhdsWithin] with z hz hIz
    exact (hf hIz.1 ht.1 hz.le).trans_lt htu

/-- The same supremum argument for the upper infinite endpoint. -/
theorem monotoneOn_tendsto_atTop_of_isLUB
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : ℝ → β} {I : Set ℝ} {L : β}
    (hf : MonotoneOn f I) (hL : IsLUB (f '' I) L) :
    Tendsto f (atTop ⊓ 𝓟 I) (𝓝 L) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨_, ⟨t, ht, rfl⟩, hlt⟩ := (lt_isLUB_iff hL).mp hl
    have hn : ∀ᶠ z in (atTop ⊓ 𝓟 I : Filter ℝ), t ≤ z :=
      (eventually_ge_atTop t).filter_mono inf_le_left
    have hI : ∀ᶠ z in (atTop ⊓ 𝓟 I : Filter ℝ), z ∈ I :=
      (eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
    filter_upwards [hn, hI] with z hz hIz
    exact hlt.trans_le (hf ht hIz hz)
  · have hI : ∀ᶠ z in (atTop ⊓ 𝓟 I : Filter ℝ), z ∈ I :=
      (eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
    filter_upwards [hI] with z hz
    exact (hL.1 (mem_image_of_mem f hz)).trans_lt hu

/-- The infimum argument at the lower infinite endpoint. -/
theorem monotoneOn_tendsto_atBot_of_isGLB
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : ℝ → β} {I : Set ℝ} {L : β}
    (hf : MonotoneOn f I) (hL : IsGLB (f '' I) L) :
    Tendsto f (atBot ⊓ 𝓟 I) (𝓝 L) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have hI : ∀ᶠ z in (atBot ⊓ 𝓟 I : Filter ℝ), z ∈ I :=
      (eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
    filter_upwards [hI] with z hz
    exact hl.trans_le (hL.1 (mem_image_of_mem f hz))
  · obtain ⟨_, ⟨t, ht, rfl⟩, htu⟩ := (isGLB_lt_iff hL).mp hu
    have hn : ∀ᶠ z in (atBot ⊓ 𝓟 I : Filter ℝ), z ≤ t :=
      (eventually_le_atBot t).filter_mono inf_le_left
    have hI : ∀ᶠ z in (atBot ⊓ 𝓟 I : Filter ℝ), z ∈ I :=
      (eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
    filter_upwards [hn, hI] with z hz hIz
    exact (hf hIz ht hz).trans_lt htu

/-- Interior points have genuine approaches on both sides. -/
theorem interior_side_accumulation {I : Set ℝ} {a : ℝ} (ha : a ∈ interior I) :
    LeftAccumulation I a ∧ RightAccumulation I a := by
  obtain ⟨l, u, ⟨hla, hau⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp ha)
  constructor
  · intro δ hδ
    let d := min (a - l) δ / 2
    have hd : 0 < d := half_pos (lt_min (sub_pos.mpr hla) hδ)
    have hd₁ : d < a - l := (half_lt_self (lt_min (sub_pos.mpr hla) hδ)).trans_le
      (min_le_left _ _)
    have hd₂ : d < δ := (half_lt_self (lt_min (sub_pos.mpr hla) hδ)).trans_le
      (min_le_right _ _)
    refine ⟨a - d, hsub ⟨by linarith, by linarith⟩, ?_⟩
    change a - δ < a - d ∧ a - d < a
    constructor <;> linarith
  · intro δ hδ
    let d := min (u - a) δ / 2
    have hd : 0 < d := half_pos (lt_min (sub_pos.mpr hau) hδ)
    have hd₁ : d < u - a := (half_lt_self (lt_min (sub_pos.mpr hau) hδ)).trans_le
      (min_le_left _ _)
    have hd₂ : d < δ := (half_lt_self (lt_min (sub_pos.mpr hau) hδ)).trans_le
      (min_le_right _ _)
    refine ⟨a + d, hsub ⟨by linarith, by linarith⟩, ?_⟩
    change a < a + d ∧ a + d < a + δ
    constructor <;> linarith

/-- Explicit bridge between the accepted left-limit predicate and topology. -/
theorem leftRelativeLimit_filter_iff {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (I : Set ℝ) (a : ℝ) (L : Y) :
    LeftRelativeLimit f I a L ↔ LeftAccumulation I a ∧
      Tendsto f (𝓝[I ∩ Iio a] a) (𝓝 L) := by
  rw [leftRelativeLimit_iff, Metric.tendsto_nhdsWithin_nhds]
  apply and_congr_right
  intro _
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun t ht hd => hb t ht.1 ?_ ht.2⟩
    have := (abs_lt.mp (show |t - a| < δ from hd)).1
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun t ht hlow hhigh => hb ⟨ht, hhigh⟩ ?_⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hhigh)]
    linarith

/-- Explicit bridge between the accepted right-limit predicate and topology. -/
theorem rightRelativeLimit_filter_iff {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (I : Set ℝ) (a : ℝ) (L : Y) :
    RightRelativeLimit f I a L ↔ RightAccumulation I a ∧
      Tendsto f (𝓝[I ∩ Ioi a] a) (𝓝 L) := by
  rw [rightRelativeLimit_iff, Metric.tendsto_nhdsWithin_nhds]
  apply and_congr_right
  intro _
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun t ht hd => hb t ht.1 ht.2 ?_⟩
    have := (abs_lt.mp (show |t - a| < δ from hd)).2
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, fun t ht hlow hhigh => hb ⟨ht, hlow⟩ ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hlow)]
    linarith

/-- Nonemptiness and bounds are proved, rather than inferred from the total
real sSup/sInf operations. The statement also supplies the decreasing dual. -/
theorem monotoneOn_interior_bounds {β : Type*} [ConditionallyCompleteLinearOrder β]
    {f : ℝ → β} {I : Set ℝ} {a : ℝ} (hf : MonotoneOn f I)
    (ha : a ∈ interior I) :
    IsLUB (f '' (I ∩ Iio a)) (sSup (f '' (I ∩ Iio a))) ∧
    IsGLB (f '' (I ∩ Ioi a)) (sInf (f '' (I ∩ Ioi a))) ∧
    sSup (f '' (I ∩ Iio a)) ≤ f a ∧ f a ≤ sInf (f '' (I ∩ Ioi a)) := by
  have haI : a ∈ I := interior_subset ha
  obtain ⟨hl, hr⟩ := interior_side_accumulation ha
  obtain ⟨l, hlI, hla⟩ := hl 1 zero_lt_one
  obtain ⟨r, hrI, har⟩ := hr 1 zero_lt_one
  have hneL : (f '' (I ∩ Iio a)).Nonempty :=
    ⟨f l, mem_image_of_mem f ⟨hlI, hla.2⟩⟩
  have hneR : (f '' (I ∩ Ioi a)).Nonempty :=
    ⟨f r, mem_image_of_mem f ⟨hrI, har.1⟩⟩
  have hbL : f a ∈ upperBounds (f '' (I ∩ Iio a)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hf ht.1 haI ht.2.le
  have hbR : f a ∈ lowerBounds (f '' (I ∩ Ioi a)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hf haI ht.1 ht.2.le
  exact ⟨isLUB_csSup hneL ⟨f a, hbL⟩, isGLB_csInf hneR ⟨f a, hbR⟩,
    csSup_le hneL hbL, le_csInf hneR hbR⟩

theorem monotone_interior_limits :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.increasingInterior := by
  intro f I _ hf a ha
  obtain ⟨hL, hR, hLf, hfR⟩ := monotoneOn_interior_bounds hf ha
  obtain ⟨hl, hr⟩ := interior_side_accumulation ha
  exact ⟨hL, hR,
    (leftRelativeLimit_filter_iff _ _ _ _).mpr
      ⟨hl, monotoneOn_tendsto_left_of_isLUB hf hL⟩,
    (rightRelativeLimit_filter_iff _ _ _ _).mpr
      ⟨hr, monotoneOn_tendsto_right_of_isGLB hf hR⟩, hLf, hfR⟩

theorem antitone_interior_limits :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.decreasingInterior := by
  intro f I _ hf a ha
  obtain ⟨hL, hR, hLf, hfR⟩ := monotoneOn_interior_bounds (β := ℝᵒᵈ) hf ha
  obtain ⟨hl, hr⟩ := interior_side_accumulation ha
  exact ⟨hL, hR,
    (leftRelativeLimit_filter_iff _ _ _ _).mpr
      ⟨hl, monotoneOn_tendsto_left_of_isLUB (β := ℝᵒᵈ) hf hL⟩,
    (rightRelativeLimit_filter_iff _ _ _ _).mpr
      ⟨hr, monotoneOn_tendsto_right_of_isGLB (β := ℝᵒᵈ) hf hR⟩, hLf, hfR⟩

theorem monotone_extended_limits :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.increasingExtended := by
  intro f I _ hf
  have h : MonotoneOn (fun t => (f t : EReal)) I :=
    fun _ hx _ hy hxy => EReal.coe_le_coe (hf hx hy hxy)
  exact ⟨fun a _ => monotoneOn_tendsto_left_of_isLUB h (isLUB_sSup _),
    fun a _ => monotoneOn_tendsto_right_of_isGLB h (isGLB_sInf _),
    fun _ => monotoneOn_tendsto_atTop_of_isLUB h (isLUB_sSup _),
    fun _ => monotoneOn_tendsto_atBot_of_isGLB h (isGLB_sInf _)⟩

theorem antitone_extended_limits :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.decreasingExtended := by
  intro f I _ hf
  have h : MonotoneOn (fun t => OrderDual.toDual (f t : EReal)) I :=
    fun _ hx _ hy hxy => EReal.coe_le_coe (hf hx hy hxy)
  exact ⟨fun a _ => monotoneOn_tendsto_left_of_isLUB (β := ERealᵒᵈ) h (isLUB_sSup _),
    fun a _ => monotoneOn_tendsto_right_of_isGLB (β := ERealᵒᵈ) h (isGLB_sInf _),
    fun _ => monotoneOn_tendsto_atTop_of_isLUB (β := ERealᵒᵈ) h (isLUB_sSup _),
    fun _ => monotoneOn_tendsto_atBot_of_isGLB (β := ERealᵒᵈ) h (isGLB_sInf _)⟩

/-- Removing the center only makes the filter smaller, so the accepted
accumulation predicate guarantees a nontrivial side filter. -/
theorem sideFilter_neBot_of_accumulation {S : Set ℝ} {a : ℝ}
    (ha : DomainAccumulation S a) : (𝓝[S] a).NeBot := by
  have hn := (domainAccumulation_filter_iff S a).mp ha
  exact hn.mono (nhdsWithin_mono a sdiff_subset)

/-- Continuity is equivalent to equality of the bounding finite side limits.
The order-dual instance yields exactly the decreasing jump criterion. -/
theorem monotoneOn_interior_jump_iff {β : Type*} [ConditionallyCompleteLinearOrder β]
    [TopologicalSpace β] [OrderTopology β] [T2Space β]
    {f : ℝ → β} {I : Set ℝ} {a : ℝ} (hf : MonotoneOn f I)
    (ha : a ∈ interior I) :
    ¬ ContinuousWithinAt f I a ↔
      sSup (f '' (I ∩ Iio a)) < sInf (f '' (I ∩ Ioi a)) := by
  obtain ⟨hL, hR, hLf, hfR⟩ := monotoneOn_interior_bounds hf ha
  have hl := monotoneOn_tendsto_left_of_isLUB hf hL
  have hr := monotoneOn_tendsto_right_of_isGLB hf hR
  have hC : ContinuousWithinAt f I a ↔
      sSup (f '' (I ∩ Iio a)) = sInf (f '' (I ∩ Ioi a)) := by
    constructor
    · intro hc
      obtain ⟨hla, hra⟩ := interior_side_accumulation ha
      have : (𝓝[I ∩ Iio a] a).NeBot := sideFilter_neBot_of_accumulation
        ((leftAccumulation_domain_iff I a).mp hla)
      have : (𝓝[I ∩ Ioi a] a).NeBot := sideFilter_neBot_of_accumulation
        ((rightAccumulation_domain_iff I a).mp hra)
      have heL := tendsto_nhds_unique hl (hc.mono inter_subset_left)
      have heR := tendsto_nhds_unique hr (hc.mono inter_subset_left)
      exact heL.trans heR.symm
    · intro he
      have heL : sSup (f '' (I ∩ Iio a)) = f a :=
        le_antisymm hLf (he ▸ hfR)
      have heR : sInf (f '' (I ∩ Ioi a)) = f a := he.symm.trans heL
      apply continuousWithinAt_iff_continuous_left'_right'.mpr
      constructor
      · simpa only [ContinuousWithinAt, heL] using hl
      · simpa only [ContinuousWithinAt, heR] using hr
  constructor
  · intro hn
    exact lt_of_le_of_ne (hLf.trans hfR) (fun he => hn (hC.mpr he))
  · intro hlt hc
    exact (ne_of_lt hlt) (hC.mp hc)

theorem monotone_interior_discontinuity_is_jump :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.increasingJump := by
  intro f I _ hf a ha
  exact monotoneOn_interior_jump_iff hf ha

theorem antitone_interior_discontinuity_is_jump :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.decreasingJump := by
  intro f I _ hf a ha
  exact monotoneOn_interior_jump_iff (β := ℝᵒᵈ) hf ha

/-- The library theorem is for monotonicity and continuity relative to I;
no extension outside the interval or endpoint continuity is assumed. -/
theorem monotone_countable_discontinuities :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.increasingCountable := by
  intro f I _ hf
  exact hf.countable_not_continuousWithinAt

theorem antitone_countable_discontinuities :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.decreasingCountable := by
  intro f I _ hf
  exact hf.countable_not_continuousWithinAt

/-- Every included noninterior point of an interval is one of its extremities. -/
theorem interval_noninterior_is_extremity {I : Set ℝ} (hI : I.OrdConnected)
    {x : ℝ} (hx : x ∈ I \ interior I) : IsLeast I x ∨ IsGreatest I x := by
  classical
  by_cases hl : ∀ t ∈ I, x ≤ t
  · exact Or.inl ⟨hx.1, hl⟩
  · push Not at hl
    obtain ⟨l, hlI, hlx⟩ := hl
    right
    refine ⟨hx.1, fun u hu => ?_⟩
    by_contra hux
    have hxu : x < u := lt_of_not_ge hux
    have hsub : Ioo l u ⊆ I := fun _ ht => hI.out hlI hu ⟨ht.1.le, ht.2.le⟩
    exact hx.2 (mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (Ioo_mem_nhds hlx hxu) hsub))

/-- Included endpoints add at most two points, including degenerate intervals. -/
theorem interval_included_endpoints :
    Specs.SingleVariableAnalysis.Ch03.MonotoneLimits.includedEndpoints := by
  intro I hI
  classical
  have hmin : ∃ a : ℝ, ∀ x, IsLeast I x → x = a := by
    by_cases h : ∃ a, IsLeast I a
    · obtain ⟨a, ha⟩ := h
      exact ⟨a, fun x hx => hx.unique ha⟩
    · exact ⟨0, fun x hx => (h ⟨x, hx⟩).elim⟩
  have hmax : ∃ b : ℝ, ∀ x, IsGreatest I x → x = b := by
    by_cases h : ∃ b, IsGreatest I b
    · obtain ⟨b, hb⟩ := h
      exact ⟨b, fun x hx => hx.unique hb⟩
    · exact ⟨0, fun x hx => (h ⟨x, hx⟩).elim⟩
  obtain ⟨a, ha⟩ := hmin
  obtain ⟨b, hb⟩ := hmax
  refine ⟨a, b, fun x hx => ?_⟩
  rcases interval_noninterior_is_extremity hI hx with h | h
  · simp only [mem_insert_iff, mem_singleton_iff]
    exact Or.inl (ha x h)
  · simp only [mem_insert_iff, mem_singleton_iff]
    exact Or.inr (hb x h)

end SingleVariableAnalysis
