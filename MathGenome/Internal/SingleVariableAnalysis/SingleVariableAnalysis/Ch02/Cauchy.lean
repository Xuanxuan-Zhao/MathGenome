import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The Cauchy criterion for finite relative limits

K03.02.cauchy, paper.tex:409–419. The completeness step uses Mathlib's
`cauchy_map_iff_exists_tendsto`. Complex completeness is obtained from the
upstream scalar sequence criterion, rather than added as a hypothesis.
The basis lemma keeps both tested points in the same approach neighborhood.
Finite-point domains may themselves be real or complex metric subdomains.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology

universe u v w

private theorem complex_completeSpace : CompleteSpace ℂ := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro z hz
  obtain ⟨L, hL⟩ := (complex_cauchy_criterion z).mpr (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hz ε hε
    exact ⟨N, fun m hm n hn => by
      simpa only [dist_eq_norm] using hN n hn m hm⟩)
  exact ⟨L, (complexSequenceConverges_iff z L).mp hL⟩

attribute [local instance] complex_completeSpace

/-- In a complete metric target, small pairwise distances on basis sets
characterize existence of a finite limit. Nontriviality is essential. -/
theorem exists_limit_iff_cauchy_on_basis {X : Type u} {Y : Type v} {ι : Type w}
    [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (l : Filter X) [l.NeBot]
    {p : ι → Prop} {s : ι → Set X} (hb : l.HasBasis p s) :
    (∃ L : Y, Tendsto f l (𝓝 L)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ i, p i ∧
        ∀ x ∈ s i, ∀ y ∈ s i, dist (f x) (f y) < ε := by
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  constructor
  · rintro ⟨_, h⟩ ε hε
    obtain ⟨t, ht, hd⟩ := h ε hε
    obtain ⟨i, hi, hs⟩ := hb.mem_iff.mp ht
    exact ⟨i, hi, fun x hx y hy => hd (f x) (hs hx) (f y) (hs hy)⟩
  · intro h
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨i, hi, hd⟩ := h ε hε
    refine ⟨f '' s i, ?_, ?_⟩
    · exact hb.mem_iff.mpr ⟨i, hi, fun x hx => ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hd x hx y hy

/-- The metric version includes all four real/complex domain/target choices. -/
theorem relativePuncturedLimit_cauchy_criterion {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    (f : X → Y) (E : Set X) (a : X) (ha : DomainAccumulation E a) :
    (∃ L : Y, RelativePuncturedLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < dist x a → dist x a < δ →
          0 < dist y a → dist y a < δ → dist (f x) (f y) < ε := by
  have : (PuncturedDomainFilter E a).NeBot := (domainAccumulation_filter_iff E a).mp ha
  rw [show (∃ L : Y, RelativePuncturedLimit f E a L) ↔
      ∃ L : Y, Tendsto f (PuncturedDomainFilter E a) (𝓝 L) from
    exists_congr (relativePuncturedLimit_filter_iff f E a)]
  have hb : (PuncturedDomainFilter E a).HasBasis (fun δ : ℝ => 0 < δ)
      (fun δ => Metric.ball a δ ∩ (E \ {a})) := Metric.nhdsWithin_basis_ball
  rw [exists_limit_iff_cauchy_on_basis f _ hb]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx y hy hxp hxd hyp hyd => ?_⟩
    exact hd x ⟨hxd, hx, by simpa using dist_pos.mp hxp⟩
      y ⟨hyd, hy, by simpa using dist_pos.mp hyp⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx y hy => ?_⟩
    exact hd x hx.2.1 y hy.2.1
      (dist_pos.mpr (by simpa using hx.2.2)) hx.1
      (dist_pos.mpr (by simpa using hy.2.2)) hy.1

private theorem approach_isBasis (E : Set ℝ) (q : RealApproach) :
    Filter.IsBasis (fun r : ℝ => 0 < r) (fun r => E ∩ ApproachRegion q r) := by
  refine ⟨⟨1, zero_lt_one⟩, ?_⟩
  intro r t hr ht
  cases q with
  | punctured a =>
    refine ⟨min r t, lt_min hr ht, ?_⟩
    rintro x ⟨hx, hp, hd⟩
    exact ⟨⟨hx, hp, lt_of_lt_of_le hd (min_le_left _ _)⟩,
      ⟨hx, hp, lt_of_lt_of_le hd (min_le_right _ _)⟩⟩
  | right a =>
    refine ⟨min r t, lt_min hr ht, ?_⟩
    rintro x ⟨hx, hp, hd⟩
    exact ⟨⟨hx, hp, by change x < a + r; linarith [min_le_left r t]⟩,
      ⟨hx, hp, by change x < a + t; linarith [min_le_right r t]⟩⟩
  | left a =>
    refine ⟨min r t, lt_min hr ht, ?_⟩
    rintro x ⟨hx, hd, hp⟩
    exact ⟨⟨hx, (sub_le_sub_left (min_le_left _ _) _).trans_lt hd, hp⟩,
      ⟨hx, (sub_le_sub_left (min_le_right _ _) _).trans_lt hd, hp⟩⟩
  | posInfinity =>
    refine ⟨max r t, lt_of_lt_of_le hr (le_max_left _ _), ?_⟩
    rintro x ⟨hx, hd⟩
    exact ⟨⟨hx, (le_max_left r t).trans_lt hd⟩,
      ⟨hx, (le_max_right r t).trans_lt hd⟩⟩
  | negInfinity =>
    refine ⟨max r t, lt_of_lt_of_le hr (le_max_left _ _), ?_⟩
    rintro x ⟨hx, hd⟩
    exact ⟨⟨hx, hd.trans_le (neg_le_neg (le_max_left r t))⟩,
      ⟨hx, hd.trans_le (neg_le_neg (le_max_right r t))⟩⟩

/-- Both finite sides and both infinite endpoints use the same basis argument.
The selected domain must meet every approach region. -/
theorem finiteApproachLimit_cauchy_criterion {Y : Type u}
    [MetricSpace Y] [CompleteSpace Y] (f : ℝ → Y) (E : Set ℝ)
    (q : RealApproach) (ha : ApproachNontrivial E q) :
    (∃ L : Y, FiniteApproachLimit f E q L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ E, ∀ y ∈ E, x ∈ ApproachRegion q r →
          y ∈ ApproachRegion q r → dist (f x) (f y) < ε := by
  let b := approach_isBasis E q
  have : b.filter.NeBot := b.hasBasis.neBot_iff.mpr (fun {r} hr => by
    obtain ⟨x, hx, hxr⟩ := ha r hr
    exact ⟨x, hx, hxr⟩)
  have hL (L : Y) : FiniteApproachLimit f E q L ↔ Tendsto f b.filter (𝓝 L) := by
    rw [b.hasBasis.tendsto_iff Metric.nhds_basis_ball]
    simp only [FiniteApproachLimit, ha, true_and, ApproachEventually,
      Set.mem_inter_iff, Metric.mem_ball, and_imp]
  rw [show (∃ L : Y, FiniteApproachLimit f E q L) ↔
      ∃ L : Y, Tendsto f b.filter (𝓝 L) from exists_congr hL,
    exists_limit_iff_cauchy_on_basis f _ b.hasBasis]
  constructor
  · intro h ε hε
    obtain ⟨r, hr, hd⟩ := h ε hε
    exact ⟨r, hr, fun x hx y hy hxr hyr => hd x ⟨hx, hxr⟩ y ⟨hy, hyr⟩⟩
  · intro h ε hε
    obtain ⟨r, hr, hd⟩ := h ε hε
    exact ⟨r, hr, fun x hx y hy => hd x hx.1 y hy.1 hx.2 hy.2⟩

theorem real_real_relativeLimit_cauchy_criterion :
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), DomainAccumulation E a →
    ((∃ L : ℝ, RelativePuncturedLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < |x - a| → |x - a| < δ →
          0 < |y - a| → |y - a| < δ → |f x - f y| < ε) := by
  intro f E a ha
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    relativePuncturedLimit_cauchy_criterion f E a ha

theorem real_complex_relativeLimit_cauchy_criterion :
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), DomainAccumulation E a →
    ((∃ L : ℂ, RelativePuncturedLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < |x - a| → |x - a| < δ →
          0 < |y - a| → |y - a| < δ → ‖f x - f y‖ < ε) := by
  intro f E a ha
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    relativePuncturedLimit_cauchy_criterion f E a ha

theorem complex_real_relativeLimit_cauchy_criterion :
  ∀ (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ), DomainAccumulation E a →
    ((∃ L : ℝ, RelativePuncturedLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ →
          0 < ‖y - a‖ → ‖y - a‖ < δ → |f x - f y| < ε) := by
  intro f E a ha
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    relativePuncturedLimit_cauchy_criterion f E a ha

theorem complex_complex_relativeLimit_cauchy_criterion :
  ∀ (f : ℂ → ℂ) (E : Set ℂ) (a : ℂ), DomainAccumulation E a →
    ((∃ L : ℂ, RelativePuncturedLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ →
          0 < ‖y - a‖ → ‖y - a‖ < δ → ‖f x - f y‖ < ε) := by
  intro f E a ha
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    relativePuncturedLimit_cauchy_criterion f E a ha

theorem real_rightLimit_cauchy_criterion :
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), RightAccumulation E a →
    ((∃ L : ℝ, RightRelativeLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a < x → x < a + δ → a < y → y < a + δ → |f x - f y| < ε) := by
  intro f E a ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E (.right a) ha

theorem real_leftLimit_cauchy_criterion :
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), LeftAccumulation E a →
    ((∃ L : ℝ, LeftRelativeLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a - δ < x → x < a → a - δ < y → y < a → |f x - f y| < ε) := by
  intro f E a ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E (.left a) ha

theorem real_posInfinityLimit_cauchy_criterion :
  ∀ (f : ℝ → ℝ) (E : Set ℝ) , DomainUnboundedAbove E →
    ((∃ L : ℝ, LimitAtPosInfinity f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, A < x → A < y → |f x - f y| < ε) := by
  intro f E ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E .posInfinity ha

theorem real_negInfinityLimit_cauchy_criterion :
  ∀ (f : ℝ → ℝ) (E : Set ℝ) , DomainUnboundedBelow E →
    ((∃ L : ℝ, LimitAtNegInfinity f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, x < -A → y < -A → |f x - f y| < ε) := by
  intro f E ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E .negInfinity ha

theorem complex_rightLimit_cauchy_criterion :
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), RightAccumulation E a →
    ((∃ L : ℂ, RightRelativeLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a < x → x < a + δ → a < y → y < a + δ → ‖f x - f y‖ < ε) := by
  intro f E a ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E (.right a) ha

theorem complex_leftLimit_cauchy_criterion :
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), LeftAccumulation E a →
    ((∃ L : ℂ, LeftRelativeLimit f E a L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, a - δ < x → x < a → a - δ < y → y < a → ‖f x - f y‖ < ε) := by
  intro f E a ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E (.left a) ha

theorem complex_posInfinityLimit_cauchy_criterion :
  ∀ (f : ℝ → ℂ) (E : Set ℝ) , DomainUnboundedAbove E →
    ((∃ L : ℂ, LimitAtPosInfinity f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, A < x → A < y → ‖f x - f y‖ < ε) := by
  intro f E ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E .posInfinity ha

theorem complex_negInfinityLimit_cauchy_criterion :
  ∀ (f : ℝ → ℂ) (E : Set ℝ) , DomainUnboundedBelow E →
    ((∃ L : ℂ, LimitAtNegInfinity f E L) ↔
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
        ∀ x ∈ E, ∀ y ∈ E, x < -A → y < -A → ‖f x - f y‖ < ε) := by
  intro f E ha
  simpa only [RightRelativeLimit, LeftRelativeLimit, LimitAtPosInfinity,
    LimitAtNegInfinity, ApproachRegion, Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio,
    and_imp, dist_eq_norm, Real.norm_eq_abs] using
    finiteApproachLimit_cauchy_criterion f E .negInfinity ha

end SingleVariableAnalysis
