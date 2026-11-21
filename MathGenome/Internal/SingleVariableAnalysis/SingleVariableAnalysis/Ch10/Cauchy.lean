import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Cauchy

/-! Cauchy's criterion for one-sided improper Darboux integrals.
Proper splitting identifies tail values with differences of truncations.
Completeness is used only for the scalar limit of these truncations, via
the previously proved Cauchy criterion on a filter basis. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Cauchy
open Filter
open scoped Topology

/-- The truncation indices carry the ordinary real order. -/
noncomputable instance rightIndexLinearOrder (a : ℝ) (b : WithTop ℝ) :
    LinearOrder (RightIndex a b) :=
  inferInstanceAs (LinearOrder {t : ℝ // a < t ∧ (t : WithTop ℝ) < b})

noncomputable instance leftIndexLinearOrder (a : WithBot ℝ) (b : ℝ) :
    LinearOrder (LeftIndex a b) :=
  inferInstanceAs (LinearOrder {t : ℝ // a < (t : WithBot ℝ) ∧ t < b})

private theorem scalar_complete (k : ScalarKind) : CompleteSpace (S.scalarValue k) := by
  cases k with
  | real => exact inferInstanceAs (CompleteSpace ℝ)
  | complex => exact inferInstanceAs (CompleteSpace ℂ)

/-- The strict-tail Cauchy criterion in a complete metric space. Testing
ordered pairs suffices, since distances are symmetric and vanish on the diagonal. -/
theorem exists_cofinal_limit_iff {α Y : Type*} [LinearOrder α]
    [MetricSpace Y] [CompleteSpace Y] (H : α → Y)
    (hne : Nonempty α) (hmore : ∀ r : α, ∃ s, r < s) :
    (∃ L : Y, ∀ ε : ℝ, 0 < ε → ∃ r : α,
      ∀ t : α, r < t → dist (H t) L < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ u v : α,
      r < u → u < v → dist (H v) (H u) < ε) := by
  classical
  let B : Filter.IsBasis (fun _ : α => True) (fun r => {t : α | r < t}) := by
    refine ⟨⟨Classical.choice hne, trivial⟩, ?_⟩
    intro r s _ _
    exact ⟨max r s, trivial, fun t ht =>
      ⟨(le_max_left _ _).trans_lt ht, (le_max_right _ _).trans_lt ht⟩⟩
  have : B.filter.NeBot := B.hasBasis.neBot_iff.mpr (fun {r} _ => hmore r)
  have hL (L : Y) :
      (∀ ε : ℝ, 0 < ε → ∃ r : α, ∀ t : α, r < t → dist (H t) L < ε) ↔
      Tendsto H B.filter (𝓝 L) := by
    rw [B.hasBasis.tendsto_iff Metric.nhds_basis_ball]
    simp only [true_and, Set.mem_ofPred_eq, Metric.mem_ball]
  rw [show (∃ L : Y, ∀ ε : ℝ, 0 < ε → ∃ r : α,
      ∀ t : α, r < t → dist (H t) L < ε) ↔
      ∃ L : Y, Tendsto H B.filter (𝓝 L) from exists_congr hL,
    exists_limit_iff_cauchy_on_basis H _ B.hasBasis]
  constructor
  · intro h ε hε
    obtain ⟨r, _, hr⟩ := h ε hε
    exact ⟨r, fun u v hru huv => hr v (hru.trans huv) u hru⟩
  · intro h ε hε
    obtain ⟨r, hr⟩ := h ε hε
    refine ⟨r, trivial, fun u hu v hv => ?_⟩
    rcases lt_trichotomy u v with huv | rfl | hvu
    · simpa only [dist_comm] using hr u v hu huv
    · simpa only [dist_self] using hε
    · exact hr v u hv hvu

/-- Proper splitting for the common scalar interface. -/
theorem scalar_integral_split (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a u v : ℝ} (hau : a ≤ u) (huv : u ≤ v)
    (hav : I.scalarIntegrableValue k f a v)
    (ha_u : I.scalarIntegrableValue k f a u)
    (hu_v : I.scalarIntegrableValue k f u v) :
    I.scalarIntegralValue k f hav =
      I.scalarIntegralValue k f ha_u + I.scalarIntegralValue k f hu_v := by
  cases k with
  | real => exact (real_split f hau huv (RealIntegrable.bounded hav)).2 hav ha_u hu_v
  | complex => exact (complex_split f hau huv (ComplexIntegrable.norm_bound hav)).2 hav ha_u hu_v

/-- Restriction preserves proper scalar integrability, including endpoints. -/
theorem scalar_integrable_subinterval (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {L U u v : ℝ} (h : I.scalarIntegrableValue k f L U)
    (hLu : L ≤ u) (huv : u ≤ v) (hvU : v ≤ U) :
    I.scalarIntegrableValue k f u v := by
  cases k with
  | real => exact RealIntegrable.subinterval h hLu huv hvU
  | complex => exact ComplexIntegrable.subinterval h hLu huv hvU

/-- Every tail is a proper integral equal to the difference of right truncations. -/
theorem right_tail_difference (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (a : ℝ) (b : WithTop ℝ) (h : RightRegular k f a b)
    (u v : RightIndex a b) (huv : u.val < v.val) :
    ∃ ht : I.scalarIntegrableValue k f u.val v.val,
      I.scalarIntegralValue k f ht =
        RightTruncation k f a b h v - RightTruncation k f a b h u := by
  have ht := scalar_integrable_subinterval k f (h.2 v) u.property.1.le huv.le le_rfl
  refine ⟨ht, ?_⟩
  have heq := scalar_integral_split k f u.property.1.le huv.le (h.2 v) (h.2 u) ht
  change I.scalarIntegralValue k f ht =
    I.scalarIntegralValue k f (h.2 v) - I.scalarIntegralValue k f (h.2 u)
  rw [heq, add_sub_cancel_left]

/-- Left truncations run from the variable endpoint up to the regular endpoint. -/
theorem left_tail_difference (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (a : WithBot ℝ) (b : ℝ) (h : LeftRegular k f a b)
    (u v : LeftIndex a b) (huv : u.val < v.val) :
    ∃ ht : I.scalarIntegrableValue k f u.val v.val,
      I.scalarIntegralValue k f ht =
        LeftTruncation k f a b h u - LeftTruncation k f a b h v := by
  have ht := scalar_integrable_subinterval k f (h.2 u) le_rfl huv.le v.property.2.le
  refine ⟨ht, ?_⟩
  have heq := scalar_integral_split k f huv.le v.property.2.le (h.2 u) ht (h.2 v)
  change I.scalarIntegralValue k f ht =
    I.scalarIntegralValue k f (h.2 u) - I.scalarIntegralValue k f (h.2 v)
  rw [heq, add_sub_cancel_right]

theorem right_index_nonempty {k : ScalarKind} {f : ℝ → S.scalarValue k}
    {a : ℝ} {b : WithTop ℝ} (h : RightRegular k f a b) : Nonempty (RightIndex a b) := by
  cases b using WithTop.recTopCoe with
  | top => exact ⟨⟨a + 1, lt_add_one _, WithTop.coe_lt_top _⟩⟩
  | coe b =>
    obtain ⟨r, har, hrb⟩ := exists_between (WithTop.coe_lt_coe.mp h.1)
    exact ⟨⟨r, har, WithTop.coe_lt_coe.mpr hrb⟩⟩

theorem left_index_nonempty {k : ScalarKind} {f : ℝ → S.scalarValue k}
    {a : WithBot ℝ} {b : ℝ} (h : LeftRegular k f a b) : Nonempty (LeftIndex a b) := by
  cases a using WithBot.recBotCoe with
  | bot => exact ⟨⟨b - 1, WithBot.bot_lt_coe _, sub_one_lt _⟩⟩
  | coe a =>
    obtain ⟨r, har, hrb⟩ := exists_between (WithBot.coe_lt_coe.mp h.1)
    exact ⟨⟨r, WithBot.coe_lt_coe.mpr har, hrb⟩⟩

theorem right_cauchy_criterion : rightCauchyCriterion := by
  intro k f a b h
  let : CompleteSpace (S.scalarValue k) := scalar_complete k
  have hc := exists_cofinal_limit_iff (RightTruncation k f a b h)
    (right_index_nonempty h) (fun r => by
      obtain ⟨s, hrs, _⟩ := right_later r r
      exact ⟨s, hrs⟩)
  change (∃ L, ∃ h' : RightRegular k f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ t : RightIndex a b,
      r.val < t.val → dist (RightTruncation k f a b h' t) L < ε) ↔ _
  rw [show (∃ L, ∃ h' : RightRegular k f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ t : RightIndex a b,
      r.val < t.val → dist (RightTruncation k f a b h' t) L < ε) ↔
      (∃ L, ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a b, ∀ t : RightIndex a b,
        r < t → dist (RightTruncation k f a b h t) L < ε) from
    ⟨fun ⟨L, _, hL⟩ => ⟨L, hL⟩, fun ⟨L, hL⟩ => ⟨L, h, hL⟩⟩, hc]
  constructor
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun u v hru huv => ?_⟩
    obtain ⟨ht, heq⟩ := right_tail_difference k f a b h u v huv
    refine ⟨ht, ?_⟩
    rw [heq]
    simpa only [dist_eq_norm] using hr u v hru huv
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun u v hru huv => ?_⟩
    obtain ⟨ht, heq⟩ := right_tail_difference k f a b h u v huv
    obtain ⟨ht', hlt⟩ := hr u v hru huv
    rw [dist_eq_norm, ← heq]
    exact hlt

theorem left_cauchy_criterion : leftCauchyCriterion := by
  intro k f a b h
  let : CompleteSpace (S.scalarValue k) := scalar_complete k
  have hc := exists_cofinal_limit_iff (α := OrderDual (LeftIndex a b))
    (LeftTruncation k f a b h) (left_index_nonempty h) (fun r => by
      obtain ⟨s, hsr, _⟩ := left_earlier r r
      exact ⟨s, hsr⟩)
  change (∃ L, ∃ h' : LeftRegular k f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ t : LeftIndex a b,
      t.val < r.val → dist (LeftTruncation k f a b h' t) L < ε) ↔ _
  rw [show (∃ L, ∃ h' : LeftRegular k f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ t : LeftIndex a b,
      t.val < r.val → dist (LeftTruncation k f a b h' t) L < ε) ↔
      (∃ L, ∀ ε : ℝ, 0 < ε → ∃ r : OrderDual (LeftIndex a b),
        ∀ t : OrderDual (LeftIndex a b), r < t →
          dist (LeftTruncation k f a b h t) L < ε) from
    ⟨fun ⟨L, _, hL⟩ => ⟨L, hL⟩, fun ⟨L, hL⟩ => ⟨L, h, hL⟩⟩, hc]
  constructor
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun u v huv hvr => ?_⟩
    obtain ⟨ht, heq⟩ := left_tail_difference k f a b h u v huv
    refine ⟨ht, ?_⟩
    rw [heq]
    simpa only [dist_eq_norm] using hr v u hvr huv
  · intro hd ε hε
    obtain ⟨r, hr⟩ := hd ε hε
    refine ⟨r, fun v u hvr huv => ?_⟩
    obtain ⟨ht, heq⟩ := left_tail_difference k f a b h u v huv
    obtain ⟨ht', hlt⟩ := hr u v huv hvr
    rw [dist_eq_norm, ← heq]
    exact hlt

end SingleVariableAnalysis.Riemann.Improper
