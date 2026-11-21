import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Nonnegative

/-! Nonnegative improper Darboux integrals. The proof uses order and
additivity on regular compact intervals, then real completeness on the range
of partial values. No measure integral or absolute convergence is assumed. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.Nonnegative

/-- A nonempty interval of truncation parameters, also at +∞. -/
theorem rightIndex_nonempty {a : ℝ} {b : WithTop ℝ}
    (hab : (a : WithTop ℝ) < b) : Nonempty (RightIndex a b) := by
  cases b using WithTop.recTopCoe with
  | top => exact ⟨⟨a + 1, lt_add_one a, WithTop.coe_lt_top _⟩⟩
  | coe b =>
    obtain ⟨t, hat, htb⟩ := exists_between (WithTop.coe_lt_coe.mp hab)
    exact ⟨⟨t, hat, WithTop.coe_lt_coe.mpr htb⟩⟩

/-- Positivity for the existing proof-indexed proper Darboux integral. -/
theorem realIntegral_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hn : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    0 ≤ realIntegral f hf := by
  obtain ⟨hz, heq⟩ := real_zero_value hf.ordered
  rw [← heq]
  exact realIntegral_mono _ _ hz hf hn

theorem right_nonnegative_monotone : rightNonnegativeMonotone := by
  intro f a b h hn u v huv
  have hv : RealIntegrable f a v.val := h.2 v
  have hu : RealIntegrable f a u.val := h.2 u
  have huv' : u.val ≤ v.val := huv
  have hi : RealIntegrable f u.val v.val :=
    hv.subinterval u.property.1.le huv' le_rfl
  have hpos : 0 ≤ realIntegral f hi := realIntegral_nonneg hi (by
    intro x hx
    exact hn x (u.property.1.le.trans hx.1)
      ((WithTop.coe_le_coe.mpr hx.2).trans_lt v.property.2))
  have hadd := (real_split f u.property.1.le huv' hv.bounded).2 hv hu hi
  change realIntegral f hu ≤ realIntegral f hv
  linarith

theorem right_nonnegative_hasIntegral_supremum : rightNonnegativeHasIntegralSupremum := by
  intro f a b h hn hb
  let H : RightIndex a b → ℝ := fun t => RightTruncation .real f a b h t
  obtain ⟨t₀⟩ := rightIndex_nonempty h.1
  have hne : (Set.range H).Nonempty := ⟨H t₀, Set.mem_range_self t₀⟩
  have hm (u v : RightIndex a b) (huv : u.val ≤ v.val) : H u ≤ H v :=
    right_nonnegative_monotone f a b h hn u v huv
  refine ⟨h, fun ε hε => ?_⟩
  obtain ⟨y, hy, hlow, _⟩ := real_supremum_approx (Set.range H) hne hb ε hε
  obtain ⟨r, rfl⟩ := hy
  refine ⟨r, fun t hrt => ?_⟩
  have hupper : H t ≤ sSup (Set.range H) := le_csSup hb (Set.mem_range_self t)
  have hlower : sSup (Set.range H) - ε < H t := hlow.trans_le (hm r t hrt.le)
  change dist (H t) (sSup (Set.range H)) < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  change sSup (Set.range H) - ε < H r at hlow
  linarith

theorem right_nonnegative_converges_iff_bounded : rightNonnegativeConvergesIffBounded := by
  intro f a b h hn
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨h', hL⟩ := hL
    let l : ℝ := L
    obtain ⟨r, hr⟩ := hL 1 zero_lt_one
    obtain ⟨s, hrs, _⟩ := right_later r r
    let H : RightIndex a b → ℝ := fun t => RightTruncation .real f a b h t
    have hm (u v : RightIndex a b) (huv : u.val ≤ v.val) : H u ≤ H v :=
      right_nonnegative_monotone f a b h hn u v huv
    refine ⟨max (H s) (l + 1), ?_⟩
    rintro _ ⟨t, rfl⟩
    by_cases hts : t.val ≤ s.val
    · exact (hm t s hts).trans (le_max_left _ _)
    · have ht : r.val < t.val := hrs.trans (lt_of_not_ge hts)
      have he := hr t ht
      change dist (H t) l < 1 at he
      rw [Real.dist_eq] at he
      exact (by linarith [(abs_lt.mp he).2] : H t ≤ l + 1).trans (le_max_right _ _)
  · intro hb
    exact ⟨_, right_nonnegative_hasIntegral_supremum f a b h hn hb⟩

theorem right_nonnegative_diverges_of_unbounded : rightNonnegativeDivergesOfUnbounded := by
  intro f a b h hn hb
  let H : RightIndex a b → ℝ := fun t => RightTruncation .real f a b h t
  have hm (u v : RightIndex a b) (huv : u.val ≤ v.val) : H u ≤ H v :=
    right_nonnegative_monotone f a b h hn u v huv
  refine ⟨h, fun B => ?_⟩
  have hex : ∃ r, B < H r := by
    by_contra hnex
    apply hb
    refine ⟨B, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact le_of_not_gt (fun hgt => hnex ⟨t, hgt⟩)
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, fun t hrt => hr.trans_le (hm r t hrt.le)⟩

theorem right_nonnegative_diverges_of_not_converges : rightNonnegativeDivergesOfNotConverges := by
  intro f a b h hn hnot
  apply right_nonnegative_diverges_of_unbounded f a b h hn
  exact fun hb => hnot ((right_nonnegative_converges_iff_bounded f a b h hn).mpr hb)

end SingleVariableAnalysis.Riemann.Improper
