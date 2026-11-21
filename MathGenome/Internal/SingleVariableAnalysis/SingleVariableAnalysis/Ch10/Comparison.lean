import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Comparison

/-! Comparison of improper Riemann integrals by order of proper tail integrals.
Only the tail must be nonnegative. The supremum argument is applied on that
cofinal tail, so earlier partial values need not satisfy any sign bound. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.Comparison

set_option backward.isDefEq.respectTransparency false

noncomputable local instance (a : ℝ) (b : WithTop ℝ) : LinearOrder (RightIndex a b) := by
  change LinearOrder {t : ℝ // a < t ∧ (t : WithTop ℝ) < b}
  infer_instance

noncomputable local instance (a : WithBot ℝ) (b : ℝ) : LinearOrder (LeftIndex a b) := by
  change LinearOrder {t : ℝ // a < (t : WithBot ℝ) ∧ t < b}
  infer_instance

/-- A bounded increasing cofinal tail has a finite limit. -/
theorem cofinal_limit_of_monotone_bounded {ι : Type*} [LinearOrder ι]
    (later : ∀ r s : ι, ∃ t, r < t ∧ s < t) (H : ι → ℝ) (r : ι)
    (hm : ∀ u v, r < u → u ≤ v → H u ≤ H v)
    (hb : ∃ B : ℝ, ∀ t, r < t → H t ≤ B) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ι, ∀ t, s < t → dist (H t) L < ε := by
  let S : Set ℝ := H '' Set.Ioi r
  obtain ⟨q, hrq, _⟩ := later r r
  have hne : S.Nonempty := ⟨H q, ⟨q, hrq, rfl⟩⟩
  have hbd : BddAbove S := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, by rintro _ ⟨t, ht, rfl⟩; exact hB t ht⟩
  refine ⟨sSup S, fun ε hε => ?_⟩
  obtain ⟨y, ⟨s, hrs, rfl⟩, hs, _⟩ := real_supremum_approx S hne hbd ε hε
  refine ⟨s, fun t hst => ?_⟩
  have hu : H t ≤ sSup S := le_csSup hbd ⟨t, hrs.trans hst, rfl⟩
  have hl : sSup S - ε < H t := hs.trans_le (hm s t hrs hst.le)
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

/-- Domination of nonnegative increments on a tail transfers finite
convergence. The functions may have arbitrary values before that tail. -/
theorem cofinal_comparison {ι : Type*} [LinearOrder ι]
    (later : ∀ r s : ι, ∃ t, r < t ∧ s < t)
    (H G : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (r : ι)
    (hi : ∀ u v, r < u → u ≤ v →
      0 ≤ H v - H u ∧ H v - H u ≤ C * (G v - G u))
    (hg : ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ι,
      ∀ t, s < t → dist (G t) L < ε) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ι, ∀ t, s < t → dist (H t) L < ε := by
  obtain ⟨L, hL⟩ := hg
  obtain ⟨s, hs⟩ := hL 1 zero_lt_one
  obtain ⟨q, hrq, hsq⟩ := later r s
  apply cofinal_limit_of_monotone_bounded later H q
  · intro u v hqu huv
    have h := (hi u v (hrq.trans hqu) huv).1
    linarith
  · refine ⟨H q + C * (L + 1 - G q), fun t hqt => ?_⟩
    have h := (hi q t hrq hqt.le).2
    have hg' := hs t (hsq.trans hqt)
    rw [Real.dist_eq] at hg'
    have hu : G t ≤ L + 1 := by linarith [(abs_lt.mp hg').2]
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right hu (G q)) hC
    linarith

/-- Proper interval order, with a constant majorant. -/
theorem realIntegral_scaled_comparison {f g : ℝ → ℝ} {u v C : ℝ}
    (hf : RealIntegrable f u v) (hg : RealIntegrable g u v)
    (hp : ∀ x ∈ Set.Icc u v, 0 ≤ f x ∧ f x ≤ C * g x) :
    0 ≤ realIntegral f hf ∧ realIntegral f hf ≤ C * realIntegral g hg := by
  obtain ⟨hCg, hval⟩ := real_mul_value hg C
  refine ⟨realIntegral_nonneg hf (fun x hx => (hp x hx).1), ?_⟩
  rw [← hval]
  exact realIntegral_mono _ _ hf hCg (fun x hx => (hp x hx).2)

/-- The increment of a right partial integral is its proper tail integral. -/
theorem right_truncation_sub {f : ℝ → ℝ} {a : ℝ} {b : WithTop ℝ}
    (h : RightRegular .real f a b) (u v : RightIndex a b) (huv : u.val ≤ v.val)
    (hi : RealIntegrable f u.val v.val) :
    RightTruncation .real f a b h v - RightTruncation .real f a b h u =
      realIntegral f hi := by
  have hv : RealIntegrable f a v.val := h.2 v
  have hu : RealIntegrable f a u.val := h.2 u
  have hadd := (real_split f u.property.1.le huv hv.bounded).2 hv hu hi
  change realIntegral f hv - realIntegral f hu = realIntegral f hi
  linarith

/-- The increment toward a left endpoint is its proper tail integral. -/
theorem left_truncation_sub {f : ℝ → ℝ} {a : WithBot ℝ} {b : ℝ}
    (h : LeftRegular .real f a b) (u v : LeftIndex a b) (huv : v.val ≤ u.val)
    (hi : RealIntegrable f v.val u.val) :
    LeftTruncation .real f a b h v - LeftTruncation .real f a b h u =
      realIntegral f hi := by
  have hv : RealIntegrable f v.val b := h.2 v
  have hu : RealIntegrable f u.val b := h.2 u
  have hadd := (real_split f huv u.property.2.le hv.bounded).2 hv hi hu
  change realIntegral f hv - realIntegral f hu = realIntegral f hi
  linarith

/-- Eventual comparison by any nonnegative constant, at a right endpoint. -/
theorem right_scaled_comparison (f g : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (hf : RightRegular .real f a b) (hg : RightRegular .real g a b)
    (C : ℝ) (hC : 0 ≤ C)
    (hp : ∃ r : RightIndex a b, ∀ x : RightIndex a b,
      r.val < x.val → 0 ≤ f x.val ∧ f x.val ≤ C * g x.val)
    (hc : RightConverges .real g a b) : RightConverges .real f a b := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨L, _, hL⟩ := hc
  obtain ⟨M, hM⟩ := cofinal_comparison (ι := RightIndex a b)
    (fun r s => right_later r s)
    (RightTruncation .real f a b hf) (RightTruncation .real g a b hg)
    C hC r (by
      intro u v hru huv
      have hfv : RealIntegrable f a v.val := hf.2 v
      have hgv : RealIntegrable g a v.val := hg.2 v
      have hfi := hfv.subinterval u.property.1.le huv le_rfl
      have hgi := hgv.subinterval u.property.1.le huv le_rfl
      rw [right_truncation_sub hf u v huv hfi, right_truncation_sub hg u v huv hgi]
      apply realIntegral_scaled_comparison hfi hgi
      intro x hx
      exact hr ⟨x, u.property.1.trans_le hx.1,
        (WithTop.coe_le_coe.mpr hx.2).trans_lt v.property.2⟩ (hru.trans_le hx.1))
    ⟨L, hL⟩
  exact ⟨M, hf, hM⟩

/-- Eventual comparison by any nonnegative constant, at a left endpoint. -/
theorem left_scaled_comparison (f g : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ)
    (hf : LeftRegular .real f a b) (hg : LeftRegular .real g a b)
    (C : ℝ) (hC : 0 ≤ C)
    (hp : ∃ r : LeftIndex a b, ∀ x : LeftIndex a b,
      x.val < r.val → 0 ≤ f x.val ∧ f x.val ≤ C * g x.val)
    (hc : LeftConverges .real g a b) : LeftConverges .real f a b := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨L, _, hL⟩ := hc
  obtain ⟨M, hM⟩ := cofinal_comparison (ι := (LeftIndex a b)ᵒᵈ)
    (fun r s => left_earlier r s)
    (LeftTruncation .real f a b hf) (LeftTruncation .real g a b hg)
    C hC r (by
      intro u v hru huv
      have hfv : RealIntegrable f v.val b := hf.2 v
      have hgv : RealIntegrable g v.val b := hg.2 v
      have hfi := hfv.subinterval le_rfl huv u.property.2.le
      have hgi := hgv.subinterval le_rfl huv u.property.2.le
      rw [left_truncation_sub hf u v huv hfi, left_truncation_sub hg u v huv hgi]
      apply realIntegral_scaled_comparison hfi hgi
      intro x hx
      exact hr ⟨x, v.property.1.trans_le (WithBot.coe_le_coe.mpr hx.1),
        hx.2.trans_lt u.property.2⟩ (hx.2.trans_lt hru))
    ⟨L, hL⟩
  exact ⟨M, hf, hM⟩

theorem right_comparison : rightComparison := by
  intro f g a b hf hg hp hc
  apply right_scaled_comparison f g a b hf hg 1 zero_le_one _ hc
  simpa only [one_mul] using hp

theorem left_comparison : leftComparison := by
  intro f g a b hf hg hp hc
  apply left_scaled_comparison f g a b hf hg 1 zero_le_one _ hc
  simpa only [one_mul] using hp

/-- A positive finite ratio gives two positive constant comparisons. -/
theorem ratio_comparison_bounds {F G c : ℝ} (hc : 0 < c) (hG : 0 < G)
    (he : |F / G - c| < c / 2) :
    F ≤ (3 * c / 2) * G ∧ G ≤ (2 / c) * F := by
  have hl : c / 2 < F / G := by linarith [(abs_lt.mp he).1]
  have hu : F / G < 3 * c / 2 := by linarith [(abs_lt.mp he).2]
  have hl' := (lt_div_iff₀ hG).mp hl
  refine ⟨((div_lt_iff₀ hG).mp hu).le, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  linarith

theorem right_limit_comparison : rightLimitComparison := by
  intro f g a b c hf hg hc hp hlim
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hlim (c / 2) (half_pos hc)
  obtain ⟨q, hrq, hsq⟩ := right_later r s
  have hp' (x : RightIndex a b) (hqx : q.val < x.val) := hr x (hrq.trans hqx)
  have hb (x : RightIndex a b) (hqx : q.val < x.val) :=
    ratio_comparison_bounds hc (hp' x hqx).2 (hs x (hsq.trans hqx))
  constructor
  · intro hconv
    apply right_scaled_comparison g f a b hg hf (2 / c) (by positivity) _ hconv
    exact ⟨q, fun x hx => ⟨(hp' x hx).2.le, (hb x hx).2⟩⟩
  · intro hconv
    apply right_scaled_comparison f g a b hf hg (3 * c / 2) (by positivity) _ hconv
    exact ⟨q, fun x hx => ⟨(hp' x hx).1.le, (hb x hx).1⟩⟩

theorem left_limit_comparison : leftLimitComparison := by
  intro f g a b c hf hg hc hp hlim
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hlim (c / 2) (half_pos hc)
  obtain ⟨q, hqr, hqs⟩ := left_earlier r s
  have hp' (x : LeftIndex a b) (hxq : x.val < q.val) := hr x (hxq.trans hqr)
  have hb (x : LeftIndex a b) (hxq : x.val < q.val) :=
    ratio_comparison_bounds hc (hp' x hxq).2 (hs x (hxq.trans hqs))
  constructor
  · intro hconv
    apply left_scaled_comparison g f a b hg hf (2 / c) (by positivity) _ hconv
    exact ⟨q, fun x hx => ⟨(hp' x hx).2.le, (hb x hx).2⟩⟩
  · intro hconv
    apply left_scaled_comparison f g a b hf hg (3 * c / 2) (by positivity) _ hconv
    exact ⟨q, fun x hx => ⟨(hp' x hx).1.le, (hb x hx).1⟩⟩

/-- Restricting to a regular tail preserves proper integrability. -/
theorem right_regular_tail {f : ℝ → ℝ} {a : ℝ} {b : WithTop ℝ}
    (hf : RightRegular .real f a b) (r : RightIndex a b) :
    RightRegular .real f r.val b := by
  refine ⟨r.property.2, fun t => ?_⟩
  have ht : RealIntegrable f a t.val :=
    hf.2 ⟨t.val, r.property.1.trans t.property.1, t.property.2⟩
  exact ht.subinterval r.property.1.le t.property.1.le le_rfl

/-- Restricting to a regular tail preserves proper integrability. -/
theorem left_regular_tail {f : ℝ → ℝ} {a : WithBot ℝ} {b : ℝ}
    (hf : LeftRegular .real f a b) (r : LeftIndex a b) :
    LeftRegular .real f a r.val := by
  refine ⟨r.property.1, fun t => ?_⟩
  have ht : RealIntegrable f t.val b :=
    hf.2 ⟨t.val, t.property.1, t.property.2.trans r.property.2⟩
  exact ht.subinterval le_rfl t.property.2.le r.property.2.le

/-- Exact finite correction to the limit when the regular endpoint moves. -/
theorem right_hasIntegral_prefix {f : ℝ → ℝ} {a : ℝ} {b : WithTop ℝ}
    (hf : RightRegular .real f a b) (r : RightIndex a b) (M : ℝ) :
    RightHasIntegral .real f a b ((show ℝ from RightTruncation .real f a b hf r) + M) ↔
      RightHasIntegral .real f r.val b M := by
  let ht := right_regular_tail hf r
  have hdist (t : RightIndex r.val b) :
      dist (RightTruncation .real f r.val b ht t) M =
      dist (RightTruncation .real f a b hf
        ⟨t.val, r.property.1.trans t.property.1, t.property.2⟩)
        ((show ℝ from RightTruncation .real f a b hf r) + M) := by
    have hs := right_truncation_sub hf r
      ⟨t.val, r.property.1.trans t.property.1, t.property.2⟩ t.property.1.le (ht.2 t)
    let ti : RightIndex a b :=
      ⟨t.val, r.property.1.trans t.property.1, t.property.2⟩
    change realIntegral f (hf.2 ti) - realIntegral f (hf.2 r) =
      realIntegral f (ht.2 t) at hs
    change dist (realIntegral f (ht.2 t)) M =
      dist (realIntegral f (hf.2 ti)) (realIntegral f (hf.2 r) + M)
    rw [Real.dist_eq, Real.dist_eq]
    congr 1
    linarith
  constructor
  · rintro ⟨_, hL⟩
    refine ⟨ht, fun ε hε => ?_⟩
    obtain ⟨s, hs⟩ := hL ε hε
    obtain ⟨q, hsq, hrq⟩ := right_later s r
    refine ⟨⟨q.val, hrq, q.property.2⟩, fun t hqt => ?_⟩
    rw [hdist t]
    exact hs _ (hsq.trans hqt)
  · rintro ⟨_, hM⟩
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨s, hs⟩ := hM ε hε
    refine ⟨⟨s.val, r.property.1.trans s.property.1, s.property.2⟩, fun t hst => ?_⟩
    let ti : RightIndex r.val b := ⟨t.val, s.property.1.trans hst, t.property.2⟩
    have he := hs ti hst
    rw [hdist ti] at he
    exact he

/-- Exact finite correction to the limit when the regular endpoint moves. -/
theorem left_hasIntegral_prefix {f : ℝ → ℝ} {a : WithBot ℝ} {b : ℝ}
    (hf : LeftRegular .real f a b) (r : LeftIndex a b) (M : ℝ) :
    LeftHasIntegral .real f a b ((show ℝ from LeftTruncation .real f a b hf r) + M) ↔
      LeftHasIntegral .real f a r.val M := by
  let ht := left_regular_tail hf r
  have hdist (t : LeftIndex a r.val) :
      dist (LeftTruncation .real f a r.val ht t) M =
      dist (LeftTruncation .real f a b hf
        ⟨t.val, t.property.1, t.property.2.trans r.property.2⟩)
        ((show ℝ from LeftTruncation .real f a b hf r) + M) := by
    have hs := left_truncation_sub hf r
      ⟨t.val, t.property.1, t.property.2.trans r.property.2⟩ t.property.2.le (ht.2 t)
    let ti : LeftIndex a b :=
      ⟨t.val, t.property.1, t.property.2.trans r.property.2⟩
    change realIntegral f (hf.2 ti) - realIntegral f (hf.2 r) =
      realIntegral f (ht.2 t) at hs
    change dist (realIntegral f (ht.2 t)) M =
      dist (realIntegral f (hf.2 ti)) (realIntegral f (hf.2 r) + M)
    rw [Real.dist_eq, Real.dist_eq]
    congr 1
    linarith
  constructor
  · rintro ⟨_, hL⟩
    refine ⟨ht, fun ε hε => ?_⟩
    obtain ⟨s, hs⟩ := hL ε hε
    obtain ⟨q, hqs, hqr⟩ := left_earlier s r
    refine ⟨⟨q.val, q.property.1, hqr⟩, fun t htq => ?_⟩
    rw [hdist t]
    exact hs _ (htq.trans hqs)
  · rintro ⟨_, hM⟩
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨s, hs⟩ := hM ε hε
    refine ⟨⟨s.val, s.property.1, s.property.2.trans r.property.2⟩, fun t hts => ?_⟩
    let ti : LeftIndex a r.val := ⟨t.val, t.property.1, hts.trans s.property.2⟩
    have he := hs ti hts
    rw [hdist ti] at he
    exact he

theorem right_finite_prefix : rightFinitePrefix := by
  intro f a b hf r
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - RightTruncation .real f a b hf r, ?_⟩
    apply (right_hasIntegral_prefix hf r _).mp
    convert hL using 1
    abel
  · rintro ⟨M, hM⟩
    exact ⟨_, (right_hasIntegral_prefix hf r M).mpr hM⟩

theorem left_finite_prefix : leftFinitePrefix := by
  intro f a b hf r
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - LeftTruncation .real f a b hf r, ?_⟩
    apply (left_hasIntegral_prefix hf r _).mp
    convert hL using 1
    abel
  · rintro ⟨M, hM⟩
    exact ⟨_, (left_hasIntegral_prefix hf r M).mpr hM⟩

end SingleVariableAnalysis.Riemann.Improper
