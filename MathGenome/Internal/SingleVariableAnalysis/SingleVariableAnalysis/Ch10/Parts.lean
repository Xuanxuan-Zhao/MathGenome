import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.SeveralEndpoints
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Abel

/-! Improper integration by parts, K03.10.parts. Only finite scalar limit
algebra is needed after the given proper formula. Each singular side is
handled on its own cutoff domain before any component values are added. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.Parts
open scoped BigOperators

/-- Finite limit algebra for a directed system of cutoff tails. -/
private theorem tail_remainder {ι V : Type*} [NormedAddCommGroup V]
    (R : ι → ι → Prop)
    (merge : ∀ r s, ∃ q, ∀ t, R q t → R r t ∧ R s t)
    (f w g : ι → V) (W G c : V)
    (he : ∀ t, f t = w t - c - g t)
    (hw : ∀ ε : ℝ, 0 < ε → ∃ r, ∀ t, R r t → dist (w t) W < ε)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ r, ∀ t, R r t → dist (g t) G < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ r, ∀ t, R r t → dist (f t) (W - c - G) < ε := by
  intro ε hε
  obtain ⟨r, hr⟩ := hw (ε / 2) (half_pos hε)
  obtain ⟨s, hs⟩ := hg (ε / 2) (half_pos hε)
  obtain ⟨q, hq⟩ := merge r s
  refine ⟨q, fun t ht => ?_⟩
  have h₁ := hr t (hq t ht).1
  have h₂ := hs t (hq t ht).2
  rw [he t]
  have hb := dist_sub_sub_le (w t - c) (g t) (W - c) G
  rw [dist_sub_right] at hb
  linarith

private theorem right_common_tail {a : ℝ} {b : WithTop ℝ} (r s : RightIndex a b) :
    ∃ q : RightIndex a b, ∀ t : RightIndex a b,
      q.val < t.val → r.val < t.val ∧ s.val < t.val := by
  obtain ⟨q, hrq, hsq⟩ := right_later r s
  exact ⟨q, fun _ ht => ⟨hrq.trans ht, hsq.trans ht⟩⟩

private theorem left_common_tail {a : WithBot ℝ} {b : ℝ} (r s : LeftIndex a b) :
    ∃ q : LeftIndex a b, ∀ t : LeftIndex a b,
      t.val < q.val → t.val < r.val ∧ t.val < s.val := by
  obtain ⟨q, hqr, hqs⟩ := left_earlier r s
  exact ⟨q, fun _ ht => ⟨ht.trans hqr, ht.trans hqs⟩⟩

theorem right_parts_from_du : rightPartsFromDu := by
  intro k u v du dv a b B J hd hB hJ
  obtain ⟨hf, hg, he⟩ := hd
  obtain ⟨hg', hJ⟩ := hJ
  exact ⟨hf, tail_remainder (fun r t : RightIndex a b => r.val < t.val)
    right_common_tail (RightTruncation k _ a b hf)
    (fun t => u t.val * v t.val) (RightTruncation k _ a b hg)
    B J (u a * v a) he hB.2 hJ⟩

theorem right_parts_from_dv : rightPartsFromDv := by
  intro k u v du dv a b B H hd hB hH
  obtain ⟨hf, hg, he⟩ := hd
  obtain ⟨hf', hH⟩ := hH
  have he' (t : RightIndex a b) : RightTruncation k (fun x => du x * v x) a b hg t =
      u t.val * v t.val - u a * v a - RightTruncation k (fun x => u x * dv x) a b hf t := by
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [add_comm] using eq_sub_iff_add_eq.mp (he t))
  exact ⟨hg, tail_remainder (fun r t : RightIndex a b => r.val < t.val)
    right_common_tail (RightTruncation k _ a b hg)
    (fun t => u t.val * v t.val) (RightTruncation k _ a b hf)
    B H (u a * v a) he' hB.2 hH⟩

theorem right_parts : rightParts := by
  intro k u v du dv a b B hd hB
  constructor
  · constructor
    · rintro ⟨H, hH⟩
      exact ⟨_, right_parts_from_dv k u v du dv a b B H hd hB hH⟩
    · rintro ⟨J, hJ⟩
      exact ⟨_, right_parts_from_du k u v du dv a b B J hd hB hJ⟩
  · intro H J hH hJ
    exact right_unique k _ a b _ _ hH (right_parts_from_du k u v du dv a b B J hd hB hJ)

theorem left_parts_from_du : leftPartsFromDu := by
  intro k u v du dv a b A J hd hA hJ
  obtain ⟨hf, hg, he⟩ := hd
  obtain ⟨hg', hJ⟩ := hJ
  have hb : ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ t : LeftIndex a b,
      t.val < r.val → dist (u b * v b - u t.val * v t.val) (u b * v b - A) < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := hA.2 ε hε
    exact ⟨r, fun t ht => by simpa only [dist_sub_left] using hr t ht⟩
  have hh := tail_remainder (fun r t : LeftIndex a b => t.val < r.val)
    left_common_tail (LeftTruncation k _ a b hf)
    (fun t => u b * v b - u t.val * v t.val) (LeftTruncation k _ a b hg)
    (u b * v b - A) J 0 (by simpa only [sub_zero] using he) hb hJ
  exact ⟨hf, by simpa only [sub_zero] using hh⟩

theorem left_parts_from_dv : leftPartsFromDv := by
  intro k u v du dv a b A H hd hA hH
  obtain ⟨hf, hg, he⟩ := hd
  obtain ⟨hf', hH⟩ := hH
  have he' (t : LeftIndex a b) : LeftTruncation k (fun x => du x * v x) a b hg t =
      u b * v b - u t.val * v t.val - LeftTruncation k (fun x => u x * dv x) a b hf t := by
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [add_comm] using eq_sub_iff_add_eq.mp (he t))
  have hb : ∀ ε : ℝ, 0 < ε → ∃ r : LeftIndex a b, ∀ t : LeftIndex a b,
      t.val < r.val → dist (u b * v b - u t.val * v t.val) (u b * v b - A) < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := hA.2 ε hε
    exact ⟨r, fun t ht => by simpa only [dist_sub_left] using hr t ht⟩
  have hh := tail_remainder (fun r t : LeftIndex a b => t.val < r.val)
    left_common_tail (LeftTruncation k _ a b hg)
    (fun t => u b * v b - u t.val * v t.val) (LeftTruncation k _ a b hf)
    (u b * v b - A) H 0 (by simpa only [sub_zero] using he') hb hH
  exact ⟨hg, by simpa only [sub_zero] using hh⟩

theorem left_parts : leftParts := by
  intro k u v du dv a b A hd hA
  constructor
  · constructor
    · rintro ⟨H, hH⟩
      exact ⟨_, left_parts_from_dv k u v du dv a b A H hd hA hH⟩
    · rintro ⟨J, hJ⟩
      exact ⟨_, left_parts_from_du k u v du dv a b A J hd hA hJ⟩
  · intro H J hH hJ
    exact left_unique k _ a b _ _ hH (left_parts_from_du k u v du dv a b A J hd hA hJ)


/-- Restrict the given formula on a regular component to each of its two
independent truncation families. -/
theorem parts_on_truncations (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (c : RegularPoint a b)
    (hd : PartsOn k u v du dv a b) :
    LeftPartsData k u v du dv a c.val ∧ RightPartsData k u v du dv c.val b := by
  obtain ⟨hf, hg, he⟩ := hd
  have hfl : LeftRegular k (fun x => u x * dv x) a c.val :=
    ⟨c.property.1, fun t => hf _ _ t.property.1 t.property.2.le c.property.2⟩
  have hgl : LeftRegular k (fun x => du x * v x) a c.val :=
    ⟨c.property.1, fun t => hg _ _ t.property.1 t.property.2.le c.property.2⟩
  have hfr : RightRegular k (fun x => u x * dv x) c.val b :=
    ⟨c.property.2, fun t => hf _ _ c.property.1 t.property.1.le t.property.2⟩
  have hgr : RightRegular k (fun x => du x * v x) c.val b :=
    ⟨c.property.2, fun t => hg _ _ c.property.1 t.property.1.le t.property.2⟩
  constructor
  · refine ⟨hfl, hgl, fun t => ?_⟩
    let r : RegularPoint a b := ⟨t.val, t.property.1,
      (WithTop.coe_le_coe.mpr t.property.2.le).trans_lt c.property.2⟩
    exact he r c t.property.2.le
  · refine ⟨hfr, hgr, fun t => ?_⟩
    let r : RegularPoint a b := ⟨t.val,
      c.property.1.trans_le (WithBot.coe_le_coe.mpr t.property.1.le), t.property.2⟩
    exact he c r t.property.1.le

/-- Each endpoint is passed to the limit separately, before adding values. -/
theorem split_parts_from_du (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (c : RegularPoint a b) (A B J : S.scalarValue k)
    (hd : PartsOn k u v du dv a b)
    (hA : LeftBoundaryLimit k (fun x => u x * v x) a c.val A)
    (hB : RightBoundaryLimit k (fun x => u x * v x) c.val b B)
    (hJ : HasIntegralAtSplit k (fun x => du x * v x) a b c J) :
    HasIntegralAtSplit k (fun x => u x * dv x) a b c (B - A - J) := by
  obtain ⟨hdl, hdr⟩ := parts_on_truncations k u v du dv c hd
  obtain ⟨l, r, hl, hr, rfl⟩ := hJ
  refine ⟨_, _, left_parts_from_du k u v du dv a c.val A l hdl hA hl,
    right_parts_from_du k u v du dv c.val b B r hdr hB hr, ?_⟩
  abel

theorem split_parts_from_dv (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (c : RegularPoint a b) (A B H : S.scalarValue k)
    (hd : PartsOn k u v du dv a b)
    (hA : LeftBoundaryLimit k (fun x => u x * v x) a c.val A)
    (hB : RightBoundaryLimit k (fun x => u x * v x) c.val b B)
    (hH : HasIntegralAtSplit k (fun x => u x * dv x) a b c H) :
    HasIntegralAtSplit k (fun x => du x * v x) a b c (B - A - H) := by
  obtain ⟨hdl, hdr⟩ := parts_on_truncations k u v du dv c hd
  obtain ⟨l, r, hl, hr, rfl⟩ := hH
  refine ⟨_, _, left_parts_from_dv k u v du dv a c.val A l hdl hA hl,
    right_parts_from_dv k u v du dv c.val b B r hdr hB hr, ?_⟩
  abel

theorem component_parts_from_du (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (c : RegularPoint a b) (A B J : S.scalarValue k)
    (hd : PartsOn k u v du dv a b)
    (hA : LeftBoundaryLimit k (fun x => u x * v x) a c.val A)
    (hB : RightBoundaryLimit k (fun x => u x * v x) c.val b B)
    (hJ : HasIntegral k (fun x => du x * v x) a b J) :
    HasIntegral k (fun x => u x * dv x) a b (B - A - J) := by
  have hJ' := ((hasIntegral_at_every_split k _ a b c J).mp hJ).2
  have hH := split_parts_from_du k u v du dv c A B J hd hA hB hJ'
  obtain ⟨hf, hg, he⟩ := hd
  exact (hasIntegral_at_every_split k _ a b c _).mpr ⟨hf, hH⟩

theorem component_parts_from_dv (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (c : RegularPoint a b) (A B H : S.scalarValue k)
    (hd : PartsOn k u v du dv a b)
    (hA : LeftBoundaryLimit k (fun x => u x * v x) a c.val A)
    (hB : RightBoundaryLimit k (fun x => u x * v x) c.val b B)
    (hH : HasIntegral k (fun x => u x * dv x) a b H) :
    HasIntegral k (fun x => du x * v x) a b (B - A - H) := by
  have hH' := ((hasIntegral_at_every_split k _ a b c H).mp hH).2
  have hJ := split_parts_from_dv k u v du dv c A B H hd hA hB hH'
  obtain ⟨hf, hg, he⟩ := hd
  exact (hasIntegral_at_every_split k _ a b c _).mpr ⟨hg, hJ⟩

theorem two_endpoint_parts : twoEndpointParts := by
  intro k u v du dv a b c A B hd hA hB
  constructor
  · constructor
    · rintro ⟨H, hH⟩
      exact ⟨_, component_parts_from_dv k u v du dv c A B H hd hA hB hH⟩
    · rintro ⟨J, hJ⟩
      exact ⟨_, component_parts_from_du k u v du dv c A B J hd hA hB hJ⟩
  · intro H J hH hJ
    have hH' := ((hasIntegral_at_every_split k _ a b c H).mp hH).2
    have hresult := component_parts_from_du k u v du dv c A B J hd hA hB hJ
    have hresult' := ((hasIntegral_at_every_split k _ a b c _).mp hresult).2
    exact split_unique k _ a b c _ _ hH' hresult'


/-- Transfer a finite improper integral while keeping all adjacent side limits. -/
theorem finite_parts_from_du (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    (n : ℕ) (a : WithBot ℝ) (b : WithTop ℝ) (s : Fin n → ℝ)
    (c : SplitFamily n a b s) (A B : Fin (n+1) → S.scalarValue k) (J : S.scalarValue k)
    (hd : ∀ i, PartsOn k u v du dv (componentLeft n a s i) (componentRight n b s i))
    (hA : ∀ i, LeftBoundaryLimit k (fun x => u x * v x) (componentLeft n a s i) (c i).val (A i))
    (hB : ∀ i, RightBoundaryLimit k (fun x => u x * v x) (c i).val (componentRight n b s i) (B i))
    (hJ : FiniteHasIntegral k (fun x => du x * v x) n a b s c J) :
    FiniteHasIntegral k (fun x => u x * dv x) n a b s c ((∑ i, (B i - A i)) - J) := by
  obtain ⟨z, hz, rfl⟩ := hJ
  refine ⟨(fun i => B i - A i - z i), ?_, ?_⟩
  · intro i
    obtain ⟨hf, hg, he⟩ := hd i
    exact ⟨hf, split_parts_from_du k u v du dv (c i) (A i) (B i) (z i)
      (hd i) (hA i) (hB i) (hz i).2⟩
  · exact (Finset.sum_sub_distrib (fun i => B i - A i) z).symm

/-- Transfer a finite improper integral while keeping all adjacent side limits. -/
theorem finite_parts_from_dv (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    (n : ℕ) (a : WithBot ℝ) (b : WithTop ℝ) (s : Fin n → ℝ)
    (c : SplitFamily n a b s) (A B : Fin (n+1) → S.scalarValue k) (J : S.scalarValue k)
    (hd : ∀ i, PartsOn k u v du dv (componentLeft n a s i) (componentRight n b s i))
    (hA : ∀ i, LeftBoundaryLimit k (fun x => u x * v x) (componentLeft n a s i) (c i).val (A i))
    (hB : ∀ i, RightBoundaryLimit k (fun x => u x * v x) (c i).val (componentRight n b s i) (B i))
    (hJ : FiniteHasIntegral k (fun x => u x * dv x) n a b s c J) :
    FiniteHasIntegral k (fun x => du x * v x) n a b s c ((∑ i, (B i - A i)) - J) := by
  obtain ⟨z, hz, rfl⟩ := hJ
  refine ⟨(fun i => B i - A i - z i), ?_, ?_⟩
  · intro i
    obtain ⟨hf, hg, he⟩ := hd i
    exact ⟨hg, split_parts_from_dv k u v du dv (c i) (A i) (B i) (z i)
      (hd i) (hA i) (hB i) (hz i).2⟩
  · exact (Finset.sum_sub_distrib (fun i => B i - A i) z).symm

theorem finite_endpoint_parts : finiteEndpointParts := by
  intro k u v du dv n a b s c A B hd hA hB
  constructor
  · constructor
    · rintro ⟨H, hH⟩
      exact ⟨_, finite_parts_from_dv k u v du dv n a b s c A B H hd hA hB hH⟩
    · rintro ⟨J, hJ⟩
      exact ⟨_, finite_parts_from_du k u v du dv n a b s c A B J hd hA hB hJ⟩
  · intro H J hH hJ
    exact finite_unique k _ n a b s c _ _ hH
      (finite_parts_from_du k u v du dv n a b s c A B J hd hA hB hJ)

end SingleVariableAnalysis.Riemann.Improper
