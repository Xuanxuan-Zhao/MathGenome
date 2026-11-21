import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints

namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
open SingleVariableAnalysis
open scoped BigOperators

abbrev RegularPoint := regularPointValue
abbrev LocallyIntegrable := locallyIntegrableValue
noncomputable abbrev HasIntegralAtSplit := hasIntegralAtSplitValue
noncomputable abbrev ConvergesAtSplit := convergesAtSplitValue
noncomputable abbrev integralAtSplit := integralAtSplitValue
noncomputable abbrev HasIntegral := hasIntegralValue
noncomputable abbrev Converges := convergesValue
noncomputable abbrev integral := integralValue
abbrev componentLeft := componentLeftValue
abbrev componentRight := componentRightValue
abbrev SplitFamily := splitFamilyValue
noncomputable abbrev FiniteHasIntegral := finiteHasIntegralValue
noncomputable abbrev FiniteConverges := finiteConvergesValue
noncomputable abbrev finiteIntegral := finiteIntegralValue

private theorem bot_coe_lt_of_le {a : WithBot ℝ} {x y : ℝ}
    (h : a < (x : WithBot ℝ)) (hxy : x ≤ y) : a < (y : WithBot ℝ) :=
  h.trans_le (WithBot.coe_le_coe.mpr hxy)

private theorem coe_top_lt_of_le {b : WithTop ℝ} {x y : ℝ}
    (h : (y : WithTop ℝ) < b) (hxy : x ≤ y) : (x : WithTop ℝ) < b :=
  lt_of_le_of_lt (WithTop.coe_le_coe.mpr hxy) h

private theorem regular_min {a : WithBot ℝ} {b : WithTop ℝ}
    (c d : RegularPoint a b) :
    a < ((min c.val d.val : ℝ) : WithBot ℝ) := by
  rcases le_total c.val d.val with h | h
  · simpa [min_eq_left h] using c.property.1
  · simpa [min_eq_right h] using d.property.1

private theorem regular_max {a : WithBot ℝ} {b : WithTop ℝ}
    (c d : RegularPoint a b) :
    ((max c.val d.val : ℝ) : WithTop ℝ) < b := by
  rcases le_total c.val d.val with h | h
  · simpa [max_eq_right h] using d.property.2
  · simpa [max_eq_left h] using c.property.2

/-- Oriented proper integral between any two regular points. -/
noncomputable def regularIntegral (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) : S.scalarValue k :=
  if c.val ≤ d.val then
    I.scalarIntegralValue k f (h _ _ (regular_min c d) min_le_max (regular_max c d))
  else -I.scalarIntegralValue k f (h _ _ (regular_min c d) min_le_max (regular_max c d))

private theorem regularIntegral_agreement (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) (hcd : c.val ≤ d.val)
    (hp : I.scalarIntegrableValue k f c.val d.val) :
    regularIntegral k f h c d = I.scalarIntegralValue k f hp := by
  simp only [regularIntegral, ite_eq_left hcd]
  congr 1 <;> simp only [min_eq_left hcd, max_eq_right hcd]

private theorem regularIntegral_add (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d e : RegularPoint a b) :
    regularIntegral k f h c d + regularIntegral k f h d e = regularIntegral k f h c e := by
  have hL : a < ((min c.val (min d.val e.val) : ℝ) : WithBot ℝ) := by
    rcases le_total d.val e.val with hde | hed
    · simpa [min_eq_left hde] using regular_min c d
    · simpa [min_eq_right hed] using regular_min c e
  have hU : ((max c.val (max d.val e.val) : ℝ) : WithTop ℝ) < b := by
    rcases le_total d.val e.val with hde | hed
    · simpa [max_eq_right hde] using regular_max c e
    · simpa [max_eq_left hed] using regular_max c d
  have hp := h _ _ hL (le_trans (min_le_left _ _) (le_max_left _ _)) hU
  cases k with
  | real =>
    obtain ⟨hcd, hde, hce, heq⟩ := oriented_real_additivity f c.val d.val e.val hp
    exact heq
  | complex =>
    obtain ⟨hcd, hde, hce, heq⟩ := oriented_complex_additivity f c.val d.val e.val hp
    exact heq

private theorem regularIntegral_self (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c : RegularPoint a b) : regularIntegral k f h c c = 0 := by
  have hh := regularIntegral_add k f h c c c
  exact add_left_cancel (hh.trans (add_zero _).symm)

private theorem regularIntegral_symm (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) : regularIntegral k f h d c = -regularIntegral k f h c d := by
  have hh := regularIntegral_add k f h c d c
  rw [regularIntegral_self k f h c] at hh
  exact eq_neg_of_add_eq_zero_right hh

private theorem leftRegular_of_local (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c : RegularPoint a b) : LeftRegular k f a c.val :=
  ⟨c.property.1, fun t => h _ _ t.property.1 t.property.2.le c.property.2⟩

private theorem rightRegular_of_local (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c : RegularPoint a b) : RightRegular k f c.val b :=
  ⟨c.property.2, fun t => h _ _ c.property.1 t.property.1.le t.property.2⟩

private theorem exists_left_index {a : WithBot ℝ} {x : ℝ} (h : a < (x : WithBot ℝ)) :
    ∃ y : ℝ, a < (y : WithBot ℝ) ∧ y < x := by
  cases a using WithBot.recBotCoe with
  | bot => exact ⟨x-1, WithBot.bot_lt_coe _, sub_one_lt _⟩
  | coe a =>
    obtain ⟨y, hay, hyx⟩ := exists_between (WithBot.coe_lt_coe.mp h)
    exact ⟨y, WithBot.coe_lt_coe.mpr hay, hyx⟩

private theorem exists_right_index {b : WithTop ℝ} {x : ℝ} (h : (x : WithTop ℝ) < b) :
    ∃ y : ℝ, x < y ∧ (y : WithTop ℝ) < b := by
  cases b using WithTop.recTopCoe with
  | top => exact ⟨x+1, lt_add_one _, WithTop.coe_lt_top _⟩
  | coe b =>
    obtain ⟨y, hxy, hyb⟩ := exists_between (WithTop.coe_lt_coe.mp h)
    exact ⟨y, hxy, WithTop.coe_lt_coe.mpr hyb⟩

/-- Moving the regular upper endpoint of a left improper integral adds a
fixed oriented proper integral. The singular cutoff remains independent. -/
theorem left_change_split (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) (L : S.scalarValue k)
    (hL : LeftHasIntegral k f a c.val L) :
    LeftHasIntegral k f a d.val (L + regularIntegral k f h c d) := by
  rcases hL with ⟨hc, hL⟩
  let hd := leftRegular_of_local k f h d
  refine ⟨hd, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hL ε hε
  have har : a < ((min r.val d.val : ℝ) : WithBot ℝ) := by
    rcases le_total r.val d.val with hrd | hdr
    · simpa [min_eq_left hrd] using r.property.1
    · simpa [min_eq_right hdr] using d.property.1
  obtain ⟨s, has, hsm⟩ := exists_left_index har
  have hsr : s < r.val := hsm.trans_le (min_le_left _ _)
  have hsd : s < d.val := hsm.trans_le (min_le_right _ _)
  refine ⟨⟨s, has, hsd⟩, fun t hts => ?_⟩
  have htc : t.val < c.val := hts.trans (hsr.trans r.property.2)
  let tc : LeftIndex a c.val := ⟨t.val, t.property.1, htc⟩
  let tp : RegularPoint a b := ⟨t.val, t.property.1,
    coe_top_lt_of_le d.property.2 t.property.2.le⟩
  have heq : LeftTruncation k f a d.val hd t =
      LeftTruncation k f a c.val hc tc + regularIntegral k f h c d := by
    have he := regularIntegral_add k f h tp c d
    rw [regularIntegral_agreement k f h tp c htc.le (hc.2 tc),
      regularIntegral_agreement k f h tp d t.property.2.le (hd.2 t)] at he
    exact he.symm
  change dist (LeftTruncation k f a d.val hd t) (L + regularIntegral k f h c d) < ε
  rw [heq, dist_add_right]
  exact hr tc (hts.trans hsr)

/-- Moving the regular lower endpoint subtracts the same fixed proper value. -/
theorem right_change_split (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) (R : S.scalarValue k)
    (hR : RightHasIntegral k f c.val b R) :
    RightHasIntegral k f d.val b (R - regularIntegral k f h c d) := by
  rcases hR with ⟨hc, hR⟩
  let hd := rightRegular_of_local k f h d
  refine ⟨hd, fun ε hε => ?_⟩
  obtain ⟨r, hr⟩ := hR ε hε
  have hrb : ((max r.val d.val : ℝ) : WithTop ℝ) < b := by
    rcases le_total r.val d.val with hrd | hdr
    · simpa [max_eq_right hrd] using d.property.2
    · simpa [max_eq_left hdr] using r.property.2
  obtain ⟨s, hms, hsb⟩ := exists_right_index hrb
  have hrs : r.val < s := (le_max_left _ _).trans_lt hms
  have hds : d.val < s := (le_max_right _ _).trans_lt hms
  refine ⟨⟨s, hds, hsb⟩, fun t hst => ?_⟩
  have hct : c.val < t.val := r.property.1.trans (hrs.trans hst)
  let tc : RightIndex c.val b := ⟨t.val, hct, t.property.2⟩
  let tp : RegularPoint a b := ⟨t.val,
    bot_coe_lt_of_le d.property.1 t.property.1.le, t.property.2⟩
  have heq : RightTruncation k f d.val b hd t =
      RightTruncation k f c.val b hc tc - regularIntegral k f h c d := by
    have he := regularIntegral_add k f h c d tp
    rw [regularIntegral_agreement k f h c tp hct.le (hc.2 tc),
      regularIntegral_agreement k f h d tp t.property.1.le (hd.2 t)] at he
    exact eq_sub_of_add_eq' he
  change dist (RightTruncation k f d.val b hd t) (R - regularIntegral k f h c d) < ε
  rw [heq, dist_sub_right]
  exact hr tc (hrs.trans hst)

theorem split_existence : splitExistence := by
  intro k f a b c
  constructor
  · rintro ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
    exact ⟨l+r, l, r, hl, hr, rfl⟩
  · rintro ⟨L, l, r, hl, hr, _⟩
    exact ⟨⟨l, hl⟩, ⟨r, hr⟩⟩

theorem split_unique : splitUnique := by
  intro k f a b c L M hL hM
  rcases hL with ⟨l, r, hl, hr, rfl⟩
  rcases hM with ⟨l', r', hl', hr', rfl⟩
  rw [left_unique k f a c.val l l' hl hl', right_unique k f c.val b r r' hr hr']

theorem split_integral_hasValue : splitIntegralHasValue := by
  intro k f a b c h
  exact ⟨_, _, left_integral_hasValue k f a c.val h.1,
    right_integral_hasValue k f c.val b h.2, rfl⟩

private theorem split_transfer (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {b : WithTop ℝ} (h : LocallyIntegrable k f a b)
    (c d : RegularPoint a b) (L : S.scalarValue k)
    (hL : HasIntegralAtSplit k f a b c L) : HasIntegralAtSplit k f a b d L := by
  rcases hL with ⟨l, r, hl, hr, rfl⟩
  refine ⟨l + regularIntegral k f h c d, r - regularIntegral k f h c d,
    left_change_split k f h c d l hl, right_change_split k f h c d r hr, ?_⟩
  abel

theorem split_independent : splitIndependent := by
  intro k f a b h c d L
  exact ⟨split_transfer k f h c d L, split_transfer k f h d c L⟩

theorem split_convergence_independent : splitConvergenceIndependent := by
  intro k f a b h c d
  rw [split_existence k f a b c, split_existence k f a b d]
  exact exists_congr (fun L => split_independent k f a b h c d L)

theorem split_value_independent : splitValueIndependent := by
  intro k f a b h c d hc hd
  exact split_unique k f a b d _ _
    ((split_independent k f a b h c d _).mp (split_integral_hasValue k f a b c hc))
    (split_integral_hasValue k f a b d hd)

theorem hasIntegral_at_every_split : hasIntegralAtEverySplit := by
  intro k f a b c L
  constructor
  · rintro ⟨h, d, hd⟩
    exact ⟨h, (split_independent k f a b h d c L).mp hd⟩
  · rintro ⟨h, hc⟩
    exact ⟨h, c, hc⟩

theorem integral_hasValue : integralHasValue := by
  intro k f a b h
  exact Classical.choose_spec h

theorem integral_eq : integralEq := by
  intro k f a b h L hL
  have hv := integral_hasValue k f a b h
  obtain ⟨hlocal, c, hc⟩ := hL
  exact split_unique k f a b c _ L
    ((hasIntegral_at_every_split k f a b c _).mp hv).2 hc

theorem no_cancellation : noCancellation := by
  intro k f a b c hn ⟨L, hL⟩
  have hc := (split_existence k f a b c).mpr
    ⟨L, ((hasIntegral_at_every_split k f a b c L).mp hL).2⟩
  exact hn.elim (fun hl => hl hc.1) (fun hr => hr hc.2)

/-- Every regular component keeps its own two one-sided limits. -/
theorem finite_independent : finiteIndependent := by
  intro k f n a b s c d L
  constructor
  · rintro ⟨v, hv, hsum⟩
    refine ⟨v, fun i => ⟨(hv i).1, ?_⟩, hsum⟩
    exact (split_independent k f _ _ (hv i).1 (c i) (d i) (v i)).mp (hv i).2
  · rintro ⟨v, hv, hsum⟩
    refine ⟨v, fun i => ⟨(hv i).1, ?_⟩, hsum⟩
    exact (split_independent k f _ _ (hv i).1 (d i) (c i) (v i)).mp (hv i).2

theorem finite_convergence_independent : finiteConvergenceIndependent := by
  intro k f n a b s c d
  exact exists_congr (fun L => finite_independent k f n a b s c d L)

theorem finite_unique : finiteUnique := by
  intro k f n a b s c L M hL hM
  rcases hL with ⟨v, hv, rfl⟩
  rcases hM with ⟨w, hw, rfl⟩
  exact Finset.sum_congr rfl (fun i _ => split_unique k f _ _ (c i) _ _ (hv i).2 (hw i).2)

theorem finite_integral_hasValue : finiteIntegralHasValue := by
  intro k f n a b s c h
  exact Classical.choose_spec h

theorem finite_value_independent : finiteValueIndependent := by
  intro k f n a b s c d hc hd
  exact finite_unique k f n a b s d _ _
    ((finite_independent k f n a b s c d _).mp (finite_integral_hasValue k f n a b s c hc))
    (finite_integral_hasValue k f n a b s d hd)

theorem finite_existence : finiteExistence := by
  intro k f n a b s c
  constructor
  · rintro ⟨L, v, hv, _⟩ i
    have hi := (split_existence k f _ _ (c i)).mpr ⟨v i, (hv i).2⟩
    exact ⟨(hv i).1, hi.1, hi.2⟩
  · intro hc
    have hi : ∀ i, ConvergesAtSplit k f _ _ (c i) := fun i => ⟨(hc i).2.1, (hc i).2.2⟩
    let v := fun i => integralAtSplit k f _ _ (c i) (hi i)
    exact ⟨∑ i, v i, v, fun i => ⟨(hc i).1, split_integral_hasValue k f _ _ (c i) (hi i)⟩, rfl⟩

/-- Density of the real line supplies every regular split for a finite sorted
singular list. This also covers n=0 and infinite outer endpoints. -/
theorem splitFamily_exists : splitFamilyExists := by
  intro n a b s hnonempty hmono hbounds
  classical
  suffices hh : ∀ i : Fin (n+1), Nonempty (regularPointValue
      (componentLeft n a s i) (componentRight n b s i)) from
    ⟨fun i => Classical.choice (hh i)⟩
  intro i
  by_cases hi : i.val = 0
  · by_cases hn : i.val < n
    · obtain ⟨y, hay, hys⟩ := exists_left_index (hbounds ⟨i.val, hn⟩).1
      exact ⟨⟨y, by simpa [componentLeft, componentLeftValue, hi] using hay,
        by simpa [componentRight, componentRightValue, hn] using
          (WithTop.coe_lt_coe.mpr hys)⟩⟩
    · have hn' : ¬ 0 < n := by omega
      simpa [componentLeft, componentLeftValue, hi,
        componentRight, componentRightValue, hn'] using hnonempty
  · let j : Fin n := ⟨i.val-1, by omega⟩
    by_cases hn : i.val < n
    · have hlt : s j < s ⟨i.val, hn⟩ := hmono (by change i.val - 1 < i.val; omega)
      obtain ⟨y, hsy, hys⟩ := exists_between hlt
      exact ⟨⟨y, by simpa [componentLeft, componentLeftValue, hi, j] using
          (WithBot.coe_lt_coe.mpr hsy),
        by simpa [componentRight, componentRightValue, hn] using
          (WithTop.coe_lt_coe.mpr hys)⟩⟩
    · obtain ⟨y, hsy, hyb⟩ := exists_right_index (hbounds j).2
      exact ⟨⟨y, by simpa [componentLeft, componentLeftValue, hi, j] using
          (WithBot.coe_lt_coe.mpr hsy),
        by simpa [componentRight, componentRightValue, hn] using hyb⟩⟩

theorem finite_zero : finiteZero := by
  intro k f a b s c L
  constructor
  · rintro ⟨v, hv, hL⟩
    have hL' : L = v 0 := by simpa using hL
    simpa [hL', componentLeftValue, componentRightValue] using hv 0
  · rintro ⟨hlocal, hL⟩
    refine ⟨fun _ => L, ?_, by simp⟩
    intro i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    exact ⟨hlocal, hL⟩

theorem finite_no_cancellation : finiteNoCancellation := by
  intro k f n a b s c i hn hc
  have hi := (finite_existence k f n a b s c).mp hc i
  exact hn.elim (fun hl => hl hi.2.1) (fun hr => hr hi.2.2)

end SingleVariableAnalysis.Riemann.Improper
