import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Ekeland
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set Filter Topology

namespace ExpandedFA.P1

/-- The descent relation used in Ekeland's principle. -/
def Descent {X : Type*} [MetricSpace X] (f : X → ℝ) (a : ℝ) (x y : X) : Prop :=
  f y + a * dist y x ≤ f x

lemma descent_refl {X : Type*} [MetricSpace X] (f : X → ℝ) (a : ℝ) (x : X) :
    Descent f a x x := by simp [Descent]

lemma descent_trans {X : Type*} [MetricSpace X] {f : X → ℝ} {a : ℝ}
    (ha : 0 ≤ a) {x y z : X} (hxy : Descent f a x y) (hyz : Descent f a y z) :
    Descent f a x z := by
  dsimp [Descent] at *
  have := mul_le_mul_of_nonneg_left (dist_triangle z y x) ha
  linarith

lemma descent_closed {X : Type*} [MetricSpace X] {f : X → ℝ}
    (hf : LowerSemicontinuous f) (a : ℝ) (x : X) :
    IsClosed {y | Descent f a x y} := by
  exact (hf.add (continuous_const.mul (continuous_id.dist continuous_const)).lowerSemicontinuous).isClosed_preimage (f x)

/-- A complete metric descent relation has a terminal point. -/
theorem exists_terminal_descent {X : Type*} [MetricSpace X] [CompleteSpace X]
    {f : X → ℝ} (hf : LowerSemicontinuous f) (hb : BddBelow (range f))
    {a : ℝ} (ha : 0 < a) (x₀ : X) :
    ∃ z, Descent f a x₀ z ∧ ∀ y, Descent f a z y → y = z := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have hchoice : ∀ x : X, ∀ n : ℕ, ∃ y, Descent f a x y ∧
      ∀ w, Descent f a x w → f y < f w + e n := by
    intro x n
    let s := f '' {y | Descent f a x y}
    have hs : s.Nonempty := ⟨f x, x, descent_refl f a x, rfl⟩
    have hbs : BddBelow s := hb.mono (image_subset_range _ _)
    obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt hs (lt_add_of_pos_right (sInf s) (he n))
    rcases hv with ⟨y, hy, rfl⟩
    refine ⟨y, hy, fun w hw => ?_⟩
    exact hvlt.trans_le (add_le_add (csInf_le hbs ⟨w, hw, rfl⟩) (le_refl (e n)))
  choose next hnext happrox using hchoice
  let u : ℕ → X := fun n => Nat.rec x₀ (fun n x => next x n) n
  have hu0 : u 0 = x₀ := rfl
  have hus : ∀ n, u (n+1) = next (u n) n := fun n => rfl
  have hstep (n : ℕ) : Descent f a (u n) (u (n+1)) := by
    rw [hus]; exact hnext _ _
  have hchain : ∀ n m : ℕ, n ≤ m → Descent f a (u n) (u m) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact descent_refl _ _ _
    | succ m hm ih => exact descent_trans ha.le ih (hstep m)
  have hmono : Antitone (fun n => f (u n)) := by
    intro n m hnm
    have hd := hchain n m hnm
    have hp := mul_nonneg ha.le (dist_nonneg (x := u m) (y := u n))
    dsimp [Descent] at hd
    linarith
  have hfb : BddBelow (range (fun n => f (u n))) := hb.mono (range_comp_subset_range u f)
  obtain ⟨l, hl⟩ : ∃ l : ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciInf hmono hfb⟩
  have hlower (n : ℕ) : l ≤ f (u n) := hmono.le_of_tendsto hl n
  have hbound (n m : ℕ) (hnm : n ≤ m) :
      dist (u m) (u n) ≤ (f (u n) - l) / a := by
    apply (le_div_iff₀ ha).2
    have hd := hchain n m hnm
    dsimp [Descent] at hd
    have := hlower m
    nlinarith
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff'.2
    intro ε hε
    have ht : Tendsto (fun n => (f (u n) - l) / a) atTop (𝓝 0) := by
      simpa using (hl.sub_const l).div_const a
    obtain ⟨N, hN⟩ := (eventually_atTop.1 ((tendsto_order.1 ht).2 ε hε))
    refine ⟨N, fun n hn => ?_⟩
    exact (hbound N n hn).trans_lt (hN N le_rfl)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  have hzS (n : ℕ) : Descent f a (u n) z := by
    apply (descent_closed hf a (u n)).mem_of_tendsto hz
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hchain n m hm
  refine ⟨z, by simpa [hu0] using hzS 0, ?_⟩
  intro y hy
  have hyS (n : ℕ) : Descent f a (u n) y := descent_trans ha.le (hzS n) hy
  have hzle (n : ℕ) : f z ≤ f (u n) := by
    have hd := hzS n
    have hp := mul_nonneg ha.le (dist_nonneg (x := z) (y := u n))
    dsimp [Descent] at hd
    linarith
  have hsmall (n : ℕ) : a * dist y z < e n := by
    have hv : f (u (n+1)) < f y + e n := by
      rw [hus]; exact happrox _ _ y (hyS n)
    have hvz := hzle (n+1)
    dsimp [Descent] at hy
    linarith
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa [e] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hzero : a * dist y z ≤ 0 := ge_of_tendsto he0 (Eventually.of_forall fun n => (hsmall n).le)
  have : dist y z = 0 := by nlinarith [dist_nonneg (x := y) (y := z)]
  exact dist_eq_zero.1 this

/-- Ekeland's quantitative conclusion for a real-valued function. The universal
near-minimum bound is equivalent to the usual bound using the infimum. -/
theorem ekeland_real {X : Type*} [MetricSpace X] [CompleteSpace X]
    {f : X → ℝ} (hf : LowerSemicontinuous f) (hb : BddBelow (range f))
    (x₀ : X) {a r : ℝ} (ha : 0 < a)
    (hnear : ∀ y, f x₀ ≤ f y + a * r) :
    ∃ z, dist z x₀ ≤ r ∧ f z ≤ f x₀ ∧
      ∀ y, y ≠ z → f z - a * dist y z < f y := by
  obtain ⟨z, hz, hterminal⟩ := exists_terminal_descent hf hb ha x₀
  have hp := mul_nonneg ha.le (dist_nonneg (x := z) (y := x₀))
  have hn := hnear z
  dsimp [Descent] at hz
  refine ⟨z, ?_, by linarith, ?_⟩
  · nlinarith
  · intro y hy
    by_contra h
    have hd : Descent f a z y := by dsimp [Descent]; linarith
    exact hy (hterminal y hd)

/-- Capping an extended-real function at a real height produces a real function. -/
noncomputable def capReal {X : Type*} (F : X → EReal) (c : ℝ) (x : X) : ℝ :=
  (min (F x) (c : EReal)).toReal

lemma coe_capReal {X : Type*} (F : X → EReal) (hbot : ∀ x, F x ≠ ⊥)
    (c : ℝ) (x : X) : (capReal F c x : EReal) = min (F x) (c : EReal) := by
  apply EReal.coe_toReal
  · exact ne_of_lt ((min_le_right _ _).trans_lt (EReal.coe_lt_top c))
  · exact min_ne_bot (hbot x) (EReal.coe_ne_bot c)

lemma lowerSemicontinuous_capReal {X : Type*} [TopologicalSpace X]
    {F : X → EReal} (hf : LowerSemicontinuous F) (hbot : ∀ x, F x ≠ ⊥) (c : ℝ) :
    LowerSemicontinuous (capReal F c) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro t
  by_cases hct : c ≤ t
  · have heq : capReal F c ⁻¹' Iic t = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      apply EReal.coe_le_coe_iff.1
      rw [coe_capReal F hbot c x]
      exact (min_le_right _ _).trans (EReal.coe_le_coe hct)
    rw [heq]; exact isClosed_univ
  · have heq : capReal F c ⁻¹' Iic t = F ⁻¹' Iic (t : EReal) := by
      ext x
      change capReal F c x ≤ t ↔ F x ≤ (t : EReal)
      rw [← EReal.coe_le_coe_iff, coe_capReal F hbot c x, min_le_iff]
      simp only [EReal.coe_le_coe_iff, hct, or_false]
    rw [heq]
    exact hf.isClosed_preimage _

/-- Ekeland's variational principle for proper lower-semicontinuous
extended-real functions on an arbitrary complete metric space. -/
theorem ekeland : Specs.ExpandedFA.P1.Ekeland := by
  intro X _ _ F hf hb hproper x₀ a r ha hr hnear
  obtain ⟨b, hb⟩ := hb
  have hbot : ∀ x, F x ≠ ⊥ := fun x => ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (hb x)
  obtain ⟨p, hp⟩ := hproper
  have hinf : (⨅ x, F x) ≠ ⊤ :=
    ne_of_lt ((iInf_le F p).trans_lt (lt_top_iff_ne_top.2 hp))
  have hfinite : F x₀ ≠ ⊤ :=
    ne_of_lt (hnear.trans_lt (EReal.add_lt_top hinf (EReal.coe_ne_top _)))
  let q : ℝ := (F x₀).toReal
  have hq : (q : EReal) = F x₀ := EReal.coe_toReal hfinite (hbot x₀)
  let c : ℝ := q + 1
  let f := capReal F c
  have hcoe (x : X) : (f x : EReal) = min (F x) (c : EReal) := coe_capReal F hbot c x
  have hf0 : f x₀ = q := by
    apply EReal.coe_injective
    rw [hcoe, ← hq, min_eq_left]
    exact EReal.coe_le_coe (by dsimp [c]; linarith)
  have hfb : BddBelow (range f) := by
    refine ⟨min b c, ?_⟩
    rintro _ ⟨x, rfl⟩
    apply EReal.coe_le_coe_iff.1
    rw [hcoe]
    exact le_min ((EReal.coe_le_coe (min_le_left b c)).trans (hb x))
      (EReal.coe_le_coe (min_le_right b c))
  have hfn : ∀ y, f x₀ ≤ f y + a * r := by
    intro y
    apply EReal.coe_le_coe_iff.1
    rw [hf0, EReal.coe_add, hq, hcoe]
    have hny : F x₀ ≤ F y + ((a * r : ℝ) : EReal) :=
      hnear.trans (add_le_add (iInf_le F y) le_rfl)
    rw [← min_add_add_right]
    apply le_min hny
    rw [← hq, ← EReal.coe_add]
    apply EReal.coe_le_coe
    dsimp [c]
    nlinarith
  obtain ⟨z, hdist, hz, hstrict⟩ :=
    ekeland_real (lowerSemicontinuous_capReal hf hbot c) hfb x₀ ha hfn
  change f z ≤ f x₀ at hz
  have hzc : (f z : EReal) < (c : EReal) := by
    apply EReal.coe_lt_coe
    rw [hf0] at hz
    dsimp [c]
    linarith
  have hzF : (f z : EReal) = F z := by
    rw [hcoe] at hzc ⊢
    exact min_eq_left (le_of_lt ((min_lt_iff.1 hzc).resolve_right (lt_irrefl _)))
  refine ⟨z, hdist, ?_, ?_⟩
  · rw [← hzF, ← hq]
    exact EReal.coe_le_coe (by simpa [hf0] using hz)
  · intro y hy
    rw [← hzF, ← EReal.coe_sub]
    exact (EReal.coe_lt_coe (hstrict y hy)).trans_le (by rw [hcoe]; exact min_le_left _ _)

end ExpandedFA.P1
