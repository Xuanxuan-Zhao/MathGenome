import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientProductCounterexample
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The quotient product counterexample (paper.tex, d10:03:quotient-product-failure).
We use irrational aₙ in (0, 1/(n+1)), which may replace the paper's
√2/(n+1). The open strips contain every collapsed fiber. A product
neighborhood at (q 1, 0) would contain a point on a strip's excluded cone,
contradicting saturation and the disjointness of the integer strips.
-/

open Set Topology

namespace D10Topology.Ch03.IntegerCollapse

theorem class_eq (x y : ℝ) :
    q x = q y ↔ x = y ∨ (x ∈ positiveIntegers ∧ y ∈ positiveIntegers) :=
  Quotient.eq

private theorem small_irrational_exists (n : ℕ) :
    ∃ a : ℝ, Irrational a ∧ 0 < a ∧ a < 1 / ((n : ℝ) + 1) :=
  exists_irrational_btwn (by positivity)

private noncomputable def a (n : ℕ) : ℝ :=
  Classical.choose (small_irrational_exists n)

private theorem a_properties (n : ℕ) :
    Irrational (a n) ∧ 0 < a n ∧ a n < 1 / ((n : ℝ) + 1) :=
  Classical.choose_spec (small_irrational_exists n)

/-- The n-th strip, indexed by n+1 so that ℕ starts at zero. -/
private def strip (n : ℕ) : Set (ℝ × ℚ) :=
  {p | |p.1 - ((n : ℝ) + 1)| < 1/4 ∧
    |p.1 - ((n : ℝ) + 1)| < |(p.2 : ℝ) - a n|}

private def witness : Set (ℝ × ℚ) := ⋃ n : ℕ, strip n

private theorem strip_open (n : ℕ) : IsOpen (strip n) := by
  apply IsOpen.inter
  · exact isOpen_lt (continuous_fst.sub continuous_const).abs continuous_const
  · exact isOpen_lt (continuous_fst.sub continuous_const).abs
      ((Rat.continuous_coe_real.comp continuous_snd).sub continuous_const).abs

private theorem witness_open : IsOpen witness :=
  isOpen_iUnion strip_open

private theorem integer_mem_witness (n : ℕ) (r : ℚ) :
    (((n : ℝ) + 1), r) ∈ witness := by
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  change |(n : ℝ) + 1 - ((n : ℝ) + 1)| < 1/4 ∧
    |(n : ℝ) + 1 - ((n : ℝ) + 1)| < |(r : ℝ) - a n|
  simp only [sub_self, abs_zero]
  refine ⟨by norm_num, abs_pos.mpr ?_⟩
  intro h
  exact (a_properties n).1 ⟨r, (sub_eq_zero.mp h)⟩

private theorem witness_saturated :
    productMap ⁻¹' (productMap '' witness) = witness := by
  apply Subset.antisymm
  · rintro ⟨x, r⟩ ⟨⟨y, s⟩, hy, heq⟩
    have hq : q y = q x := congrArg Prod.fst heq
    have hr : s = r := congrArg Prod.snd heq
    subst s
    rcases (class_eq y x).mp hq with h | ⟨_, hx⟩
    · simpa only [h] using hy
    · obtain ⟨n, rfl⟩ := hx
      exact integer_mem_witness n r
  · exact subset_preimage_image productMap witness

private theorem strip_index_unique (n m : ℕ) (t : ℝ)
    (ht : 0 < t) (ht' : t < 1/4)
    (hm : |((n : ℝ) + 1 + t) - ((m : ℝ) + 1)| < 1/4) : m = n := by
  have hb := abs_lt.mp hm
  rcases lt_trichotomy m n with h | h | h
  · have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith
  · exact h
  · have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith

private theorem witness_image_not_open : ¬ IsOpen (productMap '' witness) := by
  intro hopen
  have hb : (q 1, (0 : ℚ)) ∈ productMap '' witness := by
    exact ⟨(1, 0), by simpa using integer_mem_witness 0 0, rfl⟩
  obtain ⟨W, R, hW, hbW, hR, h0R, hWR⟩ :=
    mem_nhds_prod_iff'.mp (hopen.mem_nhds hb)
  obtain ⟨δ, hδ, hδR⟩ := Metric.mem_nhds_iff.mp (hR.mem_nhds h0R)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have han : a n < δ := (a_properties n).2.2.trans hn
  have hapos : 0 < a n := (a_properties n).2.1
  have hq : q ((n : ℝ) + 1) = q 1 := by
    apply (class_eq _ _).mpr
    exact Or.inr ⟨⟨n, rfl⟩, ⟨0, by norm_num⟩⟩
  have hpre : IsOpen (q ⁻¹' W) :=
    (show IsOpen W ↔ IsOpen (q ⁻¹' W) from Iff.rfl).mp hW
  have hnW : (n : ℝ) + 1 ∈ q ⁻¹' W := by
    change q ((n : ℝ) + 1) ∈ W
    rwa [hq]
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hnW)
  let t : ℝ := min η (1/4) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htη : t < η := by
    have := min_le_left η (1/4 : ℝ)
    dsimp [t]
    linarith
  have htquarter : t < 1/4 := by
    have := min_le_right η (1/4 : ℝ)
    dsimp [t]
    linarith
  have hgap : max (-δ) (a n - t) < min δ (a n + t) := by
    apply max_lt
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hgap
  have hrδ : |(r : ℝ)| < δ := by
    exact abs_lt.mpr ⟨(le_max_left _ _).trans_lt hrlo,
      hrhi.trans_le (min_le_left _ _)⟩
  have hrat : |(r : ℝ) - a n| < t := by
    apply abs_lt.mpr
    constructor
    · have := (le_max_right _ _).trans_lt hrlo
      linarith
    · have := hrhi.trans_le (min_le_right _ _)
      linarith
  have hrR : r ∈ R := hδR (by
    change dist r 0 < δ
    rw [Rat.dist_eq, Rat.cast_zero, sub_zero]
    exact hrδ)
  have hxW : q ((n : ℝ) + 1 + t) ∈ W := by
    apply hηW
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htη
  have hv : productMap (((n : ℝ) + 1 + t), r) ∈ productMap '' witness :=
    hWR ⟨hxW, hrR⟩
  have hu : (((n : ℝ) + 1 + t), r) ∈ witness := by
    rw [← witness_saturated]
    exact hv
  obtain ⟨m, hm⟩ := mem_iUnion.mp hu
  change |((n : ℝ) + 1 + t) - ((m : ℝ) + 1)| < 1/4 ∧
    |((n : ℝ) + 1 + t) - ((m : ℝ) + 1)| < |(r : ℝ) - a m| at hm
  have hmn : m = n := strip_index_unique n m t ht htquarter hm.1
  subst m
  have hwrong : t < |(r : ℝ) - a n| := by
    simpa [abs_of_pos ht] using hm.2
  exact (lt_asymm hrat hwrong)

/-- The class map for the specified quotient topology is quotient. -/
theorem q_quotient : QuotientMap q :=
  equivalenceQuotient_classMap collapseSetoid

/-- The exact counterexample from the paper. -/
theorem counterexample :
    QuotientMap q ∧ QuotientMap (id : ℚ → ℚ) ∧ ¬ QuotientMap productMap := by
  refine ⟨q_quotient, ⟨Function.surjective_id, fun _ => Iff.rfl⟩, ?_⟩
  intro h
  apply witness_image_not_open
  apply (h.2 (productMap '' witness)).mpr
  rw [witness_saturated]
  exact witness_open

end D10Topology.Ch03.IntegerCollapse
