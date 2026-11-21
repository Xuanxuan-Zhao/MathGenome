import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.BalancedIncidenceSets
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Field

noncomputable section

namespace ExpandedFA.AP.BalancedIncidenceSets
open ExpandedFA.AP.Incidence
open scoped BigOperators

lemma growthFactor_pos : 0 < growthFactor := by norm_num [growthFactor]
lemma one_le_growthFactor : 1 ≤ growthFactor := by norm_num [growthFactor]

lemma one_le_dimension (offset m : ℕ) : 1 ≤ dimension offset m := by
  apply (Nat.le_floor_iff (pow_nonneg growthFactor_pos.le _)).2
  simpa using one_le_pow₀ one_le_growthFactor

/-- Taking the floor loses at most a factor of two for powers at least one. -/
lemma half_pow_le_dimension (offset m : ℕ) :
    growthFactor ^ (m + offset) / 2 ≤ (dimension offset m : ℝ) := by
  have h : (1 : ℝ) ≤ dimension offset m := by exact_mod_cast one_le_dimension offset m
  have hfloor := Nat.lt_floor_add_one (growthFactor ^ (m + offset))
  change growthFactor ^ (m + offset) < (dimension offset m : ℝ) + 1 at hfloor
  linarith

lemma dimension_at_least_two (offset m : ℕ) (h : 4 ≤ offset) :
    2 ≤ dimension offset m := by
  apply (Nat.le_floor_iff (pow_nonneg growthFactor_pos.le _)).2
  have hp : growthFactor ^ 4 ≤ growthFactor ^ (m + offset) :=
    pow_le_pow_right₀ one_le_growthFactor (by omega)
  have h4 : (2 : ℝ) ≤ growthFactor ^ 4 := by norm_num [growthFactor]
  exact h4.trans hp

lemma reciprocal_dimension_le (offset m : ℕ) :
    1 / (dimension offset m : ℝ) ≤ 2 * ((5 / 6 : ℝ) ^ m) := by
  have hd : (0 : ℝ) < dimension offset m := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_dimension offset m)
  have hp : 0 < growthFactor ^ (m + offset) := pow_pos growthFactor_pos _
  have hhalf := half_pow_le_dimension offset m
  have hpow : growthFactor ^ m ≤ growthFactor ^ (m + offset) :=
    pow_le_pow_right₀ one_le_growthFactor (Nat.le_add_right m offset)
  calc
    1 / (dimension offset m : ℝ) ≤ 2 / growthFactor ^ (m + offset) := by
      apply (div_le_div_iff₀ hd hp).2
      linarith
    _ ≤ 2 / growthFactor ^ m := by
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos growthFactor_pos m) hpow
    _ = 2 * ((5 / 6 : ℝ) ^ m) := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num [growthFactor]

/-- The source's reciprocal-dimension series is dominated by a geometric series. -/
theorem reciprocal_dimensions_summable :
    Specs.ExpandedFA.AP.BalancedIncidenceSets.reciprocalDimensionsSummable := by
  intro offset
  have hg : Summable (fun m : ℕ => 2 * ((5 / 6 : ℝ) ^ m)) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6)
      (by norm_num : (5 / 6 : ℝ) < 1)).mul_left 2
  exact hg.of_nonneg_of_le (fun m => by positivity) (reciprocal_dimension_le offset)

/-- Elementary exponential bounds suffice in place of Stirling's formula. -/
lemma walsh_size_upper (n : ℕ) : ExpandedFA.AP.Walsh.levelSize n ≤ 4 ^ n := by
  calc
    ExpandedFA.AP.Walsh.levelSize n ≤ Nat.centralBinom n :=
      Nat.choose_le_centralBinom (n - 1) n
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

lemma walsh_size_central_identity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) * ExpandedFA.AP.Walsh.levelSize n = n * Nat.centralBinom n := by
  have h := Nat.choose_succ_right_eq (2 * n) (n - 1)
  have hn1 : n - 1 + 1 = n := by omega
  have hsub : 2 * n - (n - 1) = n + 1 := by omega
  rw [hn1, hsub] at h
  simpa [ExpandedFA.AP.Walsh.levelSize, Nat.centralBinom, mul_comm] using h.symm

lemma walsh_size_lower (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * n * ExpandedFA.AP.Walsh.levelSize n := by
  have hcentral := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hid := walsh_size_central_identity n hn
  have hc : Nat.centralBinom n ≤ 2 * ExpandedFA.AP.Walsh.levelSize n := by
    nlinarith
  nlinarith

/-- The row block selected by a position in the source's list. -/
def listBlock (k s j : ℕ) : ℕ := j % (k / s)

def listColumn (k t s j : ℕ) : ℕ := (j / (k / s)) % t

def listSlope (k t s j : ℕ) : ℕ := j / ((k / s) * t)

lemma quotient_pos {k s : ℕ} (hs : 0 < s) (hsk : s ≤ k) : 0 < k / s :=
  Nat.div_pos hsk hs

/-- An individual point in a set cut from a cyclic list. The row numbers in
its column formula start at one, as in the manuscript. -/
def cyclicPoint (k t s : ℕ) (ht : 0 < t) (hs : 0 < s) (hsk : s ≤ k)
    (j : ℕ) (u : Fin s) : Fin k × Fin t :=
  (⟨listBlock k s j * s + u.val, by
    have hb : listBlock k s j < k / s := Nat.mod_lt j (quotient_pos hs hsk)
    have hmul : (k / s) * s ≤ k := Nat.div_mul_le_self k s
    have hu := u.isLt
    nlinarith⟩,
   ⟨((listBlock k s j * s + u.val + 1) * listSlope k t s j +
      listColumn k t s j) % t, Nat.mod_lt _ ht⟩)

lemma cyclicPoint_injective (k t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (j : ℕ) : Function.Injective (cyclicPoint k t s ht hs hsk j) := by
  intro u v huv
  have hrow := congrArg (fun e : Fin k × Fin t => e.1.val) huv
  simp only [cyclicPoint] at hrow
  apply Fin.ext
  omega

/-- The `j`th set, with no division of row lengths and no repeated rows. -/
def cyclicSet (k t s : ℕ) (ht : 0 < t) (hs : 0 < s) (hsk : s ≤ k)
    (j : ℕ) : Finset (Fin k × Fin t) :=
  Finset.univ.image (cyclicPoint k t s ht hs hsk j)

lemma cyclicSet_card (k t s : ℕ) (ht : 0 < t) (hs : 0 < s) (hsk : s ≤ k)
    (j : ℕ) : (cyclicSet k t s ht hs hsk j).card = s := by
  rw [cyclicSet, Finset.card_image_of_injective _
    (cyclicPoint_injective k t s ht hs hsk j)]
  simp

lemma cyclicSet_one_per_row (k t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (j : ℕ) (r : Fin k) :
    ((cyclicSet k t s ht hs hsk j).filter (fun e => e.1 = r)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, har⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbr⟩ := Finset.mem_filter.mp hb
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
  have he : u = v := by
    have hrow := congrArg Fin.val (har.trans hbr.symm)
    simp only [cyclicPoint] at hrow
    apply Fin.ext
    omega
  rw [he]

/-- Collision of two affine functions modulo `t` forces a quantitative gap
between distinct rows. No primality or coprimality assumption on `t` is used. -/
lemma modular_collision_spacing (t r R ρ σ κ κ₂ v : ℕ)
    (hr : r < R) (hρσ : ρ ≠ σ) (hρ : ρ < v) (hσ : σ < v)
    (h₁ : (r * ρ + κ) % t = (r * σ + κ₂) % t)
    (h₂ : (R * ρ + κ) % t = (R * σ + κ₂) % t) :
    t ≤ (R - r) * v := by
  have hd₁ := (Nat.modEq_iff_dvd.mp h₁)
  have hd₂ := (Nat.modEq_iff_dvd.mp h₂)
  have hd : (t : ℤ) ∣ ((R : ℤ) - r) * ((σ : ℤ) - ρ) := by
    convert dvd_sub hd₂ hd₁ using 1
    push_cast
    ring
  have hne : ((R : ℤ) - r) * ((σ : ℤ) - ρ) ≠ 0 := by
    apply mul_ne_zero
    · omega
    · omega
  have hle := Int.natAbs_le_of_dvd_ne_zero hd hne
  have habs : ((R : ℤ) - r).natAbs = R - r := by
    rw [← Int.natCast_sub hr.le, Int.natAbs_natCast]
  rw [Int.natAbs_natCast, Int.natAbs_mul, habs] at hle
  exact hle.trans (Nat.mul_le_mul_left _
    (Int.natAbs_coe_sub_coe_le_of_le hσ.le hρ.le))

lemma cyclicSet_column (k t s : ℕ) (ht : 0 < t) (hs : 0 < s) (hsk : s ≤ k)
    (j : ℕ) (e : Fin k × Fin t) (he : e ∈ cyclicSet k t s ht hs hsk j) :
    e.2.val = ((e.1.val + 1) * listSlope k t s j + listColumn k t s j) % t := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  rfl

lemma cyclicSet_block (k t s : ℕ) (ht : 0 < t) (hs : 0 < s) (hsk : s ≤ k)
    (j : ℕ) (e : Fin k × Fin t) (he : e ∈ cyclicSet k t s ht hs hsk j) :
    e.1.val / s = listBlock k s j := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  simp only [cyclicPoint]
  rw [Nat.mul_comm (listBlock k s j) s, Nat.mul_add_div hs, Nat.div_eq_of_lt u.isLt, add_zero]

lemma listIndex_identity (k t s j : ℕ) :
    j = listBlock k s j + (k / s) * listColumn k t s j +
      ((k / s) * t) * listSlope k t s j := by
  dsimp [listBlock, listColumn, listSlope]
  have h₁ := Nat.mod_add_div j (k / s)
  have h₂ := congrArg (fun x => (k / s) * x) (Nat.mod_add_div (j / (k / s)) t)
  rw [Nat.div_div_eq_div_mul] at h₂
  nlinarith

/-- In one slope-list the sets are disjoint, including across column cuts. -/
lemma cyclicSet_disjoint_same_slope (k t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (i j : ℕ) (hij : i ≠ j)
    (hρ : listSlope k t s i = listSlope k t s j) :
    Disjoint (cyclicSet k t s ht hs hsk i) (cyclicSet k t s ht hs hsk j) := by
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hbi := cyclicSet_block k t s ht hs hsk i e hei
  have hbj := cyclicSet_block k t s ht hs hsk j e hej
  have hci := cyclicSet_column k t s ht hs hsk i e hei
  have hcj := cyclicSet_column k t s ht hs hsk j e hej
  have hκ : listColumn k t s i = listColumn k t s j := by
    have he : ((e.1.val + 1) * listSlope k t s i + listColumn k t s i) ≡
        ((e.1.val + 1) * listSlope k t s i + listColumn k t s j) [MOD t] := by
      simpa only [Nat.ModEq, hρ] using hci.symm.trans hcj
    have hc := Nat.ModEq.add_left_cancel' ((e.1.val + 1) * listSlope k t s i) he
    exact hc.eq_of_lt_of_lt (Nat.mod_lt _ ht) (Nat.mod_lt _ ht)
  apply hij
  have hi := listIndex_identity k t s i
  have hj := listIndex_identity k t s j
  rw [hbi.symm.trans hbj, hκ, hρ] at hi
  exact hi.trans hj.symm

/-- Packing separated indices into an interval. The bucket map gives the
bound directly, without an enumeration or a minimum-spacing limit argument. -/
lemma spaced_card_le (s t v : ℕ) (ht : 0 < t) (A : Finset (Fin s))
    (hgap : ∀ a ∈ A, ∀ b ∈ A, a.val < b.val → t ≤ (b.val - a.val) * v) :
    A.card ≤ s * v / t + 1 := by
  have hg : ∀ a ∈ A, ∀ b ∈ A, a.val < b.val → a.val * v / t ≠ b.val * v / t := by
    intro a ha b hb hab he
    have hsep := hgap a ha b hb hab
    have hda := Nat.mod_add_div (a.val * v) t
    have hdb := Nat.mod_add_div (b.val * v) t
    have hma := Nat.mod_lt (a.val * v) ht
    have hmb := Nat.mod_lt (b.val * v) ht
    have hsub : (b.val - a.val) * v + a.val * v = b.val * v := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hab.le]
    rw [he] at hda
    omega
  calc
    A.card ≤ (Finset.range (s * v / t + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin s => a.val * v / t)
      · intro a ha
        apply Finset.mem_range.mpr
        have hmul := Nat.mul_le_mul_right v a.isLt.le
        have hdiv := Nat.div_le_div_right hmul (c := t)
        exact Nat.lt_succ_of_le hdiv
      · intro a ha b hb he
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hab | hab
        · exact hg a ha b hb hab he
        · exact hg b hb a ha hab he.symm
    _ = s * v / t + 1 := Finset.card_range _

/-- The position inside the selected block determines a point of a cyclic set. -/
lemma cyclicSet_position_injOn (k t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (i : ℕ) :
    Set.InjOn (fun e : Fin k × Fin t => (⟨e.1.val % s, Nat.mod_lt _ hs⟩ : Fin s))
      (cyclicSet k t s ht hs hsk i) := by
  intro e he f hf hef
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf
  have heq := congrArg Fin.val hef
  simp [cyclicPoint, Nat.add_mod, Nat.mod_eq_of_lt u.isLt,
    Nat.mod_eq_of_lt w.isLt] at heq
  exact congrArg (cyclicPoint k t s ht hs hsk i) (Fin.ext heq)

/-- The finite quantitative intersection estimate, before its asymptotic
specialization. The `+1` includes the possible first common row. -/
lemma cyclicSet_intersection_bound (k t s q : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (i j : Fin q) (hij : i ≠ j) :
    ((cyclicSet k t s ht hs hsk i ∩ cyclicSet k t s ht hs hsk j).card : ℝ) ≤
      1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t := by
  let v := q / ((k / s) * t) + 1
  by_cases hρ : listSlope k t s i = listSlope k t s j
  · have hd := cyclicSet_disjoint_same_slope k t s ht hs hsk i j
      (fun h => hij (Fin.ext h)) hρ
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, Nat.cast_zero]
    positivity
  let B := cyclicSet k t s ht hs hsk i ∩ cyclicSet k t s ht hs hsk j
  let f : Fin k × Fin t → Fin s := fun e => ⟨e.1.val % s, Nat.mod_lt _ hs⟩
  let A : Finset (Fin s) := B.image f
  have hf : Set.InjOn f B :=
    (cyclicSet_position_injOn k t s ht hs hsk i).mono (by
      intro e he
      exact (Finset.mem_inter.mp he).1)
  have hcard : A.card = B.card := Finset.card_image_of_injOn hf
  have hvi : listSlope k t s i < v := by
    have h := Nat.div_le_div_right (c := (k / s) * t) i.isLt.le
    exact Nat.lt_succ_of_le h
  have hvj : listSlope k t s j < v := by
    have h := Nat.div_le_div_right (c := (k / s) * t) j.isLt.le
    exact Nat.lt_succ_of_le h
  have hpack : A.card ≤ s * v / t + 1 := by
    apply spaced_card_le s t v ht A
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hei, hej⟩ := Finset.mem_inter.mp he
    obtain ⟨hgi, hgj⟩ := Finset.mem_inter.mp hg
    have hbe := cyclicSet_block k t s ht hs hsk i e hei
    have hbg := cyclicSet_block k t s ht hs hsk i g hgi
    have hde := Nat.mod_add_div e.1.val s
    have hdg := Nat.mod_add_div g.1.val s
    rw [hbe] at hde
    rw [hbg] at hdg
    have hlt : e.1.val + 1 < g.1.val + 1 := by
      change e.1.val % s < g.1.val % s at hab
      omega
    have hdiff : (g.1.val + 1 - (e.1.val + 1)) = (f g).val - (f e).val := by
      dsimp [f]
      omega
    have hce := (cyclicSet_column k t s ht hs hsk i e hei).symm.trans
      (cyclicSet_column k t s ht hs hsk j e hej)
    have hcg := (cyclicSet_column k t s ht hs hsk i g hgi).symm.trans
      (cyclicSet_column k t s ht hs hsk j g hgj)
    have h := modular_collision_spacing t (e.1.val + 1) (g.1.val + 1)
      (listSlope k t s i) (listSlope k t s j)
      (listColumn k t s i) (listColumn k t s j) v hlt hρ hvi hvj hce hcg
    rwa [hdiff] at h
  rw [hcard] at hpack
  calc
    (B.card : ℝ) ≤ (s * v / t + 1 : ℕ) := by exact_mod_cast hpack
    _ = ((s * v / t : ℕ) : ℝ) + 1 := by push_cast; rfl
    _ ≤ ((s * v : ℕ) : ℝ) / t + 1 := by
      have hcast : ((s * v / t : ℕ) : ℝ) ≤ ((s * v : ℕ) : ℝ) / (t : ℝ) :=
        Nat.cast_div_le
      linarith only [hcast]
    _ = 1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t := by
      dsimp [v]
      push_cast
      ring

theorem walsh_size_bounds : Specs.ExpandedFA.AP.BalancedIncidenceSets.walshSizeBounds := by
  intro n hn
  exact ⟨walsh_size_lower n hn, walsh_size_upper n⟩

theorem intersections_and_rows :
    Specs.ExpandedFA.AP.BalancedIncidenceSets.intersectionsAndRows := by
  intro k t s q ht hs hsk
  refine ⟨fun j => cyclicSet k t s ht hs hsk j, ?_, ?_, ?_⟩
  · intro j
    exact cyclicSet_card k t s ht hs hsk j
  · intro i j hij
    exact cyclicSet_intersection_bound k t s q ht hs hsk i j hij
  · intro j r
    exact cyclicSet_one_per_row k t s ht hs hsk j r

/-- Every selected point belongs to an active row. -/
lemma cyclicSet_active (k t s : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (j : ℕ) (e : Fin k × Fin t)
    (he : e ∈ cyclicSet k t s ht hs hsk j) : e.1.val < (k / s) * s := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  have hb : listBlock k s j < k / s := Nat.mod_lt j (quotient_pos hs hsk)
  change listBlock k s j * s + u.val < (k / s) * s
  nlinarith [u.isLt]

/-- A symbol occurs at most once in each slope-list. -/
lemma cyclic_incidence_le (k t s q : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (e : Fin k × Fin t) :
    incidenceCount (fun j : Fin q => cyclicSet k t s ht hs hsk j) e ≤
      q / ((k / s) * t) + 1 := by
  classical
  unfold incidenceCount
  calc
    _ ≤ (Finset.range (q / ((k / s) * t) + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun j : Fin q => listSlope k t s j)
      · intro j _
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right j.isLt.le))
      · intro i hi j hj heq
        by_contra hij
        have hd := cyclicSet_disjoint_same_slope k t s ht hs hsk i j
          (fun h => hij (Fin.ext h)) heq
        exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2
    _ = _ := Finset.card_range _

lemma cyclic_incidence_inactive (k t s q : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hsk : s ≤ k) (e : Fin k × Fin t) (he : ¬ e.1.val < (k / s) * s) :
    incidenceCount (fun j : Fin q => cyclicSet k t s ht hs hsk j) e = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact he (cyclicSet_active k t s ht hs hsk j e (Finset.mem_filter.mp hj).2)

/-- Double counting includes all set indices, even if some selected sets coincide. -/
lemma sum_incidenceCount {k t s q : ℕ} (N : Fin q → Finset (Fin k × Fin t))
    (hcard : ∀ j, (N j).card = s) :
    ∑ e : Fin k × Fin t, incidenceCount N e = q * s := by
  classical
  simp_rw [incidenceCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hsum (j : Fin q) : (∑ e : Fin k × Fin t, if e ∈ N j then 1 else 0) = s := by
    simpa using hcard j
  simp_rw [hsum]
  simp

/-- The number of active symbols, in the full ambient set of symbols. -/
lemma active_symbols_card (k t ell : ℕ) (hell : ell ≤ k) :
    (Finset.univ.filter (fun e : Fin k × Fin t => e.1.val < ell)).card = ell * t := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [← Finset.sum_filter, Finset.sum_const, Finset.filter_const,
    Finset.card_univ, Fintype.card_fin, Finset.card_empty, nsmul_eq_mul, mul_one]
  simp only [apply_ite (fun x : Finset (Fin t) => x.card)]
  simp [Finset.sum_ite, Fin.card_filter_val_lt, min_eq_right hell]

/-- A one-sided incidence cap and the total number of incidences suffice
for a balance bound. The factor two avoids choosing a modular inverse. -/
lemma balance_of_incidence_cap {k t s q ell v : ℕ}
    (ht : 0 < t) (hs : 0 < s) (hq : 0 < q) (hell : 0 < ell) (hellk : ell ≤ k)
    (N : Fin q → Finset (Fin k × Fin t))
    (hcard : ∀ j, (N j).card = s)
    (hcap : ∀ e, incidenceCount N e ≤ v)
    (hinactive : ∀ e : Fin k × Fin t, ¬ e.1.val < ell → incidenceCount N e = 0)
    (hcoverage : q * s ≤ ell * t * v) :
    (∑ e : Fin k × Fin t,
      |1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)|) ≤
      2 * ((ell : ℝ) * t * v / ((q : ℝ) * s) - (ell : ℝ) / k) := by
  classical
  have hk : 0 < k := hell.trans_le hellk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hkt : (0 : ℝ) < (k : ℝ) * t := mul_pos hkr htr
  have hqs : (0 : ℝ) < (q : ℝ) * s := mul_pos hqr hsr
  have hcoverageR : (q : ℝ) * s ≤ (ell : ℝ) * t * v := by exact_mod_cast hcoverage
  have hellkR : (ell : ℝ) ≤ k := by exact_mod_cast hellk
  have ha : 1 / ((k : ℝ) * t) ≤ (v : ℝ) / ((q : ℝ) * s) := by
    apply (div_le_div_iff₀ hkt hqs).2
    nlinarith [mul_le_mul_of_nonneg_right hellkR (mul_nonneg htr.le (Nat.cast_nonneg v))]
  have hp (e : Fin k × Fin t) :
      |1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)| ≤
        (if e.1.val < ell then
          2 * ((v : ℝ) / ((q : ℝ) * s) - 1 / ((k : ℝ) * t)) else 0) +
          1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s) := by
    by_cases he : e.1.val < ell
    · rw [if_pos he]
      have hc : (incidenceCount N e : ℝ) / ((q : ℝ) * s) ≤
          (v : ℝ) / ((q : ℝ) * s) :=
        (div_le_div_iff_of_pos_right hqs).2 (by exact_mod_cast hcap e)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [if_neg he, hinactive e he]
      simp only [Nat.cast_zero, zero_div, sub_zero, zero_add]
      exact le_of_eq (abs_of_nonneg (by positivity))
  have hsum : (∑ e : Fin k × Fin t, (incidenceCount N e : ℝ)) = (q : ℝ) * s := by
    exact_mod_cast sum_incidenceCount N hcard
  calc
    _ ≤ ∑ e : Fin k × Fin t,
        ((if e.1.val < ell then
          2 * ((v : ℝ) / ((q : ℝ) * s) - 1 / ((k : ℝ) * t)) else 0) +
          1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)) :=
      Finset.sum_le_sum (fun e _ => hp e)
    _ = 2 * ((ell : ℝ) * t * v / ((q : ℝ) * s) - (ell : ℝ) / k) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, hsum]
      rw [Finset.sum_ite, Finset.sum_const, active_symbols_card k t ell hellk]
      simp only [Finset.sum_const_zero, sub_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp [ne_of_gt hkr, ne_of_gt htr, ne_of_gt hqr, ne_of_gt hsr]
      <;> ring

/-- Quantitative balance of the cyclic construction, including inactive rows. -/
lemma cyclicSet_balance (k t s q : ℕ) (ht : 0 < t) (hs : 0 < s)
    (hq : 0 < q) (hsk : s ≤ k) :
    (∑ e : Fin k × Fin t,
      |1 / ((k : ℝ) * t) -
        (incidenceCount (fun j : Fin q => cyclicSet k t s ht hs hsk j) e : ℝ) /
          ((q : ℝ) * s)|) ≤
      2 * (s : ℝ) / k + 2 * ((k / s : ℕ) : ℝ) * t / q := by
  let L := k / s
  let P := L * t
  let v := q / P + 1
  have hL : 0 < L := quotient_pos hs hsk
  have hP : 0 < P := Nat.mul_pos hL ht
  have hell : 0 < L * s := Nat.mul_pos hL hs
  have hellk : L * s ≤ k := Nat.div_mul_le_self k s
  have hcover : q * s ≤ (L * s) * t * v := by
    have h := Nat.lt_mul_div_succ q hP
    have h' := Nat.mul_le_mul_right s h.le
    dsimp [v]
    change q * s ≤ L * t * (q / P + 1) * s at h'
    nlinarith only [h']
  have hb := balance_of_incidence_cap ht hs hq hell hellk
    (fun j : Fin q => cyclicSet k t s ht hs hsk j)
    (fun j => cyclicSet_card k t s ht hs hsk j)
    (cyclic_incidence_le k t s q ht hs hsk)
    (cyclic_incidence_inactive k t s q ht hs hsk) hcover
  apply hb.trans
  have hk : 0 < k := hs.trans_le hsk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hv : P * v ≤ q + P := by
    dsimp [v]
    nlinarith [Nat.div_mul_le_self q P]
  have hvR : (L : ℝ) * t * v ≤ (q : ℝ) + (L : ℝ) * t := by
    exact_mod_cast hv
  have hrem : k ≤ L * s + s := by
    have h := Nat.mod_lt k hs
    have h' := Nat.mod_add_div k s
    dsimp [L]
    nlinarith
  have hremR : (k : ℝ) ≤ (L : ℝ) * s + s := by exact_mod_cast hrem
  change 2 * (((L * s : ℕ) : ℝ) * t * (v : ℝ) / ((q : ℝ) * s) -
    ((L * s : ℕ) : ℝ) / k) ≤
      2 * (s : ℝ) / k + 2 * (L : ℝ) * t / q
  simp only [Nat.cast_mul]
  apply (le_of_sub_nonneg ?_)
  field_simp [ne_of_gt hkr, ne_of_gt hsr, ne_of_gt hqr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hvR) hkr.le,
    mul_nonneg (sub_nonneg.mpr hremR) hqr.le]

/-- All finite combinatorial requirements, before the growth specialization. -/
theorem finite_incidence_family :
    Specs.ExpandedFA.AP.BalancedIncidenceSets.finiteIncidenceFamily := by
  intro k t s q ht hs hq hsk
  refine ⟨fun j => cyclicSet k t s ht hs hsk j, ?_, ?_, ?_, ?_⟩
  · exact fun j => cyclicSet_card k t s ht hs hsk j
  · exact fun i j hij => cyclicSet_intersection_bound k t s q ht hs hsk i j hij
  · exact fun j r => cyclicSet_one_per_row k t s ht hs hsk j r
  · exact cyclicSet_balance k t s q ht hs hq hsk


lemma levelSize_pos (offset m : ℕ) : 0 < levelSize offset m := by
  unfold levelSize ExpandedFA.AP.Walsh.levelSize
  apply Nat.choose_pos
  omega

lemma rowCount_pos (offset m : ℕ) : 0 < rowCount offset m := by
  unfold rowCount
  exact pow_pos (levelSize_pos offset m) _

open Filter

lemma dimensions_tendsto : Tendsto (dimension 0) atTop atTop := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num [growthFactor] : 1 < growthFactor)
  convert tendsto_nat_floor_atTop.comp hp using 1
  funext p
  simp [dimension]

/-- Coarse rational bounds on adjacent dimensions, with room for both floors. -/
lemma dimension_step_bounds (p : ℕ) (hn : 30 ≤ dimension 0 p) :
    7 * dimension 0 p ≤ 6 * dimension 0 (p + 1) ∧
      4 * dimension 0 (p + 1) ≤ 5 * dimension 0 p := by
  have h₁ := Nat.floor_le (pow_nonneg growthFactor_pos.le p)
  have h₂ := Nat.lt_floor_add_one (growthFactor ^ p)
  have h₃ := Nat.floor_le (pow_nonneg growthFactor_pos.le (p + 1))
  have h₄ := Nat.lt_floor_add_one (growthFactor ^ (p + 1))
  change (dimension 0 p : ℝ) ≤ growthFactor ^ p at h₁
  change growthFactor ^ p < (dimension 0 p : ℝ) + 1 at h₂
  change (dimension 0 (p + 1) : ℝ) ≤ growthFactor ^ (p + 1) at h₃
  change growthFactor ^ (p + 1) < (dimension 0 (p + 1) : ℝ) + 1 at h₄
  rw [pow_succ] at h₃ h₄
  have hnR : (30 : ℝ) ≤ dimension 0 p := by exact_mod_cast hn
  norm_num [growthFactor] at h₁ h₂ h₃ h₄
  constructor
  · have h : 7 * (dimension 0 p : ℝ) ≤ 6 * (dimension 0 (p + 1) : ℝ) := by linarith
    exact_mod_cast h
  · have h : 4 * (dimension 0 (p + 1) : ℝ) ≤ 5 * (dimension 0 p : ℝ) := by linarith
    exact_mod_cast h

/-- One elementary polynomial bound replaces all uses of Stirling asymptotics. -/
lemma polynomial_bound_eventually :
    ∀ᶠ n : ℕ in atTop, (128 * n) ^ 20 ≤ 4 ^ n := by
  have hh := (tendsto_pow_const_div_const_pow_of_one_lt 20
    (by norm_num : (1 : ℝ) < 4)).const_mul ((128 : ℝ) ^ 20)
  have he := hh.eventually (gt_mem_nhds (by norm_num : ((128 : ℝ) ^ 20) * 0 < 1))
  filter_upwards [he] with n hn
  have hp : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hb : (128 : ℝ) ^ 20 * (n : ℝ) ^ 20 ≤ (4 : ℝ) ^ n := by
    have h : (128 : ℝ) ^ 20 * (n : ℝ) ^ 20 / 4 ^ n ≤ 1 := by
      simpa only [mul_div_assoc] using hn.le
    simpa only [one_mul] using (div_le_iff₀ hp).mp h
  exact_mod_cast (by simpa only [mul_pow] using hb : ((128 : ℝ) * n) ^ 20 ≤ 4 ^ n)

/-- Explicit sufficient polynomial comparisons between two Walsh sizes. -/
lemma walsh_growth_comparisons (n n' : ℕ) (hn : 1 ≤ n)
    (hstep₁ : 7 * n ≤ 6 * n') (hstep₂ : 4 * n' ≤ 5 * n)
    (hpoly : (128 * n) ^ 20 ≤ 4 ^ n) :
    let t := ExpandedFA.AP.Walsh.levelSize n
    let s := ExpandedFA.AP.Walsh.levelSize n'
    8 * n' ≤ t ∧ 8 * n' ≤ s ∧ 8 * n' * s ≤ t ^ 2 ∧
      8 * n' * t ^ 3 ≤ s ^ 3 ∧ 32 * n' * s ^ 3 ≤ t ^ 4 := by
  dsimp only
  let t := ExpandedFA.AP.Walsh.levelSize n
  let s := ExpandedFA.AP.Walsh.levelSize n'
  have hnn' : n ≤ n' := by omega
  have hn' : 1 ≤ n' := hn.trans hnn'
  have hn'2 : n' ≤ 2 * n := by omega
  have htl : 4 ^ n ≤ 4 * n * t := walsh_size_lower n hn
  have hsl : 4 ^ n' ≤ 4 * n' * s := walsh_size_lower n' hn'
  have htu : t ≤ 4 ^ n := walsh_size_upper n
  have hsu : s ≤ 4 ^ n' := walsh_size_upper n'
  have hA : 1 ≤ 128 * n := by omega
  have hpow (d : ℕ) (hd : d ≤ 20) : (128 * n) ^ d ≤ 4 ^ n :=
    (pow_le_pow_right₀ hA hd).trans hpoly
  have ht : 8 * n' ≤ t := by
    apply Nat.le_of_mul_le_mul_left (c := 4 * n) ?_ (by omega)
    calc
      (4 * n) * (8 * n') ≤ (128 * n) ^ 2 := by nlinarith
      _ ≤ 4 ^ n := hpow 2 (by omega)
      _ ≤ _ := htl
  have hs : 8 * n' ≤ s := by
    apply Nat.le_of_mul_le_mul_left (c := 4 * n') ?_ (by omega)
    calc
      (4 * n') * (8 * n') ≤ (128 * n) ^ 2 := by nlinarith
      _ ≤ 4 ^ n := hpow 2 (by omega)
      _ ≤ 4 ^ n' := pow_le_pow_right₀ (by omega) hnn'
      _ ≤ _ := hsl
  have hi : 32 * n' * s ^ 3 ≤ t ^ 4 := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Nat.zero_le _)
    apply Nat.le_of_mul_le_mul_left (c := (4 * n) ^ 16) ?_ (by positivity)
    calc
      (4 * n) ^ 16 * (32 * n' * s ^ 3) ^ 4 =
          ((32 * n') ^ 4 * (4 * n) ^ 16) * s ^ 12 := by ring
      _ ≤ (128 * n) ^ 20 * (4 ^ n') ^ 12 := by
        apply Nat.mul_le_mul
        · calc
            (32 * n') ^ 4 * (4 * n) ^ 16 ≤ (128 * n) ^ 4 * (128 * n) ^ 16 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                (Nat.pow_le_pow_left (by omega) _)
            _ = _ := by rw [← pow_add]
        · exact Nat.pow_le_pow_left hsu _
      _ ≤ 4 ^ n * 4 ^ (15 * n) := by
        apply Nat.mul_le_mul hpoly
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by omega) (by omega)
      _ = (4 ^ n) ^ 16 := by rw [← pow_add, ← pow_mul]; congr 1 <;> omega
      _ ≤ (4 * n * t) ^ 16 := Nat.pow_le_pow_left htl _
      _ = (4 * n) ^ 16 * (t ^ 4) ^ 4 := by ring
  have hb : 8 * n' * t ^ 3 ≤ s ^ 3 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Nat.zero_le _)
    apply Nat.le_of_mul_le_mul_left (c := (4 * n') ^ 6) ?_ (by positivity)
    calc
      (4 * n') ^ 6 * (8 * n' * t ^ 3) ^ 2 =
          ((8 * n') ^ 2 * (4 * n') ^ 6) * t ^ 6 := by ring
      _ ≤ (128 * n) ^ 8 * (4 ^ n) ^ 6 := by
        apply Nat.mul_le_mul
        · calc
            (8 * n') ^ 2 * (4 * n') ^ 6 ≤ (128 * n) ^ 2 * (128 * n) ^ 6 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                (Nat.pow_le_pow_left (by omega) _)
            _ = _ := by rw [← pow_add]
        · exact Nat.pow_le_pow_left htu _
      _ ≤ 4 ^ n * (4 ^ n) ^ 6 := Nat.mul_le_mul_right _ (hpow 8 (by omega))
      _ = 4 ^ (7 * n) := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega
      _ ≤ 4 ^ (6 * n') := pow_le_pow_right₀ (by omega) hstep₁
      _ = (4 ^ n') ^ 6 := by rw [← pow_mul]; congr 1 <;> omega
      _ ≤ (4 * n' * s) ^ 6 := Nat.pow_le_pow_left hsl _
      _ = (4 * n') ^ 6 * (s ^ 3) ^ 2 := by ring
  have hk : 8 * n' * s ≤ t ^ 2 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Nat.zero_le _)
    calc
      (8 * n' * s) ^ 2 = (32 * n' * s ^ 2) * (2 * n') := by ring
      _ ≤ (32 * n' * s ^ 2) * s := Nat.mul_le_mul_left _ (by omega)
      _ = 32 * n' * s ^ 3 := by ring
      _ ≤ t ^ 4 := hi
      _ = (t ^ 2) ^ 2 := by ring
  exact ⟨ht, hs, hk, hb, hi⟩

/-- Convert the integer growth comparisons to the two real estimates needed
by the construction. Natural division in the number of lists is retained. -/
lemma numerical_bounds (t s n : ℕ) (hn : 0 < n)
    (ht : 8 * n ≤ t) (hs : 8 * n ≤ s)
    (hk : 8 * n * s ≤ t ^ 2) (hb : 8 * n * t ^ 3 ≤ s ^ 3)
    (hi : 32 * n * s ^ 3 ≤ t ^ 4) :
    s ≤ t ^ 2 ∧
      1 + (s : ℝ) * (s ^ 2 / ((t ^ 2 / s) * t) + 1 : ℕ) / t ≤
        (s : ℝ) / (2 * n) ∧
      2 * (s : ℝ) / (t ^ 2 : ℕ) +
        2 * ((t ^ 2 / s : ℕ) : ℝ) * t / (s ^ 2 : ℕ) ≤ 1 / (n : ℝ) := by
  have htpos : 0 < t := by omega
  have hspos : 0 < s := by omega
  have hsk : s ≤ t ^ 2 := by nlinarith
  let L := t ^ 2 / s
  have hL : 0 < L := quotient_pos hspos hsk
  have hLs : L * s ≤ t ^ 2 := Nat.div_mul_le_self _ _
  have hkLs : t ^ 2 ≤ 2 * L * s := by
    have hrem := Nat.mod_lt (t ^ 2) hspos
    have hdiv := Nat.mod_add_div (t ^ 2) s
    change t ^ 2 % s + s * L = t ^ 2 at hdiv
    nlinarith
  have hLi : 16 * n * s ^ 2 ≤ L * t ^ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := 2 * s) ?_ (by positivity)
    calc
      (2 * s) * (16 * n * s ^ 2) = 32 * n * s ^ 3 := by ring
      _ ≤ t ^ 4 := hi
      _ ≤ (2 * L * s) * t ^ 2 := by nlinarith [Nat.mul_le_mul_right (t ^ 2) hkLs]
      _ = (2 * s) * (L * t ^ 2) := by ring
  have hLb : 8 * n * L * t ≤ s ^ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := s) ?_ hspos
    calc
      s * (8 * n * L * t) = (8 * n * t) * (L * s) := by ring
      _ ≤ (8 * n * t) * t ^ 2 := Nat.mul_le_mul_left _ hLs
      _ = 8 * n * t ^ 3 := by ring
      _ ≤ s ^ 3 := hb
      _ = s * s ^ 2 := by ring
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have htr : (0 : ℝ) < t := by exact_mod_cast htpos
  have hsr : (0 : ℝ) < s := by exact_mod_cast hspos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have htR : 8 * (n : ℝ) ≤ t := by exact_mod_cast ht
  have hsR : 8 * (n : ℝ) ≤ s := by exact_mod_cast hs
  have hkR : 8 * (n : ℝ) * s ≤ (t : ℝ) ^ 2 := by exact_mod_cast hk
  have hLiR : 16 * (n : ℝ) * (s : ℝ) ^ 2 ≤ (L : ℝ) * (t : ℝ) ^ 2 := by
    exact_mod_cast hLi
  have hLbR : 8 * (n : ℝ) * L * t ≤ (s : ℝ) ^ 2 := by exact_mod_cast hLb
  have hsinv : 1 / (s : ℝ) ≤ 1 / (8 * (n : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hsR
  have htinv : 1 / (t : ℝ) ≤ 1 / (8 * (n : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) htR
  have hquot : (s : ℝ) ^ 2 / ((L : ℝ) * (t : ℝ) ^ 2) ≤ 1 / (16 * (n : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hLiR]
  have hv : ((s ^ 2 / (L * t) + 1 : ℕ) : ℝ) / t ≤
      1 / (16 * (n : ℝ)) + 1 / (8 * (n : ℝ)) := by
    calc
      _ ≤ ((s : ℝ) ^ 2 / ((L : ℝ) * t) + 1) / t := by
        apply (div_le_div_iff_of_pos_right htr).2
        push_cast
        have hc : ((s ^ 2 / (L * t) : ℕ) : ℝ) ≤
            ((s ^ 2 : ℕ) : ℝ) / ((L * t : ℕ) : ℝ) := Nat.cast_div_le
        push_cast at hc
        linarith only [hc]
      _ = (s : ℝ) ^ 2 / ((L : ℝ) * (t : ℝ) ^ 2) + 1 / (t : ℝ) := by
        field_simp
        <;> ring
      _ ≤ _ := add_le_add hquot htinv
  refine ⟨hsk, ?_, ?_⟩
  · change 1 + (s : ℝ) * (s ^ 2 / (L * t) + 1 : ℕ) / t ≤ (s : ℝ) / (2 * n)
    calc
      _ = (s : ℝ) * (1 / (s : ℝ) + ((s ^ 2 / (L * t) + 1 : ℕ) : ℝ) / t) := by
        field_simp
        <;> ring
      _ ≤ (s : ℝ) * (1 / (8 * (n : ℝ)) +
          (1 / (16 * (n : ℝ)) + 1 / (8 * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hsinv hv) hsr.le
      _ ≤ (s : ℝ) / (2 * n) := by
        field_simp [ne_of_gt hnr]
        nlinarith
  · change 2 * (s : ℝ) / (t ^ 2 : ℕ) + 2 * (L : ℝ) * t / (s ^ 2 : ℕ) ≤ _
    push_cast
    have hb₁ : 2 * (s : ℝ) / (t : ℝ) ^ 2 ≤ 1 / (4 * (n : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hkR]
    have hb₂ : 2 * (L : ℝ) * t / (s : ℝ) ^ 2 ≤ 1 / (4 * (n : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hLbR]
    calc
      _ ≤ 1 / (4 * (n : ℝ)) + 1 / (4 * (n : ℝ)) := add_le_add hb₁ hb₂
      _ ≤ 1 / (n : ℝ) := by field_simp [ne_of_gt hnr]; nlinarith

/-- One offset works for every subsequent pair of blocks. -/
theorem uniform_growth_bounds : ∃ offset : ℕ, 4 ≤ offset ∧ ∀ m : ℕ,
    let t := levelSize offset m
    let s := levelSize offset (m + 1)
    let k := rowCount offset m
    let q := rowCount offset (m + 1)
    let n := dimension offset (m + 1)
    s ≤ k ∧
      1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t ≤ (s : ℝ) / (2 * n) ∧
      2 * (s : ℝ) / k + 2 * ((k / s : ℕ) : ℝ) * t / q ≤ 1 / (n : ℝ) := by
  have he : ∀ᶠ p : ℕ in atTop,
      30 ≤ dimension 0 p ∧ (128 * dimension 0 p) ^ 20 ≤ 4 ^ dimension 0 p :=
    (dimensions_tendsto.eventually (eventually_ge_atTop 30)).and
      (dimensions_tendsto.eventually polynomial_bound_eventually)
  obtain ⟨p₀, hp₀⟩ := he.exists_forall_of_atTop
  refine ⟨max p₀ 4, le_max_right _ _, ?_⟩
  intro m
  have hp := hp₀ (m + max p₀ 4) (by omega)
  obtain ⟨hstep₁, hstep₂⟩ := dimension_step_bounds _ hp.1
  have hcomp := walsh_growth_comparisons _ _ (one_le_dimension 0 _)
    hstep₁ hstep₂ hp.2
  have hnum := numerical_bounds _ _ _
    (Nat.zero_lt_of_lt (one_le_dimension 0 _))
    hcomp.1 hcomp.2.1 hcomp.2.2.1 hcomp.2.2.2.1 hcomp.2.2.2.2
  have hd : dimension (max p₀ 4) m = dimension 0 (m + max p₀ 4) := by
    simp only [dimension, Nat.add_zero]
  have hd' : dimension (max p₀ 4) (m + 1) = dimension 0 (m + max p₀ 4 + 1) := by
    simp only [dimension, Nat.add_zero, Nat.add_right_comm m 1 (max p₀ 4)]
  simpa only [rowCount, levelSize, hd, hd'] using hnum

/-- Assemble the finite construction and uniform numerical estimates. -/
theorem incidence_sets_exist_of_bounds
    (hfinite : ∀ k t s q : ℕ, 0 < t → 0 < s → 0 < q → s ≤ k →
      ∃ N : Fin q → Finset (Fin k × Fin t),
        (∀ j, (N j).card = s) ∧
        (∀ i j, i ≠ j → ((N i ∩ N j).card : ℝ) ≤
          1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t) ∧
        (∀ j (r : Fin k), ((N j).filter (fun e => e.1 = r)).card ≤ 1) ∧
        (∑ e : Fin k × Fin t,
          |1 / ((k : ℝ) * t) - (incidenceCount N e : ℝ) / ((q : ℝ) * s)|) ≤
            2 * (s : ℝ) / k + 2 * ((k / s : ℕ) : ℝ) * t / q)
    (hgrowth : ∃ offset : ℕ, 4 ≤ offset ∧ ∀ m : ℕ,
      let t := levelSize offset m
      let s := levelSize offset (m + 1)
      let k := rowCount offset m
      let q := rowCount offset (m + 1)
      let n := dimension offset (m + 1)
      s ≤ k ∧
        1 + (s : ℝ) * (q / ((k / s) * t) + 1 : ℕ) / t ≤
          (s : ℝ) / (2 * n) ∧
        2 * (s : ℝ) / k + 2 * ((k / s : ℕ) : ℝ) * t / q ≤ 1 / (n : ℝ)) :
    Specs.ExpandedFA.AP.BalancedIncidenceSets.incidenceSetsExist := by
  classical
  obtain ⟨offset, hoffset, hgrowth⟩ := hgrowth
  have hex : ∀ m : ℕ, ∃ N : Fin (rowCount offset (m + 1)) → Finset (Symbol offset m),
        (∀ j, (N j).card = levelSize offset (m + 1)) ∧
        (∀ i j, i ≠ j → ((N i ∩ N j).card : ℝ) ≤
          1 + (levelSize offset (m + 1) : ℝ) *
            (rowCount offset (m + 1) /
              ((rowCount offset m / levelSize offset (m + 1)) * levelSize offset m) + 1 : ℕ) /
              levelSize offset m) ∧
        (∀ j (r : Fin (rowCount offset m)),
          ((N j).filter (fun e => e.1 = r)).card ≤ 1) ∧
        (∑ e : Symbol offset m,
          |1 / ((rowCount offset m : ℝ) * levelSize offset m) -
            (incidenceCount N e : ℝ) /
              ((rowCount offset (m + 1) : ℝ) * levelSize offset (m + 1))|) ≤
            2 * (levelSize offset (m + 1) : ℝ) / rowCount offset m +
              2 * ((rowCount offset m / levelSize offset (m + 1) : ℕ) : ℝ) *
                levelSize offset m / rowCount offset (m + 1) := by
    intro m
    exact hfinite _ _ _ _ (levelSize_pos offset m) (levelSize_pos offset (m + 1))
      (rowCount_pos offset (m + 1)) (hgrowth m).1
  choose N hN using hex
  refine ⟨offset, N, ?_, ?_, ?_⟩
  · intro m _
    exact dimension_at_least_two offset m hoffset
  · intro m _
    obtain ⟨hcard, hinter, hrow, hbalance⟩ := hN m
    exact ⟨hcard, fun i j hij => (hinter i j hij).trans (hgrowth m).2.1,
      hrow, hbalance.trans (hgrowth m).2.2⟩
  · exact (summable_nat_add_iff 1).mpr (reciprocal_dimensions_summable offset)

/-- The source’s full incidence construction, with one simultaneous offset. -/
theorem incidence_sets_exist :
    Specs.ExpandedFA.AP.BalancedIncidenceSets.incidenceSetsExist :=
  incidence_sets_exist_of_bounds finite_incidence_family uniform_growth_bounds

end ExpandedFA.AP.BalancedIncidenceSets
