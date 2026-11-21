import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyWhitney
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Set TopologicalSpace MeasureTheory
open scoped Topology ContDiff

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

namespace DyadicCube

instance {d : ℕ} : Countable (DyadicCube d) :=
  Function.Injective.countable (f := fun Q : DyadicCube d => (Q.level, Q.corner)) (by
    intro Q R h
    cases Q
    cases R
    simpa using h)

@[simp] theorem side_pos {d : ℕ} (Q : DyadicCube d) : 0 < Q.side := by
  exact zpow_pos (by norm_num) _

@[simp] theorem side_nonneg {d : ℕ} (Q : DyadicCube d) : 0 ≤ Q.side := Q.side_pos.le

@[simp] theorem mem_dilate {d : ℕ} (Q : DyadicCube d) (t : ℝ) (x : Domain d) :
    x ∈ Q.dilate t ↔ dist x Q.center ≤ t * Q.side / 2 := Iff.rfl

@[simp] theorem center_mem_carrier {d : ℕ} (Q : DyadicCube d) : Q.center ∈ Q.carrier := by
  change dist Q.center Q.center ≤ 1 * Q.side / 2
  simp only [dist_self, one_mul]
  exact div_nonneg Q.side_nonneg (by norm_num)

@[simp] theorem center_mem_star {d : ℕ} (Q : DyadicCube d) : Q.center ∈ Q.star := by
  change dist Q.center Q.center ≤ (9 / 8) * Q.side / 2
  simp only [dist_self]
  exact div_nonneg (mul_nonneg (by norm_num) Q.side_nonneg) (by norm_num)

theorem isCompact_dilate {d : ℕ} (Q : DyadicCube d) (t : ℝ) : IsCompact (Q.dilate t) :=
  isCompact_closedBall _ _

theorem carrier_subset_star {d : ℕ} (Q : DyadicCube d) : Q.carrier ⊆ Q.star := by
  apply Metric.closedBall_subset_closedBall
  have := Q.side_pos
  linarith

/-- The closed-ball model is exactly the ordinary coordinate dyadic cube. -/
theorem carrier_eq_Icc {d : ℕ} (Q : DyadicCube d) :
    Q.carrier = Icc (fun i => Q.side * (Q.corner i : ℝ))
      (fun i => Q.side * ((Q.corner i : ℝ) + 1)) := by
  ext x
  change (dist x Q.center ≤ 1 * Q.side / 2) ↔ _
  rw [dist_pi_le_iff (by simpa only [one_mul] using div_nonneg Q.side_nonneg (show (0 : ℝ) ≤ 2 by norm_num))]
  simp only [Real.dist_eq, center, one_mul, mem_Icc, Pi.le_def]
  constructor
  · intro h
    constructor <;> intro i <;> have hi := abs_le.mp (h i) <;> linarith
  · rintro ⟨hl, hu⟩ i
    apply abs_le.mpr
    constructor <;> have hl' := hl i <;> have hu' := hu i <;> linarith

/-- Actual Lebesgue volume, rather than an unrelated assigned cube weight. -/
theorem volume_carrier {d : ℕ} (Q : DyadicCube d) :
    volume Q.carrier = ENNReal.ofReal (Q.side ^ d) := by
  unfold carrier dilate
  rw [Real.volume_pi_closedBall _ (by simpa using div_nonneg Q.side_nonneg (by norm_num : (0 : ℝ) ≤ 2))]
  simp only [Fintype.card_fin]
  congr 1
  congr 1
  ring

@[simp] theorem volume_carrier_toReal {d : ℕ} (Q : DyadicCube d) :
    (volume Q.carrier).toReal = Q.side ^ d := by
  rw [volume_carrier, ENNReal.toReal_ofReal (pow_nonneg Q.side_nonneg _)]

theorem dist_le_of_mem_star {d : ℕ} {Q : DyadicCube d} {x : Domain d}
    (hx : x ∈ Q.star) : dist x Q.center ≤ (9 / 16) * Q.side := by
  change dist x Q.center ≤ (9 / 8) * Q.side / 2 at hx
  linarith

theorem dist_le_of_mem_star_pair {d : ℕ} {Q : DyadicCube d} {x y : Domain d}
    (hx : x ∈ Q.star) (hy : y ∈ Q.star) : dist x y ≤ (9 / 8) * Q.side := by
  have h := dist_triangle x Q.center y
  have hx' := dist_le_of_mem_star hx
  have hy' := dist_le_of_mem_star hy
  rw [dist_comm Q.center y] at h
  linarith

/-- Size control at one intersection implies the required dilation containment. -/
theorem star_subset_dilate_of_inter {d : ℕ} {Q R : DyadicCube d}
    (h : (R.star ∩ Q.star).Nonempty) (hs : R.side ≤ 3 * Q.side) :
    R.star ⊆ Q.dilate 8 := by
  obtain ⟨x, hxR, hxQ⟩ := h
  intro y hy
  have hxy := dist_le_of_mem_star_pair hy hxR
  have hx := dist_le_of_mem_star hxQ
  have ht := dist_triangle y x Q.center
  change dist y Q.center ≤ 8 * Q.side / 2
  have := Q.side_pos
  linarith

end DyadicCube

namespace DyadicCube

/-- The unique parent in the standard dyadic grid. Integer division is
floor division, so this also handles negative corners. -/
def parent {d : ℕ} (Q : DyadicCube d) : DyadicCube d :=
  ⟨Q.level + 1, fun i => Q.corner i / 2⟩

@[simp] theorem side_parent {d : ℕ} (Q : DyadicCube d) : Q.parent.side = 2 * Q.side := by
  simp only [side, parent, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

theorem dist_center_parent {d : ℕ} (Q : DyadicCube d) :
    dist Q.center Q.parent.center ≤ Q.side / 2 := by
  rw [dist_pi_le_iff (div_nonneg Q.side_nonneg (by norm_num))]
  intro i
  rw [Real.dist_eq]
  change |Q.side * ((Q.corner i : ℝ) + 1 / 2) -
    Q.parent.side * (((Q.corner i / 2 : ℤ) : ℝ) + 1 / 2)| ≤ Q.side / 2
  rw [side_parent]
  apply abs_le.mpr
  have hm₀ := Int.emod_nonneg (Q.corner i) (by norm_num : (2 : ℤ) ≠ 0)
  have hm₁ := Int.emod_lt_of_pos (Q.corner i) (by norm_num : (0 : ℤ) < 2)
  have hlo : 2 * (Q.corner i / 2) ≤ Q.corner i := by omega
  have hhi : Q.corner i ≤ 2 * (Q.corner i / 2) + 1 := by omega
  have hlo' : 2 * ((Q.corner i / 2 : ℤ) : ℝ) ≤ (Q.corner i : ℝ) := by exact_mod_cast hlo
  have hhi' : (Q.corner i : ℝ) ≤ 2 * ((Q.corner i / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hhi
  constructor <;> nlinarith [mul_nonneg Q.side_nonneg (sub_nonneg.mpr hlo'),
    mul_nonneg Q.side_nonneg (sub_nonneg.mpr hhi')]

/-- Membership in a child implies membership in its dyadic parent. -/
theorem carrier_subset_parent {d : ℕ} (Q : DyadicCube d) : Q.carrier ⊆ Q.parent.carrier := by
  intro x hx
  have hx' : dist x Q.center ≤ Q.side / 2 := by
    simpa only [carrier, mem_dilate, one_mul] using hx
  have ht := dist_triangle x Q.center Q.parent.center
  have hc := dist_center_parent Q
  change dist x Q.parent.center ≤ 1 * Q.parent.side / 2
  rw [side_parent]
  linarith

/-- A cube of every dyadic scale containing a given point. -/
noncomputable def atScale {d : ℕ} (x : Domain d) (k : ℤ) : DyadicCube d :=
  ⟨k, fun i => ⌊x i / (2 : ℝ) ^ k⌋⟩

@[simp] theorem side_atScale {d : ℕ} (x : Domain d) (k : ℤ) :
    (atScale x k).side = (2 : ℝ) ^ k := rfl

theorem mem_atScale {d : ℕ} (x : Domain d) (k : ℤ) : x ∈ (atScale x k).carrier := by
  rw [carrier_eq_Icc]
  constructor <;> intro i
  · have h := Int.floor_le (x i / (2 : ℝ) ^ k)
    have h' := (le_div_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) k)).mp h
    simpa only [atScale, side, mul_comm] using h'
  · have h := Int.lt_floor_add_one (x i / (2 : ℝ) ^ k)
    have h' := (div_lt_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) k)).mp h
    exact le_of_lt (by simpa only [atScale, side, mul_comm] using h')

/-- Every point of an open set is contained in an admissible dyadic cube.
No boundedness assumption on the open set is needed for this local step. -/
theorem exists_small_admissible {d : ℕ} {Ω : Set (Domain d)} (hΩ : IsOpen Ω)
    {x : Domain d} (hx : x ∈ Ω) : ∃ Q : DyadicCube d, x ∈ Q.carrier ∧ Q.dilate 20 ⊆ Ω := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by norm_num : (0 : ℝ) < 11))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let Q := atScale x (-(n : ℤ))
  have hside : Q.side < ε / 11 := by
    simpa only [Q, side_atScale, zpow_neg, zpow_natCast, one_div, inv_pow] using hn
  refine ⟨Q, mem_atScale x _, ?_⟩
  intro y hy
  apply hball
  have hy' : dist y Q.center ≤ 20 * Q.side / 2 := hy
  have hx' : dist x Q.center ≤ Q.side / 2 := by
    simpa only [carrier, mem_dilate, one_mul] using mem_atScale x (-(n : ℤ))
  have ht := dist_triangle y Q.center x
  rw [dist_comm Q.center x] at ht
  change dist y x < ε
  have hp := Q.side_pos
  linarith

/-- All admissible cubes through one point have their levels bounded above
when the open set has a nonempty complement. -/
theorem admissible_levels_bounded {d : ℕ} {Ω : Set (Domain d)} (hne : Ωᶜ.Nonempty)
    (x : Domain d) :
    ∃ b : ℤ, ∀ Q : DyadicCube d, x ∈ Q.carrier → Q.dilate 20 ⊆ Ω → Q.level ≤ b := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (dist z x) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_⟩
  intro Q hx hQ
  have hx' : dist x Q.center ≤ Q.side / 2 := by
    simpa only [carrier, mem_dilate, one_mul] using hx
  have hz' : z ∉ Q.dilate 20 := fun h => hz (hQ h)
  have hfar : 20 * Q.side / 2 < dist z Q.center := lt_of_not_ge hz'
  have ht := dist_triangle z x Q.center
  have hp := Q.side_pos
  have hs : Q.side < (2 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    linarith
  exact le_of_lt ((zpow_lt_zpow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp hs)

/-- At every point of a proper open set there is a dyadic cube satisfying
twentyfold admissibility whose parent fails it. -/
theorem exists_admissible_parent_failure {d : ℕ} {Ω : Set (Domain d)}
    (hΩ : IsOpen Ω) (hne : Ωᶜ.Nonempty) {x : Domain d} (hx : x ∈ Ω) :
    ∃ Q : DyadicCube d, x ∈ Q.carrier ∧ Q.dilate 20 ⊆ Ω ∧ ¬ Q.parent.dilate 20 ⊆ Ω := by
  let P : ℤ → Prop := fun k => ∃ Q : DyadicCube d,
    Q.level = k ∧ x ∈ Q.carrier ∧ Q.dilate 20 ⊆ Ω
  obtain ⟨b, hb⟩ := admissible_levels_bounded hne x
  have hbounded : ∃ b : ℤ, ∀ k, P k → k ≤ b := by
    refine ⟨b, ?_⟩
    rintro k ⟨Q, rfl, hxQ, hQ⟩
    exact hb Q hxQ hQ
  have hexists : ∃ k, P k := by
    obtain ⟨Q, hxQ, hQ⟩ := exists_small_admissible hΩ hx
    exact ⟨Q.level, Q, rfl, hxQ, hQ⟩
  obtain ⟨k, ⟨Q, hlevel, hxQ, hQ⟩, hmax⟩ := Int.exists_greatest_of_bdd hbounded hexists
  refine ⟨Q, hxQ, hQ, ?_⟩
  intro hp
  have hplevel : P (k + 1) :=
    ⟨Q.parent, by simp only [parent, hlevel], carrier_subset_parent Q hxQ, hp⟩
  have := hmax (k + 1) hplevel
  omega

/-- The twentyfold admissibility and the failure of the parent give the
quantitative boundary-distance estimates used by the rest of the proof. -/
theorem distance_bounds_of_parent_failure {d : ℕ} {Ω : Set (Domain d)}
    (Q : DyadicCube d) (hQ : Q.dilate 20 ⊆ Ω) (hparent : ¬ Q.parent.dilate 20 ⊆ Ω)
    (x : Domain d) (hx : x ∈ Q.star) :
    9 * Q.side ≤ Metric.infDist x Ωᶜ ∧ Metric.infDist x Ωᶜ ≤ 22 * Q.side := by
  classical
  obtain ⟨z, hzP, hzΩ⟩ := Set.not_subset.mp hparent
  have hne : Ωᶜ.Nonempty := ⟨z, hzΩ⟩
  have hx' := dist_le_of_mem_star hx
  have hp := Q.side_pos
  constructor
  · apply (Metric.le_infDist hne).mpr
    intro y hy
    have hyQ : y ∉ Q.dilate 20 := fun hyQ => hy (hQ hyQ)
    have hfar : 20 * Q.side / 2 < dist y Q.center := lt_of_not_ge hyQ
    have ht := dist_triangle y x Q.center
    rw [dist_comm y x] at ht
    linarith
  · have hz' : dist z Q.parent.center ≤ 20 * Q.parent.side / 2 := hzP
    rw [side_parent] at hz'
    have h₁ := dist_triangle x Q.center Q.parent.center
    have h₂ := dist_triangle x Q.parent.center z
    have h₃ := dist_center_parent Q
    rw [dist_comm Q.parent.center z] at h₂
    have h₄ := Metric.infDist_le_dist_of_mem (x := x) (show z ∈ Ωᶜ from hzΩ)
    linarith

end DyadicCube

/-- Finite measure implies a nonempty complement in the source's positive
dimensions. This discharges the side condition for real-valued `infDist`. -/
theorem complement_nonempty {d : ℕ} (hd : 0 < d) {Ω : Set (Domain d)}
    (hΩ : volume Ω < ⊤) : Ωᶜ.Nonempty := by
  have huniv : volume (univ : Set (Domain d)) = ⊤ := by
    rw [volume_pi, Measure.pi_univ]
    simp only [Real.volume_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact ENNReal.top_pow (Nat.ne_of_gt hd)
  by_contra h
  have hfull : Ω = univ := by
    ext x
    simp only [mem_univ, iff_true]
    by_contra hx
    exact h ⟨x, hx⟩
  rw [hfull, huniv] at hΩ
  exact lt_irrefl _ hΩ

/-- The distance comparison used for nested open sets. The nonemptiness
condition is on the coarse complement, as required by Mathlib's real-valued
`infDist`; it follows from finite measure when `d ≥ 1`. -/
theorem boundary_distance_mono {d : ℕ} {Ω Ω' : Set (Domain d)}
    (hΩ : Ω' ⊆ Ω) (hne : Ωᶜ.Nonempty) (x : Domain d) :
    Metric.infDist x Ω'ᶜ ≤ Metric.infDist x Ωᶜ :=
  Metric.infDist_le_infDist_of_subset (compl_subset_compl.mpr hΩ) hne

/-- Nested side lengths follow from the boundary-distance inequalities at
any common point; no reverse inclusion of the open sets is used. -/
theorem nested_side_le {d : ℕ} {Ω Ω' : Set (Domain d)}
    {S S' : Set (DyadicCube d)} (hΩ : Ω' ⊆ Ω) (hne : Ωᶜ.Nonempty)
    (hS : DistanceBounds Ω S) (hS' : DistanceBounds Ω' S')
    {Q R : DyadicCube d} (hQ : Q ∈ S) (hR : R ∈ S')
    (h : (R.star ∩ Q.star).Nonempty) : R.side ≤ 3 * Q.side := by
  obtain ⟨x, hxR, hxQ⟩ := h
  have hf := (hS' R hR x hxR).1
  have hc := (hS Q hQ x hxQ).2
  have hm := boundary_distance_mono hΩ hne x
  have := Q.side_pos
  linarith

/-- Both geometric assertions at a nested-level intersection, with one
absolute dilation factor. -/
theorem nested_size_and_containment {d : ℕ} {Ω Ω' : Set (Domain d)}
    {S S' : Set (DyadicCube d)} (hΩ : Ω' ⊆ Ω) (hne : Ωᶜ.Nonempty)
    (hS : DistanceBounds Ω S) (hS' : DistanceBounds Ω' S')
    {Q R : DyadicCube d} (hQ : Q ∈ S) (hR : R ∈ S')
    (h : (R.star ∩ Q.star).Nonempty) :
    R.side ≤ 8 * Q.side ∧ R.star ⊆ Q.dilate 8 := by
  have hs := nested_side_le hΩ hne hS hS' hQ hR h
  exact ⟨by have := Q.side_pos; linarith,
    DyadicCube.star_subset_dilate_of_inter h hs⟩

/-- All coarse cubes meeting one fixed fine enlargement have comparable
sides. This is the quantitative input to the nested packing argument. -/
theorem coarse_sides_comparable {d : ℕ} {Ω Ω' : Set (Domain d)}
    {S S' : Set (DyadicCube d)} (hΩ : Ω' ⊆ Ω) (hne : Ωᶜ.Nonempty)
    (hS : DistanceBounds Ω S) (hS' : DistanceBounds Ω' S')
    {Q₁ Q₂ R : DyadicCube d} (hQ₁ : Q₁ ∈ S) (hQ₂ : Q₂ ∈ S) (hR : R ∈ S')
    (h₁ : (R.star ∩ Q₁.star).Nonempty) (h₂ : (R.star ∩ Q₂.star).Nonempty) :
    Q₁.side ≤ 3 * Q₂.side := by
  obtain ⟨x, hxR, hxQ⟩ := h₁
  obtain ⟨y, hyR, hyQ⟩ := h₂
  have hl := (hS Q₁ hQ₁ x hxQ).1
  have hu := (hS Q₂ hQ₂ y hyQ).2
  have hd := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Ωᶜ)
  have hxy := DyadicCube.dist_le_of_mem_star_pair hxR hyR
  have hr := (hS' R hR y hyR).1
  have hm := boundary_distance_mono hΩ hne y
  have := Q₂.side_pos
  linarith

/-- Volume packing for disjoint dyadic interiors. It gives genuine finiteness
as well as a quantitative cardinal bound. -/
theorem cube_packing {d : ℕ} (S : Set (DyadicCube d))
    (hdisj : S.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)))
    (x : Domain d) (a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hside : ∀ Q ∈ S, a ≤ Q.side)
    (hsub : ∀ Q ∈ S, Q.carrier ⊆ Metric.closedBall x r) :
    S.Finite ∧ (S.ncard : ℝ) * a ^ d ≤ (2 * r) ^ d := by
  classical
  let B : S → Set (Domain d) := fun Q => Metric.ball Q.val.center (Q.val.side / 2)
  have hBint (Q : S) : B Q ⊆ interior Q.val.carrier := by
    simpa only [DyadicCube.carrier, DyadicCube.dilate, one_mul] using
      (Metric.ball_subset_interior_closedBall (x := Q.val.center) (ε := Q.val.side / 2))
  have hBsub (Q : S) : B Q ⊆ Metric.closedBall x r :=
    (hBint Q).trans (interior_subset.trans (hsub Q.val Q.property))
  have hBvol (Q : S) : volume (B Q) = ENNReal.ofReal (Q.val.side ^ d) := by
    dsimp [B]
    rw [Real.volume_pi_ball _ (div_pos Q.val.side_pos (by norm_num))]
    simp only [Fintype.card_fin]
    congr 1
    congr 1
    ring
  have hBlo (Q : S) : ENNReal.ofReal (a ^ d) ≤ volume (B Q) := by
    rw [hBvol]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le (hside Q.val Q.property) _)
  have hdB : Pairwise (fun Q R : S => Disjoint (B Q) (B R)) := by
    intro Q R hne
    exact (hdisj Q.property R.property (fun heq => hne (Subtype.ext heq))).mono (hBint Q) (hBint R)
  have hU : (⋃ Q : S, B Q) ⊆ Metric.closedBall x r := iUnion_subset hBsub
  have hUfin : volume (⋃ Q : S, B Q) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hU)
  have hfinite := Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr (pow_pos ha d))
    (fun Q : S => Metric.isOpen_ball.measurableSet) hdB hUfin
  have huniv : (univ : Set S).Finite := by
    convert hfinite using 1
    ext Q
    simp only [mem_univ, mem_ofPred_eq, true_iff]
    exact hBlo Q
  let : Finite S := finite_univ_iff.mp huniv
  let : Fintype S := Fintype.ofFinite S
  refine ⟨Set.toFinite S, ?_⟩
  have hsum : volume (⋃ Q : S, B Q) = ∑ Q : S, volume (B Q) := by
    rw [measure_iUnion hdB (fun _ => Metric.isOpen_ball.measurableSet), tsum_fintype]
  calc
    (S.ncard : ℝ) * a ^ d = ∑ _Q : S, a ^ d := by
      rw [show S.ncard = Fintype.card S from Nat.card_eq_fintype_card]
      simp
    _ ≤ ∑ Q : S, (volume (B Q)).toReal := by
      apply Finset.sum_le_sum
      intro Q _
      rw [hBvol, ENNReal.toReal_ofReal (pow_nonneg Q.val.side_nonneg _)]
      exact pow_le_pow_left₀ ha.le (hside Q.val Q.property) _
    _ = (volume (⋃ Q : S, B Q)).toReal := by
      rw [hsum, ENNReal.toReal_sum (fun Q _ => by rw [hBvol]; exact ENNReal.ofReal_ne_top)]
    _ ≤ (volume (Metric.closedBall x r)).toReal :=
      ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono hU)
    _ = (2 * r) ^ d := by
      rw [Real.volume_pi_closedBall _ hr, Fintype.card_fin,
        ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (by norm_num) hr) _)]

/-- The complete nested-level packing bound, assuming only the ordinary
Whitney distance estimates and disjoint coarse interiors. -/
theorem nested_meeting_bound {d : ℕ} {Ω Ω' : Set (Domain d)}
    {S S' : Set (DyadicCube d)} (hΩ : Ω' ⊆ Ω) (hne : Ωᶜ.Nonempty)
    (hS : DistanceBounds Ω S) (hS' : DistanceBounds Ω' S')
    (hdisj : S.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)))
    {R : DyadicCube d} (hR : R ∈ S') :
    {Q | Q ∈ S ∧ (R.star ∩ Q.star).Nonempty}.Finite ∧
      {Q | Q ∈ S ∧ (R.star ∩ Q.star).Nonempty}.ncard ≤ 30 ^ d := by
  classical
  let T : Set (DyadicCube d) := {Q | Q ∈ S ∧ (R.star ∩ Q.star).Nonempty}
  by_cases ht : T.Nonempty
  · obtain ⟨Q₀, hQ₀, hm₀⟩ := ht
    have hRside := nested_side_le hΩ hne hS hS' hQ₀ hR hm₀
    have hlow (Q : DyadicCube d) (hQ : Q ∈ T) : Q₀.side / 3 ≤ Q.side := by
      have := coarse_sides_comparable hΩ hne hS hS' hQ₀ hQ.1 hR hm₀ hQ.2
      linarith
    have hupper (Q : DyadicCube d) (hQ : Q ∈ T) : Q.side ≤ 3 * Q₀.side :=
      coarse_sides_comparable hΩ hne hS hS' hQ.1 hQ₀ hR hQ.2 hm₀
    have hsub (Q : DyadicCube d) (hQ : Q ∈ T) :
        Q.carrier ⊆ Metric.closedBall R.center (5 * Q₀.side) := by
      obtain ⟨x, hxR, hxQ⟩ := hQ.2
      intro y hy
      have h₁ : dist y Q.center ≤ Q.side / 2 := by
        simpa only [DyadicCube.carrier, DyadicCube.mem_dilate, one_mul] using hy
      have h₂ := DyadicCube.dist_le_of_mem_star hxQ
      have h₃ := DyadicCube.dist_le_of_mem_star hxR
      have h₄ := dist_triangle y Q.center x
      have h₅ := dist_triangle y x R.center
      rw [dist_comm Q.center x] at h₄
      have hu := hupper Q hQ
      have hp := Q₀.side_pos
      exact (show dist y R.center ≤ 5 * Q₀.side by linarith)
    obtain ⟨hfin, hb⟩ := cube_packing T (hdisj.mono (fun _ h => h.1)) R.center
      (Q₀.side / 3) (5 * Q₀.side) (div_pos Q₀.side_pos (by norm_num))
      (mul_nonneg (by norm_num) Q₀.side_nonneg) hlow hsub
    refine ⟨hfin, ?_⟩
    have hp : 0 < (Q₀.side / 3) ^ d := pow_pos (div_pos Q₀.side_pos (by norm_num)) _
    have heq : (30 : ℝ) ^ d * (Q₀.side / 3) ^ d = (2 * (5 * Q₀.side)) ^ d := by
      rw [← mul_pow]
      congr 1
      ring
    have hb' : (T.ncard : ℝ) ≤ (30 : ℝ) ^ d := by
      nlinarith
    exact_mod_cast hb'
  · have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp ht
    change T.Finite ∧ T.ncard ≤ 30 ^ d
    rw [hempty]
    simp

/-- Bounded point multiplicity is a consequence of the nested packing
argument at two identical levels. -/
theorem point_multiplicity_bound {d : ℕ} {Ω : Set (Domain d)} {S : Set (DyadicCube d)}
    (hne : Ωᶜ.Nonempty) (hS : DistanceBounds Ω S)
    (hdisj : S.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)))
    (x : Domain d) :
    {Q | Q ∈ S ∧ x ∈ Q.star}.Finite ∧ {Q | Q ∈ S ∧ x ∈ Q.star}.ncard ≤ 30 ^ d := by
  classical
  let T : Set (DyadicCube d) := {Q | Q ∈ S ∧ x ∈ Q.star}
  by_cases ht : T.Nonempty
  · obtain ⟨R, hR, hxR⟩ := ht
    obtain ⟨hfin, hb⟩ := nested_meeting_bound (Subset.refl Ω) hne hS hS hdisj hR
    have hsub : T ⊆ {Q | Q ∈ S ∧ (R.star ∩ Q.star).Nonempty} :=
      fun Q hQ => ⟨hQ.1, ⟨x, hxR, hQ.2⟩⟩
    exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hb⟩
  · have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp ht
    change T.Finite ∧ T.ncard ≤ 30 ^ d
    rw [hempty]
    simp

/-- The boundary-distance estimates give local finiteness in the open
subtype, even though the family can accumulate at the excluded boundary. -/
theorem locallyFinite_stars {d : ℕ} (Ω : Opens (Domain d)) (S : Set (DyadicCube d))
    (hne : (Ω : Set (Domain d))ᶜ.Nonempty) (hS : DistanceBounds Ω S)
    (hdisj : S.Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier))) :
    LocallyFinite (fun Q : S => (Subtype.val : Ω → Domain d) ⁻¹' Q.val.star) := by
  classical
  intro x
  let δ := Metric.infDist (x : Domain d) (Ω : Set (Domain d))ᶜ
  have hδ : 0 < δ := Ω.isOpen.isClosed_compl.notMem_iff_infDist_pos hne |>.mp
    (show (x : Domain d) ∉ (Ω : Set (Domain d))ᶜ from not_not.mpr x.property)
  let T : Set (DyadicCube d) :=
    {Q | Q ∈ S ∧ (Q.star ∩ Metric.ball (x : Domain d) (δ / 2)).Nonempty}
  have hside (Q : DyadicCube d) (hQ : Q ∈ T) : δ / 44 ≤ Q.side := by
    obtain ⟨y, hyQ, hyx⟩ := hQ.2
    have hu := (hS Q hQ.1 y hyQ).2
    have hd := Metric.infDist_le_infDist_add_dist
      (x := (x : Domain d)) (y := y) (s := (Ω : Set (Domain d))ᶜ)
    have hxy : dist (x : Domain d) y < δ / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hyx
    dsimp [δ] at *
    linarith
  have hsub (Q : DyadicCube d) (hQ : Q ∈ T) :
      Q.carrier ⊆ Metric.closedBall (x : Domain d) δ := by
    obtain ⟨y, hyQ, hyx⟩ := hQ.2
    have hl := (hS Q hQ.1 y hyQ).1
    have hd := Metric.infDist_le_infDist_add_dist
      (x := y) (y := (x : Domain d)) (s := (Ω : Set (Domain d))ᶜ)
    have hy : dist y (x : Domain d) < δ / 2 := hyx
    have hupper : Q.side ≤ δ / 6 := by dsimp [δ] at *; linarith
    intro z hz
    have hz' : dist z Q.center ≤ Q.side / 2 := by
      simpa only [DyadicCube.carrier, DyadicCube.mem_dilate, one_mul] using hz
    have hy' := DyadicCube.dist_le_of_mem_star hyQ
    have ht₁ := dist_triangle z Q.center y
    rw [dist_comm Q.center y] at ht₁
    have ht₂ := dist_triangle z y (x : Domain d)
    exact (show dist z (x : Domain d) ≤ δ by linarith)
  have hfin := (cube_packing T (hdisj.mono (fun _ h => h.1)) x (δ / 44) δ
    (div_pos hδ (by norm_num)) hδ.le hside hsub).1
  let U : Set Ω := (Subtype.val : Ω → Domain d) ⁻¹' Metric.ball (x : Domain d) (δ / 2)
  refine ⟨U, ?_, ?_⟩
  · exact (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (Metric.mem_ball_self (div_pos hδ (by norm_num)))
  · have hf : {Q : S | Q.val ∈ T}.Finite := hfin.preimage Subtype.val_injective.injOn
    apply hf.subset
    intro Q hQ
    obtain ⟨y, hyQ, hyU⟩ := hQ
    exact ⟨Q.property, ⟨y, hyQ, hyU⟩⟩

namespace DyadicCube

theorem ext {d : ℕ} {Q R : DyadicCube d} (hl : Q.level = R.level)
    (hc : Q.corner = R.corner) : Q = R := by
  cases Q
  cases R
  cases hl
  cases hc
  rfl

/-- Interior membership supplies strict coordinate inequalities. -/
theorem coordinate_bounds_of_interior {d : ℕ} {Q : DyadicCube d} {x : Domain d}
    (hx : x ∈ interior Q.carrier) (i : Fin d) :
    Q.side * (Q.corner i : ℝ) < x i ∧ x i < Q.side * ((Q.corner i : ℝ) + 1) := by
  have hr : Q.side / 2 ≠ 0 := ne_of_gt (div_pos Q.side_pos (by norm_num))
  have hball : dist x Q.center < Q.side / 2 := by
    simpa only [carrier, dilate, one_mul, interior_closedBall _ hr, Metric.mem_ball] using hx
  have hi := (dist_pi_lt_iff (div_pos Q.side_pos (by norm_num))).mp hball i
  rw [Real.dist_eq] at hi
  have habs := abs_lt.mp hi
  dsimp only [center] at habs
  constructor <;> linarith

/-- At a fixed scale, distinct cubes have disjoint interiors. -/
theorem eq_of_same_level_interiors_inter {d : ℕ} {Q R : DyadicCube d}
    (hl : Q.level = R.level) (h : (interior Q.carrier ∩ interior R.carrier).Nonempty) : Q = R := by
  obtain ⟨x, hxQ, hxR⟩ := h
  have hs : R.side = Q.side := by simp only [side, hl]
  apply ext hl
  funext i
  have hQ := coordinate_bounds_of_interior hxQ i
  have hR := coordinate_bounds_of_interior hxR i
  rw [hs] at hR
  have h₁ : (Q.corner i : ℝ) < (R.corner i : ℝ) + 1 :=
    (mul_lt_mul_iff_right₀ Q.side_pos).mp (hQ.1.trans hR.2)
  have h₂ : (R.corner i : ℝ) < (Q.corner i : ℝ) + 1 :=
    (mul_lt_mul_iff_right₀ Q.side_pos).mp (hR.1.trans hQ.2)
  have h₁' : Q.corner i < R.corner i + 1 := by exact_mod_cast h₁
  have h₂' : R.corner i < Q.corner i + 1 := by exact_mod_cast h₂
  omega

/-- An intersecting cube at the next scale is precisely the dyadic parent. -/
theorem parent_eq_of_next_level_interiors_inter {d : ℕ} {Q R : DyadicCube d}
    (hl : R.level = Q.level + 1)
    (h : (interior Q.carrier ∩ interior R.carrier).Nonempty) : Q.parent = R := by
  obtain ⟨x, hxQ, hxR⟩ := h
  have hs : R.side = 2 * Q.side := by
    rw [side, hl, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    exact mul_comm _ _
  apply ext hl.symm
  funext i
  have hQ := coordinate_bounds_of_interior hxQ i
  have hR := coordinate_bounds_of_interior hxR i
  rw [hs] at hR
  have h₁ : (Q.corner i : ℝ) < 2 * ((R.corner i : ℝ) + 1) := by
    apply (mul_lt_mul_iff_right₀ Q.side_pos).mp
    calc
      Q.side * (Q.corner i : ℝ) < (2 * Q.side) * ((R.corner i : ℝ) + 1) := hQ.1.trans hR.2
      _ = Q.side * (2 * ((R.corner i : ℝ) + 1)) := by ring
  have h₂ : 2 * (R.corner i : ℝ) < (Q.corner i : ℝ) + 1 := by
    apply (mul_lt_mul_iff_right₀ Q.side_pos).mp
    calc
      Q.side * (2 * (R.corner i : ℝ)) = (2 * Q.side) * (R.corner i : ℝ) := by ring
      _ < Q.side * ((Q.corner i : ℝ) + 1) := hR.1.trans hQ.2
  have h₁' : Q.corner i < 2 * (R.corner i + 1) := by exact_mod_cast h₁
  have h₂' : 2 * R.corner i < Q.corner i + 1 := by exact_mod_cast h₂
  change Q.corner i / 2 = R.corner i
  omega

end DyadicCube

/-- The canonical cubes used in the source proof. -/
def maximalCubes {d : ℕ} (Ω : Set (Domain d)) : Set (DyadicCube d) :=
  {Q | Q.dilate 20 ⊆ Ω ∧ ¬ Q.parent.dilate 20 ⊆ Ω}

theorem maximalCubes_distance {d : ℕ} (Ω : Set (Domain d)) :
    DistanceBounds Ω (maximalCubes Ω) := by
  intro Q hQ x hx
  exact Q.distance_bounds_of_parent_failure hQ.1 hQ.2 x hx

theorem maximalCubes_inside {d : ℕ} {Ω : Set (Domain d)} {Q : DyadicCube d}
    (hQ : Q ∈ maximalCubes Ω) : Q.star ⊆ Ω := by
  apply Subset.trans ?_ hQ.1
  apply Metric.closedBall_subset_closedBall
  have := Q.side_pos
  linarith

theorem maximalCubes_cover {d : ℕ} {Ω : Set (Domain d)}
    (hΩ : IsOpen Ω) (hne : Ωᶜ.Nonempty) :
    (⋃ Q : maximalCubes Ω, Q.val.carrier) = Ω := by
  apply Subset.antisymm
  · apply iUnion_subset
    intro Q
    exact Q.val.carrier_subset_star.trans (maximalCubes_inside Q.property)
  · intro x hx
    obtain ⟨Q, hxQ, hQ, hp⟩ := DyadicCube.exists_admissible_parent_failure hΩ hne hx
    exact mem_iUnion.mpr ⟨⟨Q, hQ, hp⟩, hxQ⟩

/-- Parent failure, together with the dyadic grid, gives disjoint interiors.
Only the equal and adjacent scale cases need grid arithmetic: all wider
scale gaps are already excluded by the boundary-distance inequalities. -/
theorem maximalCubes_disjoint {d : ℕ} {Ω : Set (Domain d)} (hne : Ωᶜ.Nonempty) :
    (maximalCubes Ω).Pairwise (fun Q R => Disjoint (interior Q.carrier) (interior R.carrier)) := by
  have hdist := maximalCubes_distance Ω
  have ordered (Q R : DyadicCube d) (hQ : Q ∈ maximalCubes Ω) (hR : R ∈ maximalCubes Ω)
      (hl : Q.level ≤ R.level)
      (hi : (interior Q.carrier ∩ interior R.carrier).Nonempty) : Q = R := by
    by_cases heq : Q.level = R.level
    · exact DyadicCube.eq_of_same_level_interiors_inter heq hi
    by_cases hnext : R.level = Q.level + 1
    · have hp := DyadicCube.parent_eq_of_next_level_interiors_inter hnext hi
      exact False.elim (hQ.2 (hp ▸ hR.1))
    have hgap : Q.level + 2 ≤ R.level := by omega
    have hs : 4 * Q.side ≤ R.side := by
      have hz := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hgap
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hz
      norm_num at hz
      simpa only [DyadicCube.side, mul_comm] using hz
    obtain ⟨x, hxQ, hxR⟩ := hi
    have hxQ' := Q.carrier_subset_star (interior_subset hxQ)
    have hxR' := R.carrier_subset_star (interior_subset hxR)
    have hc := nested_side_le (Subset.refl Ω) hne hdist hdist hQ hR ⟨x, hxR', hxQ'⟩
    have := Q.side_pos
    linarith
  intro Q hQ R hR hneQR
  apply disjoint_iff_inter_eq_empty.mpr
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hi
  rcases le_total Q.level R.level with hl | hl
  · exact hneQR (ordered Q R hQ hR hl hi)
  · exact hneQR (ordered R Q hR hQ hl (by simpa only [inter_comm] using hi)).symm

/-- Passing from the ambient cube set to its subtype index preserves
both finiteness and the actual counting bound. -/
theorem subtype_counting_bound {α : Type*} (S : Set α) (P : α → Prop) (N : ℕ)
    (hf : {Q | Q ∈ S ∧ P Q}.Finite) (hb : {Q | Q ∈ S ∧ P Q}.ncard ≤ N) :
    {Q : S | P Q.val}.Finite ∧ {Q : S | P Q.val}.ncard ≤ N := by
  classical
  have hpre : ((Subtype.val : S → α) ⁻¹' {Q | Q ∈ S ∧ P Q}).Finite :=
    hf.preimage Subtype.val_injective.injOn
  refine ⟨hpre.subset (fun Q hQ => ⟨Q.property, hQ⟩), ?_⟩
  have himage : (Subtype.val : S → α) '' {Q : S | P Q.val} = {Q | Q ∈ S ∧ P Q} := by
    ext Q
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · rintro ⟨hQ, hP⟩
      exact ⟨⟨Q, hQ⟩, hP, rfl⟩
  rw [← Set.ncard_image_of_injective _ (Subtype.val_injective : Function.Injective (Subtype.val : S → α)),
    himage]
  exact hb

/-- All geometric conclusions are realized by the canonical maximal
cubes, rather than left as certificates to be assumed. -/
theorem geometric_whitney : Specs.ExpandedFA.PartIV.HardyWhitney.geometricWhitneyType := by
  intro d hd Ω
  let S := maximalCubes (Ω.val : Set (Domain d))
  have hne := complement_nonempty hd Ω.property.2
  have hdist : DistanceBounds Ω.val S := maximalCubes_distance _
  have hdisj := maximalCubes_disjoint hne
  refine ⟨S, maximalCubes_cover Ω.val.isOpen hne, hdisj, ?_,
    locallyFinite_stars Ω.val S hne hdist hdisj, ?_, ?_, hdist⟩
  · intro Q
    exact ⟨Q.val.isCompact_dilate _, maximalCubes_inside Q.property⟩
  · intro x
    obtain ⟨hf, hb⟩ := point_multiplicity_bound hne hdist hdisj x
    exact subtype_counting_bound S (fun Q => x ∈ Q.star) _ hf hb
  · intro Q R h
    exact ⟨nested_side_le (Subset.refl _) hne hdist hdist R.property Q.property h,
      nested_side_le (Subset.refl _) hne hdist hdist Q.property R.property
        (by simpa only [inter_comm] using h)⟩

/-- The canonical choices also satisfy every nested-level geometric
assertion, with the same constants for all pairs of eligible domains. -/
theorem maximalCubes_nested {d : ℕ} (hd : 0 < d) (Ω Ω' : EligibleOpen d)
    (hΩ : (Ω'.val : Set (Domain d)) ⊆ Ω.val) :
    (∀ (R : maximalCubes (Ω'.val : Set (Domain d))) (Q : maximalCubes (Ω.val : Set (Domain d))),
      (R.val.star ∩ Q.val.star).Nonempty →
        R.val.side ≤ 8 * Q.val.side ∧ R.val.star ⊆ Q.val.dilate 8) ∧
    (∀ R : maximalCubes (Ω'.val : Set (Domain d)),
      {Q : maximalCubes (Ω.val : Set (Domain d)) | (R.val.star ∩ Q.val.star).Nonempty}.Finite ∧
      {Q : maximalCubes (Ω.val : Set (Domain d)) | (R.val.star ∩ Q.val.star).Nonempty}.ncard ≤ 30 ^ d) := by
  have hne := complement_nonempty hd Ω.property.2
  have hc := maximalCubes_distance (Ω.val : Set (Domain d))
  have hf := maximalCubes_distance (Ω'.val : Set (Domain d))
  constructor
  · intro R Q h
    exact nested_size_and_containment hΩ hne hc hf Q.property R.property h
  · intro R
    obtain ⟨hfin, hb⟩ := nested_meeting_bound hΩ hne hc hf (maximalCubes_disjoint hne) R.property
    exact subtype_counting_bound (maximalCubes (Ω.val : Set (Domain d))) (fun Q : DyadicCube d => (R.val.star ∩ Q.star).Nonempty) _ hfin hb

/-- The unnormalized cutoff for one cube. All cubes use the same
ratio of outer to inner radius, so these are translates and dilates
of a single fixed smooth function. -/
noncomputable def cubeBump {d : ℕ} (Q : DyadicCube d) : ContDiffBump Q.center where
  rIn := Q.side / 2
  rOut := (9 / 16) * Q.side
  rIn_pos := div_pos Q.side_pos (by norm_num)
  rIn_lt_rOut := by have := Q.side_pos; linarith

theorem cubeBump_contDiff {d : ℕ} (Q : DyadicCube d) : ContDiff ℝ (⊤ : ℕ∞) (cubeBump Q) :=
  (cubeBump Q).contDiff

theorem cubeBump_nonneg {d : ℕ} (Q : DyadicCube d) (x : Domain d) :
    0 ≤ cubeBump Q x := (cubeBump Q).nonneg

theorem cubeBump_le_one {d : ℕ} (Q : DyadicCube d) (x : Domain d) :
    cubeBump Q x ≤ 1 := (cubeBump Q).le_one

theorem cubeBump_one {d : ℕ} (Q : DyadicCube d) {x : Domain d} (hx : x ∈ Q.carrier) :
    cubeBump Q x = 1 := by
  apply (cubeBump Q).one_of_mem_closedBall
  simpa only [cubeBump, DyadicCube.carrier, DyadicCube.dilate, one_mul] using hx

theorem cubeBump_tsupport {d : ℕ} (Q : DyadicCube d) : tsupport (cubeBump Q) = Q.star := by
  rw [(cubeBump Q).tsupport_eq]
  unfold cubeBump DyadicCube.star DyadicCube.dilate
  congr 1
  ring

/-- Each cutoff is already a genuine test function on every open domain
containing its enlarged cube. -/
noncomputable def cubeTest {d : ℕ} (Ω : Opens (Domain d)) (Q : DyadicCube d)
    (hQ : Q.star ⊆ Ω) : Tests ℝ Ω where
  toFun := cubeBump Q
  contDiff' := cubeBump_contDiff Q
  hasCompactSupport' := (cubeBump Q).hasCompactSupport
  tsupport_subset' := (cubeBump_tsupport Q).subset.trans hQ

/-- Fixed reference cutoff at unit scale, centered at the origin. -/
noncomputable def unitBump (d : ℕ) : ContDiffBump (0 : Domain d) where
  rIn := 1 / 2
  rOut := 9 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The family uses one reference shape, which is essential for uniform
constants across the infinitely many cubes. -/
theorem cubeBump_eq_rescaled {d : ℕ} (Q : DyadicCube d) (x : Domain d) :
    cubeBump Q x = unitBump d (Q.side⁻¹ • (x - Q.center)) := by
  simp only [ContDiffBump.apply, cubeBump, unitBump]
  have hs : Q.side ≠ 0 := ne_of_gt Q.side_pos
  apply congrArg₂ (someContDiffBumpBase (Domain d)).toFun
  · field_simp [hs]
  · ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero]
    field_simp [hs]

/-- Uniform operator-norm derivative bounds for the scaled cutoffs. These
imply the corresponding bounds for every coordinate partial derivative. -/
theorem cubeBump_derivative_bounds (d : ℕ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ (Q : DyadicCube d) (k : ℕ) (x : Domain d),
        ‖iteratedFDeriv ℝ k (cubeBump Q) x‖ ≤ B k * Q.side ^ (-(k : ℤ)) := by
  classical
  have hbound (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Domain d, ‖iteratedFDeriv ℝ k (unitBump d) x‖ ≤ C := by
    obtain ⟨C, hC, h⟩ := (unitBump d).hasCompactSupport.exists_bound_iteratedFDeriv
      (unitBump d).contDiff k
    exact ⟨C, hC, h k le_rfl⟩
  choose C hC hboundC using hbound
  refine ⟨fun k => C k + 1, fun k => by linarith [hC k], ?_⟩
  intro Q k x
  let L : Domain d →L[ℝ] Domain d := Q.side⁻¹ • ContinuousLinearMap.id ℝ (Domain d)
  have hL : ‖L‖ ≤ Q.side⁻¹ := by
    apply L.opNorm_le_bound (inv_nonneg.mpr Q.side_nonneg)
    intro v
    simp only [L, smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Q.side_pos)]
    exact le_rfl
  have heq : (cubeBump Q : Domain d → ℝ) =
      fun y => ((unitBump d : Domain d → ℝ) ∘ L) (y - Q.center) := by
    funext y
    exact cubeBump_eq_rescaled Q y
  have hf : ContDiff ℝ (⊤ : ℕ∞) (unitBump d) := (unitBump d).contDiff
  rw [heq, iteratedFDeriv_comp_sub,
    L.iteratedFDeriv_comp_right hf _ (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (unitBump d) (L (x - Q.center))‖ * ∏ _i : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C k * (Q.side⁻¹) ^ k := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hboundC k _) (pow_le_pow_left₀ (norm_nonneg L) hL _)
        (pow_nonneg (norm_nonneg L) _) (hC k)
    _ ≤ (C k + 1) * Q.side ^ (-(k : ℤ)) := by
      rw [zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (pow_nonneg Q.side_nonneg _))

end ExpandedFA.PartIV.HardyWhitney

open Set TopologicalSpace MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- A locally finite family of closed supports has a finite-sum germ at
an interior point, using exactly the supports containing that point. -/
theorem finsum_germ_on_open {d : ℕ} {ι : Type*} (Ω : Opens (Domain d))
    (f : ι → Domain d → ℝ) (s : ι → Set (Domain d))
    (hs : ∀ i, IsClosed (s i))
    (hlf : LocallyFinite (fun i => (Subtype.val : Ω → Domain d) ⁻¹' s i))
    (hfs : ∀ i, Function.support (f i) ⊆ s i)
    {x : Domain d} (hx : x ∈ Ω) :
    ∃ t : Finset ι, (∀ i, i ∈ t ↔ x ∈ s i) ∧
      (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ t, f i y) := by
  classical
  have hf : {i | x ∈ s i}.Finite := hlf.point_finite (⟨x, hx⟩ : Ω)
  refine ⟨hf.toFinset, fun i => hf.mem_toFinset, ?_⟩
  have he := hlf.eventually_subset (fun i => (hs i).preimage continuous_subtype_val)
    (⟨x, hx⟩ : Ω)
  have he' : ∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} := by
    rw [← Ω.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hx⟩ : Ω)]
    exact he
  filter_upwards [he'] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact hf.mem_toFinset.mpr (hy (hfs i hi))

theorem contDiffAt_finsum_on_open {d : ℕ} {ι : Type*} (Ω : Opens (Domain d))
    (f : ι → Domain d → ℝ) (s : ι → Set (Domain d))
    (hs : ∀ i, IsClosed (s i))
    (hlf : LocallyFinite (fun i => (Subtype.val : Ω → Domain d) ⁻¹' s i))
    (hfs : ∀ i, Function.support (f i) ⊆ s i)
    (hfd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {x : Domain d} (hx : x ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∑ᶠ i, f i y) x := by
  obtain ⟨t, ht, he⟩ := finsum_germ_on_open Ω f s hs hlf hfs hx
  exact ((ContDiff.sum fun i _ => hfd i).contDiffAt).congr_of_eventuallyEq he

end ExpandedFA.PartIV.HardyWhitney

open Set TopologicalSpace MeasureTheory

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- Nonnegative real tests dominate their lower bound times the actual volume
of every dyadic carrier on which the lower bound holds. -/
theorem test_integral_lower_bound {d : ℕ} {Ω : Opens (Domain d)}
    (f : Tests ℝ Ω) (Q : DyadicCube d) (c : ℝ)
    (hnonneg : ∀ x, 0 ≤ f x) (hlower : ∀ x ∈ Q.carrier, c ≤ f x) :
    Integrable f ∧ c * (volume Q.carrier).toReal ≤ ∫ x, f x := by
  have hint : Integrable f := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  refine ⟨hint, ?_⟩
  have hcarrier : MeasurableSet Q.carrier := (Q.isCompact_dilate 1).measurableSet
  have hfinite : volume Q.carrier ≠ ⊤ := by
    rw [Q.volume_carrier]
    exact ENNReal.ofReal_ne_top
  calc
    c * (volume Q.carrier).toReal ≤ ∫ x in Q.carrier, f x :=
      setIntegral_ge_of_const_le_real hcarrier hfinite hlower hint.integrableOn
    _ ≤ ∫ x, f x := setIntegral_le_integral hint (Filter.Eventually.of_forall hnonneg)

/-- The exact normalized-bump lower bound needed in the Whitney application. -/
theorem test_integral_lower_bound_inv {d : ℕ} {Ω : Opens (Domain d)}
    (f : Tests ℝ Ω) (Q : DyadicCube d) (N : ℕ)
    (hnonneg : ∀ x, 0 ≤ f x) (hlower : ∀ x ∈ Q.carrier, 1 / (N : ℝ) ≤ f x) :
    Integrable f ∧ (1 / (N : ℝ)) * (volume Q.carrier).toReal ≤ ∫ x, f x :=
  test_integral_lower_bound f Q _ hnonneg hlower

end ExpandedFA.PartIV.HardyWhitney

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- Analytic properties used to assemble the partition estimates. Geometric
clauses and the integral inequality are obtained from the cube construction. -/
def NormalizedWeightEstimates {d : ℕ} (A : ℕ → ℝ) (Ω : EligibleOpen d)
    (η : maximalCubes (Ω.val : Set (Domain d)) → Tests ℝ Ω.val) : Prop :=
  (∀ Q x, 0 ≤ η Q x) ∧
  (∀ Q, tsupport (η Q) ⊆ Q.val.star) ∧
  (∀ x ∈ Ω.val, ∑ᶠ Q, η Q x = 1) ∧
  (∀ Q, ∀ x ∈ Q.val.carrier, 1 / ((30 ^ d : ℕ) : ℝ) ≤ η Q x) ∧
  (∀ Q (k : ℕ) (a : Fin k → Fin d) (x : Domain d),
    ‖iteratedFDeriv ℝ k (η Q) x (fun j => coordinateVector (a j))‖ ≤
      A k * Q.val.side ^ (-(k : ℤ)))

/-- Canonical geometric data for the simultaneous maximal-cube selection. -/
theorem maximalCubes_geometry {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d) :
    CubeGeometry Ω.val (maximalCubes (Ω.val : Set (Domain d))) := by
  let S := maximalCubes (Ω.val : Set (Domain d))
  have hne := complement_nonempty hd Ω.property.2
  have hdist : DistanceBounds Ω.val S := maximalCubes_distance _
  have hdisj := maximalCubes_disjoint hne
  refine ⟨maximalCubes_cover Ω.val.isOpen hne, hdisj, ?_,
    locallyFinite_stars Ω.val S hne hdist hdisj, ?_, ?_, hdist⟩
  · intro Q
    exact ⟨Q.val.isCompact_dilate _, maximalCubes_inside Q.property⟩
  · intro x
    obtain ⟨hf, hb⟩ := point_multiplicity_bound hne hdist hdisj x
    exact subtype_counting_bound S (fun Q => x ∈ Q.star) _ hf hb
  · intro Q R h
    exact ⟨nested_side_le (Subset.refl _) hne hdist hdist R.property Q.property h,
      nested_side_le (Subset.refl _) hne hdist hdist Q.property R.property
        (by simpa only [inter_comm] using h)⟩

/-- Assemble geometric and analytic estimates with uniform constants
`c = 1 / 30^d`, `C = 8` and `N = 30^d`. -/
theorem smooth_whitney_from_normalized_weights {d : ℕ} (hd : 0 < d)
    (hanalytic : ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ Ω : EligibleOpen d, ∃ η : maximalCubes (Ω.val : Set (Domain d)) → Tests ℝ Ω.val,
        NormalizedWeightEstimates A Ω η) :
    ∃ (c C : ℝ) (A : ℕ → ℝ) (N : ℕ),
      0 < c ∧ 1 ≤ C ∧ (∀ k, 0 < A k) ∧ 0 < N ∧
      ∃ W : ∀ Ω : EligibleOpen d, Partition Ω.val,
        (∀ Ω, PartitionEstimates c C A N (W Ω)) ∧
        (∀ Ω Ω' : EligibleOpen d,
          (Ω'.val : Set (Domain d)) ⊆ Ω.val → NestedEstimates C N (W Ω) (W Ω')) := by
  classical
  obtain ⟨A, hA, hweights⟩ := hanalytic
  choose η hη using hweights
  let W : ∀ Ω : EligibleOpen d, Partition Ω.val :=
    fun Ω => ⟨maximalCubes (Ω.val : Set (Domain d)), η Ω⟩
  refine ⟨1 / ((30 ^ d : ℕ) : ℝ), 8, A, 30 ^ d, by positivity, by norm_num, hA,
    by positivity, W, ?_, ?_⟩
  · intro Ω
    obtain ⟨hcover, hdisj, hinside, hlocal, hoverlap, hneighbor, _⟩ :=
      maximalCubes_geometry hd Ω
    obtain ⟨hnonneg, hsupp, hsum, hlower, hderiv⟩ := hη Ω
    refine ⟨hcover, hdisj, hinside, hlocal, hoverlap, hnonneg, hsupp, hsum, ?_, hderiv, ?_⟩
    · intro Q
      exact test_integral_lower_bound_inv (η Ω Q) Q.val (30 ^ d) (hnonneg Q) (hlower Q)
    · intro Q R h
      obtain ⟨hQR, hRQ⟩ := hneighbor Q R h
      constructor <;> nlinarith [Q.val.side_pos, R.val.side_pos]
  · intro Ω Ω' hΩ
    exact maximalCubes_nested hd Ω Ω' hΩ

end ExpandedFA.PartIV.HardyWhitney

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- Coordinate vectors have norm at most one for the paper's supremum norm. -/
theorem coordinateVector_norm_le_one {d : ℕ} (i : Fin d) :
    ‖coordinateVector i‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro j
  by_cases h : j = i
  · subst j
    simp [coordinateVector]
  · simp [coordinateVector, Pi.single_eq_of_ne h]

/-- Operator derivative estimates imply all coordinate-word estimates without
loss in the constant, including derivative order zero. -/
theorem coordinate_derivative_le_operator {d k : ℕ} (f : Domain d → ℝ)
    (a : Fin k → Fin d) (x : Domain d) :
    ‖iteratedFDeriv ℝ k f x (fun j => coordinateVector (a j))‖ ≤
      ‖iteratedFDeriv ℝ k f x‖ := by
  apply (iteratedFDeriv ℝ k f x).unit_le_opNorm
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro j
  exact coordinateVector_norm_le_one (a j)

end ExpandedFA.PartIV.HardyWhitney


open Set TopologicalSpace MeasureTheory
open scoped Topology
namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

noncomputable def cutoffSum {d : ℕ} (S : Set (DyadicCube d)) (x : Domain d) : ℝ :=
  ∑ᶠ Q : S, cubeBump Q.val x

noncomputable def normalizedCutoff {d : ℕ} (S : Set (DyadicCube d)) (Q : S)
    (x : Domain d) : ℝ := cubeBump Q.val x / cutoffSum S x

theorem cutoffSum_eq_sum {d : ℕ} (S : Set (DyadicCube d)) (x : Domain d)
    (hf : {Q : S | x ∈ Q.val.star}.Finite) :
    cutoffSum S x = ∑ Q ∈ hf.toFinset, cubeBump Q.val x := by
  apply finsum_eq_sum_of_support_subset_of_finite _ _ hf
  intro Q hQ
  change x ∈ Q.val.star
  simpa only [cubeBump_tsupport] using subset_tsupport (cubeBump Q.val) hQ

theorem cutoffSum_nonneg {d : ℕ} (S : Set (DyadicCube d)) (x : Domain d) :
    0 ≤ cutoffSum S x := by
  exact finsum_nonneg fun Q => cubeBump_nonneg Q.val x

theorem cutoffSum_bounds {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S) (x : Domain d) (hx : x ∈ Ω) :
    1 ≤ cutoffSum S x ∧ cutoffSum S x ≤ (30 ^ d : ℕ) := by
  classical
  obtain ⟨hf, hn⟩ := hG.2.2.2.2.1 x
  rw [cutoffSum_eq_sum S x hf]
  constructor
  · have hcover : x ∈ ⋃ Q : S, Q.val.carrier := hG.1.symm ▸ hx
    obtain ⟨Q, hQ⟩ := mem_iUnion.mp hcover
    have hstar : x ∈ Q.val.star := by
      rw [← cubeBump_tsupport]
      apply subset_tsupport
      rw [Function.mem_support, cubeBump_one Q.val hQ]
      norm_num
    have hmem : Q ∈ hf.toFinset := hf.mem_toFinset.mpr hstar
    calc
      1 = cubeBump Q.val x := (cubeBump_one Q.val hQ).symm
      _ ≤ ∑ R ∈ hf.toFinset, cubeBump R.val x := Finset.single_le_sum
        (fun R _ => cubeBump_nonneg R.val x) hmem
  · calc
      _ ≤ ∑ _Q ∈ hf.toFinset, (1 : ℝ) := Finset.sum_le_sum fun Q _ => cubeBump_le_one Q.val x
      _ = (hf.toFinset.card : ℝ) := by simp
      _ ≤ (30 ^ d : ℕ) := by
        rw [Set.ncard_eq_toFinset_card _ hf] at hn
        exact_mod_cast hn

theorem normalizedCutoff_nonneg {d : ℕ} (S : Set (DyadicCube d)) (Q : S) (x : Domain d) :
    0 ≤ normalizedCutoff S Q x :=
  div_nonneg (cubeBump_nonneg Q.val x) (cutoffSum_nonneg S x)

theorem normalizedCutoff_tsupport {d : ℕ} (S : Set (DyadicCube d)) (Q : S) :
    tsupport (normalizedCutoff S Q) ⊆ Q.val.star := by
  rw [← cubeBump_tsupport Q.val]
  change tsupport (fun x => cubeBump Q.val x / cutoffSum S x) ⊆ _
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

theorem cutoffSum_contDiffAt {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S) (x : Domain d) (hx : x ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (cutoffSum S) x := by
  apply contDiffAt_finsum_on_open Ω (fun Q : S => (cubeBump Q.val : Domain d → ℝ))
    (fun Q => Q.val.star) (fun Q => (Q.val.isCompact_dilate _).isClosed)
    hG.2.2.2.1
  · intro Q y hy
    simpa only [cubeBump_tsupport] using subset_tsupport (cubeBump Q.val) hy
  · exact fun Q => cubeBump_contDiff Q.val
  · exact hx

theorem normalizedCutoff_contDiff {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S)
    (hs : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) (cutoffSum S) x) (Q : S) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedCutoff S Q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Q.val.star
  · have hxΩ := (hG.2.2.1 Q).2 hx
    exact (cubeBump_contDiff Q.val).contDiffAt.div (hs x hxΩ)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffSum_bounds hG x hxΩ).1))
  · have hz : normalizedCutoff S Q =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (normalizedCutoff_tsupport S Q h))
    exact contDiffAt_const.congr_of_eventuallyEq hz

noncomputable def normalizedTest {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S)
    (hs : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) (cutoffSum S) x) (Q : S) : Tests ℝ Ω where
  toFun := normalizedCutoff S Q
  contDiff' := normalizedCutoff_contDiff hG hs Q
  hasCompactSupport' := (hG.2.2.1 Q).1.of_isClosed_subset (isClosed_tsupport _)
    (normalizedCutoff_tsupport S Q)
  tsupport_subset' := (normalizedCutoff_tsupport S Q).trans (hG.2.2.1 Q).2

theorem normalizedCutoff_sum {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S) (x : Domain d) (hx : x ∈ Ω) :
    ∑ᶠ Q : S, normalizedCutoff S Q x = 1 := by
  classical
  have hf : Function.HasFiniteSupport (fun Q : S => cubeBump Q.val x) :=
    (hG.2.2.2.2.1 x).1.subset fun Q hQ =>
      by
        change x ∈ Q.val.star
        simpa only [cubeBump_tsupport] using subset_tsupport (cubeBump Q.val) hQ
  simp only [normalizedCutoff, div_eq_mul_inv]
  rw [← finsum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffSum_bounds hG x hx).1))

theorem normalizedCutoff_lower {d : ℕ} {Ω : Opens (Domain d)} {S : Set (DyadicCube d)}
    (hG : CubeGeometry Ω S) (Q : S) {x : Domain d} (hx : x ∈ Q.val.carrier) :
    ((30 ^ d : ℕ) : ℝ)⁻¹ ≤ normalizedCutoff S Q x := by
  have hstar : x ∈ Q.val.star := by
    rw [← cubeBump_tsupport]
    apply subset_tsupport
    rw [Function.mem_support, cubeBump_one Q.val hx]
    norm_num
  have hb := cutoffSum_bounds hG x ((hG.2.2.1 Q).2 hstar)
  simp only [normalizedCutoff, cubeBump_one Q.val hx, one_div]
  exact inv_anti₀ (lt_of_lt_of_le zero_lt_one hb.1) hb.2

/-- The canonical normalized Whitney test function, with smoothness obtained
from the proved local finiteness of the enlarged cubes. -/
noncomputable def whitneyWeight {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (Q : maximalCubes (Ω.val : Set (Domain d))) : Tests ℝ Ω.val :=
  normalizedTest (maximalCubes_geometry hd Ω)
    (cutoffSum_contDiffAt (maximalCubes_geometry hd Ω)) Q

@[simp] theorem whitneyWeight_apply {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (Q : maximalCubes (Ω.val : Set (Domain d))) (x : Domain d) :
    whitneyWeight hd Ω Q x = normalizedCutoff (maximalCubes (Ω.val : Set (Domain d))) Q x := rfl

theorem whitneyWeight_nonneg {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (Q : maximalCubes (Ω.val : Set (Domain d))) (x : Domain d) :
    0 ≤ whitneyWeight hd Ω Q x := normalizedCutoff_nonneg _ _ _

theorem whitneyWeight_tsupport {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (Q : maximalCubes (Ω.val : Set (Domain d))) :
    tsupport (whitneyWeight hd Ω Q) ⊆ Q.val.star := normalizedCutoff_tsupport _ _

theorem whitneyWeight_sum {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (x : Domain d) (hx : x ∈ Ω.val) :
    ∑ᶠ Q, whitneyWeight hd Ω Q x = 1 :=
  normalizedCutoff_sum (maximalCubes_geometry hd Ω) x hx

theorem whitneyWeight_lower {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d)
    (Q : maximalCubes (Ω.val : Set (Domain d))) (x : Domain d) (hx : x ∈ Q.val.carrier) :
    1 / ((30 ^ d : ℕ) : ℝ) ≤ whitneyWeight hd Ω Q x := by
  simpa only [whitneyWeight_apply, one_div] using
    normalizedCutoff_lower (maximalCubes_geometry hd Ω) Q hx

end ExpandedFA.PartIV.HardyWhitney

open Set TopologicalSpace MeasureTheory

namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- Comparing sides transfers inverse-power derivative scales. -/
theorem neg_pow_le_three_mul_of_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ≤ 3 * b) (k : ℕ) :
    b ^ (-(k : ℤ)) ≤ (3 : ℝ) ^ k * a ^ (-(k : ℤ)) := by
  have hinv : b⁻¹ ≤ 3 * a⁻¹ := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using
      (div_le_div_iff₀ hb ha).mpr (show 1 * a ≤ 3 * b by simpa using h)
  simp only [zpow_neg, zpow_natCast, ← inv_pow]
  calc
    (b⁻¹) ^ k ≤ (3 * a⁻¹) ^ k :=
      pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hinv k
    _ = (3 : ℝ) ^ k * (a⁻¹) ^ k := mul_pow _ _ _

/-- The derivatives of a finite family of neighboring cube cutoffs satisfy a
uniform sum estimate. The index map allows a finset of the actual cube subtype. -/
theorem finite_cubeBump_sum_derivative_bound {d : ℕ} {ι : Type*} [DecidableEq ι]
    (q : ι → DyadicCube d) (t : Finset ι) (Q : DyadicCube d) (N : ℕ)
    (B : ℕ → ℝ) (hBnonneg : ∀ k, 0 ≤ B k)
    (hB : ∀ (R : DyadicCube d) (k : ℕ) (x : Domain d),
      ‖iteratedFDeriv ℝ k (cubeBump R) x‖ ≤ B k * R.side ^ (-(k : ℤ)))
    (hcard : t.card ≤ N) (hside : ∀ i ∈ t, Q.side ≤ 3 * (q i).side)
    (k : ℕ) (x : Domain d) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i ∈ t, cubeBump (q i) y) x‖ ≤
      (N : ℝ) * B k * (3 : ℝ) ^ k * Q.side ^ (-(k : ℤ)) := by
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((cubeBump_contDiff (q i)).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt)]
  have hp : 0 ≤ B k * (3 : ℝ) ^ k * Q.side ^ (-(k : ℤ)) :=
    mul_nonneg (mul_nonneg (hBnonneg k) (pow_nonneg (by norm_num) k))
      (zpow_nonneg Q.side_nonneg _)
  calc
    ‖∑ i ∈ t, iteratedFDeriv ℝ k (cubeBump (q i)) x‖ ≤
        ∑ i ∈ t, ‖iteratedFDeriv ℝ k (cubeBump (q i)) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ t, B k * (3 : ℝ) ^ k * Q.side ^ (-(k : ℤ)) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ B k * (q i).side ^ (-(k : ℤ)) := hB (q i) k x
        _ ≤ B k * ((3 : ℝ) ^ k * Q.side ^ (-(k : ℤ))) :=
          mul_le_mul_of_nonneg_left
            (neg_pow_le_three_mul_of_le Q.side_pos (q i).side_pos (hside i hi) k) (hBnonneg k)
        _ = _ := by ring
    _ = (t.card : ℝ) * (B k * (3 : ℝ) ^ k * Q.side ^ (-(k : ℤ))) := by simp
    _ ≤ (N : ℝ) * (B k * (3 : ℝ) ^ k * Q.side ^ (-(k : ℤ))) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hp
    _ = _ := by ring

end ExpandedFA.PartIV.HardyWhitney


open Set Filter
open scoped Topology ContDiff

namespace ExpandedFA.PartIV.HardyWhitney.Analytic

/-- A bump that is one on `[1,N]` and vanishes on a neighborhood of zero. -/
noncomputable def reciprocalBump (N : ℕ) : ContDiffBump ((N : ℝ) + 1) where
  rIn := (N : ℝ) + 1 / 2
  rOut := (N : ℝ) + 3 / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def reciprocalCutoff (N : ℕ) (t : ℝ) : ℝ :=
  reciprocalBump N t * t⁻¹

theorem reciprocalCutoff_contDiff (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (reciprocalCutoff N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hb : (0 : ℝ) ∉ tsupport (reciprocalBump N) := by
      rw [(reciprocalBump N).tsupport_eq]
      simp only [Metric.mem_closedBall, Real.dist_eq, reciprocalBump]
      rw [abs_of_nonpos (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith)]
      push Not
      linarith
    have he : reciprocalCutoff N =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hb] with y hy
      simp only [reciprocalCutoff, hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (reciprocalBump N).contDiff.contDiffAt.mul (contDiffAt_inv ℝ ht)

theorem reciprocalCutoff_hasCompactSupport (N : ℕ) :
    HasCompactSupport (reciprocalCutoff N) :=
  (reciprocalBump N).hasCompactSupport.mul_right

theorem reciprocalCutoff_eventuallyEq_inv {E : Type*} [TopologicalSpace E]
    {N : ℕ} {H : E → ℝ} {x : E} (hH : ContinuousAt H x)
    (hlo : 1 ≤ H x) (hhi : H x ≤ N) :
    (fun y => reciprocalCutoff N (H y)) =ᶠ[𝓝 x] (fun y => (H y)⁻¹) := by
  have hx : H x ∈ Metric.ball ((N : ℝ) + 1) (reciprocalBump N).rIn := by
    simp only [Metric.mem_ball, Real.dist_eq, reciprocalBump]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hb := (reciprocalBump N).eventuallyEq_one_of_mem_ball hx
  filter_upwards [hH.eventually hb] with y hy
  simp only [reciprocalCutoff, hy, Pi.one_apply, one_mul]

noncomputable def jetEnvelope (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (k + 1), |M i|

theorem one_le_jetEnvelope (M : ℕ → ℝ) (k : ℕ) : 1 ≤ jetEnvelope M k := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => abs_nonneg _))

theorem coefficient_le_jetEnvelope_pow (M : ℕ → ℝ) {i k : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) : M i ≤ jetEnvelope M k ^ i := by
  have hle : |M i| ≤ ∑ j ∈ Finset.range (k + 1), |M j| :=
    Finset.single_le_sum (fun j hj => abs_nonneg (M j)) (Finset.mem_range.mpr (by omega))
  calc
    M i ≤ |M i| := le_abs_self _
    _ ≤ jetEnvelope M k := by unfold jetEnvelope; linarith
    _ ≤ jetEnvelope M k ^ i := le_self_pow₀ (one_le_jetEnvelope M k) (by omega)

/-- Uniform operator-derivative estimates for quotients at points where the denominator
lies in `[1,N]`. The two functions are globally smooth; no global lower bound on the
denominator is required. `B` and `M` bound the jets of numerator and denominator at the
point, with scale `r`. Constants depend only on these sequences and `N`. -/
theorem quotient_derivative_bounds (N : ℕ) (B M : ℕ → ℝ) :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (f H : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hH : ContDiff ℝ (⊤ : ℕ∞) H) (x : E) (r : ℝ) (hr : 0 < r) (k : ℕ),
        1 ≤ H x → H x ≤ N →
        (∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ B i * (r⁻¹) ^ i) →
        (∀ i ≤ k, ‖iteratedFDeriv ℝ i H x‖ ≤ M i * (r⁻¹) ^ i) →
        ‖iteratedFDeriv ℝ k (fun y => f y / H y) x‖ ≤ A k * (r⁻¹) ^ k := by
  classical
  have hC (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i ≤ k, ∀ t, ‖iteratedFDeriv ℝ i (reciprocalCutoff N) t‖ ≤ C :=
    (reciprocalCutoff_hasCompactSupport N).exists_bound_iteratedFDeriv
      (reciprocalCutoff_contDiff N) k
  choose C hC hCb using hC
  let I : ℕ → ℝ := fun j => (j.factorial : ℝ) * C j * jetEnvelope M j ^ j
  have hI (j : ℕ) : 0 ≤ I j := by
    dsimp [I]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j))
      (pow_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_jetEnvelope M j)) _)
  let A : ℕ → ℝ := fun k => 1 + ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * |B i| * I (k - i)
  have hA (k : ℕ) : 0 < A k := by
    dsimp [A]
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * |B i| * I (k - i) :=
      Finset.sum_nonneg (fun i hi => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (hI _))
    linarith
  refine ⟨A, hA, ?_⟩
  intro E _ _ f H hf hH x r hr k hlo hhi hfjet hHjet
  have hr' : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hinv (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j ((reciprocalCutoff N) ∘ H) x‖ ≤ I j * (r⁻¹) ^ j := by
    have hb := norm_iteratedFDeriv_comp_le
      (reciprocalCutoff_contDiff N) hH
      (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
      x (fun i hi => hCb j i hi (H x)) (D := jetEnvelope M j * r⁻¹) ?_
    · calc
        _ ≤ (j.factorial : ℝ) * C j * (jetEnvelope M j * r⁻¹) ^ j := hb
        _ = I j * (r⁻¹) ^ j := by dsimp [I]; rw [mul_pow]; ring
    · intro i hi hij
      calc
        ‖iteratedFDeriv ℝ i H x‖ ≤ M i * (r⁻¹) ^ i := hHjet i (hij.trans hj)
        _ ≤ jetEnvelope M j ^ i * (r⁻¹) ^ i :=
          mul_le_mul_of_nonneg_right (coefficient_le_jetEnvelope_pow M hi hij)
            (pow_nonneg hr' _)
        _ = (jetEnvelope M j * r⁻¹) ^ i := (mul_pow _ _ _).symm
  have he : (fun y => f y / H y) =ᶠ[𝓝 x]
      (fun y => f y * reciprocalCutoff N (H y)) := by
    filter_upwards [reciprocalCutoff_eventuallyEq_inv hH.continuous.continuousAt hlo hhi]
      with y hy
    rw [div_eq_mul_inv, hy]
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k - i) ((reciprocalCutoff N) ∘ H) x‖ :=
      norm_iteratedFDeriv_mul_le hf ((reciprocalCutoff_contDiff N).comp hH) x
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (|B i| * (r⁻¹) ^ i) * (I (k - i) * (r⁻¹) ^ (k - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left ((hfjet i hik).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr' _)))
          (Nat.cast_nonneg _)
      · exact hinv (k - i) (Nat.sub_le _ _)
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hr' _))
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |B i| * I (k - i)) *
        (r⁻¹) ^ k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show (r⁻¹) ^ k = (r⁻¹) ^ i * (r⁻¹) ^ (k - i) by
        rw [← pow_add, Nat.add_sub_of_le hik]]
      ring
    _ ≤ A k * (r⁻¹) ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr' _)
      dsimp [A]
      linarith

end ExpandedFA.PartIV.HardyWhitney.Analytic

open Set TopologicalSpace MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- Normalization preserves the uniform scaled estimates for every derivative
order, with constants independent of the open set and cube. -/
theorem normalizedCutoff_derivative_bounds (d : ℕ) :
    ∃ A : ℕ → ℝ, (∀ k, 0 < A k) ∧
      ∀ (Ω : Opens (Domain d)) (S : Set (DyadicCube d)) (_hG : CubeGeometry Ω S)
        (Q : S) (k : ℕ) (x : Domain d),
        ‖iteratedFDeriv ℝ k (normalizedCutoff S Q) x‖ ≤
          A k * Q.val.side ^ (-(k : ℤ)) := by
  classical
  obtain ⟨B, hBpos, hB⟩ := cubeBump_derivative_bounds d
  let M : ℕ → ℝ := fun k => ((30 ^ d : ℕ) : ℝ) * B k * 3 ^ k
  obtain ⟨A, hApos, hA⟩ := Analytic.quotient_derivative_bounds (30 ^ d) B M
  refine ⟨A, hApos, ?_⟩
  intro Ω S hG Q k x
  by_cases hx : x ∈ Q.val.star
  · have hxΩ : x ∈ Ω := (hG.2.2.1 Q).2 hx
    obtain ⟨t, ht, he⟩ := finsum_germ_on_open Ω
      (fun R : S => (cubeBump R.val : Domain d → ℝ)) (fun R => R.val.star)
      (fun R => (R.val.isCompact_dilate _).isClosed) hG.2.2.2.1
      (fun R => by rw [← cubeBump_tsupport]; exact subset_tsupport _) hxΩ
    let H : Domain d → ℝ := fun y => ∑ R ∈ t, cubeBump R.val y
    have heH : cutoffSum S =ᶠ[𝓝 x] H := he
    have hHx : H x = cutoffSum S x := heH.eq_of_nhds.symm
    have hHdiff : ContDiff ℝ (⊤ : ℕ∞) H :=
      ContDiff.sum fun R _ => cubeBump_contDiff R.val
    have hcard : t.card ≤ 30 ^ d := by
      have htset : (t : Set S) = {R : S | x ∈ R.val.star} := by
        ext R
        exact ht R
      have hn := (hG.2.2.2.2.1 x).2
      simpa only [← htset, Set.ncard_coe_finset] using hn
    have hside (R : S) (hR : R ∈ t) : Q.val.side ≤ 3 * R.val.side :=
      (hG.2.2.2.2.2.1 Q R ⟨x, hx, (ht R).mp hR⟩).1
    have hb := cutoffSum_bounds hG x hxΩ
    have hfinite := hA (cubeBump Q.val) H (cubeBump_contDiff Q.val) hHdiff
      x Q.val.side Q.val.side_pos k (hHx ▸ hb.1) (hHx ▸ hb.2)
      (fun i _ => by simpa only [zpow_neg, zpow_natCast, inv_pow] using hB Q.val i x)
      (fun i _ => by
        have hh := finite_cubeBump_sum_derivative_bound Subtype.val t Q.val (30 ^ d) B
          (fun j => (hBpos j).le) hB hcard hside i x
        simpa only [H, M, zpow_neg, zpow_natCast, inv_pow] using hh)
    have heq : normalizedCutoff S Q =ᶠ[𝓝 x] (fun y => cubeBump Q.val y / H y) := by
      filter_upwards [heH] with y hy
      simp only [normalizedCutoff, hy]
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hfinite
  · have hz : iteratedFDeriv ℝ k (normalizedCutoff S Q) x = 0 := by
      apply Function.notMem_support.mp
      intro hh
      exact hx (normalizedCutoff_tsupport S Q (support_iteratedFDeriv_subset k hh))
    rw [hz, norm_zero]
    exact mul_nonneg (hApos k).le (le_of_lt (zpow_pos Q.val.side_pos _))

end ExpandedFA.PartIV.HardyWhitney

open Set TopologicalSpace MeasureTheory
namespace ExpandedFA.PartIV.HardyWhitney
open ExpandedFA.Distributions

/-- The smooth Whitney partition, including all uniform derivative, integral,
overlap and nested-level estimates from `fa2:p4:hardy-whitney`. -/
theorem smooth_whitney : Specs.ExpandedFA.PartIV.HardyWhitney.smoothWhitneyType := by
  intro d hd
  apply smooth_whitney_from_normalized_weights hd
  obtain ⟨A, hApos, hA⟩ := normalizedCutoff_derivative_bounds d
  refine ⟨A, hApos, ?_⟩
  intro Ω
  refine ⟨whitneyWeight hd Ω, whitneyWeight_nonneg hd Ω,
    whitneyWeight_tsupport hd Ω, whitneyWeight_sum hd Ω, ?_, ?_⟩
  · intro Q x hx
    exact whitneyWeight_lower hd Ω Q x hx
  · intro Q k a x
    change ‖iteratedFDeriv ℝ k (normalizedCutoff _ Q) x
      (fun j => coordinateVector (a j))‖ ≤ _
    exact (coordinate_derivative_le_operator _ a x).trans
      (hA Ω.val _ (maximalCubes_geometry hd Ω) Q k x)

end ExpandedFA.PartIV.HardyWhitney

