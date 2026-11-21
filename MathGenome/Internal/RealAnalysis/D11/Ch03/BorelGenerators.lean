import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.BorelGenerators

open Set MeasurableSpace

namespace D11.Ch03.BorelGenerators

abbrev euclideanBorel (d : ℕ) : MeasurableSpace (Space d) := borel (Space d)

theorem borel_open : Specs.D11.Ch03.BorelGenerators.borel_open := by
  intro d _
  rfl

theorem real_left_closed_intervals : Specs.D11.Ch03.BorelGenerators.real_left_closed_intervals :=
  borel_eq_generateFrom_Ico ℝ

theorem real_right_closed_intervals : Specs.D11.Ch03.BorelGenerators.real_right_closed_intervals :=
  borel_eq_generateFrom_Ioc ℝ

theorem real_closed_intervals : Specs.D11.Ch03.BorelGenerators.real_closed_intervals :=
  borel_eq_generateFrom_Icc ℝ

theorem real_left_open_rays : Specs.D11.Ch03.BorelGenerators.real_left_open_rays :=
  borel_eq_generateFrom_Iio ℝ

theorem real_right_open_rays : Specs.D11.Ch03.BorelGenerators.real_right_open_rays :=
  borel_eq_generateFrom_Ioi ℝ

theorem real_left_closed_rays : Specs.D11.Ch03.BorelGenerators.real_left_closed_rays :=
  borel_eq_generateFrom_Iic ℝ

theorem real_right_closed_rays : Specs.D11.Ch03.BorelGenerators.real_right_closed_rays :=
  borel_eq_generateFrom_Ici ℝ

theorem real_open_intervals : Specs.D11.Ch03.BorelGenerators.real_open_intervals := by
  apply le_antisymm
  · rw [Real.borel_eq_generateFrom_Ioo_rat]
    apply generateFrom_mono
    intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    rcases hs with ⟨a, b, hab, rfl⟩
    exact ⟨(a : ℝ), (b : ℝ), Rat.cast_lt.mpr hab, rfl⟩
  · apply generateFrom_le
    rintro s ⟨a, b, _, rfl⟩
    exact isOpen_Ioo.measurableSet

/-- The coordinate map is a homeomorphism, even though it changes the norm
from Euclidean to the finite product's sup norm. Thus its pullback of the
product Borel structure is exactly the Euclidean Borel structure. -/
theorem euclidean_borel_comap (d : ℕ) :
    borel (Space d) = (borel (Fin d → ℝ)).comap (EuclideanSpace.equiv (Fin d) ℝ) := by
  rw [← borel_comap]
  rfl

/-- Pulling coordinate rectangles back along the coordinate homeomorphism
produces exactly the Euclidean boxes specified above. -/
theorem boxes_pullback (d : ℕ) (C : Set (Set ℝ)) :
    boxes d C = Set.preimage (EuclideanSpace.equiv (Fin d) ℝ) ''
      (Set.pi univ '' Set.pi univ (fun _ : Fin d => C)) := by
  ext s
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨Set.pi univ U, ⟨U, ?_, rfl⟩, ?_⟩
    · simpa only [mem_univ_pi] using hU
    · ext x
      simp
  · rintro ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    refine ⟨U, ?_, ?_⟩
    · simpa only [mem_univ_pi] using hU
    · ext x
      simp

/-- A finite product of a countably spanning generating family generates the
Euclidean Borel structure. -/
theorem borel_from_boxes (d : ℕ) (C : Set (Set ℝ))
    (hgen : generateFrom C = borel ℝ) (hspan : IsCountablySpanning C) :
    borel (Space d) = generateFrom (boxes d C) := by
  rw [euclidean_borel_comap, boxes_pullback, ← comap_generateFrom]
  congr 1
  exact BorelSpace.measurable_eq.symm.trans
    (generateFrom_eq_pi (fun _ : Fin d => hgen) (fun _ => hspan)).symm

-- The intervals (-n-1,n+1) cover ℝ. The same enclosing intervals with either
-- half-open convention also cover ℝ. These witnesses ensure that only bounded
-- boxes are used in the preceding finite-product generation theorem.
theorem rational_intervals_spanning : IsCountablySpanning rationalOpenIntervals := by
  refine ⟨fun n => Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_⟩
  · intro n
    simp only [rationalOpenIntervals, mem_iUnion, mem_singleton_iff]
    refine ⟨-((n : ℚ) + 1), (n : ℚ) + 1, by linarith [Nat.cast_nonneg (α := ℚ) n], ?_⟩
    push_cast
    rfl
  · apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩ <;> linarith [le_abs_self x, neg_abs_le x]

theorem left_closed_intervals_spanning : IsCountablySpanning leftClosedIntervals := by
  refine ⟨fun n => Ico (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_⟩
  · intro n
    exact ⟨_, _, by linarith [Nat.cast_nonneg (α := ℝ) n], rfl⟩
  · apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩ <;> linarith [le_abs_self x, neg_abs_le x]

theorem right_closed_intervals_spanning : IsCountablySpanning rightClosedIntervals := by
  refine ⟨fun n => Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_⟩
  · intro n
    exact ⟨_, _, by linarith [Nat.cast_nonneg (α := ℝ) n], rfl⟩
  · apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩ <;> linarith [le_abs_self x, neg_abs_le x]

theorem rational_open_boxes : Specs.D11.Ch03.BorelGenerators.rational_open_boxes := by
  intro d _
  exact borel_from_boxes d rationalOpenIntervals Real.borel_eq_generateFrom_Ioo_rat.symm
    rational_intervals_spanning

theorem left_closed_boxes : Specs.D11.Ch03.BorelGenerators.left_closed_boxes := by
  intro d _
  exact borel_from_boxes d leftClosedIntervals real_left_closed_intervals.symm
    left_closed_intervals_spanning

theorem right_closed_boxes : Specs.D11.Ch03.BorelGenerators.right_closed_boxes := by
  intro d _
  exact borel_from_boxes d rightClosedIntervals real_right_closed_intervals.symm
    right_closed_intervals_spanning

/-- Rational closed coordinate rays generate: they make every coordinate
measurable, and hence make the full coordinate map measurable. -/
theorem rational_coordinate_halfspaces :
    Specs.D11.Ch03.BorelGenerators.rational_coordinate_halfspaces := by
  intro d _
  let m := generateFrom (rationalCoordinateHalfspaces d)
  apply le_antisymm
  · rw [euclidean_borel_comap]
    have hcoord (j : Fin d) :
        @Measurable (Space d) ℝ m (borel ℝ) (fun x => x j) := by
      rw [Real.borel_eq_generateFrom_Iic_rat]
      apply @measurable_generateFrom _ _ m
      intro s hs
      simp only [mem_iUnion, mem_singleton_iff] at hs
      rcases hs with ⟨q, rfl⟩
      exact measurableSet_generateFrom ⟨j, q, rfl⟩
    have hmap : @Measurable (Space d) (Fin d → ℝ) m
        MeasurableSpace.pi (EuclideanSpace.equiv (Fin d) ℝ) :=
      measurable_pi_iff.mpr hcoord
    rw [← BorelSpace.measurable_eq (α := Fin d → ℝ)]
    exact hmap.comap_le
  · apply generateFrom_le
    rintro s ⟨j, q, rfl⟩
    exact isClosed_Iic.measurableSet.preimage
      (EuclideanSpace.proj j).continuous.borel_measurable

end D11.Ch03.BorelGenerators
