import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.OneSided

/-!
# One-sided derivatives with real increments

K03.04.one_sided, paper.tex:649–660. Side availability includes the value at a
and a whole interval of domain on that side. Derivative values belong to the
normed real target (in particular ℝ or ℂ), so are finite. No complex increments
or infinite derivative values are used. Values outside I are immaterial.

The two-sided equivalence is obtained from the upstream one-sided limit
criterion for the same real-increment quotient. At included endpoints we state
only the available one-sided/within convention.
-/
namespace SingleVariableAnalysis
open scoped Topology
universe u

def RightIntervalAvailable (I : Set ℝ) (a : ℝ) : Prop :=
  a ∈ I ∧ ∃ r : ℝ, 0 < r ∧ Set.Ioo a (a + r) ⊆ I

def LeftIntervalAvailable (I : Set ℝ) (a : ℝ) : Prop :=
  a ∈ I ∧ ∃ r : ℝ, 0 < r ∧ Set.Ioo (a - r) a ⊆ I

def HasRightRealIncrementDerivativeWithin {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) : Prop :=
  RightIntervalAvailable I a ∧
    RightRelativeLimit (RealIncrementQuotient f a) {h : ℝ | a + h ∈ I} 0 L

def HasLeftRealIncrementDerivativeWithin {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) : Prop :=
  LeftIntervalAvailable I a ∧
    LeftRelativeLimit (RealIncrementQuotient f a) {h : ℝ | a + h ∈ I} 0 L

lemma RightIntervalAvailable.increment_accumulation {I : Set ℝ} {a : ℝ}
    (ha : RightIntervalAvailable I a) : RightAccumulation {h : ℝ | a + h ∈ I} 0 := by
  obtain ⟨_, r, hr, hI⟩ := ha
  rw [rightAccumulation_iff]
  intro δ hδ
  have hm : 0 < min r δ := lt_min hr hδ
  have hmr := min_le_left r δ
  have hmd := min_le_right r δ
  refine ⟨min r δ / 2, hI ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma LeftIntervalAvailable.increment_accumulation {I : Set ℝ} {a : ℝ}
    (ha : LeftIntervalAvailable I a) : LeftAccumulation {h : ℝ | a + h ∈ I} 0 := by
  obtain ⟨_, r, hr, hI⟩ := ha
  rw [leftAccumulation_iff]
  intro δ hδ
  have hm : 0 < min r δ := lt_min hr hδ
  have hmr := min_le_left r δ
  have hmd := min_le_right r δ
  refine ⟨-(min r δ / 2), hI ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem interior_sideIntervals (I : Set ℝ) (a : ℝ) (ha : a ∈ interior I) :
    RightIntervalAvailable I a ∧ LeftIntervalAvailable I a := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  refine ⟨⟨interior_subset ha, r, hr, ?_⟩,
    ⟨interior_subset ha, r, hr, ?_⟩⟩
  · intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
    linarith [hx.2]
  · intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hx.2)]
    linarith [hx.1]

theorem rightDerivative_epsilon_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) :
    HasRightRealIncrementDerivativeWithin f L I a ↔ RightIntervalAvailable I a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → 0 < h → h < δ →
          ‖RealIncrementQuotient f a h - L‖ < ε := by
  rw [HasRightRealIncrementDerivativeWithin, rightRelativeLimit_iff]
  constructor
  · rintro ⟨ha, _, h⟩
    exact ⟨ha, by simpa only [zero_add, dist_eq_norm, Set.mem_ofPred_eq] using h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, ha.increment_accumulation,
      by simpa only [zero_add, dist_eq_norm, Set.mem_ofPred_eq] using h⟩

theorem leftDerivative_epsilon_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) :
    HasLeftRealIncrementDerivativeWithin f L I a ↔ LeftIntervalAvailable I a ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → -δ < h → h < 0 →
          ‖RealIncrementQuotient f a h - L‖ < ε := by
  rw [HasLeftRealIncrementDerivativeWithin, leftRelativeLimit_iff]
  constructor
  · rintro ⟨ha, _, h⟩
    exact ⟨ha, by simpa only [zero_sub, dist_eq_norm, Set.mem_ofPred_eq] using h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, ha.increment_accumulation,
      by simpa only [zero_sub, dist_eq_norm, Set.mem_ofPred_eq] using h⟩

theorem withinDerivative_iff_one_sided {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (hr : RightIntervalAvailable I a) (hl : LeftIntervalAvailable I a) :
    HasRealIncrementDerivativeWithin f L I a ↔
      HasRightRealIncrementDerivativeWithin f L I a ∧
      HasLeftRealIncrementDerivativeWithin f L I a := by
  simpa only [HasRealIncrementDerivativeWithin, HasRightRealIncrementDerivativeWithin,
    HasLeftRealIncrementDerivativeWithin, hr, hl, true_and] using
    relativePuncturedLimit_iff_one_sided (RealIncrementQuotient f a)
      {h : ℝ | a + h ∈ I} 0 L hr.increment_accumulation hl.increment_accumulation

theorem interiorDerivative_iff_one_sided {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) :
    HasDerivAt f L a ↔ HasRightRealIncrementDerivativeWithin f L I a ∧
      HasLeftRealIncrementDerivativeWithin f L I a := by
  rw [← withinDerivative_interior_iff f L I a ha]
  exact withinDerivative_iff_one_sided f L I a
    (interior_sideIntervals I a ha).1 (interior_sideIntervals I a ha).2

theorem finiteDerivative_exists_iff_one_sided_agree {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (I : Set ℝ) (a : ℝ) (ha : a ∈ interior I) :
    (∃ L : F, HasRealIncrementDerivativeWithin f L I a) ↔
      ∃ L R : F, HasLeftRealIncrementDerivativeWithin f L I a ∧
        HasRightRealIncrementDerivativeWithin f R I a ∧ L = R := by
  obtain ⟨hr, hl⟩ := interior_sideIntervals I a ha
  constructor
  · rintro ⟨L, hd⟩
    obtain ⟨hR, hL⟩ := (withinDerivative_iff_one_sided f L I a hr hl).mp hd
    exact ⟨L, L, hL, hR, rfl⟩
  · rintro ⟨L, R, hL, hR, heq⟩
    subst R
    exact ⟨L, (withinDerivative_iff_one_sided f L I a hr hl).mpr ⟨hR, hL⟩⟩

theorem differentiableAt_iff_one_sided_agree {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (I : Set ℝ) (a : ℝ) (ha : a ∈ interior I) :
    DifferentiableAt ℝ f a ↔
      ∃ L R : F, HasLeftRealIncrementDerivativeWithin f L I a ∧
        HasRightRealIncrementDerivativeWithin f R I a ∧ L = R := by
  rw [← finiteDerivative_exists_iff_one_sided_agree f I a ha]
  constructor
  · intro hd
    exact ⟨deriv f a, (withinDerivative_interior_iff f _ I a ha).mpr hd.hasDerivAt⟩
  · rintro ⟨L, hd⟩
    exact ((withinDerivative_interior_iff f L I a ha).mp hd).differentiableAt

theorem rightDerivative_unique {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L M : F) (I : Set ℝ) (a : ℝ)
    (hL : HasRightRealIncrementDerivativeWithin f L I a)
    (hM : HasRightRealIncrementDerivativeWithin f M I a) : L = M := by
  have hacc := (rightAccumulation_domain_iff _ _).mp hL.1.increment_accumulation
  exact relativePuncturedLimit_unique _ _ _ _ _ hacc
    ((rightRelativeLimit_relative_iff _ _ _ _).mp hL.2).2
    ((rightRelativeLimit_relative_iff _ _ _ _).mp hM.2).2

theorem leftDerivative_unique {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L M : F) (I : Set ℝ) (a : ℝ)
    (hL : HasLeftRealIncrementDerivativeWithin f L I a)
    (hM : HasLeftRealIncrementDerivativeWithin f M I a) : L = M := by
  have hacc := (leftAccumulation_domain_iff _ _).mp hL.1.increment_accumulation
  exact relativePuncturedLimit_unique _ _ _ _ _ hacc
    ((leftRelativeLimit_relative_iff _ _ _ _).mp hL.2).2
    ((leftRelativeLimit_relative_iff _ _ _ _).mp hM.2).2

theorem rightDerivative_congr {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (hfg : Set.EqOn f g I) :
    HasRightRealIncrementDerivativeWithin f L I a ↔
      HasRightRealIncrementDerivativeWithin g L I a := by
  rw [rightDerivative_epsilon_iff, rightDerivative_epsilon_iff]
  apply and_congr_right
  intro ha
  have heq (h : ℝ) (hh : a + h ∈ I) :
      RealIncrementQuotient f a h = RealIncrementQuotient g a h := by
    simp only [RealIncrementQuotient, hfg hh, hfg ha.1]
  constructor <;> intro hd ε hε <;> obtain ⟨δ, hδ, hb⟩ := hd ε hε
  · exact ⟨δ, hδ, fun h hh hp hd => by rw [← heq h hh]; exact hb h hh hp hd⟩
  · exact ⟨δ, hδ, fun h hh hp hd => by rw [heq h hh]; exact hb h hh hp hd⟩

theorem leftDerivative_congr {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (hfg : Set.EqOn f g I) :
    HasLeftRealIncrementDerivativeWithin f L I a ↔
      HasLeftRealIncrementDerivativeWithin g L I a := by
  rw [leftDerivative_epsilon_iff, leftDerivative_epsilon_iff]
  apply and_congr_right
  intro ha
  have heq (h : ℝ) (hh : a + h ∈ I) :
      RealIncrementQuotient f a h = RealIncrementQuotient g a h := by
    simp only [RealIncrementQuotient, hfg hh, hfg ha.1]
  constructor <;> intro hd ε hε <;> obtain ⟨δ, hδ, hb⟩ := hd ε hε
  · exact ⟨δ, hδ, fun h hh hn hp => by rw [← heq h hh]; exact hb h hh hn hp⟩
  · exact ⟨δ, hδ, fun h hh hn hp => by rw [heq h hh]; exact hb h hh hn hp⟩

theorem leftEndpointDerivative_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : RightIntervalAvailable I a) (hI : I ⊆ Set.Ici a) :
    HasRealIncrementDerivativeWithin f L I a ↔
      HasRightRealIncrementDerivativeWithin f L I a := by
  rw [withinDerivative_epsilon_iff, rightDerivative_epsilon_iff]
  constructor
  · intro hd
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    refine ⟨δ, hδ, fun h hh hp hd => hb h hh ?_ ?_⟩
    · simpa only [abs_of_pos hp] using hp
    · simpa only [abs_of_pos hp] using hd
  · rintro ⟨_, hd⟩ ε hε
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    refine ⟨δ, hδ, fun h hh hp hd => ?_⟩
    have hnonneg : 0 ≤ h := by have := hI hh; change a ≤ a + h at this; linarith
    have hpos : 0 < h := by rwa [abs_of_nonneg hnonneg] at hp
    exact hb h hh hpos (by simpa only [abs_of_pos hpos] using hd)

theorem rightEndpointDerivative_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : LeftIntervalAvailable I a) (hI : I ⊆ Set.Iic a) :
    HasRealIncrementDerivativeWithin f L I a ↔
      HasLeftRealIncrementDerivativeWithin f L I a := by
  rw [withinDerivative_epsilon_iff, leftDerivative_epsilon_iff]
  constructor
  · intro hd
    refine ⟨ha, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    refine ⟨δ, hδ, fun h hh hn hp => hb h hh ?_ ?_⟩
    · rw [abs_of_neg hp]; linarith
    · rw [abs_of_neg hp]; linarith
  · rintro ⟨_, hd⟩ ε hε
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    refine ⟨δ, hδ, fun h hh hp hd => ?_⟩
    have hnonpos : h ≤ 0 := by have := hI hh; change a + h ≤ a at this; linarith
    have hneg : h < 0 := by rw [abs_of_nonpos hnonpos] at hp; linarith
    apply hb h hh _ hneg
    rw [abs_of_neg hneg] at hd
    linarith

theorem closedInterval_leftEndpoint_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a b : ℝ) (hab : a < b) :
    HasRealIncrementDerivativeWithin f L (Set.Icc a b) a ↔
      HasRightRealIncrementDerivativeWithin f L (Set.Icc a b) a := by
  apply leftEndpointDerivative_iff f L (Set.Icc a b) a
  · refine ⟨⟨le_rfl, hab.le⟩, b - a, sub_pos.mpr hab, ?_⟩
    intro x hx
    exact ⟨hx.1.le, by linarith [hx.2]⟩
  · exact fun x hx => hx.1

theorem closedInterval_rightEndpoint_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a b : ℝ) (hab : a < b) :
    HasRealIncrementDerivativeWithin f L (Set.Icc a b) b ↔
      HasLeftRealIncrementDerivativeWithin f L (Set.Icc a b) b := by
  apply rightEndpointDerivative_iff f L (Set.Icc a b) b
  · refine ⟨⟨hab.le, le_rfl⟩, b - a, sub_pos.mpr hab, ?_⟩
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  · exact fun x hx => hx.2

theorem closedInterval_unavailable_sides {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a b : ℝ) :
    ¬ HasLeftRealIncrementDerivativeWithin f L (Set.Icc a b) a ∧
    ¬ HasRightRealIncrementDerivativeWithin f L (Set.Icc a b) b := by
  constructor
  · rintro ⟨⟨_, r, hr, hI⟩, _⟩
    have hx : a - r / 2 ∈ Set.Ioo (a - r) a := ⟨by linarith, by linarith⟩
    have := (hI hx).1
    linarith
  · rintro ⟨⟨_, r, hr, hI⟩, _⟩
    have hx : b + r / 2 ∈ Set.Ioo b (b + r) := ⟨by linarith, by linarith⟩
    have := (hI hx).2
    linarith

end SingleVariableAnalysis
