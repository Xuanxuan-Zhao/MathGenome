import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.InverseContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Inverse
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Ring

/-!
K03.04.inverse, paper.tex:706–720. `Function.invFunOn f I` is an ambient
representative of the inverse on `f '' I`. Its values outside that image are
irrelevant. The proof uses continuity of the inverse and the reciprocal
identity for difference quotients, so ordinary differentiability suffices;
no strict differentiability or continuity of the derivative is assumed.
-/
noncomputable section
namespace SingleVariableAnalysis
open scoped Topology

/-- The canonical inverse has exactly the inverse identities and continuity
on the image supplied by the interval inverse theorem. -/
theorem intervalInverse_properties (f : ℝ → ℝ) (I : Set ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) :
    Set.MapsTo (Function.invFunOn f I) (f '' I) I ∧
    (∀ x ∈ I, Function.invFunOn f I (f x) = x) ∧
    (∀ y ∈ f '' I, f (Function.invFunOn f I y) = y) ∧
    RelativeContinuous (Function.invFunOn f I) (f '' I) := by
  obtain ⟨hbij, _, g, hg, hleft, hright⟩ := continuous_monotone_inverse f I hI hf hm
  have heq (y : f '' I) : Function.invFunOn f I y = (g y : ℝ) := by
    apply hbij.injOn (Function.invFunOn_mem y.property) (g y).property
    exact (Function.invFunOn_eq y.property).trans (hright y).symm
  refine ⟨fun _ hy => Function.invFunOn_mem hy,
    hbij.injOn.leftInvOn_invFunOn, fun _ hy => Function.invFunOn_eq hy, ?_⟩
  apply (relativeContinuous_subtype_iff _ _).mpr
  have hc : Continuous (fun y : f '' I => (g y : ℝ)) := continuous_subtype_val.comp hg
  exact hc.congr (fun y => (heq y).symm)

/-- The reciprocal identity transports a derivative through any continuous
inverse on the image. This version also works at included endpoints. -/
lemma inverse_incrementDerivativeWithin (f g : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hg : RelativeContinuousAt g (f '' I) (f a))
    (hga : g (f a) = a) (hmap : Set.MapsTo g (f '' I) I)
    (hfg : ∀ y ∈ f '' I, f (g y) = y)
    (hd : HasRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    HasRealIncrementDerivativeWithin g (1 / L) (f '' I) (f a) := by
  rw [withinDerivative_epsilon_iff] at hd ⊢
  intro ε hε
  obtain ⟨η, hη, hinv⟩ := Metric.continuousAt_iff.mp
    (continuousAt_inv₀ hL : ContinuousAt (fun x : ℝ => x⁻¹) L) ε hε
  obtain ⟨δ, hδ, hquot⟩ := hd η hη
  obtain ⟨r, hr, hcont⟩ := hg δ hδ
  refine ⟨r, hr, fun h hh hp hsmall => ?_⟩
  let k := g (f a + h) - a
  have hkI : a + k ∈ I := by
    have harg : a + k = g (f a + h) := by dsimp [k]; ring
    rw [harg]
    exact hmap hh
  have hk0 : k ≠ 0 := by
    intro hk
    have hga' : g (f a + h) = a := sub_eq_zero.mp hk
    have he := hfg (f a + h) hh
    rw [hga'] at he
    have : h = 0 := by linarith
    simp [this] at hp
  have hkδ : |k| < δ := by
    have he := hcont (f a + h) hh (by
      simpa only [Real.dist_eq, add_sub_cancel_left] using hsmall)
    simpa only [Real.dist_eq, hga] using he
  have hq := hquot k hkI (abs_pos.mpr hk0) hkδ
  have heq : RealIncrementQuotient g (f a) h =
      (RealIncrementQuotient f a k)⁻¹ := by
    have harg : a + k = g (f a + h) := by dsimp [k]; ring
    simp only [RealIncrementQuotient, smul_eq_mul, harg, hfg _ hh, hga,
      add_sub_cancel_left, mul_inv_rev, inv_inv]
    rfl
  rw [heq]
  simpa only [one_div, dist_eq_norm] using hinv (by
    simpa only [dist_eq_norm] using hq)

lemma rightInterval_image_strictMono (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (hJ : RealInterval (f '' I)) (hm : StrictMonoOn f I)
    (ha : RightIntervalAvailable I a) : RightIntervalAvailable (f '' I) (f a) := by
  obtain ⟨ha, r, hr, hside⟩ := ha
  have hx : a + r / 2 ∈ I := hside ⟨by linarith, by linarith⟩
  have hlt := hm ha hx (by linarith : a < a + r / 2)
  refine ⟨⟨a, ha, rfl⟩, f (a + r / 2) - f a, sub_pos.mpr hlt, ?_⟩
  intro y hy
  exact hJ ⟨a, ha, rfl⟩ ⟨a + r / 2, hx, rfl⟩ hy.1.le (by linarith [hy.2])

lemma rightInterval_image_strictAnti (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (hJ : RealInterval (f '' I)) (hm : StrictAntiOn f I)
    (ha : RightIntervalAvailable I a) : LeftIntervalAvailable (f '' I) (f a) := by
  obtain ⟨ha, r, hr, hside⟩ := ha
  have hx : a + r / 2 ∈ I := hside ⟨by linarith, by linarith⟩
  have hlt := hm ha hx (by linarith : a < a + r / 2)
  refine ⟨⟨a, ha, rfl⟩, f a - f (a + r / 2), sub_pos.mpr hlt, ?_⟩
  intro y hy
  exact hJ ⟨a + r / 2, hx, rfl⟩ ⟨a, ha, rfl⟩ (by linarith [hy.1]) hy.2.le

lemma leftInterval_image_strictMono (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (hJ : RealInterval (f '' I)) (hm : StrictMonoOn f I)
    (ha : LeftIntervalAvailable I a) : LeftIntervalAvailable (f '' I) (f a) := by
  obtain ⟨ha, r, hr, hside⟩ := ha
  have hx : a - r / 2 ∈ I := hside ⟨by linarith, by linarith⟩
  have hlt := hm hx ha (by linarith : a - r / 2 < a)
  refine ⟨⟨a, ha, rfl⟩, f a - f (a - r / 2), sub_pos.mpr hlt, ?_⟩
  intro y hy
  exact hJ ⟨a - r / 2, hx, rfl⟩ ⟨a, ha, rfl⟩ (by linarith [hy.1]) hy.2.le

lemma leftInterval_image_strictAnti (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (hJ : RealInterval (f '' I)) (hm : StrictAntiOn f I)
    (ha : LeftIntervalAvailable I a) : RightIntervalAvailable (f '' I) (f a) := by
  obtain ⟨ha, r, hr, hside⟩ := ha
  have hx : a - r / 2 ∈ I := hside ⟨by linarith, by linarith⟩
  have hlt := hm hx ha (by linarith : a - r / 2 < a)
  refine ⟨⟨a, ha, rfl⟩, f (a - r / 2) - f a, sub_pos.mpr hlt, ?_⟩
  intro y hy
  exact hJ ⟨a, ha, rfl⟩ ⟨a - r / 2, hx, rfl⟩ hy.1.le (by linarith [hy.2])

lemma interior_of_sideIntervals (I : Set ℝ) (a : ℝ)
    (hr : RightIntervalAvailable I a) (hl : LeftIntervalAvailable I a) :
    a ∈ interior I := by
  obtain ⟨ha, r, hr, hright⟩ := hr
  obtain ⟨_, l, hl, hleft⟩ := hl
  apply mem_interior_iff_mem_nhds.mpr
  refine Metric.mem_nhds_iff.mpr ⟨min r l, lt_min hr hl, ?_⟩
  intro x hx
  have hb := abs_lt.mp (show |x - a| < min r l from hx)
  rcases lt_trichotomy x a with hxa | rfl | hax
  · exact hleft ⟨by linarith [min_le_right r l], hxa⟩
  · exact ha
  · exact hright ⟨hax, by linarith [min_le_left r l]⟩

/-- A continuous strictly monotone interval map sends interior points to
interior points of its image, in either monotonicity direction. -/
theorem monotone_image_interior (f : ℝ → ℝ) (I : Set ℝ) (a : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) (ha : a ∈ interior I) :
    f a ∈ interior (f '' I) := by
  have hJ := continuous_real_interval_image f I hI hf
  obtain ⟨hr, hl⟩ := interior_sideIntervals I a ha
  rcases hm with hm | hm
  · exact interior_of_sideIntervals _ _
      (rightInterval_image_strictMono f I a hJ hm hr)
      (leftInterval_image_strictMono f I a hJ hm hl)
  · exact interior_of_sideIntervals _ _
      (leftInterval_image_strictAnti f I a hJ hm hl)
      (rightInterval_image_strictAnti f I a hJ hm hr)

/-- The ordinary inverse derivative at an interior point. -/
theorem inverse_derivative (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) (ha : a ∈ interior I)
    (hd : HasRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    f a ∈ interior (f '' I) ∧
    HasRealIncrementDerivative (Function.invFunOn f I) (1 / L) (f a) := by
  have hb := monotone_image_interior f I a hI hf hm ha
  obtain ⟨hmap, hleft, hright, hg⟩ := intervalInverse_properties f I hI hf hm
  have hdg := inverse_incrementDerivativeWithin f (Function.invFunOn f I) I a L
    (hg _ ⟨a, interior_subset ha, rfl⟩) (hleft a (interior_subset ha)) hmap hright hd hL
  exact ⟨hb, (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
    ((withinDerivative_interior_iff _ _ _ _ hb).mp hdg)⟩

/-- A common within-domain form, before choosing an ordinary or endpoint convention. -/
lemma intervalInverse_derivativeWithin (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I)
    (hm : StrictMonoOn f I ∨ StrictAntiOn f I) (ha : a ∈ I)
    (hd : HasRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    HasRealIncrementDerivativeWithin (Function.invFunOn f I) (1 / L) (f '' I) (f a) := by
  obtain ⟨hmap, hleft, hright, hg⟩ := intervalInverse_properties f I hI hf hm
  exact inverse_incrementDerivativeWithin f (Function.invFunOn f I) I a L
    (hg _ ⟨a, ha, rfl⟩) (hleft a ha) hmap hright hd hL

/-- At a left endpoint a strictly increasing map
has an inverse derivative on the right side of its image. -/
theorem inverse_rightDerivative_of_strictMono (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I) (hm : StrictMonoOn f I)
    (hbound : I ⊆ Set.Ici a)
    (hd : HasRightRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    f '' I ⊆ Set.Ici (f a) ∧
    HasRightRealIncrementDerivativeWithin (Function.invFunOn f I) (1 / L) (f '' I) (f a) := by
  have hb : f '' I ⊆ Set.Ici (f a) := by
    rintro y ⟨x, hx, rfl⟩
    exact hm.monotoneOn hd.1.1 hx (hbound hx)
  have hside := rightInterval_image_strictMono f I a
    (continuous_real_interval_image f I hI hf) hm hd.1
  have hdf := (leftEndpointDerivative_iff f L I a hd.1 hbound).mpr hd
  have hdg := intervalInverse_derivativeWithin f I a L hI hf (Or.inl hm)
    hd.1.1 hdf hL
  exact ⟨hb, (leftEndpointDerivative_iff _ _ _ _ hside hb).mp hdg⟩

/-- At a left endpoint a strictly decreasing map
has an inverse derivative on the left side of its image. -/
theorem inverse_rightDerivative_of_strictAnti (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I) (hm : StrictAntiOn f I)
    (hbound : I ⊆ Set.Ici a)
    (hd : HasRightRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    f '' I ⊆ Set.Iic (f a) ∧
    HasLeftRealIncrementDerivativeWithin (Function.invFunOn f I) (1 / L) (f '' I) (f a) := by
  have hb : f '' I ⊆ Set.Iic (f a) := by
    rintro y ⟨x, hx, rfl⟩
    exact hm.antitoneOn hd.1.1 hx (hbound hx)
  have hside := rightInterval_image_strictAnti f I a
    (continuous_real_interval_image f I hI hf) hm hd.1
  have hdf := (leftEndpointDerivative_iff f L I a hd.1 hbound).mpr hd
  have hdg := intervalInverse_derivativeWithin f I a L hI hf (Or.inr hm)
    hd.1.1 hdf hL
  exact ⟨hb, (rightEndpointDerivative_iff _ _ _ _ hside hb).mp hdg⟩

/-- At a right endpoint a strictly increasing map
has an inverse derivative on the left side of its image. -/
theorem inverse_leftDerivative_of_strictMono (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I) (hm : StrictMonoOn f I)
    (hbound : I ⊆ Set.Iic a)
    (hd : HasLeftRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    f '' I ⊆ Set.Iic (f a) ∧
    HasLeftRealIncrementDerivativeWithin (Function.invFunOn f I) (1 / L) (f '' I) (f a) := by
  have hb : f '' I ⊆ Set.Iic (f a) := by
    rintro y ⟨x, hx, rfl⟩
    exact hm.monotoneOn hx hd.1.1 (hbound hx)
  have hside := leftInterval_image_strictMono f I a
    (continuous_real_interval_image f I hI hf) hm hd.1
  have hdf := (rightEndpointDerivative_iff f L I a hd.1 hbound).mpr hd
  have hdg := intervalInverse_derivativeWithin f I a L hI hf (Or.inl hm)
    hd.1.1 hdf hL
  exact ⟨hb, (rightEndpointDerivative_iff _ _ _ _ hside hb).mp hdg⟩

/-- At a right endpoint a strictly decreasing map
has an inverse derivative on the right side of its image. -/
theorem inverse_leftDerivative_of_strictAnti (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hI : RealInterval I) (hf : RelativeContinuous f I) (hm : StrictAntiOn f I)
    (hbound : I ⊆ Set.Iic a)
    (hd : HasLeftRealIncrementDerivativeWithin f L I a) (hL : L ≠ 0) :
    f '' I ⊆ Set.Ici (f a) ∧
    HasRightRealIncrementDerivativeWithin (Function.invFunOn f I) (1 / L) (f '' I) (f a) := by
  have hb : f '' I ⊆ Set.Ici (f a) := by
    rintro y ⟨x, hx, rfl⟩
    exact hm.antitoneOn hx hd.1.1 (hbound hx)
  have hside := leftInterval_image_strictAnti f I a
    (continuous_real_interval_image f I hI hf) hm hd.1
  have hdf := (rightEndpointDerivative_iff f L I a hd.1 hbound).mpr hd
  have hdg := intervalInverse_derivativeWithin f I a L hI hf (Or.inr hm)
    hd.1.1 hdf hL
  exact ⟨hb, (leftEndpointDerivative_iff _ _ _ _ hside hb).mp hdg⟩

end SingleVariableAnalysis
