import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions

/-! The circle, increasing lifts, and their induced orientation-preserving homeomorphisms. -/
namespace D13Unified.Ch15.CircleLift

noncomputable section

abbrev Circle : Specs.D13Unified.Ch15.CircleLift.CircleType := Specs.D13Unified.Ch15.CircleLift.Circle
abbrev quotientMap : Specs.D13Unified.Ch15.CircleLift.quotientMapType := Specs.D13Unified.Ch15.CircleLift.quotientMap
abbrev IncreasingLift : Specs.D13Unified.Ch15.CircleLift.IncreasingLiftType := Specs.D13Unified.Ch15.CircleLift.IncreasingLift
abbrev inverseLift : Specs.D13Unified.Ch15.CircleLift.inverseLiftType := Specs.D13Unified.Ch15.CircleLift.inverseLift
abbrev circleMap : Specs.D13Unified.Ch15.CircleLift.circleMapType := Specs.D13Unified.Ch15.CircleLift.circleMap
abbrev PositivelyOrdered : Specs.D13Unified.Ch15.CircleLift.PositivelyOrderedType := Specs.D13Unified.Ch15.CircleLift.PositivelyOrdered
abbrev OrientationPreserving : Specs.D13Unified.Ch15.CircleLift.OrientationPreservingType := Specs.D13Unified.Ch15.CircleLift.OrientationPreserving

theorem increasingLift_iff (h : ℝ ≃ₜ ℝ) :
    (∃ L : IncreasingLift, L.toHomeomorph = h) ↔
      Monotone h ∧ ∀ x : ℝ, h (x + 1) = h x + 1 := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.strictMono'.monotone, L.map_add_one'⟩
  · rintro ⟨hm, ht⟩
    exact ⟨⟨h, hm.strictMono_of_injective h.injective, ht⟩, rfl⟩

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  QuotientAddGroup.mk_surjective

theorem quotientMap_eq_iff (x y : ℝ) :
    quotientMap x = quotientMap y ↔ ∃ k : ℤ, x = y + (k : ℝ) := by
  change (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

/-- The library metric is precisely the infimum over integer representatives. -/
theorem circle_dist_eq_iInf (x y : ℝ) :
    dist (quotientMap x) (quotientMap y) = ⨅ k : ℤ, |x - y - (k : ℝ)| := by
  change dist (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) = _
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  apply le_antisymm
  · exact le_ciInf fun k => round_le (x - y) k
  · exact ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact abs_nonneg _⟩ (round (x - y))

theorem map_add_int (L : IncreasingLift) (x : ℝ) (k : ℤ) :
    L (x + (k : ℝ)) = L x + (k : ℝ) := by
  have hNat : ∀ (n : ℕ) (x : ℝ), L (x + (n : ℝ)) = L x + (n : ℝ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc, L.map_add_one', ih]
  cases k with
  | ofNat n => exact hNat n x
  | negSucc n =>
    have h := hNat (n + 1) (x - ((n : ℝ) + 1))
    simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel] at h
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    change L (x - ((n : ℝ) + 1)) = L x - ((n : ℝ) + 1)
    linarith

theorem lift_well_defined (L : IncreasingLift) (x y : ℝ)
    (h : quotientMap x = quotientMap y) : quotientMap (L x) = quotientMap (L y) := by
  obtain ⟨k, rfl⟩ := (quotientMap_eq_iff x y).mp h
  apply (quotientMap_eq_iff _ _).mpr
  exact ⟨k, map_add_int L y k⟩

@[simp]
theorem circleMap_quotient (L : IncreasingLift) (x : ℝ) :
    circleMap L (quotientMap x) = quotientMap (L x) := rfl

theorem circleMap_inverse (L : IncreasingLift) (a : Circle) :
    circleMap (inverseLift L) (circleMap L a) = a ∧
    circleMap L (circleMap (inverseLift L) a) = a := by
  obtain ⟨x, rfl⟩ := quotientMap_surjective a
  simp only [circleMap_quotient]
  exact ⟨congrArg quotientMap (L.toHomeomorph.symm_apply_apply x),
    congrArg quotientMap (L.toHomeomorph.apply_symm_apply x)⟩

private theorem circleMap_continuous (L : IncreasingLift) : Continuous (circleMap L) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp L.toHomeomorph.continuous

/-- An explicit continuous inverse is induced by the inverse lift. -/
private def inducedHomeomorph (L : IncreasingLift) : Circle ≃ₜ Circle where
  toFun := circleMap L
  invFun := circleMap (inverseLift L)
  left_inv := fun a => (circleMap_inverse L a).1
  right_inv := fun a => (circleMap_inverse L a).2
  continuous_toFun := circleMap_continuous L
  continuous_invFun := circleMap_continuous (inverseLift L)

theorem circleMap_isHomeomorph (L : IncreasingLift) : IsHomeomorph (circleMap L) :=
  (inducedHomeomorph L).isHomeomorph

private theorem positiveTriple_map (L : IncreasingLift) {a b c : Circle}
    (h : PositivelyOrdered a b c) :
    PositivelyOrdered (circleMap L a) (circleMap L b) (circleMap L c) := by
  obtain ⟨x, y, z, rfl, rfl, rfl, hxy, hyz, hzx⟩ := h
  refine ⟨L x, L y, L z, rfl, rfl, rfl, L.strictMono' hxy, L.strictMono' hyz, ?_⟩
  simpa only [L.map_add_one'] using L.strictMono' hzx

theorem circleMap_orientationPreserving (L : IncreasingLift) :
    OrientationPreserving (circleMap L) := by
  intro a b c
  constructor
  · exact positiveTriple_map L
  · intro h
    have h' := positiveTriple_map (inverseLift L) h
    simpa only [(circleMap_inverse L a).1, (circleMap_inverse L b).1,
      (circleMap_inverse L c).1] using h'

theorem exists_unique_inducedHomeomorph (L : IncreasingLift) :
    ∃! F : Circle ≃ₜ Circle,
      (∀ x : ℝ, F (quotientMap x) = quotientMap (L x)) ∧ OrientationPreserving F := by
  refine ⟨inducedHomeomorph L, ⟨circleMap_quotient L, circleMap_orientationPreserving L⟩, ?_⟩
  intro F hF
  apply Homeomorph.ext
  intro a
  obtain ⟨x, rfl⟩ := quotientMap_surjective a
  exact hF.1 x

theorem circleMap_iterate (L : IncreasingLift) (n : ℕ) (x : ℝ) :
    (circleMap L)^[n] (quotientMap x) = quotientMap ((L : ℝ → ℝ)^[n] x) := by
  have h : Function.Semiconj quotientMap (L : ℝ → ℝ) (circleMap L) :=
    fun x => (circleMap_quotient L x).symm
  exact (h.iterate_right n x).symm

theorem inducedHomeomorph_integerIterate (L : IncreasingLift) (F : Circle ≃ₜ Circle)
    (hF : ∀ x : ℝ, F (quotientMap x) = quotientMap (L x)) (n : ℤ) (x : ℝ) :
    DiscreteDefinitions.integerIterate F.toEquiv n (quotientMap x) =
      quotientMap (DiscreteDefinitions.integerIterate L.toHomeomorph.toEquiv n x) := by
  have h : Function.Semiconj quotientMap (L.toHomeomorph : ℝ → ℝ) (F : Circle → Circle) :=
    fun x => (hF x).symm
  have hi : Function.Semiconj quotientMap (L.toHomeomorph.symm : ℝ → ℝ)
      (F.symm : Circle → Circle) := by
    intro y
    apply F.injective
    rw [F.apply_symm_apply, hF, L.toHomeomorph.apply_symm_apply]
  cases n with
  | ofNat k => exact (h.iterate_right k x).symm
  | negSucc k => exact (hi.iterate_right (k + 1) x).symm

end
end D13Unified.Ch15.CircleLift
