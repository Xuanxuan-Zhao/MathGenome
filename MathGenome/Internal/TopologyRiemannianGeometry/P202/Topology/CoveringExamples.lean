import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringExamples
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.DeckGroup
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace P202.Topology.CoveringExamples
open P202Specs.Topology P202Specs.Topology.BasicFundamentalGroups
open P202Specs.Topology.CoveringExamples
open scoped unitInterval
noncomputable section

/-- Passing from a circle root to its canonical unit changes neither its value
nor its multiplication. -/
def circleRootsEquiv (m : ℕ) : CircleRoots m ≃* rootsOfUnity m Circle where
  toFun r := ⟨toUnits r.val, by
    apply (mem_rootsOfUnity' m _).mpr
    exact r.property⟩
  invFun r := ⟨r.val.val, (mem_rootsOfUnity' m r.val).mp r.property⟩
  left_inv _ := rfl
  right_inv r := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Units.ext; rfl

/-- The usual character of Z/mZ lists all the m-th roots of unity. -/
def residueRootsEquiv (m : ℕ) [NeZero m] : Multiplicative (ZMod m) ≃* CircleRoots m := by
  let f := (ZMod.rootsOfUnityAddChar m).toMonoidHom
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Multiplicative.toAdd.injective ((bijective_rootsOfUnityAddChar m).injective h)
    · intro r
      obtain ⟨a, ha⟩ := (bijective_rootsOfUnityAddChar m).surjective r
      exact ⟨Multiplicative.ofAdd a, ha⟩
  exact (MulEquiv.ofBijective f hf).trans (circleRootsEquiv m).symm

theorem circleRoots_card (m : ℕ) [NeZero m] : Nat.card (CircleRoots m) = m := by
  rw [← Nat.card_congr (residueRootsEquiv m).toEquiv]
  exact Nat.card_zmod m

theorem circlePower_covering (m : ℕ) (hm : 1 ≤ m) : Covering (circlePower m) := by
  letI : NeZero m := ⟨by omega⟩
  exact (coveringBridge Circle Circle (circlePower m)).mpr
    ⟨(Circle.isQuotientCoveringMap_npow m).isCoveringMap,
      (Circle.isQuotientCoveringMap_npow m).surjective⟩

theorem circleCovering : P202Specs.Topology.CoveringExamples.Expected.circleCovering := by
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  refine ⟨circlePower_covering m hm, fun z => ?_⟩
  obtain ⟨x, hx⟩ := (Circle.isQuotientCoveringMap_npow m).surjective z
  exact (Nat.card_congr ((Circle.isQuotientCoveringMap_npow m).fiberEquivGroup
    ⟨x, hx⟩)).trans (circleRoots_card m)

/-- Rotation by an m-th root is a deck transformation of the actual power map. -/
def rootDeck (m : ℕ) (r : CircleRoots m) : DeckGroup (circlePower m) :=
  ⟨Homeomorph.mulLeft r.val, by
    funext z
    change (r.val * z) ^ m = z ^ m
    rw [mul_pow, show r.val ^ m = 1 from r.property, one_mul]⟩

@[simp] theorem rootDeck_apply (m : ℕ) (r : CircleRoots m) (z : Circle) :
    (rootDeck m r).val z = r.val * z := rfl

/-- Uniqueness of lifts says that a deck transformation is the rotation
specified by its value at 1. -/
theorem exists_rootDeck (m : ℕ) (hm : 1 ≤ m) (F : DeckGroup (circlePower m)) :
    ∃ r : CircleRoots m, rootDeck m r = F := by
  have hroot : (F.val 1) ^ m = 1 := by
    simpa [circlePower] using congrFun F.property 1
  let r : CircleRoots m := ⟨F.val 1, hroot⟩
  refine ⟨r, DeckGroup.determined Circle Circle (circlePower m)
    (circlePower_covering m hm) 1 ?_⟩
  exact mul_one _

theorem circleDeckTransformations : Expected.circleDeckTransformations := by
  intro m hm
  constructor
  · intro F
    obtain ⟨r, rfl⟩ := exists_rootDeck m hm F
    exact ⟨r, fun _ => rfl⟩
  · exact fun r => ⟨rootDeck m r, fun _ => rfl⟩

def rootsDeckEquiv (m : ℕ) (hm : 1 ≤ m) : CircleRoots m ≃* DeckGroup (circlePower m) := by
  let f : CircleRoots m →* DeckGroup (circlePower m) :=
    { toFun := rootDeck m
      map_one' := by apply Subtype.ext; apply Homeomorph.ext; intro z; exact one_mul z
      map_mul' := by
        intro r s
        apply Subtype.ext; apply Homeomorph.ext; intro z
        exact mul_assoc _ _ _ }
  exact MulEquiv.ofBijective f
    ⟨fun r s h => Subtype.ext (by
        have hh := congrArg (fun F : DeckGroup (circlePower m) => F.val 1) h
        simpa [f] using hh), exists_rootDeck m hm⟩

theorem circleDeckGroup : Expected.circleDeckGroup := by
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  exact ⟨(rootsDeckEquiv m hm).symm.trans (residueRootsEquiv m).symm⟩

/-- The order-two group acts by the antipodal involution. -/
instance antipodalAction (n : ℕ) : MulAction (Multiplicative (ZMod 2)) (Sphere n) where
  smul g x := if g = 1 then x else -x
  one_smul _ := if_pos rfl
  mul_smul g h x := by
    change (if g * h = 1 then x else -x) =
      if g = 1 then (if h = 1 then x else -x) else -(if h = 1 then x else -x)
    have cases_two (a : Multiplicative (ZMod 2)) :
        a = 1 ∨ a = Multiplicative.ofAdd 1 := by
      have : ∀ a : Multiplicative (ZMod 2),
          a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
      exact this a
    rcases cases_two g with rfl | rfl <;>
      rcases cases_two h with rfl | rfl <;>
        simp [show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 from by decide,
          show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
            from by decide]


theorem twoGroup_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  have : ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide
  exact this g

@[simp] theorem antipodal_smul (n : ℕ) (g : Multiplicative (ZMod 2)) (x : Sphere n) :
    g • x = if g = 1 then x else -x := rfl

instance antipodal_continuous (n : ℕ) :
    ContinuousConstSMul (Multiplicative (ZMod 2)) (Sphere n) where
  continuous_const_smul g := by
    change Continuous (fun x : Sphere n => if g = 1 then x else -x)
    by_cases h : g = 1
    · simp only [h, ↓reduceIte]; exact continuous_id
    · simp only [h, ↓reduceIte]; exact continuous_neg

instance antipodal_free (n : ℕ) : IsCancelSMul (Multiplicative (ZMod 2)) (Sphere n) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  by_cases hg : g = 1
  · exact hg
  · exact False.elim (sphere_neg_ne_self x (by simpa only [antipodal_smul, if_neg hg] using hx))

theorem antipodal_orbit (n : ℕ) (x y : Sphere n) :
    x ∈ MulAction.orbit (Multiplicative (ZMod 2)) y ↔ x = y ∨ x = -y := by
  constructor
  · rintro ⟨g, hg⟩
    rcases twoGroup_cases g with rfl | rfl
    · exact Or.inl (by simpa only [one_smul] using hg.symm)
    · exact Or.inr (by
        simpa [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
          using hg.symm)
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨Multiplicative.ofAdd 1, by
        simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]⟩

/-- The quotient topology and the actual antipodal equivalence relation give
precisely the orbit covering of the free finite action. -/
theorem antipodal_quotientCovering (n : ℕ) :
    IsQuotientCoveringMap (antipodalProjection n) (Multiplicative (ZMod 2)) := by
  apply Topology.IsQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (G := Multiplicative (ZMod 2))
    (show Topology.IsQuotientMap (antipodalProjection n) from isQuotientMap_quotient_mk')
  intro x y
  change Quotient.mk (antipodalSetoid n) x = Quotient.mk (antipodalSetoid n) y ↔ _
  rw [Quotient.eq, antipodal_orbit]
  rfl

theorem projectiveCovering : Expected.projectiveCovering := by
  intro n hn
  have hp := antipodal_quotientCovering n
  refine ⟨(coveringBridge _ _ (antipodalProjection n)).mpr ⟨hp.isCoveringMap, hp.surjective⟩,
    (spheresSimplyConnected n hn).2, fun b => ?_⟩
  obtain ⟨x, hx⟩ := hp.surjective b
  exact (Nat.card_congr (hp.fiberEquivGroup ⟨x, hx⟩)).trans (Nat.card_zmod 2)

theorem projectiveSubgroup : Expected.projectiveSubgroup := by
  intro n hn x
  have := (spheresSimplyConnected n hn).2
  apply MonoidHom.range_eq_bot_iff.mpr
  ext a
  have ha : a = 1 := Subsingleton.elim _ _
  simp [ha]

theorem projectiveFundamentalGroup : Expected.projectiveFundamentalGroup := by
  intro n hn b
  letI := (spheresSimplyConnected n hn).2
  have hp := antipodal_quotientCovering n
  obtain ⟨x, hx⟩ := hp.surjective b
  exact ⟨(oppositeEquiv (hp.fundamentalGroupEquiv ⟨x, hx⟩)).trans
    (MulEquiv.opOp (Multiplicative (ZMod 2))).symm⟩

/-- Scaling the real exponential parameter is the circle power map. -/
theorem circleCover_mul_nat (m : ℕ) (t : ℝ) :
    circleCover ((m : ℝ) * t) = (circleCover t) ^ m := by
  change Circle.exp (2 * Real.pi * ((m : ℝ) * t)) = Circle.exp (2 * Real.pi * t) ^ m
  rw [show 2 * Real.pi * ((m : ℝ) * t) = (m : ℝ) * (2 * Real.pi * t) by ring]
  exact Circle.exp_natCast_mul _ _

/-- Winding number is multiplied by m under z ↦ z^m. The proof uses the
normalized real lift, so its sign agrees with the source convention. -/
theorem winding_power (w : Pi1 Circle 1 ≃* Multiplicative ℤ)
    (hw : WindingFormula w) (m : ℕ) (a : Pi1 Circle 1) :
    (w ((circlePowerPointed m).induced a)).toAdd = (m : ℤ) * (w a).toAdd := by
  obtain ⟨a, rfl⟩ := loopClass_surjective a
  obtain ⟨L, hL, _⟩ := pathLifting ℝ Circle circleCover P202.Topology.circleCovering.1 a.toContinuousMap 0
    (by simpa [circleCover] using a.source.symm)
  let M : C(unitInterval, ℝ) := ⟨fun t => (m : ℝ) * L t, by fun_prop⟩
  let b := (a.map (circlePower m).continuous).cast
    (circlePowerPointed m).point.symm (circlePowerPointed m).point.symm
  have hM : ∀ t, circleCover (M t) = b t := by
    intro t
    change circleCover ((m : ℝ) * L t) = (a t) ^ m
    rw [circleCover_mul_nat, hL.1 t]
    rfl
  have hM0 : M 0 = 0 := by change (m : ℝ) * L 0 = 0; rw [hL.2, mul_zero]
  have he := hw b M hM hM0
  have ha := hw a L hL.1 hL.2
  rw [inducedFormula Circle Circle 1 1 (circlePowerPointed m) a]
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_mul, Int.cast_natCast]
  change ((w (loopClass b)).toAdd : ℝ) = (m : ℝ) * ((w (loopClass a)).toAdd : ℝ)
  rw [he, ha]
  rfl

theorem circleSubgroup : Expected.circleSubgroup := by
  obtain ⟨w, hw⟩ := windingNumber
  refine ⟨w, hw, fun m hm a => ?_⟩
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(w b).toAdd, winding_power w hw m b⟩
  · rintro ⟨k, hk⟩
    refine ⟨w.symm (Multiplicative.ofAdd k), ?_⟩
    apply w.injective
    apply Multiplicative.toAdd.injective
    rw [winding_power w hw, w.apply_symm_apply]
    exact hk.symm

end
end P202.Topology.CoveringExamples
