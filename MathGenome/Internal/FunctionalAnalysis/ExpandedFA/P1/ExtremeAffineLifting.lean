import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.ExtremeAffineLifting
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24FaceExtreme

/-!
# Extreme points lift through continuous affine surjections

The extreme-point lifting clause of `fa2:p1:milman-converse`
(paper.tex:5415–5436). The fiber over an extreme point is a nonempty
compact face. Apply the accepted compact-face extreme-point theorem
directly, without any metrizability or completeness assumption.
-/

universe u v

namespace ExpandedFA.P1

open ExtremeAffineLiftingSpec

/-- The fiber over an extreme point is a nonempty compact face. -/
theorem affine_extreme_fiber_isCompactFace : compactFiberType.{u, v} := by
  intro E F _ _ _ _ _ _ _ K L T hK hconv hT haff hsurj y hy
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hfiberCompact : IsCompact (affineFiber T y) :=
    ((isClosed_singleton.preimage hT).isCompact).image continuous_subtype_val
  obtain ⟨x₀, hx₀⟩ := hsurj y
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfiberCompact⟩
  · exact ⟨x₀, x₀, hx₀, rfl⟩
  · intro x hx z hz a b ha hb hab
    obtain ⟨x, hxT, rfl⟩ := hx
    obtain ⟨z, hzT, rfl⟩ := hz
    change T x = y at hxT
    change T z = y at hzT
    let w : K := ⟨a • (x : E) + b • (z : E), hconv x.property z.property ha hb hab⟩
    refine ⟨w, ?_, rfl⟩
    change T w = y
    apply Subtype.ext
    rw [haff x z w a b ha hb hab rfl, hxT, hzT, ← add_smul, hab, one_smul]
  · rintro x ⟨z, _, rfl⟩
    exact z.property
  · intro x hx z hz t ht0 ht1 hw
    obtain ⟨w, hwT, hw⟩ := hw
    change T w = y at hwT
    let x' : K := ⟨x, hx⟩
    let z' : K := ⟨z, hz⟩
    have himage : (y : F) = t • (T x' : F) + (1 - t) • (T z' : F) := by
      rw [← hwT]
      exact haff x' z' w t (1 - t) ht0.le (sub_nonneg.mpr ht1.le)
        (add_sub_cancel _ _) hw
    obtain ⟨hx', hz'⟩ := hy.2 (T x') (T x').property (T z') (T z').property
      t ht0 ht1 himage
    exact ⟨⟨x', Subtype.ext hx', rfl⟩, ⟨z', Subtype.ext hz', rfl⟩⟩

/-- Real continuous affine surjections lift extreme points. -/
theorem real_extreme_affine_lifting : realLiftingType.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ K L T hK hconv _hL _hLconv hT haff hsurj y hy
  have hfiber := affine_extreme_fiber_isCompactFace K L T hK hconv hT haff hsurj y hy
  obtain ⟨x, hx, hext⟩ := real_compact_face_extremePoint K (affineFiber T y) hfiber
  obtain ⟨x', hx'T, rfl⟩ := hx
  exact ⟨x', hext, hx'T⟩

/-- Complex ambient spaces are treated with their original real convexity. -/
theorem complex_extreme_affine_lifting : complexLiftingType.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ K L T hK hconv hL hLconv hT haff hsurj y hy
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : ContinuousSMul ℝ F := IsScalarTower.continuousSMul ℂ
  exact real_extreme_affine_lifting K L T hK hconv hL hLconv hT haff hsurj y hy

end ExpandedFA.P1
