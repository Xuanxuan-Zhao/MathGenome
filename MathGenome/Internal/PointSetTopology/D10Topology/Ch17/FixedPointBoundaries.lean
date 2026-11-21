import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.FixedPointBoundaries
import Mathlib.Tactic.Linarith

/-! Boundary examples for Brouwer's conclusion, paper.tex lines 2911–2918. -/
open Set
noncomputable section
universe u

namespace D10Topology.Ch17

abbrev unitCircle := Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle
abbrev circleRotation := Specs.D10Topology.Ch17.FixedPointBoundaries.circleRotation
abbrev intervalMap := Specs.D10Topology.Ch17.FixedPointBoundaries.intervalMap

theorem empty_no_fixed_point :
    Specs.D10Topology.Ch17.FixedPointBoundaries.empty_no_fixed_point.{u} := by
  intro X _ _ f
  exact ⟨continuous_of_discreteTopology, fun ⟨x, _⟩ => isEmptyElim x⟩

theorem circle_plane_coordinates :
    Specs.D10Topology.Ch17.FixedPointBoundaries.circle_plane_coordinates := by
  refine ⟨Complex.equivRealProdCLM.toHomeomorph.isHomeomorph, ?_, ?_⟩
  · intro z
    change ‖z‖ = 1 ↔ z.re ^ 2 + z.im ^ 2 = 1
    have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq z).symm
    constructor
    · intro hz
      rw [hz] at h
      nlinarith
    · intro hz
      have := norm_nonneg z
      nlinarith
  · intro a ha z
    exact Prod.ext (Complex.mul_re a z.1) (Complex.mul_im a z.1)

theorem circle_geometry :
    Specs.D10Topology.Ch17.FixedPointBoundaries.circle_geometry := by
  refine ⟨⟨1, by simp [Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle]⟩,
    ?_, ?_⟩
  · simpa only [unitCircle, Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle,
      Metric.sphere, dist_zero_right] using (isCompact_sphere (0 : ℂ) 1)
  · intro hc
    have hp : (1 : ℂ) ∈ unitCircle := by simp [unitCircle,
      Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle]
    have hm : (-1 : ℂ) ∈ unitCircle := by simp [unitCircle,
      Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle]
    have hz := hc hp hm (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    simp only [smul_neg, add_neg_cancel] at hz
    norm_num [Specs.D10Topology.Ch17.FixedPointBoundaries.unitCircle] at hz

theorem rotation_properties :
    Specs.D10Topology.Ch17.FixedPointBoundaries.rotation_properties := by
  intro a ha hn
  constructor
  · exact (continuous_const.mul continuous_subtype_val).subtype_mk _
  · rintro ⟨z, hz⟩
    have he : a * z.1 = 1 * z.1 := by
      simpa only [circleRotation, Specs.D10Topology.Ch17.FixedPointBoundaries.circleRotation,
        one_mul] using congrArg Subtype.val hz
    have hne : z.1 ≠ 0 := by
      intro h
      have hnorm : ‖z.1‖ = 1 := z.2
      simp [h] at hnorm
    exact hn (mul_right_cancel₀ hne he)

theorem interval_geometry :
    Specs.D10Topology.Ch17.FixedPointBoundaries.interval_geometry := by
  exact ⟨⟨1/2, by norm_num⟩, convex_Ioo 0 1, Metric.isBounded_Ioo 0 1, by simp⟩

theorem interval_properties :
    Specs.D10Topology.Ch17.FixedPointBoundaries.interval_properties := by
  constructor
  · exact ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk _
  · rintro ⟨x, hx⟩
    have he : (x.1 + 1) / 2 = x.1 := congrArg Subtype.val hx
    have := x.2.2
    linarith

theorem identity_properties :
    Specs.D10Topology.Ch17.FixedPointBoundaries.identity_properties.{u} := by
  intro E _ _ K _ _ hK
  obtain ⟨x, hx, y, hy, hxy⟩ := hK
  let a : K := ⟨x, hx⟩
  let b : K := ⟨y, hy⟩
  have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
  refine ⟨continuous_id, fun _ => rfl, ⟨a, b, hab, rfl, rfl⟩, ?_⟩
  intro q hq h
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hbound := h a b
  change dist a b ≤ q * dist a b at hbound
  nlinarith

end D10Topology.Ch17
