import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Nullclines
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Coordinate nullclines and short straight transverse segments.
The tangent assertions refer to solution velocities, not tangents to the
nullcline as a geometric level set. No nullcline invariance is asserted. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.Nullclines
open Specs.D13Unified.Ch13.Nullclines
open Ch06.StateDerivative

def nullclineX : AutonomousODE Plane → Set Plane := nullclineXValue

def nullclineY : AutonomousODE Plane → Set Plane := nullclineYValue

def openQuadrant : Bool → Bool → Set Plane := openQuadrantValue

def phaseRegion : AutonomousODE Plane → Bool → Bool → Set Plane := phaseRegionValue

def StraightSegment.point : StraightSegment → ℝ → Plane := segmentPointValue

def StraightSegment.carrier : StraightSegment → Set Plane := segmentCarrierValue

def StraightSegment.coordinate : StraightSegment → Plane → ℝ := segmentCoordinateValue

def normalComponent : AutonomousODE Plane → StraightSegment → Plane → ℝ :=
  normalComponentValue

def IsTransverse : AutonomousODE Plane → StraightSegment → Prop := isTransverseValue

theorem equilibria_intersection : EquilibriaIntersection := by
  intro F
  ext p
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨⟨hp, congrArg Prod.fst hz⟩, ⟨hp, congrArg Prod.snd hz⟩⟩
  · rintro ⟨⟨hp, hx⟩, ⟨_, hy⟩⟩
    exact ⟨hp, Prod.ext hx hy⟩

theorem constant_iff_intersection : ConstantIffIntersection := by
  intro F hF p hp
  rw [← Ch11.Orbits.equilibrium_characterization F hF p hp]
  constructor
  · intro hz
    exact ⟨⟨hp, congrArg Prod.fst hz⟩, ⟨hp, congrArg Prod.snd hz⟩⟩
  · rintro ⟨⟨_, hx⟩, ⟨_, hy⟩⟩
    exact Prod.ext hx hy

theorem trajectory_tangent : TrajectoryTangent := by
  intro F I x hx t ht
  exact (hx.2.2 t ht).deriv

theorem tangent_quadrant : TangentQuadrant := by
  intro F I x hx t ht sx sy
  rw [trajectory_tangent F I x hx t ht]
  exact ⟨fun hv => ⟨hx.2.1 t ht, hv⟩, fun hv => hv.2⟩

private lemma unique_quadrant {v : Plane} (hx : v.1 ≠ 0) (hy : v.2 ≠ 0) :
    ∃! s : Bool × Bool, v ∈ openQuadrant s.1 s.2 := by
  rcases lt_or_gt_of_ne hx with hxn | hxp <;>
    rcases lt_or_gt_of_ne hy with hyn | hyp
  · refine ⟨(false, false), ⟨hxn, hyn⟩, ?_⟩
    rintro ⟨sx, sy⟩ hs
    cases sx <;> cases sy <;> simp_all [openQuadrant, openQuadrantValue]
    all_goals linarith
  · refine ⟨(false, true), ⟨hxn, hyp⟩, ?_⟩
    rintro ⟨sx, sy⟩ hs
    cases sx <;> cases sy <;> simp_all [openQuadrant, openQuadrantValue]
    all_goals linarith
  · refine ⟨(true, false), ⟨hxp, hyn⟩, ?_⟩
    rintro ⟨sx, sy⟩ hs
    cases sx <;> cases sy <;> simp_all [openQuadrant, openQuadrantValue]
    all_goals linarith
  · refine ⟨(true, true), ⟨hxp, hyp⟩, ?_⟩
    rintro ⟨sx, sy⟩ hs
    cases sx <;> cases sy <;> simp_all [openQuadrant, openQuadrantValue]
    all_goals linarith

theorem unique_tangent_quadrant : UniqueTangentQuadrant := by
  intro F I x hx t ht hnx hny
  have h₁ : (F.eval (x t)).1 ≠ 0 := fun he => hnx ⟨hx.2.1 t ht, he⟩
  have h₂ : (F.eval (x t)).2 ≠ 0 := fun he => hny ⟨hx.2.1 t ht, he⟩
  rw [trajectory_tangent F I x hx t ht]
  exact ⟨unique_quadrant h₁ h₂, fun he => h₁ (congrArg Prod.fst he)⟩

theorem vertical_tangent : VerticalTangent := by
  intro F I x hx t ht hmem
  have h₁ := hmem.1.2
  have h₂ : (F.eval (x t)).2 ≠ 0 := fun he => hmem.2 ⟨hx.2.1 t ht, he⟩
  rw [trajectory_tangent F I x hx t ht]
  exact ⟨Prod.ext h₁ rfl, h₂, fun he => h₂ (congrArg Prod.snd he)⟩

theorem horizontal_tangent : HorizontalTangent := by
  intro F I x hx t ht hmem
  have h₂ := hmem.1.2
  have h₁ : (F.eval (x t)).1 ≠ 0 := fun he => hmem.2 ⟨hx.2.1 t ht, he⟩
  rw [trajectory_tangent F I x hx t ht]
  exact ⟨Prod.ext rfl h₂, h₁, fun he => h₁ (congrArg Prod.fst he)⟩

theorem flow_tangent : FlowTangent := by
  intro F hF p hp t ht
  exact ((flow_ivp F hF hp).1.2.2 t ht).deriv

private lemma direction_sq_pos (S : StraightSegment) :
    0 < S.direction.1 ^ 2 + S.direction.2 ^ 2 := by
  have hn := S.direction_ne_zero
  have : S.direction.1 ≠ 0 ∨ S.direction.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (Prod.ext h.1 h.2)
  rcases this with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

theorem coordinate_point : CoordinatePoint := by
  intro S u
  have hn := ne_of_gt (direction_sq_pos S)
  change (((S.center.1 + u * S.direction.1) - S.center.1) * S.direction.1 +
    ((S.center.2 + u * S.direction.2) - S.center.2) * S.direction.2) /
    (S.direction.1 ^ 2 + S.direction.2 ^ 2) = u
  apply (div_eq_iff hn).mpr
  ring

theorem coordinate_order : CoordinateOrder := by
  intro S u v
  rw [coordinate_point S u, coordinate_point S v]

lemma StraightSegment.point_injective (S : StraightSegment) : Function.Injective S.point := by
  intro u v huv
  have := congrArg S.coordinate huv
  change segmentCoordinateValue S (segmentPointValue S u) =
    segmentCoordinateValue S (segmentPointValue S v) at this
  rw [coordinate_point S u, coordinate_point S v] at this
  exact this

theorem segment_parametrization : SegmentParametrization := by
  intro S p
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, ⟨hu, he⟩, fun v hv => S.point_injective (hv.2.trans he.symm)⟩
  · rintro ⟨u, ⟨hu, he⟩, _⟩
    exact ⟨u, hu, he⟩

/-- Pull back admissibility and the nonzero normal component along a fixed
line. A small closed parameter interval then lies in both neighborhoods. -/
private lemma small_transverse_with_direction (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (p : Plane) (hp : p ∈ F.domain)
    (d : Plane) (hdet : d.1 * (F.eval p).2 - d.2 * (F.eval p).1 ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ S : TransverseSegment F, S.center = p ∧ S.radius < R := by
  have hd : d ≠ 0 := by
    intro he
    apply hdet
    simp [he]
  let g : ℝ → Plane := fun u => p + u • d
  have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hf : ContinuousAt F.eval (g 0) := by
    simpa [g] using hF.continuousOn.continuousAt (F.isOpen_domain.mem_nhds hp)
  have hfc : ContinuousAt (fun u => F.eval (g u)) 0 := hf.comp hg.continuousAt
  have hnc : ContinuousAt (fun u =>
      d.1 * (F.eval (g u)).2 - d.2 * (F.eval (g u)).1) 0 :=
    (continuousAt_const.mul hfc.snd).sub (continuousAt_const.mul hfc.fst)
  have hne : ∀ᶠ u in 𝓝 (0 : ℝ),
      d.1 * (F.eval (g u)).2 - d.2 * (F.eval (g u)).1 ≠ 0 :=
    hnc.eventually_ne (by simpa [g] using hdet)
  have hdom : ∀ᶠ u in 𝓝 (0 : ℝ), g u ∈ F.domain :=
    hg.continuousAt (F.isOpen_domain.mem_nhds (by simpa [g] using hp))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hdom.and hne)
  let r := min R ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by
    have := min_le_left R ε
    dsimp [r]
    linarith
  have hrε : r < ε := by
    have := min_le_right R ε
    dsimp [r]
    linarith
  let S : StraightSegment := ⟨p, d, r, hr, hd⟩
  have hS : IsTransverse F S := by
    have hu (u : ℝ) (hu : u ∈ Icc (-r) r) :
        g u ∈ F.domain ∧ d.1 * (F.eval (g u)).2 - d.2 * (F.eval (g u)).1 ≠ 0 := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    constructor
    · rintro _ ⟨u, hu', rfl⟩
      exact (hu u hu').1
    · rintro _ ⟨u, hu', rfl⟩
      exact (hu u hu').2
  exact ⟨⟨S, hS⟩, rfl, hrR⟩

theorem small_transverse_segment : SmallTransverseSegment := by
  intro F hF p hp hn R hR
  by_cases hx : (F.eval p).1 = 0
  · have hy : (F.eval p).2 ≠ 0 := fun he => hn (Prod.ext hx he)
    apply small_transverse_with_direction F hF p hp (1, 0) _ R hR
    simpa using hy
  · apply small_transverse_with_direction F hF p hp (0, 1) _ R hR
    simpa using hx

end D13Unified.Ch13.Nullclines
