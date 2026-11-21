import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith

/-! Canonical convex-body data and the elementary consequences preceding
`fa2:p2:projection-regularity`, paper.tex:9081–9109. -/
namespace ExpandedFA.HilbertCharacterization

universe u
open Set Metric
open scoped Topology
open Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup

abbrev symmetricConvexBody := @SymmetricConvexBody
abbrev bodyProjection := @BodyProjection
abbrev planeProjections := @PlaneProjections
abbrev projectionBody := @ProjectionBody
abbrev normalCone := @NormalCone
abbrev planarNormalCone := @PlanarNormalCone
abbrev normalRestriction := @restrictNormal

/-- These data really describe a projection with full range L. -/
theorem bodyProjection_algebra : projectionAlgebraType.{u} := by
  intro E _ _ K L P hP
  constructor
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hP.1 y
    · intro hx
      exact ⟨x, hP.2.1 x hx⟩
  · ext x
    exact hP.2.1 (P x) (hP.1 x)

/-- Preservation of the body gives equality with the central section. -/
theorem bodyProjection_image : projectionImageType.{u} := by
  intro E _ _ K L P hP
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hP.2.2 hy, hP.1 y⟩
  · rintro ⟨hx, hxL⟩
    exact ⟨x, hx, hP.2.1 x hxL⟩

/-- Compactness gives an outer radius and zero interior gives an inner radius. -/
theorem symmetricConvexBody_radii : radiiType.{u} := by
  intro E _ _ K hK
  obtain ⟨ε, hε, hin⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK.2.2.2)
  obtain ⟨R, hR, hout⟩ := hK.1.isBounded.subset_ball_lt 0 (0 : E)
  refine ⟨ε / 2, R, by linarith, hR, ?_, fun x hx => ball_subset_closedBall (hout hx)⟩
  exact (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hin

/-- Scale a Euclidean unit vector into the inner ball. Its projection lies
in the outer ball, giving r ‖P x‖ ≤ R, uniformly in the plane and projection. -/
theorem bodyProjection_norm_le : projectionBoundType.{u} := by
  intro E _ _ K L P r R hP hr hR hin hout
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hR hr.le)
  intro x hx
  have hmem : r • x ∈ closedBall (0 : E) r := by
    simp [mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hx]
  have hbound := hout (hP.2.2 (hin hmem))
  have hb : r * ‖P x‖ ≤ R := by
    simpa [mem_closedBall, dist_eq_norm, map_smul, norm_smul, abs_of_pos hr] using hbound
  exact (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hb)

/-- One pair of radii controls every K-preserving projection. -/
theorem projectionBody_uniform_bound : uniformBoundType.{u} := by
  intro E _ _ _ K hK
  obtain ⟨r, R, hr, hR, hin, hout⟩ := symmetricConvexBody_radii K hK.2.1
  exact ⟨r, R, hr, hR, hin, hout, fun L P hP => bodyProjection_norm_le K L P r R hP hr hR.le hin hout⟩

/-- Zero is retained, and the supporting functionals form a closed cone. -/
theorem normalCone_properties : normalConePropertiesType.{u} := by
  intro E _ _ K p
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : NormalCone K p = ⋂ x ∈ K, {f : E →L[ℝ] ℝ | f x ≤ f p} := by
      ext f
      simp [NormalCone]
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_le (by fun_prop) (by fun_prop)
  · intro x _
    simp
  · intro f hf g hg x hx
    exact add_le_add (hf x hx) (hg x hx)
  · intro t ht f hf x hx
    exact mul_le_mul_of_nonneg_left (hf x hx) ht

/-- A nonzero normal cannot have value zero at a boundary point, since the
body contains a neighborhood of zero. -/
theorem normalCone_positive : positiveNormalType.{u} := by
  intro E _ _ K p hK f hf hfn
  have hopen : IsOpen (f '' interior K) := f.isOpenMap_of_ne_zero hfn _ isOpen_interior
  have hzero : (0 : ℝ) ∈ f '' interior K := ⟨0, hK, map_zero f⟩
  obtain ⟨ε, hε, hin⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  have ha : ε / 2 ∈ f '' interior K := by
    apply hin
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  obtain ⟨x, hx, hfx⟩ := ha
  have hapos : 0 < f x := by rw [hfx]; linarith
  exact hapos.trans_le (hf x (interior_subset hx))

/-- Geometric Hahn–Banach supplies a nonzero supporting functional at each
boundary point. There is no regularity assumption on the body. -/
theorem normalCone_nonzero : supportingNormalType.{u} := by
  intro E _ _ K p hK hp
  obtain ⟨f, hfn, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hK.2.1 hp.2 ⟨0, hK.2.2.2⟩
  exact ⟨f, hf, hfn⟩

/-- Explicit extension by composition g P_L. -/
theorem planarNormal_extend : extendNormalType.{u} := by
  intro E _ _ K L P hP p g hg
  let Q : E →L[ℝ] L := P.codRestrict L hP.1
  refine ⟨g.comp Q, ?_, ?_, fun _ => rfl⟩
  · intro x hx
    have hp : Q (p : E) = p := Subtype.ext (hP.2.1 p p.property)
    change g (Q x) ≤ g (Q p)
    rw [hp]
    exact hg (Q x) (hP.2.2 hx)
  · ext x
    change g (Q (x : E)) = g x
    congr 1
    exact Subtype.ext (hP.2.1 x x.property)

/-- Restriction maps the ambient normal cone onto the normal cone of the section. -/
theorem normalCone_restriction : restrictionTypeTheorem.{u} := by
  intro E _ _ K L P hP p
  apply Set.Subset.antisymm
  · rintro g ⟨f, hf, rfl⟩ x hx
    exact hf x hx
  · intro g hg
    obtain ⟨f, hf, hfg, _⟩ := planarNormal_extend K L P hP p g hg
    exact ⟨f, hf, hfg⟩

/-- The exact central-plane specialization used in the regularity proof. -/
theorem projectionBody_normalCone_restriction : planeRestrictionType.{u} := by
  intro E _ _ _ K hK L hL p _hp
  obtain ⟨P, hP⟩ := hK.2.2 L hL
  exact normalCone_restriction K L P hP p

end ExpandedFA.HilbertCharacterization
