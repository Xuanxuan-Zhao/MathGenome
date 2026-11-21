import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionCornerCollar
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Independent geometric interface for the two-direction local graph argument.
The region, signs, curves and joins are precisely the canonical source objects.
No analytic identity or smoothness of the graph at a join is assumed. -/
noncomputable section
open Set Topology
open scoped ContDiff

namespace P202Specs.BoundaryGraphDirections
open P202Specs.PlanarRegionTopology

/-- The original scalar projection; no reparametrization of the curve is made. -/
def arcProjection (c : RegularJordanCurve) (e : Plane) (t : ℝ) : ℝ :=
  inner ℝ e (realLift c.parametrization t)

/-- Actual two-sided smooth extensions and strict signed projection on a short
real lift. The two pieces, cut at `t`, are the finite smooth pieces needed for
one-dimensional substitution. The interval is shorter than a full period. -/
structure DirectedProjectionArc (c : RegularJordanCurve) (σ t : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  short : 2 * radius < 1
  axis : Plane
  unit_axis : ‖axis‖ = 1
  extensionRadius : ℝ
  radius_lt : radius < extensionRadius
  leftExtension : ℝ → Plane
  rightExtension : ℝ → Plane
  left_smooth : ContDiffOn ℝ ∞ leftExtension (Ioo (t - extensionRadius) (t + extensionRadius))
  right_smooth : ContDiffOn ℝ ∞ rightExtension (Ioo (t - extensionRadius) (t + extensionRadius))
  left_eq : EqOn leftExtension (realLift c.parametrization) (Icc (t - radius) t)
  right_eq : EqOn rightExtension (realLift c.parametrization) (Icc t (t + radius))
  left_positive : ∀ u ∈ Icc (t - radius) t, 0 < σ * inner ℝ axis (deriv leftExtension u)
  right_positive : ∀ u ∈ Icc t (t + radius), 0 < σ * inner ℝ axis (deriv rightExtension u)
  increasing_signed : StrictMonoOn (fun u => σ * arcProjection c axis u)
    (Icc (t - radius) (t + radius))

/-- The frame map has standard Euclidean coordinates, with its second axis
exactly the positive quarter turn of its first. Thus it preserves orientation.
The map is an actual affine isometry, here based at the origin. -/
structure OrientedFrame (e : Plane) where
  map : Plane ≃ᵃⁱ[ℝ] Plane
  formula : ∀ z, map z = z 0 • e + z 1 • quarterTurn e

/-- Exact graph data on a *common ambient* neighborhood. The height is an
ordinary continuous real function, extended outside the projected subarc.
`local_visits` excludes other components and remote visits, including at a
period seam. Its unique parameter lies in the open short interval. -/
structure LocalDirectedBoundaryGraph (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (i : Fin R.boundaryCount) (t : ℝ) (O : Set Plane) where
  arc : DirectedProjectionArc (R.curve i) (s i) t
  frame : OrientedFrame arc.axis
  height : ℝ → ℝ
  continuous_height : Continuous height
  arc_identity : ∀ u ∈ Icc (t - arc.radius) (t + arc.radius),
    realLift (R.curve i).parametrization u =
      frame.map !₂[arcProjection (R.curve i) arc.axis u,
        height (arcProjection (R.curve i) arc.axis u)]
  domain_eq : R.domain ∩ O = (frame.map '' {z : Plane | height (z 0) < z 1}) ∩ O
  boundary_eq : R.boundary ∩ O = (frame.map '' {z : Plane | z 1 = height (z 0)}) ∩ O
  subarc_eq : R.boundary ∩ O =
    (realLift (R.curve i).parametrization '' Icc (t - arc.radius) (t + arc.radius)) ∩ O
  increasing : s i = 1 → StrictMonoOn (arcProjection (R.curve i) arc.axis)
    (Icc (t - arc.radius) (t + arc.radius))
  decreasing : s i = -1 → StrictAntiOn (arcProjection (R.curve i) arc.axis)
    (Icc (t - arc.radius) (t + arc.radius))
  local_visits : ∀ (j : Fin R.boundaryCount) (q : ParameterCircle),
    (R.curve j).parametrization q ∈ O → j = i ∧
      ∃! u : ℝ, u ∈ Ioo (t - arc.radius) (t + arc.radius) ∧ (u : ParameterCircle) = q
  periodic : Function.Periodic (realLift (R.curve i).parametrization) 1
  periodic_derivative : Function.Periodic (deriv (realLift (R.curve i).parametrization)) 1

/-- Both directions work in one neighborhood of the given actual point.
The directions are the second frame axes, hence unit and constant. -/
structure TwoDirectionBoundaryGraphs (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (p : Plane) where
  component : Fin R.boundaryCount
  parameter : ℝ
  at_point : realLift (R.curve component).parametrization parameter = p
  neighborhood : Set Plane
  open_neighborhood : IsOpen neighborhood
  mem_neighborhood : p ∈ neighborhood
  graphs : Fin 2 → LocalDirectedBoundaryGraph R s component parameter neighborhood
  independent : LinearIndependent ℝ (fun k => quarterTurn (graphs k).arc.axis)
  unit_normal : ∀ k, ‖quarterTurn (graphs k).arc.axis‖ = 1

namespace Expected

/-- The complete original geometric obligation, including the actual side and
all original boundary visits. Neither a graph nor its sign is an input. -/
def boundaryGraphDirections : Prop := ∀ (R : PlanarRegion)
  (s : Fin R.boundaryCount → ℝ), IsInducedBoundaryOrientation R s →
    ∀ p ∈ R.boundary, Nonempty (TwoDirectionBoundaryGraphs R s p)

/-- An open strict tangent cone contains two independent unit axes. -/
def twoStrictDirections : Prop := ∀ u v : Plane, u ≠ 0 → v ≠ 0 →
  NormedSpace.normalize u ≠ -NormedSpace.normalize v →
  ∃ e : Fin 2 → Plane, LinearIndependent ℝ e ∧
    ∀ k, ‖e k‖ = 1 ∧ 0 < inner ℝ (e k) u ∧ 0 < inner ℝ (e k) v

/-- Two independent short signed projections with the actual smooth extension
and cut data. The given sign is allowed to reverse the original parameter. -/
def twoDirectedProjectionArcs : Prop := ∀ (c : RegularJordanCurve) (σ t : ℝ),
  (σ = 1 ∨ σ = -1) → ∃ A : Fin 2 → DirectedProjectionArc c σ t,
    LinearIndependent ℝ (fun k => (A k).axis)

end Expected
end P202Specs.BoundaryGraphDirections
