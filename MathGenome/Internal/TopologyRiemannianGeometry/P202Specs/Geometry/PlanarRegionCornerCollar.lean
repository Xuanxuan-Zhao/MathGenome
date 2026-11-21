import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionFoundation

/-!
Independent statements for the local geometry in paper.tex 4789–4809.
The full target uses only the canonical geometric input. The projection and
parametrized-graph statements are intermediate conclusions, not extra region
hypotheses. In particular no collar or graph is assumed in `localGeometry`.
-/
noncomputable section
open Set Topology
open scoped ContDiff

namespace P202Specs.PlanarRegionTopology

/-- A continuous parametrization of a closed arc as a graph over an ordinary
closed scalar interval. Its projection is the identity, and its image is
exactly the given subarc. This does not itself assert ambient side charts. -/
structure ProjectedArcGraph (c : RegularJordanCurve) (t ε : ℝ) (a : Plane) where
  map : C(Icc (inner ℝ a (realLift c.parametrization (t - ε)))
    (inner ℝ a (realLift c.parametrization (t + ε))), Plane)
  projection : ∀ x, inner ℝ a (map x) = x.val
  image_eq : range map = realLift c.parametrization '' Icc (t - ε) (t + ε)

/-- The left normals to all differentiable one-sided extensions of the actual
curve at a point. Both limiting normals are retained at a corner. -/
def oneSidedCurveNormals (c : RegularJordanCurve) (p : Plane) : Set Plane :=
  {v | ∃ (s η : ℝ) (f : ℝ → Plane), 0 < η ∧
    realLift c.parametrization s = p ∧ DifferentiableAt ℝ f s ∧
    (EqOn f (realLift c.parametrization) (Icc (s - η) s) ∨
      EqOn f (realLift c.parametrization) (Icc s (s + η))) ∧
    v = quarterTurn (deriv f s)}


namespace Expected

/-- Unchanged full local-geometry assertion from the parent draft. -/
def localGeometry : Prop := ∀ R : PlanarRegion,
  IsSurfaceWithBoundary R.carrier R.boundary ∧
    LocallyContractibleSpace R.carrier ∧
    Nonempty (BoundaryCollar R.carrier R.boundary) ∧
    ∃ s, IsInducedBoundaryOrientation R s

/-- Actual half-plane charts for the original closed region, with exactly its frontier. -/
def regionSurface : Prop := ∀ R : PlanarRegion,
  IsSurfaceWithBoundary R.carrier R.boundary

/-- Local contractibility derived from the charts constructed from the geometric input. -/
def regionLocallyContractible : Prop := ∀ R : PlanarRegion,
  LocallyContractibleSpace R.carrier

/-- Smooth ambient positive transverse directions along every actual smooth arc.
This is an intermediate conclusion and does not prescribe which side is the domain. -/
def curveSmoothPositiveTransverseField : Prop := ∀ c : RegularJordanCurve,
  ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
    ∀ s : ℝ, (s : ParameterCircle) ∉ c.joins →
      0 < inner ℝ (F (realLift c.parametrization s))
        (quarterTurn (deriv (realLift c.parametrization) s))

/-- Transversality includes every actual one-sided tangent at corners. -/
def curveSmoothOneSidedTransverseField : Prop := ∀ c : RegularJordanCurve,
  ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
    (∀ p ∈ c.trace, ∀ v ∈ oneSidedCurveNormals c p, 0 < inner ℝ (F p) v) ∧
    (∀ p ∈ c.trace, F p ≠ 0)

/-- One smooth ambient field is transverse to all actual one-sided tangents
on every given boundary component, and is nonzero on the entire frontier. -/
def regionSmoothOneSidedTransverseField : Prop := ∀ R : PlanarRegion,
  ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
    (∀ (i : Fin R.boundaryCount) (p : Plane), p ∈ (R.curve i).trace →
      ∀ v ∈ oneSidedCurveNormals (R.curve i) p, 0 < inner ℝ (F p) v) ∧
    (∀ p ∈ R.boundary, F p ≠ 0)

/-- A single increasing projection across both sides of every join, including
reflex corners, obtained from the actual noncuspidal derivative hypotheses. -/
def cornerProjection : Prop := ∀ (c : RegularJordanCurve) (t : ℝ),
  ∃ (ε : ℝ) (a : Plane), 0 < ε ∧ a ≠ 0 ∧
    StrictMonoOn (fun s => inner ℝ a (realLift c.parametrization s))
      (Icc (t - ε) (t + ε))

/-- Continuous inverse graph coordinates on an actual two-sided subarc. -/
def cornerGraph : Prop := ∀ (c : RegularJordanCurve) (t : ℝ),
  ∃ (ε : ℝ) (a : Plane), 0 < ε ∧ a ≠ 0 ∧
    inner ℝ a (realLift c.parametrization (t - ε)) <
      inner ℝ a (realLift c.parametrization (t + ε)) ∧
    Nonempty (ProjectedArcGraph c t ε a)

/-- Every actual boundary point has a neighborhood in which the entire
region boundary is precisely the constructed graph subarc. -/
def boundaryLocalGraph : Prop := ∀ (R : PlanarRegion) (i : Fin R.boundaryCount) (t : ℝ),
  ∃ (ε : ℝ) (a : Plane) (G : ProjectedArcGraph (R.curve i) t ε a) (O : Set Plane),
    0 < ε ∧ a ≠ 0 ∧ IsOpen O ∧ realLift (R.curve i).parametrization t ∈ O ∧
    inner ℝ a (realLift (R.curve i).parametrization (t - ε)) <
      inner ℝ a (realLift (R.curve i).parametrization t) ∧
    inner ℝ a (realLift (R.curve i).parametrization t) <
      inner ℝ a (realLift (R.curve i).parametrization (t + ε)) ∧
    O ∩ R.boundary = O ∩ range G.map

/-- The original local side hypothesis selects opposite roles for the two
connected sides of a constructed graph neighborhood. The partition is an
intermediate proof-stage object; it is not assumed in `localGeometry`. -/
def localSideSelection : Prop := ∀ (U O A B : Set Plane) (p : Plane),
  IsOpen U → LocallyOneSided U → p ∈ frontier U → IsOpen O → p ∈ O →
    IsPreconnected A → IsPreconnected B → O \ frontier U = A ∪ B →
    (A ⊆ U ∧ B ⊆ (closure U)ᶜ) ∨ (B ⊆ U ∧ A ⊆ (closure U)ᶜ)

/-- Actual half-plane charts suffice for local contractibility. This
implication is a helper; the full target still requires construction of charts. -/
def surfaceLocallyContractible : Prop := ∀ K B : Set Plane,
  IsSurfaceWithBoundary K B → LocallyContractibleSpace K

end Expected
end P202Specs.PlanarRegionTopology
