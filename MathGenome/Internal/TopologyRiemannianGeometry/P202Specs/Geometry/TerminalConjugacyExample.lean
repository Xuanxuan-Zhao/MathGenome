import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ModelPolarDomains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConstantCurvaturePolar

/-! The substantive endpoint example following cor:p202-no-interior-conjugate,
paper.tex 4177–4182. The sphere, induced metric, intrinsic tangent fibers,
geodesics, competitor curves and Jacobi equation are the canonical upstream
objects. Every unit initial direction and every global maximal representative
are covered. No minimizing or conjugacy certificate occurs in the hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace P202.TerminalConjugacyData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.SpaceFormData P202.MetricData P202.ConnectionData P202.CurveConnectionData
  P202.GeodesicData P202.CurveData P202.CurvatureData P202.JacobiData
  P202.ExponentialJacobiData P202.ConstantCurvaturePolarData P202.ModelPolarData

/-- A great semicircle has its original arc-length parametrization, minimizes
among all piecewise C¹ competitors (on any compact parameter interval), and has
an explicit nonzero normal Jacobi field vanishing at both endpoints. The field
is nonzero at the midpoint, so nontriviality holds on the segment itself. -/
def SemicircleConclusion {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a)
    (v : TangentSpace B.manifold p) (q : ℝ → Phase B.manifold) : Prop :=
  (∀ t : ℝ, (q t).1.val = greatCircle a p.val (B.ambientVector p v) t ∧
    tangentNorm B.metric (q t).1 (q t).2 = 1) ∧
  (q (Real.pi * a)).1.val = -p.val ∧
  (∃ γ : PiecewiseC1Curve B.manifold 0 (Real.pi * a),
    (∀ t, γ t = (q t).1) ∧ γ 0 = p ∧
    length B.metric γ = Real.pi * a ∧
    modelDistance B.metric p (q (Real.pi * a)).1 = Real.pi * a ∧
    ∀ {l r : ℝ} (η : PiecewiseC1Curve B.manifold l r),
      η l = p → η r = (q (Real.pi * a)).1 → length B.metric γ ≤ length B.metric η) ∧
  ∃ R : CurvatureTensor B.manifold, RepresentsCurvature B.connection R ∧
    ∃ w : TangentSpace B.manifold (q 0).1,
      w ≠ 0 ∧ pairing B.metric (q 0).1 w (q 0).2 = 0 ∧
      let J := fun t => (a * Real.sin (t / a)) •
        parallel B.connection D13Unified.OpenTimeInterval.whole q w t
      IsJacobiField B.connection R Set.univ q J ∧ J 0 = 0 ∧ J (Real.pi * a) = 0 ∧
      HasCovariantDerivativeAt B.connection (fun t => (q t).1) J 0 w ∧
      (∀ t, pairing B.metric (q t).1 (J t) (q t).2 = 0) ∧
      J (Real.pi * a / 2) ≠ 0 ∧
      ConjugateAlong B.manifold B.connection R D13Unified.OpenTimeInterval.whole q
        ⟨0, Set.mem_univ _⟩ ⟨Real.pi * a, Set.mem_univ _⟩

end P202.TerminalConjugacyData

namespace P202Specs.Geometry.TerminalConjugacyExample
open SmoothManifolds.TangentData P202.SpaceFormData P202.MetricData
  P202.GeodesicData P202.TerminalConjugacyData

/-- Original unconditional proposition. Extra premises of the conditional
implementation belong only to its helper, never to this independent Spec. -/
def terminal_conjugacyType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∀ (A : EuclideanModel (n + 1)) (B : SphericalModel n a A), B.Conclusion →
    ∀ (p : Sphere n a) (v : TangentSpace B.manifold p), tangentNorm B.metric p v = 1 →
    ∀ q : ℝ → Phase B.manifold,
      IsMaximalThrough B.manifold B.connection ⟨p, v⟩ D13Unified.OpenTimeInterval.whole q →
      SemicircleConclusion B p v q

end P202Specs.Geometry.TerminalConjugacyExample
