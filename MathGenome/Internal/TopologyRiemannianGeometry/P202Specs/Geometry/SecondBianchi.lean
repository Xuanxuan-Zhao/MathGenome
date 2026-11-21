import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! The differential Bianchi identity of paper.tex, Theorem
`thm:p202-curvature-symmetry` (3553–3556, 3591–3598).

We use the multilinear-map realization of a (1,3) tensor. The induced
connection is characterized by differentiation of evaluation: differentiate
the output and subtract differentiation in each of the three input slots.
Existence, uniqueness, smoothness and this characterization are proof
obligations, not fields of the curvature tensor or additional hypotheses.
The default in `covariantDerivative` is eliminated by `derivative_ruleType`.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P202.SecondBianchiData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.CurvatureData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Evaluation of an actual smooth (1,3) tensor on smooth fields. -/
noncomputable def tensorSection (T : CurvatureTensor S) (Y Z W : Field S) : Field S :=
  ⟨fun p => T.val p (Y.val p) (Z.val p) (W.val p), T.smooth Y Z W⟩

/-- The evaluation Leibniz rule defining the induced tensor derivative. -/
noncomputable def tensorDerivativeField (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W : Field S) : Field S :=
  C.cov X (tensorSection T Y Z W) + (-1 : ℝ) • tensorSection T (C.cov X Y) Z W +
    (-1 : ℝ) • tensorSection T Y (C.cov X Z) W + (-1 : ℝ) • tensorSection T Y Z (C.cov X W)

abbrev FiberDerivative (S : SmoothManifold n a M) (p : M) :=
  TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ]
    TangentSpace S p →ₗ[ℝ] TangentSpace S p

def InducedDerivativeRule (C : Connection (tangentBundle S)) (T : CurvatureTensor S)
    (p : M) (D : FiberDerivative S p) : Prop :=
  ∀ X Y Z W : Field S, D (X.val p) (Y.val p) (Z.val p) (W.val p) =
    (tensorDerivativeField C T X Y Z W).val p

/-- The actual induced derivative on the multilinear-map representation.
Its defining property, and hence independence of all extensions, is proved
for every smooth tensor and arbitrary connection. No Bianchi identity is
part of the definition. -/
noncomputable def covariantDerivative (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (p : M) : FiberDerivative S p := by
  classical
  exact if h : ∃ D : FiberDerivative S p, InducedDerivativeRule C T p D then
    Classical.choose h else 0

end P202.SecondBianchiData

namespace P202Specs.Geometry.SecondBianchi
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.CurvatureData P202.SecondBianchiData
universe u

def covariantDerivativeType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → Connection (tangentBundle S) →
    CurvatureTensor S → (p : M) → FiberDerivative S p
noncomputable def covariantDerivativeValue : covariantDerivativeType := @covariantDerivative

/-- The induced derivative exists and is uniquely determined by evaluation. -/
def derivative_ruleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (p : M),
    InducedDerivativeRule C T p (covariantDerivative C T p) ∧
    ∀ D : FiberDerivative S p, InducedDerivativeRule C T p D →
      D = covariantDerivative C T p

def derivative_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S))
    (T : CurvatureTensor S) (X Y Z W : Field S),
    SmoothSection (tangentBundle S) (fun p =>
      covariantDerivative C T p (X.val p) (Y.val p) (Z.val p) (W.val p))

/-- The cyclic identity is equality of actual tangent endomorphisms, at every
point and in all finite dimensions. Curvature is the original commutator of
the Levi–Civita connection with the source sign convention. -/
def second_bianchiType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (X Y Z : TangentSpace S p),
      covariantDerivative C T p X Y Z + covariantDerivative C T p Y Z X +
        covariantDerivative C T p Z X Y = 0

end P202Specs.Geometry.SecondBianchi
