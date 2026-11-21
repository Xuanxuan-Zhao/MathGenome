import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Fin.VecNotation

/-! Algebraic part of paper.tex, Theorem `thm:p202-curvature-symmetry`,
with the sectional-curvature convention of lines 87–94. All fibers and
connections are the intrinsic upstream ones. Smoothness is the same test-field
criterion as for the upstream torsion tensor. No dimension restriction is made. -/
set_option autoImplicit false
namespace P202.CurvatureData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- The source sign convention, before descent to fibers. -/
noncomputable def curvature (C : Connection (tangentBundle S)) (X Y Z : Field S) : Field S :=
  C.cov X (C.cov Y Z) + (-1 : ℝ) • C.cov Y (C.cov X Z) +
    (-1 : ℝ) • C.cov (P202.TorsionMetricData.bracket X Y) Z

structure CurvatureTensor (S : SmoothManifold n a M) where
  val : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ]
    TangentSpace S p →ₗ[ℝ] TangentSpace S p
  smooth : ∀ X Y Z : Field S, SmoothManifolds.SectionExtensionData.SmoothSection
    (tangentBundle S) (fun p => val p (X.val p) (Y.val p) (Z.val p))

def RepresentsCurvature (C : Connection (tangentBundle S)) (T : CurvatureTensor S) : Prop :=
  ∀ (X Y Z : Field S) (p : M),
    T.val p (X.val p) (Y.val p) (Z.val p) = (curvature C X Y Z).val p

noncomputable def curvatureForm (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) (X Y Z W : TangentSpace S p) : ℝ :=
  pairing g p (T.val p X Y Z) W

/-- Defined only on independent pairs, so dimension zero and one have no
sectional planes. The denominator is the metric Gram determinant. -/
noncomputable def sectionalCurvature (g : RiemannianMetric S) (T : CurvatureTensor S)
    (p : M) (X Y : TangentSpace S p) (_h : LinearIndependent ℝ ![X, Y]) : ℝ :=
  curvatureForm g T p X Y Y X /
    (pairing g p X X * pairing g p Y Y - pairing g p X Y ^ 2)

end P202.CurvatureData

namespace P202Specs.Geometry.CurvatureAlgebra
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.CurvatureData
universe u

def curvatureType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → Connection (tangentBundle S) → Field S → Field S → Field S → Field S
noncomputable def curvatureValue : curvatureType := @curvature

def curvatureFormType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → RiemannianMetric S → CurvatureTensor S →
  (p : M) → TangentSpace S p → TangentSpace S p → TangentSpace S p → TangentSpace S p → ℝ
noncomputable def curvatureFormValue : curvatureFormType := @curvatureForm

def sectionalCurvatureType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n a M} → RiemannianMetric S → CurvatureTensor S →
  (p : M) → (X Y : TangentSpace S p) → LinearIndependent ℝ ![X, Y] → ℝ
noncomputable def sectionalCurvatureValue : sectionalCurvatureType := @sectionalCurvature

def tensorialType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)),
    (∀ (f : GlobalSmooth S) (X Y Z : Field S),
      curvature C (mulSection f X) Y Z = mulSection f (curvature C X Y Z)) ∧
    (∀ (f : GlobalSmooth S) (X Y Z : Field S),
      curvature C X (mulSection f Y) Z = mulSection f (curvature C X Y Z)) ∧
    (∀ (f : GlobalSmooth S) (X Y Z : Field S),
      curvature C X Y (mulSection f Z) = mulSection f (curvature C X Y Z))

def tensor_exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : Connection (tangentBundle S)),
    ∃! T : CurvatureTensor S, RepresentsCurvature C T

/-- Smooth coefficients in the canonical tangent trivializations. -/
def tensor_coordinates_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (T : CurvatureTensor S)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S) (j k l : Fin n)
    (p : M), p ∈ (tangentBundle S).baseSet i →
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => ((tangentBundle S).trivialization i
        ⟨q, T.val q
          (((tangentBundle S).trivialization i).symm q (Pi.single j 1))
          (((tangentBundle S).trivialization i).symm q (Pi.single k 1))
          (((tangentBundle S).trivialization i).symm q (Pi.single l 1))⟩).2) p

def symmetriesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (X Y Z W : TangentSpace S p),
      curvatureForm g T p X Y Z W = -curvatureForm g T p Y X Z W ∧
      curvatureForm g T p X Y Z W = -curvatureForm g T p X Y W Z ∧
      curvatureForm g T p X Y Z W = curvatureForm g T p Z W X Y

def first_bianchiType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (X Y Z : TangentSpace S p),
      T.val p X Y Z + T.val p Y Z X + T.val p Z X Y = 0

def sectional_basis_independentType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (p : M) (X Y U V : TangentSpace S p)
      (hXY : LinearIndependent ℝ ![X, Y]) (hUV : LinearIndependent ℝ ![U, V]),
      Submodule.span ℝ ({X, Y} : Set (TangentSpace S p)) =
        Submodule.span ℝ ({U, V} : Set (TangentSpace S p)) →
      sectionalCurvature g T p X Y hXY = sectionalCurvature g T p U V hUV

end P202Specs.Geometry.CurvatureAlgebra
