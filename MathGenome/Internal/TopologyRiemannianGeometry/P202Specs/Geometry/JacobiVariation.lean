import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiIVP
import Mathlib.Topology.Compactness.Compact

/-! Linearized geodesics, paper.tex 3975–4022. The parameter domains below
are open subsets of the actual geodesic interval. Smoothness is ordinary
joint C-infinity smoothness in position charts, not a Jacobi certificate.
A variation stores phase values only to record actual affine velocities.
No regularity, equation, or extension is required outside its rectangle.
-/
set_option autoImplicit false
namespace P202.JacobiVariationData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData P202.ConnectionData P202.MetricData
  P202.CurveConnectionData P202.GeodesicData P202.JacobiData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Both ordinary parameters are in their canonical real coordinates. -/
def PositionSmoothAt (Q : ℝ × ℝ → Phase S) (z : ℝ × ℝ) : Prop :=
  ContinuousAt (fun w => (Q w).1) z ∧
    ∀ e ∈ S.smoothStructure.val, (Q z).1 ∈ e.source →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (e (Q w).1).val) z

/-- A variation through affinely parametrized geodesics on an open set U.
The central equality is an equality of total representatives; off U it
imposes no equation or smoothness, and can always be obtained by changing
irrelevant representatives there. -/
structure GeodesicVariation (C : Connection (tangentBundle S))
    (q : ℝ → Phase S) (U : Set ℝ) where
  width : ℝ
  width_pos : 0 < width
  phase : ℝ × ℝ → Phase S
  central : ∀ t, phase (0, t) = q t
  smooth : ∀ s ∈ Ioo (-width) width, ∀ t ∈ U, PositionSmoothAt phase (s, t)
  geodesic : ∀ s ∈ Ioo (-width) width,
    IsGeodesicOn S C U (fun t => phase (s, t))

/-- The tangent fiber cast uses only the specified equality of base points. -/
def IsVariationField {C : Connection (tangentBundle S)} {q : ℝ → Phase S}
    {U : Set ℝ} (V : GeodesicVariation C q U)
    (J : (t : ℝ) → TangentSpace S (q t).1) : Prop :=
  ∀ t ∈ U, HasVelocityWithinAt S (fun s => (V.phase (s, t)).1) univ 0
    (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t)).symm (J t))

/-- Both the position and the covariant velocity jet vary. This uses an
actual derivative relation, rather than a default value of a total derivative. -/
def HasInitialVelocityJet {C : Connection (tangentBundle S)} {q : ℝ → Phase S}
    {U : Set ℝ} (V : GeodesicVariation C q U) (t₀ : ℝ)
    (w : TangentSpace S (q t₀).1) : Prop :=
  HasCovariantDerivativeAt C (fun s => (V.phase (s, t₀)).1)
    (fun s => (V.phase (s, t₀)).2) 0
    (Eq.mp (congrArg (fun z : Phase S => TangentSpace S z.1) (V.central t₀)).symm w)

end P202.JacobiVariationData

namespace P202Specs.Geometry.JacobiVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.JacobiVariationData
open Set
universe u

/-- Smoothness supplies the intrinsic s-derivative along the central row. -/
def variation_field_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (V : GeodesicVariation C q U),
      ∃ J : (t : ℝ) → TangentSpace S (q t).1, IsVariationField V J

def variation_field_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    {q : ℝ → Phase S} {U : Set ℝ} (V : GeodesicVariation C q U)
    {J K : (t : ℝ) → TangentSpace S (q t).1},
      IsVariationField V J → IsVariationField V K → ∀ t ∈ U, J t = K t

/-- Every smooth geodesic variation, allowing arbitrary rank and constant
central geodesics, satisfies the intrinsic Jacobi equation. -/
def variation_jacobiType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (U : Set ℝ), IsOpen U → ∀ (q : ℝ → Phase S)
      (V : GeodesicVariation C q U)
      (J : (t : ℝ) → TangentSpace S (q t).1),
      IsVariationField V J → IsJacobiField C R U q J

/-- Compact-segment realization on the actual open survival domain. The
initial time may lie anywhere in the original interval, even outside [a,b].
The open U contains both it and [a,b], and has one common positive s-width.
All phase values on the rectangle are supplied by the actual maximal flow.
The initial phase curve is genuinely continuous at zero and its position
and velocity have the prescribed intrinsic jets. -/
def realizationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q →
    ∀ (J : (t : ℝ) → TangentSpace S (q t).1), IsJacobiField C R I.carrier q J →
    ∀ t₀ ∈ I.carrier, ∀ w : TangentSpace S (q t₀).1,
      HasCovariantDerivativeAt C (fun t => (q t).1) J t₀ w →
    ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I.carrier →
    ∀ (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ∃ (U : Set ℝ) (_hU : IsOpen U), Icc a b ⊆ U ∧ t₀ ∈ U ∧ U ⊆ I.carrier ∧
        ∃ V : GeodesicVariation C q U,
          IsVariationField V J ∧ HasInitialVelocityJet V t₀ w ∧
          ContinuousAt (fun s => V.phase (s, t₀)) 0 ∧
          ∀ s ∈ Ioo (-V.width) V.width, ∀ t ∈ U,
            (t - t₀, V.phase (s, t₀)) ∈ flowDomain F ∧
              V.phase (s, t) = F.curve (V.phase (s, t₀)) (t - t₀)

/-- Reuse the full interval IVP and decomposition; they are part of the
complete source theorem but do not require a second independent proof. -/
def exists_uniqueType : Prop := P202Specs.Geometry.JacobiIVP.exists_uniqueType.{u}
def decompositionType : Prop := P202Specs.Geometry.JacobiIVP.decompositionType.{u}

/-- Simultaneous existence of a maximal family ensures that the realization
statement is not vacuous. No completeness or positive dimension is assumed. -/
def family_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)),
    ∃ F : CurveFamily (Phase S), P202.GeodesicData.IsMaximalFamily S C F

/-- The uniform tube assertion used in the source compactness argument.
It is intentionally stated for arbitrary compact sets, including the empty set. -/
def compact_survivalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
    ∀ (K : Set ℝ), IsCompact K → ∀ (t₀ : ℝ) (v : ℝ → Phase S),
      ContinuousAt v 0 → (∀ t ∈ K, (t - t₀, v 0) ∈ flowDomain F) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ K,
        (t - t₀, v s) ∈ flowDomain F

end P202Specs.Geometry.JacobiVariation
