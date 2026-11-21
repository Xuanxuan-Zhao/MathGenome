import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes

/-! Independent statements for M10.08's geometric boundary comparison.
The original intrinsic and D04 charts, tangent submodules, outward predicates,
orientation constructions and restrictions are compared on their common domain.
The theorem types contain no assumed compatibility certificate. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff SmoothManifolds.BoundaryConeData

namespace Specs.SmoothManifolds.Integration.EmbeddedBoundary
universe u v
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.EmbeddedCalculusData _root_.SmoothManifolds.EmbeddedAtlasData
  _root_.SmoothManifolds.BoundaryOrientationData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.OrientationData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model (EmbeddedChart IsEmbeddedManifold)
open Specs.D04.C14.ChartIndependentTangentSpaces.Model (tangentSpace chartDifferential)
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model (IsBoundaryParameter)
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model

/-- The local boundary comparison in matching embedded coordinates.
The only chart hypotheses are literal raw coordinate agreement and membership.
In particular no tangent, outwardness, orthogonality, or restriction identity is
assumed. All form degrees, including zero, are quantified. -/
def matching_boundary_geometryType : Prop :=
  ∀ {d N : ℕ} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) .halfSpace M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (e : ModelChart (d+1) .halfSpace M), e ∈ S.smoothStructure.val →
  ∀ c : EmbeddedChart ∞ (d+1) N M, MatchesEmbeddedChart e c →
  ∀ (u : E (d+1)) (hu : u ∈ c.source), IsBoundaryParameter c u →
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  p ∈ e.source →
  ∃ hp : p ∈ intrinsicBoundary S,
  ∃ hq : p.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M,
  ∀ B : SmoothManifold d .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
  ∀ L : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] TangentSpace S p,
  IsDifferential B S Subtype.val ⟨p, hp⟩ L →
  ∃! J : TangentSpace B ⟨p, hp⟩ ≃ₗ[ℝ]
      tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val,
    (∀ v, (J v).val = (I p (L v)).val) ∧
    (∀ v : TangentSpace S p,
      IsOutward S ⟨p, hp⟩ v ↔ IsOutwardVector 2 d M p.val (I p v).val) ∧
    (∃! ν : TangentSpace S p,
      IsOutwardUnitConormal 2 d M p.val (I p ν).val ∧ IsOutward S ⟨p, hp⟩ ν) ∧
    (∀ (k : ℕ) (η : Fiber (TangentSpace S p) k),
      transportCovector J k (_root_.SmoothManifolds.FormPullbackData.fiberPullback k L η) =
        (transportCovector (I p) k η).compLinearMap
          (Specs.D04.C15.GeneralizedStokes.Model.boundaryTangentInclusion 2 d M ⟨p.val, hq⟩))

/-- The actual quotient rays agree locally; an actual D04 unit conormal
lies on that ray. Changing any outward representative by its positive normal
factor and a tangent term has exactly the expected exterior-power effect. -/
def matching_outward_raysType : Prop :=
  ∀ {d N : ℕ} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) .halfSpace M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (e : ModelChart (d+1) .halfSpace M), e ∈ S.smoothStructure.val →
  ∀ c : EmbeddedChart ∞ (d+1) N M, MatchesEmbeddedChart e c →
  ∀ (u : E (d+1)) (hu : u ∈ c.source), IsBoundaryParameter c u →
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  p ∈ e.source →
  ∃ hp : p ∈ intrinsicBoundary S,
  ∀ B : SmoothManifold d .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
  ∀ L : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] TangentSpace S p,
  IsDifferential B S Subtype.val ⟨p, hp⟩ L →
  ∃ Q : NormalLine L ≃ₗ[ℝ] ℝ,
    Module.finrank ℝ (NormalLine L) = 1 ∧
    outwardRay L = {q | Q q < 0} ∧
    outwardRay L = Submodule.Quotient.mk ''
      {v : TangentSpace S p | IsOutwardVector 2 d M p.val (I p v).val} ∧
    (∃ ν : TangentSpace S p,
      IsOutwardUnitConormal 2 d M p.val (I p ν).val ∧
      Submodule.Quotient.mk ν ∈ outwardRay L) ∧
    ∀ v w : TangentSpace S p,
      IsOutwardVector 2 d M p.val (I p v).val →
      IsOutwardVector 2 d M p.val (I p w).val →
      ∃ t : ℝ, 0 < t ∧ w - t • v ∈ LinearMap.range L ∧
        ∀ η : ⋀[ℝ]^d (TangentSpace B ⟨p, hp⟩),
          normalWedge L w η = t • normalWedge L v η

/-- Dimension zero has empty boundaries in both original constructions.
Neither nonemptiness nor a chart-existence assumption is required. -/
def boundary_zeroType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} (M : Set (E N)) (S : SmoothManifold 0 a M),
    intrinsicBoundary S = ∅ ∧
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 0 M = ∅

/-- Required global equality, deliberately kept independent of the local
matching-chart theorem. This includes both model kinds and the empty and zero-dimensional cases. -/
def boundary_setType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
  ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
    intrinsicBoundary S = Subtype.val ⁻¹'
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 n M

/-- Matching smooth embedded charts are available at every boundary point;
no raw-coordinate matching hypothesis is added to the global comparison. -/
def boundary_matching_chartType : Prop :=
  ∀ {d N : ℕ} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) .halfSpace M, IsInducedSmoothStructure S →
  ∀ p : intrinsicBoundary S,
    ∃ (c : EmbeddedChart ∞ (d+1) N M) (u : E (d+1)) (hu : u ∈ c.source)
      (e : ModelChart (d+1) .halfSpace M),
      e ∈ S.smoothStructure.val ∧ MatchesEmbeddedChart e c ∧
      IsBoundaryParameter c u ∧ c.toFun u = p.val.val ∧ p.val ∈ e.source

/-- The canonical boundary tangent identification is characterized by the
actual inclusion differential and its ambient value. Outwardness, the unique
unit conormal, and all-degree restrictions agree at every boundary point.
No chart, compactness, or nonemptiness assumption is imposed. -/
def boundary_geometryType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (p : intrinsicBoundary S),
  ∃ hq : p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M,
  ∀ B : SmoothManifold d .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
  ∀ L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val,
  IsDifferential B S Subtype.val p L →
  ∃! J : TangentSpace B p ≃ₗ[ℝ]
      tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val.val,
    (∀ v, (J v).val = (I p.val (L v)).val) ∧
    (∀ v : TangentSpace S p.val,
      IsOutward S p v ↔ IsOutwardVector 2 d M p.val.val (I p.val v).val) ∧
    (∃! ν : TangentSpace S p.val,
      IsOutwardUnitConormal 2 d M p.val.val (I p.val ν).val ∧ IsOutward S p ν) ∧
    (∀ (k : ℕ) (η : Fiber (TangentSpace S p.val) k),
      transportCovector J k (_root_.SmoothManifolds.FormPullbackData.fiberPullback k L η) =
        (transportCovector (I p.val) k η).compLinearMap
          (Specs.D04.C15.GeneralizedStokes.Model.boundaryTangentInclusion 2 d M ⟨p.val.val, hq⟩))

/-- A family of genuine boundary inclusion differentials and its unique
canonical ambient tangent identification. The actual pullback field agrees
with D04 restriction in every degree, and in top boundary degree this is
literally D04's `boundaryRestriction`. -/
def boundary_restrictionType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (B : SmoothManifold d .euclidean (intrinsicBoundary S)), IsNaturalBoundary S B →
  ∃ (hq : ∀ p : intrinsicBoundary S,
      p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    (∀ p, IsDifferential B S Subtype.val p (L p)) ∧
    ∃! J : (p : intrinsicBoundary S) → TangentSpace B p ≃ₗ[ℝ]
        tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val.val,
      (∀ p v, (J p v).val = (I p.val (L p v)).val) ∧
      (∀ (k : ℕ) (η : Field S k) (p : intrinsicBoundary S),
        transportCovector (J p) k
          (_root_.SmoothManifolds.FormPullbackData.pullbackField B S Subtype.val L η p) =
          (transportField S I k η ⟨p.val.val, p.val.property⟩).compLinearMap
            (Specs.D04.C15.GeneralizedStokes.Model.boundaryTangentInclusion 2 d M ⟨p.val.val, hq p⟩)) ∧
      (∀ (η : Field S d) (p : intrinsicBoundary S),
        transportCovector (J p) d
          (_root_.SmoothManifolds.FormPullbackData.pullbackField B S Subtype.val L η p) =
          Specs.D04.C15.GeneralizedStokes.Model.boundaryRestriction
            (transportField S I d η) ⟨p.val.val, hq p⟩)

/-- Canonical determinant duality, rather than an identification by notation:
an intrinsic ray of determinant vectors determines a unique D04 orientation
of alternating top forms after any tangent isomorphism. The basis criterion
also distinguishes the two rays in degree zero. Manifold continuity and
induced boundary orientations are separate obligations. -/
def determinant_dualityType : Prop :=
  ∀ {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (n : ℕ), Module.finrank ℝ V = n →
  ∀ (I : V ≃ₗ[ℝ] W) (r : Module.Ray ℝ (⋀[ℝ]^n V)),
    ∃! o : _root_.Orientation ℝ W (Fin n),
      ∀ b : Module.Basis (Fin n) ℝ W,
        b.orientation = o ↔
          _root_.SmoothManifolds.OrientationData.IsPositive r
            (exteriorPower.ιMulti ℝ n (fun j => I.symm (b j)))

/-- Intrinsic determinant-vector rays determine a unique actual D04 continuous
positive-dimensional manifold orientation. Local constancy is proved for every
C² D04 chart, not assumed as a transport certificate. -/
def orientation_transportType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, 0 < n →
  IsEmbeddedManifold ∞ n M →
  ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (o : _root_.SmoothManifolds.OrientationData.Orientation S),
  ∃! O : Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation 2 n M,
    ∀ (p : M) (b : Module.Basis (Fin n) ℝ (tangentSpace 2 n M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p)
          (exteriorPower.ιMulti ℝ n (fun j => (I p).symm (b j)))

/-- Global normal-quotient rays and invariance under a change of outward representative. -/
def boundary_outward_raysType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : BundleOperationsData.CotangentBundle S) (p : intrinsicBoundary S),
  ∀ B : SmoothManifold d .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
  ∀ L : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val,
  IsDifferential B S Subtype.val p L →
  ∃ Q : NormalLine L ≃ₗ[ℝ] ℝ,
    Module.finrank ℝ (NormalLine L) = 1 ∧
    outwardRay L = {q | Q q < 0} ∧
    outwardRay L = Submodule.Quotient.mk ''
      {v : TangentSpace S p.val | IsOutwardVector 2 d M p.val.val (I p.val v).val} ∧
    (∃ ν : TangentSpace S p.val,
      IsOutwardUnitConormal 2 d M p.val.val (I p.val ν).val ∧
      Submodule.Quotient.mk ν ∈ outwardRay L) ∧
    ∀ v w : TangentSpace S p.val,
      IsOutwardVector 2 d M p.val.val (I p.val v).val →
      IsOutwardVector 2 d M p.val.val (I p.val w).val →
      ∃ t : ℝ, 0 < t ∧ w - t • v ∈ LinearMap.range L ∧
        ∀ η : ⋀[ℝ]^d (TangentSpace B p),
          normalWedge L w η = t • normalWedge L v η

def boundary_orientationType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+2) M →
  ∀ S : AtlasData.SmoothManifold (d+2) a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+2) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : BundleOperationsData.CotangentBundle S) (o : OrientationData.Orientation S),
  ∃ O : PositiveManifoldOrientation 2 (d+2) M,
    (∀ (p : M) (b : Module.Basis (Fin (d+2)) ℝ (tangentSpace 2 (d+2) M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        IsPositive (o.val p) (exteriorPower.ιMulti ℝ (d+2) (fun i => (I p).symm (b i)))) ∧
    ∀ B : AtlasData.SmoothManifold (d+1) .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
    ∀ q : OrientationData.Orientation B, IsInducedOrientation o q →
    ∃ (hq : ∀ p : intrinsicBoundary S,
        p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M)
      (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
      (J : (p : intrinsicBoundary S) → TangentSpace B p ≃ₗ[ℝ]
        tangentSpace 2 (d+1) (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) p.val.val),
      (∀ p, IsDifferential B S Subtype.val p (L p)) ∧
      (∀ p w, (J p w).val = (I p.val (L p w)).val) ∧
      ∀ ν : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M → E N,
      (∀ x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M,
        IsOutwardUnitConormal 2 (d+1) M x (ν x)) →
      ∃! bO : PositiveManifoldOrientation 2 (d+1)
          (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M),
        (∀ (x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M)
          (b : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1)
            (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) x)),
          b.orientation = bO.atPoint x x.property ↔ PositiveWithOutward O x (ν x) b) ∧
        (∀ (p : intrinsicBoundary S)
          (b : Module.Basis (Fin (d+1)) ℝ (tangentSpace 2 (d+1)
            (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+2) M) p.val.val)),
          b.orientation = bO.atPoint p.val.val (hq p) ↔
            IsPositive (q.val p)
              (exteriorPower.ιMulti ℝ (d+1) (fun i => (J p).symm (b i))))

def boundary_tangent_hyperplaneType : Prop :=
  ∀ {d N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ (d+1) M →
  ∀ S : SmoothManifold (d+1) a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 (d+1) M p.val,
  IsInclusionIdentification S I →
  ∀ (C : BundleOperationsData.CotangentBundle S)
    (c : EmbeddedChart ∞ (d+1) N M)
    (u : E (d+1)) (hu : u ∈ c.source), IsBoundaryParameter c u →
  let p : M := ⟨c.toFun u, (c.map_source hu).1⟩
  ∃ hp : p ∈ intrinsicBoundary S,
  ∀ B : SmoothManifold d .euclidean (intrinsicBoundary S), IsNaturalBoundary S B →
  ∀ L : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] TangentSpace S p,
  IsDifferential B S Subtype.val ⟨p, hp⟩ L →
  let K : TangentSpace B ⟨p, hp⟩ →ₗ[ℝ] E N :=
    (tangentSpace 2 (d+1) M p.val).subtype.comp ((I p).toLinearMap.comp L)
  LinearMap.range K =
      tangentSpace 2 d (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 (d+1) M) p.val ∧
    (LinearMap.range K : Set (E N)) =
      chartDifferential c u '' {w : E (d+1) | w (Fin.last d) = 0}

/-- The boundary comparison preserves the original subspace topology and every
underlying ambient point, including empty boundaries and dimension zero. -/
def boundary_baseType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
  ∀ S : SmoothManifold n a M, IsInducedSmoothStructure S →
  ∃! β : intrinsicBoundary S ≃ₜ
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 n M,
    ∀ p, (β p).val = p.val.val

/-- The two zero-dimensional conventions retain the same independent sign at
every point, including empty embedded bases. -/
def zero_orientation_transportType : Prop :=
  ∀ {N : ℕ} {a : ModelKind} (M : Set (E N)) (S : SmoothManifold 0 a M),
  ∃ F : _root_.SmoothManifolds.OrientationData.Orientation S ≃
      Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation M,
    ∀ (o : _root_.SmoothManifolds.OrientationData.Orientation S) (p : M),
      (F o p).val = 1 ↔ _root_.SmoothManifolds.OrientationData.IsPositive (o.val p)
        ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1)

/-- The induced orientation on a one-dimensional manifold's actual boundary
is precisely D04's signed-point construction. The actual ambient orientation
is constructed from the intrinsic determinant rays; no compatibility data is
an input hypothesis. All intrinsic induced realizations are covered. -/
def boundary_point_comparisonType : Prop :=
  ∀ {N : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ 1 M →
  ∀ S : SmoothManifold 1 a M, IsInducedSmoothStructure S →
  ∀ I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 1 M p.val,
  IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (o : _root_.SmoothManifolds.OrientationData.Orientation S),
  ∃ O : Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation 2 1 M,
    (∀ (p : M) (b : Module.Basis (Fin 1) ℝ (tangentSpace 2 1 M p.val)),
      b.orientation = O.atPoint p.val p.property ↔
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p)
          (exteriorPower.ιMulti ℝ 1 (fun j => (I p).symm (b j)))) ∧
    ∀ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)), IsNaturalBoundary S B →
    ∀ q : _root_.SmoothManifolds.OrientationData.Orientation B,
      IsInducedOrientation o q →
    ∃ hq : ∀ p : intrinsicBoundary S,
      p.val.val ∈ Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M,
    ∀ ν : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M → E N,
      (∀ x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M,
        IsOutwardUnitConormal 2 0 M x (ν x)) →
    ∃! s : Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1 M),
      (∀ x, ((s x).val = 1 ↔ PositiveOutwardLine O x (ν x)) ∧
        ((s x).val = -1 ↔ ¬ PositiveOutwardLine O x (ν x))) ∧
      (∀ p : intrinsicBoundary S,
        (s ⟨p.val.val, hq p⟩).val = 1 ↔
          _root_.SmoothManifolds.OrientationData.IsPositive (q.val p)
            ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1))

/-- The full actual orientation and signed endpoint comparison for a fixed
oriented interval and its direction ε. The natural boundary and orientation
are arbitrary intrinsic realizations. The base map preserves every ambient
point, and F recognizes the canonical scalar unit in degree zero. -/
def IntervalOrientationComparison (a b ε : ℝ)
    (S : SmoothManifold 1 .halfSpace {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
    (o : _root_.SmoothManifolds.OrientationData.Orientation S)
    (O : Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation 2 1
      {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) : Prop :=
  ∀ (B : SmoothManifold 0 .euclidean (intrinsicBoundary S)), IsNaturalBoundary S B →
  ∀ q : _root_.SmoothManifolds.OrientationData.Orientation B, IsInducedOrientation o q →
  ∃ β : intrinsicBoundary S ≃ₜ
      Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
        {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    (∀ p, (β p).val = p.val.val) ∧
  ∃ F : _root_.SmoothManifolds.OrientationData.Orientation B ≃
      Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
          {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}),
    (∀ (r : _root_.SmoothManifolds.OrientationData.Orientation B) (p : intrinsicBoundary S),
      (F r (β p)).val = 1 ↔ _root_.SmoothManifolds.OrientationData.IsPositive (r.val p)
        ((exteriorPower.zeroEquiv ℝ (TangentSpace B p)).symm 1)) ∧
  ∃ (ν : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
          {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} → E 1)
    (s : Specs.D04.C14.OrientationsAndChartSigns.Model.ZeroManifoldOrientation
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
          {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})),
    Continuous ν ∧
    (∀ x : Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
        {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
      IsOutwardUnitConormal 2 0 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} x (ν x)) ∧
    (∀ x, ((s x).val = 1 ↔ PositiveOutwardLine O x (ν x)) ∧
      ((s x).val = -1 ↔ ¬ PositiveOutwardLine O x (ν x))) ∧
    F q = s ∧
    ∃ (ha : a • standardBasis 1 0 ∈
        Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
          {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (hb : b • standardBasis 1 0 ∈
        Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 2 1
          {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}),
      (s ⟨a • standardBasis 1 0, ha⟩).val = -ε ∧
      (s ⟨b • standardBasis 1 0, hb⟩).val = ε ∧
      (ε = 1 → (s ⟨a • standardBasis 1 0, ha⟩).val = -1 ∧
        (s ⟨b • standardBasis 1 0, hb⟩).val = 1)

/-- Every intrinsic orientation of the actual smooth interval determines its
direction ε and the matching D04 endpoint signs. No directed-orientation or
compatibility hypothesis is added. The displayed intrinsic basis criterion
identifies the derived direction and treats both choices. -/
def interval_comparisonType : Prop :=
  ∀ a b : ℝ, a < b →
  ∀ S : SmoothManifold 1 .halfSpace {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    IsInducedSmoothStructure S →
  ∀ I : (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) →
      TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val,
    IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (o : _root_.SmoothManifolds.OrientationData.Orientation S),
  ∃ O : Specs.D04.C14.OrientationsAndChartSigns.Model.PositiveManifoldOrientation 2 1
      {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    (∀ (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (c : Module.Basis (Fin 1) ℝ
        (tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val)),
      c.orientation = O.atPoint p.val p.property ↔
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p)
          (exteriorPower.ιMulti ℝ 1 (fun j => (I p).symm (c j)))) ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
        (c : Module.Basis (Fin 1) ℝ
          (tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val)),
        _root_.SmoothManifolds.OrientationData.IsPositive (o.val p)
          (exteriorPower.ιMulti ℝ 1 (fun j => (I p).symm (c j))) ↔
            0 < ε * (c 0).val 0) ∧
      IntervalOrientationComparison a b ε S o O


/-- The standard positive intrinsic direction has actual D04 and intrinsic
endpoint signs -1,+1 under the canonical signed-point identification. -/
def interval_positiveType : Prop :=
∀ a b : ℝ, a < b →
  ∀ S : _root_.SmoothManifolds.AtlasData.SmoothManifold 1 .halfSpace {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    IsInducedSmoothStructure S →
  ∀ I : (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b}) →
      TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val,
    IsInclusionIdentification S I →
  ∀ (C : _root_.SmoothManifolds.BundleOperationsData.CotangentBundle S)
    (o : _root_.SmoothManifolds.OrientationData.Orientation S),
  (∀ (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
    (c : Module.Basis (Fin 1) ℝ
      (tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val)),
    IsPositive (o.val p) (exteriorPower.ιMulti ℝ 1 (fun j => (I p).symm (c j))) ↔
      0 < (c 0).val 0) →
  ∃ O : PositiveManifoldOrientation 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b},
    (∀ (p : {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b})
      (c : Module.Basis (Fin 1) ℝ
        (tangentSpace 2 1 {x : E 1 | a ≤ x 0 ∧ x 0 ≤ b} p.val)),
      c.orientation = O.atPoint p.val p.property ↔
        IsPositive (o.val p)
          (exteriorPower.ιMulti ℝ 1 (fun j => (I p).symm (c j)))) ∧
    IntervalOrientationComparison a b 1 S o O
end Specs.SmoothManifolds.Integration.EmbeddedBoundary
