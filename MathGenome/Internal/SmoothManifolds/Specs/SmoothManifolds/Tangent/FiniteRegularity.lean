import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Coordinate derivatives and finite-regularity tangent vectors.
All constructions start with ordinary C^r atlases and ambient derivatives,
including at half-space faces. No derivation model is used in their definition. -/
namespace SmoothManifolds.FiniteRegularityData
open ModelData AtlasData MapData Set Filter
open scoped Topology
universe u v

/-- A coordinate derivative is realized by an actual differentiable ambient
extension of the germ. It has no arbitrary derivative certificate. -/
def HasCoordinateDerivative {n m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) (g : M → Euclidean m) (p : M)
    (L : Euclidean n →L[ℝ] Euclidean m) : Prop :=
  ∃ F : Euclidean n → Euclidean m,
    HasFDerivAt F L (e p).val ∧
      (fun y => F (e y).val) =ᶠ[𝓝 p] g

/-- The uniquely determined ambient derivative when it exists. The zero default
only makes the expression total outside the differentiable locus. -/
noncomputable def coordinateDerivative {n m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) (g : M → Euclidean m) (p : M) :
    Euclidean n →L[ℝ] Euclidean m := by
  classical
  exact if h : ∃ L, HasCoordinateDerivative e g p L then Classical.choose h else 0

noncomputable def chartDerivative {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (e : ModelChart n a M) (d : ModelChart m b N) (f : M → N) (p : M) :
    Euclidean n →L[ℝ] Euclidean m :=
  coordinateDerivative e (fun y => (d (f y)).val) p

/-- A representative consists of an atlas chart at p and an unrestricted
coordinate vector; normal directions are retained at boundary points. -/
abbrev CoordinateRepresentative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (p : M) :=
  {e : ModelChart n a M // e ∈ A ∧ p ∈ e.source} × Euclidean n

/-- The relation to be proved an equivalence from the derivative cocycle. -/
def RepresentativeRel {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (p : M)
    (v w : CoordinateRepresentative A p) : Prop :=
  chartDerivative v.1.val w.1.val id p v.2 = w.2

/-- Quotient by the equivalence closure is defined without assuming the cocycle.
The theorem that `Quot.eq` is exactly `RepresentativeRel` rules out spurious
identifications and supplies the intended quotient. -/
abbrev CoordinateTangent {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (p : M) :=
  Quot (RepresentativeRel A p)

def tangentClass {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (p : M)
    (e : ModelChart n a M) (he : e ∈ A) (hp : p ∈ e.source) (v : Euclidean n) :
    CoordinateTangent A p := Quot.mk _ (⟨e, he, hp⟩, v)

/-- The vector space structure and all its coordinate realizations are outputs
of the construction. This is not additional data on the input manifold. -/
structure FiberModel {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : Set (ModelChart n a M)) (p : M) where
  group : AddCommGroup (CoordinateTangent A p)
  module : @Module ℝ (CoordinateTangent A p) _ group.toAddCommMonoid
  coordinates : letI := group; letI := module
    ∀ (e : ModelChart n a M), e ∈ A → p ∈ e.source →
      CoordinateTangent A p ≃ₗ[ℝ] Euclidean n
  coordinates_class : ∀ (e d : ModelChart n a M) (he : e ∈ A) (hd : d ∈ A)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) (v : Euclidean n),
    coordinates d hd hpd (tangentClass A p e he hp v) = chartDerivative e d id p v

/-- The coordinate characterization of the induced linear tangent map. -/
def IsCoordinateDifferential {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    {A : Set (ModelChart n a M)} {B : Set (ModelChart m b N)}
    (f : M → N) (p : M) (S : FiberModel A p) (T : FiberModel B (f p)) :
    letI := S.group; letI := S.module; letI := T.group; letI := T.module
    (CoordinateTangent A p →ₗ[ℝ] CoordinateTangent B (f p)) → Prop :=
  fun L => ∀ (e : ModelChart n a M) (d : ModelChart m b N)
    (he : e ∈ A) (hd : d ∈ B) (hp : p ∈ e.source) (hfp : f p ∈ d.source)
    (v : CoordinateTangent A p),
    T.coordinates d hd hfp (L v) = chartDerivative e d f p (S.coordinates e he hp v)

/-- The coordinate expression of the total tangent map of an ambient map. -/
noncomputable def ambientTangentMap {n m : ℕ} (F : Euclidean n → Euclidean m)
    (z : Euclidean n × Euclidean n) : Euclidean m × Euclidean m :=
  (F z.1, fderiv ℝ F z.1 z.2)

end SmoothManifolds.FiniteRegularityData

namespace Specs.SmoothManifolds.Tangent.FiniteRegularity
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.FiniteRegularityData
open Set Filter
open scoped Topology
universe u v w

def HasCoordinateDerivativeType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ModelChart n a M → (M → Euclidean m) → M →
      (Euclidean n →L[ℝ] Euclidean m) → Prop
noncomputable def HasCoordinateDerivativeValue : HasCoordinateDerivativeType :=
  @FiniteRegularityData.HasCoordinateDerivative

def coordinateDerivativeType :=
  {n m : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ModelChart n a M → (M → Euclidean m) → M → (Euclidean n →L[ℝ] Euclidean m)
noncomputable def coordinateDerivativeValue : coordinateDerivativeType :=
  @FiniteRegularityData.coordinateDerivative

def chartDerivativeType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
    [TopologicalSpace M] → [TopologicalSpace N] →
    ModelChart n a M → ModelChart m b N → (M → N) → M →
      (Euclidean n →L[ℝ] Euclidean m)
noncomputable def chartDerivativeValue : chartDerivativeType :=
  @FiniteRegularityData.chartDerivative

def CoordinateRepresentativeType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n a M) → M → Type u
noncomputable def CoordinateRepresentativeValue : CoordinateRepresentativeType :=
  @FiniteRegularityData.CoordinateRepresentative

def RepresentativeRelType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (A : Set (ModelChart n a M)) → (p : M) →
      CoordinateRepresentative A p → CoordinateRepresentative A p → Prop
noncomputable def RepresentativeRelValue : RepresentativeRelType :=
  @FiniteRegularityData.RepresentativeRel

def CoordinateTangentType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n a M) → M → Type u
noncomputable def CoordinateTangentValue : CoordinateTangentType :=
  @FiniteRegularityData.CoordinateTangent

def tangentClassType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (A : Set (ModelChart n a M)) → (p : M) → (e : ModelChart n a M) →
      e ∈ A → p ∈ e.source → Euclidean n → CoordinateTangent A p
noncomputable def tangentClassValue : tangentClassType :=
  @FiniteRegularityData.tangentClass

def FiberModelType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n a M) → M → Type u
noncomputable def FiberModelValue : FiberModelType := @FiniteRegularityData.FiberModel

def IsCoordinateDifferentialType :=
  {n m : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
    [TopologicalSpace M] → [TopologicalSpace N] →
    {A : Set (ModelChart n a M)} → {B : Set (ModelChart m b N)} →
    (f : M → N) → (p : M) → (S : FiberModel A p) → (T : FiberModel B (f p)) →
      letI := S.group; letI := S.module; letI := T.group; letI := T.module
      (CoordinateTangent A p →ₗ[ℝ] CoordinateTangent B (f p)) → Prop
noncomputable def IsCoordinateDifferentialValue : IsCoordinateDifferentialType :=
  @FiniteRegularityData.IsCoordinateDifferential

def ambientTangentMapType :=
  {n m : ℕ} → (Euclidean n → Euclidean m) →
    (Euclidean n × Euclidean n) → (Euclidean m × Euclidean m)
noncomputable def ambientTangentMapValue : ambientTangentMapType :=
  @FiniteRegularityData.ambientTangentMap

def extension_independenceType : Prop :=
  ∀ {n m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (g : M → Euclidean m) (p : M),
    p ∈ e.source → ∀ L K, HasCoordinateDerivative e g p L →
      HasCoordinateDerivative e g p K → L = K

def coordinateDerivative_eqType : Prop :=
  ∀ {n m : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (g : M → Euclidean m) (p : M),
    p ∈ e.source → ∀ L, HasCoordinateDerivative e g p L →
      coordinateDerivative e g p = L

def chartDerivative_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞), 1 ≤ r →
    ∀ (e : ModelChart n a M) (d : ModelChart m b N) (f : M → N) (p : M),
    ChartContDiffAt r e d f p →
      HasCoordinateDerivative e (fun y => (d (f y)).val) p (chartDerivative e d f p)

def chartDerivative_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (e : ModelChart n a M) (p : M), p ∈ e.source →
      chartDerivative e e id p = ContinuousLinearMap.id ℝ (Euclidean n)

def chartDerivative_compType : Prop :=
  ∀ {n m l : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (r : ℕ∞), 1 ≤ r →
    ∀ (e : ModelChart n a M) (d : ModelChart m b N) (k : ModelChart l c P)
      (f : M → N) (g : N → P) (p : M),
    p ∈ e.source → ContinuousAt f p → ChartContDiffAt r e d f p →
    ChartContDiffAt r d k g (f p) →
    chartDerivative e k (g ∘ f) p =
      (chartDerivative d k g (f p)).comp (chartDerivative e d f p)

def derivative_cocycleType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞), 1 ≤ r → ∀ (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ∀ (e d k : ModelChart n a M), e ∈ A → d ∈ A → k ∈ A →
    ∀ (p : M), p ∈ e.source → p ∈ d.source → p ∈ k.source →
      chartDerivative e k id p =
        (chartDerivative d k id p).comp (chartDerivative e d id p)

def ambientTangentMap_regularType : Prop :=
  ∀ {n m : ℕ} (r : ℕ), 1 ≤ r →
    ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean m),
      IsOpen U → ContDiffOn ℝ r F U →
      ContDiffOn ℝ (r - 1 : ℕ) (ambientTangentMap F) (U ×ˢ univ)

/-- The quotient is exactly by transition derivatives, without further
identifications from the equivalence closure. -/
def tangentClass_eq_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞), 1 ≤ r → ∀ (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ∀ (p : M) (e d : ModelChart n a M) (he : e ∈ A) (hd : d ∈ A)
      (hp : p ∈ e.source) (hpd : p ∈ d.source) (v w : Euclidean n),
      tangentClass A p e he hp v = tangentClass A p d hd hpd w ↔
        chartDerivative e d id p v = w

def fiberModel_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞), 1 ≤ r → ∀ (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ∀ p : M, Nonempty (FiberModel A p)

def coordinateDifferential_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞), 1 ≤ r →
    ∀ (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)),
    IsContDiffAtlas r A → IsContDiffAtlas r B → ∀ (f : M → N),
    ManifoldContDiff r A B f → ∀ (p : M) (S : FiberModel A p) (T : FiberModel B (f p)),
    letI := S.group; letI := S.module; letI := T.group; letI := T.module
    ∃! L : CoordinateTangent A p →ₗ[ℝ] CoordinateTangent B (f p),
      IsCoordinateDifferential f p S T L

def coordinateDifferential_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞), 1 ≤ r → ∀ (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ∀ (p : M) (S : FiberModel A p),
    letI := S.group; letI := S.module
    IsCoordinateDifferential id p S S LinearMap.id

def coordinateDifferential_compType : Prop :=
  ∀ {n m l : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (r : ℕ∞), 1 ≤ r →
    ∀ (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N))
      (C : Set (ModelChart l c P)),
    IsContDiffAtlas r A → IsContDiffAtlas r B → IsContDiffAtlas r C →
    ∀ (f : M → N) (g : N → P), ManifoldContDiff r A B f → ManifoldContDiff r B C g →
    ∀ (p : M) (S : FiberModel A p) (T : FiberModel B (f p)) (U : FiberModel C (g (f p))),
    letI := S.group; letI := S.module; letI := T.group; letI := T.module
    letI := U.group; letI := U.module
    ∀ (L : CoordinateTangent A p →ₗ[ℝ] CoordinateTangent B (f p))
      (K : CoordinateTangent B (f p) →ₗ[ℝ] CoordinateTangent C (g (f p))),
      IsCoordinateDifferential f p S T L → IsCoordinateDifferential g (f p) T U K →
        IsCoordinateDifferential (g ∘ f) p S U (K.comp L)

/-- A single C^(r-1) ambient extension represents the actual tangent map
near each base point, at every fiber vector. Applied to id in two charts,
this is the total tangent-space transition regularity assertion. -/
def tangentMap_local_regularType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ), 1 ≤ r →
    ∀ (e : ModelChart n a M) (d : ModelChart m b N) (f : M → N) (p : M),
    p ∈ e.source → ChartContDiffAt r e d f p →
      ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean m),
        IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ r F U ∧
        ContDiffOn ℝ (r - 1 : ℕ) (ambientTangentMap F) (U ×ˢ univ) ∧
        ∀ᶠ y in 𝓝 p, (e y).val ∈ U ∧ ∀ v : Euclidean n,
          ambientTangentMap F ((e y).val, v) = ((d (f y)).val, chartDerivative e d f y v)

/-- The total transition between two tangent charts is C^(r-1) in local
ambient coordinates on every overlap, with its actual derivative. -/
def tangentTransition_local_regularType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ), 1 ≤ r → ∀ (A : Set (ModelChart n a M)), IsContDiffAtlas r A →
    ∀ (e d : ModelChart n a M), e ∈ A → d ∈ A → ∀ (p : M),
    p ∈ e.source → p ∈ d.source →
      ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
        IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ r F U ∧
        ContDiffOn ℝ (r - 1 : ℕ) (ambientTangentMap F) (U ×ˢ univ) ∧
        ∀ᶠ y in 𝓝 p, (e y).val ∈ U ∧ ∀ v : Euclidean n,
          ambientTangentMap F ((e y).val, v) = ((d y).val, chartDerivative e d id y v)

/-- On smooth data the coordinate quotient is the same tangent fiber as the
shared derivation model, with agreement in every chart. -/
def smooth_compatibilityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (F : FiberModel S.smoothStructure.val p),
    letI := F.group; letI := F.module
    ∃ E : CoordinateTangent S.smoothStructure.val p ≃ₗ[ℝ] TangentData.TangentSpace S p,
      ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
        (C : TangentData.TangentSpace S p ≃ₗ[ℝ] Euclidean n),
        DifferentialData.IsChartCoordinates S p e C →
          ∀ v, C (E v) = F.coordinates e he hp v

/-- The same identifications intertwine the finite-coordinate and smooth
intrinsic differentials, not merely the dimensions of their fibers. -/
def smooth_differential_compatibilityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    IsSmoothMap S T f → ∀ (p : M)
      (F : FiberModel S.smoothStructure.val p) (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ (E : CoordinateTangent S.smoothStructure.val p ≃ₗ[ℝ] TangentData.TangentSpace S p)
      (H : CoordinateTangent T.smoothStructure.val (f p) ≃ₗ[ℝ] TangentData.TangentSpace T (f p)),
    (∀ (e : ModelChart n a M) (he) (hp) (C), DifferentialData.IsChartCoordinates S p e C →
      ∀ v, C (E v) = F.coordinates e he hp v) →
    (∀ (d : ModelChart m b N) (hd) (hfp) (D), DifferentialData.IsChartCoordinates T (f p) d D →
      ∀ v, D (H v) = G.coordinates d hd hfp v) →
    ∀ (L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
        CoordinateTangent T.smoothStructure.val (f p))
      (K : TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p)),
      IsCoordinateDifferential f p F G L → DifferentialData.IsDifferential S T f p K →
        ∀ v, H (L v) = K (E v)

end Specs.SmoothManifolds.Tangent.FiniteRegularity
