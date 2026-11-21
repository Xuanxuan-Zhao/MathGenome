import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.AmbientSimplexStokes

/-! M12.03, paper.tex:2709–2775. The imported scalar integral uses the actual
ordered simplex in ambient coordinates and determinant-normalized evaluation
of intrinsic forms. No integration, Stokes or naturality certificate is assumed.
The totalized chart expression is differentiated only within the simplex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped Classical
namespace SmoothManifolds.IntegrationCochainData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  SmoothSingularData CornerData DeRhamData Set MeasureTheory
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

/-- A realization of the required integration map. Its existence is a theorem
obligation, not an additional premise on the manifold or on forms. -/
structure IntegrationMap {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) where
  map : ∀ q, K.forms q →ₗ[ℝ] Cochains S q
  evaluation : ∀ q (ω : K.forms q) (σ : SingularSimplex S q),
    map q ω (Finsupp.single σ 1) = simplexIntegral S C ω.val σ
  commutes : ∀ q (ω : K.forms q),
    map (q+1) (K.d q ω) = coboundary S q (map q ω)

/-- Explicit quotient instances keep the shared nested cochain types opaque. -/
instance singularCocyclesAddCommGroup (q : ℕ) : AddCommGroup (cocycles S q) :=
  @Submodule.addCommGroup ℝ (Cochains S q) inferInstance inferInstance inferInstance (cocycles S q)

instance singularCocyclesModule (q : ℕ) : Module ℝ (cocycles S q) :=
  @Submodule.module ℝ (Cochains S q) inferInstance inferInstance inferInstance (cocycles S q)

instance singularCohomologyAddCommGroup (q : ℕ) :
    AddCommGroup (SmoothSingularData.Cohomology S q) :=
  @Submodule.Quotient.addCommGroup ℝ (cocycles S q) inferInstance
    (singularCocyclesAddCommGroup S q) (singularCocyclesModule S q) (coboundaries S q)

instance singularCohomologyModule (q : ℕ) : Module ℝ (SmoothSingularData.Cohomology S q) :=
  @Submodule.Quotient.module ℝ (cocycles S q) inferInstance
    (singularCocyclesAddCommGroup S q) (singularCocyclesModule S q) (coboundaries S q)

/-- The quotient map for the already defined smooth singular cohomology. -/
def singularClass (q : ℕ) : cocycles S q →ₗ[ℝ] SmoothSingularData.Cohomology S q :=
  (coboundaries S q).mkQ

/-- The induced map is characterized on every closed intrinsic representative. -/
def IsInduced {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} (I : IntegrationMap S K)
    (F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q) : Prop :=
  ∀ q (ω : K.closed q), ∃ c : cocycles S q,
    c.val = I.map q ω.val ∧ F q (K.classOf q ω) = singularClass S q c

/-- The actual smooth singular pullback, specified by its values on cocycles. -/
def IsSingularCohomologyPullback {m : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (f : M → N)
    (G : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ] SmoothSingularData.Cohomology S q) : Prop :=
  ∀ q (c : cocycles T q), ∃ d : cocycles S q,
    d.val = cochainMap S T f q c.val ∧ G q (singularClass T q c) = singularClass S q d

end SmoothManifolds.IntegrationCochainData

namespace Specs.SmoothManifolds.Comparison.IntegrationCochain
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.SmoothSingularData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.IntegrationCochainData
  _root_.SmoothManifolds.CornerData Set MeasureTheory
universe u

/-- Each selected transverse vector points outwards across its barycentric face. -/
def face_outwardType : Prop :=
  ∀ {q : ℕ} (j : Fin (q+2)),
    simplexBarycentric (faceOutward j) j - simplexBarycentric (0 : Euclidean (q+1)) j = -1

/-- Outward-first sign relative to the ordered face map, including q=0 endpoints. -/
def face_orientationType : Prop :=
  ∀ {q : ℕ} (j : Fin (q+2)),
    (Matrix.of (fun r k : Fin (q+1) => orderedFaceFrame j k r)).det = (-1 : ℝ)^j.val

def simplexIntegralType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n a M) → CotangentBundle S → {q : ℕ} →
      Field S q → SingularSimplex S q → ℝ

noncomputable def simplexIntegralValue : simplexIntegralType :=
  fun S C _ ω σ => ∫ y in simplexSet _, ambientPullbackCoefficient S C ω σ y

def integrationCochainType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {C : CotangentBundle S} → {q : ℕ} →
      Field S q → Cochains S q

noncomputable def integrationCochainValue : integrationCochainType :=
  fun {_ _ _ _ S C _} ω => Finsupp.linearCombination ℝ (fun σ => simplexIntegral S C ω σ)

def simplex_compactType : Prop := ∀ q : ℕ, IsCompact (simplexSet q)

def zero_normalizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S}
    (ω : Field S 0) (σ : SingularSimplex S 0) (x : SmoothSingularData.Simplex 0),
    simplexIntegral S C ω σ =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S (σ.val x))) (ω (σ.val x))

def integration_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} (I J : IntegrationMap S K), I = J

/-- A conditional assembly lemma, not a replacement for integration_existsType. -/
def integrable_stokes_sufficeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B},
    (∀ q (ω : K.forms q) (σ : SingularSimplex S q),
      IntegrableOn (ambientPullbackCoefficient S C ω.val σ) (simplexSet q)) →
    (∀ q (ω : K.forms q) (σ : SingularSimplex S (q+1)),
      ∃ τ : Fin (q+2) → SingularSimplex S q,
        (∀ j, (τ j).val = σ.val ∘ face j) ∧
        simplexIntegral S C (K.d q ω).val σ =
          ∑ j, (-1 : ℝ)^j.val * simplexIntegral S C ω.val (τ j)) →
    Nonempty (IntegrationMap S K)

/-- Compactness and integrability are conclusions for every smooth form and simplex. -/
def integrabilityType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : FormBundle C q)
    (ω : Form B) (σ : SingularSimplex S q),
    IsCompact (simplexSet q) ∧
      IntegrableOn (ambientPullbackCoefficient S C ω.field σ) (simplexSet q)

/-- Existence for the full smooth de Rham complex, in all nonnegative degrees. -/
def integration_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B), Nonempty (IntegrationMap S K)

/-- Naturality is equality with the actual pullback by the intrinsic differential. -/
def naturalityType : Prop :=
  ∀ {n m q : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (f : M → N), MapData.IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∀ (ω : Field T q) (B : FormBundle A q), IsForm B ω →
    ∀ (σ : SingularSimplex S q) (hσ : SimplexSmooth T (f ∘ σ.val)),
      simplexIntegral S C (FormPullbackData.pullbackField S T f L ω) σ =
        simplexIntegral T A ω ⟨f ∘ σ.val,hσ⟩

/-- The full alternating-face Stokes identity; q=0 is the endpoint rule. -/
def simplex_stokesType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (ω : K.forms q) (σ : SingularSimplex S (q+1)),
    ∃ τ : Fin (q+2) → SingularSimplex S q,
      (∀ j, (τ j).val = σ.val ∘ face j) ∧
      simplexIntegral S C (K.d q ω).val σ =
        ∑ j : Fin (q+2), (-1 : ℝ)^j.val * simplexIntegral S C ω.val (τ j)

/-- The integration map descends to unique real-linear maps on the full quotients. -/
def cohomology_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (I : IntegrationMap S K),
    ∃! F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q, IsInduced S I F

/-- Every smooth map induces the usual pullback on smooth singular cohomology. -/
def singular_pullback_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    MapData.IsSmoothMap S T f →
    ∃ G : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ] SmoothSingularData.Cohomology S q,
      IsSingularCohomologyPullback S T f G

/-- The naturality square on the original de Rham and smooth singular quotients. -/
def cohomology_naturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E) (I : IntegrationMap S K) (H : IntegrationMap T J)
    (F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q)
    (G : ∀ q, J.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology T q),
    IsInduced S I F → IsInduced T H G →
    ∀ (f : M → N), MapData.IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∀ (P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q)
      (Q : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ] SmoothSingularData.Cohomology S q),
    IsCohomologyPullback C B K J f L P → IsSingularCohomologyPullback S T f Q →
    ∀ q (x : J.Cohomology q), F q (P q x) = Q q (G q x)

/-- Naturality of the whole cochain for the genuine pullback of smooth forms. -/
def cochain_naturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (I : IntegrationMap S K) (H : IntegrationMap T J)
    (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (q : ℕ) (α : J.forms q) (β : K.forms q)
    (hβ : β.val = FormPullbackData.pullbackField S T f L α.val),
    I.map q β = cochainMap S T f q (H.map q α)

/-- The map and its induced maps exist without analytic certificates. -/
def integration_cohomology_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B), ∃ I : IntegrationMap S K,
      ∃! F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q, IsInduced S I F

/-- Right-positive and left-negative endpoint evaluations. -/
def endpoint_sumType : Prop :=
  Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.endpoint_sumType

end Specs.SmoothManifolds.Comparison.IntegrationCochain
