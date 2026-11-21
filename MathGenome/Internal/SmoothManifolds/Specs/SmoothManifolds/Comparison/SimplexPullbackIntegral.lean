import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.SmoothSingularComplex
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalStokes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Canonical definitions migrated from the unaccepted parent draft.
The within derivative never differentiates the artificial zero extension across
an edge of the simplex. Analytic regularity is a conclusion to be proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SmoothManifolds.IntegrationCochainData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  SmoothSingularData CornerData DeRhamData Set MeasureTheory
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

/-- A choice from the given maximal smooth atlas; it imposes no extra hypothesis. -/
def targetChart (p : M) : ModelChart n a M :=
  (S.smoothStructure.property.1.1 p).choose

theorem targetChart_mem (p : M) : targetChart S p ∈ S.smoothStructure.val :=
  (S.smoothStructure.property.1.1 p).choose_spec.1

theorem mem_targetChart_source (p : M) : p ∈ (targetChart S p).source :=
  (S.smoothStructure.property.1.1 p).choose_spec.2

/-- An arbitrary totalization outside the simplex, used only for within derivatives. -/
def chartExpression {q : ℕ} (σ : SingularSimplex S q)
    (c : ModelChart n a M) (y : Euclidean q) : Euclidean n :=
  if hy : y ∈ simplexSet q then (c (σ.val ⟨y,hy⟩)).val else 0

/-- The coordinate realization of dσ at x, transported to the intrinsic tangent
fiber. The within derivative retains all corner points and works in degree zero. -/
def simplexDifferential (C : CotangentBundle S) {q : ℕ}
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) :
    Euclidean q →ₗ[ℝ] TangentSpace S (σ.val x) :=
  let c := targetChart S (σ.val x)
  ((C.tangent.fiberCoordinates.equiv c (targetChart_mem S _) (σ.val x)
    (mem_targetChart_source S _)).symm.toLinearMap).comp
      (fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val).toLinearMap

/-- Coefficient of σ*ω in dt₁∧⋯∧dt_q, in the source's standard orientation. -/
def pullbackCoefficient (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) : ℝ :=
  evaluate (TangentSpace S (σ.val x)) q (ω (σ.val x))
    (fun i => simplexDifferential S C σ x (Pi.single i 1))

def ambientPullbackCoefficient (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q) (σ : SingularSimplex S q) (y : Euclidean q) : ℝ :=
  if hy : y ∈ simplexSet q then pullbackCoefficient S C ω σ ⟨y,hy⟩ else 0

/-- Lebesgue integral on the standard simplex, with the empty-product measure at q=0. -/
def simplexIntegral (C : CotangentBundle S) {q : ℕ}
    (ω : Field S q) (σ : SingularSimplex S q) : ℝ :=
  ∫ y in simplexSet q, ambientPullbackCoefficient S C ω σ y

end SmoothManifolds.IntegrationCochainData

namespace SmoothManifolds.SimplexPullbackIntegral
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  SmoothSingularData CornerData IntegrationCochainData Set
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S}

/-- The literal alternating pullback on every closed-simplex tangent space. -/
def simplexPullback {q r : ℕ} (ω : Field S r) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) : (Euclidean q) [⋀^Fin r]→ₗ[ℝ] ℝ :=
  (evaluate (TangentSpace S (σ.val x)) r (ω (σ.val x))).compLinearMap
    (simplexDifferential S C σ x)

/-- The continuous coordinate realization. The implementation proves continuity
of every finite-dimensional alternating pullback, so the fallback is never used
on the simplex. Values outside the simplex are immaterial totalizations. -/
def coordinatePullback {q r : ℕ} (ω : Field S r) (σ : SingularSimplex S q) :
    LocalStokesData.CoordinateForm q r := fun y =>
  if hy : y ∈ simplexSet q then
    if h : Continuous (simplexPullback (C := C) ω σ ⟨y,hy⟩) then
      { simplexPullback (C := C) ω σ ⟨y,hy⟩ with cont := h }
    else 0
  else 0

end SmoothManifolds.SimplexPullbackIntegral

namespace Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.SmoothSingularData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.IntegrationCochainData Set MeasureTheory
open _root_.SmoothManifolds.SimplexPullbackIntegral
open scoped Topology
universe u

def simplex_compactType : Prop := ∀ q : ℕ, IsCompact (simplexSet q)
def simplex_uniqueDiffType : Prop := ∀ q : ℕ, UniqueDiffOn ℝ (simplexSet q)

/-- Every local smooth chart extension has precisely the canonical within Jacobian.
The agreement is only required as a germ on the actual closed simplex. -/
def chart_jacobianType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (σ : SingularSimplex S q)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (x : SmoothSingularData.Simplex q) (hx : σ.val x ∈ c.source),
    ∃ U : Set (Euclidean q), IsOpen U ∧ x.val ∈ U ∧
      ∃ F : Euclidean q → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun y : SmoothSingularData.Simplex q => F y.val) =ᶠ[𝓝 x]
          (fun y => (c (σ.val y)).val) ∧
        fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val =
          fderiv ℝ F x.val

/-- No chosen extension can change the within Jacobian, even on higher faces. -/
def extension_independentType : Prop :=
  ∀ {n q : ℕ} (x : SmoothSingularData.Simplex q)
    (F G : Euclidean q → Euclidean n),
    DifferentiableAt ℝ F x.val → DifferentiableAt ℝ G x.val →
    ((fun y : SmoothSingularData.Simplex q => F y.val) =ᶠ[𝓝 x]
      (fun y => G y.val)) → fderiv ℝ F x.val = fderiv ℝ G x.val

def zero_normalizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S}
    (ω : Field S 0) (σ : SingularSimplex S 0) (x : SmoothSingularData.Simplex 0),
    simplexIntegral S C ω σ =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S (σ.val x))) (ω (σ.val x))

/-- Integrability is still an unconditional conclusion for all smooth forms. -/
def integrabilityType : Prop :=
  ∀ {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : FormBundle C q)
    (ω : Form B) (σ : SingularSimplex S q),
    IntegrableOn (ambientPullbackCoefficient S C ω.field σ) (simplexSet q)


/-! Full analytic obligations. No support, interior-point or positive-dimension
hypothesis is imposed. Smoothness of face maps and postcomposition is part of
the existential conclusions, supplied by the smooth singular interfaces. -/

def differential_chartType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q : ℕ} (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hx : σ.val x ∈ c.source) (v : Euclidean q),
    C.tangent.fiberCoordinates.equiv c hc (σ.val x) hx
      (simplexDifferential S C σ x v) =
        fderivWithin ℝ (chartExpression S σ c) (simplexSet q) x.val v

def differential_independentType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q : ℕ} (A : CotangentBundle S)
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q),
    simplexDifferential S C σ x = simplexDifferential S A σ x

def coordinate_evaluationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ} (ω : Field S r) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q) (v : Fin r → Euclidean q),
    coordinatePullback (C := C) ω σ x.val v =
      evaluate (TangentSpace S (σ.val x)) r (ω (σ.val x))
        (fun i => simplexDifferential S C σ x (v i))

def determinant_normalizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ}
    (β : (p : M) → Fin r → Module.Dual ℝ (TangentSpace S p))
    (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q) (v : Fin r → Euclidean q),
    coordinatePullback (C := C) (fun p => exteriorPower.ιMulti ℝ r (β p)) σ x.val v =
      (Matrix.of (fun i j => β (σ.val x) i (simplexDifferential S C σ x (v j)))).det

def coefficient_identificationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q : ℕ} (ω : Field S q) (σ : SingularSimplex S q)
    (x : SmoothSingularData.Simplex q),
    coordinatePullback (C := C) ω σ x.val (LocalStokesData.frame q) =
      pullbackCoefficient S C ω σ x

def pullback_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ} (B : FormBundle C r)
    (ω : Field S r), IsForm B ω → ∀ σ : SingularSimplex S q,
    LocallySmoothOn (simplexSet q) (fun x => coordinatePullback (C := C) ω σ x.val)

def postcompositionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {m q r : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (A : CotangentBundle T)
    (σ : SingularSimplex S q) (f : M → N) (hf : MapData.IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∃ τ : SingularSimplex T q, τ.val = f ∘ σ.val ∧
      ∀ ω : Field T r,
        coordinatePullback (C := C) (FormPullbackData.pullbackField S T f L ω) σ =
          coordinatePullback (C := A) ω τ

def ordered_facesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ} (σ : SingularSimplex S (q+1)) (j : Fin (q+2)),
    ∃ τ : SingularSimplex S q, τ.val = σ.val ∘ face j ∧
      ∀ (ω : Field S r) (x : SmoothSingularData.Simplex q),
        coordinatePullback (C := C) ω τ x.val =
          (coordinatePullback (C := C) ω σ (face j x).val).compContinuousLinearMap
            (fderiv ℝ (faceAmbient j) x.val)

def exterior_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ} (B : ∀ k, FormBundle C k)
    (K : DeRhamData.Calculus C B) (ω : Field S r), IsForm (B r) ω →
    ∀ (σ : SingularSimplex S q) (x : SmoothSingularData.Simplex q),
    extDerivWithin (coordinatePullback (C := C) ω σ) (simplexSet q) x.val =
      coordinatePullback (C := C) (K.D r ω) σ x.val

def integral_linearityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {q : ℕ} (B : FormBundle C q)
    (α β : Form B) (σ : SingularSimplex S q),
    (simplexIntegral S C (α.field + β.field) σ =
      simplexIntegral S C α.field σ + simplexIntegral S C β.field σ) ∧
    (∀ t : ℝ, simplexIntegral S C (t • α.field) σ =
      t • simplexIntegral S C α.field σ)

def integral_naturalityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {m q : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N) (A : CotangentBundle T)
    (σ : SingularSimplex S q) (f : M → N), MapData.IsSmoothMap S T f →
    ∀ L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
    (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
    ∃ τ : SingularSimplex T q, τ.val = f ∘ σ.val ∧
      ∀ ω : Field T q,
        simplexIntegral S C (FormPullbackData.pullbackField S T f L ω) σ =
          simplexIntegral T A ω τ

def targetChartType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → M → ModelChart n a M
noncomputable def targetChartValue : targetChartType := @targetChart

def chartExpressionType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → {q : ℕ} → SingularSimplex S q →
    ModelChart n a M → Euclidean q → Euclidean n
noncomputable def chartExpressionValue : chartExpressionType := @chartExpression

def simplexDifferentialType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → (C : CotangentBundle S) → {q : ℕ} →
    (σ : SingularSimplex S q) → (x : SmoothSingularData.Simplex q) →
      Euclidean q →ₗ[ℝ] TangentSpace S (σ.val x)
noncomputable def simplexDifferentialValue : simplexDifferentialType := @simplexDifferential

def pullbackCoefficientType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → (C : CotangentBundle S) → {q : ℕ} →
    Field S q → SingularSimplex S q → SmoothSingularData.Simplex q → ℝ
noncomputable def pullbackCoefficientValue : pullbackCoefficientType := @pullbackCoefficient

def ambientPullbackCoefficientType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → (C : CotangentBundle S) → {q : ℕ} →
    Field S q → SingularSimplex S q → Euclidean q → ℝ
noncomputable def ambientPullbackCoefficientValue : ambientPullbackCoefficientType := @ambientPullbackCoefficient

def simplexIntegralType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  (S : SmoothManifold n a M) → (C : CotangentBundle S) → {q : ℕ} →
    Field S q → SingularSimplex S q → ℝ
noncomputable def simplexIntegralValue : simplexIntegralType := @simplexIntegral

def simplexPullbackType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ},
    Field S r → SingularSimplex S q → SmoothSingularData.Simplex q →
      (Euclidean q) [⋀^Fin r]→ₗ[ℝ] ℝ
noncomputable def simplexPullbackValue : simplexPullbackType := @simplexPullback

def coordinatePullbackType := ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {q r : ℕ},
    Field S r → SingularSimplex S q → LocalStokesData.CoordinateForm q r
noncomputable def coordinatePullbackValue : coordinatePullbackType := @coordinatePullback

end Specs.SmoothManifolds.Comparison.SimplexPullbackIntegral
