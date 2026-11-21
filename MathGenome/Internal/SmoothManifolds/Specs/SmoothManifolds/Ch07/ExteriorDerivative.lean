import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.FormPullback
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-! Independent statements for M07.03 (paper.tex 1489–1530).
Full global existence, uniqueness, coordinate compatibility and naturality
are stated on the original intrinsic exterior sections.
No candidate proof is imported here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.ExteriorDerivativeData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  CovectorData ExteriorData Set
universe u

/-- The coordinate coefficient, extended by zero off the chart image. It is
only differentiated *within* that image, so this creates no artificial edge. -/
def ambientCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (I : Index n k) (z : Euclidean n) : ℝ := by
  classical
  exact if hz : z ∈ modelSet n a then
    if ht : (⟨z, hz⟩ : ModelSpace n a) ∈ c.target then
      coefficients C k c hc ω ⟨c.symm ⟨z, hz⟩, c.map_target ht⟩ I
    else 0
  else 0

/-- Synthesis of ∑_(I,j) A_I(e_j) dx^j ∧ dx^I in the original
homogeneous exterior fibers, with determinant normalization. -/
def coordinateExpression {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    Fiber (TangentSpace S p) (k+1) :=
  Eq.ndrec (motive := fun d => ExteriorData.Fiber (TangentSpace S p) d)
    (∑ I : Index n k, ∑ j : Fin n, (A I (Pi.single j 1)) •
      ExteriorData.wedge (V := TangentSpace S p) (k := 1) (l := k)
        ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (coordinateCovector C.tangent.fiberCoordinates c hc p hp j))
        (exteriorPower.ιMulti ℝ k (fun i =>
          coordinateCovector C.tangent.fiberCoordinates c hc p hp
            (Set.powersetCard.ofFinEmbEquiv.symm I i)))) (Nat.add_comm 1 k)

/-- The literal coordinate derivative, using derivatives within the chart image. -/
def coordinateDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : M) (hp : p ∈ c.source) : Fiber (TangentSpace S p) (k+1) :=
  coordinateExpression C k c hc p hp (fun I =>
    fderivWithin ℝ (ambientCoefficient C k c hc ω I) (Subtype.val '' c.target) (c p).val)

/-- Coordinate characterization of d, without assuming a global operator.
The C¹ existence and overlap compatibility theorem is a separate obligation. -/
def HasExteriorDerivative {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) {k : ℕ}
    (ω : Field S k) (η : Field S (k+1)) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source),
    η p = coordinateDerivative C k c hc ω p hp

/-- C^r coefficients in every smooth chart, with the specified ambient-extension
convention. The finite coefficient vector includes the empty index set at k=0. -/
def IsRegularField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (r : ℕ∞) (k : ℕ)
    (ω : Field S k) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    LocallyContDiffAlong r (fun p : c.source => (c p.val).val)
      (fun p => fun I : Index n k => coefficients C k c hc ω p I)

def IsContinuousField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (ω : Field S k) : Prop :=
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
    Continuous (fun p : c.source => coefficients C k c hc ω p I)

/-- The three characterizing axioms and real linearity on smooth fields.
This is a predicate on a proposed operator, not assumed manifold data.
The family may be arbitrarily defined on nonsmooth fields; its uniqueness below
is asserted exactly on Ω^k, the smooth fields. Exterior-algebra coercions express
the Leibniz rule without inessential arithmetic casts between homogeneous degrees. -/
structure DerivativeAxioms {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D : ∀ k, Field S k → Field S (k+1)) : Prop where
  smooth : ∀ k ω, IsForm (B k) ω → IsForm (B (k+1)) (D k ω)
  add : ∀ k α β, IsForm (B k) α → IsForm (B k) β → D k (α+β) = D k α + D k β
  smul : ∀ k (r : ℝ) α, IsForm (B k) α → D k (r • α) = r • D k α
  function_rule : ∀ (f : M → ℝ) (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) p,
    D 0 (FormPullbackData.scalarField S f) p =
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (dFunction S f hf p)
  square : ∀ k ω, IsForm (B k) ω → D (k+1) (D k ω) = 0
  leibniz : ∀ k l α β, IsForm (B k) α → IsForm (B l) β → ∀ p,
    (D (k+l) (fieldWedge α β) p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      (ExteriorData.wedge (V := TangentSpace S p) (k := k+1) (l := l) (D k α p) (β p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) +
      (-1 : ℝ)^k • (ExteriorData.wedge (V := TangentSpace S p) (k := k) (l := l+1) (α p) (D l β p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p)))

end SmoothManifolds.ExteriorDerivativeData

namespace Specs.SmoothManifolds.Ch07.ExteriorDerivative
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.FormPullbackData
  _root_.SmoothManifolds.ExteriorDerivativeData
  Set Filter
open scoped Topology
universe u

/-- This holds for every field, hence in particular for continuous forms.
There is no differentiability assumption on the family of linear fiber maps. -/
def pullback_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    Continuous f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (k : ℕ) (ω : Field T k),
      sectionSupport (FormPullbackData.pullbackField S T f L ω) ⊆
        f ⁻¹' sectionSupport ω

/-- The support is the closure in the source base, also for dependent fibers. -/
def proper_pullback_compact_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    IsProperMap f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (k : ℕ) (ω : Field T k), IsCompact (sectionSupport ω) →
      IsCompact (sectionSupport (FormPullbackData.pullbackField S T f L ω))

/-- A closed embedded smooth face is a special case of a closed embedding.
This topological statement needs no smoothness or dimension hypothesis. -/
def closed_embedding_properType : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (i : X → Y),
    Topology.IsClosedEmbedding i → IsProperMap i

def closed_face_inclusion_properType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X), IsClosed A →
    IsProperMap (Subtype.val : A → X)

/-- Analytic extension independence on any unique-differentiability domain.
The ambient extensions only need to be differentiable at the point. -/
def extension_independenceType : Prop :=
  ∀ (n k : ℕ) (s : Set (Euclidean n)), UniqueDiffOn ℝ s →
    ∀ (x : Euclidean n), x ∈ s →
    ∀ (ω η : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      DifferentiableAt ℝ ω x → DifferentiableAt ℝ η x →
      ω =ᶠ[𝓝[s] x] η → extDeriv ω x = extDeriv η x

/-- The elementary corner model uses exactly the shared first-k convention. -/
def uniqueDiffOn_orthantType : Prop :=
  ∀ (n : ℕ) (c : Fin (n+1)), UniqueDiffOn ℝ (orthantSet n c)

/-- Any pair of C¹ extensions on a relative open corner domain gives the same d. -/
def orthant_extension_independenceType : Prop :=
  ∀ (n k : ℕ) (c : Fin (n+1)) (s : Set (Orthant n c)), IsOpen s →
    ∀ (U V : Set (Euclidean n)), IsOpen U → IsOpen V →
    ∀ (ω η : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      ContDiffOn ℝ 1 ω U → ContDiffOn ℝ 1 η V →
      (∀ y ∈ s, y.val ∈ U → y.val ∈ V → ω y.val = η y.val) →
      ∀ x ∈ s, x.val ∈ U → x.val ∈ V → extDeriv ω x.val = extDeriv η x.val

/-- The same independence in every ordinary manifold model, including n=0. -/
def model_extension_independenceType : Prop :=
  ∀ (n k : ℕ) (a : ModelKind) (s : Set (ModelSpace n a)), IsOpen s →
    ∀ (U V : Set (Euclidean n)), IsOpen U → IsOpen V →
    ∀ (ω η : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      ContDiffOn ℝ 1 ω U → ContDiffOn ℝ 1 η V →
      (∀ y ∈ s, y.val ∈ U → y.val ∈ V → ω y.val = η y.val) →
      ∀ x ∈ s, x.val ∈ U → x.val ∈ V → extDeriv ω x.val = extDeriv η x.val

/-- At a point where the input is C¹, the local exterior derivative is continuous. -/
def ambient_derivative_continuousType : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclidean n)), IsOpen U →
    ∀ (ω : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      ContDiffOn ℝ 1 ω U → ContinuousOn (extDeriv ω) U

/-- The analytic d squares to zero for C² extensions, with the manuscript's normalization. -/
def ambient_derivative_squareType : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclidean n)), IsOpen U →
    ∀ (ω : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      ContDiffOn ℝ 2 ω U → ∀ x ∈ U, extDeriv (extDeriv ω) x = 0

/-- Naturality needs only first derivatives of the form coefficients; the map is smooth.
The extensions may take values outside the original target model. -/
def ambient_naturalityType : Prop :=
  ∀ (n m k : ℕ) (U : Set (Euclidean n)) (V : Set (Euclidean m)),
    IsOpen U → IsOpen V →
    ∀ (ω : Euclidean m → (Euclidean m) [⋀^Fin k]→L[ℝ] ℝ)
      (f : Euclidean n → Euclidean m),
      ContDiffOn ℝ 1 ω V → ContDiffOn ℝ (⊤ : ℕ∞) f U → MapsTo f U V →
      ∀ x ∈ U,
        extDeriv (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) x =
          (extDeriv ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

/-- The derivative vanishes in dimension zero in every degree. -/
def ambient_dimension_zeroType : Prop :=
  ∀ (k : ℕ) (ω : Euclidean 0 → (Euclidean 0) [⋀^Fin k]→L[ℝ] ℝ)
    (x : Euclidean 0), extDeriv ω x = 0

/-- Equality of germs of input fields implies equality of their coordinate d's. -/
def coordinate_localityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω η : Field S k) (p : M) (hp : p ∈ c.source),
    (∀ᶠ q in 𝓝 p, ω q = η q) →
      coordinateDerivative C k c hc ω p hp = coordinateDerivative C k c hc η p hp

/-- The coordinate formula determines a derivative uniquely, if one exists. -/
def derivative_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η ζ : Field S (k+1)),
    HasExteriorDerivative C ω η → HasExteriorDerivative C ω ζ → η = ζ

/-- Locality for fields satisfying the coordinate characterization. -/
def derivative_localityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω α : Field S k) (η β : Field S (k+1)),
    HasExteriorDerivative C ω η → HasExteriorDerivative C α β →
    ∀ p, (∀ᶠ q in 𝓝 p, ω q = α q) → η p = β p

/-- Support control follows from the coordinate formula. Existence is not assumed
as a property of the manifold; it remains a theorem to be established. -/
def derivative_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)),
    HasExteriorDerivative C ω η → sectionSupport η ⊆ sectionSupport ω

/-- Every actual C¹ coefficient extension computes the same intrinsic sum.
Together with overlap compatibility, this is formula (7.3). -/
def coordinate_formula_extensionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (F : Index n k → Euclidean n → ℝ),
    IsOpen U → (c p).val ∈ U → (∀ I, ContDiffOn ℝ 1 (F I) U) →
    (∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F I z.val = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I) →
    coordinateDerivative C k c hc ω p hp =
      coordinateExpression C k c hc p hp (fun I => fderiv ℝ (F I) (c p).val)

def zero_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ),
    HasExteriorDerivative C (0 : Field S k) 0

def zero_dim_derivativeType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (C : CotangentBundle S) (k : ℕ) (ω : Field S k),
    HasExteriorDerivative C ω 0

def derivative_compact_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)), HasExteriorDerivative C ω η →
    IsCompact (sectionSupport ω) → IsCompact (sectionSupport η)

/-- Every C^r field, including r=0, is a continuous field. -/
def regular_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (r : ℕ∞) (ω : Field S k),
    IsRegularField C r k ω → IsContinuousField C k ω

/-- Real linearity on C¹ inputs, for the intrinsic derivative relation. -/
def derivative_addType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω α : Field S k) (η β : Field S (k+1)),
    IsRegularField C 1 k ω → IsRegularField C 1 k α →
    HasExteriorDerivative C ω η → HasExteriorDerivative C α β →
    HasExteriorDerivative C (ω+α) (η+β)

def derivative_smulType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r : ℝ) (ω : Field S k) (η : Field S (k+1)), IsRegularField C 1 k ω →
    HasExteriorDerivative C ω η → HasExteriorDerivative C (r • ω) (r • η)

/-- On smooth functions the coordinate derivative is the existing ordinary differential. -/
def function_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f),
    HasExteriorDerivative C (FormPullbackData.scalarField S f)
      (fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (dFunction S f hf p))

/-- Coefficient extensions lose exactly one requested order under d. The
coordinate relation is a hypothesis here; its existence is a separate target. -/
def derivative_regularType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r s : ℕ∞), r+1 ≤ s → ∀ (ω : Field S k) (η : Field S (k+1)),
    IsRegularField C s k ω → HasExteriorDerivative C ω η →
      IsRegularField C r (k+1) η

/-- Continuity of an existing intrinsic derivative of a C¹ field. -/
def c1_derivative_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)), IsRegularField C 1 k ω →
    HasExteriorDerivative C ω η → IsContinuousField C (k+1) η

/-- Smoothness follows from the coordinate formula on smooth input. -/
def derivative_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (E : FormBundle C (k+1))
    (ω : Field S k) (η : Field S (k+1)), IsForm B ω →
    HasExteriorDerivative C ω η → IsForm E η

/-- The smooth-section interface entails coefficient regularity at any order. -/
def smooth_regularType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (ω : Field S k) (r : ℕ∞),
    IsForm B ω → IsRegularField C r k ω

def axioms_zero_germType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k)
    (hω : IsForm (B k) ω) (p : M) (hz : ∀ᶠ q in 𝓝 p, ω q = 0), D k ω p = 0

def axioms_localityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (α β : Field S k)
    (hα : IsForm (B k) α) (hβ : IsForm (B k) β)
    (p : M) (heq : ∀ᶠ q in 𝓝 p, α q = β q), D k α p = D k β p

def axioms_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k)
    (hω : IsForm (B k) ω), sectionSupport (D k ω) ⊆ sectionSupport ω

def coefficient_alternating_bridgeType : Prop :=
  ∀ (n k : ℕ),
    ∃ e : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      (∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
        e a v = evaluate (Euclidean n) k
          (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v) ∧
      ∀ (f : Euclidean n → Index n k → ℝ) (x : Euclidean n),
        DifferentiableAt ℝ f x → ∀ v : Fin (k+1) → Euclidean n,
          extDeriv (fun y => e (f y)) x v =
            evaluate (Euclidean n) (k+1) (∑ I : Index n k,
              exteriorPower.ιMulti ℝ (k+1)
                (Fin.cons (fderiv ℝ (fun y => f y I) x).toLinearMap
                  (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
                    (Set.powersetCard.ofFinEmbEquiv.symm I j)))) v

def ambientDerivativeExpression (n k : ℕ) (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    ⋀[ℝ]^(k+1) (Euclidean n) :=
  Eq.ndrec (motive := fun d => ⋀[ℝ]^d (Euclidean n))
    (∑ I : Index n k, ∑ j : Fin n, (A I (Pi.single j 1)) •
      exteriorPower.wedge ℝ (Euclidean n) 1 k
        ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1))
        (exteriorPower.ιMulti ℝ k (fun i =>
          Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I i) 1))) (Nat.add_comm 1 k)

def ambientCoefficientBasis (n k : ℕ) := (Pi.basisFun ℝ (Fin n)).exteriorPower k

def ambientCoefficientSynthesis (n k : ℕ) (a : Index n k → ℝ) : ⋀[ℝ]^k (Euclidean n) :=
  (ambientCoefficientBasis n k).equivFun.symm a

def ambientCoefficientWedge (n k l : ℕ) :
    (Index n k → ℝ) →L[ℝ] (Index n l → ℝ) →L[ℝ] (Index n (k+l) → ℝ) :=
  let L := ((exteriorPower.wedge ℝ (Euclidean n) k l).compl₁₂
    (ambientCoefficientBasis n k).equivFun.symm.toLinearMap
    (ambientCoefficientBasis n l).equivFun.symm.toLinearMap).compr₂
    (ambientCoefficientBasis n (k+l)).equivFun.toLinearMap
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp L)


def ambient_coefficient_leibnizType : Prop :=
  ∀ {n k l : ℕ}
    (f : Euclidean n → Index n k → ℝ) (g : Euclidean n → Index n l → ℝ)
    (x : Euclidean n) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x),
    (ambientDerivativeExpression n (k+l)
      (fun I => fderiv ℝ (fun y => ambientCoefficientWedge n k l (f y) (g y) I) x) :
        ExteriorAlgebra ℝ (Euclidean n)) =
      (exteriorPower.wedge ℝ (Euclidean n) (k+1) l
        (ambientDerivativeExpression n k (fun I => fderiv ℝ (fun y => f y I) x))
        (ambientCoefficientSynthesis n l (g x)) : ExteriorAlgebra ℝ (Euclidean n)) +
      (-1 : ℝ)^k • (exteriorPower.wedge ℝ (Euclidean n) k (l+1)
        (ambientCoefficientSynthesis n k (f x))
        (ambientDerivativeExpression n l (fun I => fderiv ℝ (fun y => g y I) x)) :
          ExteriorAlgebra ℝ (Euclidean n))

def pullback_regularType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (k : ℕ) (r : ℕ∞) (ω : Field T k) (hω : IsRegularField A r k ω),
    IsRegularField C r k (FormPullbackData.pullbackField S T f L ω)

def intrinsic_derivative_squareType : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)) (ζ : Field S ((k+1)+1))
    (hω : IsRegularField C 2 k ω) (hη : HasExteriorDerivative C ω η)
    (hζ : HasExteriorDerivative C η ζ) , ζ = 0

def intrinsic_derivative_leibnizType : Prop :=
  ∀ {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k l : ℕ)
    (α : Field S k) (β : Field S l) (η : Field S (k+1)) (ζ : Field S (l+1))
    (θ : Field S ((k+l)+1))
    (hα : IsRegularField C 1 k α) (hβ : IsRegularField C 1 l β)
    (hη : HasExteriorDerivative C α η) (hζ : HasExteriorDerivative C β ζ)
    (hθ : HasExteriorDerivative C (fieldWedge α β) θ) (p : M) ,
    (θ p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      (wedge (V := TangentSpace S p) (η p) (β p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) +
      (-1 : ℝ)^k • (wedge (V := TangentSpace S p) (α p) (ζ p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p)))

def coordinate_derivative_pullbackType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (k : ℕ) (ω : Field T k) (hω : IsRegularField A 1 k ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) ,
    coordinateDerivative C k c hc (FormPullbackData.pullbackField S T f L ω) p hp =
      fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) (k+1) (L p) (coordinateDerivative A k d hd ω (f p) hfp)

def smooth_naturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (D : ∀ k, Field S k → Field S (k+1)) (J : ∀ k, Field T k → Field T (k+1))
    (hD : DerivativeAxioms C B D) (hJ : DerivativeAxioms A E J)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (k : ℕ) (ω : Field T k)
    (hω : IsForm (E k) ω) ,
    FormPullbackData.pullbackField S T f L (J k ω) =
      D k (FormPullbackData.pullbackField S T f L ω)

def c1_restrictionType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (i : M → N)
    (hi : MapClassData.IsSmoothEmbedding S T i)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (i p))
    (hL : ∀ p, IsDifferential S T i p (L p))
    (k : ℕ) (ω : Field T k) (η : Field T (k+1))
    (hω : IsRegularField A 1 k ω) (hη : HasExteriorDerivative A ω η) ,
    IsRegularField C 1 k (FormPullbackData.pullbackField S T i L ω) ∧
      HasExteriorDerivative C (FormPullbackData.pullbackField S T i L ω)
        (FormPullbackData.pullbackField S T i L η)

def axioms_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D E : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (hE : DerivativeAxioms C B E)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) , D k ω = E k ω

def orthant_extDerivWithin_pullbackType : Prop :=
  ∀ {n m k : ℕ}
    {c : Fin (n+1)} {d : Fin (m+1)}
    (s : Set (Orthant n c)) (t : Set (Orthant m d)) (hs : IsOpen s) (_ht : IsOpen t)
    (ω : Euclidean m → (Euclidean m) [⋀^Fin k]→L[ℝ] ℝ)
    (f : Euclidean n → Euclidean m)
    (hω : LocallyContDiffOn 1 (Subtype.val '' t : Set (Euclidean m)) (fun y => ω y.val))
    (hf : LocallyContDiffOn (⊤ : ℕ∞) (Subtype.val '' s : Set (Euclidean n)) (fun x => f x.val))
    (hmap : MapsTo f (Subtype.val '' s) (Subtype.val '' t))
    (x : Euclidean n) (hx : x ∈ (Subtype.val '' s : Set (Euclidean n))) ,
    extDerivWithin
      (fun y => (ω (f y)).compContinuousLinearMap
        (fderivWithin ℝ f (Subtype.val '' s) y)) (Subtype.val '' s) x =
      (extDerivWithin ω (Subtype.val '' t) (f x)).compContinuousLinearMap
        (fderivWithin ℝ f (Subtype.val '' s) x)

def continuous_field_section_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (ω : Field S k) ,
    IsContinuousField C k ω ↔
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    Continuous (fun p => (⟨p,ω p⟩ :
      Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k)))

def c1_derivative_section_continuousType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C (k+1)) (ω : Field S k) (η : Field S (k+1))
    (hω : IsRegularField C 1 k ω) (hη : HasExteriorDerivative C ω η) ,
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    Continuous (fun p => (⟨p,η p⟩ :
      Bundle.TotalSpace (Euclidean (n.choose (k+1))) (fun q => Fiber (TangentSpace S q) (k+1))))

/- Full global statements, with existence as a conclusion and no assumed
derivative family included in the manifold data. -/

/-- Existence and uniqueness on smooth forms under exactly the stated axioms. -/
def smooth_family_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k),
    ∃ D : ∀ k, Field S k → Field S (k+1), DerivativeAxioms C B D ∧
      ∀ E, DerivativeAxioms C B E → ∀ k ω, IsForm (B k) ω → D k ω = E k ω

/-- In dimension zero the zero family already gives the full characterization. -/
def zero_dim_family_existsType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k),
    ∃ D : ∀ k, Field S k → Field S (k+1), DerivativeAxioms C B D ∧
      ∀ E, DerivativeAxioms C B E → ∀ k ω, IsForm (B k) ω → D k ω = E k ω

def global_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D : ∀ k, Field S k → Field S (k+1)), DerivativeAxioms C B D →
    ∀ k ω, IsForm (B k) ω → HasExteriorDerivative C ω (D k ω)

/-- For C¹ forms, the intrinsic coordinate derivative exists and is continuous. -/
def c1_derivative_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (ω : Field S k),
    IsRegularField C 1 k ω →
      ∃ η : Field S (k+1), HasExteriorDerivative C ω η ∧ IsContinuousField C (k+1) η

/-- Smooth pullback preserves C¹ forms, and commutes with their derivative. -/
def c1_naturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N), IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, IsDifferential S T f p (L p)) →
      ∀ (k : ℕ) (ω : Field T k) (η : Field T (k+1)), IsRegularField A 1 k ω →
        HasExteriorDerivative A ω η →
        IsRegularField C 1 k (FormPullbackData.pullbackField S T f L ω) ∧
        HasExteriorDerivative C (FormPullbackData.pullbackField S T f L ω)
          (FormPullbackData.pullbackField S T f L η)

/-- Smooth forms have the same smooth coefficients as in the accepted Ω^k interface. -/
def smooth_coefficientsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (ω : Field S k),
    IsForm B ω ↔ IsRegularField C (⊤ : ℕ∞) k ω

/-- The cotangent identity is in the original total manifold and its intrinsic
exterior fibers. dp_i differentiates the actual induced momentum coordinate germ;
dx^i is pulled back along the genuine differential of π. It includes n=0. -/
def tautological_derivativeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S),
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∀ (A : CotangentBundle Q) (B : FormBundle A 2)
      (L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj),
      (∀ ξ, IsDifferential Q S Bundle.TotalSpace.proj ξ (L ξ)) →
      ∃ η : Field Q 2, IsForm B η ∧
        HasExteriorDerivative A
          (fun ξ => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ξ))).symm
            (tautologicalField C L ξ)) η ∧
        ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
          (ξ : CotangentTotal S) (hξ : ξ.proj ∈ c.source),
          ∃ g : Fin n → SmoothGerm Q ξ,
            (∀ j, (g j).val = Germ.ofFun (fun ζ : CotangentTotal S =>
              (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ζ).2 j)) ∧
            η ξ = ∑ j : Fin n,
              ExteriorData.wedge (V := TangentSpace Q ξ) (k := 1) (l := 1)
                ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ξ))).symm
                (germDifferential Q ξ (g j)))
                ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ξ))).symm
                  ((coordinateCovector C.tangent.fiberCoordinates c hc ξ.proj hξ j).comp (L ξ)))

end Specs.SmoothManifolds.Ch07.ExteriorDerivative
