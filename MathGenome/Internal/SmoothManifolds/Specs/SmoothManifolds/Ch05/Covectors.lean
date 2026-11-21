import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames

/-! Independent interface for paper.tex 1317--1327 (M05.06).

All covectors are linear functionals on the shared intrinsic derivation fibers.
Smooth one-forms are actual smooth sections of an arbitrary realization of T*M.
Differentials of maps are kept explicit, as in the upstream tangent interface;
their existence is a conclusion below, not an additional assumption on a map.
Every model kind and dimension is allowed, including boundary and dimension zero.
-/
set_option autoImplicit false

namespace SmoothManifolds.CovectorData
open ModelData AtlasData MapData PartitionData TangentData TangentBundleData
  DifferentialData BundleData BundleOperationsData FrameData Set Filter
open scoped Topology
universe u

section Base
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

abbrev CovectorField (S : SmoothManifold n a M) := (p : M) → CotangentFiber S p

/-- Expose the dual bundle with the topology on its original tangent fibers. -/
def cotangentSpace {S : SmoothManifold n a M} (C : CotangentBundle S) :
    BundleSpace S n (TangentIndex S) (CotangentFiber S) :=
  letI := C.realization.space.topology
  C.dual.space

/-- Smoothness is tested on the section into the actual cotangent total space. -/
def IsOneForm {S : SmoothManifold n a M} (C : CotangentBundle S)
    (α : CovectorField S) : Prop :=
  letI := (cotangentSpace C).topology
  IsSmoothMap S (cotangentSpace C).bundle.totalManifold
    (fun p => (⟨p, α p⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))

structure OneForm {S : SmoothManifold n a M} (C : CotangentBundle S) where
  field : CovectorField S
  smooth : IsOneForm C field

/-- Evaluation on a smooth germ is the intrinsic differential of that germ. -/
def germDifferential (S : SmoothManifold n a M) (p : M) (g : SmoothGerm S p) :
    CotangentFiber S p where
  toFun v := v.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A globally smooth function supplies a smooth germ at every point. -/
def functionGerm (S : SmoothManifold n a M) (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) (p : M) : SmoothGerm S p :=
  ⟨Germ.ofFun u, Algebra.subset_adjoin ⟨u, hu p, rfl⟩⟩

def dFunction (S : SmoothManifold n a M) (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u) : CovectorField S :=
  fun p => germDifferential S p (functionGerm S u hu p)

/-- The coordinate vector and covector use the original tangent chart. -/
noncomputable def coordinateVector {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) : TangentSpace S p :=
  (K.equiv c hc p hp).symm (Pi.single j 1)

noncomputable def coordinateCovector {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) : CotangentFiber S p :=
  (LinearMap.proj j).comp (K.equiv c hc p hp).toLinearMap

end Base

section Maps
variable {n m : ℕ} {a b : ModelKind} {M P : Type u}
  [TopologicalSpace M] [TopologicalSpace P]

/-- This is restriction over points, retaining the *ambient* covector fibers. -/
def ambientRestriction (S : SmoothManifold n a M) (f : P → M)
    (α : CovectorField S) : (p : P) → CotangentFiber S (f p) := fun p => α (f p)

/-- Pullback as a form additionally precomposes with the tangent differential. -/
def pullbackField (T : SmoothManifold m b P) (S : SmoothManifold n a M) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (α : CovectorField S) : CovectorField T := fun p => (α (f p)).comp (L p)

end Maps
end SmoothManifolds.CovectorData

namespace Specs.SmoothManifolds.Ch05.Covectors
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.PartitionData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.FrameData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.CovectorData Set Filter
open scoped Topology
universe u

/-- The dx^j are smooth local sections, form a basis, evaluate as the Kronecker
symbol on coordinate vectors, and are the differentials of coordinate germs. -/
def coordinate_dual_frameType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    letI := (cotangentSpace C).topology
    ∃ b : LocalFrame (cotangentSpace C).bundle c.source c.open_source,
      (∀ j p, b.section_ j p = coordinateCovector C.tangent.fiberCoordinates c hc p.val p.property j) ∧
      (∀ p (hp : p ∈ c.source) (j k : Fin n),
        coordinateCovector C.tangent.fiberCoordinates c hc p hp j
          (coordinateVector C.tangent.fiberCoordinates c hc p hp k) = if k = j then 1 else 0) ∧
      ∀ p (hp : p ∈ c.source) (j : Fin n) (g : SmoothGerm S p),
        g.val = Germ.ofFun (fun y => (c y).val j) →
        germDifferential S p g = coordinateCovector C.tangent.fiberCoordinates c hc p hp j

/-- A smooth function's germ differential is a smooth cotangent section. -/
def differential_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u), IsOneForm C (dFunction S u hu)

/-- Partial derivatives use any actual ambient extension of the function germ.
The finite sum includes the empty expansion in dimension zero. -/
def differential_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (u : M → ℝ)
    (hu : ScalarSmooth S.smoothStructure.val u)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (F : Euclidean n → ℝ),
    GermChartExtension S p c (functionGerm S u hu p) F →
      (∀ j : Fin n, dFunction S u hu p
        (coordinateVector C.tangent.fiberCoordinates c hc p hp j) =
          fderiv ℝ F (c p).val (Pi.single j 1)) ∧
      dFunction S u hu p = ∑ j : Fin n,
        (fderiv ℝ F (c p).val (Pi.single j 1)) •
          coordinateCovector C.tangent.fiberCoordinates c hc p hp j

/-- No differential family is assumed for existence of the pullback. -/
def pullback_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : P → M),
    IsSmoothMap T S f → ∀ α : OneForm C,
      ∃ L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p),
        (∀ p, IsDifferential T S f p (L p)) ∧
        IsOneForm D (pullbackField T S f L α.field)

/-- Smoothness for every representative of the genuine differential. -/
def pullback_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : P → M),
    IsSmoothMap T S f →
    ∀ (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p)),
      (∀ p, IsDifferential T S f p (L p)) → ∀ α : CovectorField S,
        IsOneForm C α → IsOneForm D (pullbackField T S f L α)

/-- The defining evaluation formula, on the original full tangent fibers. -/
def pullback_applyType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
    (α : CovectorField S) (p : P) (v : TangentSpace T p),
    pullbackField T S f L α p v = α (f p) (L p v)

def pullback_differentialType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P) (f : P → M),
    IsSmoothMap T S f →
    ∀ (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p)),
      (∀ p, IsDifferential T S f p (L p)) → ∀ (u : M → ℝ)
      (hu : ScalarSmooth S.smoothStructure.val u),
      ∃ huf : ScalarSmooth T.smoothStructure.val (u ∘ f),
        dFunction T (u ∘ f) huf = pullbackField T S f L (dFunction S u hu)

def pullback_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    (∀ p, IsDifferential S S id p (L p)) → ∀ α : CovectorField S,
      pullbackField S S id L α = α

def pullback_compType : Prop :=
  ∀ {n m k : ℕ} {a b c : ModelKind} {M P Q : Type u}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (U : SmoothManifold k c Q) (f : P → M) (g : Q → P),
    IsSmoothMap T S f → IsSmoothMap U T g →
    ∀ (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (f p))
      (K : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace T (g q))
      (H : (q : Q) → TangentSpace U q →ₗ[ℝ] TangentSpace S (f (g q))),
      (∀ p, IsDifferential T S f p (L p)) →
      (∀ q, IsDifferential U T g q (K q)) →
      (∀ q, IsDifferential U S (f ∘ g) q (H q)) → ∀ α : CovectorField S,
      pullbackField U S (f ∘ g) H α =
        pullbackField U T g K (pullbackField T S f L α)

/-- Restriction as a one-form is pullback by the embedding. The right-hand
side first restricts over points, retaining ambient covectors, then precomposes
with di. These have different fiber types. No neatness or interior assumption
is made, including when either manifold has ordinary boundary. -/
def restrictionType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (D : CotangentBundle T) (i : P → M),
    IsSmoothEmbedding T S i →
    ∀ (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (i p)),
      (∀ p, IsDifferential T S i p (L p)) → ∀ α : CovectorField S,
      IsOneForm C α →
      IsOneForm D (pullbackField T S i L α) ∧
        ∀ p, pullbackField T S i L α p = (ambientRestriction S i α p).comp (L p)

/-- The zero-dimensional case has no nonzero covectors. -/
def zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (α : CovectorField S) (p : M), α p = 0

end Specs.SmoothManifolds.Ch05.Covectors
