import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.VectorFieldDerivations
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.FiniteRegularity
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.Matrix.Normed

/-! Independent statements for M06.02. All sections use the intrinsic germ
fibers, without any tangency restriction at the boundary. The bracket operation
is characterized by its action on functions. Algebraic identities are stated
pointwise, so they do not depend on a choice of instances on smooth sections. -/
namespace SmoothManifolds.LieBracketData
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData VectorFieldData FiniteRegularityData Set Filter
open scoped Topology Matrix.Norms.Elementwise
universe u

/-- A bracket on actual smooth sections, characterized on every represented
pair of derivations. Existence of these representatives is a separate theorem,
not a hypothesis on an individual field. -/
def BracketOperation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (b : SmoothField B → SmoothField B → SmoothField B) : Prop :=
  ∀ (X Y : SmoothField B) (D E : RealDerivation S),
    Represents X D → Represents Y E → Represents (b X Y) ⁅D, E⁆

/-- Total coordinate functions; the zero outside the chart is irrelevant to
any assertion at a point in its open source. -/
noncomputable def coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : Section S) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) : Euclidean n := by
  classical
  exact if hp : p ∈ e.source then B.fiberCoordinates.equiv e he p hp (X p) else 0

/-- C^r regularity of a section on the given smooth manifold. At a boundary
point the extension is to an ambient Euclidean open set. -/
def FieldRegular {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (B : TangentBundleStructure S) (r : ℕ∞)
    (X : Section S) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
    LocalCoordinateExtension r (fun y => (e y).val) (coefficients B X e he) p

/-- The local coordinate commutator. Its derivative arguments are actual
ambient derivatives in the shared coordinate-derivative model. -/
def HasBracketCoefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X Y Z : Section S) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
    ∀ (L K : Euclidean n →L[ℝ] Euclidean n),
      HasCoordinateDerivative e (coefficients B X e he) p L →
      HasCoordinateDerivative e (coefficients B Y e he) p K →
      ∀ j, coefficients B Z e he p j = ∑ i,
        (coefficients B X e he p i * K (Pi.single i 1) j -
          coefficients B Y e he p i * L (Pi.single i 1) j)

/-- Ordinary finite-dimensional real Lie-group data in the project's charts.
Only multiplication and inversion are assumed smooth. No field or tangent
classification theorem is a field of this structure. -/
structure LieGroupStructure {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    (S : SmoothManifold n .euclidean G) where
  productCoordinates : ProductData.ProductCoordinates n .euclidean n .euclidean .euclidean
  productManifold : SmoothManifold (n + n) .euclidean (G × G)
  productAtlas : productManifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (ProductData.productAtlas productCoordinates S.smoothStructure.val S.smoothStructure.val)
  multiplication_smooth : IsSmoothMap productManifold S (fun z => z.1 * z.2)
  inversion_smooth : IsSmoothMap S S (fun g => g⁻¹)

/-- The usual left-invariance equation, for the actual intrinsic differential.
Smoothness of the left translations and existence of these differentials are
proved from LieGroupStructure. -/
def IsLeftInvariant {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} {B : TangentBundleStructure S}
    (X : SmoothField B) : Prop :=
  ∀ (g p : G) (L : TangentSpace S p →ₗ[ℝ] TangentSpace S (g * p)),
    IsDifferential S S (fun q => g * q) p L → L (X.val p) = X.val (g * p)

abbrev LeftInvariantField {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (B : TangentBundleStructure S) :=
  {X : SmoothField B // IsLeftInvariant X}

/-- Evaluation at the identity is the inverse of this equivalence. The sigma
identity records the formula d(L_g)_e v without identifying dependent fibers
by an unstated cast. -/
def LeftInvariantEquivalence {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} {B : TangentBundleStructure S}
    (e : TangentSpace S (1 : G) ≃ LeftInvariantField B) : Prop :=
  (∀ X : LeftInvariantField B, e.symm X = X.val.val 1) ∧
  ∀ (v : TangentSpace S (1 : G)) (g : G)
    (L : TangentSpace S (1 : G) →ₗ[ℝ] TangentSpace S (g * 1)),
    IsDifferential S S (fun q => g * q) 1 L →
      (⟨g, (e v).val.val g⟩ : TotalSpace S) = ⟨g * 1, L v⟩

/-- GL_d(R), as the actual open locus of invertible real square matrices.
Its topology is the subspace topology of the finite matrix space. -/
abbrev OpenMatrixGroup (d : ℕ) := {g : Matrix (Fin d) (Fin d) ℝ // IsUnit g}

def matrixLeft {d : ℕ} (g p : OpenMatrixGroup d) : OpenMatrixGroup d :=
  ⟨g.val * p.val, g.property.mul p.property⟩

/-- A realization of the standard open-matrix-group manifold. The full chart
is the matrix inclusion followed by an actual linear coordinate identification.
Existence, rather than this definition, supplies these data. -/
structure MatrixGroupModel (d : ℕ) (P : Type u) [TopologicalSpace P] where
  points : P ≃ₜ OpenMatrixGroup d
  coordinates : Matrix (Fin d) (Fin d) ℝ ≃L[ℝ] Euclidean (d * d)
  manifold : SmoothManifold (d * d) .euclidean P
  bundle : TangentBundleStructure manifold
  chart : ModelChart (d * d) .euclidean P
  chart_mem : chart ∈ manifold.smoothStructure.val
  full_source : chart.source = univ
  chart_apply : ∀ g, (chart g).val = coordinates (points g).val

def matrixLeftOn {d : ℕ} {P : Type u} [TopologicalSpace P]
    (A : MatrixGroupModel d P) (g p : P) : P :=
  A.points.symm (matrixLeft (A.points g) (A.points p))

def MatrixField {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P) (v : Matrix (Fin d) (Fin d) ℝ)
    (X : SmoothField A.bundle) : Prop :=
  ∀ g, coefficients A.bundle X.val A.chart A.chart_mem g = A.coordinates ((A.points g).val * v)

end SmoothManifolds.LieBracketData

namespace Specs.SmoothManifolds.Ch06.LieBracket
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.PartitionData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.FiniteRegularityData
  _root_.SmoothManifolds.LieBracketData Set Filter
open scoped Topology Matrix.Norms.Elementwise
universe u

/-- The commutator defines one and only one operation on smooth fields. -/
def bracket_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    ∃! b : SmoothField B → SmoothField B → SmoothField B, BracketOperation b

/-- Closure under addition and multiplication by smooth functions, followed
by bilinearity, antisymmetry, Jacobi, and the smooth-function Leibniz rule.
The fields W in the identities are arbitrary smooth realizations of the
indicated pointwise combinations; the first two conclusions supply them. -/
def bracket_algebraType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S),
    (∀ X Y : SmoothField B, ∃ W : SmoothField B, ∀ p, W.val p = X.val p + Y.val p) ∧
    (∀ (h : GlobalSmooth S) (X : SmoothField B),
      ∃ W : SmoothField B, ∀ p, W.val p = h.val p • X.val p) ∧
    ∀ b : SmoothField B → SmoothField B → SmoothField B, BracketOperation b →
      (∀ X Y : SmoothField B, ∀ p, (b X Y).val p = -(b Y X).val p) ∧
      (∀ X Y Z : SmoothField B, ∀ p,
        (b X (b Y Z)).val p + (b Y (b Z X)).val p + (b Z (b X Y)).val p = 0) ∧
      (∀ X Y Z W : SmoothField B, (∀ p, W.val p = X.val p + Y.val p) →
        ∀ p, (b W Z).val p = (b X Z).val p + (b Y Z).val p) ∧
      (∀ X Y Z W : SmoothField B, (∀ p, W.val p = Y.val p + Z.val p) →
        ∀ p, (b X W).val p = (b X Y).val p + (b X Z).val p) ∧
      (∀ (r : ℝ) (X Y W : SmoothField B), (∀ p, W.val p = r • X.val p) →
        ∀ p, (b W Y).val p = r • (b X Y).val p) ∧
      (∀ (r : ℝ) (X Y W : SmoothField B), (∀ p, W.val p = r • Y.val p) →
        ∀ p, (b X W).val p = r • (b X Y).val p) ∧
      (∀ (h : GlobalSmooth S) (X Y W : SmoothField B) (D : RealDerivation S),
        Represents X D → (∀ p, W.val p = h.val p • Y.val p) →
        ∀ p, (b X W).val p = h.val p • (b X Y).val p + (D h).val p • Y.val p)

/-- The coordinate formula, using every valid ambient derivative, with existence
of the derivatives made explicit. Includes zero dimension and boundary points. -/
def bracket_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ X Y : SmoothField B,
      (∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
        ∃ L K : Euclidean n →L[ℝ] Euclidean n,
          HasCoordinateDerivative e (coefficients B X.val e he) p L ∧
          HasCoordinateDerivative e (coefficients B Y.val e he) p K) ∧
      HasBracketCoefficients B X.val Y.val (b X Y).val

/-- Related fields under every smooth map have related brackets; no local
invertibility or projectability assumption is added. -/
def bracket_relatedType : Prop :=
  ∀ {n m : ℕ} {a c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m c N)
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (b : SmoothField B → SmoothField B → SmoothField B)
    (d : SmoothField C → SmoothField C → SmoothField C),
    BracketOperation b → BracketOperation d →
    ∀ f : M → N, IsSmoothMap S T f →
    ∀ L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
      (∀ p, IsDifferential S T f p (L p)) →
    ∀ (X Y : SmoothField B) (X' Y' : SmoothField C),
      (∀ p, L p (X.val p) = X'.val (f p)) →
      (∀ p, L p (Y.val p) = Y'.val (f p)) →
      ∀ p, L p ((b X Y).val p) = (d X' Y').val (f p)

/-- The coordinate commutator of C^r inputs glues to a unique C^(r-1)
section, also at an ordinary boundary. It does not assert smoothness when the
inputs have only finite regularity. -/
def bracket_finiteRegularityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (r : ℕ), 1 ≤ r →
    ∀ X Y : Section S, FieldRegular B r X → FieldRegular B r Y →
      ∃! Z : Section S,
        FieldRegular B (r - 1 : ℕ) Z ∧ HasBracketCoefficients B X Y Z

/-- Every vector at e extends to precisely one smooth left-invariant field,
for every finite-dimensional real Lie group, without connectedness or a matrix
realization assumption. -/
def leftInvariant_correspondenceType : Prop :=
  ∀ {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    (S : SmoothManifold n .euclidean G) (B : TangentBundleStructure S),
    LieGroupStructure S →
      ∃ e : TangentSpace S (1 : G) ≃ LeftInvariantField B, LeftInvariantEquivalence e

/-- Left translations preserve brackets. Evaluation at e therefore induces
an operation on T_eG whose associated invariant field is the field bracket. -/
def leftInvariant_bracketType : Prop :=
  ∀ {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    (S : SmoothManifold n .euclidean G) (B : TangentBundleStructure S),
    LieGroupStructure S →
    ∀ b : SmoothField B → SmoothField B → SmoothField B, BracketOperation b →
      (∀ X Y : LeftInvariantField B, IsLeftInvariant (b X.val Y.val)) ∧
      ∀ e : TangentSpace S (1 : G) ≃ LeftInvariantField B, LeftInvariantEquivalence e →
        ∃ β : TangentSpace S (1 : G) → TangentSpace S (1 : G) → TangentSpace S (1 : G),
          ∀ v w, β v w = (b (e v).val (e w).val).val 1 ∧
            (e (β v w)).val = b (e v).val (e w).val

/-- The matrix example uses the standard open invertible locus, not an
unrelated abstract manifold assumed to have the desired fields. -/
def matrix_model_existsType : Prop := ∀ d : ℕ, Nonempty (MatrixGroupModel d (OpenMatrixGroup d))

/-- On GL_d(R), X_v(g)=gv is an actual smooth left-invariant field, and the
intrinsic field bracket has matrix value g(vw-wv). The full chart identifies
each tangent fiber with matrix space; at the identity it identifies v with v. -/
def matrix_fieldsType : Prop :=
  ∀ {P : Type u} [TopologicalSpace P] (d : ℕ) (A : MatrixGroupModel d P)
    (b : SmoothField A.bundle → SmoothField A.bundle → SmoothField A.bundle),
    BracketOperation b →
      (∀ v : Matrix (Fin d) (Fin d) ℝ, ∃! X : SmoothField A.bundle, MatrixField A v X) ∧
      (∀ (v : Matrix (Fin d) (Fin d) ℝ) (X : SmoothField A.bundle), MatrixField A v X →
        ∀ (g p : P)
          (L : TangentSpace A.manifold p →ₗ[ℝ] TangentSpace A.manifold (matrixLeftOn A g p)),
          IsDifferential A.manifold A.manifold (matrixLeftOn A g) p L →
            L (X.val p) = X.val (matrixLeftOn A g p)) ∧
      (∀ (v w : Matrix (Fin d) (Fin d) ℝ) (X Y : SmoothField A.bundle),
        MatrixField A v X → MatrixField A w Y → ∀ g,
          coefficients A.bundle (b X Y).val A.chart A.chart_mem g =
            A.coordinates ((A.points g).val * (v * w - w * v)))

end Specs.SmoothManifolds.Ch06.LieBracket
