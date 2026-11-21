import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Tensors
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BracketFromFlow

/-! Independent specification for M07.06 (paper.tex 1595--1608).

These definitions use the original intrinsic tangent fibers and their algebraic
mixed tensor products. Smoothness means locally smoothly extendible scalar
coordinate entries, including at the boundary. No connection is part of the
data. The construction, flow identification and algebra laws apply in every
dimension and variance, including the zero cases.
-/
set_option autoImplicit false

namespace SmoothManifolds.TensorLieData
open ModelData AtlasData MapData PartitionData TangentData TangentBundleData VectorFieldData
  DifferentialData TensorData LieBracketData FiniteRegularityData
open Set Filter
open scoped Topology
universe u

/-- A chart component is a linear functional on the actual algebraic tensor
fiber. Upper indices pair with the coordinate covectors, lower indices with the
coordinate vectors. Zero outside the chart only totalizes the representative. -/
noncomputable def component {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (r s : ℕ) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (I : Fin r → Fin n) (J : Fin s → Fin n) :
    Fiber (TangentSpace S p) r s →ₗ[ℝ] ℝ := by
  classical
  by_cases hp : p ∈ e.source
  · let c := B.fiberCoordinates.equiv e he p hp
    let args : (i : Fin r ⊕ Fin s) → Argument (TangentSpace S p) r s i :=
      Sum.rec (fun i => (LinearMap.proj (I i)).comp c.toLinearMap)
        (fun j => c.symm (Pi.single (J j) 1))
    exact
      { toFun := fun A => evaluate (TangentSpace S p) r s A args
        map_add' := by intro A C; simp only [map_add, add_apply]
        map_smul' := by intro z A; simp only [map_smul, smul_apply,
          RingHom.id_apply] }
  · exact 0

noncomputable def tensorCoefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    {r s : ℕ} (A : Field S r s) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (I : Fin r → Fin n) (J : Fin s → Fin n)
    (p : M) : ℝ := component B r s e he p I J (A p)

/-- Smoothness tested on all entries in every chart. ScalarContDiffAt is the
shared local ambient-extension convention; no interior-only smoothness is used. -/
def TensorSmooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    {r s : ℕ} (A : Field S r s) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
    ∀ (I : Fin r → Fin n) (J : Fin s → Fin n),
      ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (tensorCoefficients B A e he I J) p

structure SmoothTensor {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (r s : ℕ) where
  val : Field S r s
  smooth : TensorSmooth B val

/-- The canonical scalar tensor, using the two zeroth tensor powers. -/
noncomputable def scalarTensorField {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (f : M → ℝ) : Field S 0 0 :=
  fun p => f p • TensorData.pure Fin.elim0 Fin.elim0

/-- A vector field as a tensor with one upper slot and no lower slots. -/
noncomputable def vectorTensorField {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (Y : Section S) : Field S 1 0 :=
  fun p => TensorData.pure (fun _ : Fin 1 => Y p) Fin.elim0

/-- Evaluation of an actual covariant tensor, using the canonical scalar
zeroth upper tensor power and the supplied algebraic covariant evaluation map. -/
noncomputable def covariantEvaluation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {s : ℕ}
    (A : Field S 0 s) (Y : Fin s → Section S) (p : M) : ℝ :=
  covariantEvaluate (TangentSpace S p) s
    (covariantEquiv (TangentSpace S p) s (A p)) (fun i => Y i p)

/-- Scalar chart derivatives use an actual differentiable ambient extension.
This is the scalar analogue of the frozen HasCoordinateDerivative predicate. -/
def HasScalarCoordinateDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) (g : M → ℝ) (p : M)
    (K : Euclidean n →L[ℝ] ℝ) : Prop :=
  ∃ G : Euclidean n → ℝ, HasFDerivAt G K (e p).val ∧
    (fun q => G (e q).val) =ᶠ[𝓝 p] g

/-- The full mixed-variance coordinate formula, with minus signs on upper
indices and plus signs on lower indices. Existence of every derivative is
required, so no conclusion is hidden in a universal implication. The formula
uses all ambient derivatives, including at boundary points. -/
def CoordinateLieDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (X : SmoothField B) {r s : ℕ} (A Z : Field S r s) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
    (∃ L, HasCoordinateDerivative e (coefficients B X.val e he) p L) ∧
    ∀ (I : Fin r → Fin n) (J : Fin s → Fin n),
      (∃ K, HasScalarCoordinateDerivative e (tensorCoefficients B A e he I J) p K) ∧
      ∀ (L : Euclidean n →L[ℝ] Euclidean n) (K : Euclidean n →L[ℝ] ℝ),
        HasCoordinateDerivative e (coefficients B X.val e he) p L →
        HasScalarCoordinateDerivative e (tensorCoefficients B A e he I J) p K →
        tensorCoefficients B Z e he I J p =
          K (coefficients B X.val e he p) -
            (∑ i : Fin r, ∑ k : Fin n,
              L (Pi.single k 1) (I i) *
                tensorCoefficients B A e he (Function.update I i k) J p) +
            (∑ j : Fin s, ∑ k : Fin n,
              L (Pi.single (J j) 1) k *
                tensorCoefficients B A e he I (Function.update J j k) p)

/-- The source's formula on an ambient coordinate neighborhood. This remains
meaningful for an arbitrary field at a boundary, since the chosen ambient
extensions need not preserve the half-space. -/
noncomputable def arrayLie (n r s : ℕ) (X : Euclidean n → Euclidean n)
    (A : Euclidean n → (Fin r → Fin n) → (Fin s → Fin n) → ℝ)
    (z : Euclidean n) (I : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  fderiv ℝ (fun w => A w I J) z (X z) -
    (∑ i : Fin r, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single k 1) (I i) * A z (Function.update I i k) J) +
    (∑ j : Fin s, ∑ k : Fin n,
      fderiv ℝ X z (Pi.single (J j) 1) k * A z I (Function.update J j k))

/-- Time differentiation of mixed pullback, in the fixed fiber at p. The
family e consists of genuine forward differentials on a neighborhood of zero.
Its inverse is therefore applied to upper tensor factors by mixedTransport.
Existence of such a family is part of the conclusions below. -/
def HasTensorFlowDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) {r s : ℕ} (A Z : Field S r s) (p : M) : Prop :=
  ∃ d : (t : ℝ) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t),
    (∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier ∧
      IsDifferential S S (fun q => F.curve q t) p (d t).toLinearMap) ∧
    ∀ d : (t : ℝ) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve p t),
      (∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (F.interval p).carrier ∧
        IsDifferential S S (fun q => F.curve q t) p (d t).toLinearMap) →
      ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val), p ∈ e.source →
        ∀ (I : Fin r → Fin n) (J : Fin s → Fin n),
          HasDerivAt (fun t => component B r s e he p I J
            (mixedTransport r s (d t) (A (F.curve p t))))
            (tensorCoefficients B Z e he I J p) 0

end SmoothManifolds.TensorLieData

namespace Specs.SmoothManifolds.Ch07.TensorLieDerivative
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.LieBracketData _root_.SmoothManifolds.BracketFlowData
  _root_.SmoothManifolds.BoundaryFlowData _root_.SmoothManifolds.TensorLieData
universe u

/-- The scalar derivative along every admissible integral curve, also in an
ordinary boundary chart. The value is the intrinsic action Xf. -/
def scalar_flowType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S), Represents X D →
    ∀ (I : Set ℝ) (γ : ℝ → M), IsOpen I →
      BoundaryFlowData.IsIntegralCurveOn X I γ →
      ∀ (f : GlobalSmooth S) (t : ℝ), t ∈ I →
        HasDerivAt (fun s => f.val (γ s)) ((D f).val (γ t)) t

/-- Actual vector pullback at every allowed time, with no tangency condition
on Y. The second clause is the up-to-boundary version, with precisely tangency
of X. The original inverse differential and its moving evaluation point are
those in BracketFlowData.pullback, not an arbitrarily chosen transport. -/
def vector_flowType : Prop :=
  (∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B) (F : MaximalFlowData.CurveFamily M),
      MaximalFlowData.IsMaximalFamily X F →
        PullbackCorrect S F ∧
        (∀ p, pullback F Y.val 0 p = Y.val p) ∧
        (∀ z ∈ MaximalFlowData.flowDomain F, PullbackSmoothAt B F Y.val z) ∧
        (∀ p, HasPullbackTimeDerivative B F Y.val (b X Y).val p 0) ∧
        ∀ p t, t ∈ (F.interval p).carrier →
          HasPullbackTimeDerivative B F Y.val (pullback F (b X Y).val t) p t) ∧
  (∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B), IsTangentToBoundary X →
    ∀ F : MaximalFlowData.CurveFamily M, BoundaryFlowData.IsMaximalFamily X F →
      PullbackCorrect S F ∧
      (∀ p, pullback F Y.val 0 p = Y.val p) ∧
      (∀ z ∈ MaximalFlowData.flowDomain F, PullbackSmoothAt B F Y.val z) ∧
      (∀ p, HasPullbackTimeDerivative B F Y.val (b X Y).val p 0) ∧
      ∀ p t, t ∈ (F.interval p).carrier →
        HasPullbackTimeDerivative B F Y.val (pullback F (b X Y).val t) p t)

/-- Intrinsic construction: a unique smooth mixed tensor with the intrinsic
coordinate formula, at all boundary points for every field X. It agrees with
the actual flow whenever X is boundary tangent. The Euclidean flow clause is stated
separately to avoid adding even a vacuous tangency premise to that case. -/
def tensor_constructionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (r s : ℕ) (A : SmoothTensor B r s),
    ∃! Z : SmoothTensor B r s, CoordinateLieDerivative B X A.val Z.val ∧
      (IsTangentToBoundary X → ∀ F : MaximalFlowData.CurveFamily M,
        BoundaryFlowData.IsMaximalFamily X F →
          ∀ p, HasTensorFlowDerivative B F A.val Z.val p)

/-- The boundaryless flow identification, without a tangency hypothesis. -/
def tensor_boundaryless_flowType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (r s : ℕ) (A Z : SmoothTensor B r s),
    CoordinateLieDerivative B X A.val Z.val →
    ∀ F : MaximalFlowData.CurveFamily M, MaximalFlowData.IsMaximalFamily X F →
      ∀ p, HasTensorFlowDerivative B F A.val Z.val p

/-- Arrays of all coordinate entries separate the actual mixed tensor fiber.
This includes zero variance and dimension zero. -/
def tensor_coefficients_extType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (r s : ℕ)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M), p ∈ e.source →
    ∀ A C : TensorData.Fiber (TangentSpace S p) r s,
      (∀ (I : Fin r → Fin n) (J : Fin s → Fin n),
        component B r s e he p I J A = component B r s e he p I J C) → A = C

/-- Smooth local ambient extension of the complete mixed-variance formula.
This proves regularity of the local formula; compatibility of the formulas on
chart overlaps and reconstruction as an intrinsic tensor remain separate. -/
def local_formula_smoothType : Prop :=
  ∀ (n r s : ℕ) (U : Set (ModelData.Euclidean n)), IsOpen U →
    ∀ (X : ModelData.Euclidean n → ModelData.Euclidean n)
      (A : ModelData.Euclidean n → (Fin r → Fin n) → (Fin s → Fin n) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) X U →
      (∀ I J, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => A z I J) U) →
      ∀ I J, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => arrayLie n r s X A z I J) U

/-- Uniqueness from the intrinsic coordinate formula, for every tensor
variance and all boundary points. No flow hypothesis is needed. -/
def tensor_coordinate_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (r s : ℕ) (A Z W : TensorData.Field S r s),
      CoordinateLieDerivative B X A Z → CoordinateLieDerivative B X A W → Z = W

/-- The intrinsic covariant evaluation formula. Smoothness of the
evaluated scalar is a conclusion, not an extra hypothesis. The tested section
Z has the full coordinate Lie formula. This applies to arbitrary X up to the
boundary and imposes no boundary tangency on any of the test fields. -/
def covariant_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X : SmoothField B) (s : ℕ) (A : SmoothTensor B 0 s)
      (Y : Fin s → SmoothField B),
    ∃ f : GlobalSmooth S,
      f.val = covariantEvaluation A.val (fun i => (Y i).val) ∧
      ∀ Z : SmoothTensor B 0 s, CoordinateLieDerivative B X A.val Z.val →
      ∀ D : RealDerivation S, Represents X D → ∀ p : M,
        covariantEvaluation Z.val (fun i => (Y i).val) p = (D f).val p -
          ∑ i : Fin s, covariantEvaluation A.val
            (fun j => (Function.update Y i (b X (Y i)) j).val) p

/-- Uniqueness of smooth extension from the ordinary interior, with no
flow or tangency premise and no positive-dimension or nonempty-base restriction. -/
def boundary_extension_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (r s : ℕ)
    (A Z : SmoothTensor B r s),
      (∀ p ∈ BoundaryData.manifoldInterior S, A.val p = Z.val p) → A = Z

/-- Contraction commutes with differentiation of actual flow pullback.
This implication applies wherever the input flow derivative exists. -/
def tensor_flow_contractionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) (r s : ℕ)
    (i : Fin (r+1)) (j : Fin (s+1)) (A Z : TensorData.Field S (r+1) (s+1)) (p : M),
    HasTensorFlowDerivative B F A Z p →
    HasTensorFlowDerivative B F
      (fun q => TensorData.contract (TangentSpace S q) i j (A q))
      (fun q => TensorData.contract (TangentSpace S q) i j (Z q)) p

/-- Like-slot permutations commute with differentiation of actual pullback. -/
def tensor_flow_permutationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M) (r s : ℕ)
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s))
    (A Z : TensorData.Field S r s) (p : M),
    HasTensorFlowDerivative B F A Z p →
    HasTensorFlowDerivative B F
      (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ (A q))
      (fun q => TensorData.mixedPermute (TangentSpace S q) r s σ τ (Z q)) p

/-- The tensor-product rule for actual local-flow derivatives. The
zero-time identity is automatic for both kinds of maximal flow upstream. -/
def tensor_flow_productType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (F : MaximalFlowData.CurveFamily M), (∀ q, F.curve q 0 = q) →
    ∀ (r s r' s' : ℕ) (A : TensorData.Field S r s) (C : TensorData.Field S r' s')
      (ZA : TensorData.Field S r s) (ZC : TensorData.Field S r' s') (p : M),
    HasTensorFlowDerivative B F A ZA p → HasTensorFlowDerivative B F C ZC p →
    HasTensorFlowDerivative B F
      (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (C q))
      (fun q => TensorData.tensorMultiply (TangentSpace S q) r s r' s' (ZA q) (C q) +
        TensorData.tensorMultiply (TangentSpace S q) r s r' s' (A q) (ZC q)) p

/-- The coordinate test describes smooth sections of the existing mixed tensor
bundle, for every allowed choice of its realization. -/
def tensor_smooth_iffType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (T : TensorData.TensorBundle S r s) (A : TensorData.Field S r s),
    TensorSmooth B A ↔ TensorData.IsSmoothField T A

/-- The standard scalar inclusion identifies the tensor coordinate rule with Xf. -/
def scalar_tensorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S), Represents X D →
    ∀ f : GlobalSmooth S,
      TensorSmooth B (scalarTensorField (S := S) f.val) ∧
      TensorSmooth B (scalarTensorField (S := S) (D f).val) ∧
      CoordinateLieDerivative B X (scalarTensorField (S := S) f.val)
        (scalarTensorField (S := S) (D f).val)

/-- The standard vector inclusion identifies the mixed rule with the bracket. -/
def vector_tensorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ X Y : SmoothField B,
      TensorSmooth B (vectorTensorField Y.val) ∧
      TensorSmooth B (vectorTensorField (b X Y).val) ∧
      CoordinateLieDerivative B X (vectorTensorField Y.val) (vectorTensorField (b X Y).val)

/-- The invariant evaluation of smooth covariant tensors is a smooth scalar. -/
def covariant_evaluation_smoothType : Prop :=
  ∀ {n s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (A : SmoothTensor B 0 s) (Y : Fin s → SmoothField B),
    ∃ f : GlobalSmooth S, f.val = covariantEvaluation A.val (fun i => (Y i).val)

/-- Tensor products, contraction and like-slot permutations preserve the
coordinate smoothness test, including on a boundary. -/
def tensor_operations_smoothType : Prop :=
  (∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (i : Fin (r+1)) (j : Fin (s+1)) (A : TensorData.Field S (r+1) (s+1)),
    TensorSmooth B A →
    TensorSmooth B (fun p => TensorData.contract (TangentSpace S p) i j (A p))) ∧
  (∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) (A : TensorData.Field S r s),
    TensorSmooth B A →
    TensorSmooth B (fun p => TensorData.mixedPermute (TangentSpace S p) r s σ τ (A p))) ∧
  (∀ {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (A : TensorData.Field S r s) (C : TensorData.Field S r' s'),
    TensorSmooth B A → TensorSmooth B C →
    TensorSmooth B (fun p => TensorData.tensorMultiply (TangentSpace S p) r s r' s' (A p) (C p)))

/-- Arbitrary fields, including fields normal to the boundary: the Lie rule
commutes with permutations of upper slots and of lower slots. -/
def tensor_permutationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (r s : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s))
    (A Z : TensorData.Field S r s), CoordinateLieDerivative B X A Z →
    CoordinateLieDerivative B X
      (fun p => TensorData.mixedPermute (TangentSpace S p) r s σ τ (A p))
      (fun p => TensorData.mixedPermute (TangentSpace S p) r s σ τ (Z p))

/-- Arbitrary fields: the Lie rule commutes with every permitted contraction. -/
def tensor_contractionType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (i : Fin (r+1)) (j : Fin (s+1)) (A Z : SmoothTensor B (r+1) (s+1)),
    CoordinateLieDerivative B X A.val Z.val →
    CoordinateLieDerivative B X
      (fun p => TensorData.contract (TangentSpace S p) i j (A.val p))
      (fun p => TensorData.contract (TangentSpace S p) i j (Z.val p))

/-- Arbitrary fields: the mixed tensor rule satisfies the tensor product
Leibniz identity. All inputs are smooth tensors of the original variance. -/
def tensor_productType : Prop :=
  ∀ {n r s r' s' : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (A ZA : SmoothTensor B r s) (C ZC : SmoothTensor B r' s'),
    CoordinateLieDerivative B X A.val ZA.val → CoordinateLieDerivative B X C.val ZC.val →
    CoordinateLieDerivative B X
      (fun p => TensorData.tensorMultiply (TangentSpace S p) r s r' s' (A.val p) (C.val p))
      (fun p => TensorData.tensorMultiply (TangentSpace S p) r s r' s' (ZA.val p) (C.val p) +
        TensorData.tensorMultiply (TangentSpace S p) r s r' s' (A.val p) (ZC.val p))

/-- Real linearity of the tensor Lie rule. Together with tensor_productType
this states that the operator is a derivation of the tensor algebra. -/
def tensor_linearityType : Prop :=
  (∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (A ZA C ZC : TensorData.Field S r s),
    CoordinateLieDerivative B X A ZA → CoordinateLieDerivative B X C ZC →
    CoordinateLieDerivative B X (fun p => A p + C p) (fun p => ZA p + ZC p)) ∧
  (∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S) (X : SmoothField B)
    (c : ℝ) (A Z : TensorData.Field S r s), CoordinateLieDerivative B X A Z →
    CoordinateLieDerivative B X (fun p => c • A p) (fun p => c • Z p))

end Specs.SmoothManifolds.Ch07.TensorLieDerivative
