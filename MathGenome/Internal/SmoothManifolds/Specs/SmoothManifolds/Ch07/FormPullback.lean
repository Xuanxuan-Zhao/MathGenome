import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorAlgebra

/-! Independent interface for M07.02, paper.tex 1471--1484.
Pullback uses the actual homogeneous exterior powers and genuine differentials
on the intrinsic tangent fibers. Differential families are explicit, with their
existence a conclusion, following the upstream covector interface. All model
kinds and dimensions are allowed. The Jacobian is signed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SmoothManifolds.FormPullbackData
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleData BundleOperationsData CovectorData ExteriorData
universe u

/-- Algebraic pullback in a single fiber. -/
def fiberPullback {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (L : V →ₗ[ℝ] W) :
    Fiber W k →ₗ[ℝ] Fiber V k := exteriorPower.map k L.dualMap

/-- Pullback along a family of tangent maps. -/
def pullbackField {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    {k : ℕ} (ω : Field T k) : Field S k :=
  fun p => fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) k (L p) (ω (f p))

/-- Degree-zero fields corresponding to scalar functions. -/
def scalarField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → ℝ) : Field S 0 :=
  fun p => (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (f p)

/-- The coefficient in the ordered top coordinate wedge. -/
def topCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (ω : Field S n) : ℝ :=
  evaluate (TangentSpace S p) n (ω p) (coordinateVector K c hc p hp)

abbrev CotangentTotal {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := Bundle.TotalSpace (Euclidean n) (CotangentFiber S)

/-- The intrinsic tautological covector: θ_ξ = ξ ∘ dπ_ξ. -/
def tautologicalField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) :
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ((ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj) →
      CovectorField Q := by
  letI := (cotangentSpace C).topology
  exact fun L ξ => ξ.snd.comp (L ξ)

end SmoothManifolds.FormPullbackData

namespace Specs.SmoothManifolds.Ch07.FormPullback
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.BundleData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.FormPullbackData
  _root_.SmoothManifolds.MapClassData Set Filter
open scoped Topology
universe u

def pullback_applyType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (k : ℕ) (ω : Field T k) (p : M) (v : Fin k → TangentSpace S p),
    evaluate (TangentSpace S p) k (FormPullbackData.pullbackField S T f L ω p) v =
      evaluate (TangentSpace T (f p)) k (ω (f p)) (fun i => L p (v i))

def pullback_zeroType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) (g : N → ℝ),
    FormPullbackData.pullbackField S T f L (scalarField T g) = scalarField S (g ∘ f)

def pullback_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : M → N),
    IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, IsDifferential S T f p (L p)) → ∀ (k : ℕ)
      (A : FormBundle C k) (B : FormBundle D k) (ω : Field T k),
      IsForm B ω → IsForm A (FormPullbackData.pullbackField S T f L ω)

def pullback_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : M → N),
    IsSmoothMap S T f → ∀ (k : ℕ) (A : FormBundle C k) (B : FormBundle D k) (ω : Form B),
      ∃ L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
        (∀ p, IsDifferential S T f p (L p)) ∧
        IsForm A (FormPullbackData.pullbackField S T f L ω.field)

def pullback_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    (∀ p, IsDifferential S S id p (L p)) → ∀ (k : ℕ) (ω : Field S k),
      FormPullbackData.pullbackField S S id L ω = ω

def pullback_compType : Prop :=
  ∀ {n m r : ℕ} {a b c : ModelKind} {M N P : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold r c P)
    (f : M → N) (g : N → P), IsSmoothMap S T f → IsSmoothMap T U g →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (K : (q : N) → TangentSpace T q →ₗ[ℝ] TangentSpace U (g q))
      (H : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace U (g (f p))),
      (∀ p, IsDifferential S T f p (L p)) →
      (∀ q, IsDifferential T U g q (K q)) →
      (∀ p, IsDifferential S U (g ∘ f) p (H p)) → ∀ (k : ℕ) (ω : Field U k),
      FormPullbackData.pullbackField S U (g ∘ f) H ω =
        FormPullbackData.pullbackField S T f L (FormPullbackData.pullbackField T U g K ω)

def pullback_wedgeType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (k l : ℕ) (α : Field T k) (β : Field T l),
    FormPullbackData.pullbackField S T f L (fieldWedge α β) =
      fieldWedge (FormPullbackData.pullbackField S T f L α)
        (FormPullbackData.pullbackField S T f L β)

/-- Restriction to an embedded submanifold includes the tangent inclusion. -/
def restrictionType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (D : CotangentBundle T) (i : M → N),
    IsSmoothEmbedding S T i →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (i p)),
      (∀ p, IsDifferential S T i p (L p)) → ∀ (k : ℕ)
      (A : FormBundle C k) (B : FormBundle D k) (ω : Field T k), IsForm B ω →
      IsForm A (FormPullbackData.pullbackField S T i L ω) ∧
      ∀ (p : M) (v : Fin k → TangentSpace S p),
        evaluate (TangentSpace S p) k (FormPullbackData.pullbackField S T i L ω p) v =
          evaluate (TangentSpace T (i p)) k (ω (i p)) (fun j => L p (v j))

/-- No lower bound on dimension or degree. -/
def pullback_high_degreeType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (k : ℕ) (ω : Field T k),
    (n < k ∨ m < k) → ∀ p, FormPullbackData.pullbackField S T f L ω p = 0

/-- Every actual smooth ambient coordinate extension gives the signed Jacobian
multiplier. The two tangent coordinate systems are the original ones. -/
def signed_jacobianType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (C : CotangentBundle S) (D : CotangentBundle T) (f : M → N),
    IsSmoothMap S T f →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (L p)) →
    ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (d : ModelChart n b N) (hd : d ∈ T.smoothStructure.val)
      (p : M) (hp : p ∈ c.source) (hq : f p ∈ d.source)
      (W : Set (Euclidean n)) (H : Euclidean n → Euclidean n),
      IsOpen W → (c p).val ∈ W → ContDiffOn ℝ (⊤ : ℕ∞) H W →
      (fun q => H (c q).val) =ᶠ[𝓝 p] (fun q => (d (f q)).val) →
      ∀ ω : Field T n,
      topCoefficient C.tangent.fiberCoordinates c hc p hp
        (FormPullbackData.pullbackField S T f L ω) =
      topCoefficient D.tangent.fiberCoordinates d hd (f p) hq ω *
        (Matrix.of (fun i j => fderiv ℝ H (c p).val (Pi.single j 1) i)).det

/-- Existence of the projection differential, so no tangent data are assumed
for the construction of the tautological form. -/
def tautological_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S),
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∃ L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj,
      (∀ ξ, IsDifferential Q S Bundle.TotalSpace.proj ξ (L ξ)) ∧
      ∀ A : CotangentBundle Q, IsOneForm A (tautologicalField C L)

/-- Every representative of dπ gives the same smooth tautological form. -/
def tautological_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S),
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∀ (L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj),
      (∀ ξ, IsDifferential Q S Bundle.TotalSpace.proj ξ (L ξ)) →
      ∀ A : CotangentBundle Q, IsOneForm A (tautologicalField C L)

def tautological_applyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S),
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∀ (L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj)
      (ξ : CotangentTotal S) (V : TangentSpace Q ξ),
      tautologicalField C L ξ V = ξ.snd (L ξ V)

/-- θ = Σ p_i dx^i: p_i are the induced cotangent coordinates, and dx^i
on the total space is the pullback of the original coordinate covector by π.
This includes the empty sum when n = 0. -/
def tautological_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S),
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∀ (L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj),
      (∀ ξ, IsDifferential Q S Bundle.TotalSpace.proj ξ (L ξ)) →
      ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (ξ : CotangentTotal S) (hξ : ξ.proj ∈ c.source),
      tautologicalField C L ξ = ∑ j : Fin n,
        (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ξ).2 j •
          (coordinateCovector C.tangent.fiberCoordinates c hc ξ.proj hξ j).comp (L ξ)

end Specs.SmoothManifolds.Ch07.FormPullback
