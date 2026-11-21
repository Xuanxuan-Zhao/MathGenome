import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! M05.03, quotient clause (paper.tex 1286--1295).

The input is a family of actual submodules with smooth local bases in the
ambient bundle. In particular an adapted frame, a complement, a quotient
trivialization, or smoothness of a quotient map is NOT an input hypothesis.
All smoothness tests use the shared ambient-extension convention.
-/
namespace SmoothManifolds.QuotientData
open ModelData AtlasData MapData ProductData BundleData FrameData Bundle Module Set
universe u v w z t

section Algebra
variable {M : Type u} {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]

/-- Actual algebraic quotient fibers; no replacement by chosen complements. -/
abbrev QuotientFiber (K : (p : M) → Submodule ℝ (E p)) (p : M) := E p ⧸ K p

/-- The canonical fiberwise quotient projection. -/
def quotientProjection (K : (p : M) → Submodule ℝ (E p)) (p : M) :
    E p →ₗ[ℝ] QuotientFiber K p := (K p).mkQ

/-- Vanishing on every vector of the prescribed subbundle. -/
def VanishesOn (K : (p : M) → Submodule ℝ (E p))
    (A : (p : M) → E p →ₗ[ℝ] F p) : Prop :=
  ∀ p v, v ∈ K p → A p v = 0

/-- The algebraically forced factorization; smoothness is a theorem obligation. -/
def quotientLift (K : (p : M) → Submodule ℝ (E p))
    (A : (p : M) → E p →ₗ[ℝ] F p) (hA : VanishesOn K A) (p : M) :
    QuotientFiber K p →ₗ[ℝ] F p :=
  (K p).liftQ (A p) (fun v hv => hA p v hv)

end Algebra

section Bundle
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Smooth local basis of K, viewed as sections of E. No topology on K is
presupposed and no extension of this basis to an E-frame is required. -/
structure LocalSubbundleFrame (K : (p : M) → Submodule ℝ (E p)) (k : ℕ)
    (U : Set M) (hU : IsOpen U) where
  basis : ∀ p : U, Basis (Fin k) ℝ (K p.val)
  smooth : ∀ j, ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
    B.totalManifold.smoothStructure.val (fun p : U =>
      (⟨p.val, (basis p j).val⟩ : TotalSpace (Euclidean r) E))

/-- The usual local-frame definition of a smooth rank-k subbundle of E. -/
def SmoothSubbundle (K : (p : M) → Submodule ℝ (E p)) (k : ℕ) : Prop :=
  ∀ p : M, ∃ U : Set M, ∃ hU : IsOpen U,
    p ∈ U ∧ Nonempty (LocalSubbundleFrame B K k U hU)

/-- All fields are OUTPUT conclusions of quotient construction. The bundle
uses the actual quotient fibers and the already shared SmoothVectorBundle.
One trivialization per point is enough, so its index type is M (also if empty).
`descent_smooth` is the smooth quotient test for every target bundle. -/
structure SmoothQuotient (K : (p : M) → Submodule ℝ (E p)) (k : ℕ) where
  topology : TopologicalSpace (TotalSpace (Euclidean (r - k)) (QuotientFiber K))
  bundle : @SmoothVectorBundle n a M _ S (r - k) M (QuotientFiber K)
    (fun _ => inferInstance) (fun _ => inferInstance) topology
  projection_smooth : @IsSmoothMap (n + r) (n + (r - k))
    (productKind n a r .euclidean) (productKind n a (r - k) .euclidean)
    (TotalSpace (Euclidean r) E) (TotalSpace (Euclidean (r - k)) (QuotientFiber K))
    _ topology B.totalManifold bundle.totalManifold
    (fun q => ⟨q.proj, quotientProjection K q.proj q.snd⟩)
  descent_smooth : ∀ {s : ℕ} {κ : Type t} {F : M → Type z}
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (D : SmoothVectorBundle S s κ F) (L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p),
    IsSmoothMap B.totalManifold D.totalManifold
      (fun q => ⟨q.proj, L q.proj (quotientProjection K q.proj q.snd)⟩) →
    @IsSmoothMap (n + (r - k)) (n + s)
      (productKind n a (r - k) .euclidean) (productKind n a s .euclidean)
      (TotalSpace (Euclidean (r - k)) (QuotientFiber K)) (TotalSpace (Euclidean s) F)
      topology _ bundle.totalManifold D.totalManifold
      (fun q => ⟨q.proj, L q.proj q.snd⟩)

end Bundle

/-- A component means an actual connected component of the given base. -/
def componentSet {M : Type u} [TopologicalSpace M] (c : ConnectedComponents M) : Set M :=
  {p | ConnectedComponents.mk p = c}

/-- Variable ranks are represented by smooth bundles on the open components.
Their base structures are the restrictions of the SAME base smooth structure.
The component fibers remain E_p, rather than newly introduced bundle fibers.
There is no boundedness requirement on the ranks across components. -/
structure ComponentwiseBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (E : M → Type w)
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)] where
  isOpen_component : ∀ c : ConnectedComponents M, IsOpen (componentSet c)
  base : ∀ c : ConnectedComponents M, SmoothManifold n a (componentSet c)
  base_atlas : ∀ c, (base c).smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (openSubsetAtlas S.smoothStructure.val (componentSet c) (isOpen_component c))
  rank : ConnectedComponents M → ℕ
  index : ConnectedComponents M → Type v
  topology : ∀ c, TopologicalSpace
    (TotalSpace (Euclidean (rank c)) (fun p : componentSet c => E p.val))
  bundle : ∀ c, @SmoothVectorBundle n a (componentSet c) _ (base c) (rank c) (index c)
    (fun p : componentSet c => E p.val) (fun _ => inferInstance)
    (fun _ => inferInstance) (topology c)

end SmoothManifolds.QuotientData

namespace Specs.SmoothManifolds.Ch05.QuotientBundles
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BundleData
  _root_.SmoothManifolds.FrameData _root_.SmoothManifolds.QuotientData Bundle Module Set
universe u v w z t

/-- Independent full propositions, with no axiom/certificate for the results. -/
def exists_smoothQuotientType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (K : (p : M) → Submodule ℝ (E p)) (k : ℕ),
    SmoothSubbundle B K k → Nonempty (SmoothQuotient.{u,v,w,z,t} B K k)

def smoothQuotient_factorizationType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F)
    (K : (p : M) → Submodule ℝ (E p)) (k : ℕ)
    (Q : SmoothQuotient.{u,v,w,z,t} B K k) (A : (p : M) → E p →ₗ[ℝ] F p),
    IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, A q.proj q.snd⟩) →
    VanishesOn K A →
    letI := Q.topology
    ∃! L : (p : M) → QuotientFiber K p →ₗ[ℝ] F p,
      @IsSmoothMap (n + (r - k)) (n + s)
        (productKind n a (r - k) .euclidean) (productKind n a s .euclidean)
        (TotalSpace (Euclidean (r - k)) (QuotientFiber K)) (TotalSpace (Euclidean s) F)
        Q.topology _ Q.bundle.totalManifold D.totalManifold
        (fun q => ⟨q.proj, L q.proj q.snd⟩) ∧
      ∀ p, (L p).comp (quotientProjection K p) = A p

def quotientProjection_surjectiveType : Prop :=
  ∀ {M : Type u} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (K : (p : M) → Submodule ℝ (E p)) (p : M),
    Function.Surjective (quotientProjection K p)

def quotientProjection_kernelType : Prop :=
  ∀ {M : Type u} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (K : (p : M) → Submodule ℝ (E p)) (p : M),
    LinearMap.ker (quotientProjection K p) = K p

def quotient_finrankType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (K : (p : M) → Submodule ℝ (E p)) (k : ℕ),
    SmoothSubbundle B K k → ∀ p : M,
      k ≤ r ∧ Module.finrank ℝ (QuotientFiber K p) = r - k

/-- Explicit endpoint identifications. The smooth construction applies without
any exclusion of k=0, k=r, r=0, an empty base, or a base boundary. -/
def quotient_zeroType : Prop :=
  ∀ {M : Type u} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)],
    ∃ e : (p : M) → QuotientFiber (fun q => (⊥ : Submodule ℝ (E q))) p ≃ₗ[ℝ] E p,
      ∀ p v, e p (quotientProjection (fun q => (⊥ : Submodule ℝ (E q))) p v) = v

def quotient_fullType : Prop :=
  ∀ {M : Type u} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)],
    ∀ p (v : QuotientFiber (fun q => (⊤ : Submodule ℝ (E q))) p), v = 0

/-- Both endpoint subbundles actually satisfy the smooth input hypothesis. -/
def smoothSubbundle_zeroType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
    SmoothSubbundle B (fun p => (⊥ : Submodule ℝ (E p))) 0

def smoothSubbundle_fullType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E),
    SmoothSubbundle B (fun p => (⊤ : Submodule ℝ (E p))) r

/-- The complete construction on every actual open connected component. Ranks
of E and K can both vary, with quotient rank rank(E_c)-rank(K_c).
Together with the general smooth factorization theorem this also gives the
factorization of all componentwise smooth bundle morphisms. -/
def exists_componentwise_smoothQuotientType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (B : ComponentwiseBundle.{u,v,w} S E)
    (K : (p : M) → Submodule ℝ (E p)) (k : ConnectedComponents M → ℕ),
    (∀ c, @SmoothSubbundle n (B.rank c) a (componentSet c) _ (B.base c) (B.index c)
      (fun p : componentSet c => E p.val) (fun _ => inferInstance)
      (fun _ => inferInstance) (B.topology c) (B.bundle c) (fun p => K p.val) (k c)) →
    Nonempty (∀ c, @SmoothQuotient.{u,v,w,z,t} n (B.rank c) a (componentSet c) _ (B.base c)
      (B.index c) (fun p : componentSet c => E p.val) (fun _ => inferInstance)
      (fun _ => inferInstance) (B.topology c) (B.bundle c) (fun p => K p.val) (k c))

end Specs.SmoothManifolds.Ch05.QuotientBundles
