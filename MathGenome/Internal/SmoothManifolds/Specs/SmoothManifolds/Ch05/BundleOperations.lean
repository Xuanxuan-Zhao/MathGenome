import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.ConstantRankBundles
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.QuotientBundles
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Independent interfaces for M05.04, paper.tex 1299--1304.

The fibers below are the actual algebraic constructions on the given fibers.
The topology and smooth bundle structures are outputs. Coordinate identities
specify the induced structures, rather than merely asking for unrelated bundles
of the same ranks. All base models are unrestricted, including ordinary boundary
and dimension zero. No metric or orthogonal complement is used.
-/
set_option autoImplicit false

namespace SmoothManifolds.BundleOperationsData
open ModelData AtlasData MapData ProductData BundleData FrameData ConstantRankData
  QuotientData TangentData TangentBundleData DifferentialData MapClassData Bundle Set
universe u v w z t

/-- A smooth bundle structure on prescribed fibers, with its topology supplied
as construction data. The index set need not be countable or nonempty. -/
structure BundleSpace {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : ℕ) (ι : Type v) (E : M → Type w)
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)] where
  topology : TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)
  bundle : @SmoothVectorBundle n a M _ S r ι E
    (fun _ => inferInstance) (fun _ => inferInstance) topology

section Pullback
variable {n m r : ℕ} {a b : ModelKind} {M : Type u} {P : Type v}
  [TopologicalSpace M] [TopologicalSpace P]
  {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- The pullback has exactly the given fibers and pulled-back trivializations.
The canonical map is (p,v) ↦ (f(p),v), on the actual total spaces. -/
structure PullbackBundle (B : SmoothVectorBundle S r ι E)
    (T : SmoothManifold m b P) (f : P → M) where
  space : BundleSpace T r ι (fun p => E (f p))
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = f ⁻¹' B.baseSet i
  coordinates : letI := space.topology; ∀ i p, f p ∈ B.baseSet i → ∀ v : E (f p),
    ((space.bundle.trivialization i) ⟨p, v⟩).2 =
      ((B.trivialization i) ⟨f p, v⟩).2
  canonical_smooth : letI := space.topology
    IsSmoothMap space.bundle.totalManifold B.totalManifold
      (fun q => (⟨f q.proj, q.snd⟩ : Bundle.TotalSpace (Euclidean r) E))

end Pullback

section AlgebraicOperations
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]

/-- Dual coordinates evaluate on the original local frame. Thus the induced
transition is the inverse transpose, with no chosen fiber metric. -/
structure DualBundle (B : SmoothVectorBundle S r ι E) where
  space : BundleSpace S r ι (fun p => Module.Dual ℝ (E p))
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = B.baseSet i
  coordinates : letI := space.topology; ∀ i p, p ∈ B.baseSet i → ∀ (lam : Module.Dual ℝ (E p)) (j : Fin r),
    ((space.bundle.trivialization i) ⟨p, lam⟩).2 j =
      lam ((B.trivialization i).symm p (Pi.single j 1))

/-- Finite direct sums are fiberwise products; both coordinate blocks are the
original coordinates. This fixes the canonical injections and projections. -/
structure DirectSumBundle (B : SmoothVectorBundle S r ι E)
    (D : SmoothVectorBundle S s κ F) where
  space : BundleSpace S (r + s) (ι × κ) (fun p => E p × F p)
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = B.baseSet i.1 ∩ D.baseSet i.2
  coordinates_left : letI := space.topology; ∀ i p, p ∈ space.bundle.baseSet i → ∀ v : E p × F p,
    ∀ j : Fin r, ((space.bundle.trivialization i) ⟨p, v⟩).2 (Fin.castAdd s j) =
      ((B.trivialization i.1) ⟨p, v.1⟩).2 j
  coordinates_right : letI := space.topology; ∀ i p, p ∈ space.bundle.baseSet i → ∀ v : E p × F p,
    ∀ j : Fin s, ((space.bundle.trivialization i) ⟨p, v⟩).2 (Fin.natAdd r j) =
      ((D.trivialization i.2) ⟨p, v.2⟩).2 j

/-- Coordinates on pure tensors determine the entire linear trivialization,
since pure tensors span the actual algebraic tensor product. -/
structure TensorBundle (B : SmoothVectorBundle S r ι E)
    (D : SmoothVectorBundle S s κ F) where
  space : BundleSpace S (r * s) (ι × κ) (fun p => TensorProduct ℝ (E p) (F p))
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = B.baseSet i.1 ∩ D.baseSet i.2
  coordinates : letI := space.topology; ∀ i p, p ∈ space.bundle.baseSet i → ∀ (v : E p) (w : F p)
    (j : Fin r) (k : Fin s),
    ((space.bundle.trivialization i) ⟨p, TensorProduct.tmul ℝ v w⟩).2
      (finProdFinEquiv (j, k)) =
      ((B.trivialization i.1) ⟨p, v⟩).2 j * ((D.trivialization i.2) ⟨p, w⟩).2 k

/-- Exterior powers use the actual exterior algebra's homogeneous submodule.
A single fixed model equivalence only orders its standard coordinates. The
formula on all decomposable wedges fixes the full induced trivialization. -/
structure ExteriorBundle (B : SmoothVectorBundle S r ι E) (k : ℕ) where
  space : BundleSpace S (r.choose k) ι (fun p => ⋀[ℝ]^k (E p))
  modelEquiv : (⋀[ℝ]^k (Euclidean r)) ≃ₗ[ℝ] Euclidean (r.choose k)
  baseSet : letI := space.topology; ∀ i, space.bundle.baseSet i = B.baseSet i
  coordinates : letI := space.topology; ∀ i p, p ∈ B.baseSet i → ∀ v : Fin k → E p,
    ((space.bundle.trivialization i) ⟨p, exteriorPower.ιMulti ℝ k v⟩).2 =
      modelEquiv (exteriorPower.ιMulti ℝ k
        (fun j => ((B.trivialization i) ⟨p, v j⟩).2))

end AlgebraicOperations

/-- The tangent index is the original maximal base atlas. -/
abbrev TangentIndex {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := {c : ModelChart n a M // c ∈ S.smoothStructure.val}

/-- The shared tangent construction uses a sigma total space; vector bundles
use Bundle.TotalSpace. This bridge preserves the actual derivation fibers,
original tangent coordinates and smoothness in both directions. -/
structure TangentRealization {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (TB : TangentBundleStructure S) where
  space : BundleSpace S n (TangentIndex S) (TangentSpace S)
  baseSet : letI := space.topology; ∀ c, space.bundle.baseSet c = c.val.source
  coordinates : letI := space.topology; ∀ c p (hp : p ∈ c.val.source) (v : TangentSpace S p),
    ((space.bundle.trivialization c) ⟨p, v⟩).2 =
      TB.fiberCoordinates.equiv c.val c.property p hp v
  smooth_to_original : letI := space.topology; letI := TB.topology
    IsSmoothMap space.bundle.totalManifold TB.manifold
      (fun q => (⟨q.proj, q.snd⟩ : TangentBundleData.TotalSpace S))
  smooth_from_original : letI := space.topology; letI := TB.topology
    IsSmoothMap TB.manifold space.bundle.totalManifold
      (fun q => (⟨q.1, q.2⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)))

/-- By definition T*M has the duals of the original tangent spaces as fibers. -/
abbrev CotangentFiber {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := Module.Dual ℝ (TangentSpace S p)

structure CotangentBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) where
  tangent : TangentBundleStructure S
  realization : TangentRealization tangent
  dual : @DualBundle n n a M _ S (TangentIndex S) (TangentSpace S)
    (fun _ => inferInstance) (fun _ => inferInstance) realization.space.topology
    realization.space.bundle

/-- The normal fibers are i*TM / im(di), and di identifies TS with that image.
All tangent structures, smooth image charts, and quotient structures are outputs.
The inclusion may meet the ambient or intrinsic boundary; there is no neatness
or interior-point assumption. A metric complement is not used. -/
structure NormalBundle {m n : ℕ} {a b : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m a P) (S : SmoothManifold n b M) (i : P → M) where
  sourceTangent : TangentBundleStructure T
  ambientTangent : TangentBundleStructure S
  sourceRealization : TangentRealization sourceTangent
  ambientRealization : TangentRealization ambientTangent
  pullback : letI := ambientRealization.space.topology; @PullbackBundle n m n b a M P _ _ S (TangentIndex S) (TangentSpace S)
    (fun _ => inferInstance) (fun _ => inferInstance) ambientRealization.space.topology
    ambientRealization.space.bundle T i
  differential : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (i p)
  isDifferential : ∀ p, IsDifferential T S i p (differential p)
  injective : ∀ p, Function.Injective (differential p)
  differential_smooth : letI := ambientRealization.space.topology
    letI := sourceRealization.space.topology
    letI := pullback.space.topology
    IsSmoothMap sourceRealization.space.bundle.totalManifold
      pullback.space.bundle.totalManifold (fun q => ⟨q.proj, differential q.proj q.snd⟩)
  image_smooth : letI := ambientRealization.space.topology; @IsSmoothSubbundle m n a P _ T (TangentIndex S)
    (fun p => TangentSpace S (i p)) (fun _ => inferInstance) (fun _ => inferInstance)
    pullback.space.topology pullback.space.bundle m (fun p => LinearMap.range (differential p))
  image_frame : letI := ambientRealization.space.topology; @SmoothSubbundle m n a P _ T (TangentIndex S)
    (fun p => TangentSpace S (i p)) (fun _ => inferInstance) (fun _ => inferInstance)
    pullback.space.topology pullback.space.bundle (fun p => LinearMap.range (differential p)) m
  quotient : letI := ambientRealization.space.topology; @SmoothQuotient.{u,u,u,u,u} m n a P _ T (TangentIndex S)
    (fun p => TangentSpace S (i p)) (fun _ => inferInstance) (fun _ => inferInstance)
    pullback.space.topology pullback.space.bundle (fun p => LinearMap.range (differential p)) m

end SmoothManifolds.BundleOperationsData

namespace Specs.SmoothManifolds.Ch05.BundleOperations
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.FrameData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.MapClassData
  Bundle Set
universe u v w z t

/-- Pullback existence includes its canonical smooth map to E. -/
def exists_pullbackType : Prop :=
  ∀ {n m r : ℕ} {a b : ModelKind} {M : Type u} {P : Type v}
    [TopologicalSpace M] [TopologicalSpace P]
    {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (T : SmoothManifold m b P) (f : P → M),
    IsSmoothMap T S f → Nonempty (PullbackBundle B T f)

/-- Canonical identity on E_{f(g(q))} is smooth in both directions, for any
realizations of these pulled-back charts. Its fiber map is the identity linear
equivalence, so this is precisely the canonical smooth bundle isomorphism. -/
def pullback_compType : Prop :=
  ∀ {n m l r : ℕ} {a b c : ModelKind} {M : Type u} {P : Type v} {Q : Type z}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (T : SmoothManifold m b P)
    (U : SmoothManifold l c Q) (f : P → M) (g : Q → P),
    IsSmoothMap T S f → IsSmoothMap U T g →
    ∀ (F : PullbackBundle B T f) (H : PullbackBundle B U (f ∘ g)),
    letI := F.space.topology
    ∀ (G : @PullbackBundle m l r b c P Q _ _ T ι (fun p => E (f p))
        (fun _ => inferInstance) (fun _ => inferInstance) F.space.topology F.space.bundle U g),
    letI := H.space.topology; letI := G.space.topology
    @IsSmoothMap (l+r) (l+r) _ _ _ _ H.space.topology G.space.topology
      H.space.bundle.totalManifold G.space.bundle.totalManifold id ∧
    @IsSmoothMap (l+r) (l+r) _ _ _ _ G.space.topology H.space.topology
      G.space.bundle.totalManifold H.space.bundle.totalManifold id

section AlgebraicOperations
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]

def exists_dualType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E), Nonempty (DualBundle B)

def exists_directSumType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F),
    Nonempty (DirectSumBundle B D)

def exists_tensorType : Prop :=
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F),
    Nonempty (TensorBundle B D)

def exists_exteriorType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (k : ℕ), Nonempty (ExteriorBundle B k)

/-- The smooth trivialization is the canonical zero-degree algebraic map,
not an arbitrary algebraic identification with a line. -/
def exterior_zeroType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (V : ExteriorBundle B 0),
    letI := V.space.topology
    ∃ e : SmoothTrivialization V.space.bundle,
      ∀ p v j, e.coordinates p v j = exteriorPower.zeroEquiv ℝ (E p) v

/-- All high-degree fibers vanish, and the constructed smooth bundle is the
trivial zero bundle. Existence in every degree is asserted above. -/
def exterior_above_rankType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (k : ℕ) (V : ExteriorBundle B k),
    r < k → (∀ p (v : ⋀[ℝ]^k (E p)), v = 0) ∧
      @SmoothlyTrivial n (r.choose k) a M _ S ι (fun p => ⋀[ℝ]^k (E p))
        (fun _ => inferInstance) (fun _ => inferInstance) V.space.topology V.space.bundle

end AlgebraicOperations

def exists_tangentRealizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (TB : TangentBundleData.TangentBundleStructure S),
    Nonempty (TangentRealization TB)

def exists_cotangentType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), Nonempty (CotangentBundle S)

/-- A smooth embedding includes a full injective differential at every point,
including boundary points. All normal-bundle conclusions are constructed. -/
def exists_normalType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m a P) (S : SmoothManifold n b M) (i : P → M),
    IsSmoothEmbedding T S i → Nonempty (NormalBundle T S i)

end Specs.SmoothManifolds.Ch05.BundleOperations
