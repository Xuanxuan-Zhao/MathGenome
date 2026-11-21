import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs

/-! Independent interfaces for paper.tex 1266--1275 (M05.01).

A transition `g i j p` changes i-coordinates to j-coordinates. Linear equivalences
are the coordinate-free representation of GL_r(R), acting on Fin r → R.
All smoothness tests below require actual local ambient extensions, including at
boundary points. Neither the index type nor the cover is assumed countable.
-/
namespace SmoothManifolds.BundleData
open ModelData AtlasData MapData ProductData Set Filter Bundle Module
open scoped Topology
universe u v w z

/-- Smoothness of maps into any real normed vector space, in every base chart.
Agreement is a germ on M, so junk values outside a chart do not impose conditions. -/
def SmoothOnBase {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : M → V) (U : Set M) : Prop :=
  ∀ p ∈ U, ContinuousAt f p ∧ ∀ c ∈ S.smoothStructure.val, p ∈ c.source →
    ∃ W : Set (Euclidean n), IsOpen W ∧ (c p).val ∈ W ∧
      ∃ F : Euclidean n → V, ContDiffOn ℝ (⊤ : ℕ∞) F W ∧
        (fun q => F (c q).val) =ᶠ[𝓝 p] f

/-- An open-cover cocycle. `g i j` means g_{ji} in the manuscript. -/
structure SmoothCocycle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : ℕ) (ι : Type v) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  covers : ∀ p : M, ∃ i, p ∈ baseSet i
  g : ι → ι → M → (Euclidean r ≃L[ℝ] Euclidean r)
  self : ∀ i p, p ∈ baseSet i → g i i p = ContinuousLinearEquiv.refl ℝ _
  comp : ∀ i j k p, p ∈ baseSet i → p ∈ baseSet j → p ∈ baseSet k →
    (g j k p).toContinuousLinearMap.comp (g i j p).toContinuousLinearMap =
      (g i k p).toContinuousLinearMap
  smooth : ∀ i j, SmoothOnBase S (fun p => (g i j p).toContinuousLinearMap)
    (baseSet i ∩ baseSet j)


/-- The manuscript's original overlap-only presentation. This keeps transition
values defined only where both trivializations exist; no extension to M is part
of the assumptions. The later totalization theorem supplies the junk values. -/
structure OverlapCocycle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : ℕ) (ι : Type v) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  covers : ∀ p : M, ∃ i, p ∈ baseSet i
  g : (i j : ι) → ↥(baseSet i ∩ baseSet j) → (Euclidean r ≃L[ℝ] Euclidean r)
  self : ∀ i p (hp : p ∈ baseSet i),
    g i i ⟨p, hp, hp⟩ = ContinuousLinearEquiv.refl ℝ _
  comp : ∀ i j k p (hi : p ∈ baseSet i) (hj : p ∈ baseSet j) (hk : p ∈ baseSet k),
    (g j k ⟨p, hj, hk⟩).toContinuousLinearMap.comp (g i j ⟨p, hi, hj⟩).toContinuousLinearMap =
      (g i k ⟨p, hi, hk⟩).toContinuousLinearMap
  smooth : ∀ i j (p : ↥(baseSet i ∩ baseSet j)),
    ContinuousAt (fun q => (g i j q).toContinuousLinearMap) p ∧
      ∀ c ∈ S.smoothStructure.val, p.val ∈ c.source →
        ∃ W : Set (Euclidean n), IsOpen W ∧ (c p.val).val ∈ W ∧
          ∃ F : Euclidean n → (Euclidean r →L[ℝ] Euclidean r),
            ContDiffOn ℝ (⊤ : ℕ∞) F W ∧
              (fun q : ↥(baseSet i ∩ baseSet j) => F (c q.val).val) =ᶠ[𝓝 p]
                (fun q => (g i j q).toContinuousLinearMap)

/-- The standard Euclidean fiber chart, including r = 0. -/
def fiberChart (r : ℕ) : ModelChart r .euclidean (Euclidean r) :=
  (Homeomorph.Set.univ (Euclidean r)).symm.toOpenPartialHomeomorph

/-- Bundle coordinates combine a linear trivialization with a base chart and
an actual ambient linear identification of the product model. -/
def bundleChart {n r : ℕ} {a k : ModelKind} {M : Type u} [TopologicalSpace M]
    {E : M → Type v} [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (C : ProductCoordinates n a r .euclidean k)
    (e : Trivialization (Euclidean r) (TotalSpace.proj (F := Euclidean r) (E := E)))
    (c : ModelChart n a M) : ModelChart (n + r) k (TotalSpace (Euclidean r) E) :=
  e.toOpenPartialHomeomorph.trans (productChart C c (fiberChart r))

/-- Smoothness of a map with vector parameters on an open part of M × V.
Its source ambient model is R^n × V; its target uses the given maximal atlas.
This is the local-extension test on product half-space charts. -/
def SmoothWithParameters {n d : ℕ} {a b : ModelKind}
    {M : Type u} {Q : Type v} [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold d b Q)
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : M × V → Q) (U : Set M) : Prop :=
  ∀ p : M × V, p.1 ∈ U → ContinuousAt f p ∧
    ∀ c ∈ S.smoothStructure.val, ∀ e ∈ T.smoothStructure.val,
      p.1 ∈ c.source → f p ∈ e.source →
        ∃ W : Set (Euclidean n × V), IsOpen W ∧ ((c p.1).val, p.2) ∈ W ∧
          ∃ F : (Euclidean n × V) → Euclidean d, ContDiffOn ℝ (⊤ : ℕ∞) F W ∧
            (fun q : M × V => F ((c q.1).val, q.2)) =ᶠ[𝓝 p]
              (fun q => (e (f q)).val)

/-- A smooth rank-r bundle, expressed by smooth fiber-linear trivializations.
The total topology is supplied independently; its Hausdorff and second-countable
properties are contained in `totalManifold`. The chart-membership requirement is
the smoothness of the local trivializations and their inverses. The projection,
zero section, addition and scalar multiplication are tested on their actual maps.
The latter two use local product parametrizations of the fiber product and of
R × E; these parametrizations cover those spaces. -/
structure SmoothVectorBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (r : ℕ) (ι : Type v) (E : M → Type w)
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)] where
  baseSet : ι → Set M
  covers : ∀ p : M, ∃ i, p ∈ baseSet i
  trivialization : ι → Trivialization (Euclidean r)
    (TotalSpace.proj (F := Euclidean r) (E := E))
  trivialization_baseSet : ∀ i, (trivialization i).baseSet = baseSet i
  linear : ∀ i, (trivialization i).IsLinear ℝ
  coordinates : ProductCoordinates n a r .euclidean (productKind n a r .euclidean)
  totalManifold : SmoothManifold (n + r) (productKind n a r .euclidean)
    (TotalSpace (Euclidean r) E)
  chart_mem : ∀ i c, c ∈ S.smoothStructure.val →
    bundleChart coordinates (trivialization i) c ∈ totalManifold.smoothStructure.val
  projection_smooth : IsSmoothMap totalManifold S TotalSpace.proj
  zero_smooth : IsSmoothMap S totalManifold (fun p => ⟨p, 0⟩)
  add_smooth : ∀ i, SmoothWithParameters S totalManifold
    (fun q : M × (Euclidean r × Euclidean r) =>
      (⟨q.1, (trivialization i).symm q.1 q.2.1 +
        (trivialization i).symm q.1 q.2.2⟩ : TotalSpace (Euclidean r) E)) (baseSet i)
  smul_smooth : ∀ i, SmoothWithParameters S totalManifold
    (fun q : M × (ℝ × Euclidean r) =>
      (⟨q.1, q.2.1 • (trivialization i).symm q.1 q.2.2⟩ : TotalSpace (Euclidean r) E))
    (baseSet i)

/-- Having exactly the prescribed domains and transitions, on every overlap. -/
def Realizes {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : SmoothCocycle S r ι)
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)] (B : SmoothVectorBundle S r ι E) : Prop :=
  (∀ i, B.baseSet i = C.baseSet i) ∧
    ∀ i j p, p ∈ C.baseSet i → p ∈ C.baseSet j → ∀ v : Euclidean r,
      ((B.trivialization j) ⟨p, (B.trivialization i).symm p v⟩).2 = C.g i j p v


/-- Realization stated directly for the original functions on U_i ∩ U_j. -/
def RealizesOverlap {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : OverlapCocycle S r ι)
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)] (B : SmoothVectorBundle S r ι E) : Prop :=
  (∀ i, B.baseSet i = C.baseSet i) ∧
    ∀ i j p (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j) (v : Euclidean r),
      ((B.trivialization j) ⟨p, (B.trivialization i).symm p v⟩).2 = C.g i j ⟨p, hi, hj⟩ v

/-- A local frame is an ordered basis of smooth local sections. Local sections
are defined only on U; their smoothness is tested using the restricted atlas. -/
structure LocalFrame {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)] (B : SmoothVectorBundle S r ι E)
    (U : Set M) (hU : IsOpen U) where
  section_ : Fin r → (p : U) → E p.val
  basis : ∀ p : U, Basis (Fin r) ℝ (E p.val)
  basis_eq : ∀ p j, basis p j = section_ j p
  smooth : ∀ j, ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
    B.totalManifold.smoothStructure.val (fun p : U =>
      (⟨p.val, section_ j p⟩ : TotalSpace (Euclidean r) E))

/-- The data returned by gluing. Fibers can always be chosen small, even if
M and the index set live in larger universes. There is no nonemptiness premise. -/
structure GluedBundle {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : SmoothCocycle S r ι) where
  Fiber : M → Type
  addCommGroup : ∀ p, AddCommGroup (Fiber p)
  module : ∀ p, @Module ℝ (Fiber p) _ (addCommGroup p).toAddCommMonoid
  topology : TopologicalSpace (TotalSpace (Euclidean r) Fiber)
  bundle : @SmoothVectorBundle n a M _ S r ι Fiber addCommGroup module topology
  realizes : @Realizes n r a M _ S ι C Fiber addCommGroup module topology bundle

/-- The exact coordinate-preservation condition; uniqueness is asserted among
all fiberwise linear equivalences, not just among a preselected class of maps. -/
def PreservesTrivializations {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean r) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S r ι F)
    (f : (p : M) → E p ≃ₗ[ℝ] F p) : Prop :=
  ∀ i p, p ∈ B.baseSet i → ∀ v : E p,
    ((D.trivialization i) ⟨p, f p v⟩).2 = ((B.trivialization i) ⟨p, v⟩).2

end SmoothManifolds.BundleData

namespace Specs.SmoothManifolds.Ch05.BundleGluing
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BundleData Bundle Set
universe u v w z


/-- Independent type and value contracts for the public canonical definitions. -/
def SmoothCocycleType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    SmoothManifold n a M → ℕ → (ι : Type v) → Type (max u v)

def SmoothCocycleValue : SmoothCocycleType := @BundleData.SmoothCocycle

def SmoothVectorBundleType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    (S : SmoothManifold n a M) → (r : ℕ) → (ι : Type v) → (E : M → Type w) →
    [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
    [TopologicalSpace (TotalSpace (Euclidean r) E)] → Type (max u v w)

def SmoothVectorBundleValue : SmoothVectorBundleType := @BundleData.SmoothVectorBundle

def LocalFrameType :=
  {n r : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n a M} → {ι : Type v} → {E : M → Type w} →
    [∀ p, AddCommGroup (E p)] → [∀ p, Module ℝ (E p)] →
    [TopologicalSpace (TotalSpace (Euclidean r) E)] → SmoothVectorBundle S r ι E →
    (U : Set M) → IsOpen U → Type (max u w)

def LocalFrameValue : LocalFrameType := @BundleData.LocalFrame

/-- M05.01 existence, with all the smoothness and manifold properties above. -/
def exists_gluedBundleType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : SmoothCocycle S r ι),
    Nonempty (GluedBundle C)


/-- Existence starting with functions defined only on the source overlaps.
The constructed total cocycle agrees exactly with those functions there. -/
def exists_gluedBundle_fromOverlapType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : OverlapCocycle S r ι),
    ∃ D : SmoothCocycle S r ι,
      (∀ i, D.baseSet i = C.baseSet i) ∧
      (∀ i j p (hi : p ∈ C.baseSet i) (hj : p ∈ C.baseSet j),
        D.g i j p = C.g i j ⟨p, hi, hj⟩) ∧ Nonempty (GluedBundle D)

/-- M05.01 uniqueness, for any two realizations on arbitrary fiber types.
Both directions of the resulting coordinate-preserving isomorphism are smooth. -/
def exists_unique_bundleIsomorphismType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : SmoothCocycle S r ι)
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean r) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S r ι F),
    Realizes C B → Realizes C D →
      ∃! f : (p : M) → E p ≃ₗ[ℝ] F p,
        IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, f q.proj q.snd⟩) ∧
        IsSmoothMap D.totalManifold B.totalManifold
          (fun q => ⟨q.proj, (f q.proj).symm q.snd⟩) ∧
        PreservesTrivializations B D f

/-- Uniqueness for realizations of the original overlap-only data. -/
def exists_unique_bundleIsomorphism_fromOverlapType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (C : OverlapCocycle S r ι)
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean r) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S r ι F),
    RealizesOverlap C B → RealizesOverlap C D →
      ∃! f : (p : M) → E p ≃ₗ[ℝ] F p,
        IsSmoothMap B.totalManifold D.totalManifold (fun q => ⟨q.proj, f q.proj q.snd⟩) ∧
        IsSmoothMap D.totalManifold B.totalManifold
          (fun q => ⟨q.proj, (f q.proj).symm q.snd⟩) ∧
        PreservesTrivializations B D f

end Specs.SmoothManifolds.Ch05.BundleGluing
