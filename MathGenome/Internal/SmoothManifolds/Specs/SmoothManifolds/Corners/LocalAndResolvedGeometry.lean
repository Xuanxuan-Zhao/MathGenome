import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Compactness.LocallyCompact
import Lean.Elab.Tactic.Omega

/-! Independent corner data for paper.tex 1978–1991 and 2001–2026.

This module specifies local geometry, intrinsic face germs, the resolved smooth
corner structure and proper smooth projection, and the affine box and simplex
examples. General products and outward-first orientations are separate obligations.
Orthants and their ambient-extension convention are the shared foundation objects.
-/
namespace SmoothManifolds.CornerData
open ModelData Set Filter
open scoped Topology
universe u

/-- A chart may use any number of constrained coordinates, at fixed dimension. -/
abbrev CornerChart (n : ℕ) (M : Type u) [TopologicalSpace M] :=
  Σ k : Fin (n + 1), OpenPartialHomeomorph M (Orthant n k)

/-- The two directions of a transition extend smoothly into ambient Euclidean space.
The extensions need not take values in an orthant away from the model. -/
def CornerCompatible {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c d : CornerChart n M) : Prop :=
  let e := c.2.symm.trans d.2
  OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun x => e x.val) ∧
    OrthantMapContDiffOn (⊤ : ℕ∞) e.target (fun x => e.symm x.val)

def IsSmoothCornerAtlas {n : ℕ} {M : Type u} [TopologicalSpace M]
    (A : Set (CornerChart n M)) : Prop :=
  (∀ p : M, ∃ c ∈ A, p ∈ c.2.source) ∧
    ∀ c ∈ A, ∀ d ∈ A, CornerCompatible c d

def IsMaximalSmoothCornerAtlas {n : ℕ} {M : Type u} [TopologicalSpace M]
    (A : Set (CornerChart n M)) : Prop :=
  IsSmoothCornerAtlas A ∧
    ∀ B, IsSmoothCornerAtlas B → A ⊆ B → B = A

/-- Hausdorff and second-countable are part of the source's manifold convention.
Neither nonemptiness nor a positive dimension is required. -/
structure CornerManifold (n : ℕ) (M : Type u) [TopologicalSpace M] where
  hausdorff : T2Space M
  secondCountable : SecondCountableTopology M
  atlas : Set (CornerChart n M)
  maximal : IsMaximalSmoothCornerAtlas atlas

/-- The maximal extension consists of all charts compatible with a covering atlas.
Its compatibility and maximality are conclusions, not assumed fields. -/
def cornerMaximalExtension {n : ℕ} {M : Type u} [TopologicalSpace M]
    (A : Set (CornerChart n M)) : Set (CornerChart n M) :=
  {c | ∀ a ∈ A, CornerCompatible c a}

/-- The constrained coordinates vanishing at the specified point. -/
noncomputable def activeCoordinates {n : ℕ} {k : Fin (n + 1)}
    (x : Orthant n k) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => i.val < k.val ∧ x.val i = 0)

noncomputable def modelDepth {n : ℕ} {k : Fin (n + 1)}
    (x : Orthant n k) : ℕ := (activeCoordinates x).card

/-- The coordinate description of the one-sided velocity cone. -/
def modelCone {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k) : Set (Euclidean n) :=
  {v | ∀ i, i.val < k.val → x.val i = 0 → 0 ≤ v i}

/-- Actual velocities of curves defined for nonnegative time near zero and staying
in the specified relatively open chart patch. Differentiability is one-sided. -/
def IsForwardVelocity {n : ℕ} {k : Fin (n + 1)}
    (s : Set (Orthant n k)) (x : Orthant n k) (v : Euclidean n) : Prop :=
  ∃ c : ℝ → Euclidean n, c 0 = x.val ∧
    HasDerivWithinAt c v (Ici 0) 0 ∧
    ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, c t ∈ Subtype.val '' s

/-- The same velocities can be realized with a smooth ambient extension of the
curve, the manuscript's smoothness convention at the parameter endpoint. -/
def IsSmoothForwardVelocity {n : ℕ} {k : Fin (n + 1)}
    (s : Set (Orthant n k)) (x : Orthant n k) (v : Euclidean n) : Prop :=
  ∃ c : ℝ → Euclidean n, c 0 = x.val ∧ ContDiffAt ℝ (⊤ : ℕ∞) c 0 ∧
    HasDerivAt c v 0 ∧
    ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, c t ∈ Subtype.val '' s

/-- The coordinate subspace on which all active normal coordinates vanish. -/
def modelLineality {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k) :
    Submodule ℝ (Euclidean n) where
  carrier := {v | ∀ i, i.val < k.val → x.val i = 0 → v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i hi hx
    change v i + w i = 0
    rw [hv i hi hx, hw i hi hx, add_zero]
  smul_mem' := by
    intro a v hv i hi hx
    change a * v i = 0
    rw [hv i hi hx, mul_zero]

/-- A coordinate facet of the one-sided cone. The active coordinate labels
are the local codimension-one normal directions. -/
def modelFacet {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k)
    (i : activeCoordinates x) : Set (Euclidean n) :=
  {v | v ∈ modelCone x ∧ v i.val = 0}

/-- A genuine ambient representative of a coordinate map near one point.
All fields are extension data; no assertion about its derivative is assumed. -/
structure OrthantExtension {n : ℕ} {k l : Fin (n + 1)}
    (s : Set (Orthant n k)) (f : Orthant n k → Orthant n l) (x : Orthant n k) where
  domain : Set (Euclidean n)
  isOpen_domain : IsOpen domain
  mem_domain : x.val ∈ domain
  map : Euclidean n → Euclidean n
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) map domain
  agrees : ∀ y ∈ s, y.val ∈ domain → map y.val = (f y).val

/-- The germ of the actual coordinate-face subset in the model. -/
def coordinateFaceGerm {n : ℕ} {k : Fin (n + 1)}
    (x : Orthant n k) (i : Fin n) : Filter.Germ (𝓝 x) Prop :=
  Filter.Germ.ofFun (fun y : Orthant n k => y.val i = 0)

/-- A coordinate face is considered only in its chart domain. -/
def chartFaceGerm {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart n M) (p : M) (i : Fin n) : Filter.Germ (𝓝 p) Prop :=
  Filter.Germ.ofFun (fun q => q ∈ c.2.source ∧ (c.2 q).val i = 0)

/-- Local face germs are genuine germs of subsets, rather than global boundary
components. Their equality means agreement on some neighborhood of the point. -/
def LocalFaceGerm {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (p : M) :=
  {g : Filter.Germ (𝓝 p) Prop // ∃ c ∈ S.atlas, p ∈ c.2.source ∧
    ∃ i : Fin n, i.val < c.1.val ∧ (c.2 p).val i = 0 ∧ g = chartFaceGerm c p i}

/-- The actual subset germ supplied by an active coordinate in an atlas chart. -/
def chartFaceAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (i : activeCoordinates (c.2 p)) :
    LocalFaceGerm S p :=
  ⟨chartFaceGerm c p i.val, c, hc, hp, i.val,
    (Finset.mem_filter.mp i.property).2.1,
    (Finset.mem_filter.mp i.property).2.2, rfl⟩

/-- A point of the resolved face space retains its local face germ. -/
abbrev ResolvedFaceSpace {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) := Σ p : M, LocalFaceGerm S p

def faceProjection {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) : ResolvedFaceSpace S → M := fun q => q.1

/-- One chart-face sheet, restricted by an open set of the base. -/
def faceSheet {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (i : Fin n) (U : Set M) :
    Set (ResolvedFaceSpace S) :=
  {q | q.1 ∈ U ∧ q.1 ∈ c.2.source ∧ (c.2 q.1).val i = 0 ∧
    q.2.val = chartFaceGerm c q.1 i}

/-- Local sheets are open, including at points lying on several faces. -/
@[instance_reducible] def faceSpaceTopology {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) : TopologicalSpace (ResolvedFaceSpace S) :=
  TopologicalSpace.generateFrom {s | ∃ c ∈ S.atlas, ∃ i : Fin n,
    i.val < c.1.val ∧ ∃ U : Set M, IsOpen U ∧ s = faceSheet S c i U}

instance {n : ℕ} {M : Type u} [TopologicalSpace M] (S : CornerManifold n M) :
    TopologicalSpace (ResolvedFaceSpace S) := faceSpaceTopology S

/-- A coordinate face with its subspace topology in the base chart domain. -/
abbrev ChartFacePatch {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart n M) (i : Fin n) :=
  {p : M // p ∈ c.2.source ∧ (c.2 p).val i = 0}

/-- The same coordinate-face patch in the orthant chart target. -/
abbrev ModelChartFacePatch {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart n M) (i : Fin n) :=
  {x : Orthant n c.1 // x ∈ c.2.target ∧ x.val i = 0}

/-- Inclusion of one coordinate face into the resolved face space, retaining its label. -/
def chartFaceLift {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (i : Fin n) (hi : i.val < c.1.val) : ChartFacePatch c i → ResolvedFaceSpace S :=
  fun p => ⟨p.val, ⟨chartFaceGerm c p.val i, c, hc, p.property.1, i, hi, p.property.2, rfl⟩⟩

/-- A finite disjoint family of closed coordinate faces, with the subspace
topology from model × discrete coordinate labels. -/
abbrev ModelFaceSheets (n : ℕ) (k : Fin (n + 1)) :=
  {z : Orthant n k × Fin n // z.2.val < k.val ∧ z.1.val z.2 = 0}

def modelFaceProjection {n : ℕ} {k : Fin (n + 1)} :
    ModelFaceSheets n k → Orthant n k := fun q => q.val.1

/-- Removing one constrained coordinate leaves exactly k-1 inequalities. -/
def faceConstraintCount {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) :=
  ⟨k.val - 1, by have := k.isLt; omega⟩

/-- Resolved-face coordinates delete the normal coordinate in a base chart.
The source is a whole local face sheet, rather than a depth-one stratum. -/
def IsResolvedFaceChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n + 1) M) (e : CornerChart n (ResolvedFaceSpace S)) : Prop :=
  ∃ c ∈ S.atlas, ∃ i : Fin (n + 1), i.val < c.1.val ∧
    e.1 = faceConstraintCount c.1 ∧ e.2.source = faceSheet S c i univ ∧
    ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val)

/-- A continuous map is C^r in all corner charts by local ambient extensions.
The extension is allowed to leave the target orthant off its domain. -/
def CornerMapContDiff {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞) (S : CornerManifold n M) (T : CornerManifold m N) (f : M → N) : Prop :=
  Continuous f ∧ ∀ c ∈ S.atlas, ∀ d ∈ T.atlas,
    OrthantMapContDiffOn r {x | x ∈ c.2.target ∧ f (c.2.symm x) ∈ d.2.source}
      (fun x => d.2 (f (c.2.symm x.val)))

/-- The source's ordered standard simplex, with vertices 0,e₁,...,eₙ. -/
def simplexSet (n : ℕ) : Set (Euclidean n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

abbrev Simplex (n : ℕ) := ↥(simplexSet n)

/-- Affine face functions in the vertex order, including the face opposite 0. -/
def simplexBarycentric {n : ℕ} (x : Euclidean n) : Euclidean (n + 1) :=
  Fin.cons (1 - ∑ i, x i) x

def simplexOmitBarycentric {n : ℕ} (j : Fin (n + 1)) (x : Euclidean n) : Euclidean n :=
  j.removeNth (simplexBarycentric x)

def simplexRestoreBarycentric {n : ℕ} (j : Fin (n + 1)) (y : Euclidean n) : Euclidean n :=
  Fin.tail (j.insertNth (1 - ∑ i, y i) y : Euclidean (n + 1))

/-- A closed box in the source's standard coordinate order. -/
def closedBoxSet {n : ℕ} (a b : Euclidean n) : Set (Euclidean n) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

abbrev ClosedBox {n : ℕ} (a b : Euclidean n) := ↥(closedBoxSet a b)

def boxChartSource {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) : Set (ClosedBox a b) :=
  {x | ∀ i, if ε i then a i < x.val i else x.val i < b i}

def boxCoordinate {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool)
    (x : Euclidean n) : Euclidean n :=
  fun i => if ε i then b i - x i else x i - a i

end SmoothManifolds.CornerData

namespace Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData Set

/-- Every smooth corner atlas has its canonical maximal extension. -/
def corner_atlas_extensionType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (A : Set (CornerChart n M)),
    IsSmoothCornerAtlas A →
      IsMaximalSmoothCornerAtlas (cornerMaximalExtension A) ∧ A ⊆ cornerMaximalExtension A

/-- Orthants themselves carry the corner structure generated by the identity chart. -/
def model_corner_structureType : Prop :=
  ∀ (n : ℕ) (k : Fin (n + 1)), ∃ S : CornerManifold n (Orthant n k),
    (⟨k, OpenPartialHomeomorph.refl _⟩ : CornerChart n (Orthant n k)) ∈ S.atlas

/-- Empty corner manifolds exist in every fixed dimension. -/
def empty_corner_structureType : Prop :=
  ∀ n : ℕ, Nonempty (CornerManifold n Empty)

/-- A countable subatlas suffices to cover the manifold. -/
def countable_chart_coverType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    ∃ C : Set (CornerChart n M), C.Countable ∧ C ⊆ S.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.2.source

/-- Compact chart neighborhoods are available also at multiple corners. -/
def locally_compactType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    LocallyCompactSpace M

/-- Exact velocities on every relatively open orthant patch, for both
one-sided differentiable curves and smoothly extendible curves. -/
def model_velocity_coneType : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)} (s : Set (Orthant n k)), IsOpen s →
    ∀ x ∈ s, ∀ v : Euclidean n,
      (IsForwardVelocity s x v ↔ v ∈ modelCone x) ∧
      (IsSmoothForwardVelocity s x v ↔ v ∈ modelCone x)

/-- This is the largest linear subspace contained in the velocity cone. -/
def model_linealityType : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k),
    (∀ v, v ∈ modelLineality x ↔ v ∈ modelCone x ∧ -v ∈ modelCone x) ∧
    ∀ L : Submodule ℝ (Euclidean n),
      (↑L : Set (Euclidean n)) ⊆ modelCone x → L ≤ modelLineality x

/-- Codimension is the dimension of the actual quotient, including n=0. -/
def model_lineality_codimensionType : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k),
    Module.finrank ℝ (Euclidean n ⧸ modelLineality x) = modelDepth x

/-- Every ambient representative of a smooth transition has an invertible
derivative carrying the entire one-sided cone onto the target cone. -/
def transition_coneType : Prop :=
  ∀ {n : ℕ} {k l : Fin (n + 1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l)),
    OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun z => e z.val) →
    OrthantMapContDiffOn (⊤ : ℕ∞) e.target (fun z => e.symm z.val) →
    ∀ x ∈ e.source, ∀ H : OrthantExtension e.source e x,
      ∃ E : Euclidean n ≃L[ℝ] Euclidean n,
        E.toContinuousLinearMap = fderiv ℝ H.map x.val ∧
        E '' modelCone x = modelCone (e x) ∧ modelDepth x = modelDepth (e x)

/-- Cone isomorphisms induce a bijection on active coordinate facets. The
normal component transforms by a strictly positive factor, for every vector. -/
def cone_facetsType : Prop :=
  ∀ {n : ℕ} {k l : Fin (n + 1)} (x : Orthant n k) (y : Orthant n l)
    (E : Euclidean n ≃ₗ[ℝ] Euclidean n), E '' modelCone x = modelCone y →
    ∃ σ : activeCoordinates y ≃ activeCoordinates x,
      ∃ a : activeCoordinates y → ℝ, (∀ j, 0 < a j) ∧
        (∀ v j, E v j.val = a j * v (σ j).val) ∧
        ∀ j, E '' modelFacet x (σ j) = modelFacet y j

/-- Depth computed in any two atlas charts at a point agrees. This follows
from transitions, without a chart-independence field in `CornerManifold`. -/
def chart_depthType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    (c d : CornerChart n M), c ∈ S.atlas → d ∈ S.atlas →
    ∀ p, p ∈ c.2.source → p ∈ d.2.source →
      modelDepth (c.2 p) = modelDepth (d.2 p)

/-- Distinct active coordinate faces have distinct germs, even at a multiple
corner. Thus the local sheets do not collapse to one boundary point. -/
def coordinate_germs_injectiveType : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)} (x : Orthant n k),
    Function.Injective (fun i : activeCoordinates x => coordinateFaceGerm x i.val)

/-- Transitions identify the actual local coordinate-face subset germs. -/
def chart_face_germ_transitionType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    (c d : CornerChart n M), c ∈ S.atlas → d ∈ S.atlas →
    ∀ p, p ∈ c.2.source → p ∈ d.2.source →
      ∃ σ : activeCoordinates (d.2 p) ≃ activeCoordinates (c.2 p),
        ∀ j, chartFaceGerm d p j.val = chartFaceGerm c p (σ j).val

/-- Every local face germ is represented exactly once in any chosen chart. -/
def chart_face_germsType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (p : M) (hp : p ∈ c.2.source),
      Function.Bijective (chartFaceAt S c hc p hp)

/-- The fiber of the resolved face set has exactly the intrinsic depth elements. -/
def local_face_cardinalityType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    (c : CornerChart n M), c ∈ S.atlas → ∀ p, p ∈ c.2.source →
      Finite (LocalFaceGerm S p) ∧ Nat.card (LocalFaceGerm S p) = modelDepth (c.2 p)

/-- The sheet topology makes the projection to the manifold continuous. -/
def face_projection_continuousType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    Continuous (faceProjection S)

/-- Separate germs over a single point by their distinct local sheets. -/
def resolved_face_hausdorffType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    T2Space (ResolvedFaceSpace S)

/-- A countable base atlas gives a countable base of face sheets. -/
def resolved_face_second_countableType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    SecondCountableTopology (ResolvedFaceSpace S)

/-- Each local sheet has precisely the topology of its coordinate face. -/
def face_sheet_embeddingType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (i : Fin n) (hi : i.val < c.1.val),
    Topology.IsOpenEmbedding (chartFaceLift S c hc i hi)

/-- Properness holds for the global resolved space, retaining every face germ. -/
def face_projection_properType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M),
    IsProperMap (faceProjection S)

/-- Compact support pulls back to the complete resolved face space. -/
def face_compact_supportType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold n M)
    {F : M → Type*} [∀ p, Zero (F p)] (s : ∀ p, F p),
    IsCompact (sectionSupport s) →
      IsCompact (sectionSupport (fun q : ResolvedFaceSpace S => s (faceProjection S q)))

/-- The local face charts form a smooth (n-1)-dimensional corner structure. -/
def resolved_corner_structureType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold (n + 1) M),
    ∃ T : CornerManifold n (ResolvedFaceSpace S),
      T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e}

/-- The resolved face projection is smooth for the canonical sheet structure. -/
def face_projection_smoothType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M] (S : CornerManifold (n + 1) M)
    (T : CornerManifold n (ResolvedFaceSpace S)),
    T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e} →
      CornerMapContDiff (⊤ : ℕ∞) T S (faceProjection S)

/-- The model projection is proper with the disjoint sheet topology. -/
def model_face_projection_properType : Prop :=
  ∀ (n : ℕ) (k : Fin (n + 1)),
    IsProperMap (@modelFaceProjection n k)

/-- The face set is empty for every zero-dimensional corner manifold. -/
def zero_facesType : Prop :=
  ∀ {M : Type*} [TopologicalSpace M] (S : CornerManifold 0 M),
    IsEmpty (ResolvedFaceSpace S)

/-- Coordinate deletion identifies an entire model face with an (n-1)-orthant.
Both coordinate maps have actual smooth ambient extensions. -/
def coordinate_face_chartType : Prop :=
  ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)), i.val < k.val →
    ∃ h : {x : Orthant (n + 1) k // x.val i = 0} ≃ₜ Orthant n (faceConstraintCount k),
      (∀ x j, (h x).val j = x.val.val (i.succAbove j)) ∧
      (∀ y, (h.symm y).val.val = i.insertNth 0 y.val) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean n => (i.insertNth (0 : ℝ) y : Euclidean (n + 1))) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean (n + 1) => i.removeNth x)

/-- Compact support lifts through the local resolved-face projection. Sections
may have arbitrary dependent fibers; support is closed in their base. -/
def model_face_compact_supportType : Prop :=
  ∀ {n : ℕ} {k : Fin (n + 1)} {F : Orthant n k → Type*} [∀ x, Zero (F x)]
    (s : ∀ x, F x), IsCompact (sectionSupport s) →
      IsCompact (sectionSupport (fun q : ModelFaceSheets n k => s (modelFaceProjection q)))

def simplex_corner_structureType : Prop :=
  ∀ (n : ℕ),
    ∃ S : CornerManifold n (Simplex n),
      ∃ c : Fin (n+1) → CornerChart n (Simplex n),
        (∀ j, c j ∈ S.atlas ∧ (c j).1 = Fin.last n ∧
          (c j).2.source = {x | 0 < simplexBarycentric x.val j} ∧
          (c j).2.target = {y | ∑ r, y.val r < 1} ∧
          (∀ x ∈ (c j).2.source, ((c j).2 x).val = simplexOmitBarycentric j x.val) ∧
          (∀ y ∈ (c j).2.target, ((c j).2.symm y).val = simplexRestoreBarycentric j y.val)) ∧
        (∀ x, ∃ j, x ∈ (c j).2.source) ∧
        (∀ j : Fin (n+1), ContDiff ℝ (⊤ : ℕ∞) (simplexOmitBarycentric j) ∧
          ContDiff ℝ (⊤ : ℕ∞) (simplexRestoreBarycentric j)) 

/-- The displayed ambient simplex chart formulas are actual affine equivalences. -/
def simplex_charts_affineType : Prop :=
  ∀ (n : ℕ) (j : Fin (n + 1)), ∃ A : Euclidean n ≃ᵃ[ℝ] Euclidean n,
    (∀ x, A x = simplexOmitBarycentric j x) ∧
    (∀ y, A.symm y = simplexRestoreBarycentric j y)

def box_corner_structureType : Prop :=
  ∀ (n : ℕ) (a b : Euclidean n), (∀ i, a i < b i) →
    ∃ S : CornerManifold n (ClosedBox a b), ∀ ε : Fin n → Bool,
      ∃ c ∈ S.atlas, c.1 = Fin.last n ∧ c.2.source = boxChartSource a b ε ∧
        ∀ p, (c.2 p).val = boxCoordinate a b ε p.val 

/-- The box charts cover, with explicit affine ambient maps in both directions.
The inverses agree with the displayed formula on their entire chart targets. -/
def box_corner_chartsType : Prop :=
  ∀ (n : ℕ) (a b : Euclidean n), (∀ i, a i < b i) →
    ∃ S : CornerManifold n (ClosedBox a b),
      ∃ c : (Fin n → Bool) → CornerChart n (ClosedBox a b),
        (∀ ε, c ε ∈ S.atlas ∧ (c ε).1 = Fin.last n ∧
          (c ε).2.source = boxChartSource a b ε ∧
          (c ε).2.target = {y | ∀ i, y.val i < b i - a i} ∧
          (∀ x, ((c ε).2 x).val = boxCoordinate a b ε x.val) ∧
          (∀ y ∈ (c ε).2.target, ((c ε).2.symm y).val =
            fun i => if ε i then b i - y.val i else a i + y.val i)) ∧
        (∀ x, ∃ ε, x ∈ (c ε).2.source) ∧
        (∀ ε : Fin n → Bool, ∃ A : Euclidean n ≃ᵃ[ℝ] Euclidean n,
          (∀ x, A x = boxCoordinate a b ε x) ∧
          (∀ y, A.symm y = fun i => if ε i then b i - y i else a i + y i) ∧
          ContDiff ℝ (⊤ : ℕ∞) (fun x => A x) ∧
          ContDiff ℝ (⊤ : ℕ∞) (fun y => A.symm y))

/-- The square corner really has two distinct local face germs. -/
def square_corner_two_facesType : Prop :=
  ∃ S : CornerManifold 2 (ClosedBox (0 : Euclidean 2) (fun _ => (1 : ℝ))),
    ∃ p : ClosedBox (0 : Euclidean 2) (fun _ => (1 : ℝ)),
      p.val = 0 ∧ Nat.card (LocalFaceGerm S p) = 2

end Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry
