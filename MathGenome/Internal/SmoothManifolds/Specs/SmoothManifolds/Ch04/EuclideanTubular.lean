import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.EmbeddedComparison
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.Compact

/-! Independent objects and complete statement for M04.04, paper.tex:1221–1226.
The domain is any boundaryless smooth manifold embedded by `j`. In particular
`M` may be the underlying subset of Euclidean space and `j` its inclusion.
No closedness, compactness, connectedness, or nonemptiness is imposed.

The coordinate space has its existing sup norm. Orthogonality below is the
ordinary Euclidean dot product, independent of that choice of norm.
-/
namespace SmoothManifolds.EuclideanTubularData
open ModelData AtlasData MapData EmbeddedData FiniteRegularityData Set

variable {n q : ℕ} {M : Type} [TopologicalSpace M]

/-- A chart of the actual maximal atlas, chosen at the given point. -/
noncomputable def tangentChart (S : SmoothManifold n .euclidean M) (p : M) :
    ModelChart n .euclidean M := Classical.choose (S.smoothStructure.property.1.1 p)

/-- Image of the inclusion differential in ambient standard coordinates.
Chart independence is a theorem, not an input certificate. -/
noncomputable def ambientTangent (S : SmoothManifold n .euclidean M)
    (j : M → Euclidean q) (p : M) : Submodule ℝ (Euclidean q) :=
  LinearMap.range (chartDerivative (tangentChart S p) (euclideanChart q) j p).toLinearMap

/-- Orthogonal complement for the standard positive definite dot product. -/
def dotOrthogonal (E : Submodule ℝ (Euclidean q)) : Submodule ℝ (Euclidean q) where
  carrier := {v | ∀ w ∈ E, dotProduct v w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v u hv hu w hw
    simp only [add_dotProduct, hv w hw, hu w hw, add_zero]
  smul_mem' := by
    intro a v hv w hw
    simp only [smul_dotProduct, hv w hw, smul_zero]

noncomputable def normalFiber (S : SmoothManifold n .euclidean M)
    (j : M → Euclidean q) (p : M) : Submodule ℝ (Euclidean q) :=
  dotOrthogonal (ambientTangent S j p)

/-- The total space has the subspace topology of `M × ℝ^q`. -/
abbrev NormalTotal (S : SmoothManifold n .euclidean M) (j : M → Euclidean q) :=
  {z : M × Euclidean q // z.2 ∈ normalFiber S j z.1}

def normalZero (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (p : M) : NormalTotal S j := ⟨(p, 0), (normalFiber S j p).zero_mem⟩

def normalScale (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (t : ℝ) (z : NormalTotal S j) : NormalTotal S j :=
  ⟨(z.val.1, t • z.val.2), (normalFiber S j z.val.1).smul_mem t z.property⟩

def normalAddition (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (z : NormalTotal S j) : Euclidean q := j z.val.1 + z.val.2

/-- Maximal radial core; compactness of the parameter interval makes it open
whenever `V` is open. It avoids any uniform-radius or compact-base assumption. -/
def radialCore (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (V : Set (NormalTotal S j)) : Set (NormalTotal S j) :=
  {z | ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V}

/-- Smooth linear bundle charts over charts of the original base. Their source
is the entire normal fiber over the base chart, and the coordinate formula is
linear in the normal vector. Thus this specifies a smooth normal vector bundle,
rather than just an unrelated smooth structure on its total space.
The family `b` only has to be smooth on the displayed base chart.
The dimension-zero and empty-base cases are included. -/
def IsNormalBundleStructure (S : SmoothManifold n .euclidean M)
    (j : M → Euclidean q) (N : SmoothManifold q .euclidean (NormalTotal S j)) : Prop :=
  IsSmoothMap N S (fun z => z.val.1) ∧ IsSmoothMap S N (normalZero S j) ∧
  (∀ z, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) N.smoothStructure.val
    (fun z => z.val.2) z) ∧
  ∀ p : M, ∃ (e : ModelChart n .euclidean M),
    e ∈ S.smoothStructure.val ∧ p ∈ e.source ∧
    ∃ (C : (Euclidean n × Euclidean (q - n)) ≃L[ℝ] Euclidean q)
      (b : ∀ x : M, Euclidean (q - n) ≃ₗ[ℝ] normalFiber S j x)
      (h : ModelChart q .euclidean (NormalTotal S j)),
      h ∈ N.smoothStructure.val ∧ h.source = (fun z => z.val.1) ⁻¹' e.source ∧
      h.target = {y | (C.symm y.val).1 ∈ Subtype.val '' e.target} ∧
      (∀ z ∈ h.source,
        (h z).val = C ((e z.val.1).val, (b z.val.1).symm ⟨z.val.2, z.property⟩)) ∧
      ∀ (v : Euclidean (q - n)) (x : M), x ∈ e.source →
        ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
          (fun x => (b x v).val) x

/-- Full tubular data, including the smooth strong deformation retraction.
Smoothness on the closed time interval means ambient local smooth extension,
as required by the manuscript's convention, and includes both endpoints. -/
def IsTubularNeighborhood (S : SmoothManifold n .euclidean M)
    (T : SmoothManifold q .euclidean (Euclidean q)) (j : M → Euclidean q)
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
    (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W) : Prop :=
  (∀ p, normalZero S j p ∈ V) ∧
  (∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V) ∧
  (∀ z : V, (h z).val = normalAddition S j z.val) ∧ range j ⊆ W ∧
  ManifoldSmooth (openSubsetAtlas N.smoothStructure.val V hV)
    (openSubsetAtlas T.smoothStructure.val W hW) h ∧
  ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
    (openSubsetAtlas N.smoothStructure.val V hV) h.symm ∧
  ∃ (r : W → M) (H : Icc (0 : ℝ) 1 × W → W),
    ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      S.smoothStructure.val r ∧
    (∀ y, r y = (h.symm y).val.val.1) ∧
    (∀ p, ∀ hp : j p ∈ W, r ⟨j p, hp⟩ = p) ∧
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun z : Icc (0 : ℝ) 1 × W => Fin.cons z.1.val z.2.val)
      (fun z => (H z).val) ∧
    (∀ t y, (H (t, y)).val = normalAddition S j
      (normalScale S j (1 - t.val) (h.symm y).val)) ∧
    (∀ y, H (⟨0, le_rfl, zero_le_one⟩, y) = y) ∧
    (∀ y, (H (⟨1, zero_le_one, le_rfl⟩, y)).val = j (r y)) ∧
    (∀ t p, ∀ hp : j p ∈ W, (H (t, ⟨j p, hp⟩)).val = j p)

end SmoothManifolds.EuclideanTubularData

namespace Specs.SmoothManifolds.Ch04.EuclideanTubular
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.EmbeddedData _root_.SmoothManifolds.FiniteRegularityData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.EuclideanTubularData Set

def ambientTangent_eq_chartType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    euclideanChart q ∈ T.smoothStructure.val → IsSmoothMap S T j →
    ∀ (p : M) (e : ModelChart n .euclidean M),
    e ∈ S.smoothStructure.val → p ∈ e.source →
    ambientTangent S j p = LinearMap.range (chartDerivative e (euclideanChart q) j p).toLinearMap

def normalFiber_finrankType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    euclideanChart q ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∀ p : M, Module.finrank ℝ (normalFiber S j p) = q - n

def ambientTangent_eq_differentialType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    euclideanChart q ∈ T.smoothStructure.val → IsSmoothMap S T j →
    ∀ (p : M)
      (L : TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (j p))
      (F : TangentData.TangentSpace T (j p) ≃ₗ[ℝ] Euclidean q),
      DifferentialData.IsDifferential S T j p L →
      DifferentialData.IsChartCoordinates T (j p) (euclideanChart q) F →
      ambientTangent S j p = LinearMap.range (F.toLinearMap.comp L)

def radial_shrinkingType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (V : Set (NormalTotal S j)), IsOpen V →
    (∀ p, normalZero S j p ∈ V) →
    ∃ U : Set (NormalTotal S j), IsOpen U ∧ U ⊆ V ∧
      (∀ p, normalZero S j p ∈ U) ∧
      ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ U

def normal_global_injectiveType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    Topology.IsEmbedding j →
    (∀ p : M, ∃ V : Set (NormalTotal S j),
      IsOpen V ∧ normalZero S j p ∈ V ∧ InjOn (normalAddition S j) V) →
    ∃ V : Set (NormalTotal S j), IsOpen V ∧
      (∀ p, normalZero S j p ∈ V) ∧ InjOn (normalAddition S j) V ∧
      ∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V

/-- The derivative of actual addition is bijective in a genuine normal
bundle chart at every zero. Existence of the normal bundle is still an output
of the main theorem below. -/
def normalAddition_has_bijective_derivativeType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (N : SmoothManifold q .euclidean (NormalTotal S j)),
    euclideanChart q ∈ T.smoothStructure.val →
    IsSmoothEmbedding S T j → IsNormalBundleStructure S j N →
    ∀ p : M, ∃ h : ModelChart q .euclidean (NormalTotal S j),
      h ∈ N.smoothStructure.val ∧ normalZero S j p ∈ h.source ∧
      ∃ L : Euclidean q →L[ℝ] Euclidean q,
        HasCoordinateDerivative h (normalAddition S j) (normalZero S j p) L ∧
        Function.Bijective L

/-- The analytic, global, and deformation conclusions follow from construction
of the normal bundle; no local invertibility certificate is assumed. -/
def euclidean_tubular_of_normal_bundleType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (N : SmoothManifold q .euclidean (NormalTotal S j)),
    euclideanChart q ∈ T.smoothStructure.val →
    IsSmoothEmbedding S T j → IsNormalBundleStructure S j N →
    ∃ (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
      (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
      IsTubularNeighborhood S T j N V W hV hW h

/-- Normal bundle existence from the original smooth embedding, with the
smooth projection, zero section, vector inclusion, and linear chart data. -/
def exists_normal_bundleType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    euclideanChart q ∈ T.smoothStructure.val → IsSmoothEmbedding S T j →
    ∃ N : SmoothManifold q .euclidean (NormalTotal S j),
      IsNormalBundleStructure S j N

/-- The input is an arbitrary smooth embedding into standard Euclidean space.
The smooth normal bundle, open tubular diffeomorphism, radial invariance,
retraction, and smooth deformation are all outputs. -/
def euclidean_tubularType : Prop :=
  ∀ {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M)
    (T : SmoothManifold q .euclidean (Euclidean q)),
    euclideanChart q ∈ T.smoothStructure.val →
    ∀ j : M → Euclidean q, IsSmoothEmbedding S T j →
    ∃ N : SmoothManifold q .euclidean (NormalTotal S j),
      IsNormalBundleStructure S j N ∧
      ∃ (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
        (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
        IsTubularNeighborhood S T j N V W hV hW h

end Specs.SmoothManifolds.Ch04.EuclideanTubular
