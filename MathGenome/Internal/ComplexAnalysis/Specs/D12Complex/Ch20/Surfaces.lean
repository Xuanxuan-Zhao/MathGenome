import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Connected.PathConnected

/-! Canonical interfaces for paper.tex:3311–3323. Chart images are nonempty
connected open plane sets. Overlap images need not be connected or nonempty.
All transition regularity uses the project's weak holomorphy predicate. -/

noncomputable section
open Set

namespace D12Complex.Surfaces

universe u

/-- A homeomorphism from an open subset of X onto a plane domain. -/
abbrev ComplexChart (X : Type u) [TopologicalSpace X] :=
  {e : OpenPartialHomeomorph X ℂ // D12Complex.IsDomain e.target}

/-- Compatibility includes holomorphy of both directions on the actual overlap. -/
def CompatibleCharts {X : Type u} [TopologicalSpace X] (e f : ComplexChart X) : Prop :=
  let t := e.val.symm.trans f.val
  D12Complex.BiholomorphicPair t.source t.target t t.symm

/-- An atlas covers the space and every ordered pair of charts is compatible. -/
def IsAtlas {X : Type u} [TopologicalSpace X] (A : Set (ComplexChart X)) : Prop :=
  (∀ x : X, ∃ e ∈ A, x ∈ e.val.source) ∧
  ∀ e ∈ A, ∀ f ∈ A, CompatibleCharts e f

/-- Cross compatibility of two atlases; the individual atlas conditions are separate. -/
def CompatibleAtlases {X : Type u} [TopologicalSpace X]
    (A B : Set (ComplexChart X)) : Prop :=
  ∀ e ∈ A, ∀ f ∈ B, CompatibleCharts e f

/-- All domain charts compatible with the given atlas. -/
def maximalAtlas {X : Type u} [TopologicalSpace X]
    (A : Set (ComplexChart X)) : Set (ComplexChart X) :=
  {e | ∀ f ∈ A, CompatibleCharts e f}

/-- Maximality among atlases, by inclusion. -/
def IsMaximalAtlas {X : Type u} [TopologicalSpace X]
    (A : Set (ComplexChart X)) : Prop :=
  IsAtlas A ∧ ∀ B, IsAtlas B → A ⊆ B → B = A

/-- A surface has all the separation, countability, and connectedness hypotheses
of the source. `ConnectedSpace` includes nonemptiness. The atlas is data. -/
structure RiemannSurface (X : Type u) [TopologicalSpace X] where
  connected : ConnectedSpace X
  hausdorff : T2Space X
  secondCountable : SecondCountableTopology X
  atlas : Set (ComplexChart X)
  isAtlas : IsAtlas atlas

/-- The identity coordinate on a plane domain, represented on its subtype. -/
def planeChart (Ω : Set ℂ) (hΩ : D12Complex.IsDomain Ω) : ComplexChart Ω := by
  letI : Nonempty Ω := hΩ.1.to_subtype
  let e := hΩ.2.1.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : Ω → ℂ)
  refine ⟨e, ?_⟩
  simpa only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Subtype.range_coe_subtype, ofPred_mem_eq] using hΩ

end D12Complex.Surfaces

namespace Specs.D12Complex.Ch20.Surfaces

open _root_.D12Complex _root_.D12Complex.Surfaces
universe u v

-- Definition contracts. The canonical objects above are shared with later Specs.
def ComplexChart_type := (X : Type u) → [TopologicalSpace X] → Type u
def ComplexChart_value : ComplexChart_type := fun X _ =>
  {e : OpenPartialHomeomorph X ℂ // IsDomain e.target}

def CompatibleCharts_type := {X : Type u} → [TopologicalSpace X] →
  ComplexChart X → ComplexChart X → Prop
def CompatibleCharts_value : CompatibleCharts_type := fun e f =>
  let t := e.val.symm.trans f.val
  BiholomorphicPair t.source t.target t t.symm

def IsAtlas_type := {X : Type u} → [TopologicalSpace X] → Set (ComplexChart X) → Prop
def IsAtlas_value : IsAtlas_type := fun A =>
  (∀ x, ∃ e ∈ A, x ∈ e.val.source) ∧ ∀ e ∈ A, ∀ f ∈ A, CompatibleCharts e f

def CompatibleAtlases_type := {X : Type u} → [TopologicalSpace X] →
  Set (ComplexChart X) → Set (ComplexChart X) → Prop
def CompatibleAtlases_value : CompatibleAtlases_type := fun A B =>
  ∀ e ∈ A, ∀ f ∈ B, CompatibleCharts e f

def maximalAtlas_type := {X : Type u} → [TopologicalSpace X] →
  Set (ComplexChart X) → Set (ComplexChart X)
def maximalAtlas_value : maximalAtlas_type := fun A => {e | ∀ f ∈ A, CompatibleCharts e f}

def IsMaximalAtlas_type := {X : Type u} → [TopologicalSpace X] → Set (ComplexChart X) → Prop
def IsMaximalAtlas_value : IsMaximalAtlas_type := fun A =>
  IsAtlas A ∧ ∀ B, IsAtlas B → A ⊆ B → B = A

def RiemannSurface_type := (X : Type u) → [TopologicalSpace X] → Type u
def RiemannSurface_value : RiemannSurface_type := @RiemannSurface

def planeChart_type := (Ω : Set ℂ) → IsDomain Ω → ComplexChart Ω
def planeChart_value : planeChart_type := planeChart

def compatibleCharts_symm_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {e f : ComplexChart X},
    CompatibleCharts e f → CompatibleCharts f e

def compatibleCharts_refl_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (e : ComplexChart X), CompatibleCharts e e

def atlas_union_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A B : Set (ComplexChart X)},
    IsAtlas A → IsAtlas B → CompatibleAtlases A B → IsAtlas (A ∪ B)

def atlas_iUnion_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {ι : Type v} [Nonempty ι]
    (A : ι → Set (ComplexChart X)),
    (∀ i, IsAtlas (A i)) → (∀ i j, CompatibleAtlases (A i) (A j)) → IsAtlas (⋃ i, A i)

def subset_maximalAtlas_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A : Set (ComplexChart X)},
    IsAtlas A → A ⊆ maximalAtlas A

def maximalAtlas_isAtlas_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A : Set (ComplexChart X)},
    IsAtlas A → IsAtlas (maximalAtlas A)

def maximalAtlas_isMaximal_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A : Set (ComplexChart X)},
    IsAtlas A → IsMaximalAtlas (maximalAtlas A)

def maximalAtlas_unique_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A : Set (ComplexChart X)},
    IsAtlas A → ∃! B, IsMaximalAtlas B ∧ A ⊆ B

def compatibleAtlases_iff_maximalAtlas_eq_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A B : Set (ComplexChart X)},
    IsAtlas A → IsAtlas B → (CompatibleAtlases A B ↔ maximalAtlas A = maximalAtlas B)

def surface_pathConnected_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], RiemannSurface X → PathConnectedSpace X

def planeChart_apply_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsDomain Ω) (z : Ω), (planeChart Ω hΩ).val z = (z : ℂ)

def planeChart_source_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsDomain Ω), (planeChart Ω hΩ).val.source = Set.univ

def planeChart_target_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsDomain Ω), (planeChart Ω hΩ).val.target = Ω

def plane_domain_surface_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsDomain Ω),
    ∃ S : RiemannSurface Ω, S.atlas = {planeChart Ω hΩ}

def plane_surface_iff_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → (Nonempty (RiemannSurface Ω) ↔ IsDomain Ω)

def open_components_surfaces_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω →
    (Ω = ⋃ z ∈ Ω, connectedComponentIn Ω z) ∧
    ∀ z ∈ Ω, IsDomain (connectedComponentIn Ω z) ∧
      Nonempty (RiemannSurface (connectedComponentIn Ω z))

end Specs.D12Complex.Ch20.Surfaces
