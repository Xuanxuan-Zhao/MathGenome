import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermTopology
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Topology.Connected.LocallyPathConnected

/-! The continuation component in d12:20-04, paper.tex:3372–3403.
The underlying set is defined by actual continuations, with no all-path
continuation or surjectivity hypothesis. All topology is the inherited germ
topology, and all complex structures use the canonical surface interface. -/

noncomputable section
open Set
open scoped Topology

namespace D12Complex.ContinuationSurface
open GermTopology Surfaces

/-- Endpoints of an actual continuous path with a locally represented germ family.
The equalities in the sigma space identify both basepoints and quotient germs. -/
def obtainable (Ω : Set ℂ) (p q : Space Ω) : Prop :=
  ∃ (γ : unitInterval → ℂ) (hγ : ∀ t, γ t ∈ Ω) (Φ : GermFamily γ),
    IsContinuation Ω γ (Φ 0) Φ ∧ lift γ hγ Φ 0 = p ∧ lift γ hγ Φ 1 = q

def continuationSet (Ω : Set ℂ) (p : Space Ω) : Set (Space Ω) :=
  {q | obtainable Ω p q}

/-- The subspace of precisely the obtainable germs. -/
abbrev Component (Ω : Set ℂ) (p : Space Ω) := ↥(continuationSet Ω p)

def projection (Ω : Set ℂ) (p : Space Ω) : Component Ω p → Ω :=
  fun q => q.val.1

def evaluation (Ω : Set ℂ) (p : Space Ω) : Component Ω p → ℂ :=
  fun q => q.val.2.value

end D12Complex.ContinuationSurface

namespace Specs.D12Complex.Ch20.ContinuationSurface
open _root_.D12Complex _root_.D12Complex.GermTopology
open _root_.D12Complex.Surfaces _root_.D12Complex.ContinuationSurface

def obtainable_type := (Ω : Set ℂ) → Space Ω → Space Ω → Prop
def obtainable_value : obtainable_type := obtainable
def continuationSet_type := (Ω : Set ℂ) → Space Ω → Set (Space Ω)
def continuationSet_value : continuationSet_type := continuationSet
def Component_type := (Ω : Set ℂ) → Space Ω → Type
def Component_value : Component_type := Component
def projection_type := (Ω : Set ℂ) → (p : Space Ω) → Component Ω p → Ω
def projection_value : projection_type := _root_.D12Complex.ContinuationSurface.projection
def evaluation_type := (Ω : Set ℂ) → (p : Space Ω) → Component Ω p → ℂ
def evaluation_value : evaluation_type := evaluation

def continuationSet_eq_pathComponent_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ p : Space Ω,
    continuationSet Ω p = pathComponent p

def continuationSet_isOpen_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ p : Space Ω, IsOpen (continuationSet Ω p)

def germSpace_hausdorff_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → T2Space (Space Ω)

def component_connected_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ p : Space Ω, ConnectedSpace (Component Ω p)

/-- A countable covering atlas consisting of projection coordinates. The target
of every chart is an actual plane domain, as required by `ComplexChart`. -/
def countable_projection_atlas_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ p : Space Ω,
    ∃ A : Set (ComplexChart (Component Ω p)), A.Countable ∧ IsAtlas A ∧
      ∀ e ∈ A, ∀ q ∈ e.val.source,
        e.val q = (_root_.D12Complex.ContinuationSurface.projection Ω p q : ℂ)

/-- All the structure and map conclusions, using the same complex structure.
Second countability and nonemptiness are fields of `RiemannSurface`, not premises. -/
def continuation_surface_type : Prop :=
  ∀ (Ω : Set ℂ) (hΩ : IsDomain Ω) (p : Space Ω),
    ∃ (S : RiemannSurface (Component Ω p)) (T : RiemannSurface Ω),
      S.atlas.Countable ∧ T.atlas = {planeChart Ω hΩ} ∧
      (∀ e ∈ S.atlas, ∀ q ∈ e.val.source,
        e.val q = (_root_.D12Complex.ContinuationSurface.projection Ω p q : ℂ)) ∧
      HolomorphicMap S T (_root_.D12Complex.ContinuationSurface.projection Ω p) ∧
      (∀ q, LocallyBiholomorphicAt S T
        (_root_.D12Complex.ContinuationSurface.projection Ω p) q) ∧
      ScalarHolomorphic S (evaluation Ω p)

end Specs.D12Complex.Ch20.ContinuationSurface
