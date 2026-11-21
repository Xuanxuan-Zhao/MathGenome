import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Analytic free arcs, paper.tex:2502–2507. A parametrization is given on
an open complex neighborhood, rather than by assumed boundary derivatives of
the map being extended. The upper side specifies the orientation of an arc;
reversing the real parameter interchanges its two sides. All assertions are
local at arbitrary real points of the parameter neighborhood. -/
noncomputable section
namespace D12Complex.AnalyticArcs
open Set

def side (U : Set ℂ) : Set ℂ := U ∩ {z | 0 < z.im}
def sideClosure (U : Set ℂ) : Set ℂ := U ∩ {z | 0 ≤ z.im}
def realTrace (U : Set ℂ) : Set ℂ := U ∩ {z | z.im = 0}

/-- A regular analytic parametrization; no inverse is assumed. -/
def RegularParam (U : Set ℂ) (γ : ℂ → ℂ) : Prop :=
  HolomorphicOn U γ ∧ InjOn γ U ∧ ∀ z ∈ U, deriv γ z ≠ 0

/-- A local extension agrees also with the given values on the arc. -/
def ExtendsAcross (U : Set ℂ) (γ f : ℂ → ℂ) (a : ℂ)
    (W : Set ℂ) (F : ℂ → ℂ) : Prop :=
  γ a ∈ W ∧ HolomorphicOn W F ∧ W ⊆ γ '' U ∧
    EqOn F f (W ∩ γ '' sideClosure U)

/-- `true` reverses the parameter; its positive side is the original lower side. -/
def coordinate (reverse : Bool) (z : ℂ) : ℂ := if reverse then -z else z

def sideFor (reverse : Bool) (U : Set ℂ) : Set ℂ :=
  U ∩ {z | 0 < (coordinate reverse z).im}

def closureFor (reverse : Bool) (U : Set ℂ) : Set ℂ :=
  U ∩ {z | 0 ≤ (coordinate reverse z).im}

def ExtendsAcrossFor (reverse : Bool) (U : Set ℂ) (γ f : ℂ → ℂ) (a : ℂ)
    (W : Set ℂ) (F : ℂ → ℂ) : Prop :=
  γ a ∈ W ∧ HolomorphicOn W F ∧ W ⊆ γ '' U ∧
    EqOn F f (W ∩ γ '' closureFor reverse U)

end D12Complex.AnalyticArcs

namespace Specs.D12Complex.Ch12.AnalyticArcs
open _root_.D12Complex _root_.D12Complex.AnalyticArcs Set

def side_type := Set ℂ → Set ℂ
def side_value : side_type := fun U => U ∩ {z | 0 < z.im}
def sideClosure_type := Set ℂ → Set ℂ
def sideClosure_value : sideClosure_type := fun U => U ∩ {z | 0 ≤ z.im}
def realTrace_type := Set ℂ → Set ℂ
def realTrace_value : realTrace_type := fun U => U ∩ {z | z.im = 0}
def RegularParam_type := Set ℂ → (ℂ → ℂ) → Prop
def RegularParam_value : RegularParam_type := fun U γ =>
  HolomorphicOn U γ ∧ InjOn γ U ∧ ∀ z ∈ U, deriv γ z ≠ 0

def ExtendsAcross_type := Set ℂ → (ℂ → ℂ) → (ℂ → ℂ) → ℂ → Set ℂ → (ℂ → ℂ) → Prop
def ExtendsAcross_value : ExtendsAcross_type := fun U γ f a W F =>
  γ a ∈ W ∧ HolomorphicOn W F ∧ W ⊆ γ '' U ∧
    EqOn F f (W ∩ γ '' sideClosure U)

/-- Ω may be any adjacent open domain containing the indicated local side.
The target regular arc need not contain the image of the open source side. -/
def analytic_arc_extension_type : Prop :=
  ∀ (U V Ω : Set ℂ) (γ ψ f : ℂ → ℂ),
    RegularParam U γ → RegularParam V ψ →
    γ '' side U ⊆ Ω → HolomorphicOn Ω f →
    ContinuousOn f (γ '' sideClosure U) →
    MapsTo f (γ '' realTrace U) (ψ '' realTrace V) →
    ∀ a ∈ realTrace U, ∃ W F, ExtendsAcross U γ f a W F

/-- A conformal equivalence supplies an interior inverse only. Injectivity
on the boundary arc and preservation of the prescribed open sides are explicit.
The derivative at the boundary is a conclusion, never a hypothesis. -/
def analytic_arc_conformal_extension_type : Prop :=
  ∀ (U V Ω Ξ : Set ℂ) (γ ψ f g : ℂ → ℂ),
    RegularParam U γ → RegularParam V ψ →
    γ '' side U ⊆ Ω → BiholomorphicPair Ω Ξ f g →
    ContinuousOn f (γ '' sideClosure U) →
    MapsTo f (γ '' realTrace U) (ψ '' realTrace V) →
    InjOn f (γ '' realTrace U) →
    MapsTo f (γ '' side U) (ψ '' side V) →
    ∀ a ∈ realTrace U, ∃ W F,
      ExtendsAcross U γ f a W F ∧ deriv F (γ a) ≠ 0

def coordinate_type := Bool → ℂ → ℂ
def coordinate_value : coordinate_type := fun reverse z => if reverse then -z else z
def sideFor_type := Bool → Set ℂ → Set ℂ
def sideFor_value : sideFor_type := fun reverse U => U ∩ {z | 0 < (coordinate reverse z).im}
def closureFor_type := Bool → Set ℂ → Set ℂ
def closureFor_value : closureFor_type := fun reverse U => U ∩ {z | 0 ≤ (coordinate reverse z).im}
def ExtendsAcrossFor_type := Bool → Set ℂ → (ℂ → ℂ) → (ℂ → ℂ) → ℂ → Set ℂ → (ℂ → ℂ) → Prop
def ExtendsAcrossFor_value : ExtendsAcrossFor_type := fun reverse U γ f a W F =>
  γ a ∈ W ∧ HolomorphicOn W F ∧ W ⊆ γ '' U ∧
    EqOn F f (W ∩ γ '' closureFor reverse U)

/-- Either prescribed source side is allowed, without changing the original
parametrization or the original physical point in the conclusion. -/
def analytic_arc_extension_sides_type : Prop :=
  ∀ (sourceSide : Bool) (U V Ω : Set ℂ) (γ ψ f : ℂ → ℂ),
    RegularParam U γ → RegularParam V ψ →
    γ '' sideFor sourceSide U ⊆ Ω → HolomorphicOn Ω f →
    ContinuousOn f (γ '' closureFor sourceSide U) →
    MapsTo f (γ '' realTrace U) (ψ '' realTrace V) →
    ∀ a ∈ realTrace U, ∃ W F, ExtendsAcrossFor sourceSide U γ f a W F

/-- Source and target sides are independent, covering all four choices. -/
def analytic_arc_conformal_extension_sides_type : Prop :=
  ∀ (sourceSide targetSide : Bool) (U V Ω Ξ : Set ℂ) (γ ψ f g : ℂ → ℂ),
    RegularParam U γ → RegularParam V ψ →
    γ '' sideFor sourceSide U ⊆ Ω → BiholomorphicPair Ω Ξ f g →
    ContinuousOn f (γ '' closureFor sourceSide U) →
    MapsTo f (γ '' realTrace U) (ψ '' realTrace V) →
    InjOn f (γ '' realTrace U) →
    MapsTo f (γ '' sideFor sourceSide U) (ψ '' sideFor targetSide V) →
    ∀ a ∈ realTrace U, ∃ W F,
      ExtendsAcrossFor sourceSide U γ f a W F ∧ deriv F (γ a) ≠ 0

end Specs.D12Complex.Ch12.AnalyticArcs
