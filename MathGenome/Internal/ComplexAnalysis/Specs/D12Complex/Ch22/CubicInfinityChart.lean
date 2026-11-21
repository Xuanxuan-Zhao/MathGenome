import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.CubicFiniteCharts
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Analysis.Asymptotics.Defs

/-! The infinity chart of the literal projective cubic (paper.tex:3983–3994).
The complex atlas is constructed before, and without, connectedness. -/
noncomputable section
open Set Filter Topology
open scoped Topology

namespace D12Complex.CubicInfinityChart
open ProjectivePlaneTopology CubicFiniteCharts

/-- The point [0:0:1], in the fixed coordinate order Z,X,Y. -/
def O : ComplexProjectivePlane := affineParam 2 ![0,0]
def infinityU : ComplexProjectivePlane → ℂ := coordinateRatio 2 1
def infinityV : ComplexProjectivePlane → ℂ := coordinateRatio 2 0
def infinityPoint (u v : ℂ) : ComplexProjectivePlane := affineParam 2 ![v,u]
def infinityPatch (G H : ℂ) : Set (Cubic G H) :=
  {p | p.val ∈ coordinatePatch 2}

/-- An actual u-coordinate chart with holomorphic inverse ambient coordinates. -/
def IsInfinityChart (G H : ℂ)
    (e : OpenPartialHomeomorph (Cubic G H) ℂ) : Prop :=
  e.source ⊆ infinityPatch G H ∧
  (∀ p ∈ e.source, e p = infinityU p.val) ∧
  HolomorphicOn e.target (fun z => infinityU (e.symm z).val) ∧
  HolomorphicOn e.target (fun z => infinityV (e.symm z).val)

end D12Complex.CubicInfinityChart

namespace Specs.D12Complex.Ch22.CubicInfinityChart
open _root_.D12Complex _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.CubicInfinityChart _root_.D12Complex.ProjectivePlaneTopology
open _root_.D12Complex.Surfaces
open WeierstrassEquations (g₂ g₃)

def O_type := ComplexProjectivePlane
def O_value : O_type := affineParam 2 ![0,0]
def infinityU_type := ComplexProjectivePlane → ℂ
def infinityU_value : infinityU_type := coordinateRatio 2 1
def infinityV_type := ComplexProjectivePlane → ℂ
def infinityV_value : infinityV_type := coordinateRatio 2 0
def infinityPoint_type := ℂ → ℂ → ComplexProjectivePlane
def infinityPoint_value : infinityPoint_type := fun u v => affineParam 2 ![v,u]
def infinityPatch_type := (G H : ℂ) → Set (Cubic G H)
def infinityPatch_value : infinityPatch_type := fun _ _ => {p | p.val ∈ coordinatePatch 2}
def IsInfinityChart_type := (G H : ℂ) → OpenPartialHomeomorph (Cubic G H) ℂ → Prop
def IsInfinityChart_value : IsInfinityChart_type := fun G H e =>
  e.source ⊆ infinityPatch G H ∧
  (∀ p ∈ e.source, e p = infinityU p.val) ∧
  HolomorphicOn e.target (fun z => infinityU (e.symm z).val) ∧
  HolomorphicOn e.target (fun z => infinityV (e.symm z).val)

def unique_infinity_type : Prop := ∀ G H : ℂ,
  OnCubic G H O ∧ O ∉ coordinatePatch 0 ∧
  ∀ p, OnCubic G H p → (p ∉ coordinatePatch 0 ↔ p = O)

def infinity_equation_type : Prop := ∀ G H p,
  p ∈ coordinatePatch 2 →
  (OnCubic G H p ↔ infinityV p =
    4 * infinityU p ^ 3 - G * infinityU p * infinityV p ^ 2 - H * infinityV p ^ 3)

/-- The nonzero partial derivative of the local defining equation at O. -/
def nonsingular_infinity_type : Prop := ∀ G H : ℂ,
  HasDerivAt (fun v : ℂ => v - 4 * (0 : ℂ) ^ 3 + G * 0 * v ^ 2 + H * v ^ 3)
    1 0 ∧ (1 : ℂ) ≠ 0

def infinity_graph_type : Prop := ∀ G H : ℂ,
  ∃ (U W : Set ℂ) (V : ℂ → ℂ),
    IsOpen U ∧ (0 : ℂ) ∈ U ∧ IsOpen W ∧ (0 : ℂ) ∈ W ∧
    HolomorphicOn U V ∧ V 0 = 0 ∧ MapsTo V U W ∧
    (∀ u ∈ U, ∀ v ∈ W, v = 4*u^3-G*u*v^2-H*v^3 ↔ v = V u) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun u => V u - 4*u^3) (fun u => u^7)

def infinity_chart_type : Prop := ∀ G H : ℂ,
  ∃ (U W : Set ℂ) (V : ℂ → ℂ)
    (e : OpenPartialHomeomorph (Cubic G H) ℂ),
    IsOpen U ∧ (0 : ℂ) ∈ U ∧ IsOpen W ∧ (0 : ℂ) ∈ W ∧
    HolomorphicOn U V ∧ V 0 = 0 ∧ MapsTo V U W ∧
    (∀ u ∈ U, ∀ v ∈ W, v = 4*u^3-G*u*v^2-H*v^3 ↔ v = V u) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun u => V u - 4*u^3) (fun u => u^7) ∧
    IsInfinityChart G H e ∧ e.target = U ∧
    e.source = {p | p ∈ infinityPatch G H ∧ infinityU p.val ∈ U ∧ infinityV p.val ∈ W} ∧
    (∀ u ∈ U, (e.symm u).val = infinityPoint u (V u)) ∧
    (∀ p : Cubic G H, p.val = O → p ∈ e.source ∧ e p = 0)

def finite_infinity_transitions_type : Prop :=
  ∀ G H axis (e f : OpenPartialHomeomorph (Cubic G H) ℂ),
    IsFiniteChart G H axis e → IsInfinityChart G H f →
    let t := e.symm.trans f
    BiholomorphicPair t.source t.target t t.symm

def infinity_transitions_type : Prop :=
  ∀ G H (e f : OpenPartialHomeomorph (Cubic G H) ℂ),
    IsInfinityChart G H e → IsInfinityChart G H f →
    let t := e.symm.trans f
    BiholomorphicPair t.source t.target t t.symm

/-- A nonempty compact complex one-manifold, with no connectedness premise. -/
def complex_manifold_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    let E := Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)
    Nonempty E ∧ CompactSpace E ∧ T2Space E ∧ SecondCountableTopology E ∧
    ∃ A : Set (ComplexChart E), IsAtlas A ∧
      ∀ e ∈ A, IsInfinityChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) e.val ∨
        ∃ axis, IsFiniteChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) axis e.val

end Specs.D12Complex.Ch22.CubicInfinityChart
