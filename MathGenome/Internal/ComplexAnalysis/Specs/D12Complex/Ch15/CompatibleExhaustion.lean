import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereTopology
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactExhaustion
import Mathlib.Topology.Connected.Basic

open Set

namespace D12Complex.Ch15

/-- A closed cell of the square grid with mesh `δ` and integer coordinates. -/
def closedGridCell (δ : ℝ) (a : ℤ × ℤ) : Set ℂ :=
  {z | (a.1 : ℝ) * δ ≤ z.re ∧ z.re ≤ ((a.1 : ℝ) + 1) * δ ∧
    (a.2 : ℝ) * δ ≤ z.im ∧ z.im ≤ ((a.2 : ℝ) + 1) * δ}

def gridUnion (δ : ℝ) (s : Finset (ℤ × ℤ)) : Set ℂ :=
  ⋃ a ∈ s, closedGridCell δ a

/-- The bounded holes that lie entirely in Ω are precisely those to fill. -/
def selectedHoles (Ω L : Set ℂ) : Set (Set ℂ) :=
  {C | ∃ z ∈ Lᶜ, C = connectedComponentIn Lᶜ z ∧ Bornology.IsBounded C ∧ C ⊆ Ω}

def relativeFill (Ω L : Set ℂ) : Set ℂ := L ∪ ⋃₀ selectedHoles Ω L

/-- Each component of the *spherical* complement meets the outside of Ω. -/
def HasRelativeHoleProperty (Ω K : Set ℂ) : Prop :=
  ∀ p ∈ (sphereFinite '' K)ᶜ,
    (connectedComponentIn (sphereFinite '' K)ᶜ p ∩ (sphereFinite '' Ω)ᶜ).Nonempty

/-- A grid representation together with the prescribed selection of holes. -/
def IsFilledGrid (Ω K : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ s : Finset (ℤ × ℤ),
    gridUnion δ s ⊆ Ω ∧ K = relativeFill Ω (gridUnion δ s)

/-- All the properties of a compatible exhaustion, including eventual cofinality. -/
def IsCompatibleExhaustion (Ω : Set ℂ) (K : ℕ → Set ℂ) : Prop :=
  (∀ n, IsCompact (K n) ∧ K n ⊆ Ω ∧ HasRelativeHoleProperty Ω (K n) ∧
    IsFilledGrid Ω (K n)) ∧
  (∀ n, K n ⊆ interior (K (n + 1))) ∧
  (∀ S : Set ℂ, IsCompact S → S ⊆ Ω → ∃ N, ∀ n, N ≤ n → S ⊆ K n)

end D12Complex.Ch15

namespace Specs.D12Complex.Ch15.CompatibleExhaustion
open _root_.D12Complex.Ch15

/-- Compactness and boundary control for the finite filling in the source proof. -/
def filling_type : Prop :=
  ∀ Ω : Set ℂ, IsOpen Ω → ∀ δ : ℝ, 0 < δ → ∀ s : Finset (ℤ × ℤ),
    gridUnion δ s ⊆ Ω →
    (selectedHoles Ω (gridUnion δ s)).Finite ∧
    (∀ C ∈ selectedHoles Ω (gridUnion δ s), IsCompact (closure C) ∧ closure C ⊆ Ω) ∧
    IsCompact (relativeFill Ω (gridUnion δ s)) ∧
    relativeFill Ω (gridUnion δ s) ⊆ Ω ∧
    HasRelativeHoleProperty Ω (relativeFill Ω (gridUnion δ s))

/-- The full lemma d12:15-01; no connectedness or nonemptiness assumption. -/
def compatible_exhaustion_type : Prop :=
  ∀ Ω : Set ℂ, IsOpen Ω → ∃ K : ℕ → Set ℂ,
    K 0 = ∅ ∧ IsCompatibleExhaustion Ω K

end Specs.D12Complex.Ch15.CompatibleExhaustion
