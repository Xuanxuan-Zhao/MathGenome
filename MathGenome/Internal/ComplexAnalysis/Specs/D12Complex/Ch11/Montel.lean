import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicCompactness
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicComplete

/-! Finite-valued Montel, paper.tex:2422–2427. No connectedness or
nonemptiness is imposed on the open set. The closure is taken in actual
holomorphic functions on Ω, so representatives outside Ω are identified. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch11.Montel

/-- All sequences have one subsequence converging locally uniformly on Ω
in the ordinary complex metric to an actual finite holomorphic function. -/
def FiniteNormal (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Prop :=
  ∀ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ 𝓕) →
    ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω f ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω

/-- The image of the family under restriction to Ω. This discards all
irrelevant values outside Ω and imposes no extra regularity on its members. -/
def restrictedFamily (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Set (HolomorphicSpace Ω) :=
  {g | ∃ f ∈ 𝓕, ∀ z : Ω, g.val z = f z}

/-- Compactness of the closure for precisely the series distance of d12:11-01.
The explicit metric witness avoids imposing a global metric instance. All
metrics with this distance agree, so the witness entails no choice of topology. -/
def CompactClosure (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Prop :=
  ∃ m : MetricSpace (HolomorphicSpace Ω),
    (∀ f g, @dist _ m.toDist f g = compactOpenDistance Ω f.val g.val) ∧
    @IsCompact _ m.toUniformSpace.toTopologicalSpace
      (@closure _ m.toUniformSpace.toTopologicalSpace (restrictedFamily Ω 𝓕))

end D12Complex.Ch11.Montel

namespace Specs.D12Complex.Ch11.Montel
open _root_.D12Complex _root_.D12Complex.Ch11.Montel

def locallyBounded_iff_finiteNormal_type : Prop :=
  ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)), IsOpen Ω →
    (∀ f ∈ 𝓕, HolomorphicOn Ω f) →
      (HolomorphicCompactness.LocallyBounded_value Ω 𝓕 ↔ FiniteNormal Ω 𝓕)

def locallyBounded_iff_compactClosure_type : Prop :=
  ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)), IsOpen Ω →
    (∀ f ∈ 𝓕, HolomorphicOn Ω f) →
      (HolomorphicCompactness.LocallyBounded_value Ω 𝓕 ↔ CompactClosure Ω 𝓕)

def finiteNormal_iff_compactClosure_type : Prop :=
  ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)), IsOpen Ω →
    (∀ f ∈ 𝓕, HolomorphicOn Ω f) →
      (FiniteNormal Ω 𝓕 ↔ CompactClosure Ω 𝓕)

end Specs.D12Complex.Ch11.Montel
