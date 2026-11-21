import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.LchGroupInterface
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card

/-! Independent statements for paper.tex:5834–5841. The group has no
countability assumptions. A neighborhood need not itself be open.

The inverse-image convention below enumerates the same left translates,
with inverted centers. `finiteMinimalCoverStatement` explicitly checks the
bridge to image covers, existence of finite minimizers, and leastness.
Outside the finite-cover domain the natural-number infimum defaults to zero.
-/
namespace Specs.D11.Ch21.CompactCoveringRatios

open Set TopologicalSpace
open scoped Topology Pointwise
universe u

noncomputable def coveringNumberValue (G : Type u) [Group G] (K V : Set G) : ℕ :=
  sInf (Finset.card '' {t : Finset G | K ⊆ ⋃ g ∈ t, (fun x => g * x) ⁻¹' V})

def coveringNumberType : Type (u + 1) :=
  ∀ (G : Type u) [Group G], Set G → Set G → ℕ

def coveringRatioType : Type (u + 1) :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G],
    PositiveCompacts G → Set G → Compacts G → ℝ

noncomputable def coveringRatioValue : coveringRatioType.{u} :=
  fun G _ _ K₀ U K =>
    (coveringNumberValue G K U : ℝ) / coveringNumberValue G K₀ U

/-- An actual finite cover by left-translate images, attaining the least size.
This includes `V = K₀` and every identity neighborhood `V = U`. -/
def finiteMinimalCoverStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K V : Set G),
    IsCompact K → (interior V).Nonempty →
    (∃ t : Finset G, (K ⊆ ⋃ a ∈ t, (fun x => a * x) '' V) ∧
      t.card = coveringNumberValue G K V) ∧
    (∀ t : Finset G, (K ⊆ ⋃ a ∈ t, (fun x => a * x) '' V) →
      coveringNumberValue G K V ≤ t.card)

def emptyStatement : Prop :=
  ∀ (G : Type u) [Group G] (V : Set G), coveringNumberValue G ∅ V = 0

def ratiosStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (K₀ : PositiveCompacts G)
    (U : Set G), U ∈ 𝓝 (1 : G) →
    0 < coveringNumberValue G K₀ U ∧
    coveringNumberValue G K₀ K₀ = 1 ∧
    coveringRatioValue G K₀ U K₀.toCompacts = 1 ∧
    coveringRatioValue G K₀ U ⊥ = 0 ∧
    (∀ K : Compacts G, 0 ≤ coveringRatioValue G K₀ U K ∧
      coveringRatioValue G K₀ U K ≤ (coveringNumberValue G K K₀ : ℝ)) ∧
    (∀ (a : G) (K : Compacts G),
      coveringRatioValue G K₀ U (K.map (fun x => a * x) (continuous_const_mul a)) =
        coveringRatioValue G K₀ U K) ∧
    (∀ K L : Compacts G, (K : Set G) ⊆ L →
      coveringRatioValue G K₀ U K ≤ coveringRatioValue G K₀ U L) ∧
    (∀ K L : Compacts G,
      coveringRatioValue G K₀ U (K ⊔ L) ≤
        coveringRatioValue G K₀ U K + coveringRatioValue G K₀ U L) ∧
    (∀ K L : Compacts G, Disjoint ((K : Set G) * U⁻¹) ((L : Set G) * U⁻¹) →
      coveringRatioValue G K₀ U (K ⊔ L) =
        coveringRatioValue G K₀ U K + coveringRatioValue G K₀ U L)

end Specs.D11.Ch21.CompactCoveringRatios
