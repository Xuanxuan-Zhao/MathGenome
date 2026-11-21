import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Homeomorph.Lemmas

/-! The ACL characterization on arbitrary open Euclidean sets. The transverse
parameter has exactly d-1 coordinates. In dimension zero there are no coordinate
conditions. All line statements refer to ONE representative of the original Lp
class. There are no assumptions about the boundary or the finiteness of p. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Sobolev.Lines
open ExpandedFA.Distributions

/-- The coordinates transverse to the i-th axis, with their usual product volume. -/
abbrev Transverse {d : ℕ} (i : Fin d) := {j : Fin d // j ≠ i} → ℝ

/-- Insert the varying coordinate into a transverse point. -/
def coordinateLine {d : ℕ} (i : Fin d) (y : Transverse i) (t : ℝ) : Domain d :=
  fun j => if h : j = i then t else y ⟨j, h⟩

/-- The open fiber can have arbitrarily many connected components. -/
def fiber {d : ℕ} (Ω : Opens (Domain d)) (i : Fin d) (y : Transverse i) : Opens ℝ :=
  ⟨coordinateLine i y ⁻¹' (Ω : Set (Domain d)),
    Ω.isOpen.preimage (continuous_pi fun j => by
      dsimp [coordinateLine]
      split_ifs <;> first | exact continuous_id | exact continuous_const)⟩

/-- AC on every compact interval contained in the open set. This does not
assert AC across a gap in a disconnected fiber or impose endpoint conditions. -/
def LocallyAbsolutelyContinuousOn {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → 𝕜) (U : Set ℝ) : Prop :=
  ∀ a b : ℝ, uIcc a b ⊆ U → AbsolutelyContinuousOnInterval f a b

/-- A single function is ACL in every coordinate, with the indicated Lp
classes as its classical line derivatives. The exceptional transverse set may
depend on the coordinate, but not on the compact subinterval. -/
def HasACLDerivatives {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (g : Fin d → DomainLp 𝕜 Ω p) : Prop :=
  ∀ i : Fin d, ∀ᵐ y : Transverse i ∂volume,
    LocallyAbsolutelyContinuousOn (fun t => f (coordinateLine i y t)) (fiber Ω i y) ∧
    ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
      HasDerivAt (fun s => f (coordinateLine i y s)) (g i (coordinateLine i y t)) t

/-- Coordinate form of the accepted scalar-linear distributional derivative. -/
def HasWeakCoordinateDerivatives {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p) : Prop :=
  ∀ i, lpDistribution (g i) = -(lpDistribution u).comp (testPartialCLM [i])

end ExpandedFA.Sobolev.Lines

namespace Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.Distributions

/-- The precise derivative version also identifies the line derivatives with
the actual weak derivatives, rather than merely asserting some Lp bounds. -/
def DerivativeCharacterization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (d : ℕ) (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p),
  HasWeakCoordinateDerivatives u g ↔
    ∃ f : Domain d → 𝕜,
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧ HasACLDerivatives Ω f g

/-- Membership in the original derivative graph, for all d and 1 ≤ p ≤ ∞. -/
def MembershipCharacterization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (d : ℕ) (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p),
  (∃ v : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p,
      v.val (zeroIndex d 1) = u) ↔
    ∃ (f : Domain d → 𝕜) (g : Fin d → DomainLp 𝕜 Ω p),
      u =ᵐ[volume.restrict (Ω : Set (Domain d))] f ∧ HasACLDerivatives Ω f g

end Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
