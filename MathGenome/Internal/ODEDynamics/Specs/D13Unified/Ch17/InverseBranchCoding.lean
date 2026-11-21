import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.InverseCodingConstruction
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The complete conclusion of paper.tex, Theorem `d13:17:inverse-branch-coding`.
The finite-level union and its intersection are the canonical upstream objects;
`levelSet_finiteWordsStatement` identifies them with the finite-word formula.
Compactness implies the finite-diameter hypothesis. The common contraction
constant is nonnegative and may be zero. No forward self-map of all of K, or
extension of the given local F, is assumed.

The restriction is exhibited as a self-map f of the exact intersection, with
its value proved equal to the given F. Its surjectivity and the range equality
state invariance. Chaos uses the metric induced from K, and strict sensitivity.
The ambient form handles a compact subset and F valued in the ambient space;
the nested subtype has precisely the ambient induced metric.
-/
namespace Specs.D13Unified.Ch17.InverseBranchCoding
open Set Topology NNReal
open Specs.D13Unified.Ch17.ShiftSpaces
open Specs.D13Unified.Ch17.InverseCodingConstruction
open Specs.D13Unified.Ch17.ChaosDefinitions

/-- Topological properties of the canonical intersection, before choosing F. -/
def limitSet_topologyStatement : Prop :=
  ∀ {K : Type} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    IsCompact (limitSet b) ∧
    (∀ x : limitSet b, ∀ V ∈ 𝓝 x, ∃ y ∈ V, y ≠ x) ∧
    TotallyDisconnectedSpace (limitSet b)

/-- Intrinsic compact metric space version, including the original local F. -/
def inverse_branch_codingStatement : Prop :=
  ∀ {K : Type} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    ∀ (U : Set K), IsOpen U → ∀ (F : U → K), Continuous F →
    ∀ (hbU : ∀ i x, b i x ∈ U),
    (∀ i x, F ⟨b i x, hbU i x⟩ = x) →
    IsCompact (limitSet b) ∧
    (∀ x : limitSet b, ∀ V ∈ 𝓝 x, ∃ y ∈ V, y ≠ x) ∧
    TotallyDisconnectedSpace (limitSet b) ∧
    ∃ (hΛ : limitSet b ⊆ U) (f : limitSet b → limitSet b)
      (π : OneSided ≃ₜ limitSet b),
      (∀ x, (f x : K) = F ⟨(x : K), hΛ x.property⟩) ∧
      Continuous f ∧ Function.Surjective f ∧
      Set.range (fun x : limitSet b => F ⟨(x : K), hΛ x.property⟩) = limitSet b ∧
      (∀ s, f (π s) = π (shiftPlus s)) ∧
      (∀ s, (⋂ n : ℕ, cylinderImage b s n) = {(π s : K)}) ∧
      Chaotic f

/-- A compact subset of an arbitrary ambient metric space, with no assumption
that F maps its whole neighborhood into K. -/
def ambient_inverse_branch_codingStatement : Prop :=
  ∀ {X : Type} [MetricSpace X] (K : Set X), IsCompact K → K.Nonempty →
    ∀ (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    ∀ (U : Set X), IsOpen U → ∀ (F : U → X), Continuous F →
    ∀ (hbU : ∀ i x, (b i x : X) ∈ U),
    (∀ i x, F ⟨(b i x : X), hbU i x⟩ = (x : X)) →
    IsCompact (Subtype.val '' limitSet b : Set X) ∧
    (∀ x : limitSet b, ∀ V ∈ 𝓝 x, ∃ y ∈ V, y ≠ x) ∧
    TotallyDisconnectedSpace (limitSet b) ∧
    ∃ (hΛ : ∀ x : limitSet b, ((x : K) : X) ∈ U)
      (f : limitSet b → limitSet b) (π : OneSided ≃ₜ limitSet b),
      (∀ x, ((f x : K) : X) = F ⟨((x : K) : X), hΛ x⟩) ∧
      Continuous f ∧ Function.Surjective f ∧
      Set.range (fun x : limitSet b => F ⟨((x : K) : X), hΛ x⟩) =
        Subtype.val '' limitSet b ∧
      (∀ s, f (π s) = π (shiftPlus s)) ∧
      (∀ s, (⋂ n : ℕ, cylinderImage b s n) = {(π s : K)}) ∧
      Chaotic f

end Specs.D13Unified.Ch17.InverseBranchCoding
