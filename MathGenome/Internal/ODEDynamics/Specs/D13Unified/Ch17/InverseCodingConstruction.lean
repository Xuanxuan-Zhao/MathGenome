import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact

/-! The construction part of paper.tex, Theorem `d13:17:inverse-branch-coding`.
The compact metric space is a type `K` (a compact subset can be supplied as a
subtype with its induced metric). Compactness implies finite diameter.
`q : ℝ≥0` retains the boundary case q = 0. An infinite word in `levelSet`
only contributes its first n letters; `levelSet_finiteWordsStatement` makes
its equality with the finite-word union explicit.

The local forward map really has domain `U`, not all of K. No extension of
its continuity or of its inverse identities outside U is required. The
local map may take values in an ambient space Y via an inclusion ι : K → Y;
this allows a polynomial on an ambient neighborhood of a compact interval. The
homeomorphism is characterized by its singleton cylinder intersection.
The remaining dynamical consequences are allocated to InverseBranchCoding.
-/
namespace Specs.D13Unified.Ch17.InverseCodingConstruction
open Set NNReal
open Specs.D13Unified.Ch17.ShiftSpaces
noncomputable section

/-- Append the last inverse branch on the right, so the first symbol is
always the outermost branch. -/
def wordMap {K : Type*} (b : Binary → K → K) (s : OneSided) : ℕ → K → K
  | 0 => id
  | n + 1 => fun x => wordMap b s n (b (s n) x)

def cylinderImage {K : Type*} (b : Binary → K → K) (s : OneSided) (n : ℕ) : Set K :=
  Set.range (wordMap b s n)

def levelSet {K : Type*} (b : Binary → K → K) (n : ℕ) : Set K :=
  ⋃ s : OneSided, cylinderImage b s n

def limitSet {K : Type*} (b : Binary → K → K) : Set K :=
  ⋂ n : ℕ, levelSet b (n + 1)

def wordMapType := {K : Type*} → (Binary → K → K) → OneSided → ℕ → K → K
def cylinderImageType := {K : Type*} → (Binary → K → K) → OneSided → ℕ → Set K
def levelSetType := {K : Type*} → (Binary → K → K) → ℕ → Set K
def limitSetType := {K : Type*} → (Binary → K → K) → Set K

def levelSet_finiteWordsStatement : Prop :=
  ∀ {K : Type} (b : Binary → K → K) (n : ℕ),
    levelSet b n = ⋃ w : Fin n → Binary,
      cylinderImage b (fun j => if h : j < n then w ⟨j, h⟩ else 0) n

def cylinder_geometryStatement : Prop :=
  ∀ {K : Type} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (b : Binary → K → K) (q : ℝ≥0),
    (∀ i, LipschitzWith q (b i)) →
    ∀ (s : OneSided) (n : ℕ),
      (cylinderImage b s n).Nonempty ∧ IsCompact (cylinderImage b s n) ∧
      cylinderImage b s (n + 1) ⊆ cylinderImage b s n ∧
      Metric.diam (cylinderImage b s n) ≤ (q : ℝ)^n * Metric.diam (Set.univ : Set K)

def coding_existsStatement : Prop :=
  ∀ {K : Type} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    ∃ π : OneSided ≃ₜ limitSet b,
      (∀ s, (⋂ n : ℕ, cylinderImage b s n) = {(π s : K)}) ∧
      (∀ s, (π s : K) = b (s 0) (π (shiftPlus s) : K))

def local_conjugacyStatement : Prop :=
  ∀ {K : Type} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    ∀ {Y : Type} [TopologicalSpace Y] (ι : K → Y) (U : Set K),
    IsOpen U → ∀ (F : U → Y), Continuous F →
    ∀ (hbU : ∀ i x, b i x ∈ U),
    (∀ i x, F ⟨b i x, hbU i x⟩ = ι x) →
    ∃ π : OneSided ≃ₜ limitSet b,
      (∀ s, (⋂ n : ℕ, cylinderImage b s n) = {(π s : K)}) ∧
      (∀ s, ∃ hs : (π s : K) ∈ U,
        F ⟨(π s : K), hs⟩ = ι (π (shiftPlus s) : K))


/-- Direct specialization to a compact subset of an ambient metric space.
In particular F need not map its whole neighborhood back into K. -/
def ambient_conjugacyStatement : Prop :=
  ∀ {X : Type} [MetricSpace X] (K : Set X), IsCompact K → K.Nonempty →
    ∀ (b : Binary → K → K) (q : ℝ≥0),
    (q : ℝ) < 1 → (∀ i, LipschitzWith q (b i)) →
    (∀ i, Function.Injective (b i)) →
    Disjoint (Set.range (b 0)) (Set.range (b 1)) →
    ∀ (U : Set X), IsOpen U → ∀ (F : U → X), Continuous F →
    ∀ (hbU : ∀ i x, (b i x : X) ∈ U),
    (∀ i x, F ⟨(b i x : X), hbU i x⟩ = (x : X)) →
    ∃ π : OneSided ≃ₜ limitSet b,
      (∀ s, (⋂ n : ℕ, cylinderImage b s n) = {(π s : K)}) ∧
      (∀ s, ∃ hs : ((π s : K) : X) ∈ U,
        F ⟨((π s : K) : X), hs⟩ = ((π (shiftPlus s) : K) : X))

end
end Specs.D13Unified.Ch17.InverseCodingConstruction
