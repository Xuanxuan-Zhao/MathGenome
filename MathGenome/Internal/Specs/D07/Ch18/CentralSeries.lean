import Mathlib.GroupTheory.Nilpotent

/-!
Independent specification of `K07.18.central_series`, paper.tex:4970–5000.

`upperValue G i` is the source's Z_i, with Z_0 = 1. The library constructs
this sequence together with characteristicity, so quotient group instances in
`UpperSuccessor` do not presuppose an unproved normality assumption.

`lowerValue G i` is the source's gamma_i for i ≥ 1, defined by its own
commutator recurrence. Its value at zero is an unused extension, set to G;
all claims about source lower terms are indexed by n+1. `LowerIndexing`
identifies these terms with the library's zero-based lower central series.
The subgroup bracket uses exactly xyx⁻¹y⁻¹, as in MixedCommutators.

Stabilization means equality to a fixed subgroup at every later index.
Finiteness is required only for the two existence statements. Neither
nilpotence nor an endpoint G or 1 is imposed or inferred.
-/

namespace Specs.D07.Ch18.CentralSeries

universe u

def SeriesType := (G : Type u) → [Group G] → ℕ → Subgroup G

abbrev upperValue (G : Type u) [Group G] : ℕ → Subgroup G :=
  Subgroup.upperCentralSeries G

def lowerValue (G : Type u) [Group G] : ℕ → Subgroup G
  | 0 => ⊤
  | 1 => ⊤
  | n + 2 => ⁅lowerValue G (n + 1), (⊤ : Subgroup G)⁆

def UpperZero : Prop :=
  ∀ (G : Type u) [Group G], upperValue G 0 = ⊥

def LowerOne : Prop :=
  ∀ (G : Type u) [Group G], lowerValue G 1 = ⊤

def LowerSuccessor : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    lowerValue G (n + 2) = ⁅lowerValue G (n + 1), (⊤ : Subgroup G)⁆

def LowerIndexing : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    lowerValue G (n + 1) = (⊤ : Subgroup G).lowerCentralSeries n

def UpperCharacteristic : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ), (upperValue G n).Characteristic

def LowerCharacteristic : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ), (lowerValue G (n + 1)).Characteristic

def UpperNormal : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ), (upperValue G n).Normal

def LowerNormal : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ), (lowerValue G (n + 1)).Normal

/-- The successor is the full inverse image of the quotient's center. -/
def UpperSuccessor : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    upperValue G (n + 1) =
      (Subgroup.center (G ⧸ upperValue G n)).comap (QuotientGroup.mk' (upperValue G n))

/-- The source notation Z_(n+1)/Z_n denotes its image in G/Z_n. -/
def UpperQuotientCenter : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    (upperValue G (n + 1)).map (QuotientGroup.mk' (upperValue G n)) =
      Subgroup.center (G ⧸ upperValue G n)

def UpperMonotone : Prop :=
  ∀ (G : Type u) [Group G], Monotone (upperValue G)

def LowerAntitone : Prop :=
  ∀ (G : Type u) [Group G], Antitone (fun n => lowerValue G (n + 1))

def UpperCommutator : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    ⁅(⊤ : Subgroup G), upperValue G (n + 1)⁆ ≤ upperValue G n

/-- Exactly the quotient-center obstruction when two consecutive terms agree. -/
def UpperEqualityIffTrivialCenter : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    upperValue G n = upperValue G (n + 1) ↔
      Subgroup.center (G ⧸ upperValue G n) = ⊥

def UpperStabilizesOfEquality : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    upperValue G n = upperValue G (n + 1) →
      ∀ m : ℕ, n ≤ m → upperValue G m = upperValue G n

def LowerStabilizesOfEquality : Prop :=
  ∀ (G : Type u) [Group G] (n : ℕ),
    lowerValue G (n + 1) = lowerValue G (n + 2) →
      ∀ m : ℕ, n ≤ m → lowerValue G (m + 1) = lowerValue G (n + 1)

def FiniteUpperStabilizes : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → upperValue G m = upperValue G n

def FiniteLowerStabilizes : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → lowerValue G (m + 1) = lowerValue G (n + 1)

end Specs.D07.Ch18.CentralSeries
