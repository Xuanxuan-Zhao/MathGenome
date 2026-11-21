import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent statements for `chapters/01.tex`, `d04:01:compactness`.
Compactness is the shared ambient-open-cover definition. Sequential
compactness requires a limit in the set and strictly increasing indices.
Boundedness is expressed by a single real bound on the Euclidean norm.
Every dimension is allowed, and no set is required to be nonempty. -/

namespace Specs.D04.C01.Compactness
open Specs.D04.C01.EuclideanInterfaces.Model

def compact_iff_sequentiallyCompactType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)), Compact K ↔ SequentiallyCompact K

def compact_iff_closed_boundedType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)),
    Compact K ↔ Closed K ∧ ∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B

def sequentiallyCompact_iff_closed_boundedType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)),
    SequentiallyCompact K ↔ Closed K ∧ ∃ B : ℝ, ∀ x ∈ K, ‖x‖ ≤ B

def compact_emptyType : Prop :=
  ∀ {n : ℕ}, Compact (∅ : Set (E n))

/-- In particular, the full one-point space and its empty subset are compact. -/
def compact_dimension_zeroType : Prop :=
  ∀ K : Set (E 0), Compact K

end Specs.D04.C01.Compactness
