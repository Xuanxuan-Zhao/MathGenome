import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.DistanceFunction

/-! Independent statements for the separation and compact-neighborhood assertions
of `chapters/01.tex`, `d04:01:distance`. All dimensions, including zero, are
allowed. The closed set need not be bounded. The infimum in the separation
statement ranges over every pair of points of the two nonempty sets.

The empty-set convention for closed thickenings is explicit; the real-valued
distance function itself is still used only with a nonempty set. -/

noncomputable section
open Set

namespace Specs.D04.C01.CompactSeparation.Model
open Specs.D04.C01.EuclideanInterfaces.Model

def closedThickening {n : ℕ} (K : Set (E n)) (ρ : ℝ) : Set (E n) := by
  classical
  exact if hK : K.Nonempty then {x | DistanceFunction.Model.distanceToSet K hK x ≤ ρ}
    else ∅

end Specs.D04.C01.CompactSeparation.Model

namespace Specs.D04.C01.CompactSeparation
open Specs.D04.C01.EuclideanInterfaces.Model

def closedThickeningType := {n : ℕ} → Set (E n) → ℝ → Set (E n)
def closedThickeningValue : closedThickeningType := @Model.closedThickening

def closedThickening_nonempty_eqType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)) (hK : K.Nonempty) (ρ : ℝ),
    Model.closedThickening K ρ = {x | DistanceFunction.Model.distanceToSet K hK x ≤ ρ}

def closedThickening_emptyType : Prop :=
  ∀ {n : ℕ} (ρ : ℝ), Model.closedThickening (∅ : Set (E n)) ρ = ∅

def compact_closed_separation_boundType : Prop :=
  ∀ {n : ℕ} (K F : Set (E n)), K.Nonempty → F.Nonempty →
    Compact K → Closed F → Disjoint K F →
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ F, δ ≤ ‖x - y‖

def compact_closed_separationType : Prop :=
  ∀ {n : ℕ} (K F : Set (E n)), K.Nonempty → F.Nonempty →
    Compact K → Closed F → Disjoint K F →
    0 < sInf ((fun p : E n × E n => ‖p.1 - p.2‖) '' (K ×ˢ F))

def compact_closedThickeningType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)) (ρ : ℝ),
    Compact K → Compact (Model.closedThickening K ρ)

/-- This is literally the distance sublevel set in the source. -/
def exists_compact_distance_neighborhoodType : Prop :=
  ∀ {n : ℕ} (K U : Set (E n)) (hne : K.Nonempty),
    Compact K → Open U → K ⊆ U →
    ∃ ρ > 0, {x | DistanceFunction.Model.distanceToSet K hne x ≤ ρ} ⊆ U ∧
      Compact {x | DistanceFunction.Model.distanceToSet K hne x ≤ ρ}

/-- The same conclusion with the explicit empty-set convention. -/
def exists_compact_closedThickeningType : Prop :=
  ∀ {n : ℕ} (K U : Set (E n)), Compact K → Open U → K ⊆ U →
    ∃ ρ > 0, Model.closedThickening K ρ ⊆ U ∧ Compact (Model.closedThickening K ρ)

end Specs.D04.C01.CompactSeparation
