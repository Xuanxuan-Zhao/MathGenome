import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions

open Set Filter
open scoped Uniformity
universe u

namespace Specs.D10Topology.Ch12.EntourageCalculus

open UniformConventions

/-- The zero power is the diagonal; successors compose one more copy on the left,
in the composition convention of the manuscript. -/
def relationPower {X : Type u} (V : Set (X × X)) : ℕ → Set (X × X)
  | 0 => diagonal X
  | n + 1 => relationComp V (relationPower V n)

def relationPowerType := {X : Type u} → Set (X × X) → ℕ → Set (X × X)
def relationPowerValue : relationPowerType := @relationPower

/-- A nonempty, downward directed family with the three uniformity base axioms.
Nonemptiness and the binary intersection axiom include the empty finite
intersection case: every member is contained in the universal relation. -/
def EntourageBasis {X : Type u} (B : Set (Set (X × X))) : Prop :=
  B.Nonempty ∧
  (∀ U ∈ B, ∀ x : X, (x, x) ∈ U) ∧
  (∀ U ∈ B, ∀ V ∈ B, ∃ W ∈ B, W ⊆ U ∩ V) ∧
  (∀ U ∈ B, ∃ V ∈ B, V ⊆ relationInverse U) ∧
  (∀ U ∈ B, ∃ V ∈ B, relationComp V V ⊆ U)

def entourageBasisType := {X : Type u} → Set (Set (X × X)) → Prop
def entourageBasisValue : entourageBasisType := @EntourageBasis

def symmetric_entourage : Prop :=
  ∀ {X : Type u} [UniformSpace X] (U : Set (X × X)), U ∈ 𝓤 X →
    ∃ V ∈ 𝓤 X, relationInverse V = V ∧ V ⊆ U

def symmetric_power_entourage : Prop :=
  ∀ {X : Type u} [UniformSpace X] (U : Set (X × X)), U ∈ 𝓤 X →
    ∀ m : ℕ, 0 < m → ∃ V ∈ 𝓤 X,
      relationInverse V = V ∧ relationPower V m ⊆ U

/-- The generated entourage family consists exactly of supersets of base members.
Existence and uniqueness concern the entire uniform structure, including its
induced topology. No uniform structure on X is assumed in this construction. -/
def uniformity_base_criterion : Prop :=
  ∀ {X : Type u} (B : Set (Set (X × X))), EntourageBasis B →
    ∃! uX : UniformSpace X, ∀ U : Set (X × X),
      U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U

def uniformity_base_proper : Prop :=
  ∀ {X : Type u} [Nonempty X] (B : Set (Set (X × X))), EntourageBasis B →
    ∃ uX : UniformSpace X,
      (∀ U : Set (X × X), U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U) ∧
      (@uniformity X uX).NeBot

def uniformity_base_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (B : Set (Set (X × X))), EntourageBasis B →
    ∃ uX : UniformSpace X,
      (∀ U : Set (X × X), U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U) ∧
      (@uniformity X uX).sets = {∅} ∧ ¬ (@uniformity X uX).NeBot

end Specs.D10Topology.Ch12.EntourageCalculus
