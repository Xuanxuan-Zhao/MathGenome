import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests
import Mathlib.Topology.Homeomorph.Defs

/-!
Independent types for paper.tex, d10:02:maps (homeomorphisms and
embeddings), d10:02:embedding, and d10:02:characteristic.

`Bool` represents {0,1}, with false = 0 and true = 1. The canonical data
below live in Specs so later quotient and atlas interfaces can use the
same topology and characteristic function without importing a proof.
Topologies on the domain and codomain are always specified separately.
No nonemptiness, countability, or separation assumption is imposed.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch02.CharacteristicMaps

/-- The Sierpiński topology: an open set containing 0 must contain 1. -/
@[instance_reducible] def topology : TopologicalSpace Bool where
  IsOpen U := false ∈ U → true ∈ U
  isOpen_univ := fun _ => mem_univ _
  isOpen_inter _ _ hU hV h := ⟨hU h.1, hV h.2⟩
  isOpen_sUnion _ hS := by
    rintro ⟨U, hU, h⟩
    exact ⟨U, hU, hS U hU h⟩

/-- The characteristic function with value 1 on A and 0 off A. -/
noncomputable def chi {X : Type u} (A : Set X) : X → Bool := by
  classical
  exact fun x => if x ∈ A then true else false

end D10Topology.Ch02.CharacteristicMaps

namespace Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
open _root_.D10Topology.Ch02.CharacteristicMaps
open _root_.D10Topology.Ch01

def sierpinskiTopologyType := TopologicalSpace Bool
def sierpinskiTopologyValue : sierpinskiTopologyType := topology

def characteristicType : Type (u + 1) := {X : Type u} → Set X → X → Bool
noncomputable def characteristicValue : characteristicType := @chi

def homeomorph_iff_continuous_inverse : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    IsHomeomorph f ↔ Continuous f ∧ ∃ g : Y → X,
      Function.LeftInverse g f ∧ Function.RightInverse g f ∧ Continuous g

def equiv_homeomorph_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ Y),
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm

def continuous_bijection_homeomorph_iff_open : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), Continuous f → Function.Bijective f →
      (IsHomeomorph f ↔ IsOpenMap f)

def continuous_bijection_homeomorph_iff_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), Continuous f → Function.Bijective f →
      (IsHomeomorph f ↔ IsClosedMap f)

/-- The homeomorphism must be the given map with its codomain restricted
exactly to its range, equipped with the subspace topology. -/
def embedding_iff_homeomorph_range : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
    IsEmbedding e ↔ ∃ h : X ≃ₜ range e, ∀ x, (h x : Y) = e x

def embedding_iff_open_preimages : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
    IsEmbedding e ↔ Function.Injective e ∧ Continuous e ∧
      ∀ U : Set X, IsOpen U → ∃ V : Set Y, IsOpen V ∧ U = e ⁻¹' V

def embedding_iff_induced : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (e : X → Y), IsEmbedding e ↔ Function.Injective e ∧ tX = tY.induced e

/-- Equality of actual open families, in addition to equality of topologies. -/
def embedding_iff_open_family : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (e : X → Y), IsEmbedding e ↔ Function.Injective e ∧
      openSets tX = (fun V : Set Y => e ⁻¹' V) '' openSets tY

def compose_embeddings : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X → Y) (j : Y → Z), IsEmbedding e → IsEmbedding j → IsEmbedding (j ∘ e)

/-- The domain is sigma and the codomain is tau, preserving the paper's
inclusion direction despite Lean's reverse order on topologies. -/
def identity_continuous_iff_finer : Prop :=
  ∀ {X : Type u} (tau sigma : TopologicalSpace X),
    @Continuous X X sigma tau id ↔ openSets tau ⊆ openSets sigma

def sierpinski_opens : Prop :=
  openSets topology = {∅, {true}, univ}

def sierpinski_isOpen_iff : Prop :=
  ∀ U : Set Bool, IsOpen[topology] U ↔ U = ∅ ∨ U = {true} ∨ U = univ

def characteristic_preimage_one : Prop :=
  ∀ {X : Type u} (A : Set X), chi A ⁻¹' {true} = A

def characteristic_preimage_zero : Prop :=
  ∀ {X : Type u} (A : Set X), chi A ⁻¹' {false} = Aᶜ

def characteristic_continuous_iff_open : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] (A : Set X),
    @Continuous X Bool tX topology (chi A) ↔ IsOpen A

def characteristic_discrete_continuous_iff_clopen : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] (A : Set X),
    @Continuous X Bool tX ⊥ (chi A) ↔ IsClopen A

end Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
