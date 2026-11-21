import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Branching
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardRepresentation

/-! FR-B09, source lines 808–846. The finite products below realize the
stated direct sums, with the original inherited Specht actions. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

def partition22 : Partition 4 :=
  (YoungDiagram.ofRowLens [2, 2] (by decide)).toPartition (by decide)
def partition31 : Partition 4 :=
  (YoungDiagram.ofRowLens [3, 1] (by decide)).toPartition (by decide)
def partition211 : Partition 4 :=
  (YoungDiagram.ofRowLens [2, 1, 1] (by decide)).toPartition (by decide)
def partition21 : Partition 3 := standardPartition 3 (by decide)
def partition3 : Partition 3 :=
  (YoungDiagram.ofRowLens [3] (by decide)).toPartition (by decide)

def partition22Type := Partition 4
def partition31Type := Partition 4
def partition211Type := Partition 4
def partition21Type := Partition 3
def partition3Type := Partition 3

def small_diagram_partsType : Prop :=
  parts partition22 = [2, 2] ∧ parts partition31 = [3, 1] ∧
  parts partition211 = [2, 1, 1] ∧ parts partition21 = [2, 1] ∧ parts partition3 = [3]

def small_diagram_dimensionsType : Prop :=
  Module.finrank ℂ (SpechtModule partition22) = 2 ∧
  Module.finrank ℂ (SpechtModule partition31) = 3 ∧
  Module.finrank ℂ (SpechtModule partition211) = 3 ∧
  Module.finrank ℂ (SpechtModule partition21) = 2 ∧
  Module.finrank ℂ (SpechtModule partition3) = 1

def restriction22Type : Prop :=
  ∀ (σ : Representation ℂ (SymmetricGroup 4) (SpechtModule partition22))
    (τ : Representation ℂ (SymmetricGroup 3) (SpechtModule partition21)),
    InheritedSpechtAction partition22 σ → InheritedSpechtAction partition21 τ →
    Nonempty (Representation.Equiv (σ.comp (symmetricGroupEmbedding 3)) τ)

def restriction31Type : Prop :=
  ∀ (σ : Representation ℂ (SymmetricGroup 4) (SpechtModule partition31))
    (τ : Representation ℂ (SymmetricGroup 3) (SpechtModule partition3))
    (υ : Representation ℂ (SymmetricGroup 3) (SpechtModule partition21)),
    InheritedSpechtAction partition31 σ → InheritedSpechtAction partition3 τ →
    InheritedSpechtAction partition21 υ →
    Nonempty (Representation.Equiv (σ.comp (symmetricGroupEmbedding 3)) (τ.prod υ))

attribute [local instance] P103.Ch09.rightSubgroupModule
  P103.Ch09.inducedAlgebraModule P103.Ch09.inducedScalarModule

def induction21Type : Prop :=
  ∀ (σ : Representation ℂ (SymmetricGroup 3) (SpechtModule partition21))
    (τ : Representation ℂ (SymmetricGroup 4) (SpechtModule partition31))
    (υ : Representation ℂ (SymmetricGroup 4) (SpechtModule partition22))
    (ω : Representation ℂ (SymmetricGroup 4) (SpechtModule partition211)),
    InheritedSpechtAction partition21 σ → InheritedSpechtAction partition31 τ →
    InheritedSpechtAction partition22 υ → InheritedSpechtAction partition211 ω →
    ∃ E : SymmetricGroup 3 ≃* lastLabelSubgroup 3,
      (∀ g, (E g).val = extendPermutation g) ∧
      Nonempty ((P103.Ch09.induction (lastLabelSubgroup 3)
        (σ.comp E.symm.toMonoidHom)).Equiv (τ.prod (υ.prod ω))) ∧
      Module.finrank ℂ (P103.Ch09.Induced (lastLabelSubgroup 3)
        (σ.comp E.symm.toMonoidHom)) = 8

/-- The sum has dimension 3+2+3=8, also the index 4 times dimension 2. -/
def small_induction_dimension_checkType : Prop :=
  (lastLabelSubgroup 3).index = 4 ∧
  Module.finrank ℂ (SpechtModule partition31 ×
    (SpechtModule partition22 × SpechtModule partition211)) = 8 ∧
  Module.finrank ℂ (SpechtModule partition31) +
    Module.finrank ℂ (SpechtModule partition22) +
    Module.finrank ℂ (SpechtModule partition211) =
    (lastLabelSubgroup 3).index * Module.finrank ℂ (SpechtModule partition21)

/-- Retain the general point-module identification, its coordinate action,
and its two-dimensional S₃ specialization from FR-B09-Standard. -/
def small_standard_pointType : Prop :=
  standard_representationType ∧ point_coordinatesType ∧ standard_S3Type

end Specs.AdvancedFiniteGroupRepresentations
