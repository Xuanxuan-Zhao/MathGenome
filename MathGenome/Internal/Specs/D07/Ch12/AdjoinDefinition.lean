import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
Independent specification for K07.12.adjoin_definition, paper.tex:3559–3570.
The chosen `Algebra K L` records the specified embedding. All subfields and
composita lie in this same ambient field L. There are no algebraicity,
finite-degree, or algebraic-closedness hypotheses, and S may be empty or infinite.
The intersection statement uses *all* subfields containing the image of K and S.
-/

universe u v

namespace Specs.D07.Ch12.AdjoinDefinition

def GeneratedFieldType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Set L → IntermediateField K L

def generatedFieldValue : GeneratedFieldType.{u, v} :=
  fun K _ _ _ _ S => IntermediateField.adjoin K S

def SimpleFieldType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    L → IntermediateField K L

def simpleFieldValue : SimpleFieldType.{u, v} :=
  fun K _ _ _ _ α => IntermediateField.adjoin K {α}

def CompositumType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    IntermediateField K L → IntermediateField K L → IntermediateField K L

def compositumValue : CompositumType.{u, v} :=
  fun K _ _ _ _ E F => IntermediateField.adjoin K ((E : Set _) ∪ (F : Set _))

/-- This is the source's defining intersection of subfields, with K interpreted
as the image of its specified structure map. -/
def AdjoinIntersection : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (S : Set L),
    (IntermediateField.adjoin K S).toSubfield =
      sInf {T : Subfield L | Set.range (algebraMap K L) ∪ S ⊆ (T : Set L)}

/-- The intersected family is inhabited even for arbitrary S. -/
def DefiningFamilyNonempty : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (S : Set L),
    {T : Subfield L | Set.range (algebraMap K L) ∪ S ⊆ (T : Set L)}.Nonempty

def AdjoinContains : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (S : Set L),
    Set.range (algebraMap K L) ⊆ (IntermediateField.adjoin K S : Set L) ∧
    S ⊆ (IntermediateField.adjoin K S : Set L)

def AdjoinLeast : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (S : Set L) (E : IntermediateField K L),
    IntermediateField.adjoin K S ≤ E ↔ S ⊆ (E : Set L)

/-- In particular, taking an intersection preserves the field operations,
including inverses. The result is an intermediate field by its very type. -/
def AdjoinFieldOperations : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (S : Set L),
    (0 : L) ∈ IntermediateField.adjoin K S ∧
    (1 : L) ∈ IntermediateField.adjoin K S ∧
    ∀ x ∈ IntermediateField.adjoin K S, ∀ y ∈ IntermediateField.adjoin K S,
      x - y ∈ IntermediateField.adjoin K S ∧
      x * y ∈ IntermediateField.adjoin K S ∧
      x⁻¹ ∈ IntermediateField.adjoin K S

def SimpleFieldLeast : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (α : L) (E : IntermediateField K L),
    IntermediateField.adjoin K {α} ≤ E ↔ α ∈ E

/-- The source's compositum definition agrees with the lattice supremum. -/
def CompositumSup : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E F : IntermediateField K L),
    IntermediateField.adjoin K ((E : Set L) ∪ (F : Set L)) = E ⊔ F

/-- Leastness holds among all ambient subfields, not just a restricted family
of finite or algebraic intermediate fields. -/
def CompositumLeast : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E F : IntermediateField K L),
    let C := IntermediateField.adjoin K ((E : Set L) ∪ (F : Set L))
    E.toSubfield ≤ C.toSubfield ∧ F.toSubfield ≤ C.toSubfield ∧
    ∀ T : Subfield L, E.toSubfield ≤ T → F.toSubfield ≤ T → C.toSubfield ≤ T

def InfimumIntersection : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E F : IntermediateField K L),
    ((E ⊓ F : IntermediateField K L) : Set L) = (E : Set L) ∩ (F : Set L) ∧
    ∀ T : IntermediateField K L, (T ≤ E ⊓ F ↔ T ≤ E ∧ T ≤ F)

/-- The empty generating set is allowed and leaves precisely the chosen base. -/
def EmptyAdjoin : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (IntermediateField.adjoin K (∅ : Set L) : Set L) = Set.range (algebraMap K L)

end Specs.D07.Ch12.AdjoinDefinition
