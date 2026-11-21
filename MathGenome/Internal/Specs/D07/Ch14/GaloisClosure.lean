import MathGenome.Internal.Specs.D07.Ch14.SplittingCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of K07.14.galois_closure (paper.tex:4222–4230).
`E` and `N` are literal intermediate fields in the same specified algebraic
closure. Finite degree is the shared cardinal-dimension predicate. Galois
means algebraic, normal, and separable, with no characteristic restriction.
Minimality is even among all normal intermediate fields, as in the proof.
The conjugates of a generator are all roots of its minimal polynomial.
Lists may be empty or contain repetitions. Uniqueness is equality inside Ω.
The final statement records the source's inseparability boundary.
-/

universe u v

namespace Specs.D07.Ch14.GaloisClosure

/-- The finite normal closure also exists without a separability assumption. -/
def FiniteNormalClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E : IntermediateField K Ω),
    Ch12.DegreeDefinition.finiteExtensionValue K E →
    ∃! N : IntermediateField K Ω,
      E ≤ N ∧ Ch12.DegreeDefinition.finiteExtensionValue K N ∧ Normal K N ∧
      ∀ M : IntermediateField K Ω, Normal K M → E ≤ M → N ≤ M

/-- Existence, finiteness, and embedded uniqueness of the smallest Galois
extension containing an arbitrary finite separable extension in Ω. -/
def FiniteGaloisClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E : IntermediateField K Ω),
    Ch12.DegreeDefinition.finiteExtensionValue K E →
    Ch12.SeparableDefinition.extensionSeparableValue K E →
    ∃! N : IntermediateField K Ω,
      E ≤ N ∧ Ch12.DegreeDefinition.finiteExtensionValue K N ∧
      Algebra.IsAlgebraic K N ∧ Normal K N ∧
      Ch12.SeparableDefinition.extensionSeparableValue K N ∧
      ∀ M : IntermediateField K Ω, Normal K M → E ≤ M → N ≤ M

/-- Any chosen finite generating list gives precisely the same closure.
This also holds for finite inseparable extensions, with a normal closure. -/
def GeneratedByConjugates : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E N : IntermediateField K Ω),
    Ch12.DegreeDefinition.finiteExtensionValue K E →
    E ≤ N → Normal K N →
    (∀ M : IntermediateField K Ω, Normal K M → E ≤ M → N ≤ M) →
    ∀ (r : ℕ) (a : Fin r → Ω), IntermediateField.adjoin K (Set.range a) = E →
      N = IntermediateField.adjoin K {y : Ω | ∃ i, y ∈ (minpoly K (a i)).rootSet Ω}

/-- An extension containing an inseparable element cannot be separable. -/
def InseparableObstruction : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω), E ≤ M →
    ¬ Ch12.SeparableDefinition.extensionSeparableValue K E →
    ¬ Ch12.SeparableDefinition.extensionSeparableValue K M

/-- The elementwise form of the same obstruction, with no finiteness premise. -/
def InseparableElementObstruction : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (x : Ω) (M : IntermediateField K Ω), ¬ IsSeparable K x → x ∈ M →
    ¬ Ch12.SeparableDefinition.extensionSeparableValue K M

end Specs.D07.Ch14.GaloisClosure
