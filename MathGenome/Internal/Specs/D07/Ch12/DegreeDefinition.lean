import MathGenome.Internal.Specs.D07.Ch12.ExtensionDefinition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specification for K07.12.degree_definition, paper.tex:3554–3558.
The Algebra argument retains the specified field embedding and its scalar action.
Degree is cardinal-valued even for extensions of infinite dimension. Finiteness
means that cardinal dimension is a natural number, not that the field is finite.
The statements involving finrank explicitly require finite dimension (or recover
it from an equality of the cardinal degree with a natural number).
-/

universe u v

namespace Specs.D07.Ch12.DegreeDefinition

noncomputable section

def DegreeType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Cardinal.{v}

def degreeValue : DegreeType.{u, v} :=
  fun K L _ _ _ => Module.rank K L

/-- The same degree with the structure map supplied as an explicit argument. -/
def DegreeOfType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], (K →+* L) → Cardinal.{v}

def degreeOfValue : DegreeOfType.{u, v} :=
  fun K L _ _ ι => letI := ι.toAlgebra; Module.rank K L

def FiniteExtensionPredicateType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L], Prop

def finiteExtensionValue : FiniteExtensionPredicateType.{u, v} :=
  fun K L _ _ _ => ∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})

/-- Checks the bridge from the source's definition to Mathlib's vector-space
finiteness predicate, whose meaning is finite generation as a module. -/
def FiniteIffFiniteDimensional : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})) ↔ FiniteDimensional K L

def FiniteIffDegreeLtAleph0 : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})) ↔ Module.rank K L < Cardinal.aleph0

/-- Natural-number dimensions agree with degree only with finite dimension. -/
def DegreeEqFinrank : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L], Module.rank K L = (Module.finrank K L : Cardinal.{v})

/-- An equality with a natural cardinal supplies the finiteness needed to use
finrank, including the boundary case n = 0. -/
def DegreeEqNatIff : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (n : ℕ),
    Module.rank K L = (n : Cardinal.{v}) ↔
      FiniteDimensional K L ∧ Module.finrank K L = n

/-- The source's assertion about the underlying set of a finite extension. -/
def FiniteExtensionOfInfiniteBase : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Infinite K],
    (∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})) → Infinite L

end

end Specs.D07.Ch12.DegreeDefinition
