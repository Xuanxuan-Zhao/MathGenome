import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.LinearAlgebra.Complex.Module

/-!
Independent specification for K07.12.splitting_definition, paper.tex:3697–3701.
The source applies to nonzero polynomials. The explicit nonzero conjunct keeps
that domain separate from Mathlib's convention for the zero polynomial.
The specified Algebra structure records the base embedding. No finiteness,
separability, characteristic, or algebraic-closedness hypothesis is added.
-/

universe u v

namespace Specs.D07.Ch12.SplittingDefinition

open Polynomial

def SplittingFieldPredicateType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Polynomial K → Prop

/-- The extension splits the nonzero polynomial and is generated as a FIELD
by its roots, using the generated-field object of the preceding entry. -/
def splittingFieldValue : SplittingFieldPredicateType.{u, v} :=
  fun K L _ _ _ f => f ≠ 0 ∧ (f.map (algebraMap K L)).Splits ∧
    IntermediateField.adjoin K (f.rootSet L) = ⊤

/-- An explicit product of linear factors, including multiplicities and the
nonzero leading constant, together with generation by the actual zeros of f.
The multiset may be empty, precisely as needed for nonzero constants. -/
def SourceCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (_hf : f ≠ 0),
    splittingFieldValue K L f ↔
      (∃ m : Multiset L,
        f.map (algebraMap K L) =
          C (f.map (algebraMap K L)).leadingCoeff *
            (m.map (fun a => X - C a)).prod) ∧
      IntermediateField.adjoin K {a : L | aeval a f = 0} = ⊤

/-- The source's field-generation condition agrees with the library's
algebra-generation condition for roots of a nonzero polynomial. -/
def LibraryCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (_hf : f ≠ 0),
    splittingFieldValue K L f ↔ Polynomial.IsSplittingField K L f

/-- No proper intermediate field can contain every root of a splitting field. -/
def RootsGenerate : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), splittingFieldValue K L f →
    ∀ E : IntermediateField K L,
      (∀ a : L, aeval a f = 0 → a ∈ E) → E = ⊤

def ConstantBase : Prop :=
  ∀ (K : Type u) [Field K] (c : K), c ≠ 0 →
    splittingFieldValue K K (C c)

/-- For an arbitrary chosen embedding, a constant's splitting field contains
only base scalars. This states equality with the embedded base, not equality
of unrelated field types. -/
def ConstantCharacterization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (c : K) (_hc : c ≠ 0),
    splittingFieldValue K L (C c) ↔ Function.Surjective (algebraMap K L)

def ConstantEquivalence : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (c : K), splittingFieldValue K L (C c) → Nonempty (K ≃ₐ[K] L)

/-- X splits over C, but its roots generate only the embedded real field,
which is proper in C. Only complex arithmetic is used here. -/
def ContainingRootsInsufficient : Prop :=
  ((X : Polynomial ℝ).map (algebraMap ℝ ℂ)).Splits ∧
    IntermediateField.adjoin ℝ ((X : Polynomial ℝ).rootSet ℂ) = ⊥ ∧
    (⊥ : IntermediateField ℝ ℂ) < ⊤ ∧
    ¬ splittingFieldValue ℝ ℂ (X : Polynomial ℝ)

end Specs.D07.Ch12.SplittingDefinition
