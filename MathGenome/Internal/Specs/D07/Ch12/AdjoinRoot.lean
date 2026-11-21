import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Independent statements for K07.12.adjoin_root (paper.tex:3599–3605).
The quotient has its canonical ring operations and K-algebra structure.
`IsField` asserts nontriviality and existence of inverses for these operations.
The polynomial is arbitrary irreducible, with no monicity assumption; no
ambient extension or pre-existing root is part of the hypotheses.
-/

universe u

namespace Specs.D07.Ch12.AdjoinRoot

open Polynomial

/-- The principal-ideal quotient of an irreducible polynomial is a field. -/
def QuotientIsField : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), Irreducible f →
    IsField (Polynomial K ⧸ Ideal.span {f})

/-- Constants embed in the quotient, and this is its specified scalar map. -/
def ConstantEmbedding : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), Irreducible f →
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {f})).comp C) ∧
    (Ideal.Quotient.mk (Ideal.span {f})).comp C =
      algebraMap K (Polynomial K ⧸ Ideal.span {f})

/-- The residue class of X is a root, evaluated using the canonical K-algebra. -/
def RootEquation : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), Irreducible f →
    aeval (Ideal.Quotient.mk (Ideal.span {f}) X) f = 0

end Specs.D07.Ch12.AdjoinRoot
