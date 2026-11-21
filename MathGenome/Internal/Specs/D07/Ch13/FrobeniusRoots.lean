import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Separable

/-!
K07.13.frobenius_roots (paper.tex:3974–3983).

The finite base K and its specified embedding in L are retained throughout;
q is Nat.card K. The ambient field L can in particular be the fixed algebraic
closure in the source. In fact no algebraic-closedness assumption is needed
once the given root a exists. No monicity assumption is imposed on f.

The embedded field of q^d elements is identified by its carrier, the roots
of X^(q^d)-X, as well as by uniqueness among embedded finite subfields with
that cardinality. This expresses literal equality in the specified ambient
field, rather than an identification of unrelated abstract field copies.
-/

universe u v
namespace Specs.D07.Ch13.FrobeniusRoots

open Polynomial

/-- All conclusions for an arbitrary irreducible polynomial and a chosen root. -/
def FrobeniusRootsTheorem : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (f : K[X]) (a : L), Irreducible f → aeval a f = 0 →
    let d := f.natDegree
    let E := IntermediateField.adjoin K {a}
    0 < d ∧
    Finite E ∧
    Module.finrank K E = d ∧
    Nat.card E = Nat.card K ^ d ∧
    IsSplittingField K E f ∧
    (∀ x : L, x ∈ E ↔ x ^ (Nat.card K ^ d) = x) ∧
    (∀ S : IntermediateField K L, Finite S → Nat.card S = Nat.card K ^ d → S = E) ∧
    Function.Injective (fun i : Fin d => a ^ (Nat.card K ^ i.val)) ∧
    (∀ b : L, aeval b f = 0 ↔ ∃ i : Fin d, b = a ^ (Nat.card K ^ i.val)) ∧
    a ^ (Nat.card K ^ d) = a ∧
    (∀ j : ℕ, 0 < j → a ^ (Nat.card K ^ j) = a → d ≤ j) ∧
    f.Separable ∧
    f.map (algebraMap K L) = C (algebraMap K L f.leadingCoeff) *
      ∏ i : Fin d, ((X : L[X]) - C (a ^ (Nat.card K ^ i.val)))

end Specs.D07.Ch13.FrobeniusRoots
