import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
K07.15.radical_equivalence_char_zero, paper.tex:4426–4433.
The specified algebraic, algebraically closed overfield is a fixed algebraic
closure. Radical membership uses the shared finite-tower predicate, rather
than an assumed certificate or a different meaning of radical closure.
The polynomial is arbitrary nonzero: constants and repeated factors are
included. Its group is the automorphism group of its splitting field.
-/

universe u v
namespace Specs.D07.Ch15.RadicalEquivalenceCharZero

open Polynomial Specs.D07.Ch15.RadicalDefinition

def RadicalEquivalence : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] [CharZero K]
    (f : K[X]), f ≠ 0 →
      ((∀ a : Ω, aeval a f = 0 → solvableByRadicalsValue K Ω a) ↔
        Group.IsSolvable f.Gal)

end Specs.D07.Ch15.RadicalEquivalenceCharZero
