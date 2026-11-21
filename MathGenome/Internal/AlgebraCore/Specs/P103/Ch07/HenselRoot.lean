import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Root part of paper.tex, Theorem 7.8 (1296–1311).
`IsAdicComplete I R` includes separatedness and completeness for all powers of `I`.
The scalar ideals `d² I` and coset `a + d I` are written explicitly as scalar
multiples with a witness in `I`. No cancellation is imposed for existence. -/
universe u
namespace P103.Specs.Ch07.HenselRoot
open Polynomial

def root_existsType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a : R)
    (_ : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c),
    ∃ b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0

def root_uniqueType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a : R)
    (_ : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c)
    (_ : Function.Injective (fun x : R => f.derivative.eval a * x)),
    ∃! b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0

def zero_derivativeType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a : R)
    (_ : f.derivative.eval a = 0)
    (_ : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c),
    f.eval a = 0 ∧
      {b : R | ∃ t ∈ I, b = a + f.derivative.eval a * t} = {a} ∧
      ∃! b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0

def simple_root_liftType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : R[X]) (x : IsLocalRing.ResidueField R)
    (_ : (f.map (IsLocalRing.residue R)).eval x = 0)
    (_ : ((f.map (IsLocalRing.residue R)).derivative).eval x ≠ 0),
    ∃! b : R, f.eval b = 0 ∧ IsLocalRing.residue R b = x

end P103.Specs.Ch07.HenselRoot
