import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicDegreeOne
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

namespace Specs.GaloisFormalization.GH.CyclicHilbert90

open _root_.GaloisFormalization.GH.CyclicDegreeOne

universe u v

/-- The additive cyclic norm on the extension field is its field trace included in the field. -/
def TraceFormula : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ → ∀ x : E,
      norm s x = algebraMap k E (Algebra.trace k E x)

/-- The cyclic norm on the units, written additively, agrees with the field norm. -/
def NormFormula : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ → ∀ x : Eˣ,
      ((norm s (Additive.ofMul x)).toMul : E) = algebraMap k E (Algebra.norm k (x : E))

/-- The degree-one cyclic quotient for the additive group of the extension field vanishes. -/
def AdditiveQuotientVanishing : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ →
      Subsingleton (NormQuotient (A := E) s)

/-- The degree-one cyclic quotient for the units of the extension field vanishes. -/
def MultiplicativeQuotientVanishing : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ →
      Subsingleton (NormQuotient (A := Additive Eˣ) s)

/-- The trace-zero elements are precisely the differences for the chosen generator. -/
def AdditiveHilbert90 : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ → ∀ x : E,
      Algebra.trace k E x = 0 ↔ ∃ b : E, x = s b - b

/-- The norm-one units are precisely the ratios for the chosen generator. -/
def MultiplicativeHilbert90 : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (s : Gal(E/k)), Subgroup.zpowers s = ⊤ → ∀ x : Eˣ,
      Algebra.norm k (x : E) = 1 ↔ ∃ b : Eˣ, x = (s • b) / b

end Specs.GaloisFormalization.GH.CyclicHilbert90
