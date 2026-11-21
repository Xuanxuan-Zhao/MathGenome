import MathGenome.Internal.Specs.D05.M10.Semisimple
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-! Independent statement of K05.10.semisimple_decomposition,
paper.tex:1589–1603. A field homomorphism into ℂ expresses the named
field's inclusion; injectivity follows from the field axioms. Semisimplicity
is the upstream invariant-complement predicate over K. All endomorphisms
and polynomial coefficients remain over K, and zero dimension is allowed.
-/

namespace Specs.D05.M10.SemisimpleDecomposition

/-- Existence with polynomial formulas, and uniqueness among every commuting
semisimple–nilpotent pair, without polynomial assumptions on competitors. -/
noncomputable def decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (_ι : K →+* ℂ) (T : Module.End K V),
    ∃ S N : Module.End K V,
      T = S + N ∧
      Specs.D05.M10.Semisimple.semisimple_value K V S ∧
      IsNilpotent N ∧ Commute S N ∧
      (∃ p : Polynomial K, Polynomial.aeval T p = S) ∧
      (∃ q : Polynomial K, Polynomial.aeval T q = N) ∧
      ∀ S' N' : Module.End K V,
        T = S' + N' →
        Specs.D05.M10.Semisimple.semisimple_value K V S' →
        IsNilpotent N' → Commute S' N' → S' = S ∧ N' = N

end Specs.D05.M10.SemisimpleDecomposition
