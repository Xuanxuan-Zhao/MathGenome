import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable

/-! The residue-field assertion of ET-19 (paper.tex 2035–2037, 2048–2059).
The algebra structure on κ(q) is explicitly the canonical residue-field map
for A → B; thus the equivalence preserves the given extension of κ(p). -/
namespace Specs.AdvCommAlg.Etale.ResidueExtension

universe u v

noncomputable def realization : Prop :=
  ∀ (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L],
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      etaleValue A B ∧ ∃ (q : Ideal B) (_ : q.IsPrime) (_ : q.LiesOver p),
        letI : Algebra p.ResidueField q.ResidueField :=
          (Ideal.ResidueField.map p q (algebraMap A B) (q.over_def p)).toAlgebra
        Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L)

end Specs.AdvCommAlg.Etale.ResidueExtension
