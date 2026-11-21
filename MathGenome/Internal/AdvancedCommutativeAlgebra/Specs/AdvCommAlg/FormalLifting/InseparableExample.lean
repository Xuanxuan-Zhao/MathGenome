import Mathlib.RingTheory.AdjoinRoot
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplittingCriterion

/-! The characteristic-p example of FL-12, paper.tex:771–785.
`AdjoinRoot` is the literal quotient k[X]/(X^p), with its quotient algebra
structure. A singleton basis specifies both rank one and its generator dx. -/
namespace Specs.AdvCommAlg.FormalLifting.InseparableExample

universe u
noncomputable section

abbrev TruncatedPolynomial (k : Type u) [Field k] (p : ℕ) :=
  AdjoinRoot (Polynomial.X ^ p : Polynomial k)

/-- The polynomial action is the quotient map itself. -/
instance polynomialAlgebra (k : Type u) [Field k] (p : ℕ) :
    Algebra (Polynomial k) (TruncatedPolynomial k p) :=
  (AdjoinRoot.mk (Polynomial.X ^ p : Polynomial k)).toAlgebra

instance polynomialScalarTower (k : Type u) [Field k] (p : ℕ) :
    IsScalarTower k (Polynomial k) (TruncatedPolynomial k p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

abbrev x (k : Type u) [Field k] (p : ℕ) : TruncatedPolynomial k p :=
  AdjoinRoot.root (Polynomial.X ^ p : Polynomial k)

def differentialBasis : Prop := ∀ (k : Type u) [Field k] (p : ℕ),
  p.Prime → ∀ [CharP k p],
  ∃ b : Module.Basis Unit (TruncatedPolynomial k p)
      (KaehlerDifferential k (TruncatedPolynomial k p)),
    b () = KaehlerDifferential.D k (TruncatedPolynomial k p) (x k p)

/-- The actual relation class in I/I² is nonzero and killed by the actual
conormal map of k[X] → k[X]/(X^p). -/
def conormalObstruction : Prop := ∀ (k : Type u) [Field k] (p : ℕ),
  p.Prime → ∀ [CharP k p]
    (h : Function.Surjective (algebraMap (Polynomial k) (TruncatedPolynomial k p))),
  ∃ f : RingHom.ker (algebraMap (Polynomial k) (TruncatedPolynomial k p)),
    f.val = Polynomial.X ^ p ∧
    Algebra.Extension.Cotangent.mk
      (P := Specs.AdvCommAlg.Differentials.conormalExtension k (Polynomial k)
        (TruncatedPolynomial k p) h) f ≠ 0 ∧
    Specs.AdvCommAlg.Differentials.conormalMapValue k (Polynomial k)
      (TruncatedPolynomial k p) h (Algebra.Extension.Cotangent.mk f) = 0

def notFormallySmooth : Prop := ∀ (k : Type u) [Field k] (p : ℕ),
  p.Prime → ∀ [CharP k p],
  ¬ formallySmoothValue k (TruncatedPolynomial k p)

end
end Specs.AdvCommAlg.FormalLifting.InseparableExample
