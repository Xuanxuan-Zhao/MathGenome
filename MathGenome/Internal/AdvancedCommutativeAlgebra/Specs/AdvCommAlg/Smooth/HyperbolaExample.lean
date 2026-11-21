import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocalJacobianCriterion

/-! The hyperbola part of SM-16 (paper.tex, 1469–1477).
The base can be any commutative ring, including the zero ring. -/
namespace Specs.AdvCommAlg.Smooth.HyperbolaExample

universe u
noncomputable section
open MvPolynomial

/-- The equation in the specified two-variable polynomial ring. -/
def equation {A : Type u} [CommRing A] (b : A) : MvPolynomial (Fin 2) A :=
  X 0 * X 1 - C b

/-- The literal quotient A[X,Y]/(XY-b), with its canonical algebra structures. -/
abbrev Hyperbola (A : Type u) [CommRing A] (b : A) :=
  MvPolynomial (Fin 2) A ⧸ Ideal.span {equation b}

def coordinate {A : Type u} [CommRing A] (b : A) (i : Fin 2) : Hyperbola A b :=
  Ideal.Quotient.mk _ (X i)

/-- The prescribed, single equation as an element of the presentation kernel. -/
def relationFamily {A : Type u} [CommRing A] (b : A) :
    Fin 1 → RingHom.ker (algebraMap (MvPolynomial (Fin 2) A) (Hyperbola A b)) :=
  fun _ => ⟨equation b, by
    change Ideal.Quotient.mk _ (equation b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))⟩

/-- Evaluation at (0,0) on the special fiber b=0. -/
def originEvaluation (k : Type u) [Field k] : Hyperbola k 0 →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ : Fin 2 => (0 : k))) (by
    change Ideal.span {equation (0 : k)} ≤ RingHom.ker (aeval (fun _ : Fin 2 => (0 : k)))
    rw [Ideal.span_le]
    rintro p (rfl : p = equation (0 : k))
    simp [equation])

/-- The origin is the prime kernel of evaluation at (0,0). Its equality with
(Xbar,Ybar) is one of the required conclusions below. -/
def origin (k : Type u) [Field k] : PrimeSpectrum (Hyperbola k 0) :=
  ⟨RingHom.ker (originEvaluation k), RingHom.ker_isPrime _⟩

/-- Each chart admits a finite submersive presentation with variables minus
relations equal to one. This canonical predicate includes the presentation witness. -/
def charts : Prop := ∀ (A : Type u) [CommRing A] (b : A),
  Algebra.IsStandardSmoothOfRelativeDimension 1 A (Localization.Away (coordinate b 0)) ∧
  Algebra.IsStandardSmoothOfRelativeDimension 1 A (Localization.Away (coordinate b 1))

def originIdeal : Prop := ∀ (k : Type u) [Field k],
  (origin k).asIdeal = Ideal.span (Set.range (coordinate (0 : k)))

/-- The equation is a minimal generating family of the actual localized
kernel at the inverse image of the origin, as required by SM-10. -/
def originMinimalRelation : Prop := ∀ (k : Type u) [Field k],
  LocalJacobianCriterion.IsMinimalLocalGeneratingFamily
    (Ideal.Quotient.mk_surjective : Function.Surjective
      (algebraMap (MvPolynomial (Fin 2) k) (Hyperbola k 0)))
    (origin k) (relationFamily (0 : k))

def originNotSmooth : Prop := ∀ (k : Type u) [Field k],
  ¬ isSmoothAtValue k (Hyperbola k 0) (origin k)

end
end Specs.AdvCommAlg.Smooth.HyperbolaExample
