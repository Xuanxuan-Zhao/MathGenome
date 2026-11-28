import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.LocallyNilpotentExponential

/-! Simple reflection automorphisms and the multiplicities of real roots. -/

namespace Specs.LieNotes.Contragredient.ReflectionAutomorphisms

open CartanData CartanQuotient WeightExtraction
open _root_.LieNotes.Contragredient.LocallyNilpotentExponential

noncomputable section

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

set_option linter.checkUnivs false in
def CartanReflectionType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → I → (H →ₗ[ℂ] H)

/-- The simple reflection on the Cartan space. -/
def cartanReflection (R : Realization A H) (i : I) : H →ₗ[ℂ] H :=
  LinearMap.id - (R.α i).smulRight (R.h i)

set_option linter.checkUnivs false in
def ReflectionAutomorphismPredicateType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H), I → (Algebra R ≃ₗ⁅ℂ⁆ Algebra R) → Prop

/-- The specified Lie automorphism acts by the three pointwise finite exponentials. -/
def IsReflectionAutomorphism (R : Realization A H) (i : I)
    (r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R) : Prop :=
  let E := LieAlgebra.ad ℂ (Algebra R) (e R i)
  let F := LieAlgebra.ad ℂ (Algebra R) (f R i)
  ∃ (hE : LocallyNilpotent E) (hF : LocallyNilpotent F),
    ∀ x : Algebra R, r x = exp E hE (exp (-F) hF.neg (exp E hE x))

def ReflectionAutomorphismExistsUnique : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I),
    ∃! r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R, IsReflectionAutomorphism R i r

def CartanReflectionInvolutive : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I),
    Function.Involutive (cartanReflection R i)

def ReflectionAutomorphismOnCartan : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I)
    {r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R},
    IsReflectionAutomorphism R i r →
      ∀ h : H, r (cartan R h) = cartan R (cartanReflection R i h)

/-- The full image of the common eigenspace is the reflected eigenspace. -/
def ReflectionAutomorphismOnWeightSpaces : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I)
    {r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R},
    IsReflectionAutomorphism R i r →
      ∀ β : Module.Dual ℂ H,
        (weightSpace (cartanAdjoint R) β).map r.toLinearEquiv.toLinearMap =
          weightSpace (cartanAdjoint R) (R.weightReflection i β)

/-- Each simple reflection maps the integral root lattice onto itself. -/
def RootLatticePreserved : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (i : I),
    R.weightReflection i '' Set.range R.rootWeight = Set.range R.rootWeight

/-- Every finite composition of simple reflections applied to a simple root has
a one-dimensional adjoint weight space. -/
def RealRootMultiplicity : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (j : I) (w : List I),
    Module.rank ℂ
      (weightSpace (cartanAdjoint R)
        (w.foldr (fun i β ↦ R.weightReflection i β) (R.α j))) = 1

end
end Specs.LieNotes.Contragredient.ReflectionAutomorphisms
