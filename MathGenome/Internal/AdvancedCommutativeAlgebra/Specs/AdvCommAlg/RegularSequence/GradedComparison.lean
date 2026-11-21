import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AlgebraCore.P103.Ch07.ReesGradedConstruction
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.TensorProduct.Basis
/-! Canonical objects for RK-11. The Rees quotient model is identified with the
direct sum of successive quotients by `P103.Rees.component_identifications` and
`P103.Rees.module_internal`. Module-valued polynomials use scalar extension.
All rings and modules, including zero objects, are allowed. -/

namespace AdvCommAlg.RegularSequence.GradedComparison.Core
open scoped TensorProduct
open P103.Rees
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
instance associatedRTower : IsScalarTower R (AssociatedRing I) (AssociatedModule I M) :=
  IsScalarTower.of_algebraMap_smul (A := AssociatedRing I) (M := AssociatedModule I M) fun r m =>
    (IsScalarTower.algebraMap_smul (R := ReesAlgebra I) (AssociatedRing I)
      (algebraMap R (ReesAlgebra I) r) m).trans
      (IsScalarTower.algebraMap_smul (ReesAlgebra I) r m)
instance associatedBaseModule : Module (R ⧸ I) (AssociatedModule I M) :=
  Module.compHom (AssociatedModule I M) (algebraMap (R ⧸ I) (AssociatedRing I))
instance associatedBaseModuleTower : IsScalarTower (R ⧸ I) (AssociatedRing I) (AssociatedModule I M) :=
  IsScalarTower.of_compHom _ _ _
instance associatedBaseRTower : IsScalarTower R (R ⧸ I) (AssociatedModule I M) :=
  IsScalarTower.of_algebraMap_smul (A := R ⧸ I) (M := AssociatedModule I M) fun r m => by
    change (algebraMap R (AssociatedRing I) r) • m = _
    exact IsScalarTower.algebraMap_smul (AssociatedRing I) r m

def constantLinear : M →ₗ[R] ReesModule I M where
  toFun := constant I M
  map_add' := constant_add I M
  map_smul' := constant_smul I M

def constantClassR : M →ₗ[R] AssociatedModule I M where
  toFun m := Submodule.Quotient.mk (constant I M m)
  map_add' a b := by rw [constant_add, Submodule.Quotient.mk_add]
  map_smul' r m := by rw [constant_smul, Submodule.Quotient.mk_smul]; rfl

def coefficientR : (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R] AssociatedModule I M :=
  (I • ⊤ : Submodule R M).liftQ (constantClassR I M) (by
      intro m hm
      change moduleClass I M 0 ⟨m, by simp⟩ = 0
      apply (moduleClass_eq_zero_iff I M 0 _).mpr
      simpa using hm)

def coefficient : (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R ⧸ I] AssociatedModule I M :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective) (coefficientR I M)

/-- The coefficient module M/IM. -/
abbrev Coefficients := M ⧸ (I • ⊤ : Submodule R M)

variable (x : List R)

/-- The source ideal, with the ordering retained in the variable indexing. -/
abbrev sequenceIdeal : Ideal R := Ideal.ofList x

abbrev PolynomialRing := MvPolynomial (Fin x.length) (R ⧸ sequenceIdeal x)

/-- This tensor product is (M/IM)[X_1,...,X_r]. -/
abbrev PolynomialModule := PolynomialRing x ⊗[R ⧸ sequenceIdeal x] Coefficients (sequenceIdeal x) M

def monomialValue (d : Fin x.length →₀ ℕ) : R := d.prod fun i k => x[i] ^ k
theorem monomial_mem (d : Fin x.length →₀ ℕ) : monomialValue x d ∈ sequenceIdeal x ^ d.degree := by
  classical
  have h := Ideal.prod_mem_prod (I := fun i => sequenceIdeal x ^ d i)
    (s := d.support) (x := fun i => x[i] ^ d i) (fun i _ =>
      Ideal.pow_mem_pow (I := sequenceIdeal x) (Ideal.subset_span (List.getElem_mem i.isLt)) (d i))
  simpa only [monomialValue, Finsupp.prod, Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum] using h

/-- The standard finite-coefficient representation of module-valued polynomials. -/
def polynomialCoefficients : PolynomialModule M x ≃ₗ[R ⧸ sequenceIdeal x]
    ((Fin x.length →₀ ℕ) →₀ Coefficients (sequenceIdeal x) M) :=
  TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials _ _)

/-- Homogeneity means that all nonzero coefficients have the displayed total degree. -/
def PolynomialHomogeneous (n : ℕ) (p : PolynomialModule M x) : Prop :=
  ∀ d, polynomialCoefficients M x p d ≠ 0 → d.degree = n

/-- Evaluation of a homogeneous finite sum before passing to the successive quotient. -/
def homogeneousEvaluation (n : ℕ) (s : Finset (Fin x.length →₀ ℕ))
    (hd : ∀ d ∈ s, d.degree = n) (m : (Fin x.length →₀ ℕ) → M) :
    (sequenceIdeal x ^ n • (⊤ : Submodule R M) : Submodule R M) :=
  ⟨∑ d ∈ s, monomialValue x d • m d, Submodule.sum_mem _ fun d hd' => by
    have h := Submodule.smul_mem_smul (N := (⊤ : Submodule R M))
      (monomial_mem x d) (show m d ∈ (⊤ : Submodule R M) from trivial)
    rwa [hd d hd'] at h⟩

/-- The class of x_i in degree one of the associated ring. -/
def initialForm (i : Fin x.length) : AssociatedRing (sequenceIdeal x) :=
  ringClass (sequenceIdeal x) 1 ⟨x[i], by
    rw [pow_one]
    exact Ideal.subset_span (List.getElem_mem i.isLt)⟩

/-- Evaluation at the degree-one initial forms; this is an algebra homomorphism. -/
def ringComparison : PolynomialRing x →ₐ[R ⧸ sequenceIdeal x] AssociatedRing (sequenceIdeal x) :=
  MvPolynomial.aeval (initialForm x)

instance polynomialModuleAction : Module (PolynomialRing x) (AssociatedModule (sequenceIdeal x) M) :=
  Module.compHom _ (ringComparison x).toRingHom

instance polynomialModuleTower : IsScalarTower (R ⧸ sequenceIdeal x) (PolynomialRing x)
    (AssociatedModule (sequenceIdeal x) M) :=
  IsScalarTower.of_algebraMap_smul (A := PolynomialRing x)
    (M := AssociatedModule (sequenceIdeal x) M) fun r m => by
      change (ringComparison x (algebraMap (R ⧸ sequenceIdeal x) (PolynomialRing x) r)) • m = _
      rw [(ringComparison x).commutes]
      rfl

/-- The canonical comparison, linear over the displayed polynomial ring. -/
def comparison : PolynomialModule M x →ₗ[PolynomialRing x] AssociatedModule (sequenceIdeal x) M :=
  (coefficient (sequenceIdeal x) M).liftBaseChange (PolynomialRing x)

/-- Quasi-regularity uses this exact evaluation map and the nonzero coefficient module. -/
def QuasiRegular : Prop :=
  Function.Bijective (comparison M x) ∧ Nontrivial (Coefficients (sequenceIdeal x) M)

end
end AdvCommAlg.RegularSequence.GradedComparison.Core

/-! Independent closed contracts for the constructions and their full properties.
The canonical objects above are shared definitions; no candidate module is imported. -/
universe u v
namespace AdvCommAlg.RegularSequence.GradedComparison.Specs
open scoped TensorProduct
open P103.Rees Core
noncomputable section

abbrev AssociatedGraded {R : Type u} [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (x : List R) :=
  AssociatedModule (sequenceIdeal x) M

def AssociatedGradedType := ∀ {R : Type u} [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], List R → Type v

def AssociatedGradedValue : AssociatedGradedType.{u, v} :=
  fun {_} _ M _ _ x => AssociatedModule (sequenceIdeal x) M

def comparisonType := ∀ {R : Type u} [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M] (x : List R),
  Core.PolynomialModule M x →ₗ[PolynomialRing x] AssociatedModule (sequenceIdeal x) M

def comparisonValue : comparisonType.{u, v} :=
  fun {_} _ M _ _ x => Core.comparison M x

def ringComparisonType := ∀ {R : Type u} [CommRing R] (x : List R),
  PolynomialRing x →ₐ[R ⧸ sequenceIdeal x] AssociatedRing (sequenceIdeal x)

def ringComparisonValue : ringComparisonType.{u} :=
  fun {_} _ x => Core.ringComparison x

def QuasiRegularType := ∀ {R : Type u} [CommRing R] (M : Type v)
  [AddCommGroup M] [Module R M], List R → Prop

def QuasiRegularValue : QuasiRegularType.{u, v} :=
  fun {_} _ M _ _ x =>
    Function.Bijective (Core.comparison M x) ∧ Nontrivial (Coefficients (sequenceIdeal x) M)


def ringComparison_monomialType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R) (d : Fin x.length →₀ ℕ) (r : R),
    ringComparison x (MvPolynomial.monomial d (Ideal.Quotient.mk (sequenceIdeal x) r)) =
      ringClass (sequenceIdeal x) d.degree
        ⟨monomialValue x d * r, (sequenceIdeal x ^ d.degree).mul_mem_right r (monomial_mem x d)⟩


def comparison_degreewise_surjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (n : ℕ) (q : AssociatedGraded M x)
    (hq : q ∈ modulePiece (sequenceIdeal x) M n),
    ∃ p : Core.PolynomialModule M x,
      PolynomialHomogeneous M x n p ∧ comparison M x p = q


def quasiRegular_homogeneous_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (hx : QuasiRegular M x)
    (n : ℕ) (p : Core.PolynomialModule M x),
    PolynomialHomogeneous M x n p ↔ comparison M x p ∈ modulePiece (sequenceIdeal x) M n


def comparison_ring_identificationType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    ∃ s : Core.PolynomialModule R x ≃ₗ[R ⧸ sequenceIdeal x] PolynomialRing x,
    ∃ t : AssociatedModule (sequenceIdeal x) R ≃ₗ[AssociatedRing (sequenceIdeal x)]
      AssociatedRing (sequenceIdeal x),
      (∀ (p : PolynomialRing x) (r : R),
        s (p ⊗ₜ Submodule.Quotient.mk r) = Ideal.Quotient.mk (sequenceIdeal x) r • p) ∧
      (∀ r : R, t (Submodule.Quotient.mk (constant (sequenceIdeal x) R r)) =
        algebraMap (R ⧸ sequenceIdeal x) (AssociatedRing (sequenceIdeal x))
          (Ideal.Quotient.mk (sequenceIdeal x) r)) ∧
      (∀ (n : ℕ) (a : (sequenceIdeal x ^ n : Ideal R)),
        t (moduleClass (sequenceIdeal x) R n
          ⟨a.1, by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact a.2⟩) =
            ringClass (sequenceIdeal x) n a) ∧
      (∀ p, t (Core.comparison R x p) = Core.ringComparison x (s p)) ∧
      (∀ p q : PolynomialRing x,
        t (Core.comparison R x (s.symm (p * q))) =
          t (Core.comparison R x (s.symm p)) * t (Core.comparison R x (s.symm q)))


def quasiRegular_iff_exists_linearEquivType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
    QuasiRegular M x ↔
      (∃ e : Core.PolynomialModule M x ≃ₗ[PolynomialRing x] AssociatedGraded M x,
        (e : Core.PolynomialModule M x → AssociatedGraded M x) = comparison M x) ∧
      Nontrivial (Coefficients (sequenceIdeal x) M)


def ringComparison_XType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R) (i : Fin x.length),
    ringComparison x (MvPolynomial.X i) = initialForm x i


def comparison_tmulType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (p : PolynomialRing x) (m : M),
    comparison M x (p ⊗ₜ (Submodule.Quotient.mk m)) =
      ringComparison x p • (Submodule.Quotient.mk (constant (sequenceIdeal x) M m) :
        AssociatedGraded M x)


def generators_spanType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    Ideal.span (Set.range (fun i : Fin x.length => x[i])) = sequenceIdeal x


def ringComparison_surjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    Function.Surjective (ringComparison x)


def comparison_surjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
    Function.Surjective (comparison M x)


def comparison_monomialType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (d : Fin x.length →₀ ℕ) (m : M),
    comparison M x (MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk m) =
      moduleClass (sequenceIdeal x) M d.degree
        ⟨monomialValue x d • m, Submodule.smul_mem_smul (monomial_mem x d) Submodule.mem_top⟩


def comparison_homogeneous_sumType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (n : ℕ) (s : Finset (Fin x.length →₀ ℕ))
    (hd : ∀ d ∈ s, d.degree = n) (m : (Fin x.length →₀ ℕ) → M),
    comparison M x (∑ d ∈ s, MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk (m d)) =
      moduleClass (sequenceIdeal x) M n (homogeneousEvaluation M x n s hd m)


def polynomial_expansionType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (p : Core.PolynomialModule M x),
    p = (polynomialCoefficients M x p).sum
      (fun d m => MvPolynomial.monomial d 1 ⊗ₜ m)


def comparison_homogeneousType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (n : ℕ) (p : Core.PolynomialModule M x)
    (hp : PolynomialHomogeneous M x n p),
    comparison M x p ∈ modulePiece (sequenceIdeal x) M n


def ringComparison_mulType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R) (p q : PolynomialRing x),
    ringComparison x (p * q) = ringComparison x p * ringComparison x q


def comparison_smulType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (p : PolynomialRing x) (q : Core.PolynomialModule M x),
    comparison M x (p • q) = ringComparison x p • comparison M x q


def associatedGraded_componentsType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
    DirectSum.IsInternal (modulePiece (sequenceIdeal x) M) ∧
    (∀ n, ∃ e : ModuleComponent (sequenceIdeal x) M n ≃+ modulePiece (sequenceIdeal x) M n,
      ∀ m : (sequenceIdeal x ^ n • (⊤ : Submodule R M) : Submodule R M),
        (e (QuotientAddGroup.mk m) : AssociatedGraded M x) = moduleClass (sequenceIdeal x) M n m)


def coefficient_injectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (I : Ideal R),
    Function.Injective (coefficient I M)


def comparison_one_tmulType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (m : Coefficients (sequenceIdeal x) M),
    comparison M x (1 ⊗ₜ m) = coefficient (sequenceIdeal x) M m


def comparison_nil_bijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Function.Bijective (comparison M ([] : List R))


def quasiRegular_nil_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    QuasiRegular M ([] : List R) ↔ Nontrivial M


def comparison_bijective_of_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) [Subsingleton M],
    Function.Bijective (comparison M x)


def not_quasiRegular_of_subsingletonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) [Subsingleton M],
    ¬ QuasiRegular M x


def comparison_bijective_of_zero_ringType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) [Subsingleton R],
    Function.Bijective (comparison M x)


def not_quasiRegular_of_zero_ringType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : List R) [Subsingleton R],
    ¬ QuasiRegular M x


def ringComparison_homogeneousType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R) (n : ℕ) (p : PolynomialRing x)
    (hp : p.IsHomogeneous n),
    ringComparison x p ∈ ringPiece (sequenceIdeal x) n

end
end AdvCommAlg.RegularSequence.GradedComparison.Specs
