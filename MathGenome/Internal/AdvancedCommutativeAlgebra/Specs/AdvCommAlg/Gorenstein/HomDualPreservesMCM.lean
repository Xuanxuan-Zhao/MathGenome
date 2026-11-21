import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FiniteLengthDuality
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! GC-12, Hom comparison and preservation of maximal CM modules.
All reductions use the canonical quotient action, and the comparison is
specified on representatives, so its naturality includes evaluation. -/
noncomputable section
universe u
open scoped Pointwise
namespace AdvCommAlg.Gorenstein.HomDualSpec

variable {R : Type u} [CommRing R]

abbrev Reduction (x : R) (M : Type u) [AddCommGroup M] [Module R M] :=
  M ⧸ (Ideal.span {x} • (⊤ : Submodule R M))

def reductionMap (x : R) {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x N :=
  ((Ideal.span {x} • (⊤ : Submodule R M)).mapQ
    (Ideal.span {x} • (⊤ : Submodule R N)) f (by
      rw [Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul]
      intro m hm
      obtain ⟨n, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
      change f (x • n) ∈ x • (⊤ : Submodule R N)
      rw [f.map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective

@[simp] theorem reductionMap_mk (x : R) {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (m : M) :
    reductionMap x f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl

/-- The conclusion includes finiteness, the zero convention, and detection of nonzero modules. -/
def preservesMCMType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    Module.Finite R (M →ₗ[R] W) ∧
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R (M →ₗ[R] W) ∧
    (Nontrivial (M →ₗ[R] W) ↔ Nontrivial M)

/-- A quotient-ring-linear comparison, induced by reducing every map. -/
def reductionType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    ∀ (x : R) (xs : List R), CohenMacaulay.Specs.IsSystemOfParametersValue R R (x :: xs) →
    ∃ e : Reduction x (M →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
        (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W),
      ∀ f : M →ₗ[R] W, e (Submodule.Quotient.mk f) = reductionMap x f

/-- Regularity required in the evaluation comparison, including the zero module. -/
def regularityType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    ∀ (x : R) (xs : List R), CohenMacaulay.Specs.IsSystemOfParametersValue R R (x :: xs) →
    IsSMulRegular M x ∧ IsSMulRegular (M →ₗ[R] W) x ∧
      IsSMulRegular ((M →ₗ[R] W) →ₗ[R] W) x

/-- Naturality in the source, expressed without any choices of inverse maps. -/
def naturalityType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : R)
    (M N W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup W] [Module R W]
    (f : M →ₗ[R] N) (g : N →ₗ[R] W),
    reductionMap x (g.comp f) = (reductionMap x g).comp (reductionMap x f)

/-- The reduced evaluation square commutes. This equation determines it on all
representatives of both reductions and hence on the entire quotient. -/
def evaluationType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : R)
    (M W : Type u) [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]
    (e : Reduction x (M →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
      (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W)),
    (∀ f, e (Submodule.Quotient.mk f) = reductionMap x f) →
    ∀ (m : M) (f : M →ₗ[R] W),
      reductionMap x (envelopeEvaluation R W M m) (Submodule.Quotient.mk f) =
        e (Submodule.Quotient.mk f) (Submodule.Quotient.mk m)

/-- The complete square: the comparison on D(M) sends reduced evaluation to
quotient-ring evaluation precomposed with the comparison on M. -/
def evaluationSquareType : Prop :=
  ∀ (R : Type u) [CommRing R] (x : R)
    (M W : Type u) [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]
    (eM : Reduction x (M →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
      (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W))
    (eD : Reduction x ((M →ₗ[R] W) →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
      (Reduction x (M →ₗ[R] W) →ₗ[R ⧸ Ideal.span {x}] Reduction x W)),
    (∀ f, eM (Submodule.Quotient.mk f) = reductionMap x f) →
    (∀ g, eD (Submodule.Quotient.mk g) = reductionMap x g) →
    eD.toLinearMap.comp (reductionMap x (envelopeEvaluation R W M)) =
      (LinearMap.lcomp (R ⧸ Ideal.span {x}) (Reduction x W) eM.toLinearMap).comp
        (envelopeEvaluation (R ⧸ Ideal.span {x}) (Reduction x W) (Reduction x M))

/-- The evaluation comparison with both comparison isomorphisms supplied under
exactly the canonical-module and MCM hypotheses. -/
def evaluationComparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    ∀ (x : R) (xs : List R), CohenMacaulay.Specs.IsSystemOfParametersValue R R (x :: xs) →
    ∃ (eM : Reduction x (M →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
        (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W))
      (eD : Reduction x ((M →ₗ[R] W) →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
        (Reduction x (M →ₗ[R] W) →ₗ[R ⧸ Ideal.span {x}] Reduction x W)),
      (∀ f, eM (Submodule.Quotient.mk f) = reductionMap x f) ∧
      (∀ g, eD (Submodule.Quotient.mk g) = reductionMap x g) ∧
      eD.toLinearMap.comp (reductionMap x (envelopeEvaluation R W M)) =
        (LinearMap.lcomp (R ⧸ Ideal.span {x}) (Reduction x W) eM.toLinearMap).comp
          (envelopeEvaluation (R ⧸ Ideal.span {x}) (Reduction x W) (Reduction x M))

end AdvCommAlg.Gorenstein.HomDualSpec
