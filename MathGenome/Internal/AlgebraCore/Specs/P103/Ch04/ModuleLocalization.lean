import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Localization

/-!
Module localization, paper.tex 848–868 (the construction, exactness and
finite intersections), and the flatness consequence at line 873.
`LocalizedModule S M` is the fraction quotient, with its canonical
`Localization S`-module structure. No denominator regularity or nontriviality
is assumed. Local detection and finitely presented Hom base change are
separately allocated results.
-/
namespace P103.Ch04.ModuleLocalizationSpecs

universe u v w x

open TensorProduct

def FractionEquality : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (m n : M) (s t : S),
    LocalizedModule.mk m s = LocalizedModule.mk n t ↔
      ∃ a : S, (a : R) • ((t : R) • m - (s : R) • n) = 0

def FractionZero : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (m : M) (s : S),
    LocalizedModule.mk m s = 0 ↔ ∃ a : S, (a : R) • m = 0

def EveryElementIsFraction : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (z : LocalizedModule S M),
    ∃ (m : M) (s : S), z = LocalizedModule.mk m s

def ZeroDenominator : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M],
    (0 : R) ∈ S → Subsingleton (LocalizedModule S M)

def TensorEquivType :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M],
    (Localization S ⊗[R] M) ≃ₗ[Localization S] LocalizedModule S M

noncomputable def tensorEquivValue : TensorEquivType.{u,v} :=
  fun R _ S M _ _ => (LocalizedModule.equivTensorProduct S M).symm

def TensorFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (a : R) (s : S) (m : M),
    tensorEquivValue R S M (Localization.mk a s ⊗ₜ[R] m) =
      LocalizedModule.mk (a • m) s

def TensorInverseFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M] (m : M) (s : S),
    (tensorEquivValue R S M).symm (LocalizedModule.mk m s) =
      Localization.mk 1 s ⊗ₜ[R] m

def TensorNaturality : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (z : Localization S ⊗[R] M),
    tensorEquivValue R S N (TensorProduct.map LinearMap.id f z) =
      LocalizedModule.map S f (tensorEquivValue R S M z)

/-- Bridge to the single shared balanced tensor, including its outer scalar
structure and both fraction formulas. -/
def BalancedTensorEquiv : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M],
    letI := P103.BalancedTensor.commRightModule R (Localization S)
    ∃ act : Module (Localization S) (P103.BalancedTensor.Tensor R (Localization S) M),
      letI := act
      (∀ (a b : Localization S) (m : M),
        a • P103.BalancedTensor.tmul R b m = P103.BalancedTensor.tmul R (a * b) m) ∧
      ∃ e : P103.BalancedTensor.Tensor R (Localization S) M ≃ₗ[Localization S]
          LocalizedModule S M,
        (∀ (a : R) (s : S) (m : M),
          e (P103.BalancedTensor.tmul R (Localization.mk a s) m) =
            LocalizedModule.mk (a • m) s) ∧
        (∀ (m : M) (s : S), e.symm (LocalizedModule.mk m s) =
          P103.BalancedTensor.tmul R (Localization.mk 1 s) m)

def MapFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (m : M) (s : S),
    LocalizedModule.map S f (LocalizedModule.mk m s) = LocalizedModule.mk (f m) s

def PreservesExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (L : Type v) (M : Type w) (N : Type x)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N),
    Function.Exact f g → Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g)

def PreservesInjectivity : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N),
    Function.Injective f → Function.Injective (LocalizedModule.map S f)

def PreservesSurjectivity : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N),
    Function.Surjective f → Function.Surjective (LocalizedModule.map S f)

/-- The submodules are localized inside the same localized ambient module.
A finite set of indices includes the empty set, whose intersection is top. -/
def FiniteIntersections : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) (I : Finset ι) (P : ι → Submodule R M),
    (⨅ i ∈ I, P i).localized S = ⨅ i ∈ I, (P i).localized S

def Flat : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), Module.Flat R (Localization S)

end P103.Ch04.ModuleLocalizationSpecs
