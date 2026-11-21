import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Type
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension

/-!
Independent specifications for GC-01, paper.tex:4380–4406.
The socle, residue-field actions, and finite-module type are the canonical
objects of DP-05. Injective dimension is Mathlib's categorical dimension in
`WithBot ℕ∞`: zero modules have dimension `⊥`, and finite means different
from `⊤`. `IsLocalRing` includes the nonzero-ring hypothesis.
-/

universe u
open CategoryTheory

namespace AdvCommAlg.Gorenstein.Specs

def socleType := ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M], Submodule R M

abbrev socleValue : socleType.{u} :=
  fun R _ _ M _ _ => Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)

def mem_socle_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (x : M),
    x ∈ socleValue R M ↔ ∀ a ∈ IsLocalRing.maximalIdeal R, a • x = 0

def hom_socle_equivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M],
    ∃ e : Depth.ResidueHom R M ≃ₗ[IsLocalRing.ResidueField R] socleValue R M,
      ∀ g, (e g).val = g 1

/-- Evaluation equivalences commute with every R-linear map of target modules. -/
def hom_socle_naturalType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (eM : Depth.ResidueHom R M ≃ₗ[IsLocalRing.ResidueField R] socleValue R M)
    (eN : Depth.ResidueHom R N ≃ₗ[IsLocalRing.ResidueField R] socleValue R N),
    (∀ g, (eM g).val = g 1) → (∀ g, (eN g).val = g 1) →
    ∀ (f : M →ₗ[R] N) (g : Depth.ResidueHom R M),
      (eN (f.comp g)).val = f (eM g).val

def ringTypeType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R], ℕ

noncomputable def ringTypeValue : ringTypeType.{u} :=
  fun R _ _ _ => Depth.Specs.moduleTypeValue R (ModuleCat.of R R)

def FiniteInjectiveDimensionType := ∀ (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M], Prop

noncomputable def FiniteInjectiveDimensionValue : FiniteInjectiveDimensionType.{u} :=
  fun R _ M _ _ => injectiveDimension (ModuleCat.of R M) ≠ ⊤

def finiteInjectiveDimension_iff_exists_boundType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M],
    FiniteInjectiveDimensionValue R M ↔
      ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of R M) n

def LocalGorensteinType :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R], Prop

noncomputable def LocalGorensteinValue : LocalGorensteinType.{u} :=
  fun R _ _ _ => FiniteInjectiveDimensionValue R R

def GorensteinRingType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], Prop

noncomputable def GorensteinRingValue : GorensteinRingType.{u} :=
  fun R _ _ => ∀ p : PrimeSpectrum R, LocalGorensteinValue (Localization.AtPrime p.asIdeal)

def IsCanonicalModuleType :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], Prop

/-- This predicate includes the CM condition on the base ring. Its domain is
finite modules; nonzeroness makes the DP-05 type apply in its source domain. -/
noncomputable def IsCanonicalModuleValue : IsCanonicalModuleType.{u} :=
  fun R _ _ _ M _ _ _ =>
    CohenMacaulay.Specs.LocalCohenMacaulayValue R R ∧ Nontrivial M ∧
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M ∧
    Depth.Specs.moduleTypeValue R (ModuleCat.of R M) = 1 ∧
    FiniteInjectiveDimensionValue R M

def isCanonicalModule_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.LocalCohenMacaulayValue R R →
    (IsCanonicalModuleValue R M ↔ Nontrivial M ∧
      CohenMacaulay.Specs.MaximalCohenMacaulayValue R M ∧
      Depth.Specs.moduleTypeValue R (ModuleCat.of R M) = 1 ∧
      FiniteInjectiveDimensionValue R M)

end AdvCommAlg.Gorenstein.Specs
