import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.InjectiveDimensionTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularQuotientExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.RegularReduction

noncomputable section

universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

namespace AdvCommAlg.Gorenstein.RegularReduction

open Depth.Rees ConcentratedChangeOfRings

variable {R : Type u} [CommRing R]

/-- For the regular module, the module quotient is the quotient ring itself. -/
def quotientRegularModuleEquiv (I : Ideal R) :
    quotientModule I (ModuleCat.of R R) ≃ₗ[R ⧸ I] (R ⧸ I) where
  toAddEquiv := (Submodule.quotEquivOfEq
    (I • (⊤ : Submodule R R)) I (by rw [Ideal.smul_eq_mul, Ideal.mul_top])).toAddEquiv
  map_smul' a q := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction q using Submodule.Quotient.induction_on with
    | _ s => rfl

/-- Ext over the quotient ring is Ext over the original ring shifted by one.
The coefficient is identified with the regular quotient module. -/
def regularQuotientExtEquiv (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{u} (R ⧸ Ideal.span {x})) (i : ℕ) :
    Ext M (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) i ≃+
      Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj M)
        (ModuleCat.of R R) (i + 1) := by
  let e := Classical.choice (RegularQuotientExt.comparison R x (ModuleCat.of R R) hx hx i)
  exact (coefficientExtLinearEquiv
    (quotientRegularModuleEquiv (Ideal.span {x})).symm.toModuleIso M i).toAddEquiv.trans
      ((e.app (Opposite.op M)).toLinearEquiv.toAddEquiv.trans
        (firstExtAddEquiv _ M (ModuleCat.of R R) (i + 1)))

/-- A bound for self-injective dimension descends to a regular quotient. -/
lemma quotient_injectiveDimension_bound (x : R) (hx : IsSMulRegular R x) (n : ℕ)
    [HasInjectiveDimensionLE (ModuleCat.of R R) n] :
    HasInjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) n := by
  apply HasInjectiveDimensionLT.mk
  intro i hi M a
  let e := regularQuotientExtEquiv x hx M i
  have hvan := HasInjectiveDimensionLT.subsingleton (ModuleCat.of R R) (n + 1)
    (i + 1) (by omega)
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj M)
  exact e.injective (by simpa using hvan.elim (e a) 0)

variable [IsNoetherianRing R] [IsLocalRing R]

/-- Give the original residue field the quotient-ring action induced by
the factor map R/(x) → R/m. -/
def quotientResidueModule (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ModuleCat.{u} (R ⧸ Ideal.span {x}) := by
  let f : (R ⧸ Ideal.span {x}) →+* IsLocalRing.ResidueField R :=
    Ideal.Quotient.factor (Ideal.span_le.mpr (by simpa using hx))
  letI := Module.compHom (IsLocalRing.ResidueField R) f
  exact ModuleCat.of _ (IsLocalRing.ResidueField R)

/-- Restricting that quotient action recovers the original residue module. -/
def quotientResidueRestrictEquiv (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ModuleCat.of R (IsLocalRing.ResidueField R) ≃ₗ[R]
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
        (quotientResidueModule x hx)) where
  toAddEquiv := AddEquiv.refl _
  map_smul' _ _ := rfl

/-- The bound in the other direction increases by at most one. -/
lemma injectiveDimension_bound_of_quotient (x : R)
    (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hx : IsSMulRegular R x) (n : ℕ)
    [HasInjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) n] :
    HasInjectiveDimensionLE (ModuleCat.of R R) (n + 1) := by
  apply (injectiveDimension_le_iff (ModuleCat.of R R) (n + 1)).mp
  apply (InjectiveDimensionTest.injectiveDimension_le_iff_residue_ext
    R (ModuleCat.of R R) (n + 1)).mpr
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    let M := quotientResidueModule x hxmem
    haveI := HasInjectiveDimensionLT.subsingleton
      (ModuleCat.of (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) (n + 1)
      i (by omega) M
    haveI : Subsingleton (Ext
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj M)
        (ModuleCat.of R R) (i + 1)) :=
      (regularQuotientExtEquiv x hx M i).symm.injective.subsingleton
    exact FiniteExtDetection.subsingleton_ext_of_linearEquiv
      (quotientResidueRestrictEquiv x hxmem) (i + 1)

/-- GC-06: reduction by a regular element preserves and detects the
finite-self-injective-dimension Gorenstein condition. -/
theorem localGorenstein_quotient_iff (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (x : R)
    (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hx : IsSMulRegular R x) :
    letI := quotientLocalRing x hxmem
    LocalGorenstein R ↔ LocalGorenstein (R ⧸ Ideal.span {x}) := by
  letI := quotientLocalRing x hxmem
  change FiniteInjectiveDimension R R ↔
    FiniteInjectiveDimension (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})
  rw [finiteInjectiveDimension_iff_exists_bound,
    finiteInjectiveDimension_iff_exists_bound]
  constructor
  · rintro ⟨n, hn⟩
    letI := hn
    exact ⟨n, quotient_injectiveDimension_bound x hx n⟩
  · rintro ⟨n, hn⟩
    letI := hn
    exact ⟨n + 1, injectiveDimension_bound_of_quotient x hxmem hx n⟩

end AdvCommAlg.Gorenstein.RegularReduction
