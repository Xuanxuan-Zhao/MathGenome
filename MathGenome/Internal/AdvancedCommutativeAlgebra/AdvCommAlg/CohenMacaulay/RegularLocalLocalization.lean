import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularLocalLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.ResidueFieldRegularity
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay

/-- The canonical map from R/p to the residue field at p. -/
noncomputable def quotientToPrimeResidue (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] : (R ⧸ p) →ₗ[R] p.ResidueField :=
  (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap

/-- The residue field at p is the localization of R/p at the complement of p. -/
instance quotientToPrimeResidue_isLocalizedModule (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    IsLocalizedModule p.primeCompl (quotientToPrimeResidue R p) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := p.ResidueField) R p.ResidueField).commutes]
    apply IsUnit.map
    apply isUnit_iff_ne_zero.mpr
    exact fun h => s.2 (Ideal.algebraMap_residueField_eq_zero.mp h)
  surj y := by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    refine ⟨⟨Ideal.Quotient.mk p a, s⟩, ?_⟩
    change (s : R) • IsLocalRing.residue (Localization.AtPrime p)
      (IsLocalization.mk' (Localization.AtPrime p) a s) = algebraMap R p.ResidueField a
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization.AtPrime p),
      IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, mul_comm, IsLocalization.mk'_spec]
    rfl
  exists_of_eq {a b} h := by
    have hab : a = b := p.injective_algebraMap_quotient_residueField h
    exact ⟨1, by simpa using hab⟩

/-- Identification over R_p, including the scalar action used by projective dimension. -/
noncomputable def localizedQuotientResidueEquiv (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    ((ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl) ≃ₗ[Localization.AtPrime p]
      p.ResidueField :=
by
  let M : ModuleCat.{u} R := ModuleCat.of R (R ⧸ p)
  haveI : IsLocalizedModule p.primeCompl
      (M.localizedModuleMkLinearMap p.primeCompl) :=
    ModuleCat.localizedModule_isLocalizedModule M p.primeCompl
  let e : M.localizedModule p.primeCompl ≃ₗ[R] p.ResidueField :=
    IsLocalizedModule.linearEquiv p.primeCompl
      (M.localizedModuleMkLinearMap p.primeCompl) (quotientToPrimeResidue R p)
  exact e.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)

/-- Apply the exact localization functor and identify its augmentation with κ(p). -/
noncomputable def localizeQuotientResolution (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ p))) :
    ProjectiveResolution (ModuleCat.of (Localization.AtPrime p) p.ResidueField) := by
  let F := ModuleCat.localizedModuleFunctor.{u} p.primeCompl
  let Q := F.mapProjectiveResolution P
  let e := (localizedQuotientResidueEquiv R p).toModuleIso
  exact { Q with
    π := Q.π ≫ (ChainComplex.single₀ _).map e.hom
    quasiIso := by infer_instance }


/-- Localization preserves the bound on the length of the resolution. -/
theorem localizedQuotient_boundedResolution :
    Specs.localizedQuotient_boundedResolutionType.{u} := by
  intro R _ p _ P n hP
  refine ⟨localizeQuotientResolution R p P, rfl, ?_⟩
  intro i hi
  let := hP i hi
  change Subsingleton ((P.complex.X i).localizedModule p.primeCompl)
  exact (equivShrink (LocalizedModule p.primeCompl (P.complex.X i))).symm.injective.subsingleton

theorem residueField_localization_projectiveDimension_le :
    Specs.residueField_localization_projectiveDimension_leType.{u} := by
  intro R _ p _
  rw [← ModuleCat.projectiveDimension_eq_of_linearEquiv (localizedQuotientResidueEquiv R p)]
  exact ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule
    p.primeCompl (ModuleCat.of R (R ⧸ p))

/-- CM-19, prime-localization assertion. -/
theorem regularLocal_localization_atPrime :
    Specs.regularLocal_localization_atPrimeType.{u} := by
  intro R _ _ p _
  obtain ⟨xs, _, hd, _⟩ := exists_regular_generators R
  have hb := (residueField_localization_projectiveDimension_le R p).trans
    (regularLocal_projectiveDimension_le R (ModuleCat.of R (R ⧸ p)) xs.length hd)
  have hne : projectiveDimension
      (ModuleCat.of (Localization.AtPrime p) p.ResidueField) ≠ ⊥ := by
    intro hz
    have : Subsingleton (ModuleCat.of (Localization.AtPrime p) p.ResidueField) :=
      ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff _).mp hz)
    exact not_subsingleton _ this
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← he] at hb
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp (WithBot.coe_le_coe.mp hb)
  apply regularLocal_of_residueField_projectiveDimension_eq_nat n (Localization.AtPrime p)
  simpa [hn] using he.symm

end AdvCommAlg.CohenMacaulay
