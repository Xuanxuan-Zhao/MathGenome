import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Naturality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Localization
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! KD-16. Localization preserves relative derivations and their representing
modules. All rings and all multiplicative submonoids are allowed. -/
namespace AdvCommAlg.Differentials

universe u v w z
noncomputable section
open scoped TensorProduct

section Target
variable (A : Type u) (B : Type v) (T : Type w)
  [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
  (S : Submonoid B) [IsLocalization S T]

include S

/-- The canonical map on differentials has the universal property of scalar
extension to the localized ring. -/
theorem differential_isBaseChange :
    IsBaseChange T (KaehlerDifferential.map A A B T) := by
  exact IsLocalizedModule.isBaseChange S T _

variable (N : Type z) [AddCommGroup N] [Module T N] [Module B N] [Module A N]
  [IsScalarTower B T N] [IsScalarTower A T N] [IsScalarTower A B N]

/-- Extend a derivation using localization of the universal module. -/
def extendLocalizedDerivation (D : Derivation A B N) : Derivation A T N :=
  ((differential_isBaseChange A B T S).lift D.liftKaehlerDifferential).compDer
    (KaehlerDifferential.D A T)

theorem extendLocalizedDerivation_apply (D : Derivation A B N) (b : B) :
    extendLocalizedDerivation A B T S N D (algebraMap B T b) = D b := by
  change (differential_isBaseChange A B T S).lift D.liftKaehlerDifferential
    (KaehlerDifferential.D A T (algebraMap B T b)) = _
  rw [← KaehlerDifferential.map_D A A B T,
    IsBaseChange.lift_eq, Derivation.liftKaehlerDifferential_comp_D]

theorem localizedDerivation_ext (D E : Derivation A T N)
    (h : ∀ b : B, D (algebraMap B T b) = E (algebraMap B T b)) : D = E := by
  have hmaps : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (differential_isBaseChange A B T S).algHom_ext'
    apply Derivation.liftKaehlerDifferential_unique
      (R := A) (S := B) (M := N)
    ext b
    simpa using h b
  ext t
  simpa using congrArg (fun L : KaehlerDifferential A T →ₗ[T] N =>
    L (KaehlerDifferential.D A T t)) hmaps

theorem localizedDerivation_fraction (E : Derivation A T N) (b : B) (s : S) :
    E (IsLocalization.mk' T b s) =
      IsLocalization.mk' T 1 s • E (algebraMap B T b) -
        (algebraMap B T b * IsLocalization.mk' T 1 s ^ 2) •
          E (algebraMap B T (s : B)) := by
  have hinv : E (IsLocalization.mk' T 1 s) =
      -(IsLocalization.mk' T 1 s) ^ 2 • E (algebraMap B T (s : B)) :=
    E.leibniz_of_mul_eq_one (by simp)
  have hfrac : IsLocalization.mk' T b s =
      algebraMap B T b * IsLocalization.mk' T 1 s := by
    simpa only [Algebra.smul_def] using
      (IsLocalization.smul_mk'_one (S := T) b s).symm
  rw [hfrac, E.leibniz, hinv]
  simp only [neg_smul, smul_neg, ← mul_smul, sub_eq_add_neg]
  exact add_comm _ _

end Target

theorem localization_restriction_bijective :
    Specs.AdvCommAlg.Differentials.Localization.restrictionBijective.{u,v,w,z} := by
  intro A B T N _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _
  constructor
  · intro D E h
    apply localizedDerivation_ext A B T S N D E
    intro b
    exact congrArg (fun F : Derivation A B N => F b) h
  · intro D
    refine ⟨extendLocalizedDerivation A B T S N D, ?_⟩
    ext b
    exact extendLocalizedDerivation_apply A B T S N D b

theorem localization_unique_extension_formula :
    Specs.AdvCommAlg.Differentials.Localization.uniqueExtensionFormula.{u,v,w,z} := by
  intro A B T N _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ D
  refine ⟨extendLocalizedDerivation A B T S N D, ⟨?_, ?_⟩, ?_⟩
  · exact extendLocalizedDerivation_apply A B T S N D
  · intro b s
    rw [localizedDerivation_fraction A B T S N]
    rw [extendLocalizedDerivation_apply, extendLocalizedDerivation_apply]
  · intro E hE
    apply localizedDerivation_ext A B T S N
    intro b
    rw [hE.1 b, extendLocalizedDerivation_apply]

theorem localization_differential_equiv :
    Specs.AdvCommAlg.Differentials.Localization.differentialLocalization.{u,v,w} := by
  intro A B T _ _ _ _ _ _ _ S _
  refine ⟨(differential_isBaseChange A B T S).equiv, ?_⟩
  intro t b
  simp only [IsBaseChange.equiv_tmul, KaehlerDifferential.map_D]

theorem localized_differential_equiv :
    Specs.AdvCommAlg.Differentials.Localization.localizedDifferential.{u,v,w} := by
  intro A B T _ _ _ _ _ _ _ S _
  letI : Module T (LocalizedModule S (KaehlerDifferential A B)) :=
    LocalizedModule.moduleOfIsLocalization (S := S) (T := T)
  let h := IsLocalizedModule.isBaseChange S T
    (LocalizedModule.mkLinearMap S (KaehlerDifferential A B))
  refine ⟨h.equiv.symm.trans (differential_isBaseChange A B T S).equiv, ?_⟩
  intro b
  change (differential_isBaseChange A B T S).equiv
    (h.equiv.symm ((LocalizedModule.mkLinearMap S (KaehlerDifferential A B))
      (KaehlerDifferential.D A B b))) = _
  rw [IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul,
    one_smul, KaehlerDifferential.map_D]

theorem localization_base_equiv :
    Specs.AdvCommAlg.Differentials.Localization.baseLocalization.{u,v,w} := by
  intro A B A' _ _ _ _ _ U _ hU
  letI : Algebra A' B := (IsLocalization.lift (S := A') hU).toAlgebra
  letI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq hU a).symm)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B U) B :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨a, ha, rfl⟩
      exact hU ⟨a, ha⟩)
  let f := KaehlerDifferential.map A A' B B
  haveI : IsLocalizedModule U (LinearMap.id :
      KaehlerDifferential A B →ₗ[A] KaehlerDifferential A B) :=
    isLocalizedModule_id U _ A'
  let e := IsLocalizedModule.linearEquiv U
    (LinearMap.id : KaehlerDifferential A B →ₗ[A] KaehlerDifferential A B)
    (f.restrictScalars A)
  have he (x : KaehlerDifferential A B) : e x = f x :=
    IsLocalizedModule.linearEquiv_apply U _ _ x
  have hf : Function.Bijective f := by
    have : (e : KaehlerDifferential A B → KaehlerDifferential A' B) = f :=
      funext he
    rw [← this]
    exact e.bijective
  exact ⟨LinearEquiv.ofBijective f hf, fun _ => rfl⟩

end
end AdvCommAlg.Differentials
