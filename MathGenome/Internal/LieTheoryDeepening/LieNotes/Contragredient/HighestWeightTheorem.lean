import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.HighestWeightTheorem
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.IntegrableHighestWeight
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.SimpleHighestWeight
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.ReflectionAutomorphisms
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.IntegrableHighestWeight
namespace LieNotes.Contragredient.HighestWeightTheorem

open CartanQuotient LocallyNilpotentExponential ReflectionAutomorphisms
open Specs.LieNotes.Contragredient.IntegrableHighestWeight (IntegrabilityCriterion RankOneIdentity)
open Specs.LieNotes.Contragredient.VermaModules (IsWeightCharacter)
open UniversalEnvelopingAlgebra (ι)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)

universe u v w

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_intertwines {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    {V : Type w} [AddCommGroup V] [Module ℂ V] (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ V) (x : G)
    (had : LocallyNilpotent (LieAlgebra.ad ℂ G x)) (hρ : LocallyNilpotent (ρ x))
    (y : G) (z : V) :
    expEquiv (ρ x) hρ (ρ y z) = ρ (exp (LieAlgebra.ad ℂ G x) had y) (expEquiv (ρ x) hρ z) := by
  let T := expEquiv (ρ x) hρ
  have h := LinearMap.congr_fun (exp_conjugation ρ x had hρ y) (T z)
  change T (ρ y (T.symm (T z))) = ρ (exp (LieAlgebra.ad ℂ G x) had y) (T z) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

open private neg_f_ad_locally_nilpotent weightReflection_apply_cartan
  from MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.ReflectionAutomorphisms

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

set_option maxHeartbeats 600000 in
/-- The product of the simple exponentials carries the entire weight space onto its reflection. -/
private theorem reflected_weightSpace (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (Λ : Module.Dual ℂ H)
    (hχ : ∃! χ, IsWeightCharacter R Λ χ)
    (i : I)
    (he : ∀ z : SimpleHighestWeight.L R Λ hχ, ∃ n : ℕ,
      (ι ℂ (e R i) : U (Algebra R)) ^ n • z = 0)
    (hf : ∀ z : SimpleHighestWeight.L R Λ hχ, ∃ n : ℕ,
      (ι ℂ (f R i) : U (Algebra R)) ^ n • z = 0)
    (μ : Module.Dual ℂ H) :
    ∃ T : SimpleHighestWeight.L R Λ hχ ≃ₗ[ℂ] SimpleHighestWeight.L R Λ hχ,
      (SimpleHighestWeight.weightSpaceAt R Λ hχ μ).map T.toLinearMap =
        SimpleHighestWeight.weightSpaceAt R Λ hχ (R.weightReflection i μ) := by
  let V := SimpleHighestWeight.L R Λ hχ
  let a : U (Algebra R) →ₐ[ℂ] Module.End ℂ V := Algebra.lsmul ℂ ℂ V
  let ρ : Algebra R →ₗ⁅ℂ⁆ Module.End ℂ V := a.toLieHom.comp (ι ℂ)
  have action_nilpotent (x : Algebra R)
      (hx : ∀ z : V, ∃ n : ℕ, (ι ℂ x : U (Algebra R)) ^ n • z = 0) :
      LocallyNilpotent (ρ x) := by
    intro z
    obtain ⟨n, hn⟩ := hx z
    refine ⟨n, ?_⟩
    change (a (ι ℂ x) ^ n) z = 0
    rw [← map_pow]
    exact hn
  have local_e := action_nilpotent (e R i) he
  have local_f := action_nilpotent (f R i) hf
  have local_neg_f : LocallyNilpotent (ρ (-f R i)) := by
    rw [map_neg]
    exact local_f.neg
  have ad_e : LocallyNilpotent (LieAlgebra.ad ℂ (Algebra R) (e R i)) :=
    AdjointNilpotence.ad_e_locally_nilpotent hA R i
  have ad_neg_f := neg_f_ad_locally_nilpotent hA R i
  let E := expEquiv (ρ (e R i)) local_e
  let F := expEquiv (ρ (-f R i)) local_neg_f
  let T := (E.trans F).trans E
  let r := reflectionAutomorphism hA R i
  have intertwines (x : Algebra R) (z : V) : T (ρ x z) = ρ (r x) (T z) := by
    let adE := exp (LieAlgebra.ad ℂ (Algebra R) (e R i)) ad_e
    let adF := exp (LieAlgebra.ad ℂ (Algebra R) (-f R i)) ad_neg_f
    have hr (y : Algebra R) : r y = adE (adF (adE y)) := by
      change adjointExp (e R i) ad_e
        (adjointExp (-f R i) ad_neg_f (adjointExp (e R i) ad_e y)) = _
      rw [adjointExp_apply (e R i) ad_e y, adjointExp_apply (-f R i) ad_neg_f,
        adjointExp_apply (e R i) ad_e]
    change E (F (E (ρ x z))) = ρ (r x) (E (F (E z)))
    have hE (y : Algebra R) (v : V) : E (ρ y v) = ρ (adE y) (E v) :=
      exp_intertwines ρ (e R i) ad_e local_e y v
    have hF (y : Algebra R) (v : V) : F (ρ y v) = ρ (adF y) (F v) :=
      exp_intertwines ρ (-f R i) ad_neg_f local_neg_f y v
    calc
      E (F (E (ρ x z))) = E (F (ρ (adE x) (E z))) := congrArg (E ∘ F) (hE x z)
      _ = E (ρ (adF (adE x)) (F (E z))) := congrArg E (hF (adE x) (E z))
      _ = ρ (adE (adF (adE x))) (E (F (E z))) := hE (adF (adE x)) (F (E z))
      _ = ρ (r x) (E (F (E z))) := congrArg (fun y ↦ ρ y (E (F (E z)))) (hr x).symm
  let τ := cartanReflection R i
  have hCartan (h : H) (z : V) : T (ρ (cartan R h) z) = ρ (cartan R (τ h)) (T z) :=
    (intertwines (cartan R h) z).trans (by
      rw [reflectionAutomorphism_onCartan hA R i (reflectionAutomorphism_spec hA R i)])
  have hweight (γ : Module.Dual ℂ H) (h : H) : R.weightReflection i γ h = γ (τ h) :=
    weightReflection_apply_cartan R i γ h
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    intro h
    change ρ (cartan R h) (T z) = R.weightReflection i μ h • T z
    have hz' : ρ (cartan R (τ h)) z = μ (τ h) • z := hz (τ h)
    have hT := hCartan (τ h) z
    rw [cartanReflection_involutive hA R i h] at hT
    rw [← hT, hz', map_smul, hweight]
  · intro z hz
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    intro h
    change ρ (cartan R h) (T.symm z) = μ h • T.symm z
    have hz' : ρ (cartan R (τ h)) z = R.weightReflection i μ (τ h) • z := hz (τ h)
    have hμ := hweight μ (τ h)
    rw [cartanReflection_involutive hA R i h] at hμ
    apply T.injective
    rw [hCartan, map_smul, T.apply_symm_apply, hz', hμ]

theorem highestWeightTheorem_conditional
    (integrabilityCriterion : IntegrabilityCriterion.{u, v})
    (_rankOneIdentity : RankOneIdentity.{u, v, w}) :
    Specs.LieNotes.Contragredient.HighestWeightTheorem.HighestWeightResult.{u, v, w} := by
  intro I A H _ _ _ hA R Λ
  have hχ := VermaModules.weightCharacterExists R Λ
  have hInt := integrabilityCriterion hA R Λ hχ
  refine ⟨hχ, VermaModules.finiteWeightSpaces R Λ hχ,
    VermaModules.finrank_topWeightSpace R Λ hχ, SimpleHighestWeight.simpleModule R Λ hχ,
    SimpleHighestWeight.uniqueSimpleQuotient.{u, v, w} R Λ hχ, hInt, ?_, ?_⟩
  · intro μ
    rw [SimpleHighestWeight.weightSpaceImage R Λ hχ μ]
    have := VermaModules.finiteWeightSpaces R Λ hχ μ
    infer_instance
  · intro hDominant i μ
    obtain ⟨he, hf⟩ := hInt.mpr hDominant
    obtain ⟨T, hT⟩ := reflected_weightSpace hA R Λ hχ i (he i) (hf i) μ
    change Module.finrank ℂ (SimpleHighestWeight.weightSpaceAt R Λ hχ μ) =
      Module.finrank ℂ (SimpleHighestWeight.weightSpaceAt R Λ hχ (R.weightReflection i μ))
    rw [← hT, LinearEquiv.finrank_map_eq]

end
end LieNotes.Contragredient.HighestWeightTheorem

universe v8_closure_ec821745ebd36a34_u0 v8_closure_ec821745ebd36a34_u1 v8_closure_ec821745ebd36a34_u2
theorem _root_.«LieNotes».«Contragredient».«HighestWeightTheorem».«highestWeightTheorem» : _root_.«Specs».«LieNotes».«Contragredient».«HighestWeightTheorem».«HighestWeightResult».{v8_closure_ec821745ebd36a34_u0, v8_closure_ec821745ebd36a34_u1, v8_closure_ec821745ebd36a34_u2} :=
  @_root_.«LieNotes».«Contragredient».«HighestWeightTheorem».«highestWeightTheorem_conditional».{v8_closure_ec821745ebd36a34_u0, v8_closure_ec821745ebd36a34_u1, v8_closure_ec821745ebd36a34_u2} (@_root_.«LieNotes».«Contragredient».«IntegrableHighestWeight».«integrabilityCriterion».{v8_closure_ec821745ebd36a34_u0, v8_closure_ec821745ebd36a34_u1}) (@_root_.«LieNotes».«Contragredient».«IntegrableHighestWeight».«rankOneIdentity».{v8_closure_ec821745ebd36a34_u0, v8_closure_ec821745ebd36a34_u1, v8_closure_ec821745ebd36a34_u2})
