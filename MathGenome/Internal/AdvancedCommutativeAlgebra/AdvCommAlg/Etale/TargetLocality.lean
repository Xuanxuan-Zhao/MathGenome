import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.DifferentialCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.TargetLocality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.TargetLocality
import Mathlib.RingTheory.Ideal.Operations

/-! Target locality of étaleness, ET-04.
Smoothness (and hence finite presentation) descends by SM-07. KD-16
identifies each localized differential module with that of the localized
algebra. For each differential, a power of each cover element annihilates
it, so the unit-ideal condition forces it to vanish. ET-02 concludes.
-/
namespace AdvCommAlg.Etale

universe u v

theorem etale_of_finite_principal_cover :
    Specs.AdvCommAlg.Etale.etaleTargetLocality.{u,v} := by
  intro A B _ _ _ n b hspan h
  have hlocal := fun i =>
    (etale_iff_smooth_and_subsingleton_omega A (Localization.Away (b i))).mp (h i)
  apply (etale_iff_smooth_and_subsingleton_omega A B).mpr
  refine ⟨Smooth.smooth_of_finite_principal_cover A B n b hspan
    (fun i => (hlocal i).1), ?_⟩
  suffices hz : ∀ x : KaehlerDifferential A B, x = 0 from
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro x
  apply (Submodule.mem_bot B).mp
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (⊥ : Submodule B (KaehlerDifferential A B)) (Set.range b) hspan x
  rintro ⟨_, i, rfl⟩
  let S := Submonoid.powers (b i)
  let T := Localization.Away (b i)
  let : Subsingleton (KaehlerDifferential A T) := (hlocal i).2
  obtain ⟨e, _⟩ := Differentials.localized_differential_equiv A B T S
  have hzloc : LocalizedModule.mkLinearMap S (KaehlerDifferential A B) x = 0 := by
    apply e.injective
    exact Subsingleton.elim _ _
  obtain ⟨⟨s, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff S
    (LocalizedModule.mkLinearMap S (KaehlerDifferential A B))).mp hzloc
  exact ⟨k, by simpa only [Submonoid.smul_def, Submodule.mem_bot] using hk⟩

end AdvCommAlg.Etale
