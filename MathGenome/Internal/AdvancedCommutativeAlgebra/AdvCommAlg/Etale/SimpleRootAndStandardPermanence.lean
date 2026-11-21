import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.SimpleRootAndStandardPermanence

namespace AdvCommAlg.Etale

universe u v w
noncomputable section
open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.SimpleRoot
open scoped TensorProduct

variable {A : Type u} {D : Type v} [CommRing A] [CommRing D] [Algebra A D]

lemma aeval_rootImage (f g p : A[X]) :
    aeval (rootImage f g) p =
      algebraMap (AdjoinRoot f) (LocalizedQuotient f g) (AdjoinRoot.mk f p) := by
  rw [rootImage, aeval_algebraMap_apply, AdjoinRoot.aeval_eq]

lemma localized_root_is_root (f g : A[X]) : aeval (rootImage f g) f = 0 := by
  rw [aeval_rootImage, AdjoinRoot.mk_self, map_zero]

lemma localized_g_isUnit (f g : A[X]) : IsUnit (aeval (rootImage f g) g) := by
  rw [aeval_rootImage]
  exact IsLocalization.Away.algebraMap_isUnit ..

/-- Maps from the localization are determined by the distinguished root. -/
lemma localized_root_hom_ext {f g : A[X]}
    {φ ψ : LocalizedQuotient f g →ₐ[A] D}
    (h : φ (rootImage f g) = ψ (rootImage f g)) : φ = ψ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (AdjoinRoot.mk f g))
  exact AdjoinRoot.algHom_ext h

/-- The universal map obtained from a root at which the denominator is a unit. -/
def localized_root_lift (f g : A[X]) (x : D)
    (hf : aeval x f = 0) (hg : IsUnit (aeval x g)) :
    LocalizedQuotient f g →ₐ[A] D :=
  IsLocalization.Away.liftAlgHom (AdjoinRoot.mk f g)
    (f := AdjoinRoot.liftAlgHom f (Algebra.ofId A D) x hf) hg

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma localized_root_lift_root (f g : A[X]) (x : D)
    (hf : aeval x f = 0) (hg : IsUnit (aeval x g)) :
    localized_root_lift f g x hf hg (rootImage f g) = x := by
  change IsLocalization.Away.lift (AdjoinRoot.mk f g)
    (g := (AdjoinRoot.liftAlgHom f (Algebra.ofId A D) x hf).toRingHom) hg
    (algebraMap (AdjoinRoot f) (LocalizedQuotient f g) (AdjoinRoot.root f)) = x
  rw [IsLocalization.Away.lift_eq]
  exact AdjoinRoot.liftAlgHom_root ..

/-- Newton correction in a square-zero ideal; neither polynomial is monic. -/
lemma square_zero_root_correction (f g : A[X]) (J : Ideal D) (hJ : J ^ 2 = ⊥)
    (x : D) (hf : aeval (Ideal.Quotient.mk J x) f = 0)
    (hg : IsUnit (aeval (Ideal.Quotient.mk J x) g))
    (hd : IsUnit (aeval (Ideal.Quotient.mk J x) f.derivative)) :
    ∃ v : Dˣ, (v : D) = aeval x f.derivative ∧
      let y := x - aeval x f * (↑(v⁻¹) : D)
      Ideal.Quotient.mk J y = Ideal.Quotient.mk J x ∧
      aeval y f = 0 ∧ IsUnit (aeval y g) ∧
      ∀ z : D, Ideal.Quotient.mk J z = Ideal.Quotient.mk J x → aeval z f = 0 → z = y := by
  have hnil : IsNilpotent J := ⟨2, hJ⟩
  have hfJ : aeval x f ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [← Ideal.Quotient.mkₐ_eq_mk A, aeval_algHom_apply] using hf
  have hd' : IsUnit (aeval x f.derivative) := by
    rw [← hnil.isUnit_quotient_mk_iff]
    simpa only [← Ideal.Quotient.mkₐ_eq_mk A, aeval_algHom_apply] using hd
  obtain ⟨v, hv⟩ := hd'
  refine ⟨v, hv, ?_⟩
  let ε : D := -(aeval x f * (↑(v⁻¹) : D))
  have hεJ : ε ∈ J := J.neg_mem (J.mul_mem_right _ hfJ)
  have hεsq : ε ^ 2 = 0 := hJ.le (Ideal.pow_mem_pow hεJ 2)
  have hred : Ideal.Quotient.mk J (x + ε) = Ideal.Quotient.mk J x := by
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hεJ, add_zero]
  have hroot : aeval (x + ε) f = 0 := by
    rw [aeval_add_of_sq_eq_zero _ _ _ hεsq, ← hv]
    dsimp [ε]
    simp [mul_left_comm (v : D)]
  have hg' : IsUnit (aeval (x + ε) g) := by
    rw [← hnil.isUnit_quotient_mk_iff]
    rw [← Ideal.Quotient.mkₐ_eq_mk A, ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, hred]
    exact hg
  simp only [sub_eq_add_neg]
  change Ideal.Quotient.mk J (x + ε) = _ ∧ aeval (x + ε) f = 0 ∧
    IsUnit (aeval (x + ε) g) ∧ _
  refine ⟨hred, hroot, hg', ?_⟩
  intro z hz hzf
  have hzJ : z - x ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J) z x).mp hz
  have hzsq : (z - x) ^ 2 = 0 := hJ.le (Ideal.pow_mem_pow hzJ 2)
  have heq : aeval x f + (v : D) * (z - x) = 0 := by
    rw [hv, ← aeval_add_of_sq_eq_zero _ _ _ hzsq, add_sub_cancel, hzf]
  have hzε : z - x = ε := by
    apply (Units.mul_left_inj v).mp
    dsimp [ε]
    calc
      (z - x) * (v : D) = -aeval x f := by linear_combination heq
      _ = -(aeval x f * (↑(v⁻¹) : D)) * (v : D) := by simp [mul_assoc]
  linear_combination hzε


theorem simple_root_correction : simpleRootCorrection.{u,v} := by
  intro A D _ _ _ f g hd J hJ φ x hx
  have hf : aeval (Ideal.Quotient.mk J x) f = 0 := by
    rw [hx, aeval_algHom_apply, localized_root_is_root, map_zero]
  have hg : IsUnit (aeval (Ideal.Quotient.mk J x) g) := by
    rw [hx, aeval_algHom_apply]
    exact (localized_g_isUnit f g).map φ
  have hd' : IsUnit (aeval (Ideal.Quotient.mk J x) f.derivative) := by
    rw [hx, aeval_algHom_apply, aeval_rootImage]
    exact hd.map φ
  obtain ⟨v, hv, h⟩ := square_zero_root_correction f g J hJ x hf hg hd'
  exact ⟨v, hv, by simpa only [hx] using h⟩

theorem simple_root_lifting : simpleRootLifting.{u,v} := by
  intro A D _ _ _ f g hd J hJ φ
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ (rootImage f g))
  obtain ⟨v, hv, h⟩ := simple_root_correction f g hd J hJ φ x hx
  dsimp only at h
  let y := x - aeval x f * (↑(v⁻¹) : D)
  let ψ := localized_root_lift f g y h.2.1 h.2.2.1
  have hψ : (Ideal.Quotient.mkₐ A J).comp ψ = φ := by
    apply localized_root_hom_ext
    simpa only [AlgHom.comp_apply, ψ, localized_root_lift_root,
      Ideal.Quotient.mkₐ_eq_mk] using h.1
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  apply localized_root_hom_ext
  change χ (rootImage f g) = localized_root_lift f g y h.2.1 h.2.2.1 (rootImage f g)
  rw [localized_root_lift_root]
  apply h.2.2.2
  · exact congrArg (fun ξ => ξ (rootImage f g)) hχ
  · rw [aeval_algHom_apply, localized_root_is_root, map_zero]

/-- Finite presentation together with the explicit unique lifting property. -/
theorem simple_root_etale : simpleRootEtale.{u} := by
  intro A _ f g hd
  have : Algebra.FormallyEtale A (LocalizedQuotient f g) := by
    apply Algebra.FormallyEtale.iff_comp_bijective.mpr
    intro D _ _ J hJ
    exact (Function.bijective_iff_existsUnique _).mpr (simple_root_lifting f g hd J hJ)
  exact ⟨this, inferInstance⟩

theorem localization_inverse_forced : localizationInverseForced.{u,v} := by
  intro A D _ _ _ f g ψ z
  have h : aeval (ψ (rootImage f g)) g *
      ψ (IsLocalization.Away.invSelf (AdjoinRoot.mk f g)) = 1 := by
    rw [aeval_algHom_apply, aeval_rootImage, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  constructor
  · intro hz
    have hu : IsUnit (aeval (ψ (rootImage f g)) g) := by
      rw [aeval_algHom_apply]
      exact (localized_g_isUnit f g).map ψ
    exact hu.mul_right_inj.mp (hz.trans h.symm)
  · rintro rfl
    exact h

theorem standard_etale_etale : standardEtaleEtale.{u,v} := by
  intro A B _ _ _ h
  let : Algebra.IsStandardEtale A B := (standardEtale_iff A B).mp h
  exact inferInstanceAs (Algebra.Etale A B)

theorem standard_localization : standardLocalization.{u,v} := by
  intro A B _ _ _ h b
  let : Algebra.IsStandardEtale A B := (standardEtale_iff A B).mp h
  apply (standardEtale_iff A (Localization.Away b)).mpr
  exact Algebra.IsStandardEtale.of_isLocalizationAway b

theorem standard_base_change : standardBaseChange.{u,v,w} := by
  intro A B A' _ _ _ _ _ h
  let : Algebra.IsStandardEtale A B := (standardEtale_iff A B).mp h
  exact (standardEtale_iff A' (A' ⊗[A] B)).mpr inferInstance

end
end AdvCommAlg.Etale
