import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.FiveTerm
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.Transgression
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits

universe u

namespace ALG02GroupTheory.FiveTerm

open IntegralBar BarProjectionKernel Transgression
open private kernelDOne bar_one_identity
  from MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.BarProjectionKernel
open private kernelClass_eq_classOf from MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.Transgression

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

private def normalizationEquiv (G : Type u) [Group G] (n : ℕ) (hn : n ≤ 2) :
    Multiplicative (homology G n) ≃* Multiplicative ((normalizedChains G).homology n) :=
  (normalizationHomologyIso G n hn).toLinearEquiv.toAddEquiv.toMultiplicative

private theorem normalization_square {G H : Type u} [Group G] [Group H]
    (f : G →* H) (n : ℕ) (hn : n ≤ 2) :
    (asMultiplicative (HomologicalComplex.homologyMap (normalizedChainsMap f) n)).comp
        (normalizationEquiv G n hn).toMonoidHom =
      (normalizationEquiv H n hn).toMonoidHom.comp (asMultiplicative (homologyMap f n)) :=
  congrArg (fun g => asMultiplicative g) (normalization_homology_natural f n)

private theorem inclusion_square (S : GroupExtension N E Q) :
    (asMultiplicative (HomologicalComplex.homologyMap (kernelInclusion S) 1)).comp
        (homologyEquiv S).symm.toMonoidHom =
      (normalizationEquiv E 1 (by decide)).toMonoidHom.comp (integralInclusion S) := by
  apply MonoidHom.ext
  intro x
  change Multiplicative.ofAdd (HomologicalComplex.homologyMap (kernelInclusion S) 1
      ((homologyEquiv S).symm x).toAdd) =
    Multiplicative.ofAdd ((normalizationHomologyIso E 1 (by decide)).hom
      ((normalizationHomologyIso E 1 (by decide)).inv
        (HomologicalComplex.homologyMap (kernelInclusion S) 1
          ((homologyEquiv S).symm x).toAdd)))
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

private theorem transgression_square (S : GroupExtension N E Q) :
    (asMultiplicative (connecting S (projection_shortExact S))).comp
        (normalizationEquiv Q 2 (by decide)).toMonoidHom =
      (homologyEquiv S).symm.toMonoidHom.comp (integralTransgression S) := by
  apply MonoidHom.ext
  intro x
  change Multiplicative.ofAdd (connecting S (projection_shortExact S)
      (HomologicalComplex.homologyMap (normalization Q) 2 x.toAdd)) =
    (homologyEquiv S).symm (homologyEquiv S _)
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem mulExact_of_exact {K : ShortComplex (ModuleCat.{u} Integers.{u})}
    (hK : K.Exact) : Function.MulExact (asMultiplicative K.f) (asMultiplicative K.g) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact K).mp hK

private theorem projection_h1_surjective (S : GroupExtension N E Q) :
    Function.Surjective (homologyMap S.rightHom 1) := by
  let hS := projection_shortExact S
  have hzero : IsZero ((kernelChains S).homology 0) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (kernel_zero S)
  have he := hS.homology_exact₃ 1 0 rfl
  have hδ : hS.δ 1 0 rfl = 0 := hzero.eq_of_tgt _ _
  have hp : Epi (HomologicalComplex.homologyMap (normalizedChainsMap S.rightHom) 1) :=
    he.epi_f hδ
  have hE : IsIso (HomologicalComplex.homologyMap (normalization E) 1) :=
    normalization_homology_isIso 1 (by decide)
  have hQ : IsIso (HomologicalComplex.homologyMap (normalization Q) 1) :=
    normalization_homology_isIso 1 (by decide)
  apply (ModuleCat.epi_iff_surjective _).mp
  apply (epi_comp_iff_of_isIso _ (HomologicalComplex.homologyMap (normalization Q) 1)).mp
  exact normalization_homology_natural S.rightHom 1 ▸
    epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ hE) hp

/-- Exactness of the five-term sequence with the canonical transgression and inclusion. -/
theorem exact_sequence (S : GroupExtension N E Q) :
    Spec.SequenceExact S (integralTransgression S) (integralInclusion S) := by
  let hS := projection_shortExact S
  let eE₁ := normalizationEquiv E 1 (by decide)
  let eQ₁ := normalizationEquiv Q 1 (by decide)
  let eE₂ := normalizationEquiv E 2 (by decide)
  let eQ₂ := normalizationEquiv Q 2 (by decide)
  let eK := (homologyEquiv S).symm
  refine ⟨?_, ?_, ?_, projection_h1_surjective S⟩
  · exact (Function.MulExact.iff_of_ladder_mulEquiv eE₂ eQ₂ eK
      (normalization_square S.rightHom 2 (by decide)) (transgression_square S)).mp
        (mulExact_of_exact (hS.homology_exact₃ 2 1 rfl))
  · exact (Function.MulExact.iff_of_ladder_mulEquiv eQ₂ eK eE₁
      (transgression_square S) (inclusion_square S)).mp
        (mulExact_of_exact (hS.homology_exact₁ 2 1 rfl))
  · exact (Function.MulExact.iff_of_ladder_mulEquiv eK eE₁ eQ₁
      (inclusion_square S) (normalization_square S.rightHom 1 (by decide))).mp
        (mulExact_of_exact (hS.homology_exact₂ 1))

/-- The connecting homomorphism in the five-term sequence is the signed
second differential of the filtered bar complex. -/
theorem signed_transgression (S : GroupExtension N E Q) :
    Spec.IsSignedTransgression S (integralTransgression S) := by
  obtain ⟨s, t, hs, ht, hd⟩ :=
    integral_filtered_comparison S (projection_shortExact S) (homologyEquiv S)
  refine ⟨s, t, hs, ?_, hd⟩
  intro n x hx
  let y := translateDifference S n 1
  have hy : y.val = x.val := by
    change normalizedBar 1 ![S.inl n * 1] - normalizedBar 1 ![(1 : E)] = x.val
    rw [hx, mul_one, bar_one_identity, sub_zero]
  have cy : (kernelChains S).d 1 0 y = 0 := by rw [kernelDOne]; rfl
  rw [ht x y hy cy, ← kernelClass_eq_classOf S y cy]
  exact homologyEquiv_translate S n 1

private theorem homology_comm {G H G' H' : Type u}
    [Group G] [Group H] [Group G'] [Group H']
    {p : G →* H} {p' : G' →* H'} {a : G →* G'} {b : H →* H'}
    (h : p'.comp a = b.comp p) (n : ℕ) (x : homology G n) :
    homologyMap p' n (homologyMap a n x) = homologyMap b n (homologyMap p n x) := by
  have hs : homologyMap a n ≫ homologyMap p' n = homologyMap p n ≫ homologyMap b n := by
    rw [← homologyMap_comp, ← homologyMap_comp, h]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x

/-- A morphism of extensions induces a commuting diagram of five-term sequences. -/
theorem sequence_natural {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) :
    Spec.SequenceNatural f (integralTransgression S) (integralInclusion S)
      (integralTransgression T) (integralInclusion T) := by
  refine ⟨homology_comm f.right_comm 2, integralTransgression_natural f, ?_,
    homology_comm f.right_comm 1⟩
  intro z
  induction z using QuotientGroup.induction_on with
  | _ n =>
    change integralInclusion T (QuotientGroup.mk (f.kernel n)) =
      asMultiplicative (homologyMap f.middle 1) (integralInclusion S (QuotientGroup.mk n))
    rw [integralInclusion_mk, integralInclusion_mk]
    have h := homology_comm f.inl_comm.symm 1 (generatorClass n)
    rw [homologyMap_generatorClass] at h
    exact congrArg Multiplicative.ofAdd h

/-- The natural homological five-term sequence for an extension of discrete groups. -/
theorem five_term : Spec.NaturalFiveTerm.{u} :=
  ⟨fun S => integralTransgression S, fun S => integralInclusion S,
    fun S => ⟨exact_sequence S, integralInclusion_mk S, signed_transgression S⟩,
    fun f => sequence_natural f⟩

end

end ALG02GroupTheory.FiveTerm
