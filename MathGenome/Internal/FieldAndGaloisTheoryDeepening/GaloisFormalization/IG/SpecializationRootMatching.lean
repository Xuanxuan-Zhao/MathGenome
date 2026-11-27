import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationRootMatching
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationCoefficients
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SimpleRootLifting

open scoped Polynomial

namespace GaloisFormalization.IG.SpecializationRootMatching

open SpecializationData SpecializationCoefficients
open Specs.GaloisFormalization.IG.SpecializationRootMatching

noncomputable section

abbrev liftedRootImages :=
  @Specs.GaloisFormalization.IG.SpecializationRootMatching.liftedRootImages

theorem liftSpecializedRoot : LiftSpecializedRoot := by
  intro k _ ℓ _ _ a f hf hsep r hr
  have hroot := Polynomial.aeval_eq_zero_of_mem_rootSet hr
  have hder := hsep.aeval_derivative_ne_zero hroot
  have hlift := GaloisFormalization.IG.simpleRootLifting ℓ ℓ (polynomialLift ℓ a f hf) r
  have hmap : PowerSeries.map (RingHom.id ℓ) = RingHom.id (PowerSeries ℓ) :=
    RingHom.ext fun F => congrFun PowerSeries.map_id F
  simp only [Algebra.algebraMap_self, hmap, Polynomial.map_id, polynomialLift_reduction] at hlift
  apply hlift
  · rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot
  · rw [Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map]
    exact hder

private theorem coeff_zero_powerToLaurent {ℓ : Type*} [Field ℓ] (F : PowerSeries ℓ) :
    (powerToLaurent ℓ F).coeff 0 = PowerSeries.constantCoeff F := by
  change (F : LaurentSeries ℓ).coeff 0 = _
  simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    LaurentSeries.coeff_coe_powerSeries F 0

private theorem bijOn_liftedRootImages {k ℓ : Type*} [Field k] [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    (hsep : (specialize a f hf).Separable) :
    Set.BijOn (fun x : LaurentSeries ℓ => x.coeff 0) (liftedRootImages ℓ a f hf)
      ((specialize a f hf).rootSet ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, F, hF, _, rfl⟩
    simpa only [coeff_zero_powerToLaurent, hF] using hr
  · rintro _ ⟨r, hr, F, hF, hFroot, rfl⟩ _ ⟨s, _, G, hG, hGroot, rfl⟩ heq
    simp only [coeff_zero_powerToLaurent, hF, hG] at heq
    obtain ⟨H, _, huniq⟩ := liftSpecializedRoot ℓ a f hf hsep r hr
    rw [huniq F ⟨hF, hFroot⟩, huniq G ⟨hG.trans heq.symm, hGroot⟩]
  · intro r hr
    obtain ⟨F, ⟨hF, hFroot⟩, _⟩ := liftSpecializedRoot ℓ a f hf hsep r hr
    exact ⟨powerToLaurent ℓ F, ⟨r, hr, F, hF, hFroot, rfl⟩,
      (coeff_zero_powerToLaurent F).trans hF⟩

theorem laurentSpecializationRoots : LaurentSpecializationRoots := by
  classical
  intro k _ ℓ _ _ a f hf _ hmonic hsep
  let pointAlgebra := substitutionAlgebra ℓ a
  have hlift : liftedRootImages ℓ a f hf ⊆ f.rootSet (LaurentSeries ℓ) := by
    rintro _ ⟨_, _, F, _, hFroot, rfl⟩
    apply hmonic.mem_rootSet.mpr
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change (f.map (substitution ℓ a).toRingHom).eval (powerToLaurent ℓ F) = 0
    rw [← polynomialLift_laurent ℓ a f hf, Polynomial.eval_map_apply, hFroot, map_zero]
  have hcard : (liftedRootImages ℓ a f hf).ncard = f.natDegree := by
    rw [(bijOn_liftedRootImages a f hf hsep).ncard_eq, ← Set.fintypeCard_eq_ncard,
      Polynomial.card_rootSet_eq_natDegree hsep
        (Polynomial.IsSplittingField.splits ℓ (specialize a f hf))]
    exact (specialize_monicDegree a f hf hmonic).2
  have hroots : liftedRootImages ℓ a f hf = f.rootSet (LaurentSeries ℓ) :=
    Set.eq_of_subset_of_ncard_le hlift (hcard ▸ f.ncard_rootSet_le _)
      (f.rootSet_finite _)
  have hcardRootSet : (f.rootSet (LaurentSeries ℓ)).ncard = f.natDegree :=
    hroots ▸ hcard
  let p := f.map (algebraMap (RatFunc k) (LaurentSeries ℓ))
  have hcardMultiset : f.natDegree ≤ p.roots.card := by
    rw [← hcardRootSet, Polynomial.rootSet_def, Set.ncard_coe_finset]
    exact Multiset.toFinset_card_le _
  have hdegree : p.natDegree = f.natDegree :=
    Polynomial.natDegree_map (algebraMap (RatFunc k) (LaurentSeries ℓ))
  have hsplits : p.Splits := Polynomial.splits_iff_card_roots.mpr
    ((Polynomial.card_roots' p).antisymm (hdegree.le.trans hcardMultiset))
  have hseparable :=
    (Polynomial.card_rootSet_eq_natDegree_iff_of_splits hmonic.ne_zero hsplits).mp
      ((Set.fintypeCard_eq_ncard _).trans hcardRootSet)
  exact ⟨hseparable, hsplits, hroots.symm⟩

theorem pointEmbeddingRoots : PointEmbeddingRoots := by
  intro k _ ℓ _ _ a f hf _ L _ _ _ hmonic hsep
  let pointAlgebra := substitutionAlgebra ℓ a
  intro i
  obtain ⟨_, _, hroots⟩ := laurentSpecializationRoots ℓ a f hf hmonic hsep
  have himage : i '' f.rootSet L = liftedRootImages ℓ a f hf :=
    ((Polynomial.IsSplittingField.splits L f).image_rootSet i).trans hroots
  have hbijection : Set.BijOn i (f.rootSet L) (liftedRootImages ℓ a f hf) :=
    himage ▸ i.injective.bijOn_image
  refine ⟨⟨?_, (bijOn_liftedRootImages a f hf hsep).comp hbijection⟩, himage, ?_⟩
  · intro x hx
    obtain ⟨_, _, F, _, _, hF⟩ := hbijection.mapsTo hx
    exact ⟨F, hF⟩
  · apply le_antisymm
    · apply IntermediateField.toSubalgebra_le_toSubalgebra.mp
      change i.range ≤ _
      rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range L f i, hroots]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _
    · apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      have hx' : x ∈ i '' f.rootSet L := by
        rw [himage]
        exact hx
      exact AlgHom.mem_fieldRange.mpr (Set.image_subset_range _ _ hx')

theorem existsRootMatchingEmbedding : ExistsRootMatchingEmbedding := by
  intro k _ ℓ _ _ a f hf _ L _ _ _ hmonic hsep
  let pointAlgebra := substitutionAlgebra ℓ a
  have hsplits := (laurentSpecializationRoots ℓ a f hf hmonic hsep).2.1
  let i : PointEmbedding (ℓ := ℓ) a L := Polynomial.IsSplittingField.lift L f hsplits
  exact ⟨i, (pointEmbeddingRoots ℓ a f hf L hmonic hsep i).1⟩

end

end GaloisFormalization.IG.SpecializationRootMatching
