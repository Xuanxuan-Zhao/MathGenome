import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.TowerSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationDecomposition
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SimpleRootLifting
import Mathlib.RingTheory.Valuation.Integral
import Batteries.Tactic.OpenPrivate

open scoped Polynomial

namespace GaloisFormalization.IG.TowerSpecialization

open Polynomial SpecializationData SpecializationCoefficients SpecializationDecomposition
open Specs.GaloisFormalization.IG.TowerSpecialization

open private laurentMap_powerToLaurent from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationCoefficients

noncomputable section

variable {k : Type*} [Field k] {ℓ : Type*} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type*} [Field L] [Algebra (RatFunc k) L]

private theorem coeff_zero_powerToLaurent (F : PowerSeries ℓ) :
    (powerToLaurent ℓ F).coeff 0 = PowerSeries.constantCoeff F := by
  change (F : LaurentSeries ℓ).coeff 0 = _
  simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    LaurentSeries.coeff_coe_powerSeries F 0

private theorem integers_powerToLaurent :
    Valuation.Integers (Valued.v : Valuation (LaurentSeries ℓ) (WithZero (Multiplicative ℤ))) (PowerSeries ℓ) where
  hom_inj := HahnSeries.ofPowerSeries_injective
  map_le_one F := (LaurentSeries.val_le_one_iff_eq_coe ℓ _).2 ⟨F, rfl⟩
  exists_of_le_one {x} hx := (LaurentSeries.val_le_one_iff_eq_coe ℓ x).1 hx

private theorem powerSeries_splits {g : (PowerSeries ℓ)[X]} (hm : g.Monic)
    (hs : (g.map (powerToLaurent ℓ)).Splits) : g.Splits := by
  apply hs.of_splits_map_of_injective HahnSeries.ofPowerSeries_injective
  intro x hx
  have he : aeval x g = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact (mem_roots (hm.map (powerToLaurent ℓ)).ne_zero).1 hx
  exact integers_powerToLaurent.exists_of_le_one
    (integers_powerToLaurent.isIntegral_iff_v_le_one.1 ⟨g, hm, he⟩)

private theorem splits_and_matches (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    (hm : f.Monic) (hs : (specialize a f hf).Separable)
    [IsSplittingField (RatFunc k) L f] (i : PointEmbedding (ℓ := ℓ) a L) :
    ((specialize a f hf).map (algebraMap k ℓ)).Splits ∧ MatchesRoots i f hf := by
  classical
  let := substitutionAlgebra ℓ a
  let g := polynomialLift ℓ a f hf
  let g₀ := specialize a f hf
  let incl := powerToLaurent ℓ
  let red : PowerSeries ℓ →+* ℓ := PowerSeries.constantCoeff
  have hgm : g.Monic := (polynomialLift_monicDegree ℓ a f hf hm).1
  have hla : g.map incl = f.map (algebraMap (RatFunc k) (LaurentSeries ℓ)) :=
    polynomialLift_laurent ℓ a f hf
  have hred : g.map red = g₀.map (algebraMap k ℓ) := polynomialLift_reduction ℓ a f hf
  -- Monicity puts every Laurent root in the power-series ring.
  have hsp : g.Splits := powerSeries_splits hgm (by
    rw [hla, ← i.comp_algebraMap, ← map_map]
    exact (IsSplittingField.splits L f).map i.toRingHom)
  -- Reducing the split factorization records all roots, with their multiplicities.
  have hroots : (g₀.map (algebraMap k ℓ)).roots = g.roots.map red :=
    hred ▸ hsp.roots_map_of_ne_zero (hgm.map red).ne_zero
  have hnd : (g.roots.map red).Nodup := by
    rw [← hroots]
    exact nodup_roots (hs.map (f := algebraMap k ℓ))
  have hincl : Function.Injective incl := HahnSeries.ofPowerSeries_injective
  have himage : i '' f.rootSet L = f.rootSet (LaurentSeries ℓ) :=
    (IsSplittingField.splits L f).image_rootSet i
  have hmem (x : L) :
      x ∈ f.rootSet L ↔ ∃ F ∈ g.roots, incl F = i x := by
    have hmem' : i x ∈ f.rootSet (LaurentSeries ℓ) ↔ x ∈ f.rootSet L := by
      rw [← himage, Set.mem_image]
      exact ⟨fun ⟨y, hy, h⟩ => i.injective h ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    rw [← hmem']
    simp only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, ← hla,
      hsp.roots_map_of_injective hincl, Multiset.mem_map]
  refine ⟨hred ▸ hsp.map red, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨F, _, hF⟩ := (hmem x).1 hx
    exact ⟨F, hF⟩
  · intro x hx
    obtain ⟨F, hF, hFx⟩ := (hmem x).1 hx
    change (i x).coeff 0 ∈ g₀.rootSet ℓ
    rw [← hFx, coeff_zero_powerToLaurent]
    simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, hroots] using
      (Multiset.mem_map.mpr ⟨F, hF, rfl⟩ : red F ∈ g.roots.map red)
  · intro x hx y hy hxy
    obtain ⟨F, hF, hFx⟩ := (hmem x).1 hx
    obtain ⟨G, hG, hGy⟩ := (hmem y).1 hy
    change (i x).coeff 0 = (i y).coeff 0 at hxy
    rw [← hFx, ← hGy, coeff_zero_powerToLaurent, coeff_zero_powerToLaurent] at hxy
    have hFG := Multiset.inj_on_of_nodup_map hnd F hF G hG hxy
    exact i.injective (hFx.symm.trans ((congrArg incl hFG).trans hGy))
  · intro r hr
    change r ∈ g₀.rootSet ℓ at hr
    have hr' : r ∈ g.roots.map red := by
      simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, hroots] using hr
    obtain ⟨F, hF, hrF⟩ := Multiset.mem_map.mp hr'
    have hFl : incl F ∈ f.rootSet (LaurentSeries ℓ) := by
      simp only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, aroots_def, ← hla,
        hsp.roots_map_of_injective hincl, Multiset.mem_map]
      exact ⟨F, hF, rfl⟩
    rw [← himage] at hFl
    obtain ⟨x, hx, hxF⟩ := hFl
    refine ⟨x, hx, ?_⟩
    change (i x).coeff 0 = r
    rw [hxF, coeff_zero_powerToLaurent]
    exact hrF


private def laurentInclusion (E : IntermediateField k ℓ) (a : k) :
    letI := substitutionAlgebra E a
    letI := substitutionAlgebra ℓ a
    LaurentSeries E →ₐ[RatFunc k] LaurentSeries ℓ :=
  letI := substitutionAlgebra E a
  letI := substitutionAlgebra ℓ a
  { toRingHom := laurentMap (algebraMap E ℓ)
    commutes' := fun x => DFunLike.congr_fun (substitution_naturality E ℓ a) x }

private theorem embedding_into_fibre (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    (hs : (specialize a f hf).Separable) [IsSplittingField (RatFunc k) L f]
    (i : PointEmbedding (ℓ := ℓ) a L) (hmatch : MatchesRoots i f hf) :
    let E := IntermediateField.adjoin k ((specialize a f hf).rootSet ℓ)
    ∃ j : PointEmbedding (ℓ := E) a L,
      ∀ x : L, laurentMap (algebraMap E ℓ) (j x) = i x := by
  let E := IntermediateField.adjoin k ((specialize a f hf).rootSet ℓ)
  let := substitutionAlgebra ℓ a
  let := substitutionAlgebra E a
  let inc := laurentInclusion E a
  have hroot (x : L) (hx : x ∈ f.rootSet L) : i x ∈ inc.range := by
    obtain ⟨F, hF⟩ := hmatch.1 x hx
    have hr := hmatch.2.mapsTo hx
    change (i x).coeff 0 ∈ (specialize a f hf).rootSet ℓ at hr
    rw [← hF, coeff_zero_powerToLaurent] at hr
    let r : E := ⟨PowerSeries.constantCoeff F, IntermediateField.subset_adjoin k _ hr⟩
    have hr₀ : ((specialize a f hf).map (algebraMap k ℓ)).eval (algebraMap E ℓ r) = 0 := by
      rw [eval_map]
      exact aeval_eq_zero_of_mem_rootSet hr
    have hrd : (((specialize a f hf).map (algebraMap k ℓ)).derivative).eval (algebraMap E ℓ r) ≠ 0 := by
      rw [derivative_map, eval_map]
      exact hs.eval₂_derivative_ne_zero (algebraMap k ℓ) (aeval_eq_zero_of_mem_rootSet hr)
    have hred : ((polynomialLift E a f hf).map PowerSeries.constantCoeff).map (algebraMap E ℓ) =
        (specialize a f hf).map (algebraMap k ℓ) := by
      rw [polynomialLift_reduction, map_map, ← IsScalarTower.algebraMap_eq]
    have hrg : ((polynomialLift E a f hf).map PowerSeries.constantCoeff).eval r = 0 := by
      apply (algebraMap E ℓ).injective
      rw [← eval_map_apply, hred, map_zero]
      exact hr₀
    have hrdg : ((polynomialLift E a f hf).map PowerSeries.constantCoeff).derivative.eval r ≠ 0 := by
      intro hz
      apply hrd
      rw [← hred, derivative_map, eval_map_apply, hz, map_zero]
    obtain ⟨G, hG, _⟩ := simpleRootLifting E E (polynomialLift E a f hf) r
      (by simpa using hrg) (by simpa using hrdg)
    obtain ⟨H, hH, huniq⟩ := simpleRootLifting E ℓ (polynomialLift E a f hf) (algebraMap E ℓ r)
      (by rw [hred]; exact hr₀) (by rw [hred]; exact hrd)
    -- Uniqueness over the larger field identifies the two lifts.
    have hGF : PowerSeries.map (algebraMap E ℓ) G = F := by
      calc
        PowerSeries.map (algebraMap E ℓ) G = H := huniq _ ⟨by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
          rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG.1], by
          rw [eval_map_apply]
          have hid : PowerSeries.map (RingHom.id E) = RingHom.id (PowerSeries E) :=
            RingHom.ext fun F => congrFun PowerSeries.map_id F
          have hG₂ : (polynomialLift E a f hf).eval G = 0 := by simpa [hid] using hG.2
          rw [hG₂, map_zero]⟩
        _ = F := (huniq _ ⟨rfl, by
          rw [polynomialLift_naturality]
          apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℓ))
          change powerToLaurent ℓ ((polynomialLift ℓ a f hf).eval F) = powerToLaurent ℓ 0
          rw [← eval_map_apply, polynomialLift_laurent, hF, map_zero]
          rw [eval_map]
          exact aeval_eq_zero_of_mem_rootSet (rootSet_mapsTo i hx)⟩).symm
    refine ⟨powerToLaurent E G, ?_⟩
    change laurentMap (algebraMap E ℓ) (powerToLaurent E G) = i x
    rw [laurentMap_powerToLaurent, hGF, hF]
  have hrange : i.range ≤ inc.range := by
    rw [← IsSplittingField.adjoin_rootSet_eq_range L f i, Algebra.adjoin_le_iff]
    rw [← (IsSplittingField.splits L f).image_rootSet i]
    rintro _ ⟨x, hx, rfl⟩
    exact hroot x hx
  let j := (AlgEquiv.ofInjectiveField inc).symm.toAlgHom.comp
    (i.codRestrict inc.range (fun x => hrange (i.mem_range_self x)))
  refine ⟨j, fun x => ?_⟩
  exact congrArg Subtype.val ((AlgEquiv.ofInjectiveField inc).apply_symm_apply
    ⟨i x, hrange (i.mem_range_self x)⟩)


private theorem orderTop_laurentMap {E : Type*} [Field E] (g : E →+* ℓ)
    (s : LaurentSeries E) : (laurentMap g s).orderTop = s.orderTop := by
  apply le_antisymm
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro n hn
    have h := HahnSeries.coeff_eq_zero_of_lt_orderTop hn
    rw [laurentMap_coeff] at h
    exact g.injective (h.trans (map_zero g).symm)
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro n hn
    rw [laurentMap_coeff, HahnSeries.coeff_eq_zero_of_lt_orderTop hn, map_zero]

/-- Good specialization commutes with restriction in a tower of splitting fields. -/
theorem towerSpecialization : TowerSpecializationType := by
  intro k _ ℓ _ _ a L _ _ f f₀ hf hf₀ hm hm₀ hs hs₀ _ _ i hmatch L₀ _
  let := substitutionAlgebra ℓ a
  let i₀ : PointEmbedding (ℓ := ℓ) a L₀ := i.comp L₀.val
  obtain ⟨hsp, hmatch'⟩ := splits_and_matches f₀ hf₀ hm₀ hs₀ i₀
  let E := IntermediateField.adjoin k ((specialize a f₀ hf₀).rootSet ℓ)
  have hE : IsSplittingField k E (specialize a f₀ hf₀) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsp
  let := hE
  let := Normal.of_isSplittingField (E := E) (specialize a f₀ hf₀)
  let := Normal.of_isSplittingField (E := L₀) f₀
  let := Normal.of_isSplittingField (E := ℓ) (specialize a f hf)
  obtain ⟨j, hj⟩ := embedding_into_fibre f₀ hf₀ hs₀ i₀ hmatch'
  have hj' (x : L₀) : laurentMap (algebraMap E ℓ) (j x) = i (x : L) := hj x
  have hmatch₀ := (splits_and_matches f₀ hf₀ hm₀ hs₀ j).2
  have hw (x : L₀) : inducedOrder j.toRingHom x = inducedOrder i.toRingHom (x : L) := by
    change (j x).orderTop = (i (x : L)).orderTop
    rw [← hj', orderTop_laurentMap]
  let := residueAlgebra i
  let := residueAlgebra j
  obtain ⟨e, he⟩ := residueFieldEquivalence f hf hm hs i hmatch
  obtain ⟨e₀, he₀⟩ := residueFieldEquivalence f₀ hf₀ hm₀ hs₀ j hmatch₀
  obtain ⟨d, hd⟩ := decompositionEquivalence f hf hm hs i hmatch
  obtain ⟨d₀, hd₀⟩ := decompositionEquivalence f₀ hf₀ hm₀ hs₀ j hmatch₀
  let incl := includeValuationRing i L₀ E j hw
  let res := restrictDecomposition i L₀ E j hw
  have hred (x : valuationRing j.toRingHom) :
      (reduction j.toRingHom x : ℓ) = reduction i.toRingHom (incl x) := by
    rw [reduction_apply, reduction_apply]
    change algebraMap E ℓ ((j (x : L₀)).coeff 0) = (i ((x : L₀) : L)).coeff 0
    rw [← laurentMap_coeff, hj']
  have hres (σ : decompositionGroup i) (x : valuationRing j.toRingHom) :
      incl (onValuationRing j (res σ) x) = onValuationRing i σ (incl x) := by
    apply Subtype.ext
    change (↑(AlgEquiv.restrictNormalHom L₀ σ.val (x : L₀)) : L) = σ.val ((x : L₀) : L)
    exact AlgEquiv.restrictNormalHom_apply L₀ σ.val (x : L₀)
  have hsurj₀ : Function.Surjective (reduction j.toRingHom) := by
    intro y
    obtain ⟨q, rfl⟩ := e₀.surjective y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective q
    refine ⟨x, ?_⟩
    change reduction j.toRingHom x = e₀.toRingHom (IsLocalRing.residue _ x)
    rw [he₀, residueEmbedding_residue]
    exact (reduction_apply j.toRingHom x)
  have hresidue (x : valuationRing j.toRingHom) :
      (↑(e₀.toRingHom (IsLocalRing.residue _ x)) : ℓ) =
        e.toRingHom (IsLocalRing.residue _ (incl x)) := by
    rw [he₀, he, residueEmbedding_residue, residueEmbedding_residue]
    rw [← reduction_apply, ← reduction_apply]
    exact hred x
  have hcomm (σ : decompositionGroup i) :
      d₀ (res σ) = AlgEquiv.restrictNormalHom E (d σ) := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj₀ y
    apply (algebraMap E ℓ).injective
    change (↑(d₀ (res σ) (reduction j.toRingHom x)) : ℓ) =
      (↑(AlgEquiv.restrictNormalHom E (d σ) (reduction j.toRingHom x)) : ℓ)
    rw [hd₀, AlgEquiv.restrictNormalHom_apply, hred, hred, hd, hres]
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom E : (ℓ ≃ₐ[k] ℓ) →* (E ≃ₐ[k] E)) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) ℓ
  refine ⟨hE, j, hmatch₀, hj', hw, e, e₀, d, d₀, he, he₀, hresidue, hd, hd₀,
    hcomm, hsurj, ?_⟩
  intro τ
  obtain ⟨ϕ, hϕ⟩ := hsurj (d₀ τ)
  obtain ⟨σ, rfl⟩ := d.surjective ϕ
  exact ⟨σ, d₀.injective ((hcomm σ).trans hϕ)⟩

end

end GaloisFormalization.IG.TowerSpecialization
