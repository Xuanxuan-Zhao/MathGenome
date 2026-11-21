import MathGenome.Internal.Specs.D07.Appendix.PiTranscendentalSubsetSumRelation
import MathGenome.Internal.D07.Appendix.AlgebraicFta
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
Subset sums in the special Lindemann argument, paper.tex:7784–7819.
The multiset is indexed by all subsets of the distinct conjugates. Injective
homomorphisms biject subsets, so the construction commutes with embeddings and
automorphisms, including repeated values of the sum. In a finite Galois field,
fixed coefficients are in the image of Q. We construct this field as an
intermediate field of C and transport its rational product along the inclusion.
The exponential identity is proved separately by finite distributivity.
-/

namespace D07.Appendix.PiTranscendentalSubsetSumRelation

open Polynomial Classical
open Specs.D07.Appendix.PiTranscendentalSubsetSumRelation
open scoped BigOperators

/-- Taking every subset sum commutes with an injective ring homomorphism. -/
theorem subsetSums_image {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (s : Finset R) :
    subsetSums (s.image f) = (subsetSums s).map f := by
  classical
  have hfin : Function.Injective (fun t : Finset R => t.image f) := by
    intro t u h
    exact Finset.image_injective hf h
  have himg : s.powerset.image (fun t => t.image f) =
      s.powerset.map ⟨(fun t => t.image f), hfin⟩ :=
    (Finset.map_eq_image ⟨(fun t => t.image f), hfin⟩ s.powerset).symm
  rw [subsetSums, Finset.powerset_image, himg,
    Finset.map_val, Multiset.map_map, subsetSums, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro t _
  change (∑ x ∈ t.image f, x) = f (∑ x ∈ t, x)
  rw [Finset.sum_image (fun _ _ _ _ h => hf h), map_sum]

theorem nonzeroSums_image {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (s : Finset R) :
    nonzeroSums (s.image f) = (nonzeroSums s).map f := by
  classical
  simp only [nonzeroSums]
  rw [subsetSums_image f hf, Multiset.filter_map]
  have hz (x : R) : f x ≠ 0 ↔ x ≠ 0 :=
    not_congr (by rw [← map_zero f]; exact hf.eq_iff)
  simp only [Function.comp_def, hz]

theorem rootProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b : Multiset R) :
    (rootProduct b).map f = rootProduct (b.map f) := by
  change (Polynomial.mapRingHom f) _ = _
  rw [rootProduct, map_multiset_prod, Multiset.map_map, rootProduct, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro x _
  simp

theorem roots_image_automorphism {L : Type*} [Field L] [Algebra ℚ L]
    (p : ℚ[X]) (σ : L ≃ₐ[ℚ] L) :
    (distinctRoots p L).image σ = distinctRoots p L := by
  classical
  unfold distinctRoots
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : y ∈ p.rootSet L := by
      simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset] using hy
    have hz := Polynomial.rootSet_mapsTo (p := p) σ.toAlgHom hy'
    simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, AlgEquiv.coe_toAlgHom] using hz
  · intro hx
    refine Finset.mem_image.mpr ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
    have hx' : x ∈ p.rootSet L := by
      simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset] using hx
    have hz := Polynomial.rootSet_mapsTo (p := p) σ.symm.toAlgHom hx'
    simpa only [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset, AlgEquiv.coe_toAlgHom] using hz

theorem galois_subset_sums : GaloisSubsetSums := by
  classical
  intro L _ _ p σ
  dsimp only
  have hs := subsetSums_image σ.toRingHom σ.injective (distinctRoots p L)
  have hb := nonzeroSums_image σ.toRingHom σ.injective (distinctRoots p L)
  rw [show (distinctRoots p L).image σ.toRingHom = distinctRoots p L from
    roots_image_automorphism p σ] at hs hb
  refine ⟨hs.symm, hb.symm, ?_⟩
  rw [rootProduct_map, ← hb]

/-- Fixed coefficients descend to Q; no individual subset sum is assumed rational. -/
theorem rational_rootProduct {L : Type} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (p : ℚ[X]) :
    ∃ P : ℚ[X], P.map (algebraMap ℚ L) =
      rootProduct (nonzeroSums (distinctRoots p L)) := by
  classical
  apply (Polynomial.mem_map_range (algebraMap ℚ L)).mpr
  intro n
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  have h := (galois_subset_sums L p σ).2.2
  have hc := congrArg (fun q : L[X] => q.coeff n) h
  simp only [coeff_map] at hc
  change σ _ = _ at hc
  exact hc

/-- Splitting in L identifies every complex root, with no roots lost in transport. -/
theorem roots_image_overfield {L E : Type*} [Field L] [Field E]
    [Algebra ℚ L] [Algebra ℚ E] [Algebra L E] [IsScalarTower ℚ L E]
    (p : ℚ[X]) (hsplit : (p.map (algebraMap ℚ L)).Splits) :
    distinctRoots p E = (distinctRoots p L).image (algebraMap L E) := by
  classical
  have hmap : p.map (algebraMap ℚ E) =
      (p.map (algebraMap ℚ L)).map (algebraMap L E) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ L E]
  simp only [distinctRoots]
  rw [aroots_def, hmap, hsplit.roots_map, Multiset.toFinset_map]

theorem subsetSums_partition {R : Type*} [AddCommMonoid R] (s : Finset R) :
    subsetSums s = Multiset.replicate (zeroCount s) 0 + nonzeroSums s := by
  classical
  have h := (Multiset.filter_add_not (fun x : R => x = 0) (subsetSums s)).symm
  have h0 := Multiset.filter_eq' (subsetSums s) (0 : R)
  exact h.trans (congrArg₂ (· + ·) h0 rfl)

theorem zeroCount_pos {R : Type*} [AddCommMonoid R] (s : Finset R) :
    0 < zeroCount s := by
  classical
  rw [zeroCount, Multiset.count_pos, subsetSums, Multiset.mem_map]
  exact ⟨∅, by simp, by simp⟩

theorem nonzeroSums_pos {R : Type*} [AddCommMonoid R] (s : Finset R)
    {α : R} (ha : α ∈ s) (hα : α ≠ 0) : 0 < (nonzeroSums s).card := by
  classical
  apply Multiset.card_pos_iff_exists_mem.mpr
  refine ⟨α, ?_⟩
  simp only [nonzeroSums, Multiset.mem_filter]
  refine ⟨?_, hα⟩
  rw [subsetSums, Multiset.mem_map]
  exact ⟨{α}, by simpa using ha, by simp⟩

theorem exponential_relation (s : Finset ℂ) {α : ℂ}
    (ha : α ∈ s) (he : Complex.exp α = -1) :
    (zeroCount s : ℂ) + ((nonzeroSums s).map Complex.exp).sum = 0 := by
  classical
  have h : ((subsetSums s).map Complex.exp).sum = 0 := by
    rw [subsetSums, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    simp only [Function.comp_def, Complex.exp_sum]
    rw [← Finset.prod_one_add]
    exact Finset.prod_eq_zero ha (by rw [he]; simp)
  rw [subsetSums_partition, Multiset.map_add, Multiset.sum_add,
    Multiset.map_replicate, Complex.exp_zero, Multiset.sum_replicate] at h
  simpa only [nsmul_eq_mul, mul_one] using h

/-- Construct the splitting field inside C, descend the invariant product there,
and transport it along its actual inclusion into C. -/
theorem conjugates_rational_product (α : ℂ) (ha : IsAlgebraic ℚ α) :
    ∃ P : ℚ[X], P.map (algebraMap ℚ ℂ) = rootProduct (nonzeroSums (conjugates α)) := by
  classical
  let p := minpoly ℚ α
  let L := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have hsplit : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  let : p.IsSplittingField ℚ L := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  let : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L p
  let : IsGalois ℚ L := IsGalois.of_separable_splitting_field
    (minpoly.irreducible ha.isIntegral).separable
  obtain ⟨P, hP⟩ := rational_rootProduct (L := L) p
  refine ⟨P, ?_⟩
  have hroots := roots_image_overfield (L := L) (E := ℂ) p
    (Polynomial.IsSplittingField.splits L p)
  have hβ := nonzeroSums_image (algebraMap L ℂ) (algebraMap L ℂ).injective
    (distinctRoots p L)
  have hβ' : nonzeroSums (distinctRoots p ℂ) =
      (nonzeroSums (distinctRoots p L)).map (algebraMap L ℂ) :=
    (congrArg nonzeroSums hroots).trans hβ
  have h := congrArg (Polynomial.map (algebraMap L ℂ)) hP
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ L ℂ, rootProduct_map, ← hβ'] at h
  exact h

theorem subset_sum_relation : SubsetSumRelation := by
  classical
  intro α hn ha he
  have hm : α ∈ conjugates α := by
    simpa only [conjugates, distinctRoots, Multiset.mem_toFinset, Polynomial.mem_aroots] using
      And.intro (minpoly.ne_zero ha.isIntegral) (minpoly.aeval ℚ α)
  refine ⟨((conjugates α).erase α).toList, ?_, ?_, zeroCount_pos _,
    nonzeroSums_pos _ hm hn, ?_, subsetSums_partition _, exponential_relation _ hm he,
    conjugates_rational_product α ha⟩
  · exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  · rw [List.toFinset_cons, Finset.toList_toFinset, Finset.insert_erase hm]
  · intro β hβ
    exact (Multiset.mem_filter.mp hβ).2

end D07.Appendix.PiTranscendentalSubsetSumRelation
