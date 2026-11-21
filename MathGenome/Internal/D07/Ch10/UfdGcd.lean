import MathGenome.Internal.Specs.D07.Ch10.UfdGcd
import MathGenome.Internal.D07.Ch10.GcdLcm
import MathGenome.Internal.D07.Ch10.UfdPrimeIrreducible
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! Prime-exponent arithmetic with arbitrary prime representatives. -/

universe u

namespace D07.Ch10.UfdGcd

open Specs.D07.Ch10.UfdGcd Specs.D07.Ch10.GcdLcm
open UniqueFactorizationMonoid

section Helpers
variable {R : Type u} [CommRing R] [IsDomain R]

lemma primePowerProduct_ne_zero (s : Finset R) (e : R → ℕ)
    (hs : ∀ p ∈ s, Prime p) : (∏ p ∈ s, p ^ e p) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hs p hp).ne_zero

omit [IsDomain R] in
lemma associated_unit_mul (v : Rˣ) (a : R) : Associated a ((v : R) * a) :=
  ⟨v, mul_comm _ _⟩

/-- Only one representative contributes to the multiplicity of a given prime. -/
lemma emultiplicity_product_of_mem (s : Finset R) (e : R → ℕ)
    (hs : ∀ p ∈ s, Prime p) (hpair : (s : Set R).Pairwise (fun p q => ¬Associated p q))
    {p : R} (hp : p ∈ s) :
    emultiplicity p (∏ q ∈ s, q ^ e q) = (e p : ℕ∞) := by
  classical
  rw [Finset.emultiplicity_prod (hs p hp)]
  rw [Finset.sum_eq_single p]
  · exact emultiplicity_pow_self_of_prime (hs p hp) _
  · intro q hq hqp
    rw [emultiplicity_pow (hs p hp)]
    have hndvd : ¬p ∣ q := by
      intro hdvd
      exact hpair hp hq hqp.symm
        (((hs p hp).irreducible.dvd_irreducible_iff_associated (hs q hq).irreducible).mp hdvd)
    rw [emultiplicity_eq_zero.mpr hndvd, mul_zero]
  · exact fun h => (h hp).elim

lemma emultiplicity_product_of_absent (s : Finset R) (e : R → ℕ)
    (hs : ∀ p ∈ s, Prime p) {p : R} (hp : Prime p)
    (habs : ∀ q ∈ s, ¬Associated p q) :
    emultiplicity p (∏ q ∈ s, q ^ e q) = 0 := by
  rw [Finset.emultiplicity_prod hp]
  apply Finset.sum_eq_zero
  intro q hq
  rw [emultiplicity_pow hp]
  have hndvd : ¬p ∣ q := by
    intro hdvd
    exact habs q hq
      ((hp.irreducible.dvd_irreducible_iff_associated (hs q hq).irreducible).mp hdvd)
  rw [emultiplicity_eq_zero.mpr hndvd, mul_zero]

/-- Min and max compute the multiplicity at every prime, including primes
absent from both inputs. This is the bridge to the universal conditions. -/
lemma emultiplicity_min_max (s : Finset R) (e f : R → ℕ)
    (hs : ∀ p ∈ s, Prime p) (hpair : (s : Set R).Pairwise (fun p q => ¬Associated p q))
    {p : R} (hp : Prime p) :
    emultiplicity p (∏ q ∈ s, q ^ min (e q) (f q)) =
        min (emultiplicity p (∏ q ∈ s, q ^ e q))
          (emultiplicity p (∏ q ∈ s, q ^ f q)) ∧
    emultiplicity p (∏ q ∈ s, q ^ max (e q) (f q)) =
        max (emultiplicity p (∏ q ∈ s, q ^ e q))
          (emultiplicity p (∏ q ∈ s, q ^ f q)) := by
  classical
  by_cases hex : ∃ q ∈ s, Associated p q
  · obtain ⟨q, hq, hpq⟩ := hex
    simp_rw [← emultiplicity_eq_of_associated_left hpq]
    rw [emultiplicity_product_of_mem s _ hs hpair hq,
      emultiplicity_product_of_mem s _ hs hpair hq,
      emultiplicity_product_of_mem s _ hs hpair hq,
      emultiplicity_product_of_mem s _ hs hpair hq]
    constructor <;> norm_cast
  · have habs : ∀ q ∈ s, ¬Associated p q := by simpa only [not_exists, not_and] using hex
    simp only [emultiplicity_product_of_absent s _ hs hp habs, min_self, max_self, and_self]

end Helpers

theorem primePowerRepresentations : PrimePowerRepresentations.{u} := by
  intro R _ _ _ a b ha hb
  classical
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset
  have hmem (p : R) : p ∈ s ↔ p ∈ normalizedFactors a ∨ p ∈ normalizedFactors b := by
    simp only [s, Finset.mem_union, Multiset.mem_toFinset]
  have hn (p : R) (hp : p ∈ s) : normalize p = p := by
    rcases (hmem p).mp hp with h | h <;> exact normalize_normalized_factor p h
  have hPa : Associated (∏ p ∈ s, p ^ (normalizedFactors a).count p) a := by
    rw [← Finset.prod_multiset_count_of_subset (normalizedFactors a) s Finset.subset_union_left]
    exact prod_normalizedFactors ha
  have hPb : Associated (∏ p ∈ s, p ^ (normalizedFactors b).count p) b := by
    rw [← Finset.prod_multiset_count_of_subset (normalizedFactors b) s Finset.subset_union_right]
    exact prod_normalizedFactors hb
  obtain ⟨v, hv⟩ := hPa
  obtain ⟨w, hw⟩ := hPb
  refine ⟨s, fun p => (normalizedFactors a).count p,
    fun p => (normalizedFactors b).count p, v, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases (hmem p).mp hp with h | h <;> exact prime_of_normalized_factor p h
  · intro p hp q hq hpq hassoc
    exact hpq (hassoc.eq_of_normalized (hn p hp) (hn q hq))
  · intro p hp
    exact ((hmem p).mp hp).imp dvd_of_mem_normalizedFactors dvd_of_mem_normalizedFactors
  · intro p hp
    have hpa : p ∉ normalizedFactors a := fun h => hp ((hmem p).mpr (Or.inl h))
    have hpb : p ∉ normalizedFactors b := fun h => hp ((hmem p).mpr (Or.inr h))
    exact ⟨Multiset.count_eq_zero_of_notMem hpa, Multiset.count_eq_zero_of_notMem hpb⟩
  · simpa only [mul_comm] using hv.symm
  · simpa only [mul_comm] using hw.symm

theorem divisibilityByExponents : DivisibilityByExponents.{u} := by
  intro R _ _ _ s e f a b v w hs hpair ha hb
  have haP : Associated a (∏ p ∈ s, p ^ e p) := by
    rw [ha]; exact (associated_unit_mul v _).symm
  have hbP : Associated b (∏ p ∈ s, p ^ f p) := by
    rw [hb]; exact (associated_unit_mul w _).symm
  constructor
  · intro hab p hp
    have h := emultiplicity_le_emultiplicity_of_dvd_right (a := p) hab
    rw [emultiplicity_eq_of_associated_right haP,
      emultiplicity_eq_of_associated_right hbP,
      emultiplicity_product_of_mem s e hs hpair hp,
      emultiplicity_product_of_mem s f hs hpair hp] at h
    exact_mod_cast h
  · intro h
    exact haP.dvd.trans ((Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
      pow_dvd_pow p (h p hp)).trans hbP.symm.dvd)

theorem gcdFromMinimum : GcdFromMinimum.{u} := by
  intro R _ _ _ s e f a b v w hs hpair ha hb
  have haP : Associated a (∏ p ∈ s, p ^ e p) := by
    rw [ha]; exact (associated_unit_mul v _).symm
  have hbP : Associated b (∏ p ∈ s, p ^ f p) := by
    rw [hb]; exact (associated_unit_mul w _).symm
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (Units.ne_zero v) (primePowerProduct_ne_zero s e hs)
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow p (min_le_left (e p) (f p))).trans haP.symm.dvd
  · exact (Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow p (min_le_right (e p) (f p))).trans hbP.symm.dvd
  · intro c hca hcb
    have hc : c ≠ 0 := by rintro rfl; exact ha0 (zero_dvd_iff.mp hca)
    apply (dvd_iff_emultiplicity_le hc).mpr
    intro p hp
    rw [(emultiplicity_min_max s e f hs hpair hp).1]
    exact le_min
      ((emultiplicity_le_emultiplicity_of_dvd_right (a := p) hca).trans_eq
        (emultiplicity_eq_of_associated_right haP))
      ((emultiplicity_le_emultiplicity_of_dvd_right (a := p) hcb).trans_eq
        (emultiplicity_eq_of_associated_right hbP))

theorem lcmFromMaximum : LcmFromMaximum.{u} := by
  intro R _ _ _ s e f a b v w hs hpair ha hb
  have haP : Associated a (∏ p ∈ s, p ^ e p) := by
    rw [ha]; exact (associated_unit_mul v _).symm
  have hbP : Associated b (∏ p ∈ s, p ^ f p) := by
    rw [hb]; exact (associated_unit_mul w _).symm
  refine ⟨?_, ?_, ?_⟩
  · exact haP.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow p (le_max_left (e p) (f p)))
  · exact hbP.dvd.trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow p (le_max_right (e p) (f p)))
  · intro c hac hbc
    apply (dvd_iff_emultiplicity_le (primePowerProduct_ne_zero s _ hs)).mpr
    intro p hp
    rw [(emultiplicity_min_max s e f hs hpair hp).2]
    exact max_le
      ((emultiplicity_eq_of_associated_right haP).symm.trans_le
        (emultiplicity_le_emultiplicity_of_dvd_right (a := p) hac))
      ((emultiplicity_eq_of_associated_right hbP).symm.trans_le
        (emultiplicity_le_emultiplicity_of_dvd_right (a := p) hbc))

theorem minMaxProduct : MinMaxProduct.{u} := by
  intro R _ _ s e f
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add, ← pow_add, min_add_max]

theorem zeroInputProducts : ZeroInputProducts.{u} := by
  intro R _ _ a b d m hz _ hm
  rcases hz with rfl | rfl
  · have hm0 : m = 0 := (D07.Ch10.GcdLcm.lcmZeroLeft R b m).mp hm
    simp only [hm0, mul_zero, zero_mul, and_self]
  · have hm0 : m = 0 := (D07.Ch10.GcdLcm.lcmZeroRight R a m).mp hm
    simp only [hm0, mul_zero, and_self]

theorem gcdLcmProductAssociation : GcdLcmProductAssociation.{u} := by
  intro R _ _ _ a b d m hd hm
  by_cases ha : a = 0
  · obtain ⟨h1, h2⟩ := zeroInputProducts R a b d m (Or.inl ha) hd hm
    rw [h1, h2]
  by_cases hb : b = 0
  · obtain ⟨h1, h2⟩ := zeroInputProducts R a b d m (Or.inr hb) hd hm
    rw [h1, h2]
  obtain ⟨s, e, f, v, w, hs, hpair, _, _, hPa, hPb⟩ :=
    primePowerRepresentations R a b ha hb
  have hd' := gcdFromMinimum R s e f a b v w hs hpair hPa hPb
  have hm' := lcmFromMaximum R s e f a b v w hs hpair hPa hPb
  have hdD := D07.Ch10.GcdLcm.gcdUniqueUpToAssociates R a b d _ hd hd'
  have hmM := D07.Ch10.GcdLcm.lcmUniqueUpToAssociates R a b m _ hm hm'
  apply (hdD.mul_mul hmM).trans
  rw [minMaxProduct R s e f]
  exact ((associated_unit_mul v _).trans (Associated.of_eq hPa.symm)).mul_mul
    ((associated_unit_mul w _).trans (Associated.of_eq hPb.symm))

theorem gcdLcmExistence : GcdLcmExistence.{u} := by
  intro R _ _ _ a b
  by_cases ha : a = 0
  · subst a
    have hz := D07.Ch10.GcdLcm.zeroConventions R b
    exact ⟨b, 0, hz.2.2.1, hz.2.2.2.2,
      gcdLcmProductAssociation R 0 b b 0 hz.2.2.1 hz.2.2.2.2⟩
  by_cases hb : b = 0
  · subst b
    have hz := D07.Ch10.GcdLcm.zeroConventions R a
    exact ⟨a, 0, hz.2.1, hz.2.2.2.1,
      gcdLcmProductAssociation R a 0 a 0 hz.2.1 hz.2.2.2.1⟩
  obtain ⟨s, e, f, v, w, hs, hpair, _, _, hPa, hPb⟩ :=
    primePowerRepresentations R a b ha hb
  have hd := gcdFromMinimum R s e f a b v w hs hpair hPa hPb
  have hm := lcmFromMaximum R s e f a b v w hs hpair hPa hPb
  exact ⟨_, _, hd, hm, gcdLcmProductAssociation R a b _ _ hd hm⟩

end D07.Ch10.UfdGcd
