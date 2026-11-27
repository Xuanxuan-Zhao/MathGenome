import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CubicGaloisCriterion
import Mathlib.LinearAlgebra.Vandermonde

open Polynomial
open scoped Polynomial

namespace GaloisFormalization.IG

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem cubic_root_ordering (p : K[X]) [p.IsSplittingField K L]
    (hdegree : p.natDegree = 3) (hsep : p.Separable) : Nonempty (CubicRootOrdering p L) := by
  exact ⟨(Fintype.equivFinOfCardEq
    ((card_rootSet_eq_natDegree hsep (IsSplittingField.splits L p)).trans hdegree)).symm⟩

variable {p : K[X]} [p.IsSplittingField K L] (e : CubicRootOrdering p L)

theorem cubic_root_action_apply (σ : L ≃ₐ[K] L) (i : Fin 3) :
    (e (cubicRootAction e σ i)).val = σ (e i).val := by
  let : Fact (p.map (algebraMap K L)).Splits := ⟨IsSplittingField.splits L p⟩
  change (e (e.symm (Gal.galActionHom p L (Gal.restrict p L σ) (e i)))).val = σ (e i).val
  rw [e.apply_symm_apply]
  exact Gal.galActionHom_restrict p L σ (e i)

theorem cubic_root_action_faithful_transitive (hirr : Irreducible p) :
    Function.Injective (cubicRootAction e) ∧
      ∀ i j : Fin 3, ∃ σ : L ≃ₐ[K] L, cubicRootAction e σ i = j := by
  constructor
  · intro σ τ hστ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet L p)
    intro x hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hσ : (e (cubicRootAction e σ i)).val = σ (e i).val :=
      cubic_root_action_apply e σ i
    have hτ : (e (cubicRootAction e τ i)).val = τ (e i).val :=
      cubic_root_action_apply e τ i
    rw [hστ] at hσ
    rw [← show (e i).val = x from congrArg Subtype.val hi]
    exact hσ.symm.trans hτ
  · let : Fact (p.map (algebraMap K L)).Splits := ⟨IsSplittingField.splits L p⟩
    let : Normal K L := Normal.of_isSplittingField p
    intro i j
    obtain ⟨g, hg⟩ := (Gal.galAction_isPretransitive p L hirr).exists_smul_eq (e i) (e j)
    obtain ⟨σ, rfl⟩ := Gal.restrict_surjective p L g
    refine ⟨σ, ?_⟩
    change e.symm (Gal.galActionHom p L (Gal.restrict p L σ) (e i)) = j
    change Gal.galActionHom p L (Gal.restrict p L σ) (e i) = e j at hg
    rw [hg, e.symm_apply_apply]

theorem cubic_discriminant_of_roots (p : K[X]) (r : Fin 3 → L)
    (hmon : p.Monic) (hdegree : p.natDegree = 3)
    (hroots : (p.map (algebraMap K L)).roots = {r 0, r 1, r 2}) :
    cubicVandermonde r ^ 2 = algebraMap K L (cubicDiscriminant p) := by
  let P : Cubic K := ⟨p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0⟩
  have hpdeg : p.degree ≤ 3 := by
    rw [degree_eq_natDegree hmon.ne_zero, hdegree]
    exact le_rfl
  have hP : P.toPoly = p :=
    congrArg (fun q : {q : K[X] // q.degree ≤ 3} => q.val)
      (Cubic.equiv.apply_symm_apply ⟨p, hpdeg⟩)
  have ha : P.a = 1 := by
    change p.coeff 3 = 1
    rw [← hdegree, coeff_natDegree, hmon.leadingCoeff]
  have hrootsP : (P.map (algebraMap K L)).roots = {r 0, r 1, r 2} := by
    rw [Cubic.map_roots, hP, hroots]
  have h := Cubic.discr_eq_prod_three_roots (ha.trans_ne one_ne_zero) hrootsP
  change cubicVandermonde r ^ 2 = algebraMap K L P.discr
  simpa only [ha, map_one, one_mul, cubicVandermonde] using h.symm

omit [p.IsSplittingField K L] in
private theorem cubic_roots_eq (hsep : p.Separable) :
    (p.map (algebraMap K L)).roots = {(e 0).val, (e 1).val, (e 2).val} := by
  classical
  let r : Fin 3 → L := fun i => (e i).val
  let roots : Multiset L := {r 0, r 1, r 2}
  have hr : Function.Injective r := Subtype.val_injective.comp e.injective
  have h01 : r 0 ≠ r 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hr h)
  have h02 : r 0 ≠ r 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hr h)
  have h12 : r 1 ≠ r 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hr h)
  change (p.aroots L) = roots
  apply Multiset.Nodup.toFinset_inj (nodup_roots hsep.map)
  · simp [roots, h01, h02, h12]
  · apply Finset.coe_injective
    rw [← rootSet_def]
    ext x
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      rw [← show r i = x from congrArg Subtype.val hi]
      fin_cases i <;> simp [roots]
    · change x ∈ ([r 0, r 1, r 2] : Multiset L) → x ∈ p.rootSet L
      simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl)
      all_goals exact (e _).property

omit [p.IsSplittingField K L] in
theorem cubic_discriminant_eq_vandermonde_sq
    (hmon : p.Monic) (hdegree : p.natDegree = 3) (hsep : p.Separable) :
    cubicVandermonde (fun i => (e i).val) ^ 2 = algebraMap K L (cubicDiscriminant p) := by
  exact cubic_discriminant_of_roots p (fun i => (e i).val) hmon hdegree (cubic_roots_eq e hsep)

/-- Negating the rows' parameters gives the differences with the earlier root first. -/
private theorem cubicVandermonde_eq_det {R : Type*} [CommRing R] (r : Fin 3 → R) :
    cubicVandermonde r = (Matrix.vandermonde (fun i => -r i)).det := by
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  rw [Matrix.det_vandermonde, Fin.prod_univ_three, h0, h1, h2]
  simp [cubicVandermonde, sub_eq_add_neg, add_comm]

theorem cubic_vandermonde_permutation_sign {R : Type*} [CommRing R] (r : Fin 3 → R)
    (π : Equiv.Perm (Fin 3)) :
    cubicVandermonde (r ∘ π) = ((Equiv.Perm.sign π : ℤ) : R) * cubicVandermonde r := by
  rw [cubicVandermonde_eq_det, cubicVandermonde_eq_det]
  exact Matrix.det_permute π (Matrix.vandermonde (fun i => -r i))

theorem cubic_vandermonde_automorphism_sign (σ : L ≃ₐ[K] L) :
    σ (cubicVandermonde (fun i => (e i).val)) =
      ((Equiv.Perm.sign (cubicRootAction e σ) : ℤ) : L) *
        cubicVandermonde (fun i => (e i).val) := by
  have hmap : σ (cubicVandermonde (fun i => (e i).val)) =
      cubicVandermonde (fun i => σ (e i).val) := by
    simp only [cubicVandermonde, map_mul, map_sub]
  have hcomp : (fun i => σ (e i).val) =
      (fun i => (e i).val) ∘ cubicRootAction e σ := by
    funext i
    exact (cubic_root_action_apply e σ i).symm
  rw [hmap, hcomp]
  exact cubic_vandermonde_permutation_sign (fun i => (e i).val) (cubicRootAction e σ)

omit [p.IsSplittingField K L] in
theorem cubic_vandermonde_mem_base_iff_square
    (hmon : p.Monic) (hdegree : p.natDegree = 3) (hsep : p.Separable) :
    cubicVandermonde (fun i => (e i).val) ∈ Set.range (algebraMap K L) ↔
      IsSquare (cubicDiscriminant p) := by
  let d := cubicVandermonde (fun i => (e i).val)
  have hd : d ^ 2 = algebraMap K L (cubicDiscriminant p) :=
    cubic_discriminant_eq_vandermonde_sq e hmon hdegree hsep
  change d ∈ Set.range (algebraMap K L) ↔ IsSquare (cubicDiscriminant p)
  rw [isSquare_iff_exists_sq]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, (algebraMap K L).injective ?_⟩
    rw [map_pow, hc, hd]
  · rintro ⟨c, hc⟩
    have hsq : d ^ 2 = (algebraMap K L c) ^ 2 := by rw [hd, hc, map_pow]
    rcases eq_or_eq_neg_of_sq_eq_sq d (algebraMap K L c) hsq with h | h
    · exact ⟨c, h.symm⟩
    · exact ⟨-c, (map_neg (algebraMap K L) c).trans h.symm⟩

theorem cubic_root_action_alternating_iff_mem_base [CharZero K] (hsep : p.Separable) :
    (cubicRootAction e).range ≤ alternatingGroup (Fin 3) ↔
      cubicVandermonde (fun i => (e i).val) ∈ Set.range (algebraMap K L) := by
  let : FiniteDimensional K L := IsSplittingField.finiteDimensional L p
  let : IsGalois K L := IsGalois.of_separable_splitting_field hsep
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let d := cubicVandermonde (fun i => (e i).val)
  have hd : d ≠ 0 := by
    rw [show d = _ from cubicVandermonde_eq_det _]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (neg_injective.comp (Subtype.val_injective.comp e.injective))
  change (cubicRootAction e).range ≤ alternatingGroup (Fin 3) ↔
    d ∈ Set.range (algebraMap K L)
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro h σ
    have hs := Equiv.Perm.mem_alternatingGroup.mp (h ⟨σ, rfl⟩)
    have hsign : σ d = ((Equiv.Perm.sign (cubicRootAction e σ) : ℤ) : L) * d :=
      cubic_vandermonde_automorphism_sign e σ
    simpa only [hs, Units.val_one, Int.cast_one, one_mul] using hsign
  · rintro h π ⟨σ, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    rcases Int.units_eq_one_or (Equiv.Perm.sign (cubicRootAction e σ)) with hs | hs
    · exact hs
    · exfalso
      have hsign : σ d = ((Equiv.Perm.sign (cubicRootAction e σ) : ℤ) : L) * d :=
        cubic_vandermonde_automorphism_sign e σ
      have hneg : d = -d := by
        simpa only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
          using (h σ).symm.trans hsign
      apply mul_ne_zero (two_ne_zero : (2 : L) ≠ 0) hd
      simpa only [two_mul] using eq_neg_iff_add_eq_zero.mp hneg

theorem cubic_root_action_alternating_iff_square [CharZero K]
    (hmon : p.Monic) (hdegree : p.natDegree = 3) (hsep : p.Separable) :
    (cubicRootAction e).range ≤ alternatingGroup (Fin 3) ↔ IsSquare (cubicDiscriminant p) := by
  exact (cubic_root_action_alternating_iff_mem_base e hsep).trans
    (cubic_vandermonde_mem_base_iff_square e hmon hdegree hsep)

theorem exists_cubic_galois_equiv [CharZero K]
    (hmon : p.Monic) (hdegree : p.natDegree = 3) (hsep : p.Separable)
    (hirr : Irreducible p) (hns : ¬ IsSquare (cubicDiscriminant p)) :
    ∃ φ : (L ≃ₐ[K] L) ≃* Equiv.Perm (Fin 3), φ.toMonoidHom = cubicRootAction e := by
  let action := cubicRootAction e
  have hinj : Function.Injective action := (cubic_root_action_faithful_transitive e hirr).1
  have hnalt : ¬ action.range ≤ alternatingGroup (Fin 3) :=
    fun h => hns ((cubic_root_action_alternating_iff_square e hmon hdegree hsep).mp h)
  have hthree : 3 ∣ Nat.card action.range := by
    let iso : (L ≃ₐ[K] L) ≃* p.Gal := (IsSplittingField.algEquiv L p).autCongr
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr iso.toEquiv]
    simpa only [hdegree] using Gal.prime_degree_dvd_card hirr (hdegree.symm ▸ Nat.prime_three)
  let sign : action.range →* ℤˣ := Equiv.Perm.sign.comp action.range.subtype
  have hsign : Function.Surjective sign := by
    have hodd : ∃ g : action.range, sign g = -1 := by
      by_contra! h
      apply hnalt
      intro g hg
      exact Equiv.Perm.mem_alternatingGroup.mpr
        ((Int.units_eq_one_or (sign ⟨g, hg⟩)).resolve_right (h ⟨g, hg⟩))
    intro a
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨1, sign.map_one⟩
    · exact hodd
  have htwo : 2 ∣ Nat.card action.range := by
    simpa only [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] using
      Subgroup.card_dvd_of_surjective (f := sign) hsign
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hle : 6 ∣ Nat.card action.range :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have htop : action.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard]
    exact Nat.dvd_antisymm (hcard ▸ Subgroup.card_subgroup_dvd_card action.range) hle
  exact ⟨MulEquiv.ofBijective action ⟨hinj, action.range_eq_top.mp htop⟩, rfl⟩

omit e in
/-- The cubic criterion with the ordering obtained from the three distinct roots. -/
theorem cubic_galois_equiv_of_nonsquare [CharZero K]
    (hmon : p.Monic) (hdegree : p.natDegree = 3) (hsep : p.Separable)
    (hirr : Irreducible p) (hns : ¬ IsSquare (cubicDiscriminant p)) :
    ∃ (e : CubicRootOrdering p L) (φ : (L ≃ₐ[K] L) ≃* Equiv.Perm (Fin 3)),
      φ.toMonoidHom = cubicRootAction e := by
  obtain ⟨e⟩ := cubic_root_ordering p hdegree hsep (L := L)
  exact ⟨e, exists_cubic_galois_equiv e hmon hdegree hsep hirr hns⟩

end
end GaloisFormalization.IG
