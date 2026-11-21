import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The translation argument for K07.20.artin_schreier (paper.tex:6026–6040).
The p translates give all roots, so one root generates a separable splitting
field. Its automorphism group embeds in the additive prime field. Lagrange
and the finite Galois degree formula force degree one or p; the first case
would give a preimage of a under u ↦ u^p-u. Equal monic degrees then identify
the original polynomial with the minimal polynomial.
-/

noncomputable section
universe u v
namespace D07.Ch20.ArtinSchreierTranslationDichotomy
open Polynomial
open scoped Classical
open Specs.D07.Ch20.ArtinSchreierTranslationDichotomy

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

omit [CharP K p] in
lemma polynomial_monic (a : K) : (asPolynomial K p a).Monic := by
  have hdeg : (X + C a : K[X]).degree < p := by
    rw [degree_add_C (by simp : 0 < (X : K[X]).degree), degree_X]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  simpa only [asPolynomial, sub_add_eq_sub_sub] using monic_X_pow_sub hdeg

omit [CharP K p] in
lemma polynomial_natDegree (a : K) : (asPolynomial K p a).natDegree = p := by
  rw [asPolynomial, natDegree_sub_C]
  exact FiniteField.X_pow_card_sub_X_natDegree_eq K (Fact.out : p.Prime).one_lt

omit [Fact p.Prime] in
lemma polynomial_separable (a : K) : (asPolynomial K p a).Separable := by
  rw [separable_def']
  refine ⟨0, -1, ?_⟩
  simp [asPolynomial, derivative_sub, derivative_pow]

omit [Fact p.Prime] [CharP K p] in
lemma eval_polynomial (a x : K) : (asPolynomial K p a).eval x = x ^ p - x - a := by
  simp [asPolynomial]

lemma cast_pow (c : ZMod p) : (ZMod.cast c : K) ^ p = ZMod.cast c := by
  change (ZMod.castHom (dvd_refl p) K c) ^ p = ZMod.castHom (dvd_refl p) K c
  rw [← map_pow]
  congr 1
  simp

lemma cast_injective : Function.Injective (ZMod.cast : ZMod p → K) :=
  (ZMod.castHom (dvd_refl p) K).injective

lemma exists_cast_of_pow_eq_self {x : K} (hx : x ^ p = x) :
    ∃ c : ZMod p, ZMod.cast c = x := by
  have hm := (Subfield.mem_bot_iff_pow_eq_self K p).mpr hx
  rw [← ZMod.fieldRange_castHom_eq_bot p] at hm
  exact hm

lemma translate_injective (θ : K) :
    Function.Injective (fun c : ZMod p => θ + (ZMod.cast c : K)) := by
  intro c d h
  exact cast_injective (add_left_cancel h)

lemma root_translation (a θ : K) (hθ : θ ^ p - θ = a) (x : K) :
    x ^ p - x = a ↔ ∃ c : ZMod p, x = θ + ZMod.cast c := by
  constructor
  · intro hx
    have hdiff : (x - θ) ^ p = x - θ := by
      rw [sub_pow_char]
      linear_combination hx - hθ
    obtain ⟨c, hc⟩ := exists_cast_of_pow_eq_self hdiff
    exact ⟨c, by rw [hc]; ring⟩
  · rintro ⟨c, rfl⟩
    rw [add_pow_char, cast_pow]
    linear_combination hθ

lemma polynomial_roots (a θ : K) (hθ : θ ^ p - θ = a) :
    (asPolynomial K p a).roots =
      (Finset.univ.image fun c : ZMod p => θ + (ZMod.cast c : K)).val := by
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    rw [eval_polynomial, sub_eq_zero]
    exact (root_translation a θ hθ _).mpr ⟨c, rfl⟩
  · rw [Finset.card_image_of_injective _ (translate_injective θ), Finset.card_univ,
      ZMod.card, polynomial_natDegree]
  · exact (polynomial_monic a).ne_zero

lemma polynomial_factorization (a θ : K) (hθ : θ ^ p - θ = a) :
    asPolynomial K p a = ∏ c : ZMod p, (X - C (θ + ZMod.cast c)) := by
  have hr := polynomial_roots a θ hθ
  have hc : (asPolynomial K p a).roots.card = (asPolynomial K p a).natDegree := by
    rw [hr, ← Finset.card_def, Finset.card_image_of_injective _ (translate_injective θ),
      Finset.card_univ, ZMod.card, polynomial_natDegree]
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (polynomial_monic a) hc, hr]
  change (∏ x ∈ Finset.univ.image (fun c : ZMod p => θ + (ZMod.cast c : K)),
    (X - C x : K[X])) = _
  exact Finset.prod_image (fun c _ d _ h => translate_injective θ h)

omit [Fact p.Prime] [CharP K p] in
lemma polynomial_map {L : Type v} [Field L] [Algebra K L] (a : K) :
    (asPolynomial K p a).map (algebraMap K L) = asPolynomial L p (algebraMap K L a) := by
  simp [asPolynomial]

omit [CharP K p] in
lemma map_cast {L : Type v} [Field L] (f : K →+* L) (c : ZMod p) :
    f (ZMod.cast c) = ZMod.cast c := by
  simp only [ZMod.cast_eq_val, map_natCast]

lemma roots_adjoin_eq {L : Type v} [Field L] [Algebra K L]
    (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a) :
    IntermediateField.adjoin K ((asPolynomial K p a).rootSet L) =
      IntermediateField.adjoin K {θ} := by
  let : CharP L p := charP_of_injective_algebraMap' K p
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x ^ p - x = algebraMap K L a := by
      have := aeval_eq_zero_of_mem_rootSet hx
      simpa [asPolynomial, sub_eq_zero] using this
    obtain ⟨c, rfl⟩ := (root_translation _ θ hθ x).mp hx'
    apply IntermediateField.add_mem
    · exact IntermediateField.mem_adjoin_simple_self K θ
    · rw [← map_cast (algebraMap K L) c]
      exact IntermediateField.algebraMap_mem _ _
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x (rfl : x = θ)
    apply IntermediateField.subset_adjoin
    apply (polynomial_monic a).mem_rootSet.mpr
    simpa [asPolynomial, sub_eq_zero] using hθ

lemma root_splittingField {L : Type v} [Field L] [Algebra K L]
    (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a) :
    Polynomial.IsSplittingField K (IntermediateField.adjoin K {θ}) (asPolynomial K p a) := by
  let : CharP L p := charP_of_injective_algebraMap' K p
  have hsplit : ((asPolynomial K p a).map (algebraMap K L)).Splits := by
    rw [polynomial_map, polynomial_factorization _ θ hθ]
    exact Splits.prod fun c _ => Splits.X_sub_C _
  rw [← roots_adjoin_eq a θ hθ]
  exact IntermediateField.adjoin_rootSet_isSplittingField hsplit

lemma splittingField_adjoin_root {L : Type v} [Field L] [Algebra K L]
    (a : K) [Polynomial.IsSplittingField K L (asPolynomial K p a)]
    (θ : L) (hθ : θ ^ p - θ = algebraMap K L a) :
    IntermediateField.adjoin K {θ} = ⊤ := by
  rw [← roots_adjoin_eq a θ hθ]
  exact (isSplittingField_iff_intermediateField.mp inferInstance).2

section Automorphisms
variable {L : Type v} [Field L] [Algebra K L] [CharP L p]

omit [Fact p.Prime] [CharP K p] [CharP L p] in
lemma automorphism_root (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a)
    (σ : L ≃ₐ[K] L) : (σ θ) ^ p - σ θ = algebraMap K L a := by
  simpa only [map_sub, map_pow, AlgEquiv.commutes] using congrArg σ hθ

def translationValue (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a)
    (σ : L ≃ₐ[K] L) : ZMod p :=
  ((root_translation _ θ hθ (σ θ)).mp (automorphism_root a θ hθ σ)).choose

lemma translationValue_spec (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a)
    (σ : L ≃ₐ[K] L) : (ZMod.cast (translationValue a θ hθ σ) : L) = σ θ - θ := by
  have h := ((root_translation _ θ hθ (σ θ)).mp (automorphism_root a θ hθ σ)).choose_spec
  change σ θ = θ + ZMod.cast (translationValue a θ hθ σ) at h
  linear_combination -h

def translationHom (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a) :
    (L ≃ₐ[K] L) →* Multiplicative (ZMod p) where
  toFun σ := Multiplicative.ofAdd (translationValue a θ hθ σ)
  map_one' := by
    change translationValue a θ hθ 1 = 0
    apply cast_injective (K := L)
    simpa using translationValue_spec a θ hθ 1
  map_mul' σ τ := by
    change translationValue a θ hθ (σ * τ) =
      translationValue a θ hθ σ + translationValue a θ hθ τ
    apply cast_injective (K := L)
    rw [ZMod.cast_add (dvd_refl p)]
    have hτ := congrArg σ (translationValue_spec a θ hθ τ)
    rw [map_sub] at hτ
    have hc : σ (ZMod.cast (translationValue a θ hθ τ)) =
        (ZMod.cast (translationValue a θ hθ τ) : L) := map_cast σ.toRingHom _
    rw [hc] at hτ
    have hσ := translationValue_spec a θ hθ σ
    have hστ := translationValue_spec a θ hθ (σ * τ)
    change ZMod.cast (translationValue a θ hθ (σ * τ)) = σ (τ θ) - θ at hστ
    linear_combination hστ - hτ - hσ

lemma translationHom_injective (a : K) (θ : L)
    (hθ : θ ^ p - θ = algebraMap K L a)
    (hgen : IntermediateField.adjoin K {θ} = ⊤) :
    Function.Injective (translationHom a θ hθ) := by
  intro σ τ heq
  have hv : translationValue a θ hθ σ = translationValue a θ hθ τ :=
    congrArg Multiplicative.toAdd heq
  have hθeq : σ θ = τ θ := by
    have hσ := translationValue_spec a θ hθ σ
    have hτ := translationValue_spec a θ hθ τ
    rw [hv] at hσ
    linear_combination hτ - hσ
  have hint : IsIntegral K θ := by
    refine ⟨asPolynomial K p a, polynomial_monic a, ?_⟩
    simpa [asPolynomial, sub_eq_zero] using hθ
  have hgen' : Algebra.adjoin K {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hgen]
    rfl
  have heq' : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen'
    rintro x (rfl : x = θ)
    exact hθeq
  ext x
  exact congrArg (fun f : L →ₐ[K] L => f x) heq'

end Automorphisms

lemma root_integral {L : Type v} [Field L] [Algebra K L]
    (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a) : IsIntegral K θ := by
  refine ⟨asPolynomial K p a, polynomial_monic a, ?_⟩
  simpa [asPolynomial, sub_eq_zero] using hθ

lemma root_extension_finrank {L : Type v} [Field L] [Algebra K L]
    (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a)
    (ha : ¬ ∃ u : K, u ^ p - u = a) :
    Module.finrank K (IntermediateField.adjoin K {θ}) = p := by
  let E := IntermediateField.adjoin K {θ}
  let : CharP E p := charP_of_injective_algebraMap' K p
  let : Polynomial.IsSplittingField K E (asPolynomial K p a) := root_splittingField a θ hθ
  let : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E (asPolynomial K p a)
  let : IsGalois K E := IsGalois.of_separable_splitting_field (polynomial_separable a)
  let η : E := ⟨θ, IntermediateField.mem_adjoin_simple_self K θ⟩
  have hη : η ^ p - η = algebraMap K E a := by
    apply Subtype.val_injective
    exact hθ
  have hgen : IntermediateField.adjoin K {η} = ⊤ := splittingField_adjoin_root a η hη
  have hcard : Nat.card (E ≃ₐ[K] E) ∣ p := by
    have hd := Subgroup.card_dvd_of_injective (translationHom a η hη)
      (translationHom_injective a η hη hgen)
    change Nat.card (E ≃ₐ[K] E) ∣ Nat.card (ZMod p) at hd
    simpa only [Nat.card_zmod] using hd
  have hd : Module.finrank K E ∣ p := by
    rwa [IsGalois.card_aut_eq_finrank] at hcard
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with hone | hp
  · have hmem : θ ∈ (⊥ : IntermediateField K L) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hone
    obtain ⟨u, hu⟩ := hmem
    change algebraMap K L u = θ at hu
    apply False.elim
    apply ha
    refine ⟨u, (algebraMap K L).injective ?_⟩
    rw [map_sub, map_pow, hu]
    exact hθ
  · exact hp

lemma root_minpoly {L : Type v} [Field L] [Algebra K L]
    (a : K) (θ : L) (hθ : θ ^ p - θ = algebraMap K L a)
    (ha : ¬ ∃ u : K, u ^ p - u = a) : minpoly K θ = asPolynomial K p a := by
  have hint := root_integral a θ hθ
  have heval : aeval θ (asPolynomial K p a) = 0 := by
    simpa [asPolynomial, sub_eq_zero] using hθ
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (polynomial_monic a)
    (minpoly.dvd K θ heval)
  rw [polynomial_natDegree, ← IntermediateField.adjoin.finrank hint,
    root_extension_finrank a θ hθ ha]

/-- The polynomial always has degree p and derivative -1. -/
theorem degree_and_separability : DegreeAndSeparability.{u} := by
  intro K _ p _ _ a
  exact ⟨polynomial_monic a, polynomial_natDegree a, polynomial_separable a⟩

theorem translated_roots : TranslatedRoots.{u} := by
  intro K _ p _ _ a θ hθ
  exact ⟨translate_injective θ, root_translation a θ hθ, polynomial_factorization a θ hθ⟩

theorem root_generates_splitting_field : RootGeneratesSplittingField.{u, v} := by
  intro K L _ _ _ p _ _ a θ hθ
  exact root_splittingField a θ hθ

theorem translation_embedding : TranslationEmbedding.{u, v} := by
  intro K L _ _ _ p _ _ a _ θ hθ
  let : CharP L p := charP_of_injective_algebraMap' K p
  have hgen := splittingField_adjoin_root a θ hθ
  refine ⟨hgen, translationHom a θ hθ, translationHom_injective a θ hθ hgen, ?_⟩
  exact translationValue_spec a θ hθ

lemma polynomial_degree_ne_zero (a : K) : (asPolynomial K p a).degree ≠ 0 := by
  rw [degree_eq_natDegree (polynomial_monic a).ne_zero, polynomial_natDegree]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem splitting_field_roots : SplittingFieldRoots.{u, v} := by
  intro K L _ _ _ p _ _ a _
  let : CharP L p := charP_of_injective_algebraMap' K p
  have hs := Polynomial.IsSplittingField.splits L (asPolynomial K p a)
  rw [polynomial_map] at hs
  obtain ⟨θ, hθ⟩ := hs.exists_eval_eq_zero (polynomial_degree_ne_zero _)
  have hroot : θ ^ p - θ = algebraMap K L a := by
    simpa [eval_polynomial, sub_eq_zero] using hθ
  refine ⟨θ, hroot, translate_injective θ, ?_, ?_⟩
  · rw [polynomial_map]
    exact polynomial_factorization _ θ hroot
  · rw [polynomial_map, ← hs.natDegree_eq_card_roots, polynomial_natDegree]

theorem splits_iff_parameter_in_image : SplitsIffParameterInImage.{u} := by
  intro K _ p _ _ a
  constructor
  · intro hs
    obtain ⟨u, hu⟩ := hs.exists_eval_eq_zero (polynomial_degree_ne_zero a)
    exact ⟨u, by simpa [eval_polynomial, sub_eq_zero] using hu⟩
  · rintro ⟨u, hu⟩
    rw [polynomial_factorization a u hu]
    exact Splits.prod fun c _ => Splits.X_sub_C _

theorem irreducible_of_parameter_not_in_image : IrreducibleOfParameterNotInImage.{u} := by
  intro K _ p _ _ a ha
  let L := (asPolynomial K p a).SplittingField
  let : CharP L p := charP_of_injective_algebraMap' K p
  have hs := Polynomial.IsSplittingField.splits L (asPolynomial K p a)
  rw [polynomial_map] at hs
  obtain ⟨θ, hθ⟩ := hs.exists_eval_eq_zero (polynomial_degree_ne_zero _)
  have hroot : θ ^ p - θ = algebraMap K L a := by
    simpa [eval_polynomial, sub_eq_zero] using hθ
  rw [← root_minpoly a θ hroot ha]
  exact minpoly.irreducible (root_integral a θ hroot)

theorem nontrivial_root_extension : NontrivialRootExtension.{u, v} := by
  intro K L _ _ _ p _ _ a θ ha hθ
  let E := IntermediateField.adjoin K {θ}
  let : Polynomial.IsSplittingField K E (asPolynomial K p a) := root_splittingField a θ hθ
  let : FiniteDimensional K E := Polynomial.IsSplittingField.finiteDimensional E (asPolynomial K p a)
  let : IsGalois K E := IsGalois.of_separable_splitting_field (polynomial_separable a)
  have hdegree : Module.finrank K E = p := root_extension_finrank a θ hθ ha
  refine ⟨inferInstance, inferInstance, hdegree, ?_, root_minpoly a θ hθ ha⟩
  exact isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K E).trans hdegree)

end D07.Ch20.ArtinSchreierTranslationDichotomy
