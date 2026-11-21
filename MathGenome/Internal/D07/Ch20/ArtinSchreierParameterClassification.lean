import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierParameterClassification
import MathGenome.Internal.D07.Ch20.ArtinSchreierTranslationDichotomy
import Mathlib.FieldTheory.Normal.Basic

/-! The parameter classification from K07.20.artin_schreier.
A generator translating θ by 1 translates η by some c in F_p. Its fixed
field is K, so η-cθ is a base scalar. Nontriviality of b forces c ≠ 0.
Conversely, the affine change of root generates the same intermediate field.
Normality identifies isomorphic root fields in their common overfield. -/

noncomputable section
universe u v
namespace D07.Ch20.ArtinSchreierParameterClassification
open Polynomial
open scoped Classical
open Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
open Specs.D07.Ch20.ArtinSchreierParameterClassification
open D07.Ch20.ArtinSchreierTranslationDichotomy

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

omit [CharP K p] in
/-- In a Galois extension of prime degree, one nonidentity automorphism
already has the base as its fixed field. -/
lemma fixed_by_generator {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hd : Module.finrank K L = p) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (x : L) (hx : σ x = x) : ∃ u : K, algebraMap K L u = x := by
  apply (IsGalois.mem_bot_iff_fixed x).mpr
  intro τ
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) x := by
    apply Subgroup.zpowers_le.mpr
    exact hx
  exact hle (mem_zpowers_of_prime_card
    ((IsGalois.card_aut_eq_finrank K L).trans hd) hσ)

/-- The affine description of every nontrivial Artin-Schreier root in
a root field. This is the key necessity argument. -/
lemma affine_root {L : Type v} [Field L] [Algebra K L]
    (a b : K) [Polynomial.IsSplittingField K L (asPolynomial K p a)]
    (θ η : L) (ha : ¬ ∃ u : K, u ^ p - u = a)
    (hb : ¬ ∃ u : K, u ^ p - u = b)
    (hθ : θ ^ p - θ = algebraMap K L a)
    (hη : η ^ p - η = algebraMap K L b) :
    ∃ (c : ZMod p) (u : K), c ≠ 0 ∧
      η = ZMod.cast c * θ + algebraMap K L u ∧
      b = ZMod.cast c * a + (u ^ p - u) := by
  let : CharP L p := charP_of_injective_algebraMap' K p
  let : FiniteDimensional K L :=
    Polynomial.IsSplittingField.finiteDimensional L (asPolynomial K p a)
  let : IsGalois K L :=
    IsGalois.of_separable_splitting_field (polynomial_separable a)
  have hgen := splittingField_adjoin_root a θ hθ
  have hd : Module.finrank K L = p := by
    have h := root_extension_finrank a θ hθ ha
    rw [hgen, IntermediateField.finrank_top'] at h
    exact h
  have heval : aeval (θ + 1) (minpoly K θ) = 0 := by
    rw [root_minpoly a θ hθ ha]
    simp only [asPolynomial, map_sub, map_pow, aeval_X, aeval_C]
    rw [add_pow_char, one_pow]
    linear_combination hθ
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (root_integral a θ hθ).isAlgebraic heval
  have hσne : σ ≠ 1 := by
    intro h
    simp [h] at hσ
  obtain ⟨c, hc⟩ := (root_translation _ η hη (σ η)).mp
    (automorphism_root b η hη σ)
  have hfixed : σ (η - ZMod.cast c * θ) = η - ZMod.cast c * θ := by
    have hcast : σ (ZMod.cast c) = (ZMod.cast c : L) := map_cast σ.toRingHom c
    rw [map_sub, map_mul, hcast, hσ, hc]
    ring
  obtain ⟨u, hu⟩ := fixed_by_generator hd σ hσne _ hfixed
  have hcu : η = ZMod.cast c * θ + algebraMap K L u := by
    linear_combination -hu
  have hc0 : c ≠ 0 := by
    intro h
    have hηfixed : σ η = η := by simpa [h] using hc
    obtain ⟨v, hv⟩ := fixed_by_generator hd σ hσne η hηfixed
    apply hb
    refine ⟨v, (algebraMap K L).injective ?_⟩
    rw [map_sub, map_pow, hv]
    exact hη
  refine ⟨c, u, hc0, hcu, (algebraMap K L).injective ?_⟩
  rw [map_add, map_mul, map_cast (algebraMap K L) c, map_sub, map_pow]
  rw [← hη, hcu, add_pow_char, mul_pow, cast_pow]
  linear_combination (ZMod.cast c : L) * hθ

/-- Necessity for equality of the actual intermediate fields. -/
lemma parameter_of_equal_root_fields {Ω : Type v} [Field Ω] [Algebra K Ω]
    (a b : K) (θ η : Ω) (ha : ¬ ∃ u : K, u ^ p - u = a)
    (hb : ¬ ∃ u : K, u ^ p - u = b)
    (hθ : θ ^ p - θ = algebraMap K Ω a)
    (hη : η ^ p - η = algebraMap K Ω b)
    (hE : IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η}) :
    ∃ (c : ZMod p) (u : K), c ≠ 0 ∧ b = ZMod.cast c * a + (u ^ p - u) := by
  let E := IntermediateField.adjoin K {θ}
  let : Polynomial.IsSplittingField K E (asPolynomial K p a) :=
    root_splittingField a θ hθ
  let θ' : E := ⟨θ, IntermediateField.mem_adjoin_simple_self K θ⟩
  let η' : E := ⟨η, by
    change η ∈ IntermediateField.adjoin K {θ}
    rw [hE]
    exact IntermediateField.mem_adjoin_simple_self K η⟩
  have hθ' : θ' ^ p - θ' = algebraMap K E a := by
    apply Subtype.val_injective
    exact hθ
  have hη' : η' ^ p - η' = algebraMap K E b := by
    apply Subtype.val_injective
    exact hη
  obtain ⟨c, u, hc, _, hpar⟩ := affine_root a b θ' η' ha hb hθ' hη'
  exact ⟨c, u, hc, hpar⟩

/-- Sufficiency includes the invertible scaling of the generator. -/
lemma equal_root_fields_of_parameter {Ω : Type v} [Field Ω] [Algebra K Ω]
    (a b : K) (θ η : Ω)
    (hθ : θ ^ p - θ = algebraMap K Ω a)
    (hη : η ^ p - η = algebraMap K Ω b)
    (c : ZMod p) (u : K) (hc : c ≠ 0)
    (hpar : b = ZMod.cast c * a + (u ^ p - u)) :
    IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η} := by
  let : CharP Ω p := charP_of_injective_algebraMap' K p
  let ζ : Ω := ZMod.cast c * θ + algebraMap K Ω u
  have hζ : ζ ^ p - ζ = algebraMap K Ω b := by
    dsimp [ζ]
    rw [add_pow_char, mul_pow, cast_pow, hpar, map_add, map_mul,
      map_cast (algebraMap K Ω) c, map_sub, map_pow]
    linear_combination (ZMod.cast c : Ω) * hθ
  have hroots : IntermediateField.adjoin K {ζ} = IntermediateField.adjoin K {η} :=
    (roots_adjoin_eq b ζ hζ).symm.trans (roots_adjoin_eq b η hη)
  have haff : IntermediateField.adjoin K {ζ} = IntermediateField.adjoin K {θ} := by
    dsimp [ζ]
    rw [IntermediateField.adjoin_simple_add_algebraMap, mul_comm,
      ← map_cast (algebraMap K Ω) c]
    apply IntermediateField.adjoin_simple_mul_algebraMap
    intro h
    exact hc (cast_injective (h.trans (by simp)))
  exact haff.symm.trans hroots

/-- Full equality classification, uniformly for all choices of roots. -/
theorem root_fields_equal_iff : RootFieldsEqualIff.{u, v} := by
  intro K Ω _ _ _ p _ _ a b θ η ha hb hθ hη
  constructor
  · exact parameter_of_equal_root_fields a b θ η ha hb hθ hη
  · rintro ⟨c, u, hc, hpar⟩
    exact equal_root_fields_of_parameter a b θ η hθ hη c u hc hpar

/-- Normal root fields have the same image under every K-embedding,
so a K-isomorphism forces equality in the common overfield. -/
theorem root_fields_isomorphic_iff_equal : RootFieldsIsomorphicIffEqual.{u, v} := by
  intro K Ω _ _ _ p _ _ a b θ η _ha _hb hθ _hη
  let E := IntermediateField.adjoin K {θ}
  let F := IntermediateField.adjoin K {η}
  let : Polynomial.IsSplittingField K E (asPolynomial K p a) :=
    root_splittingField a θ hθ
  let : Normal K E := Normal.of_isSplittingField (asPolynomial K p a)
  constructor
  · rintro ⟨e⟩
    let f : E →ₐ[K] Ω := F.val.comp e.toAlgHom
    have hn : f.fieldRange = E := AlgHom.fieldRange_of_normal f
    have hr : f.fieldRange = F := by
      ext x
      rw [AlgHom.mem_fieldRange]
      constructor
      · rintro ⟨y, rfl⟩
        exact (e y).property
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        dsimp [f]
        simp
    exact hn.symm.trans hr
  · intro h
    exact ⟨IntermediateField.equivOfEq h⟩

/-- Existence and the full classification in one chosen algebraic closure. -/
theorem common_closure_classification : CommonClosureClassification.{u} := by
  intro K _ p _ _ a b ha hb
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K)
    (asPolynomial K p a) (polynomial_degree_ne_zero a)
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K)
    (asPolynomial K p b) (polynomial_degree_ne_zero b)
  have hθ' : θ ^ p - θ = algebraMap K (AlgebraicClosure K) a := by
    simpa [asPolynomial, sub_eq_zero] using hθ
  have hη' : η ^ p - η = algebraMap K (AlgebraicClosure K) b := by
    simpa [asPolynomial, sub_eq_zero] using hη
  have hi := root_fields_isomorphic_iff_equal K (AlgebraicClosure K) p a b θ η
    ha hb hθ' hη'
  have hp := root_fields_equal_iff K (AlgebraicClosure K) p a b θ η ha hb hθ' hη'
  exact ⟨θ, η, hθ', hη', hi.symm, hi.trans hp⟩

end D07.Ch20.ArtinSchreierParameterClassification
