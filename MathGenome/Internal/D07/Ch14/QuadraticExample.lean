import MathGenome.Internal.Specs.D07.Ch14.QuadraticExample
import MathGenome.Internal.D07.Ch11.LowDegreeIrreducible
import Mathlib.FieldTheory.SeparableClosure

/-!
Quadratic Galois groups, K07.14.quadratic_example (paper.tex:4248–4254).
Nonsquareness gives irreducibility and identifies the minimal polynomial,
hence degree two. Its derivative criterion gives separability; quadratic
normality then gives Galois. The automorphism count and prime degree classify
the group and intermediate fields. Normality supplies the conjugation taking
the generator to its negative, and its coordinate action follows from the
algebra laws. No properties of the ambient extension are assumed.
-/

universe u v

namespace D07.Ch14.QuadraticExample

open Polynomial IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

lemma quadratic_irreducible (a : Kˣ) (ha : ¬ IsSquare (a : K)) :
    Irreducible (X ^ 2 - C (a : K)) := by
  apply (Ch11.LowDegreeIrreducible.degree_two_or_three_iff_no_root K _
    (Or.inl (Polynomial.degree_X_pow_sub_C (by decide : 0 < 2) _))).mpr
  intro b hb
  apply ha
  refine ⟨b, ?_⟩
  have h : b ^ 2 = (a : K) := by
    simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hb
  simpa [pow_two] using h.symm

lemma quadratic_minpoly (a : Kˣ) (ha : ¬ IsSquare (a : K))
    (x : L) (hx : x ^ 2 = algebraMap K L (a : K)) :
    minpoly K x = X ^ 2 - C (a : K) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (quadratic_irreducible a ha)
  · simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hx
  · exact monic_X_pow_sub_C _ (by decide)

lemma quadratic_finrank (a : Kˣ) (ha : ¬ IsSquare (a : K))
    (x : L) (hx : x ^ 2 = algebraMap K L (a : K)) :
    Module.finrank K (adjoin K {x}) = 2 := by
  have hi : IsIntegral K x := ⟨X ^ 2 - C (a : K),
    monic_X_pow_sub_C _ (by decide), show aeval x (X ^ 2 - C (a : K)) = 0 by
      simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hx⟩
  rw [adjoin.finrank hi, quadratic_minpoly a ha x hx]
  exact natDegree_X_pow_sub_C

/-- Separability is proved for the generator, then passed to its generated field.
The normality instance applies only after degree two has been established. -/
lemma quadratic_galois (a : Kˣ) (hchar : (2 : K) ≠ 0)
    (ha : ¬ IsSquare (a : K)) (x : L)
    (hx : x ^ 2 = algebraMap K L (a : K)) :
    IsGalois K (adjoin K {x}) := by
  let : Algebra.IsQuadraticExtension K (adjoin K {x}) :=
    { finrank_eq_two' := quadratic_finrank a ha x hx }
  have hs : IsSeparable K x := by
    change (minpoly K x).Separable
    rw [quadratic_minpoly a ha x hx]
    exact separable_X_pow_sub_C (a : K) hchar a.ne_zero
  let : Algebra.IsSeparable K (adjoin K {x}) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K L).mpr (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hs)
  infer_instance

theorem quadratic_extension :
    Specs.D07.Ch14.QuadraticExample.QuadraticExtension.{u, v} := by
  intro K L _ _ _ a hchar ha x hx
  dsimp only
  let E := adjoin K ({x} : Set L)
  let r : E := ⟨x, mem_adjoin_simple_self K x⟩
  have hdegree : Module.finrank K E = 2 := quadratic_finrank a ha x hx
  let : Algebra.IsQuadraticExtension K E := { finrank_eq_two' := hdegree }
  let : FiniteDimensional K E := Module.finite_of_finrank_pos (by omega)
  let : IsGalois K E := quadratic_galois a hchar ha x hx
  have hcard : Nat.card (E ≃ₐ[K] E) = 2 :=
    (IsGalois.card_aut_eq_finrank K E).trans hdegree
  have hcyclic : Nonempty ((E ≃ₐ[K] E) ≃* Multiplicative (ZMod 2)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩
  have hend : ∀ M : IntermediateField K E, M = ⊥ ∨ M = ⊤ := by
    let := IntermediateField.isSimpleOrder_of_finrank_prime K E
      (by rw [hdegree]; exact Nat.prime_two)
    exact fun M => IsSimpleOrder.eq_bot_or_eq_top M
  have hr : r ^ 2 = algebraMap K E (a : K) := by
    apply Subtype.ext
    exact hx
  have hmin : minpoly K r = X ^ 2 - C (a : K) :=
    quadratic_minpoly a ha r hr
  have hroot : aeval (-r) (minpoly K r) = 0 := by
    rw [hmin]
    simpa only [map_sub, map_pow, aeval_X, aeval_C, neg_sq, sub_eq_zero] using hr
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (IsAlgebraic.of_finite K r) hroot
  have hr0 : r ≠ 0 := by
    intro h
    have hz : algebraMap K E (a : K) = 0 := by simpa [h] using hr.symm
    exact a.ne_zero ((map_eq_zero (algebraMap K E)).mp hz)
  have hσne : σ ≠ 1 := by
    intro h
    have he : r = -r := by simpa [h] using hσ
    have hz : (2 : E) * r = 0 := by
      rw [two_mul, add_eq_zero_iff_eq_neg]
      exact he
    have hc : (2 : E) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr hchar
    exact hr0 ((mul_eq_zero.mp hz).resolve_left hc)
  have hall : ∀ τ : E ≃ₐ[K] E, τ = 1 ∨ τ = σ := by
    obtain ⟨τ₀, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).mp hcard
    intro τ
    by_cases hτ : τ = 1
    · exact Or.inl hτ
    · exact Or.inr ((hunique τ hτ).trans (hunique σ hσne).symm)
  have hsquare : σ ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := σ)
    simpa only [hcard] using hh
  refine ⟨inferInstance, hdegree, inferInstance, hcyclic, hend,
    σ, hσne, hσ, hsquare, ?_, hall⟩
  intro b c
  change σ (algebraMap K E b + algebraMap K E c * r) =
    algebraMap K E b - algebraMap K E c * r
  simp [hσ, sub_eq_add_neg]

end D07.Ch14.QuadraticExample

