import MathGenome.Internal.Specs.D07.Ch20.FiniteArtinSchreier
import MathGenome.Internal.D07.Ch20.ArtinSchreier
import MathGenome.Internal.D07.Ch20.Hilbert90Additive
import MathGenome.Internal.D07.Ch13.Uniqueness
import MathGenome.Internal.D07.Ch13.FrobeniusRoots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
The absolute trace-zero set is the image of x ↦ x^p-x by additive Hilbert 90.
The general Artin–Schreier dichotomy then supplies the criterion and cyclic
extension. Finite-field uniqueness gives equality with the canonical embedded
F_(q^p). The examples include the boundary at higher p-powers, with the
quartic's two quadratic factors and its root degrees over F_2 and F_4.
-/

noncomputable section
universe u v
namespace D07.Ch20.FiniteArtinSchreier
open Polynomial
open Specs.D07.Ch20.FiniteArtinSchreier
open Specs.D07.Ch20.ArtinSchreierTranslationDichotomy (asPolynomial)

lemma trace_zero_iff (K : Type u) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (a : K) :
    Algebra.trace (ZMod p) K a = 0 ↔ ∃ b : K, b ^ p - b = a := by
  simpa only [Nat.card_zmod, eq_comm] using
    Hilbert90Additive.finite_field_additive (ZMod p) K a

theorem absolute_trace_criterion : AbsoluteTraceCriterion.{u} := by
  intro K _ _ p _ _ _ a
  constructor
  · intro hi ht
    obtain ⟨b, hb⟩ := (trace_zero_iff K p a).mp ht
    have hd := ArtinSchreierTranslationDichotomy.polynomial_natDegree (K := K) (p := p) a
    have hr : (asPolynomial K p a).IsRoot b := by
      simpa [asPolynomial, sub_eq_zero] using hb
    have := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hr)
    rw [hd] at this
    exact (Fact.out : p.Prime).ne_one this
  · intro ht
    exact ArtinSchreierTranslationDichotomy.irreducible_of_parameter_not_in_image K p a
      (fun h => ht ((trace_zero_iff K p a).mpr h))

theorem trace_zero_splitting : TraceZeroSplitting.{u} := by
  intro K _ _ p _ _ _ a ht
  obtain ⟨θ, hθ⟩ := (trace_zero_iff K p a).mp ht
  obtain ⟨hinj, _, hprod⟩ := ArtinSchreierTranslationDichotomy.translated_roots K p a θ hθ
  have hs := ArtinSchreier.splits_iff K p a |>.mpr ⟨θ, hθ⟩
  exact ⟨θ, hθ, hinj, hprod, hs.natDegree_eq_card_roots.symm.trans
    (ArtinSchreierTranslationDichotomy.polynomial_natDegree a)⟩

theorem splitting_field_description : SplittingFieldDescription.{u,v} := by
  intro K L _ _ _ _ p _ _ _ a _ ht
  let : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L (asPolynomial K p a)
  let : Finite L := Finite.of_injective (Module.finBasis K L).equivFun
    (Module.finBasis K L).equivFun.injective
  obtain ⟨θ, hθ, _⟩ := ArtinSchreierTranslationDichotomy.splitting_field_roots K L p a
  have ha : ¬ ∃ b : K, b ^ p - b = a := fun h => ht ((trace_zero_iff K p a).mpr h)
  obtain ⟨_, _, hd, _, _⟩ := ArtinSchreier.root_extension K L p a θ ha hθ
  have hgen := ArtinSchreierTranslationDichotomy.splittingField_adjoin_root a θ hθ
  rw [hgen, IntermediateField.finrank_top'] at hd
  let : IsGalois K L := IsGalois.of_separable_splitting_field
    (ArtinSchreierTranslationDichotomy.polynomial_separable a)
  refine ⟨inferInstance, inferInstance, hd, ?_, inferInstance, ?_, ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := K), hd]
  · exact isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hd)
  · exact (IsGalois.card_aut_eq_finrank K L).trans hd

theorem embedded_splitting_field : EmbeddedSplittingField.{u,v} := by
  intro K Ω _ _ _ _ _ _ p _ _ _ a ht
  let E := IntermediateField.adjoin K ((asPolynomial K p a).rootSet Ω)
  let : Polynomial.IsSplittingField K E (asPolynomial K p a) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  obtain ⟨hfin, _, _, hcard, _⟩ := splitting_field_description K E p a ht
  let := hfin
  obtain ⟨hF, hcardF, _⟩ := D07.Ch13.Existence.embedded_existence K Ω (Nat.card K) p rfl
    (Fact.out : p.Prime).one_lt.le
  exact D07.Ch13.Uniqueness.embedded_field_eq_root_field K Ω (Nat.card K) p rfl E
    hcard hF hcardF

lemma four_finrank (K : Type*) [Field K] [Finite K] [CharP K 2]
    [Algebra (ZMod 2) K] (hcard : Nat.card K = 4) :
    Module.finrank (ZMod 2) K = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) K = Nat.card K := by
      simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)).symm
    _ = 2 ^ 2 := by norm_num [hcard]

lemma quad_as (K : Type*) [Field K] [CharP K 2] :
    asPolynomial K 2 1 = (X ^ 2 + X + 1 : K[X]) := by
  simp only [asPolynomial, CharTwo.sub_eq_add, C_1]

lemma four_trace_one (K : Type*) [Field K] [Finite K] [CharP K 2]
    [Algebra (ZMod 2) K] (hcard : Nat.card K = 4) :
    Algebra.trace (ZMod 2) K 1 = 0 := by
  have h := Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2)
  norm_num [four_finrank K hcard] at h ⊢
  exact h

theorem prime_field_example : PrimeFieldExample := by
  have ht : Algebra.trace (ZMod 2) (ZMod 2) 1 = 1 := by simp
  refine ⟨ht, ?_⟩
  rw [← quad_as]
  exact (absolute_trace_criterion (ZMod 2) 2 1).mpr (by rw [ht]; exact one_ne_zero)

theorem four_element_example : FourElementExample := by
  intro K _ _ _ _ hcard
  have ht := four_trace_one K hcard
  obtain ⟨θ, hθ, _, hprod, hroots⟩ := trace_zero_splitting K 2 1 ht
  refine ⟨ht, ?_, ?_⟩
  · rw [← quad_as]
    exact ArtinSchreier.splits_iff K 2 1 |>.mpr ⟨θ, hθ⟩
  · rwa [quad_as] at hroots

/-- Choose ω with ω² + ω = 1. Its trace and that of ω+1 are both one,
so the two factors X²+X+ω and X²+X+ω+1 are irreducible. -/
theorem higher_power_counterexample : HigherPowerCounterexample := by
  intro K _ _ _ _ hcard
  have hpow (x : K) : x ^ 4 = x := by
    let := Fintype.ofFinite K
    simpa only [← Nat.card_eq_fintype_card, hcard] using FiniteField.pow_card x
  refine ⟨hpow, ?_, ?_⟩
  · intro x
    simp [hpow]
  · obtain ⟨θ, hθ, _⟩ := trace_zero_splitting K 2 1 (four_trace_one K hcard)
    have ht : Algebra.trace (ZMod 2) K θ = 1 := by
      apply (algebraMap (ZMod 2) K).injective
      rw [FiniteField.algebraMap_trace_eq_sum_pow, four_finrank K hcard, Nat.card_zmod]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, map_one]
      rw [CharTwo.sub_eq_add] at hθ
      linear_combination hθ
    have ht' : Algebra.trace (ZMod 2) K (θ + 1) = 1 := by
      rw [map_add, ht, four_trace_one K hcard, add_zero]
    refine ⟨asPolynomial K 2 θ, asPolynomial K 2 (θ + 1),
      ArtinSchreierTranslationDichotomy.polynomial_monic _,
      ArtinSchreierTranslationDichotomy.polynomial_monic _,
      ArtinSchreierTranslationDichotomy.polynomial_natDegree _,
      ArtinSchreierTranslationDichotomy.polynomial_natDegree _,
      (absolute_trace_criterion K 2 θ).mpr (by rw [ht]; exact one_ne_zero),
      (absolute_trace_criterion K 2 (θ + 1)).mpr (by rw [ht']; exact one_ne_zero), ?_, ?_⟩
    · intro he
      have hc := congrArg (fun f : K[X] => f.coeff 0) he
      simp [asPolynomial] at hc
    · rw [asPolynomial, asPolynomial]
      simp only [CharTwo.sub_eq_add, map_add, C_1]
      have hC := congrArg (C : K →+* K[X]) hθ
      simp only [map_add, map_pow, map_one, CharTwo.sub_eq_add] at hC
      linear_combination (norm := ring_nf) -hC
      simp [show (2 : K[X]) = 0 from CharP.cast_eq_zero _ 2]

lemma quartic_monic : (X ^ 4 + X + 1 : (ZMod 2)[X]).Monic := by
  monicity; norm_num
lemma quartic_degree : (X ^ 4 + X + 1 : (ZMod 2)[X]).natDegree = 4 := by
  compute_degree; norm_num

lemma quadratic_shape {F : Type*} [Field F] (g : F[X]) (hg : g.Monic)
    (hd : g.natDegree = 2) :
    g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  have hcoeff : g.coeff 2 = 1 := hd ▸ hg.coeff_natDegree
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [hcoeff]
  · have hn' : g.natDegree < n := by omega
    simp [coeff_X, coeff_C, coeff_eq_zero_of_natDegree_lt hn', show n ≠ 0 by omega,
      show 1 ≠ n by omega, show n ≠ 2 by omega]

/-- A reducible monic quartic has a monic divisor of degree one or two.
Enumerate the latter over F_2; the only rootless quadratic leaves remainder one. -/
theorem quartic_over_prime_field : QuarticOverPrimeField := by
  have hno (x : ZMod 2) : ¬ (X ^ 4 + X + 1 : (ZMod 2)[X]).IsRoot x := by
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide
  have hroot (g : (ZMod 2)[X]) (hd : g ∣ X ^ 4 + X + 1) (x : ZMod 2)
      (hx : g.IsRoot x) : False := hno x (hx.dvd hd)
  apply (quartic_monic.irreducible_iff_lt_natDegree_lt ?_).mpr
  · intro g hg hd hdiv
    rw [quartic_degree] at hd
    have hdeg : g.natDegree = 1 ∨ g.natDegree = 2 := by
      simp only [Finset.mem_Ioc] at hd
      omega
    rcases hdeg with h1 | h2
    · rw [hg.eq_X_add_C h1] at hdiv
      exact hroot _ hdiv (-g.coeff 0) (by simp [IsRoot, CharTwo.add_self_eq_zero])
    · rw [quadratic_shape g hg h2] at hdiv
      generalize g.coeff 0 = c at hdiv
      generalize g.coeff 1 = b at hdiv
      have heval (x : ZMod 2) : (X ^ 2 + C b * X + C c : (ZMod 2)[X]).eval x = x ^ 2 + b * x + c := by simp
      fin_cases b <;> fin_cases c
      · exact hroot _ hdiv 0 (by rw [IsRoot, heval]; decide)
      · exact hroot _ hdiv 1 (by rw [IsRoot, heval]; decide)
      · exact hroot _ hdiv 0 (by rw [IsRoot, heval]; decide)
      · have hid : (X ^ 4 + X + 1 : (ZMod 2)[X]) =
            (X ^ 2 + C 1 * X + C 1) * (X ^ 2 + X) + 1 := by
          ring_nf
          simp [add_assoc, CharTwo.add_self_eq_zero, show (2 : (ZMod 2)[X]) = 0 from CharP.cast_eq_zero _ 2]
        change (X ^ 2 + C 1 * X + C 1 : (ZMod 2)[X]) ∣ _ at hdiv
        simp only [C_1, one_mul] at hdiv
        have hone : (X ^ 2 + X + 1 : (ZMod 2)[X]) ∣ 1 := by
          apply (dvd_add_right (dvd_mul_right (X ^ 2 + X + 1) (X ^ 2 + X))).mp
          rw [show (X ^ 2 + X + 1 : (ZMod 2)[X]) * (X ^ 2 + X) + 1 = X ^ 4 + X + 1 by simpa using hid.symm]
          exact hdiv
        have hle := natDegree_le_of_dvd hone (by simp : (1 : (ZMod 2)[X]) ≠ 0)
        have hq : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by
          compute_degree; norm_num
        rw [hq, natDegree_one] at hle
        omega
  · intro he
    have := congrArg natDegree he
    rw [quartic_degree, natDegree_one] at this
    omega

theorem quartic_root_degrees : QuarticRootDegrees := by
  intro K L _ _ _ _ _ _ _ _ hcard θ hθ
  let : CharP L 2 := charP_of_injective_algebraMap' K 2
  have heval : aeval θ (X ^ 4 + X + 1 : (ZMod 2)[X]) = 0 := by
    simpa only [map_add, map_pow, aeval_X, map_one] using hθ
  have hmin : minpoly (ZMod 2) θ = (X ^ 4 + X + 1 : (ZMod 2)[X]) :=
    (minpoly.eq_of_irreducible_of_monic quartic_over_prime_field heval quartic_monic).symm
  obtain ⟨hfin, _, hsize⟩ := D07.Ch13.FrobeniusRoots.simple_field_data
    (X ^ 4 + X + 1 : (ZMod 2)[X]) θ quartic_over_prime_field heval
  refine ⟨by rw [hmin, quartic_degree], hfin, ?_, ?_, ?_⟩
  · norm_num only [Nat.card_zmod, quartic_degree, Nat.reducePow] at hsize
    exact hsize
  · exact D07.Ch13.FrobeniusRoots.simple_field_isSplittingField _ θ
      quartic_over_prime_field heval
  · obtain ⟨_, _, g, h, hgm, hhm, hgd, hhd, hgi, hhi, _, hfactor⟩ :=
      higher_power_counterexample K hcard
    have hzero : aeval θ (X ^ 4 - X - 1 : K[X]) = 0 := by
      simpa only [map_add, map_sub, map_pow, aeval_X, map_one, CharTwo.sub_eq_add] using hθ
    rw [hfactor, map_mul] at hzero
    rcases mul_eq_zero.mp hzero with hg | hh
    · rw [← minpoly.eq_of_irreducible_of_monic hgi hg hgm, hgd]
    · rw [← minpoly.eq_of_irreducible_of_monic hhi hh hhm, hhd]

end D07.Ch20.FiniteArtinSchreier
