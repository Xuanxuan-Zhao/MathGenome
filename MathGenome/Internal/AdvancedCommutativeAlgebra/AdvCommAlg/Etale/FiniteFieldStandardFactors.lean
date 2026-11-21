import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace AdvCommAlg.Etale.FiniteFieldStandardFactors

noncomputable section
open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.FiniteFieldStandardFactors

lemma quadratic_monic : quadratic.Monic := by
  simpa only [quadratic, add_assoc] using
    (monic_X_pow_add (R := ZMod 2) (p := X + 1) (n := 2) (by
      simpa using (degree_X_add_C (1 : ZMod 2)).trans_lt (by norm_num : (1 : WithBot ℕ) < 2)))

lemma quadratic_degree : quadratic.natDegree = 2 := by
  norm_num [quadratic, natDegree_add_eq_left_of_natDegree_lt]

set_option backward.isDefEq.respectTransparency false in
lemma quadratic_irreducible : Irreducible quadratic := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [quadratic_degree]
  · intro x
    fin_cases x <;> simp [IsRoot, quadratic, CharTwo.add_self_eq_zero]

set_option backward.isDefEq.respectTransparency false in
lemma quadratic_derivative : quadratic.derivative = 1 := by
  simp [quadratic, derivative_add, CharTwo.add_self_eq_zero]

theorem quadratic_facts : quadraticFacts :=
  ⟨quadratic_monic, quadratic_degree, quadratic_irreducible, quadratic_derivative⟩

/-- Removing the harmless localization at 1 preserves the base algebra. -/
lemma quotient_localization_one {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (hf : f.Monic) (e : AdjoinRoot f ≃ₐ[A] B)
    (hd : IsUnit (AdjoinRoot.mk f f.derivative)) :
    Nonempty (B ≃ₐ[A] LocalizedQuotient f 1) ∧ standardEtaleValue A B := by
  let : IsLocalization.Away (1 : AdjoinRoot f) (LocalizedQuotient f 1) := by
    simpa only [map_one] using
      (inferInstance : IsLocalization.Away (AdjoinRoot.mk f 1) (LocalizedQuotient f 1))
  let l : AdjoinRoot f ≃ₐ[A] LocalizedQuotient f 1 :=
    (IsLocalization.atOne (AdjoinRoot f) (LocalizedQuotient f 1)).restrictScalars A
  have hd' : IsUnit (derivativeImage f 1) := hd.map (algebraMap _ _)
  exact ⟨⟨e.symm.trans l⟩, f, hf, 1, hd', ⟨e.symm.trans l⟩⟩

theorem first_presentation : firstPresentation := by
  intro K _ _ _ hK
  let : Fact (Irreducible quadratic) := ⟨quadratic_irreducible⟩
  let : Module.Finite (ZMod 2) (AdjoinRoot quadratic) := quadratic_monic.finite_adjoinRoot
  let : Fintype (AdjoinRoot quadratic) := Module.fintypeOfFintype (AdjoinRoot.powerBasis' quadratic_monic).basis
  have hcard : Fintype.card (AdjoinRoot quadratic) = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    change 2 ^ Module.finrank (ZMod 2)
      ((ZMod 2)[X] ⧸ Ideal.span {quadratic}) = 4
    rw [finrank_quotient_span_eq_natDegree, quadratic_degree]
    norm_num
  let e : AdjoinRoot quadratic ≃ₐ[ZMod 2] K :=
    FiniteField.algEquivOfCardEq 2 (hcard.trans hK.symm)
  have hd : IsUnit (AdjoinRoot.mk quadratic quadratic.derivative) := by
    rw [quadratic_derivative, map_one]
    exact isUnit_one
  obtain ⟨hl, hs⟩ := quotient_localization_one quadratic quadratic_monic e hd
  exact ⟨⟨e⟩, hd, hl, hs⟩

variable (K : Type) [Field K] [Fintype K]

omit [Fintype K] in
lemma linear_factors_coprime (a b : K) (hab : a ≠ b) :
    IsCoprime (Ideal.span ({X - C a} : Set K[X]))
      (Ideal.span ({X - C b} : Set K[X])) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  exact isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr hab).isUnit)

lemma split_ideal_eq :
    Ideal.span ({splitPolynomial K} : Set K[X]) =
      ⨅ a : K, Ideal.span ({X - C a} : Set K[X]) := by
  classical
  rw [splitPolynomial, ← Ideal.prod_span_singleton]
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := fun a : K => Ideal.span ({X - C a} : Set K[X]))
    (fun a _ b _ hab => linear_factors_coprime K a b hab)
  simpa using h

lemma split_derivative_unit (a : K) : IsUnit ((splitPolynomial K).derivative.eval a) := by
  classical
  rw [splitPolynomial]
  change IsUnit (eval a (derivative
    (Multiset.map (fun b : K => X - C b) Finset.univ.val).prod))
  rw [eval_multiset_prod_X_sub_C_derivative (by simp)]
  apply (isUnit_iff_ne_zero).mpr
  apply Multiset.prod_ne_zero
  intro hb
  obtain ⟨c, hc, heq⟩ := Multiset.mem_map.mp hb
  have heq' : a = c := sub_eq_zero.mp heq
  subst c
  exact (Finset.univ.nodup.notMem_erase) hc

lemma split_monic : (splitPolynomial K).Monic := by
  classical
  exact monic_prod_X_sub_C _ _

theorem split_facts : splitFacts := by
  intro K _ _ hK
  refine ⟨split_monic K, ?_, linear_factors_coprime K, split_derivative_unit K⟩
  classical
  simpa [splitPolynomial] using
    (natDegree_finsetProd_X_sub_C_eq_card (Finset.univ : Finset K) id).trans
      (by simpa using hK)

/-- Evaluation on the roots, with the diagonal K-algebra structure on the product. -/
def evaluationHom : AdjoinRoot (splitPolynomial K) →ₐ[K] (K → K) :=
  AlgHom.pi fun a => AdjoinRoot.liftAlgHom (splitPolynomial K) (Algebra.ofId K K) a (by
    classical
    change eval a (splitPolynomial K) = 0
    rw [splitPolynomial, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp))

@[simp] lemma evaluationHom_mk (p : K[X]) (a : K) :
    evaluationHom K (AdjoinRoot.mk (splitPolynomial K) p) a = p.eval a := by
  rfl

lemma evaluationHom_injective : Function.Injective (evaluationHom K) := by
  apply (injective_iff_map_eq_zero (evaluationHom K)).mpr
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [split_ideal_eq]
  apply Ideal.mem_iInf.mpr
  intro a
  rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
  exact congrFun hx a

/-- CRT for the pairwise comaximal linear ideals gives surjectivity. -/
lemma evaluationHom_surjective : Function.Surjective (evaluationHom K) := by
  classical
  intro y
  let I : K → Ideal K[X] := fun a => Ideal.span {X - C a}
  obtain ⟨p, hp⟩ := Ideal.pi_quotient_surjective
    (I := I) (fun a b hab => linear_factors_coprime K a b hab)
    (fun a => (quotientSpanXSubCAlgEquiv a).symm (y a))
  refine ⟨AdjoinRoot.mk (splitPolynomial K) p, ?_⟩
  funext a
  have ha := congrArg (quotientSpanXSubCAlgEquiv a) (hp a)
  change (quotientSpanXSubCAlgEquiv a) (Ideal.Quotient.mk _ p) = _ at ha
  simpa only [quotientSpanXSubCAlgEquiv_mk, AlgEquiv.apply_symm_apply,
    evaluationHom_mk] using ha

/-- The CRT equivalence sends a polynomial class to its evaluations. -/
def evaluationEquiv : AdjoinRoot (splitPolynomial K) ≃ₐ[K] (K → K) :=
  AlgEquiv.ofBijective (evaluationHom K)
    ⟨evaluationHom_injective K, evaluationHom_surjective K⟩

theorem second_presentation : secondPresentation := by
  intro K _ _ hK
  let e := evaluationEquiv K
  have he : ∀ (p : K[X]) (a : K),
      e (AdjoinRoot.mk (splitPolynomial K) p) a = p.eval a := by
    intro p a
    exact evaluationHom_mk K p a
  have hd : IsUnit (AdjoinRoot.mk (splitPolynomial K) (splitPolynomial K).derivative) := by
    have hu : IsUnit (e (AdjoinRoot.mk (splitPolynomial K) (splitPolynomial K).derivative)) := by
      apply Pi.isUnit_iff.mpr
      intro a
      rw [he]
      exact split_derivative_unit K a
    simpa using hu.map e.symm.toMonoidHom
  let reindex : K ≃ Fin 4 := (Fintype.equivFin K).trans (finCongr hK)
  let ep : AdjoinRoot (splitPolynomial K) ≃ₐ[K] (Fin 4 → K) :=
    e.trans (AlgEquiv.piCongrLeft' K (fun _ : K => K) reindex)
  obtain ⟨hl, hs⟩ := quotient_localization_one (splitPolynomial K) (split_monic K) ep hd
  exact ⟨⟨e, he⟩, hd, hl, hs⟩

end
end AdvCommAlg.Etale.FiniteFieldStandardFactors
