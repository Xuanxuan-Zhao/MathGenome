import MathGenome.Internal.Specs.D07.Ch11.MultivariateBoundary
import MathGenome.Internal.D07.Ch11.MultivariateBoundaryBivariateNonprincipalIdeal
import MathGenome.Internal.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders
import Mathlib.Tactic.FinCases

/-! Several formal commuting indeterminates, paper.tex:2828–2874. -/

universe u
noncomputable section

namespace D07.Ch11.MultivariateBoundary

open MvPolynomial
open Specs.D07.Ch11.MultivariateBoundary
open scoped Pointwise MonomialOrder

def bivariateEquiv : BivariateEquivType.{u} := bivariateEquivValue

theorem exponentVectorModel : ExponentVectorModel := by
  intro m
  exact ⟨Finsupp.equivFunOnFinite, fun _ _ => rfl⟩

theorem coefficientModel : CoefficientModel.{u} := by
  intro R _ m
  refine ⟨fun p => p.coeff.hasFiniteSupport, ?_, ?_⟩
  · intro p q
    exact ⟨MvPolynomial.ext p q, fun h d => congrArg (fun p => p.coeff d) h⟩
  · intro a
    exact ⟨AddMonoidAlgebra.ofCoeff a, rfl⟩

theorem monomialExpansion : MonomialExpansion.{u} := by
  intro R _ m p
  conv_lhs => rw [MvPolynomial.as_sum p]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem coefficientArithmetic : CoefficientArithmetic.{u} := by
  intro R _ m p q d
  exact ⟨by simp, by simp, MvPolynomial.coeff_mul p q d⟩

theorem supportClosure : SupportClosure.{u} := by
  intro R _ m p q
  exact ⟨MvPolynomial.support_add, by ext d; simp, MvPolynomial.support_mul p q⟩

theorem ringStructure : RingStructure.{u} := by
  intro R _ m
  exact ⟨inferInstance, rfl, rfl, rfl⟩

theorem ringLaws : RingLaws.{u} := by
  intro R _ m p q r
  exact ⟨mul_assoc p q r, by rw [map_one, one_mul], by rw [map_one, mul_one],
    mul_add p q r, add_mul p q r, mul_comm p q⟩

theorem bivariateCoefficients : BivariateCoefficients.{u} := by
  intro R _ p i j
  change ((Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingEquiv.toRingHom
    (finSuccEquiv R 1 (rename (Equiv.swap (0 : Fin 2) 1) p))).coeff j).coeff i = _
  rw [Polynomial.coeff_map]
  change ((uniqueAlgEquiv R (Fin 1))
    ((finSuccEquiv R 1 (rename (Equiv.swap (0 : Fin 2) 1) p)).coeff j)).coeff i = _
  rw [coeff_uniqueAlgEquiv, finSuccEquiv_coeff_coeff]
  have h : (exponent i j).mapDomain (Equiv.swap (0 : Fin 2) 1) =
      (Finsupp.single (default : Fin 1) i).cons j := by
    ext a
    fin_cases a <;> simp [exponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.cons]
  rw [← h, coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 2) 1).injective]

theorem bivariateGenerators : BivariateGenerators.{u} := by
  intro R _
  constructor
  · change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingEquiv.toRingHom
      (finSuccEquiv R 1 (rename (Equiv.swap (0 : Fin 2) 1) (X 0))) = _
    rw [rename_X, Equiv.swap_apply_left]
    change Polynomial.map _ (finSuccEquiv R 1 (X (0 : Fin 1).succ)) = _
    rw [finSuccEquiv_X_succ, Polynomial.map_C]
    congr 1
    change uniqueAlgEquiv R (Fin 1) (X 0) = Polynomial.X
    simp
  constructor
  · simp [bivariateEquivValue, finSuccEquiv_apply, uniqueAlgEquiv]
  · intro a
    simp [bivariateEquivValue, finSuccEquiv_apply, uniqueAlgEquiv]

theorem bivariateSupport : BivariateSupport.{u} := by
  intro R _ p
  have h (i j : ℕ) : exponent i j ∈ p.support ↔
      i ∈ ((bivariateEquivValue R p).coeff j).support := by
    simp only [MvPolynomial.mem_support_iff, Polynomial.mem_support_iff,
      bivariateCoefficients R p i j]
  refine ⟨h, ?_⟩
  intro j
  simp only [Polynomial.mem_support_iff]
  constructor
  · intro hj
    by_contra hn
    apply hj
    ext i
    have hi : ¬ exponent i j ∈ p.support := fun hi => hn ⟨i, hi⟩
    simpa only [Polynomial.coeff_zero] using
      (Polynomial.notMem_support_iff.mp (fun hi' => hi ((h i j).mpr hi')))
  · rintro ⟨i, hi⟩ hz
    have := (h i j).mp hi
    simp [hz] at this

theorem bivariateProductCoefficients : BivariateProductCoefficients.{u} := by
  intro R _ p q k l
  have h : (((bivariateEquivValue R p) * (bivariateEquivValue R q)).coeff l).coeff k =
      ∑ jj ∈ Finset.antidiagonal l, ∑ ii ∈ Finset.antidiagonal k,
        p.coeff (exponent ii.1 jj.1) * q.coeff (exponent ii.2 jj.2) := by
    rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro jj hjj
    rw [Polynomial.coeff_mul]
    simp_rw [bivariateCoefficients R p, bivariateCoefficients R q]
  refine ⟨?_, h⟩
  rw [← bivariateCoefficients R (p * q) k l, map_mul]
  exact h

private theorem coordinateQuotient (R : Type u) [CommRing R]
    (a b : Fin 2) (e : MvPolynomial (Fin 2) R ≃+* Polynomial (Polynomial R))
    (ha : e (X a) = Polynomial.X) (hb : e (X b) = Polynomial.C Polynomial.X)
    (hc : ∀ r : R, e (C r) = Polynomial.C (Polynomial.C r)) :
    ∃ q : (MvPolynomial (Fin 2) R ⧸ Ideal.span ({X a} : Set (MvPolynomial (Fin 2) R)))
        ≃+* Polynomial R,
      q (Ideal.Quotient.mk _ (X b)) = Polynomial.X ∧
      ∀ r : R, q (Ideal.Quotient.mk _ (C r)) = Polynomial.C r := by
  let I : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {X a}
  let J : Ideal (Polynomial (Polynomial R)) := Ideal.span {Polynomial.X - Polynomial.C 0}
  have hIJ : J = I.map e.toRingHom := by
    simp [I, J, Ideal.map_span, ha]
  let q : (MvPolynomial (Fin 2) R ⧸ I) ≃+* Polynomial R :=
    (Ideal.quotientEquiv I J e hIJ).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : Polynomial R)).toRingEquiv
  refine ⟨q, ?_, ?_⟩
  · change Polynomial.eval 0 (e (X b)) = Polynomial.X
    rw [hb, Polynomial.eval_C]
  · intro r
    change Polynomial.eval 0 (e (C r)) = Polynomial.C r
    rw [hc, Polynomial.eval_C]

theorem coordinateQuotients : CoordinateQuotients.{u} := by
  intro R _
  obtain ⟨hx, hy, hc⟩ := bivariateGenerators R
  constructor
  · let e := (renameEquiv R (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
      (bivariateEquivValue R)
    apply coordinateQuotient R 0 1 e
    · simpa [e] using hy
    · simpa [e] using hx
    · intro r
      simpa [e] using hc r
  · exact coordinateQuotient R 1 0 (bivariateEquivValue R) hy hx hc

theorem degreeDefinitions : DegreeDefinitions.{u} := by
  intro R _ m p
  exact ⟨rfl, fun i => degreeOf_eq_sup i p⟩

theorem degreeWithBottom : DegreeWithBottom.{u} := by
  classical
  intro R _ m p
  by_cases hp : p = 0
  · subst p
    simp
  · simp only [hp, ite_false]
    have hs : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
    constructor
    · simpa only [MvPolynomial.totalDegree, Function.comp_def] using
        (Finset.coe_sup_of_nonempty hs (fun d => d.sum fun _ n => n)).symm
    · intro i
      simpa only [degreeOf_eq_sup, Function.comp_def] using
        (Finset.coe_sup_of_nonempty hs (fun d => d i)).symm

theorem exampleDegrees : ExampleDegrees.{u} := by
  intro R _ _
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · rw [totalDegree_add_eq_right_of_totalDegree_lt (by
      rw [totalDegree_X, totalDegree_X_pow]; decide), totalDegree_X_pow]
  · have h : degreeOf (0 : Fin 2) (X 1 ^ 2 : MvPolynomial (Fin 2) R) <
        degreeOf 0 (X 0 : MvPolynomial (Fin 2) R) := by
      simp [degreeOf_X_pow_of_ne (R := R) 2 (by decide : (0 : Fin 2) ≠ 1)]
    rw [degreeOf_add_eq_of_degreeOf_lt h, degreeOf_X_self]
  · have h : degreeOf (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) R) <
        degreeOf 1 (X 1 ^ 2 : MvPolynomial (Fin 2) R) := by
      simp [degreeOf_X_of_ne (R := R) (by decide : (1 : Fin 2) ≠ 0)]
    rw [add_comm, degreeOf_add_eq_of_degreeOf_lt h, degreeOf_X_self_pow]

theorem exampleLexLeadingMonomial : ExampleLexLeadingMonomial.{u} := by
  intro R _ _
  classical
  let lex := Specs.D07.Ch11.MultivariateBoundaryDistinctDivisionRemainders.lexOrder
  have hy : lex.degree (X 1 ^ 2 : MvPolynomial (Fin 2) R) = Finsupp.single 1 2 := by
    rw [X_pow_eq_monomial, lex.degree_monomial]
    simp
  have hlt : lex.degree (X 1 ^ 2 : MvPolynomial (Fin 2) R) ≺[lex]
      lex.degree (X 0 : MvPolynomial (Fin 2) R) := by
    rw [hy, lex.degree_X]
    change toLex (Finsupp.single (1 : Fin 2) 2) < toLex (Finsupp.single (0 : Fin 2) 1)
    use 0
    simp
  have hd := lex.degree_add_of_lt hlt
  have hc := lex.leadingCoeff_add_of_lt hlt
  dsimp
  refine ⟨hd.trans lex.degree_X, ?_⟩
  rw [MonomialOrder.leadingTerm, hd, hc, lex.degree_X, lex.leadingCoeff_X]
  rfl

theorem zeroRingExample : ZeroRingExample.{u} := by
  intro R _ _
  have h : (X 0 + X 1 ^ 2 : MvPolynomial (Fin 2) R) = 0 := Subsingleton.elim _ _
  dsimp
  simp [h]

theorem fieldBoundaries : FieldBoundaries.{u} := by
  exact ⟨MultivariateBoundaryBivariateNonprincipalIdeal.variables_prime,
    MultivariateBoundaryBivariateNonprincipalIdeal.x_not_dvd_y,
    MultivariateBoundaryBivariateNonprincipalIdeal.variables_not_associated,
    MultivariateBoundaryBivariateNonprincipalIdeal.origin_ideal_proper,
    MultivariateBoundaryBivariateNonprincipalIdeal.origin_ideal_not_principal,
    MultivariateBoundaryBivariateNonprincipalIdeal.ufd_not_pid,
    MultivariateBoundaryDistinctDivisionRemainders.lexVariableOrder,
    MultivariateBoundaryDistinctDivisionRemainders.leadingMonomials,
    MultivariateBoundaryDistinctDivisionRemainders.cancellationIdentities,
    MultivariateBoundaryDistinctDivisionRemainders.terminalRemainders,
    MultivariateBoundaryDistinctDivisionRemainders.idealDifference,
    MultivariateBoundaryDistinctDivisionRemainders.divisionSteps,
    MultivariateBoundaryDistinctDivisionRemainders.distinctDivisionRemainders⟩

end D07.Ch11.MultivariateBoundary
