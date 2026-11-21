import MathGenome.Internal.Specs.D07.Ch11.LinearAlgebraBridge
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.D07.Ch11.FieldPolynomialPid
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import MathGenome.LinearAlgebra.OperatorPolynomials

/-! K07.11.linear_algebra_bridge. The canonical D05 determinant and
Cayley–Hamilton theorems are reused in finite dimension. The general
annihilator theorem works without finite dimension, and the shift example
is on the polynomial vector space with its explicit countable basis. -/

noncomputable section
universe u v
namespace D07.Ch11.LinearAlgebraBridge
open Polynomial
open Specs.D07.Ch11.LinearAlgebraBridge

theorem scalarAction : ScalarAction.{u,v} := by
  intro F V _ _ _ T a
  exact ⟨Algebra.algebraMap_eq_smul_one a, fun _ => rfl, (Algebra.commutes a T).symm⟩

theorem evaluationUniversal : EvaluationUniversal.{u,v} := by
  intro F V _ _ _ T
  refine ⟨fun a => aeval_C T a, aeval_X T, ?_⟩
  intro Φ hC hX
  exact Polynomial.ringHom_ext (fun a => (hC a).trans (aeval_C T a).symm)
    (hX.trans (aeval_X T).symm)

theorem evaluationLaws : EvaluationLaws.{u,v} := by
  intro F V _ _ _ T f g
  refine ⟨map_mul (aeval T) f g, ?_⟩
  exact Ch11.EvaluationUniversal.coefficientFormula F (Module.End F V)
    (scalarHom F V) T (evaluation F V T).toRingHom (fun a => aeval_C T a) (aeval_X T) f

theorem annihilatorCarrier : AnnihilatorCarrier.{u,v} := by
  intro F V _ _ _ T f
  rfl

theorem nonzeroAnnihilatorIffIntegral : NonzeroAnnihilatorIffIntegral.{u,v} := by
  intro F V _ _ _ T
  constructor
  · intro h
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  · intro h hbot
    have hm : minpoly F T ∈ annihilator F V T := minpoly.aeval F T
    rw [hbot] at hm
    exact (minpoly.ne_zero h) hm

theorem minimalGenerator : MinimalGenerator.{u,v} := by
  intro F V _ _ _ T h
  have hi := (nonzeroAnnihilatorIffIntegral F V T).mp h
  have hm := minpoly.monic hi
  have hgen : annihilator F V T = Ideal.span {minimalPolynomial F V T} := by
    ext f
    exact minpoly.dvd_iff.symm.trans Ideal.mem_span_singleton.symm
  refine ⟨hm, hgen, minimalPolynomial F V T, ⟨hm, hgen⟩, ?_⟩
  intro p hp
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm hp.1
  · apply Ideal.mem_span_singleton.mp
    rw [← hgen, hp.2]
    exact Ideal.subset_span (Set.mem_singleton _)
  · apply Polynomial.natDegree_le_of_dvd _ hm.ne_zero
    apply Ideal.mem_span_singleton.mp
    rw [← hp.2, hgen]
    exact Ideal.subset_span (Set.mem_singleton _)

theorem annihilationIffDivisibility : AnnihilationIffDivisibility.{u,v} := by
  intro F V _ _ _ T f _
  exact minpoly.dvd_iff.symm

theorem minimalDegree : MinimalDegree.{u,v} := by
  intro F V _ _ _ T f hf he
  exact ⟨minpoly.degree_le_of_ne_zero F T hf he,
    Polynomial.natDegree_le_of_dvd (minpoly.dvd F T he) hf⟩

theorem endDimension : EndDimension.{u,v} := by
  intro F V _ _ _ _
  exact D05.M08.Annihilating.end_dimension

theorem powersDependent : PowersDependent.{u,v} := by
  intro F V _ _ _ _ T
  exact D05.M08.Annihilating.powers_dependent T

theorem finiteAnnihilator : FiniteAnnihilator.{u,v} := by
  intro F V _ _ _ _ T
  obtain ⟨p, hp, hd, he⟩ := D05.M08.Annihilating.exists_nonzero_annihilator T
  exact ⟨D05.M08.Annihilating.ideal_ne_bot T, p, hp, hd, he⟩

theorem finiteMinimalExists : FiniteMinimalExists.{u,v} := by
  intro F V _ _ _ _ T
  exact ⟨(minimalGenerator F V T (finiteAnnihilator F V T).1).1,
    (minimalGenerator F V T (finiteAnnihilator F V T).1).2.1⟩

theorem charpolyFormula : CharpolyFormula.{u,v} := by
  intro F V _ _ _ _ T n b
  rw [← LinearMap.charpoly_toMatrix T b]
  rfl

theorem charpolyBasisIndependent : CharpolyBasisIndependent.{u,v} := by
  intro F V _ _ _ _ T n m b c
  exact (charpolyFormula F V T n b).symm.trans (charpolyFormula F V T m c)

theorem charpolyDegree : CharpolyDegree.{u,v} := by
  intro F V _ _ _ _ T
  exact ⟨D05.M08.Charpoly.monic T, D05.M08.Charpoly.degree T, D05.M08.Charpoly.natDegree T⟩

theorem cayleyHamilton : CayleyHamilton.{u,v} := by
  intro F V _ _ _ _ T
  exact D05.M08.CayleyHamilton.annihilates T

theorem minpolyCharpoly : MinpolyCharpoly.{u,v} := by
  intro F V _ _ _ _ T
  have hdvd := (annihilationIffDivisibility F V T T.charpoly
    (finiteAnnihilator F V T).1).mp (cayleyHamilton F V T)
  have hd := minimalDegree F V T T.charpoly (charpolyDegree F V T).1.ne_zero
    (cayleyHamilton F V T)
  exact ⟨hdvd, hd.1.trans_eq (charpolyDegree F V T).2.1,
    hd.2.trans_eq (charpolyDegree F V T).2.2⟩

theorem zeroSpace : ZeroSpace.{u,v} := by
  intro F V _ _ _ _ T h
  have hz := (finrank_zero_iff_forall_zero (K := F) (V := V)).mp h
  let : Subsingleton V := ⟨fun x y => (hz x).trans (hz y).symm⟩
  have hμ : minimalPolynomial F V T = 1 := minpoly.subsingleton F T
  have hχ : T.charpoly = 1 := D05.M08.Charpoly.zero_dimensional T h
  refine ⟨inferInstance, Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _, ?_,
    hμ, hχ, ?_, ?_⟩
  · ext f
    simp [annihilator, RingHom.mem_ker, Subsingleton.elim (evaluation F V T f) 0]
  · rw [hμ, Polynomial.degree_one]
  · rw [hχ, Polynomial.degree_one]

/-- Evaluation at the shift is the left-regular representation of F[X]. -/
theorem shift_evaluation (F : Type u) [Field F] (f : F[X]) :
    evaluation F F[X] (shift F) f = Algebra.lmul F F[X] f := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul F F[X]) (X : F[X]) f
  simpa only [shift, evaluation, Polynomial.aeval_X_left_apply] using h

theorem shiftBasis : ShiftBasis.{u} := by
  intro F _
  have hb (i : ℕ) : Polynomial.basisMonomials F i = (X : F[X]) ^ i := by
    simp [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]
  refine ⟨hb, ?_, ?_⟩
  · intro i
    rw [hb, hb]
    change X * X ^ i = X ^ (i + 1)
    exact (pow_succ' X i).symm
  · intro h
    let := h
    exact Module.Finite.not_linearIndependent_of_infinite
      (Polynomial.basisMonomials F) (Polynomial.basisMonomials F).linearIndependent

theorem shiftEvaluation : ShiftEvaluation.{u} := by
  intro F _ f
  have h : evaluation F F[X] (shift F) f (Polynomial.basisMonomials F 0) = f := by
    rw [shift_evaluation, (shiftBasis F).1 0]
    simp
  refine ⟨h, ?_⟩
  rw [h]
  conv_rhs => arg 2; ext i; rw [(shiftBasis F).1 i]
  simpa only [Polynomial.sum_def, Algebra.smul_def, Polynomial.algebraMap_eq] using
    (Polynomial.sum_C_mul_X_pow_eq f).symm

theorem shiftNoMinimalPolynomial : ShiftNoMinimalPolynomial.{u} := by
  intro F _
  have hn (f : F[X]) (hf : f ≠ 0) :
      evaluation F F[X] (shift F) f (Polynomial.basisMonomials F 0) ≠ 0 := by
    rwa [(shiftEvaluation F f).1]
  have hbot : annihilator F F[X] (shift F) = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    have he : evaluation F F[X] (shift F) f = 0 := hf
    have he0 := congrArg (fun S : Module.End F F[X] => S (Polynomial.basisMonomials F 0)) he
    simpa only [(shiftEvaluation F f).1, LinearMap.zero_apply] using he0
  refine ⟨hn, hbot, ?_, ?_⟩
  · intro hi
    exact (nonzeroAnnihilatorIffIntegral F F[X] (shift F)).mpr hi hbot
  · rintro ⟨p, hp, he⟩
    exact hn p hp.ne_zero (by rw [he, LinearMap.zero_apply])

end D07.Ch11.LinearAlgebraBridge
