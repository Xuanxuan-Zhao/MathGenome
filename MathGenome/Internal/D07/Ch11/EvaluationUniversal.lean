import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.D07.Ch11.PolynomialArithmetic
import Mathlib.Algebra.Polynomial.Monomial

/-!
The universal property of formal polynomial evaluation,
K07.11.evaluation_universal (paper.tex:2229–2254).

`eval₂RingHom'` constructs the extension under exactly the commutation
assumption in the paper. A ring homomorphism is determined by its values on
constants and X. The formulas below retain the order φ(a_i) * s^i in an
arbitrary target ring. No nontriviality assumption is used.
-/

universe u v

namespace D07.Ch11.EvaluationUniversal

open Polynomial
open Specs.D07.Ch11.EvaluationUniversal

theorem universalEvaluation : UniversalEvaluation.{u, v} := by
  intro R S _ _ φ s hs
  let Φ := eval₂RingHom' φ s (fun a => (hs a).symm)
  have hC : ∀ a, Φ (C a) = φ a := fun a => eval₂_C φ s
  have hX : Φ X = s := eval₂_X φ s
  refine ⟨Φ, ⟨hC, hX⟩, ?_⟩
  intro Ψ hΨ
  exact Polynomial.ringHom_ext (fun a => (hΨ.1 a).trans (hC a).symm)
    (hΨ.2.trans hX.symm)

theorem coefficientFormula : CoefficientFormula.{u, v} := by
  intro R S _ _ φ s Φ hC hX f
  calc
    Φ f = Φ (∑ i ∈ f.support, C (f.coeff i) * X ^ i) := by
      simpa only [Polynomial.sum_def] using
        congrArg Φ (Polynomial.sum_C_mul_X_pow_eq f).symm
    _ = ∑ i ∈ f.support, φ (f.coeff i) * s ^ i := by
      simp only [map_sum, map_mul, map_pow, hC, hX]

theorem finiteSumFormula : FiniteSumFormula.{u, v} := by
  intro R S _ _ φ s Φ hC hX t a
  simp only [map_sum, map_mul, map_pow, hC, hX]

theorem commutativeUniversalEvaluation : CommutativeUniversalEvaluation.{u, v} := by
  intro R S _ _ φ s
  exact universalEvaluation R S φ s (fun a => Commute.all s (φ a))

theorem necessaryCommutation : NecessaryCommutation.{u, v} := by
  intro R S _ _ φ s Φ hC hX a
  have h := congrArg Φ
    (PolynomialArithmetic.indeterminateCommutesConstants R a)
  show s * φ a = φ a * s
  simpa only [map_mul, hC, hX] using h

theorem existenceIffCommutation : ExistenceIffCommutation.{u, v} := by
  intro R S _ _ φ s
  constructor
  · rintro ⟨Φ, hC, hX⟩
    exact necessaryCommutation R S φ s Φ hC hX
  · intro hs
    obtain ⟨Φ, hΦ, _⟩ := universalEvaluation R S φ s hs
    exact ⟨Φ, hΦ⟩

theorem ordinaryEvaluation : OrdinaryEvaluation.{u} := by
  intro R _ x
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro a
    exact Polynomial.eval_C
  · exact Polynomial.eval_X
  · intro Φ hC hX
    exact Polynomial.ringHom_ext (fun a => (hC a).trans Polynomial.eval_C.symm)
      (hX.trans Polynomial.eval_X.symm)

theorem conditionalSubstitution : ConditionalSubstitution.{u} := by
  intro R _ g hg
  let Φ := eval₂RingHom' (C : R →+* Polynomial R) g (fun a => (hg a).symm)
  have hC : ∀ a, Φ (C a) = C a := fun a => eval₂_C C g
  have hX : Φ X = g := eval₂_X C g
  refine ⟨Φ, ⟨hC, hX, fun _ => rfl⟩, ?_⟩
  intro Ψ hΨ
  exact Polynomial.ringHom_ext (fun a => (hΨ.1 a).trans (hC a).symm)
    (hΨ.2.1.trans hX.symm)

theorem commutativeSubstitution : CommutativeSubstitution.{u} := by
  intro R _ g
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro a
    exact Polynomial.eval₂_C C g
  · exact Polynomial.eval₂_X C g
  · intro Φ hC hX
    exact Polynomial.ringHom_ext
      (fun a => (hC a).trans (Polynomial.eval₂_C C g).symm)
      (hX.trans (Polynomial.eval₂_X C g).symm)

end D07.Ch11.EvaluationUniversal
