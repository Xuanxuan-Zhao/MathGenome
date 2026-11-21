import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.SplittingCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.InseparableExample
import Mathlib.Algebra.Polynomial.Degree.Domain
import Lean.Elab.Tactic.Omega

namespace AdvCommAlg.FormalLifting.InseparableExample

universe u
noncomputable section
open Specs.AdvCommAlg.FormalLifting.InseparableExample
open Specs.AdvCommAlg.Differentials
open TensorProduct

/-- In characteristic p the hypersurface relation imposes no relation on dx. -/
theorem differential_basis : differentialBasis.{u} := by
  intro k _ p hp _
  let B := TruncatedPolynomial k p
  let I : Submodule B B :=
    Ideal.span {AdjoinRoot.mk (Polynomial.X ^ p : Polynomial k) (Polynomial.derivative (Polynomial.X ^ p))}
  have hd : (Polynomial.X ^ p : Polynomial k).derivative = 0 := by
    simp [Polynomial.derivative_X_pow]
  have hI : I = ⊥ := by simp [I, hd]
  obtain ⟨e, he⟩ := AdvCommAlg.Differentials.univariate_hypersurface k
    (Polynomial.X ^ p)
  let c : B ≃ₗ[B] KaehlerDifferential k B :=
    (I.quotEquivOfEqBot hI).symm.trans e
  refine ⟨(Module.Basis.singleton Unit B).map c, ?_⟩
  change c ((Module.Basis.singleton Unit B) ()) = _
  rw [Module.Basis.singleton_apply]
  change e (Ideal.Quotient.mk _ 1) = _
  simpa using he 1

/-- A degree-p polynomial cannot be a multiple of X^(2p). -/
lemma relation_not_mem_square (k : Type u) [Field k] (p : ℕ) (hp : 0 < p) :
    (Polynomial.X ^ p : Polynomial k) ∉
      (Ideal.span {(Polynomial.X ^ p : Polynomial k)}) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  have hd := Polynomial.natDegree_le_of_dvd h
    (pow_ne_zero p (Polynomial.X_ne_zero : (Polynomial.X : Polynomial k) ≠ 0))
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one] at hd
  omega

theorem conormal_obstruction : conormalObstruction.{u} := by
  intro k _ p hp _ h
  let B := TruncatedPolynomial k p
  have hker : RingHom.ker (algebraMap (Polynomial k) B) =
      Ideal.span {(Polynomial.X ^ p : Polynomial k)} := by
    exact Ideal.mk_ker
  have hf : (Polynomial.X ^ p : Polynomial k) ∈
      RingHom.ker (algebraMap (Polynomial k) B) := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  let f : RingHom.ker (algebraMap (Polynomial k) B) := ⟨Polynomial.X ^ p, hf⟩
  refine ⟨f, rfl, ?_, ?_⟩
  · intro hz
    have hm := (Algebra.Extension.Cotangent.mk_eq_zero_iff
      (P := conormalExtension k (Polynomial k) B h) f).mp hz
    change (Polynomial.X ^ p : Polynomial k) ∈
      (RingHom.ker (algebraMap (Polynomial k) B)) ^ 2 at hm
    rw [hker] at hm
    exact relation_not_mem_square k p hp.pos hm
  · rw [AdvCommAlg.Differentials.conormalMap_apply]
    change (1 : B) ⊗ₜ[Polynomial k]
      (KaehlerDifferential.D k (Polynomial k) (Polynomial.X ^ p)) = 0
    have hd : KaehlerDifferential.D k (Polynomial k)
        (Polynomial.X ^ p) = 0 := by
      rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Polynomial k) p]
      have hc : (p : Polynomial k) = 0 := by
        exact CharP.cast_eq_zero (Polynomial k) p
      rw [hc, zero_smul]
    rw [hd, TensorProduct.tmul_zero]

theorem not_formally_smooth : notFormallySmooth.{u} := by
  intro k _ p hp _ hs
  let B := TruncatedPolynomial k p
  have h : Function.Surjective (algebraMap (Polynomial k) B) :=
    AdjoinRoot.mk_surjective
  have hP : Specs.AdvCommAlg.FormalLifting.formallySmoothValue k (Polynomial k) :=
    (AdvCommAlg.FormalLifting.formallySmooth_iff k (Polynomial k)).mpr inferInstance
  have hi := ((AdvCommAlg.FormalLifting.SplittingCriterion.splitting_criterion
    k (Polynomial k) B h hP).2.mp hs).1
  obtain ⟨f, _, hf, hz⟩ := conormal_obstruction k p hp h
  apply hf
  apply hi
  simpa using hz

end
end AdvCommAlg.FormalLifting.InseparableExample
