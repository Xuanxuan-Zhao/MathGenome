import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.TowerMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Transitivity

/-! KD-09: the first fundamental exact sequence and its failure of left
injectivity for k → k[t] → k, with t sent to zero. -/
namespace AdvCommAlg.Differentials

universe u v w
noncomputable section
open scoped TensorProduct

/-- Exactness at Ω_{C/A} and surjectivity onto Ω_{C/B}. -/
theorem transitivity_exact :
    Specs.AdvCommAlg.Differentials.transitivityExact.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _
  exact ⟨KaehlerDifferential.exact_mapBaseChange_map A B C,
    KaehlerDifferential.map_surjective A B C⟩

/-- Scalar extension of the univariate differential basis gives k·dt;
Ω_{k/k} is zero, so the canonical first arrow is not injective. -/
theorem transitivity_failure_example :
    Specs.AdvCommAlg.Differentials.transitivityFailureExample.{u} := by
  intro k _
  let : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  let : IsScalarTower k (Polynomial k) k :=
    IsScalarTower.of_algebraMap_eq' (by
        ext a
        change a = Polynomial.eval 0 (Polynomial.C a)
        simp)
  let dt := (1 : k) ⊗ₜ[Polynomial k]
    KaehlerDifferential.D k (Polynomial k) Polynomial.X
  let e : (k ⊗[Polynomial k] KaehlerDifferential k (Polynomial k)) ≃ₗ[k] k :=
    ((KaehlerDifferential.polynomialEquiv k).baseChange (Polynomial k) k _ _).trans
      (TensorProduct.AlgebraTensorModule.rid (Polynomial k) k k)
  have he : e dt = 1 := by simp [e, dt]
  have hdt : dt ≠ 0 := by
    intro h
    have : (0 : k) = 1 := by simpa only [h, map_zero] using he
    exact zero_ne_one this
  let : Subsingleton (KaehlerDifferential k k) := subsingleton_self k
  refine ⟨⟨e, he⟩, hdt, inferInstance, Subsingleton.elim _ _, ?_⟩
  intro h
  exact hdt (h (Subsingleton.elim _ _))

end
end AdvCommAlg.Differentials
