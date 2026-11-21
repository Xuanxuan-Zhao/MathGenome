import MathGenome.Internal.Specs.D07.Ch12.TowerLaw
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.LinearAlgebra.Dimension.Free

/-! The product-basis tower law, cardinal degree, and positive finite degree. -/

universe u v w s t

namespace D07.Ch12.TowerLaw

noncomputable section

open DegreeDefinition

theorem product_basis : Specs.D07.Ch12.TowerLaw.ProductBasis.{u, v, w, s, t} := by
  intro K E L _ _ _ _ _ _ _ I J e b
  refine ⟨e.smulTower b, ?_⟩
  intro ij
  rw [Module.Basis.smulTower_apply, Algebra.smul_def]

/-- Cardinal lifts allow the two upper fields to have unrelated universes. -/
theorem degree_tower (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] :
    Cardinal.lift.{v} (degree K L) =
      Cardinal.lift.{v} (degree E L) * Cardinal.lift.{w} (degree K E) := by
  simpa only [degree, mul_comm] using (lift_rank_mul_lift_rank K E L).symm

theorem natural_degree_tower (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (m n : ℕ) (hm : degree K E = (m : Cardinal.{v}))
    (hn : degree E L = (n : Cardinal.{w})) :
    degree K L = ((n * m : ℕ) : Cardinal.{w}) ∧
      0 < m ∧ 0 < n ∧ 0 < n * m := by
  obtain ⟨hKE, hm'⟩ := (degree_eq_nat_iff K E m).mp hm
  obtain ⟨hEL, hn'⟩ := (degree_eq_nat_iff E L n).mp hn
  let := hKE
  let := hEL
  let : FiniteDimensional K L := FiniteDimensional.trans K E L
  have hmpos : 0 < m := hm' ▸ (Module.finrank_pos_iff_of_free K E).mpr inferInstance
  have hnpos : 0 < n := hn' ▸ (Module.finrank_pos_iff_of_free E L).mpr inferInstance
  refine ⟨?_, hmpos, hnpos, Nat.mul_pos hnpos hmpos⟩
  rw [degree_eq_finrank, ← Module.finrank_mul_finrank K E L, hm', hn', Nat.mul_comm]

end

end D07.Ch12.TowerLaw
