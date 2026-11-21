import MathGenome.Internal.Specs.D07.Ch12.DegreeDivisibility
import MathGenome.Internal.D07.Ch12.TowerLaw
import Mathlib.FieldTheory.Tower
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! Positive divisibility of intermediate degrees and the prime-degree case. -/

universe u v w

namespace D07.Ch12.DegreeDivisibility

noncomputable section

open DegreeDefinition

/-- Only the total extension is assumed finite. The two finiteness conclusions
justify interpreting both intermediate finranks as degrees. -/
theorem intermediate_degrees :
    Specs.D07.Ch12.DegreeDivisibility.IntermediateDegrees.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _
  let : FiniteDimensional K E := FiniteDimensional.left K E L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  have h := TowerLaw.natural_degree_tower K E L
    (Module.finrank K E) (Module.finrank E L)
    (degree_eq_finrank K E) (degree_eq_finrank E L)
  have hprod : Module.finrank K L = Module.finrank E L * Module.finrank K E :=
    Nat.cast_injective ((degree_eq_finrank K L).symm.trans h.1)
  exact ⟨inferInstance, inferInstance, h.2.1, h.2.2.1,
    ⟨Module.finrank E L, hprod.trans (Nat.mul_comm _ _)⟩,
    ⟨Module.finrank K E, hprod⟩⟩

/-- The same conclusion directly in terms of the cardinal definition of degree. -/
theorem cardinal_intermediate_degrees :
    Specs.D07.Ch12.DegreeDivisibility.CardinalIntermediateDegrees.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ d hd
  obtain ⟨hfin, hd'⟩ := (degree_eq_nat_iff K L d).mp hd
  let := hfin
  obtain ⟨hKE, hEL, hm, hn, hmd, hnd⟩ := intermediate_degrees K E L
  let := hKE
  let := hEL
  exact ⟨Module.finrank K E, Module.finrank E L,
    degree_eq_finrank K E, degree_eq_finrank E L, hm, hn,
    hd' ▸ hmd, hd' ▸ hnd⟩

/-- In a compatible abstract tower, an endpoint is identified with the image of
its specified embedding, so endpoint equality is expressed by surjectivity. -/
theorem prime_degree_endpoints :
    Specs.D07.Ch12.DegreeDivisibility.PrimeDegreeEndpoints.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ hp
  have hprod := Module.finrank_mul_finrank K E L
  have h := hp.isUnit_or_isUnit hprod.symm
  simp only [Nat.isUnit_iff] at h
  rcases h with hKE | hEL
  · exact Or.inl (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hKE).2
  · exact Or.inr (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hEL).2

/-- A prime-degree extension has no intermediate field other than its endpoints. -/
theorem prime_degree_no_proper_intermediate :
    Specs.D07.Ch12.DegreeDivisibility.PrimeDegreeNoProperIntermediate.{u, w} := by
  intro K L _ _ _ _ hp E
  rcases prime_degree_endpoints K E L hp with hKE | hEL
  · left
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a, ha⟩ := hKE ⟨x, hx⟩
    exact IntermediateField.mem_bot.mpr ⟨a, congrArg (fun y : E => (y : L)) ha⟩
  · right
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hEL x
    change (y : L) = x at hy
    exact hy ▸ y.property

end

end D07.Ch12.DegreeDivisibility
