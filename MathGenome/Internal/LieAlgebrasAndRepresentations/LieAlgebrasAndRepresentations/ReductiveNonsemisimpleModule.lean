import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule

/-! The two-dimensional Jordan-block representation of the one-dimensional
abelian algebra. Its invariant first coordinate line has no invariant
complement: the action sends any vector with second coordinate 1 to (1,0). -/

universe u
namespace LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule

open Specs.LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [Field k]

private def jordan : Module.End k (k × k) :=
  (LinearMap.inl k k k).comp (LinearMap.snd k k k)

private def representation : k →ₗ⁅k⁆ Module.End k (k × k) :=
  { LinearMap.toSpanSingleton k (Module.End k (k × k)) (jordan k) with
    map_lie' := by
      intro x y
      ext <;> simp [LieRing.of_associative_ring_bracket, jordan, mul_comm] }

private theorem representation_apply (x : k) (v : k × k) :
    representation k x v = (x * v.2, 0) := by
  change (x * v.2, x * 0) = (x * v.2, (0 : k))
  simp

private theorem no_invariant_complement : ¬ CompletelyReducible (representation k) := by
  let W : Submodule k (k × k) := LinearMap.ker (LinearMap.snd k k k)
  have hW : Invariant (representation k) W := by
    intro x v hv
    change (representation k x v).2 = 0
    rw [representation_apply]
  intro h
  obtain ⟨U, hU, hcompl⟩ := h W hW
  have hv : ((0, 1) : k × k) ∈ W ⊔ U := by
    rw [hcompl.sup_eq_top]
    trivial
  obtain ⟨w, hw, v, hv, heq⟩ := Submodule.mem_sup.mp hv
  have hw2 : w.2 = 0 := hw
  have hv2 : v.2 = 1 := by
    have hh := congrArg Prod.snd heq
    simpa [hw2] using hh
  have he : ((1, 0) : k × k) ∈ U := by
    have hh := hU 1 v hv
    simpa [representation_apply, hv2] using hh
  have hz : ((1, 0) : k × k) = (0, 0) :=
    Submodule.disjoint_def.mp hcompl.disjoint (1, 0) (by change (0 : k) = 0; rfl) he
  exact one_ne_zero (congrArg Prod.fst hz)

/-- A reductive Lie algebra need not have completely reducible finite-dimensional
representations, even over an arbitrary characteristic-zero field. -/
theorem counterexample :
    Specs.LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule.counterexample_type := by
  intro k _ _
  have hab : ∀ x y : k, ⁅x, y⁆ = 0 := by
    intro x y
    simp [LieRing.of_associative_ring_bracket, mul_comm]
  haveI : IsLieAbelian k := ⟨hab⟩
  refine ⟨Module.finrank_self k, ?_, hab, ?_, representation k,
    representation_apply k, ?_, ?_, ?_, no_invariant_complement k⟩
  · simp [Module.finrank_prod]
  · rw [LieAlgebra.radical_eq_top_of_isSolvable,
      (LieAlgebra.isLieAbelian_iff_center_eq_top k k).mp inferInstance]
  · intro hzero
    have hh := congrArg (fun f : Module.End k (k × k) => (f (0, 1)).1) hzero
    simp [representation_apply] at hh
  · ext <;> simp [pow_two, Module.End.mul_apply, representation_apply]
  · refine ⟨2, ?_⟩
    ext <;> simp [pow_two, Module.End.mul_apply, representation_apply]

end LieAlgebrasAndRepresentations.ReductiveNonsemisimpleModule
