import MathGenome.Internal.D05.M02.SpanProperties
import MathGenome.Internal.D05.M02.Subspace
import MathGenome.Internal.Specs.D05.M02.SumIntersection

/-! K05.02.sum_intersection: actual sums, arbitrary intersections, and a union
counterexample over the named field. No finite-dimensional hypothesis is used. -/

namespace D05.M02.SumIntersection

open Specs.D05.M02.SumIntersection (sumSet)

theorem intersection_subspace : Specs.D05.M02.SumIntersection.intersection_subspace := by
  intro K V _ _ _ U W
  exact ⟨U ⊓ W, rfl⟩

theorem intersection_closed : Specs.D05.M02.SumIntersection.intersection_closed := by
  intro K V _ _ _ U W
  exact ⟨⟨U.zero_mem, W.zero_mem⟩,
    fun _ _ hx hy => ⟨U.add_mem hx.1 hy.1, W.add_mem hx.2 hy.2⟩,
    fun a _ hx => ⟨U.smul_mem a hx.1, W.smul_mem a hx.2⟩⟩

theorem sum_eq_sup : Specs.D05.M02.SumIntersection.sum_eq_sup := by
  intro K V _ _ _ U W
  ext x
  exact Submodule.mem_sup

theorem sum_closed : Specs.D05.M02.SumIntersection.sum_closed := by
  intro K V _ _ _ U W
  rw [← sum_eq_sup U W]
  exact ⟨(U ⊔ W).zero_mem, fun _ _ hx hy => (U ⊔ W).add_mem hx hy,
    fun a _ hx => (U ⊔ W).smul_mem a hx⟩

theorem union_subset_sum : Specs.D05.M02.SumIntersection.union_subset_sum := by
  intro K V _ _ _ U W x hx
  rcases hx with hu | hw
  · exact ⟨x, hu, 0, W.zero_mem, add_zero x⟩
  · exact ⟨0, U.zero_mem, x, hw, zero_add x⟩

theorem sum_le_iff : Specs.D05.M02.SumIntersection.sum_le_iff := by
  intro K V _ _ _ U W T
  constructor
  · intro h
    exact Set.Subset.trans (union_subset_sum U W) h
  · intro h x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    exact T.add_mem (h (Or.inl hu)) (h (Or.inr hw))

theorem sum_eq_span_union : Specs.D05.M02.SumIntersection.sum_eq_span_union := by
  intro K V _ _ _ U W
  rw [← sum_eq_sup U W]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    exact (Submodule.span K ((U : Set V) ∪ (W : Set V))).add_mem
      (SpanProperties.subset_span _ (Or.inl hu))
      (SpanProperties.subset_span _ (Or.inr hw))
  · exact (SpanProperties.span_le_iff _ (U ⊔ W)).mpr
      (by rw [sum_eq_sup U W]; exact union_subset_sum U W)

theorem iInter_subspace : Specs.D05.M02.SumIntersection.iInter_subspace := by
  intro K V ι _ _ _ U
  exact ⟨⨅ i, U i, Submodule.coe_iInf U⟩

theorem sInter_subspace : Specs.D05.M02.SumIntersection.sInter_subspace := by
  intro K V _ _ _ C
  refine ⟨sInf C, ?_⟩
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_sInf, Set.mem_sInter, Set.forall_mem_image]

theorem coordinate_lines_counterexample :
    Specs.D05.M02.SumIntersection.coordinate_lines_counterexample := by
  intro K _
  let U : Submodule K (K × K) :=
    { carrier := {x | x.2 = 0}
      zero_mem' := rfl
      add_mem' := by intro x y hx hy; change x.2 + y.2 = 0; rw [hx, hy, add_zero]
      smul_mem' := by intro a x hx; change a • x.2 = 0; rw [hx, smul_zero] }
  let W : Submodule K (K × K) :=
    { carrier := {x | x.1 = 0}
      zero_mem' := rfl
      add_mem' := by intro x y hx hy; change x.1 + y.1 = 0; rw [hx, hy, add_zero]
      smul_mem' := by intro a x hx; change a • x.1 = 0; rw [hx, smul_zero] }
  have he₁ : (1, 0) ∈ U := rfl
  have he₂ : (0, 1) ∈ W := rfl
  have hsum : ((1, 0) + (0, 1) : K × K) ∉
      (U : Set (K × K)) ∪ (W : Set (K × K)) := by
    change ¬ ((0 : K) + 1 = 0 ∨ (1 : K) + 0 = 0)
    simp only [zero_add, add_zero, one_ne_zero, or_self, not_false_eq_true]
  refine ⟨U, W, rfl, rfl, he₁, he₂, hsum, ?_⟩
  rintro ⟨S, hS⟩
  have h₁ : (1, 0) ∈ S := by rw [← SetLike.mem_coe, hS]; exact Or.inl he₁
  have h₂ : (0, 1) ∈ S := by rw [← SetLike.mem_coe, hS]; exact Or.inr he₂
  apply hsum
  rw [← hS]
  exact S.add_mem h₁ h₂

end D05.M02.SumIntersection
