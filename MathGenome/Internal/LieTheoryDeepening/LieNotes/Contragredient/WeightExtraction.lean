import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.WeightExtraction
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

namespace LieNotes.Contragredient

open scoped BigOperators

variable {H V ι : Type*} [AddCommGroup H] [Module ℂ H]
  [AddCommGroup V] [Module ℂ V]

abbrev weightSpace (ρ : H →ₗ[ℂ] Module.End ℂ V) (μ : Module.Dual ℂ H) : Submodule ℂ V :=
  Specs.LieNotes.Contragredient.WeightExtraction.weightSpace ρ μ

@[simp]
theorem mem_weightSpace {ρ : H →ₗ[ℂ] Module.End ℂ V} {μ : Module.Dual ℂ H} {v : V} :
    v ∈ weightSpace ρ μ ↔ ∀ h : H, ρ h v = μ h • v :=
  Iff.rfl

/-- A finite family of distinct linear weights has distinct values at some common argument. -/
theorem exists_separating_element (μ : ι → Module.Dual ℂ H) (s : Finset ι)
    (hμ : Set.InjOn μ (s : Set ι)) :
    ∃ h : H, Set.InjOn (fun i ↦ μ i h) (s : Set ι) := by
  let S := ↥(s : Set ι)
  let P := {p : S × S // p.1 ≠ p.2}
  let difference : P → Module.Dual ℂ H := fun p ↦ μ p.val.1 - μ p.val.2
  have hd (p : P) : ∃ h : H, difference p h ≠ 0 := by
    by_contra! h
    apply p.property
    apply Subtype.ext
    apply hμ p.val.1.property p.val.2.property
    ext x
    exact sub_eq_zero.mp (h x)
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists difference hd
  refine ⟨h, ?_⟩
  intro i hi j hj heq
  by_contra hij
  let p : P := ⟨(⟨i, hi⟩, ⟨j, hj⟩), fun e ↦ hij (congrArg Subtype.val e)⟩
  exact hh p (sub_eq_zero.mpr heq)

private theorem aeval_mem_of_invariant (T : Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ ⦃v : V⦄, v ∈ W → T v ∈ W) {v : V} (hv : v ∈ W) (p : Polynomial ℂ) :
    Polynomial.aeval T p v ∈ W := by
  have hpow (n : ℕ) : (T ^ n) v ∈ W := by
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa only [pow_succ', Module.End.mul_apply] using hW ih
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, LinearMap.add_apply] using W.add_mem hp hq
  | monomial n c =>
    simpa only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      using W.smul_mem c (hpow n)

/-- Applying the Lagrange projection to a finite sum extracts its chosen weight component
inside any stable submodule containing the sum. -/
theorem mem_of_weight_sum_mem (ρ : H →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W)
    (μ : ι → Module.Dual ℂ H) (s : Finset ι) (hμ : Set.InjOn μ (s : Set ι))
    (v : ι → V) (hv : ∀ i ∈ s, v i ∈ weightSpace ρ (μ i))
    (hsum : (∑ i ∈ s, v i) ∈ W) : ∀ i ∈ s, v i ∈ W := by
  classical
  obtain ⟨h, hh⟩ := exists_separating_element μ s hμ
  intro i hi
  let p := Lagrange.basis s (fun j ↦ μ j h) i
  have hproj : Polynomial.aeval (ρ h) p (∑ j ∈ s, v j) = v i := by
    rw [map_sum, Finset.sum_eq_single i]
    · rw [Module.End.aeval_apply_of_mem_apply_eq_smul (mem_weightSpace.mp (hv i hi) h),
        Lagrange.eval_basis_self hh hi, one_smul]
    · intro j hj hji
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (mem_weightSpace.mp (hv j hj) h),
        Lagrange.eval_basis_of_ne (v := fun k ↦ μ k h) hji.symm hj, zero_smul]
    · exact fun hnot ↦ (hnot hi).elim
  rw [← hproj]
  exact aeval_mem_of_invariant (ρ h) W (hW h) hsum p

/-- Common eigenspaces are independent, whether or not they span the ambient space. -/
theorem weightSpace_iSupIndep (ρ : H →ₗ[ℂ] Module.End ℂ V) : iSupIndep (weightSpace ρ) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hzero i hi
  have hbot (h : H) ⦃z : V⦄ (hz : z ∈ (⊥ : Submodule ℂ V)) : ρ h z ∈ (⊥ : Submodule ℂ V) := by
    simp [(Submodule.mem_bot ℂ).mp hz]
  have hs : (∑ j ∈ s, v j) ∈ (⊥ : Submodule ℂ V) := by simp [hzero]
  exact (Submodule.mem_bot ℂ).mp (mem_of_weight_sum_mem ρ ⊥ hbot id s
    (fun _ _ _ _ e ↦ e) v hv hs i hi)

/-- A stable submodule is spanned by its intersections with any spanning family of
distinct common eigenspaces. -/
theorem iSup_inf_weightSpace_eq (ρ : H →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W)
    (μ : ι → Module.Dual ℂ H) (hμ : Function.Injective μ)
    (hspan : (⨆ i, weightSpace ρ (μ i)) = ⊤) :
    (⨆ i, W ⊓ weightSpace ρ (μ i)) = W := by
  classical
  apply le_antisymm (iSup_le fun _ ↦ inf_le_left)
  intro x hx
  have hx' : x ∈ ⨆ i, weightSpace ρ (μ i) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨v, hv, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp
    (fun i ↦ weightSpace ρ (μ i)) x).mp hx'
  have hs := mem_of_weight_sum_mem ρ W hW μ v.support hμ.injOn v (fun i _ ↦ hv i) hx
  exact Submodule.sum_mem _ fun i hi ↦
    (le_iSup (fun j ↦ W ⊓ weightSpace ρ (μ j)) i) ⟨hs i hi, hv i⟩

open Classical in
/-- The weight-space intersections form an internal direct sum in the stable submodule. -/
theorem isInternal_weightSpace_intersections (ρ : H →ₗ[ℂ] Module.End ℂ V)
    (W : Submodule ℂ V) (hW : ∀ (h : H) ⦃v : V⦄, v ∈ W → ρ h v ∈ W)
    (μ : ι → Module.Dual ℂ H) (hμ : Function.Injective μ)
    (hspan : (⨆ i, weightSpace ρ (μ i)) = ⊤) :
    DirectSum.IsInternal (fun i ↦ (weightSpace ρ (μ i)).comap W.subtype) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hz i hi
    apply Subtype.ext
    refine (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      ((weightSpace_iSupIndep ρ).comp hμ) s (fun j ↦ (v j : V)) hv ?_ i hi
    simpa only [map_sum, map_zero, Submodule.coe_subtype] using congrArg W.subtype hz
  · apply Submodule.map_injective_of_injective W.subtype_injective
    simpa only [Submodule.map_iSup, Submodule.map_comap_subtype, ← LinearMap.range_eq_map,
      Submodule.range_subtype] using iSup_inf_weightSpace_eq ρ W hW μ hμ hspan

abbrev singleOperatorFamily (T : Module.End ℂ V) : ℂ →ₗ[ℂ] Module.End ℂ V :=
  Specs.LieNotes.Contragredient.WeightExtraction.singleOperatorFamily T

/-- For a single operator, the common weight space is the ordinary eigenspace. -/
theorem weightSpace_singleOperatorFamily (T : Module.End ℂ V) (μ : Module.Dual ℂ ℂ) :
    weightSpace (singleOperatorFamily T) μ = T.eigenspace (μ 1) := by
  ext v
  rw [mem_weightSpace, Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    simpa only [one_smul] using (show (1 : ℂ) • T v = μ 1 • v from h 1)
  · intro hv z
    have hμ : μ z = z • μ 1 := by simpa using map_smul μ z (1 : ℂ)
    change z • T v = μ z • v
    rw [hv, hμ, smul_assoc]

end LieNotes.Contragredient
