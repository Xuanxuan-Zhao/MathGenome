import MathGenome.Internal.Specs.D07.Ch12.FiniteGeneration
import MathGenome.Internal.D07.Ch12.SimpleDegree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Finite algebraic generation (K07.12.finite_generation).
A finite vector-space basis generates the field. Conversely, finite composita
of finite simple extensions are finite; their degrees are bounded by the
product of their simple degrees. This argument keeps repeated generators and
the empty list, and works in an arbitrary specified ambient field extension.
-/

universe u v

namespace D07.Ch12.FiniteGeneration

open Specs.D07.Ch12.FiniteGeneration

noncomputable section

private theorem finrank_iSup_le_product
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    {ι : Type*} (E : ι → IntermediateField K L) (s : Finset ι) :
    Module.finrank K (⨆ i ∈ s, E i : IntermediateField K L) ≤
      ∏ i ∈ s, Module.finrank K (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hempty : (⨆ i ∈ (∅ : Finset ι), E i : IntermediateField K L) = ⊥ := by simp
    rw [hempty, Finset.prod_empty, IntermediateField.finrank_bot]
  | @insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha]
    exact (IntermediateField.finrank_sup_le _ _).trans (Nat.mul_le_mul_left _ ih)

private theorem basis_adjoin_eq_top
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    {ι : Type*} (b : Module.Basis ι K L) :
    IntermediateField.adjoin K (Set.range b) = ⊤ := by
  apply top_unique
  intro x _
  have hspan : Submodule.span K (Set.range b) ≤
      (IntermediateField.adjoin K (Set.range b)).toSubalgebra.toSubmodule :=
    Submodule.span_le.mpr (IntermediateField.subset_adjoin K _)
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top : x ∈ (⊤ : Submodule K L))

/-- A finite compositum bound, with the natural degree justified by finiteness. -/
theorem adjoin_degree_bound : AdjoinDegreeBound.{u, v} := by
  intro K L _ _ _ r α hα
  let E : Fin r → IntermediateField K L := fun i => IntermediateField.adjoin K {α i}
  have hE : ∀ i, FiniteDimensional K (E i) := fun i =>
    (DegreeDefinition.finite_iff_finiteDimensional K (E i)).mp
      ((SimpleDegree.algebraic_iff_finite_simple_extension K L (α i)).mp (hα i))
  let : ∀ i, FiniteDimensional K (E i) := hE
  have heq : IntermediateField.adjoin K (Set.range α) = ⨆ i, E i := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      exact (le_iSup E i) (IntermediateField.mem_adjoin_simple_self K (α i))
    · apply iSup_le
      intro i
      apply IntermediateField.adjoin_simple_le_iff.mpr
      exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  have hfinite : FiniteDimensional K (IntermediateField.adjoin K (Set.range α)) := by
    rw [heq]
    infer_instance
  let := hfinite
  refine ⟨Module.finrank K (IntermediateField.adjoin K (Set.range α)),
    (Module.finrank_eq_rank _ _).symm, ?_⟩
  have hsimple (i : Fin r) : Module.finrank K (E i) = (minpoly K (α i)).natDegree :=
    ((DegreeDefinition.degree_eq_nat_iff K (E i) _).mp
      (SimpleDegree.simple_degree K L (α i) (hα i))).2
  rw [heq]
  have huniv : (⨆ i ∈ (Finset.univ : Finset (Fin r)), E i : IntermediateField K L) =
      ⨆ i, E i := by simp
  have hbound := finrank_iSup_le_product K L E Finset.univ
  rw [huniv] at hbound
  simpa only [hsimple] using hbound

/-- Transfer the bound through the canonical inclusion of the top field. -/
theorem generated_extension_degree_bound : GeneratedExtensionDegreeBound.{u, v} := by
  intro K L _ _ _ r α hα hgen
  obtain ⟨n, hn, hbound⟩ := adjoin_degree_bound K L r α hα
  rw [hgen] at hn
  refine ⟨n, ?_, hbound⟩
  exact (IntermediateField.topEquiv.toLinearEquiv.rank_eq).symm.trans hn

/-- A finite basis supplies algebraic field generators; the converse follows
from the finite degree bound. -/
theorem finite_iff_finite_algebraic_generation :
    FiniteIffFiniteAlgebraicGeneration.{u, v} := by
  intro K L _ _ _
  constructor
  · intro hfinite
    let : FiniteDimensional K L :=
      (DegreeDefinition.finite_iff_finiteDimensional K L).mp hfinite
    let b := Module.finBasis K L
    have halg := FiniteAlgebraic.finite_extension_is_algebraic K L hfinite
    exact ⟨Module.finrank K L, b, fun i => halg.isAlgebraic (b i),
      basis_adjoin_eq_top K L b⟩
  · rintro ⟨r, α, hα, hgen⟩
    obtain ⟨n, hn, _⟩ := generated_extension_degree_bound K L r α hα hgen
    exact ⟨n, hn⟩

theorem empty_adjoin_degree : EmptyAdjoinDegree.{u, v} := by
  intro K L _ _ _
  rw [IntermediateField.adjoin_empty]
  exact IntermediateField.rank_bot

end

end D07.Ch12.FiniteGeneration
