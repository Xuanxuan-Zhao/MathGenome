import MathGenome.Internal.Specs.D05.M02.BasisExtension.Choice
import MathGenome.Internal.D05.M02.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.Zorn

/-!
K05.02.basis_extension (paper.tex:498): unrestricted extension by Zorn's lemma.
The chain union is an upper bound because every relation has finite support.
A maximal independent extension spans, since otherwise another vector could be
adjoined. The final bridge uses the already proved basis characterization.
-/

namespace D05.M02.BasisExtension.Choice

theorem independent_chain_union :
    Specs.D05.M02.BasisExtension.Choice.independent_chain_union := by
  intro K V _ _ _ C hC h
  exact linearIndepOn_sUnion_of_directed (R := K) (v := id) hC.directedOn h

theorem independent_insert_of_not_mem_span :
    Specs.D05.M02.BasisExtension.Choice.independent_insert_of_not_mem_span := by
  intro K V _ _ _ S x hS hx
  have hxs : x ∉ S := fun h => hx (Submodule.subset_span h)
  exact (linearIndepOn_id_insert hxs).mpr ⟨hS, hx⟩

/-- This is the explicit invocation of the paper's choice principle. The
partially ordered family consists of independent subsets containing `S`. -/
theorem exists_maximal_independent_superset :
    Specs.D05.M02.BasisExtension.Choice.exists_maximal_independent_superset := by
  intro K V _ _ _ S hS
  let A : Set (Set V) :=
    {T | S ⊆ T ∧ LinearIndependent K (fun t : T => (t : V))}
  have hchain : ∀ C ⊆ A, IsChain (· ⊆ ·) C → C.Nonempty →
      ∃ U ∈ A, ∀ T ∈ C, T ⊆ U := by
    intro C hCA hC hne
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T, hT⟩ := hne
      exact (hCA hT).1.trans (Set.subset_sUnion_of_mem hT)
    · exact independent_chain_union C hC (fun T hT => (hCA hT).2)
    · intro T hT
      exact Set.subset_sUnion_of_mem hT
  obtain ⟨T, hST, hmax⟩ := zorn_subset_nonempty A hchain S ⟨Set.Subset.rfl, hS⟩
  refine ⟨T, hST, hmax.prop.2, ?_⟩
  intro U hTU hU
  exact Set.Subset.antisymm (hmax.le_of_ge ⟨hST.trans hTU, hU⟩ hTU) hTU

theorem maximal_independent_spans :
    Specs.D05.M02.BasisExtension.Choice.maximal_independent_spans := by
  intro K V _ _ _ T hT hmax
  apply top_unique
  intro x _
  by_contra hx
  have hins := independent_insert_of_not_mem_span T x hT hx
  have heq : insert x T = T := hmax (insert x T) (Set.subset_insert x T) hins
  exact hx (Submodule.subset_span (heq ▸ Set.mem_insert x T))

theorem basis_extension : Specs.D05.M02.BasisExtension.Choice.basis_extension := by
  intro K V _ _ _ S hS
  obtain ⟨T, hST, hT, hmax⟩ := exists_maximal_independent_superset S hS
  refine ⟨T, hST, ?_⟩
  apply D05.M02.Basis.basis_iff_independent_span (fun t : T => (t : V)) |>.mpr
  refine ⟨hT, ?_⟩
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    maximal_independent_spans T hT hmax

end D05.M02.BasisExtension.Choice
