import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Incidence
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations

universe u v
noncomputable section
namespace FiniteCombinatorics.Graph.Trees
open scoped Matrix

abbrev Orientation : Specs.FiniteCombinatorics.Graph.Trees.Incidence.OrientationType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.OrientationValue

abbrev incidence : Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue

abbrev edgeWeightMatrix : Specs.FiniteCombinatorics.Graph.Trees.Incidence.edgeWeightMatrixType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.edgeWeightMatrixValue

abbrev weightedLaplacian : Specs.FiniteCombinatorics.Graph.Trees.Incidence.weightedLaplacianType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.weightedLaplacianValue

abbrev principalMinor : Specs.FiniteCombinatorics.Graph.Trees.Incidence.principalMinorType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.principalMinorValue

abbrev reducedIncidence : Specs.FiniteCombinatorics.Graph.Trees.Incidence.reducedIncidenceType :=
  Specs.FiniteCombinatorics.Graph.Trees.Incidence.reducedIncidenceValue


theorem orientation_exists : Specs.FiniteCombinatorics.Graph.Trees.Incidence.orientation_existsType := by
  intro V G
  exact ⟨⟨fun e => e.val.out.2, fun e => e.val.out.1,
    fun e => Sym2.mk_fst_out_snd_out e.val⟩⟩

theorem orientation_endpoints : Specs.FiniteCombinatorics.Graph.Trees.Incidence.orientation_endpointsType := by
  intro V G o e
  have h : G.Adj (o.tail e) (o.head e) := by
    have he := e.property
    rw [← o.edge_eq e] at he
    exact he
  refine ⟨h, h.ne, ?_⟩
  intro x
  rw [← o.edge_eq e, Sym2.mem_iff, or_comm]

theorem incidence_entries : Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidence_entriesType := by
  intro V G K _ o e
  classical
  obtain ⟨_, hne, hm⟩ := orientation_endpoints G o e
  dsimp [Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue]
  refine ⟨by simp, by simp [hne], ?_⟩
  intro x hx
  have hh : x ≠ o.head e := fun h => hx ((hm x).mpr (Or.inl h))
  have ht : x ≠ o.tail e := fun h => hx ((hm x).mpr (Or.inr h))
  simp [hh, ht]

theorem laplacian_entries : Specs.FiniteCombinatorics.Graph.Trees.Incidence.laplacian_entriesType := by
  intro V G _ K _ w
  classical
  dsimp [Specs.FiniteCombinatorics.Graph.Trees.Incidence.weightedLaplacianValue]
  exact ⟨fun x => by simp, fun x y h => by simp [h.ne, h],
    fun x y hne h => by simp [hne, h]⟩

attribute [local instance] Classical.propDecidable

private theorem incidence_weight_entry {V : Type u} (G : SimpleGraph V)
    (K : Type v) [Field K] (o : EdgeOrientation G) (w : G.edgeSet → K)
    (x y : V) (e : G.edgeSet) :
    incidence G K o x e * w e * incidence G K o y e =
      (if x = y then (if x ∈ e.val then w e else 0)
       else if e.val = s(x, y) then -w e else 0) := by
  classical
  have hne := (orientation_endpoints G o e).2.1
  rw [← o.edge_eq e]
  dsimp [incidence, Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue]
  by_cases xh : x = o.head e <;> by_cases xt : x = o.tail e <;>
    by_cases yh : y = o.head e <;> by_cases yt : y = o.tail e <;>
    simp_all [Sym2.mem_iff, eq_comm]

theorem laplacian_factorization : Specs.FiniteCombinatorics.Graph.Trees.Incidence.laplacian_factorizationType := by
  intro V G _ K _ o w
  classical
  ext x y
  change weightedLaplacian G K w x y =
    ((incidence G K o * Matrix.diagonal w) * (incidence G K o).transpose) x y
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, incidence_weight_entry]
  by_cases hxy : x = y
  · subst y
    simp [weightedLaplacian, Specs.FiniteCombinatorics.Graph.Trees.Incidence.weightedLaplacianValue]
  · simp only [hxy, ite_false]
    dsimp [weightedLaplacian, Specs.FiniteCombinatorics.Graph.Trees.Incidence.weightedLaplacianValue]
    rw [ite_eq_right hxy]
    by_cases hadj : G.Adj x y
    · rw [dite_eq_left hadj]
      symm
      rw [Finset.sum_eq_single (⟨s(x, y), hadj⟩ : G.edgeSet)]
      · simp
      · intro e _ he
        have hne : e.val ≠ s(x, y) := fun h => he (Subtype.ext h)
        simp [hne]
      · simp
    · rw [dite_eq_right hadj]
      symm
      apply Finset.sum_eq_zero
      intro e _
      have hne : e.val ≠ s(x, y) := by
        intro h
        have he := e.property
        rw [h] at he
        exact hadj he
      simp [hne]

theorem reduced_factorization : Specs.FiniteCombinatorics.Graph.Trees.Incidence.reduced_factorizationType := by
  intro V G _ K _ o w r
  classical
  ext x y
  have h := congrFun (congrFun (laplacian_factorization G K o w) x.val) y.val
  simpa only [Specs.FiniteCombinatorics.Graph.Trees.Incidence.principalMinorValue,
    Specs.FiniteCombinatorics.Graph.Trees.Incidence.reducedIncidenceValue,
    Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq] using h

theorem principalMinor_det_reindex : Specs.FiniteCombinatorics.Graph.Trees.Incidence.principalMinor_det_reindexType := by
  intro V _ K _ M r I _ e
  classical
  exact Matrix.det_reindex_self e (principalMinor M r)

end FiniteCombinatorics.Graph.Trees
