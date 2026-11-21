import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.ClosedLinearImage
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RecessionSets
import Mathlib.LinearAlgebra.Projection

open Set Filter
open scoped Pointwise Topology
noncomputable section
universe u v
namespace VariationalNotes.ConvexGeometry

section Normed
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- With no nonzero recession direction in the kernel, bounded image slices are bounded. -/
lemma bounded_slice_of_recession_kernel {C : Set E} (A : E →ₗ[ℝ] F)
    (hC : IsClosed C) (hc : Convex ℝ C)
    (hk : ∀ d ∈ recession C, A d = 0 → d = 0)
    {B : Set F} (hB : IsClosed B) (hb : Convex ℝ B) (hbound : Bornology.IsBounded B) :
    Bornology.IsBounded (C ∩ A ⁻¹' B) := by
  by_cases hne : (C ∩ A ⁻¹' B).Nonempty
  · by_contra hunb
    have hclosed : IsClosed (C ∩ A ⁻¹' B) :=
      hC.inter (hB.preimage A.continuous_of_finiteDimensional)
    have hconv : Convex ℝ (C ∩ A ⁻¹' B) := hc.inter (hb.linear_preimage A)
    obtain ⟨d, hd, hd0⟩ := recession_nonzero_of_unbounded hne hclosed hconv hunb
    obtain ⟨x, hx⟩ := hne
    have hdc : d ∈ recession C :=
      recession_of_ray hC hc fun t ht => (hd x hx t ht).1
    have had : A d ∈ recession B := by
      apply recession_of_ray hB hb (x₀ := A x)
      intro t ht
      simpa only [Set.mem_preimage, map_add, map_smul] using (hd x hx t ht).2
    exact hd0 (hk d hdc (recession_eq_zero_of_bounded ⟨A x, hx.2⟩ hbound had))
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

/-- The special case with trivial kernel recession cone. -/
lemma closed_linear_image_of_recession_kernel {C : Set E} (A : E →ₗ[ℝ] F)
    (hC : IsClosed C) (hc : Convex ℝ C)
    (hk : ∀ d ∈ recession C, A d = 0 → d = 0) : IsClosed (A '' C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro y z hy hlim
  choose x hx hAx using hy
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hlim).subset_closedBall (0 : F)
  let D := C ∩ A ⁻¹' Metric.closedBall (0 : F) R
  have hclosed : IsClosed D := hC.inter
    (Metric.isClosed_closedBall.preimage A.continuous_of_finiteDimensional)
  have hbound : Bornology.IsBounded D := bounded_slice_of_recession_kernel A hC hc hk
    Metric.isClosed_closedBall (convex_closedBall _ _) Metric.isBounded_closedBall
  have hcompact : IsCompact D := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbound⟩
  have hyD : ∀ n, y n ∈ A '' D := by
    intro n
    refine ⟨x n, ⟨hx n, ?_⟩, hAx n⟩
    change A (x n) ∈ Metric.closedBall (0 : F) R
    rw [hAx n]
    exact hR (mem_range_self n)
  have hz : z ∈ A '' D :=
    (hcompact.image A.continuous_of_finiteDimensional).isClosed.mem_of_tendsto
      hlim (Eventually.of_forall hyD)
  exact Set.image_mono (fun _ h => h.1) hz

/-- Remove all kernel recession directions by passing to an algebraic complement.
Translation by either sign of such a direction preserves the original set. -/
lemma closed_linear_image_normed {C : Set E} (A : E →ₗ[ℝ] F)
    (hne : C.Nonempty) (hC : IsClosed C) (hc : Convex ℝ C)
    (hlin : recession C ∩ (A.ker : Set E) ⊆ lineality C) : IsClosed (A '' C) := by
  classical
  have hcone := recession_isCone C
  let L : Submodule ℝ E :=
    { carrier := recession C ∩ (A.ker : Set E)
      zero_mem' := ⟨hcone.1, A.ker.zero_mem⟩
      add_mem' := fun hd he => ⟨hcone.2.1 hd.1 he.1, A.ker.add_mem hd.2 he.2⟩
      smul_mem' := by
        intro r d hd
        refine ⟨?_, A.ker.smul_mem r hd.2⟩
        by_cases hr : 0 ≤ r
        · exact hcone.2.2 r hr hd.1
        · have hneg : -d ∈ recession C := by simpa using (hlin hd).2
          have hp := hcone.2.2 (-r) (neg_nonneg.mpr (le_of_not_ge hr)) hneg
          simpa using hp }
  obtain ⟨M, hLM⟩ := L.exists_isCompl
  have himage : A '' (C ∩ (M : Set E)) = A '' C := by
    apply Set.Subset.antisymm
    · exact Set.image_mono inter_subset_left
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨l, m, hsum, _⟩ := Submodule.existsUnique_add_of_isCompl hLM x
      have hneg : -(l : E) ∈ recession C := by simpa using (hlin l.property).2
      have hmC : (m : E) ∈ C := by
        have ht := hneg x hx 1 zero_le_one
        simpa [← hsum, add_assoc, add_comm, add_left_comm] using ht
      refine ⟨m, ⟨hmC, m.property⟩, ?_⟩
      have hl0 : A (l : E) = 0 := l.property.2
      rw [← hsum, map_add, hl0, zero_add]
  rw [← himage]
  apply closed_linear_image_of_recession_kernel A (hC.inter M.closed_of_finiteDimensional)
    (hc.inter M.convex)
  intro d hd had
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, m, hsum, _⟩ := Submodule.existsUnique_add_of_isCompl hLM x
  have hneg : -(l : E) ∈ recession C := by simpa using (hlin l.property).2
  have hmC : (m : E) ∈ C := by
    have ht := hneg x hx 1 zero_le_one
    simpa [← hsum, add_assoc, add_comm, add_left_comm] using ht
  have hmd : ∀ t : ℝ, 0 ≤ t → (m : E) + t • d ∈ C ∩ (M : Set E) :=
    hd m ⟨hmC, m.property⟩
  have hdc : d ∈ recession C := recession_of_ray hC hc fun t ht => (hmd t ht).1
  have hdm : d ∈ M := by
    have hm := M.sub_mem (hmd 1 zero_le_one).2 m.property
    simpa using hm
  exact Submodule.disjoint_def.mp hLM.disjoint d ⟨hdc, had⟩ hdm

end Normed

/-- A closed convex set has closed linear image when every kernel recession
vector lies in its lineality space, as in `thm:closed-image` of the manuscript. -/
theorem closed_linear_image : Specs.closed_linear_image.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C A hne hC hc hlin
  let : IsNormableSpace ℝ E := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup ℝ E
  let : NormedSpace ℝ E := IsNormableSpace.toNormedSpace ℝ E
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x hx =>
    (Metric.inseparable_iff.mpr (by simpa [dist_eq_norm] using hx)).eq
  let : IsNormableSpace ℝ F := isNormableSpace_of_finiteDimensional
  let : SeminormedAddCommGroup F := IsNormableSpace.toSeminormedAddCommGroup ℝ F
  let : NormedSpace ℝ F := IsNormableSpace.toNormedSpace ℝ F
  let : NormedAddCommGroup F := NormedAddCommGroup.ofSeparation fun x hx =>
    (Metric.inseparable_iff.mpr (by simpa [dist_eq_norm] using hx)).eq
  exact closed_linear_image_normed A hne hC hc hlin

end VariationalNotes.ConvexGeometry
