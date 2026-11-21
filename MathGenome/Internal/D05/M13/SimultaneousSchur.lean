import MathGenome.Internal.Specs.D05.M13.SimultaneousSchur
import MathGenome.Internal.D05.M10.SimultaneousTriangular
import MathGenome.Internal.D05.M13.Schur

/-! Simultaneous Schur triangularization for arbitrary commuting families.
The algebraic theorem upstream already performs finite spanning-subfamily
selection. Gram–Schmidt is applied once to its common basis, preserving the
initial spans for every member of the family simultaneously. -/

noncomputable section
namespace D05.M13.SimultaneousSchur

theorem orthonormalize_common_triangular_basis :
    Specs.D05.M13.SimultaneousSchur.orthonormalize_common_triangular_basis := by
  intro F V _ _ _ n S b hb
  -- Apply the flag-preserving construction to zero so no member of S needs
  -- to be chosen; this works even when S is empty.
  have hzero : (LinearMap.toMatrix b b (0 : Module.End F V)).IsUpperTriangular := by
    intro i j hij
    simp
  obtain ⟨e, _, heflag⟩ := D05.M13.Schur.orthonormalize_triangular_basis
    (0 : Module.End F V) b hzero
  refine ⟨e, ?_, heflag⟩
  intro T hT
  apply D05.M13.Schur.upper_triangular_of_initial_spans
  intro j
  have hk : j.val + 1 ≤ n := j.isLt
  have hej : e j ∈ Submodule.span F (b '' {i | i.val < j.val + 1}) := by
    rw [← heflag _ hk]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
  have hTe := D05.M13.Schur.initial_span_invariant T b (hb T hT) (j.val + 1) hej
  simpa only [OrthonormalBasis.coe_toBasis, heflag _ hk] using hTe

theorem simultaneous_schur : Specs.D05.M13.SimultaneousSchur.simultaneous_schur := by
  intro V _ _ _ S hc
  have ht (T : Module.End ℂ V) (_hT : T ∈ S) :
      Specs.D05.M10.Triangularization.HasUpperTriangularBasis T :=
    (D05.M10.Triangularization.triangularization T).1.mpr
      (D05.Foundations.Fta.splits T.charpoly)
  obtain ⟨n, b, hb⟩ := D05.M10.SimultaneousTriangular.simultaneous_triangular S hc ht
  obtain ⟨e, he, _⟩ := orthonormalize_common_triangular_basis S b hb
  exact ⟨n, e, he⟩

theorem simultaneous_schur_indexed :
    Specs.D05.M13.SimultaneousSchur.simultaneous_schur_indexed := by
  intro V ι _ _ _ T hc
  have hcomm : (Set.range T).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hc (fun h => hij (congrArg T h))
  obtain ⟨n, e, he⟩ := simultaneous_schur (Set.range T) hcomm
  exact ⟨n, e, fun i => he _ ⟨i, rfl⟩⟩

end D05.M13.SimultaneousSchur
