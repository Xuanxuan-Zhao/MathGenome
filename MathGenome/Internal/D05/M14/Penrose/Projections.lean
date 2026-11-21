import MathGenome.Internal.Specs.D05.M14.Penrose.Projections
import MathGenome.Internal.D05.M14.Pseudoinverse
import MathGenome.Internal.D05.M13.Adjoint

/-! The projection identities and four Penrose equations, using the intrinsic
construction of the pseudoinverse. All maps may be rectangular or zero. -/

noncomputable section

namespace D05.M14.Penrose.Projections

theorem map_comp_pseudoinverse :
    Specs.D05.M14.Penrose.Projections.map_comp_pseudoinverse := by
  intro F V W _ _ _ _ _ _ _ T
  ext w
  exact D05.M14.Pseudoinverse.map_pseudoinverse T w

theorem pseudoinverse_comp_map :
    Specs.D05.M14.Penrose.Projections.pseudoinverse_comp_map := by
  intro F V W _ _ _ _ _ _ _ T
  ext v
  let p := D05.orthogonalProjection T.ker.orthogonal v
  have hp := (D05.M12.Projection.component_characterization
    T.ker.orthogonal v p).mp rfl
  have hk := hp.2
  rw [D05.M12.OrthogonalDecomposition.double_orthogonal T.ker] at hk
  change T (v - p) = 0 at hk
  have ht : T p = T v := (sub_eq_zero.mp (by simpa only [map_sub] using hk)).symm
  apply Eq.symm
  apply (D05.M14.Pseudoinverse.characterization T (T v) p).mpr
  refine ⟨hp.1, ?_⟩
  rw [D05.M12.Projection.fixes_subspace T.range (T v) ⟨v, rfl⟩]
  exact ht

theorem map_pseudoinverse_map :
    Specs.D05.M14.Penrose.Projections.map_pseudoinverse_map := by
  intro F V W _ _ _ _ _ _ _ T
  rw [map_comp_pseudoinverse T]
  ext v
  exact D05.M12.Projection.fixes_subspace T.range (T v) ⟨v, rfl⟩

theorem pseudoinverse_map_pseudoinverse :
    Specs.D05.M14.Penrose.Projections.pseudoinverse_map_pseudoinverse := by
  intro F V W _ _ _ _ _ _ _ T
  rw [pseudoinverse_comp_map T]
  ext w
  exact D05.M12.Projection.fixes_subspace T.ker.orthogonal
    (D05.pseudoinverse T w) (D05.M14.Pseudoinverse.mem_kernel_orthogonal T w)

/-- Convert the shared projection's inner-product identity into equality with
its canonical adjoint, using the proved uniqueness of the adjoint. -/
theorem orthogonalProjection_adjoint {F V : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V]
    (U : Submodule F V) :
    LinearMap.adjoint (D05.orthogonalProjection U) = D05.orthogonalProjection U := by
  exact (D05.M13.Adjoint.adjoint_unique (D05.orthogonalProjection U)
    (D05.orthogonalProjection U) (D05.M12.Projection.self_adjoint_identity U)).symm

theorem map_comp_pseudoinverse_adjoint :
    Specs.D05.M14.Penrose.Projections.map_comp_pseudoinverse_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  rw [map_comp_pseudoinverse T]
  exact orthogonalProjection_adjoint T.range

theorem pseudoinverse_comp_map_adjoint :
    Specs.D05.M14.Penrose.Projections.pseudoinverse_comp_map_adjoint := by
  intro F V W _ _ _ _ _ _ _ T
  rw [pseudoinverse_comp_map T]
  exact orthogonalProjection_adjoint T.ker.orthogonal

theorem zero_map : Specs.D05.M14.Penrose.Projections.zero_map := by
  intro F V W _ _ _ _ _ _ _
  rw [D05.M14.Pseudoinverse.pseudoinverse_zero]
  simp

end D05.M14.Penrose.Projections
