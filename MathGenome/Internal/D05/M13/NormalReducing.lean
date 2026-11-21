import MathGenome.Internal.Specs.D05.M13.NormalReducing
import MathGenome.Internal.D05.M13.NormalReducing.Subspace
import MathGenome.Internal.D05.M13.NormalReducing.Graph

/-! K05.13.normal_reducing: assemble the finite-dimensional reduction theorem
and its graph-based commutant consequence from their proved stages. -/

noncomputable section
namespace D05.M13.NormalReducing

theorem invariant_subspace_reduces :
    Specs.D05.M13.NormalReducing.invariant_subspace_reduces := by
  intro F V _ _ _ _ T M hT hM
  obtain ⟨hMa, hP, hPa, _⟩ := Subspace.invariant_and_normal_restrictions T M hT hM
  exact ⟨hMa, hP, hPa⟩

theorem invariant_and_normal_restrictions :
    Specs.D05.M13.NormalReducing.invariant_and_normal_restrictions :=
  Subspace.invariant_and_normal_restrictions

theorem commutes_adjoint : Specs.D05.M13.NormalReducing.commutes_adjoint :=
  Graph.commutes_adjoint

theorem normal_reducing : Specs.D05.M13.NormalReducing.normal_reducing := by
  intro F V _ _ _ _ T hT
  exact ⟨fun M hM => invariant_subspace_reduces T M hT hM,
    fun S hST => commutes_adjoint T S hT hST⟩

end D05.M13.NormalReducing
