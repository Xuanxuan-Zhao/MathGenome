import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsB
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsD

/-! Matrix-model hypotheses for using reconstruction in LA-D08 and LA-F04.
Each Cartan and coroot is the one occurring in the coordinate computation. -/

namespace Specs.LieAlgebrasAndRepresentations.ClassicalMatrixCartans

open RootDecomposition RootForm MaximalTori SolvableRadical

def type_a_type : Prop :=
  ∀ n : ℕ,
    IsSemisimple_value ℂ (ClassicalRootsA.sl n) ∧
    IsMaximalToral_value (ClassicalRootsA.cartan n)

def type_b_type : Prop :=
  ∀ n : ℕ,
    IsSemisimple_value ℂ (ClassicalRootsB.algebra n) ∧
    IsMaximalToral_value (ClassicalRootsB.cartan n) ∧
    (∀ a : ClassicalRootsB.Weight n,
      ClassicalRootsB.character a ∈ rootSet_value (ClassicalRootsB.cartan n) ↔
        a ∈ ClassicalRootsB.roots n) ∧
    ∀ a ∈ ClassicalRootsB.roots n,
      ((coroot_value (ClassicalRootsB.cartan n) (ClassicalRootsB.character a) :
        ClassicalRootsB.algebra n) : ClassicalRootsB.Mat n) = ClassicalRootsB.coroot a

def type_c_type : Prop :=
  ∀ n : ℕ,
    IsSemisimple_value ℂ (ClassicalRootsC.sp n) ∧
    ∃ (H : LieSubalgebra ℂ (ClassicalRootsC.sp n)) (e : ClassicalRootsC.V n ≃ₗ[ℂ] H),
      IsMaximalToral_value H ∧
      (∀ t, ((e t : ClassicalRootsC.sp n) : ClassicalRootsC.Mat n) =
        ClassicalRootsC.diagonal t) ∧
      (∀ a : ClassicalRootsC.Weight n,
        a.comp e.symm.toLinearMap ∈ rootSet_value H ↔ a ∈ ClassicalRootsC.rootSet n) ∧
      ∀ a ∈ ClassicalRootsC.rootSet n,
        ((coroot_value H (a.comp e.symm.toLinearMap) :
          ClassicalRootsC.sp n) : ClassicalRootsC.Mat n) = ClassicalRootsC.coroot a

/-- The orthogonal rank-one exception is governed by LA-D08-D. -/
def type_d_type : Prop :=
  ∀ n : ℕ, n ≠ 1 →
    IsSemisimple_value ℂ (ClassicalRootsD.algebra n) ∧
    ∃ (H : LieSubalgebra ℂ (ClassicalRootsD.algebra n))
      (e : ClassicalRootsD.Params n ≃ₗ[ℂ] H),
      IsMaximalToral_value H ∧
      (∀ t, ((e t : ClassicalRootsD.algebra n) : ClassicalRootsD.Mat n) =
        ClassicalRootsD.diagonal n t) ∧
      (∀ a : ClassicalRootsD.Dual n,
        a.comp e.symm.toLinearMap ∈ rootSet_value H ↔ a ∈ ClassicalRootsD.roots n) ∧
      ∀ a ∈ ClassicalRootsD.roots n,
        ((coroot_value H (a.comp e.symm.toLinearMap) :
          ClassicalRootsD.algebra n) : ClassicalRootsD.Mat n) =
            ClassicalRootsD.coroot n (fun i => a (ClassicalRootsD.coordinate n i))

end Specs.LieAlgebrasAndRepresentations.ClassicalMatrixCartans
