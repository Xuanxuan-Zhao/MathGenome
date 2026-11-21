import MathGenome.Internal.Specs.D05.M07.DualRank
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M07.DualKernelImage
import MathGenome.Internal.D05.M07.AnnihilatorDimension
import MathGenome.Internal.D05.M07.DualBasis

/-! K05.07.dual_rank: rank and injectivity-surjectivity duality. -/

namespace D05.M07.DualRank

/-- Rank-nullity for pullback, the kernel-annihilator identity, and the two
dimension formulas give the paper's calculation. The final subtraction is
justified by the image being a subspace of W. -/
theorem rank_dualMap : Specs.D05.M07.DualRank.rank_dualMap := by
  intro K V W _ _ _ _ _ _ _ T
  calc
    Module.finrank K (LinearMap.range T.dualMap) =
        Module.finrank K (Module.Dual K W) -
          Module.finrank K (LinearMap.ker T.dualMap) :=
      Nat.eq_sub_of_add_eq (by
        simpa only [Nat.add_comm] using
          (D05.M03.RankNullity.rank_nullity T.dualMap).symm)
    _ = Module.finrank K W -
        (Module.finrank K W - Module.finrank K (LinearMap.range T)) := by
      rw [(D05.M07.DualBasis.dual_dimension (K := K) (V := W)).2,
        D05.M07.DualKernelImage.ker_dualMap_eq_annihilator_range T,
        (D05.M07.AnnihilatorDimension.annihilator_dimension (LinearMap.range T)).2]
    _ = Module.finrank K (LinearMap.range T) :=
      Nat.sub_sub_self (Submodule.finrank_le (LinearMap.range T))

/-- The library equivalence uses the image-annihilator identity and the fact
that annihilation distinguishes subspaces. Specialize to the finite-dimensional
spaces of the source statement. -/
theorem injective_iff_dualMap_surjective :
    Specs.D05.M07.DualRank.injective_iff_dualMap_surjective := by
  intro K V W _ _ _ _ _ _ _ T
  exact (LinearMap.dualMap_surjective_iff (f := T)).symm

/-- A pullback along a surjection is injective; conversely, a functional
annihilating a proper image gives a nonzero element of the pullback kernel.
The duals here remain algebraic duals over the original field. -/
theorem surjective_iff_dualMap_injective :
    Specs.D05.M07.DualRank.surjective_iff_dualMap_injective := by
  intro K V W _ _ _ _ _ _ _ T
  exact (LinearMap.dualMap_injective_iff (f := T)).symm

end D05.M07.DualRank
