import MathGenome.Internal.Specs.D05.M04.RankFactorization
import MathGenome.Internal.D05.M04.RankBridge
import MathGenome.Internal.D05.M02.BasisExtension
import Mathlib.LinearAlgebra.Dimension.Free

/-! K05.04.rank_factorization: choose a column-space basis and its coordinates. -/

namespace D05.M04.RankFactorization

open Matrix

theorem rank_factorization : Specs.D05.M04.RankFactorization.rank_factorization := by
  intro K _ m n r A hr
  classical
  let P := Submodule.span K (Set.range A.col)
  have hdim : Module.finrank K P = r :=
    (D05.M04.RankBridge.rank_eq_column_rank A).symm.trans hr
  let b : Module.Basis (Fin r) K P := Module.finBasisOfFinrankEq K P hdim
  let C : Matrix (Fin m) (Fin r) K := fun i j => (b j).val i
  let a : Fin n → P := fun j => ⟨A.col j, Submodule.subset_span ⟨j, rfl⟩⟩
  let R : Matrix (Fin r) (Fin n) K := fun i j => b.repr (a j) i
  have hC : LinearIndependent K C.col := by
    exact b.linearIndependent.map' P.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hprod : A = C * R := by
    ext i j
    have h := congrArg (fun x : P => x.val i) (b.sum_repr (a j))
    change A i j = ∑ k, (b k).val i * b.repr (a j) k
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm, a, Matrix.col_apply] using h.symm
  have hRrank : R.rank = r := by
    have h := D05.M03.CompositionRank.rank_comp_eq_of_injective
      R.mulVecLin C.mulVecLin (Matrix.mulVec_injective_iff.mpr hC)
    change Module.finrank K (LinearMap.range (C.mulVecLin.comp R.mulVecLin)) =
      R.rank at h
    rw [← Matrix.mulVecLin_mul, ← hprod] at h
    exact h.symm.trans hr
  have hR : LinearIndependent K R.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin r) = Module.finrank K (Submodule.span K (Set.range R.row))
    rw [Fintype.card_fin, D05.M04.RankBridge.row_rank_eq_column_rank R,
      ← D05.M04.RankBridge.rank_eq_column_rank R, hRrank]
  exact ⟨C, R, hprod, hC, hR⟩

theorem zero_rank_factorization :
    Specs.D05.M04.RankFactorization.zero_rank_factorization := by
  intro K _ m n A hr
  obtain ⟨C, R, hprod, _, _⟩ := rank_factorization A hr
  have hzero : A = 0 := by
    rw [hprod]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨hzero, ?_, ?_, ?_⟩
  · simp [hzero]
  · exact linearIndependent_empty_type
  · exact linearIndependent_empty_type

end D05.M04.RankFactorization
