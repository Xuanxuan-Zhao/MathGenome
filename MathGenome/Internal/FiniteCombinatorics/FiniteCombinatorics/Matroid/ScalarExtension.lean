import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ScalarExtension
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Extension of scalars preserves the indexed vector matroid (paper.tex W71).
Over a field every module is free, hence flat. Tensoring the injective linear
combination map therefore preserves independence. Conversely, independence over
L implies independence over K, and reflection through v ↦ 1 ⊗ v recovers the
original family. This works directly in the arbitrary ambient V.
-/
namespace FiniteCombinatorics.Matroid
open Set Submodule
open scoped TensorProduct

theorem scalarExtensionLinearIndepOn : Expected.scalarExtensionLinearIndepOn := by
  intro α K L _ _ _ V _ _ v I
  constructor
  · intro h
    exact (h.restrict_scalars' K).of_comp (TensorProduct.mk K L V 1)
  · intro h
    exact Module.Flat.linearIndependent_one_tmul h

theorem scalarExtensionMatroid : Expected.scalarExtensionMatroid := by
  intro α K L _ _ _ V _ _ E hE v
  refine _root_.Matroid.ext_indep ?_ ?_
  · rfl
  · intro I _
    rw [vectorIndep, vectorIndep, scalarExtensionLinearIndepOn K L v I]

theorem scalarExtensionRank : Expected.scalarExtensionRank := by
  intro α K L _ _ _ V _ _ E hE v A _
  unfold Expected.rank
  rw [scalarExtensionMatroid K L E hE v]

theorem scalarExtensionSpanDimension : Expected.scalarExtensionSpanDimension := by
  intro α K L _ _ _ V _ _ E hE v A hA
  have h := scalarExtensionRank K L E hE v A hA
  rw [vectorRank L E hE _ A hA, vectorRank K E hE v A hA] at h
  exact_mod_cast h

theorem scalarExtensionRepresents : Expected.scalarExtensionRepresents := by
  intro α K L _ _ _ V _ _ M v h I
  exact (h I).trans (and_congr_right fun _ =>
    (scalarExtensionLinearIndepOn K L v I).symm)

theorem scalarExtensionAlong : Expected.scalarExtensionAlong := by
  intro α K L _ _ ι V _ _ E hE v
  letI : Algebra K L := ι.toAlgebra
  exact ⟨rfl, scalarExtensionMatroid K L E hE v, scalarExtensionRank K L E hE v⟩

end FiniteCombinatorics.Matroid
