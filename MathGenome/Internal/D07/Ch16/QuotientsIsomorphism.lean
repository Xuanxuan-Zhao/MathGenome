import MathGenome.Internal.Specs.D07.Ch16.QuotientsIsomorphism
import MathGenome.Internal.D07.Ch08.IdealDefinition
import MathGenome.Internal.D07.Ch16.MapsSubmodules
import Mathlib.LinearAlgebra.Isomorphisms

/-!
K07.16.quotients_isomorphism (paper.tex:2958–2980).
The canonical quotient and first-isomorphism constructions are used with
explicit representative formulas. The standard matrix action supplies the
noncommutative boundary example.
-/

universe u v w

namespace D07.Ch16.QuotientsIsomorphism

open Specs.D07.Ch16.QuotientsIsomorphism

theorem quotientOperations : QuotientOperations.{u, v} := by
  intro R _ M _ _ N
  exact ⟨N.mkQ.map_add, fun r x => (N.mkQ.map_smul r x).symm,
    { one_smul := one_smul R
      mul_smul := mul_smul
      add_smul := add_smul
      smul_add := smul_add }⟩

theorem representativeIndependence : RepresentativeIndependence.{u, v} := by
  intro R _ M _ _ N r x y
  constructor
  · intro hxy
    have h : r • x - r • y ∈ N := by
      rw [← smul_sub]
      exact N.smul_mem r hxy
    exact ⟨h, (Submodule.Quotient.eq N).mpr h⟩
  · intro n hn
    rw [smul_add, map_add]
    have h : N.mkQ (r • n) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (N.smul_mem r hn)
    rw [h, add_zero]

theorem quotientProjection : QuotientProjection.{u, v} := by
  intro R _ M _ _ N
  exact ⟨N.mkQ_surjective, N.ker_mkQ, fun _ _ => Submodule.Quotient.eq N⟩

theorem quotientLift : QuotientLift.{u, v, w} := by
  intro R _ M _ _ L _ _ N f hN
  refine ⟨N.liftQ f hN, fun _ => rfl, N.liftQ_mkQ f hN, ?_⟩
  intro h hh
  apply Submodule.linearMap_qext
  exact hh.trans (N.liftQ_mkQ f hN).symm

theorem kernelCosets : KernelCosets.{u, v, w} := by
  intro R _ M _ _ L _ _ f x y
  change f x = f y ↔ f (x - y) = 0
  rw [map_sub, sub_eq_zero]

theorem firstIsomorphism : FirstIsomorphism.{u, v, w} := by
  intro R _ M _ _ L _ _ f
  exact ⟨f.quotKerEquivRange, fun _ => rfl⟩

theorem generatorPresentation : GeneratorPresentation.{u, v} := by
  intro R _ M _ _ m
  exact ⟨fun _ => rfl, fun _ => Iff.rfl, rfl, Iff.rfl⟩

theorem cyclicQuotient : CyclicQuotient.{u, v} := by
  intro R _ M _ _ m hm
  exact ⟨(LinearMap.toSpanSingleton R M m).quotKerEquivOfSurjective hm,
    fun _ => rfl⟩

/-- The standard action sends e₁ to the first column, over any ring. -/
theorem matrix_smul_firstVector {F : Type u} [Ring F]
    (A : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    (A • firstVector F) i = A i 0 := by
  change (Matrix.mulVec A (Pi.single 0 1)) i = A i 0
  rw [Matrix.mulVec_single_one]
  rfl

theorem matrixGenerator : MatrixGenerator.{u} := by
  intro F _ v
  let A : Matrix (Fin 2) (Fin 2) F := fun i j => if j = 0 then v i else 0
  refine ⟨A, ?_⟩
  funext i
  rw [matrix_smul_firstVector]
  simp [A]

theorem matrixAnnihilator : MatrixAnnihilator.{u} := by
  intro F _ A
  constructor
  · change (A • firstVector F = 0) ↔ _
    constructor
    · intro h i
      simpa only [matrix_smul_firstVector, Pi.zero_apply] using congrFun h i
    · intro h
      funext i
      exact (matrix_smul_firstVector A i).trans (h i)
  · intro B C hC
    exact (generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F)).mul_mem_left B hC

theorem matrixAnnihilatorNotTwoSided : MatrixAnnihilatorNotTwoSided.{u} := by
  intro F _
  have hmem : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F) ∈ generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F) := by
    apply (matrixAnnihilator F _).1.mpr
    intro i
    simp
  have hprod : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F) * Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : F) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F) := by
    exact (D07.Ch08.MatrixRing.matrixUnitProduct F 2 0 1 1 0).trans (ite_eq_left rfl)
  have hnot : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F) ∉ generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F) := by
    intro h
    have hentry := (matrixAnnihilator F _).1.mp h 0
    simp at hentry
  have hright : ¬ Specs.D07.Ch08.IdealDefinition.IsRightIdeal
      (generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F)).toAddSubgroup := by
    intro h
    apply hnot
    rw [← hprod]
    exact h _ _ hmem
  refine ⟨hmem, hprod, hnot, hright, ?_⟩
  intro htwo
  apply hright
  intro A B hA
  exact htwo.mul_mem_of_left B hA

end D07.Ch16.QuotientsIsomorphism
