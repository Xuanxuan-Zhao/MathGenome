import MathGenome.Internal.Specs.D07.Ch16.FinitePresentation
import MathGenome.Internal.D07.Ch16.FinitePresentationFiniteRelationsCounterexample
import MathGenome.Internal.D07.Ch16.QuotientsIsomorphism
import MathGenome.Internal.D07.Ch16.PidSubmodulesFinite
import MathGenome.Internal.D07.Ch16.SubmoduleFree

universe u v
noncomputable section
namespace D07.Ch16.FinitePresentation
open Specs.D07.Ch16.FinitePresentation

theorem finitePresentationCriterion : FinitePresentationCriterion.{u, v} := by
  intro R _ M _ _
  constructor
  · intro h
    let := h
    obtain ⟨n, m, π, A, hπ, hA⟩ := Module.FinitePresentation.exists_fin' R M
    refine ⟨n, π, hπ, ?_⟩
    rw [LinearMap.exact_iff.mp hA]
    exact Submodule.fg_range A
  · rintro ⟨n, π, hπ, hker⟩
    exact Module.finitePresentation_of_free_of_surjective π hπ hker

theorem matrixColumns : MatrixColumns.{u} := by
  intro R _ n m A
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    simp [matrixMap, Module.Basis.constr_apply_fintype, Finset.sum_apply]
  · intro j
    simpa only [matrixMap, Pi.basisFun_apply] using
      (Pi.basisFun R (Fin m)).constr_basis ℕ (fun j i => A i j) j
  · exact (Pi.basisFun R (Fin m)).constr_range ℕ

/-- Commutativity turns left coefficients into the usual matrix action. -/
theorem matrixMapAgreement : MatrixMapAgreement.{u} := by
  intro R _ n m A
  apply LinearMap.ext
  intro x
  funext i
  rw [(matrixColumns R n m A).1 x i]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem presentationMatrix : PresentationMatrix.{u, v} := by
  intro R _ M _ _ n π hπ hker
  obtain ⟨m, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R _).mp hker
  let A : Matrix (Fin n) (Fin m) R := fun i j => f (Pi.single j 1) i
  have hA : matrixMap A = f := by
    simpa only [matrixMap, A, Pi.basisFun_apply] using
      (Pi.basisFun R (Fin m)).constr_self ℕ f
  have heq : LinearMap.range (matrixMap A) = LinearMap.ker π := hA ▸ hf
  refine ⟨m, A, heq, ?_⟩
  rw [heq]
  refine ⟨(π.quotKerEquivOfSurjective hπ).symm, ?_⟩
  intro x
  apply (π.quotKerEquivOfSurjective hπ).injective
  simp

theorem cokernelPresentation : CokernelPresentation.{u} := by
  intro R _ n m A
  let N := LinearMap.range (matrixMap A)
  have hfg : N.FG := Submodule.fg_range (matrixMap A)
  exact ⟨N.mkQ_surjective, N.ker_mkQ, hfg,
    Module.finitePresentation_of_free_of_surjective N.mkQ N.mkQ_surjective
      (by simpa using hfg)⟩

theorem matrixCriterion : MatrixCriterion.{u, v} := by
  intro R _ M _ _
  constructor
  · intro h
    obtain ⟨n, π, hπ, hker⟩ := (finitePresentationCriterion R M).mp h
    obtain ⟨m, A, _, e, _⟩ := presentationMatrix R M n π hπ hker
    exact ⟨n, m, A, ⟨e⟩⟩
  · rintro ⟨n, m, A, ⟨e⟩⟩
    let := (cokernelPresentation R n m A).2.2.2
    exact Module.FinitePresentation.of_equiv e.symm

theorem pidKernelFree : PidKernelFree.{u, v} := by
  intro R _ _ _ M _ _ n π _hπ
  exact D07.Ch16.SubmoduleFree.finiteFree
    R n (Fin n → R) (Pi.basisFun R (Fin n)) (LinearMap.ker π)

theorem pidPresentation : PidPresentation.{u, v} := by
  intro R _ _ _ M _ _ _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  have hf := D07.Ch16.PidSubmodulesFinite.submoduleFinite
    R (Fin n → R) (LinearMap.ker π)
  have hfp := (finitePresentationCriterion R M).mpr
    ⟨n, π, hπ, Module.Finite.iff_fg.mp hf⟩
  exact ⟨hfp, (matrixCriterion R M).mp hfp⟩

theorem finiteGenerationInsufficient : FiniteGenerationInsufficient.{u} := by
  intro k _
  dsimp only
  refine ⟨inferInstance,
    D07.Ch16.FinitePresentationFiniteRelationsCounterexample.residueNotFinitelyPresented k,
    ?_⟩
  intro n π hπ hker
  exact D07.Ch16.FinitePresentationFiniteRelationsCounterexample.idealNotFinitelyGenerated k
    (D07.Ch16.FinitePresentationFiniteRelationsCounterexample.everyPresentation _ _ n π hπ hker)

end D07.Ch16.FinitePresentation
