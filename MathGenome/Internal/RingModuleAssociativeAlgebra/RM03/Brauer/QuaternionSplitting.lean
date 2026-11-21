import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.QuaternionSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MaximalSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.D07.Ch23.QuaternionAlgebra
import Mathlib.Algebra.Field.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The complex splitting of the real Hamilton quaternions and its determinant. -/

noncomputable section

namespace RM03.Brauer.QuaternionSplitting

open scoped TensorProduct
open Specs.D07.Ch23.QuaternionAlgebra (H M iH jH kH toH fromH pairMatrix pairNorm)
open Specs.RM03.Brauer.QuaternionSplitting
open D07.Ch23.QuaternionAlgebra (centerReal unitCoordinates toH_fromH matrixRepresentation
  determinantNorm normIdentification fourSquareNorm)

theorem hamilton_central_division : HamiltonCentralDivision := by
  refine (CSA.isCentralDivision_iff ℝ H).2 ⟨inferInstance, ?_⟩
  ext q
  change q ∈ Subalgebra.center ℝ H ↔ ∃ r : ℝ, algebraMap ℝ H r = q
  rw [Subalgebra.mem_center_iff]
  calc
    (∀ p : H, p * q = q * p) ↔ (∀ p : H, q * p = p * q) :=
      forall_congr' fun _ => eq_comm
    _ ↔ ∃ r : ℝ, q = algebraMap ℝ H r := centerReal.1 q
    _ ↔ _ := exists_congr fun _ => eq_comm

private theorem hamilton_degree : CSA.degree ℝ H = 2 := by
  rw [CSA.degree, Quaternion.finrank_eq_four]
  exact Nat.sqrt_eq' 2

private def complexEmbedding : ℂ →ₐ[ℝ] H where
  toFun z := ⟨z.re, z.im, 0, 0⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  commutes' x := by ext <;> simp

theorem complex_subfield : ComplexSubfield := by
  let f := complexEmbedding
  have hinj : Function.Injective f := f.toRingHom.injective
  have hi : f Complex.I = iH := by
    ext <;> simp [f, complexEmbedding, iH,
      Specs.D07.Ch08.DomainFieldQuaternionDivisionExample.iH]
  have hrange : f.range = Algebra.adjoin ℝ ({iH} : Set H) := by
    apply le_antisymm
    · rintro q ⟨z, rfl⟩
      have h : f z = algebraMap ℝ H z.re + z.im • iH := by
        calc
          f z = f ((z.re : ℂ) + z.im * Complex.I) := congrArg f (Complex.re_add_im z).symm
          _ = _ := by
            rw [map_add, map_mul, hi, Algebra.smul_def]
            rfl
      change f z ∈ Algebra.adjoin ℝ ({iH} : Set H)
      rw [h]
      apply Subalgebra.add_mem
      · exact Subalgebra.algebraMap_mem _ _
      · exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton iH)) _
    · refine Algebra.adjoin_le_iff.mpr ?_
      rw [Set.singleton_subset_iff, ← hi]
      exact ⟨Complex.I, rfl⟩
  let identify := AlgEquiv.ofInjective f hinj
  have hfield : IsField f.range :=
    identify.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField ℂ)
  have hdim : Module.finrank ℝ f.range = 2 :=
    identify.toLinearEquiv.finrank_eq.symm.trans Complex.finrank_real_complex
  have hmax : CSA.IsMaximalSubfield f.range :=
    (CSA.maximal_subfield_iff_degree hamilton_central_division f.range hfield).2
      (hdim.trans hamilton_degree.symm)
  refine ⟨f, fun _ => rfl, hinj, hrange, hdim, hmax, ?_⟩
  have hsplit := CSA.maximal_subfield_splits hamilton_central_division f.range hmax
  rw [hamilton_degree] at hsplit
  exact hsplit

theorem complex_splitting : ComplexSplitting := by
  have hH : CSA.IsCentralSimple ℝ H :=
    CSA.isCentralSimple_of_isCentralDivision ℝ H hamilton_central_division
  have hBase := CSA.isCentralSimple_baseChange (L := ℂ) hH
  let : IsSimpleRing (CSA.BaseChange ℝ ℂ H) := hBase.1
  let : FiniteDimensional ℂ (CSA.BaseChange ℝ ℂ H) := hBase.2.2
  obtain ⟨f, _, hf⟩ := matrixRepresentation
  let g := AlgHom.liftEquiv ℝ ℂ H M f
  have hinj : Function.Injective g := g.toRingHom.injective
  have hdim : Module.finrank ℂ (CSA.BaseChange ℝ ℂ H) = Module.finrank ℂ M := by
    rw [CSA.finrank_baseChange hH, Quaternion.finrank_eq_four, Module.finrank_matrix]
    simp
  let linearEquiv := LinearEquiv.ofInjectiveOfFinrankEq g.toLinearMap hinj hdim
  let e := AlgEquiv.ofBijective g ⟨hinj, linearEquiv.surjective⟩
  have he (u : ℂ × ℂ) : e (1 ⊗ₜ[ℝ] toH u) = pairMatrix u := by
    change g (1 ⊗ₜ[ℝ] toH u) = _
    simp [g, hf]
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [← unitCoordinates.1, he]
    simp [pairMatrix]
  · rw [← unitCoordinates.2.1, he]
    simp [pairMatrix]
  · intro a b c d
    let q : H := (a : H) + b • iH + c • jH + d • kH
    change (e (1 ⊗ₜ[ℝ] q)).det = _
    rw [← toH_fromH q, he, determinantNorm, (normIdentification (fromH q)).1, toH_fromH]
    exact congrArg Complex.ofReal (fourSquareNorm a b c d)

theorem reduced_norm : ReducedNorm := by
  intro h a b c d
  obtain ⟨e, _, _, hdet⟩ := complex_splitting
  let e' := e.trans (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hamilton_degree.symm))
  apply Complex.ofReal_injective
  change algebraMap ℝ ℂ (CSA.reducedNorm h _) = _
  rw [CSA.reducedNorm_map h _ e']
  change (Matrix.reindexAlgEquiv ℂ ℂ _ (e _)).det = _
  rw [Matrix.det_reindexAlgEquiv]
  exact hdet a b c d

end RM03.Brauer.QuaternionSplitting
