import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AdoComplexReal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SemidirectFaithfulModule
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section

namespace LieAlgebrasAndRepresentations.AdoComplexReal

universe u

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.AdoComplexReal
open Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem reductive_prod_of_semisimple_of_abelian
    {S T : Type u} [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
    [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
    (hS : SolvableRadical.IsSemisimple_value ℂ S) :
    Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition.IsReductive_value ℂ (S × T) := by
  change LieAlgebra.radical ℂ (S × T) = LieAlgebra.center ℂ (S × T)
  let R := LieAlgebra.radical ℂ (S × T)
  let p := LieHom.fst ℂ S T
  let J := R.map p
  let f : R →ₗ⁅ℂ⁆ J :=
    { (p.toLinearMap.comp R.incl.toLinearMap).codRestrict J.toSubmodule
        (fun x => LieIdeal.mem_map x.property) with
      map_lie' := by
        intro x y
        apply Subtype.ext
        exact p.map_lie (x : S × T) (y : S × T) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective (LieHom.fst_surjective (R := ℂ)) y.property
    exact ⟨x, Subtype.ext hx⟩
  let _ : LieAlgebra.IsSolvable R := LieAlgebra.radicalIsSolvable ℂ (S × T)
  have hJ := (LieAlgebra.LieIdeal.solvable_iff_le_radical ℂ S J).mp hf.lieAlgebra_isSolvable
  change LieAlgebra.radical ℂ S = ⊥ at hS
  rw [hS] at hJ
  refine le_antisymm ?_ (LieAlgebra.center_le_radical ℂ (S × T))
  intro x hx y
  have hx₁ : x.1 = 0 := by
    exact (LieSubmodule.mem_bot (R := ℂ) (L := S) x.1).mp
      (hJ (LieIdeal.mem_map (f := p) hx))
  change (⁅y.1, x.1⁆, ⁅y.2, x.2⁆) = (0, 0)
  rw [hx₁, lie_zero, trivial_lie_zero T T]

/-- Restrict the faithful action of the reductive–nilpotent enlargement. -/
theorem complexAdo : complexAdoType.{u} := by
  intro G _ _ _
  obtain ⟨E⟩ := ReductiveNilpotentEnlargement.enlargement G
  let _ : LieRing.IsNilpotent E.N := E.nilpotent
  obtain ⟨V, hVadd, hVmod, hVfin, ρ, hρ⟩ :=
    SemidirectFaithfulModule.faithful ℂ (E.S × E.T) E.N
      (reductive_prod_of_semisimple_of_abelian E.semisimple) E.action
  let _ : LieRing ((E.S × E.T) × E.N) := semidirect_lie_ring_value E.action
  let _ : LieAlgebra ℂ ((E.S × E.T) × E.N) := semidirect_lie_algebra_value E.action
  let _ := hVadd
  let _ := hVmod
  let e : ((E.S × E.T) × E.N) ≃ₗ⁅ℂ⁆ (E.N ⋊⁅E.action⁆ (E.S × E.T)) :=
    (semidirectCoordinates E.action).lieEquiv ℂ
  let σ : ((E.S × E.T) × E.N) →ₗ⁅ℂ⁆ Module.End ℂ V := ρ
  exact ⟨V, hVadd, hVmod, hVfin, σ.comp (e.symm.toLieHom.comp E.embedding),
    hρ.comp (e.symm.injective.comp E.injective)⟩

/-- The real Lie homomorphism into the complexification sends `x` to `1 ⊗ₜ x`. -/
private def complexificationInclusion (G : Type u) [LieRing G] [LieAlgebra ℝ G] :
    G →ₗ⁅ℝ⁆ (ℂ ⊗[ℝ] G) where
  toLinearMap := TensorProduct.mk ℝ ℂ G 1
  map_lie' := by
    intro x y
    change (1 : ℂ) ⊗ₜ[ℝ] ⁅x, y⁆ = ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

private theorem complexificationInclusion_injective
    (G : Type u) [LieRing G] [LieAlgebra ℝ G] :
    Function.Injective (complexificationInclusion G) := by
  let projection : (ℂ ⊗[ℝ] G) →ₗ[ℝ] G :=
    (TensorProduct.lid ℝ G).toLinearMap.comp (Complex.reLm.rTensor G)
  have hleft : Function.LeftInverse projection (complexificationInclusion G) := by
    intro x
    change projection ((1 : ℂ) ⊗ₜ[ℝ] x) = x
    simp [projection]
  exact hleft.injective

/-- Restrict a complex representation to real scalars on the complexification
and on its representation space. -/
private def realRepresentation
    {G V : Type u} [LieRing G] [LieAlgebra ℝ G] [AddCommGroup V] [Module ℂ V]
    (ρ : (ℂ ⊗[ℝ] G) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    (ℂ ⊗[ℝ] G) →ₗ⁅ℝ⁆ Module.End ℝ V where
  toLinearMap :=
    (LinearMap.restrictScalarsₗ ℝ ℂ V V ℝ).comp (ρ.toLinearMap.restrictScalars ℝ)
  map_lie' := by
    intro x y
    apply LinearMap.ext
    intro v
    change ρ ⁅x, y⁆ v = ρ x (ρ y v) - ρ y (ρ x v)
    rw [ρ.map_lie]
    rfl

/-- Complexification and restriction of scalars give the real faithful action. -/
theorem realAdo : realAdoType.{u} := by
  intro G _ _ _
  obtain ⟨V, hVadd, hVmod, hVfin, ρ, hρ⟩ := complexAdo (ℂ ⊗[ℝ] G)
  let _ := hVadd
  let _ := hVmod
  let _ := hVfin
  have hinj : Function.Injective (realRepresentation ρ) := by
    intro x y hxy
    apply hρ
    apply LinearMap.restrictScalars_injective ℝ
    exact hxy
  exact ⟨V, hVadd, inferInstance, inferInstance,
    (realRepresentation ρ).comp (complexificationInclusion G),
    hinj.comp (complexificationInclusion_injective G)⟩

end LieAlgebrasAndRepresentations.AdoComplexReal
