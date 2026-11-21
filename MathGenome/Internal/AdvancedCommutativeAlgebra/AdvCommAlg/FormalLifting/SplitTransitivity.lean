import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SquareZeroLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Transitivity
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplitTransitivity
import Mathlib.Algebra.TrivSqZeroExt.Ideal

namespace AdvCommAlg.FormalLifting

universe u v w z
noncomputable section
open scoped TensorProduct
open Specs.AdvCommAlg.Differentials.SquareZero
attribute [local instance] rightModule central rightTower

section Extension
variable {A : Type u} {B : Type v} {D : Type w} {M : Type z}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D]
variable [AddCommGroup M] [Module D M] [Module B M] [Module A M]
variable [IsScalarTower B D M] [IsScalarTower A D M]

/-- Formal smoothness extends every derivation on the intermediate algebra,
with the coefficient action restricted from the top algebra. -/
theorem exists_derivation_extension (h : FormallySmooth B D) (d : Derivation A B M) :
    ∃ δ : Derivation A D M, ∀ b : B, δ (algebraMap B D b) = d b := by
  let g : B →ₐ[A] TrivSqZeroExt D M :=
    { toFun := fun b => (algebraMap B D b, d b)
      map_one' := by apply TrivSqZeroExt.ext <;> simp
      map_zero' := by apply TrivSqZeroExt.ext <;> simp
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact map_add _ x y
        · exact d.map_add x y
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · exact map_mul _ x y
        · change d (x * y) = algebraMap B D x • d y + algebraMap B D y • d x
          simpa only [algebraMap_smul] using d.leibniz x y
      commutes' := by
        intro a
        apply TrivSqZeroExt.ext
        · exact (IsScalarTower.algebraMap_apply A B D a).symm
        · exact d.map_algebraMap a }
  let : Algebra B (TrivSqZeroExt D M) := g.toRingHom.toAlgebra
  let : SMul B (TrivSqZeroExt D M) := g.toRingHom.toAlgebra.toSMul
  let : IsScalarTower A B (TrivSqZeroExt D M) :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := B)
      (A := TrivSqZeroExt D M) (by apply RingHom.ext; intro a; exact (g.commutes a).symm)
  let p : TrivSqZeroExt D M →ₐ[B] D :=
    { (TrivSqZeroExt.fstHom A D M).toRingHom with
      commutes' := fun b => rfl }
  have hp : Function.Surjective p := fun x => ⟨(x, 0), rfl⟩
  have hker : IsNilpotent (RingHom.ker p.toRingHom) := by
    refine ⟨2, ?_⟩
    exact TrivSqZeroExt.kerIdeal_sq D M
  let : Algebra.FormallySmooth B D := (formallySmooth_iff B D).mp h
  let s : D →ₐ[B] TrivSqZeroExt D M :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id B D) p hp hker
  have hs : p.comp s = AlgHom.id B D := by
    ext x
    exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id B D) p hp hker x
  let sA : D →ₐ[A] TrivSqZeroExt D M := s.restrictScalars A
  have hsA : (TrivSqZeroExt.fstHom A D M).comp sA = AlgHom.id A D := by
    ext x
    exact congrArg (fun f : D →ₐ[B] D => f x) hs
  refine ⟨AdvCommAlg.Differentials.sectionDerivation ⟨sA, hsA⟩, ?_⟩
  intro b
  change (s (algebraMap B D b)).snd = d b
  rw [s.commutes]
  rfl

end Extension

/-- The retraction is obtained by extending `b ↦ 1 ⊗ db` and applying the
universal property of differentials. -/
theorem exists_transitivity_retraction
    (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D]
    (h : FormallySmooth B D) :
    ∃ r : KaehlerDifferential A D →ₗ[D] D ⊗[B] KaehlerDifferential A B,
      r.comp (KaehlerDifferential.mapBaseChange A B D) = LinearMap.id := by
  let M := D ⊗[B] KaehlerDifferential A B
  let j : KaehlerDifferential A B →ₗ[B] M :=
    TensorProduct.mk B D (KaehlerDifferential A B) 1
  let d : Derivation A B M := j.compDer (KaehlerDifferential.D A B)
  obtain ⟨δ, hδ⟩ := exists_derivation_extension h d
  refine ⟨δ.liftKaehlerDifferential, ?_⟩
  apply LinearMap.restrictScalars_injective B
  apply TensorProduct.ext'
  intro c ω
  change δ.liftKaehlerDifferential
    (KaehlerDifferential.mapBaseChange A B D (c ⊗ₜ[B] ω)) = c ⊗ₜ[B] ω
  rw [KaehlerDifferential.mapBaseChange_tmul, map_smul]
  have hw : ∀ ω : KaehlerDifferential A B,
      δ.liftKaehlerDifferential (KaehlerDifferential.map A A B D ω) = j ω := by
    have he : (δ.liftKaehlerDifferential.restrictScalars B).comp
        (KaehlerDifferential.map A A B D) = j := by
      apply Derivation.liftKaehlerDifferential_unique
      ext b
      change δ.liftKaehlerDifferential
        (KaehlerDifferential.map A A B D (KaehlerDifferential.D A B b)) =
        j (KaehlerDifferential.D A B b)
      rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
      exact hδ b
    exact LinearMap.congr_fun he
  rw [hw]
  change c • (1 ⊗ₜ[B] ω) = c ⊗ₜ[B] ω
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- FL-13: the canonical transitivity sequence is split short exact whenever
its second algebra stage is formally smooth. -/
theorem split_transitivity :
    Specs.AdvCommAlg.FormalLifting.splitTransitivity.{u,v,w} := by
  intro A B D _ _ _ _ _ _ _ h
  obtain ⟨r, hr⟩ := exists_transitivity_retraction A B D h
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B D) := by
    have hleft : Function.LeftInverse r (KaehlerDifferential.mapBaseChange A B D) :=
      fun x => LinearMap.congr_fun hr x
    exact hleft.injective
  obtain ⟨he, hs⟩ := AdvCommAlg.Differentials.transitivity_exact A B D
  exact ⟨hinj, he, hs, r, hr⟩

end
end AdvCommAlg.FormalLifting
