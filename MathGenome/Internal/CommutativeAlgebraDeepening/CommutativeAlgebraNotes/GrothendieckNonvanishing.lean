import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionDepthDimension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GrothendieckVanishing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PositiveRankTopCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GrothendieckNonvanishing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.Module

open CategoryTheory CategoryTheory.Limits IsLocalRing Order TensorProduct
open scoped TensorProduct

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.GrothendieckNonvanishing (nonvanishingType)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)
open Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion (finiteModules)

universe u

private theorem exists_support_prime_of_full_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] :
    ∃ (d : ℕ) (p : PrimeSpectrum R), p ∈ Module.support R M ∧
      Module.supportDim R M = (d : WithBot ℕ∞) ∧
      ringKrullDim (R ⧸ p.asIdeal) = (d : WithBot ℕ∞) := by
  let : FiniteDimensionalOrder (Module.support R M) :=
    finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Module.supportDim_ne_bot_of_nontrivial R M,
        ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R))
          (Module.supportDim_le_ringKrullDim R M)⟩
  let l := LTSeries.longestOf (Module.support R M)
  let p : PrimeSpectrum R := l.head.1
  have hd : Module.supportDim R M = (l.length : WithBot ℕ∞) :=
    krullDim_eq_length_of_finiteDimensionalOrder
  refine ⟨l.length, p, l.head.2, hd, ?_⟩
  rw [ringKrullDim_quotient]
  apply le_antisymm
  · rw [← hd]
    have hp : Module.annihilator R M ≤ p.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp
        ((Module.support_eq_zeroLocus (R := R) (M := M)) ▸ l.head.2)
    have hclosed : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) ⊆ Module.support R M := by
      rw [Module.support_eq_zeroLocus]
      exact PrimeSpectrum.zeroLocus_anti_mono_ideal hp
    exact krullDim_le_of_strictMono
      (fun q : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) =>
        (⟨q.1, hclosed q.2⟩ : Module.support R M))
      (fun _ _ h => h)
  · let c : LTSeries (PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) :=
      ⟨l.length, (fun i => ⟨(l i).1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (l.head_le i)⟩),
        fun i => l.step i⟩
    exact c.length_le_krullDim

private local instance primeQuotientLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

private theorem quotient_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (p : PrimeSpectrum R) :
    IsAdicComplete (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal) := by
  let B := R ⧸ p.asIdeal
  let f : R →ₗ[R] B := Algebra.linearMap R B
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map (algebraMap R B) = maximalIdeal B :=
    map_maximalIdeal_of_surjective (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  rw [← hmap, IsAdicComplete.map_algebraMap_iff]
  have hcomp : Function.Surjective (AdicCompletion.of (maximalIdeal R) B) := by
    intro x
    obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective (maximalIdeal R) hf x
    obtain ⟨z, rfl⟩ := AdicCompletion.of_surjective (I := maximalIdeal R) (M := R) y
    exact ⟨f z, (AdicCompletion.map_of _ _ _).symm⟩
  let : IsPrecomplete (maximalIdeal R) B := AdicCompletion.of_surjective_iff.mp hcomp
  exact IsAdicComplete.mk

private theorem nontrivial_localCohomology_of_surjective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N : ModuleCat.{u} R} [Module.Finite R M] (g : M ⟶ N) (hg : Function.Surjective g)
    (d : ℕ) (hd : Module.supportDim R M ≤ (d : WithBot ℕ∞))
    (hN : Nontrivial ((localCohomology I (d : ℤ)).obj N)) :
    Nontrivial ((localCohomology I (d : ℤ)).obj M) := by
  let S := g.hom.shortComplexKer
  have hS : S.ShortExact := g.hom.shortExact_shortComplexKer hg
  have hdim : Module.supportDim R S.X₁ ≤ Module.supportDim R M :=
    Module.supportDim_le_of_injective (LinearMap.ker g.hom).subtype Subtype.val_injective
  have hz := grothendieckVanishing I S.X₁ ((d : ℤ) + 1)
    (Or.inr ⟨d, hdim.trans hd, by omega⟩)
  have hex := (localCohomology_exact I hS (d : ℤ)).2.1
  have hs := (ShortComplex.moduleCat_exact_iff _).mp hex.exact
  let := hN
  suffices hsurj : Function.Surjective ((localCohomology I (d : ℤ)).map g) from
    hsurj.nontrivial
  intro x
  exact hs x ((ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _)

private theorem nontrivial_top_localCohomology_of_complete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] :
    ∃ d : ℕ, Module.supportDim R M = (d : WithBot ℕ∞) ∧
      Nontrivial ((localCohomology (maximalIdeal R) (d : ℤ)).obj M) := by
  obtain ⟨d, p, hp, hd, hpdim⟩ := exists_support_prime_of_full_dimension M
  let B := R ⧸ p.asIdeal
  let K := p.asIdeal.ResidueField
  let : IsLocalRing B := inferInstanceAs (IsLocalRing (R ⧸ p.asIdeal))
  let : IsDomain B := inferInstanceAs (IsDomain (R ⧸ p.asIdeal))
  let : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (R ⧸ p.asIdeal))
  let : IsAdicComplete (maximalIdeal B) B := quotient_isAdicComplete p
  let : Field (FractionRing B) := FractionRing.field B
  let N : ModuleCat.{u} B := ModuleCat.of B (B ⊗[R] M)
  let : Module.Finite B N := inferInstanceAs (Module.Finite B (B ⊗[R] M))
  have hfiber : Nontrivial (K ⊗[R] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hp
  have he : (FractionRing B ⊗[B] N) ≃ₗ[B] (K ⊗[R] M) :=
    TensorProduct.congr (FractionRing.algEquiv B K).toLinearEquiv (LinearEquiv.refl B N) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R B K K M).restrictScalars B
  let : Nontrivial (FractionRing B ⊗[B] N) := he.nontrivial_congr.mpr hfiber
  let : Module.Free (FractionRing B) (FractionRing B ⊗[B] N) :=
    Module.Free.of_divisionRing (FractionRing B) (FractionRing B ⊗[B] N)
  have hN := positiveRankTopCohomology (B := B) d hpdim N
    ((Module.finrank_pos_iff_of_free (FractionRing B) (FractionRing B ⊗[B] N)).mpr inferInstance)
  let f : R →+* B := Ideal.Quotient.mk p.asIdeal
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map f = maximalIdeal B := map_maximalIdeal_of_surjective f hf
  obtain ⟨e⟩ := localCohomologyChangeOfRings f (maximalIdeal R) (d : ℤ)
  rw [hmap] at e
  let N₀ := (ModuleCat.restrictScalars f).obj N
  have hN₀ : Nontrivial ((localCohomology (maximalIdeal R) (d : ℤ)).obj N₀) :=
    (e.app N).toLinearEquiv.nontrivial_congr.mpr hN
  let t := TensorProduct.mk R B M 1
  let π : M →ₗ[R] N₀ :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := by
        intro r x
        exact (t.map_smul r x).trans (algebraMap_smul B r (t x)).symm }
  have hπ : Function.Surjective π := TensorProduct.mk_surjective R M B hf
  exact ⟨d, hd, nontrivial_localCohomology_of_surjective (maximalIdeal R)
    (ModuleCat.ofHom π) hπ d hd.le hN₀⟩

/-- Grothendieck nonvanishing for a nonzero finite module over a Noetherian local ring. -/
theorem grothendieckNonvanishing : nonvanishingType.{u} := by
  intro R _ _ _ M _ _
  let A := Completion R
  let Mhat := AdicCompletion (maximalIdeal R) M
  let : IsNoetherianRing A := AdvCommAlg.CohenMacaulay.Specs.completionNoetherian R
  let : Module.Finite A Mhat := AdvCommAlg.CohenMacaulay.Specs.completionFinite R M
  let : Nontrivial Mhat := completion_nontrivial R M
  let X : ModuleCat.{u} A := ModuleCat.of A Mhat
  let : Module.Finite A X := inferInstanceAs (Module.Finite A Mhat)
  obtain ⟨d, hd, hH⟩ := nontrivial_top_localCohomology_of_complete X
  refine ⟨d, (completion_supportDim R M).symm.trans hd, ?_⟩
  obtain ⟨h, ⟨e⟩⟩ := localCohomologyAdicCompletion (R := R) (d : ℤ)
  let M₀ : (finiteModules R).FullSubcategory := ⟨M, inferInstance⟩
  have hmax : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A :=
    AdicCompletion.maximalIdeal_eq_map.symm
  rw [hmax] at e
  exact (e.app M₀).toLinearEquiv.nontrivial_congr.mpr hH

end CommutativeAlgebraNotes
