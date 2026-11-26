import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ProjectiveDimensionWithIsolatedSupport
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DepthBoundForFreeComplexes
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalizationBound
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Finiteness.Small

/-! Projective dimension and isolated support. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AdvCommAlg AdvCommAlg.CohenMacaulay
open scoped TensorProduct
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch12.TorBaseChange (coefficientComplex commutativeTor)

namespace CommutativeAlgebraNotes.Intersection.ProjectiveDimensionWithIsolatedSupport

universe u v w

variable {R : Type u} [CommRing R]

private theorem exists_projectiveDimension_eq_nat (M : ModuleCat.{u} R) [Nontrivial M]
    (hpd : projectiveDimension M ≠ ⊤) :
    ∃ s : ℕ, projectiveDimension M = (s : WithBot ℕ∞) := by
  have hbot : projectiveDimension M ≠ ⊥ := fun h =>
    not_subsingleton M (ModuleCat.subsingleton_of_isZero ((projectiveDimension_eq_bot_iff M).mp h))
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hpfin : p ≠ ⊤ := by
    intro h
    apply hpd
    rw [← hp, h, WithBot.coe_top]
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hpfin
  exact ⟨s, by simpa only [← hs, ENat.WithBot.coe_eq_natCast] using hp.symm⟩

/-- The underlying augmented resolution for the ordinary Tor comparison. -/
private def ordinaryResolution {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    LeftResolution R M where
  complex := P.complex
  ε := (P.π.f 0).hom
  surjective := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance
  exact_zero := P.exact₀.moduleCat_range_eq_ker
  exact_succ i := (P.exact_succ i).moduleCat_range_eq_ker

open private categoricalHomologyEquiv koszulTensorOrderIso
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

/-- The depth bound for a finite free complex applied to a minimal resolution. -/
private theorem depth_le_projectiveDimension_sameUniverse [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hlength : IsFiniteLength R (M ⊗[R] N)) (hpd : projectiveDimension M ≠ ⊤) :
    (Depth.depth R N : WithBot ℕ∞) ≤ projectiveDimension M := by
  obtain ⟨s, hs⟩ := exists_projectiveDimension_eq_nat M hpd
  rw [hs, ← ENat.WithBot.coe_eq_natCast, WithBot.coe_le_coe]
  obtain ⟨P, hP⟩ := exists_minimalFreeResolution M
  let Q := ordinaryResolution P
  have hQ : Q.IsProjective := fun i => by
    change Module.Projective R (P.complex.X i)
    infer_instance
  let K := ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e (i : ℕ) : K.homology i ≃ₗ[R] IsolatedTorSupport.Tor M N i :=
    (((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (koszulTensorOrderIso N P.complex)).toLinearEquiv.trans
        (categoricalHomologyEquiv (coefficientComplex (S := R) Q.complex N) i)).trans
      (IsolatedTorSupport.torLeftEquiv M N Q hQ i).symm
  refine depth_le_length_of_finite_free_complex P.complex s N hP.free hP.finite ?_ ?_ ?_
  · intro i hi
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (minimalFreeResolution_vanishes_above M P hP s hs.le i hi)
  · intro i
    exact (e i).symm.isFiniteLength (IsolatedTorSupport.tor_finite_length_of_tensor M N hlength i)
  · have := IsolatedTorSupport.tensor_nontrivial M N
    exact ⟨0, ((e 0).trans (IsolatedTorSupport.torZeroEquiv M N)).symm.injective.nontrivial⟩

/-- Finite projective dimension bounds the depth of the other module. -/
theorem depth_le_projectiveDimension : Specs.depthBoundType.{u,v,w} := by
  intro R _ _ _ M N _ _ _ _ hlength hpd
  let : Small.{u} M := Module.Finite.small R M
  let : Small.{u} N := Module.Finite.small R N
  let M₀ := ModuleCat.of R (Shrink.{u} M)
  let N₀ := ModuleCat.of R (Shrink.{u} N)
  let eM : M₀ ≃ₗ[R] M := Shrink.linearEquiv R M
  let eN : N₀ ≃ₗ[R] N := Shrink.linearEquiv R N
  have : Module.Finite R M₀ := Module.Finite.equiv eM.symm
  have : Module.Finite R N₀ := Module.Finite.equiv eN.symm
  have : Nontrivial M₀ := eM.symm.injective.nontrivial
  have : Nontrivial N₀ := eN.symm.injective.nontrivial
  have hp := ModuleCat.projectiveDimension_eq_of_linearEquiv eM
  rw [← Depth.depth_eq_of_linearEquiv eN, ← hp]
  exact depth_le_projectiveDimension_sameUniverse M₀ N₀
    ((TensorProduct.congr eM.symm eN.symm).isFiniteLength hlength) (hp.trans_ne hpd)

/-- For a Cohen–Macaulay module, its support dimension equals its depth. -/
theorem dimension_le_projectiveDimension_of_cohenMacaulay :
    Specs.cohenMacaulayDimensionBoundType.{u,v,w} := by
  intro R _ _ _ M N _ _ _ _ hlength hpd hCM
  rw [← hCM]
  exact depth_le_projectiveDimension M N hlength hpd

/-- Serre's bound and Auslander–Buchsbaum give the dimension inequality in every
characteristic over a regular local ring. -/
theorem dimension_le_projectiveDimension_of_regularLocalRing :
    Specs.regularLocalDimensionBoundType.{u,v,w} := by
  intro R _ _ M N _ _ _ _ hlength
  let d := (IsLocalRing.maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  let : Small.{u} M := Module.Finite.small R M
  let M₀ := ModuleCat.of R (Shrink.{u} M)
  let eM : M₀ ≃ₗ[R] M := Shrink.linearEquiv R M
  have : Module.Finite R M₀ := Module.Finite.equiv eM.symm
  have : Nontrivial M₀ := eM.symm.injective.nontrivial
  have hpd : projectiveDimension M₀ ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by
        rw [← ENat.WithBot.coe_eq_natCast, ← WithBot.coe_top, ne_eq, WithBot.coe_eq_coe]
        exact ENat.natCast_ne_top d)
      (regularLocal_projectiveDimension_le R M₀ d hd)
  obtain ⟨s, hs⟩ := exists_projectiveDimension_eq_nat M₀ hpd
  obtain ⟨t, ht⟩ := Depth.exists_depth_eq_nat M₀
  have hdim := SerreIntersectionDimension.dimensionBound R M N hlength
  change ringKrullDim (R ⧸ Module.annihilator R M) +
    ringKrullDim (R ⧸ Module.annihilator R N) ≤ ringKrullDim R at hdim
  rw [← Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    ← Module.supportDim_eq_ringKrullDim_quotient_annihilator] at hdim
  have hdepth : (t : WithBot ℕ∞) ≤ Module.supportDim R M := by
    simpa only [← Depth.depth_eq_of_linearEquiv eM, ht, ENat.WithBot.coe_eq_natCast] using
      Depth.depth_le_supportDim (R := R) M
  have hAB := Depth.auslanderBuchsbaum M₀ s hs
  rw [ht, depth_self_eq_dimension d (regularLocal_cohenMacaulay R) hd] at hAB
  have hsdt : (s : WithBot ℕ∞) + t = ringKrullDim R := by
    simpa only [WithBot.coe_add, ENat.WithBot.coe_eq_natCast, ← hd] using
      congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hAB
  rw [← ModuleCat.projectiveDimension_eq_of_linearEquiv eM, hs]
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := t)).mp
  calc
    Module.supportDim R N + t ≤ Module.supportDim R N + Module.supportDim R M :=
      add_le_add (le_refl _) hdepth
    _ ≤ ringKrullDim R := by simpa only [add_comm] using hdim
    _ = (s : WithBot ℕ∞) + t := hsdt.symm

end CommutativeAlgebraNotes.Intersection.ProjectiveDimensionWithIsolatedSupport
