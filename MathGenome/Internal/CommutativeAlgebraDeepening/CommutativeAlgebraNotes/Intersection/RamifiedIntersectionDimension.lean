import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.RamifiedRegularPresentation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IntersectionEulerCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.UnramifiedIntersection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalDimension
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct nonZeroDivisors
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open P103.Specs.Ch10.Comparison (LeftResolution)

namespace CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension

open IntersectionEulerCompletion
open IntersectionEulerCompletion.Specs (CompletedRing completedModuleCat)
open RegularElementEulerCancellation.Specs (QuotientRing restrict IsBoundedFiniteFree)
open IsolatedIntersectionEuler.Specs (intersectionEuler)

open private leftResolutionOfEquiv
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
open private restrictedTower finiteRestricted tensorRestrictionEquiv
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation
open private baseChangeEquiv baseChange_length baseChange_dimension completion_nontrivial
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
open private dimension_eq_support
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.UnramifiedIntersection

universe u v w

/-- A finite free resolution of a nonzero finite module, allowing the module
and the coefficient ring to have different universe levels. -/
private theorem boundedFiniteFreeResolution {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∃ P : LeftResolution R M, IsBoundedFiniteFree P d := by
  let : Small.{u} M := Module.Finite.small.{u} R M
  let A : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
  let e : A ≃ₗ[R] M := Shrink.linearEquiv R M
  let : Nontrivial A := e.symm.injective.nontrivial
  let : Module.Finite R A := Module.Finite.equiv e.symm
  obtain ⟨depth, hdepth⟩ := AdvCommAlg.Depth.exists_depth_eq_nat A
  obtain ⟨P, hfin, hfree, hbound⟩ :=
    AdvCommAlg.CohenMacaulay.regularLocal_exists_finiteFreeResolution R A d depth hd hdepth
  let F : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R := ModuleCat.uliftFunctor.{v, u} R
  let Q := leftResolutionOfEquiv M (F.obj A) (F.mapProjectiveResolution P)
    (ULift.moduleEquiv.trans e)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i
    let := hfree i
    exact inferInstanceAs (Module.Free R (ULift.{v} (P.complex.X i)))
  · intro i
    let := hfin i
    exact inferInstanceAs (Module.Finite R (ULift.{v} (P.complex.X i)))
  · intro i hi
    let := hbound i ((Nat.sub_le d depth).trans_lt hi)
    exact inferInstanceAs (Subsingleton (ULift.{v} (P.complex.X i)))

private theorem le_of_lt_nat_succ {s : WithBot ℕ∞} {d : ℕ}
    (h : s < ((d + 1 : ℕ) : WithBot ℕ∞)) : s ≤ (d : WithBot ℕ∞) := by
  cases s using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe s =>
    have hs : s < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
    apply WithBot.coe_le_coe.mpr
    cases s using ENat.recTopCoe with
    | top => exact (not_top_lt hs).elim
    | coe n =>
      exact ENat.natCast_le_natCast.mpr (Nat.le_of_lt_succ (ENat.natCast_lt_natCast.mp hs))

private theorem dimension_restrict {S : Type u} [CommRing S] (h : S)
    (L : ModuleCat.{v} (QuotientRing h)) [Module.Finite (QuotientRing h) L] :
    moduleDimensionValue S (restrict h L) = moduleDimensionValue (QuotientRing h) L := by
  let A := QuotientRing h
  let : Module.Finite S (restrict h L) := finiteRestricted h L
  let : Module.Finite A (restrict h L) := inferInstanceAs (Module.Finite A L)
  let : IsScalarTower S A (restrict h L) := restrictedTower h L
  rw [dimension_eq_support, dimension_eq_support]
  exact AdvCommAlg.CohenMacaulay.supportDim_of_surjective_algebraMap S A
    (restrict h L) Ideal.Quotient.mk_surjective

/-- Euler cancellation excludes equality in the ambient unramified bound. -/
private theorem quotient_dimension_bound {S : Type u} [CommRing S] [IsRegularLocalRing S]
    [CharZero S] (p d : ℕ) (hp : p.Prime) [CharP (ResidueField S) p]
    (hdS : ringKrullDim S = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hpS : (p : S) ∉ maximalIdeal S ^ 2)
    (h : S) (hm : h ∈ maximalIdeal S) (hreg : h ∈ S⁰)
    [IsRegularLocalRing (QuotientRing h)]
    (hdA : ringKrullDim (QuotientRing h) = (d : WithBot ℕ∞))
    (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] [Module.Finite (QuotientRing h) N]
    [Nontrivial M] [Nontrivial N] (hlen : IsFiniteLength (QuotientRing h) (M ⊗[QuotientRing h] N)) :
    moduleDimensionValue (QuotientRing h) M + moduleDimensionValue (QuotientRing h) N ≤
      (d : WithBot ℕ∞) := by
  let A := QuotientRing h
  let : Module.Finite S (restrict h M) := finiteRestricted h M
  let : Module.Finite S (restrict h N) := finiteRestricted h N
  let : Nontrivial (restrict h M) := inferInstanceAs (Nontrivial M)
  let : Nontrivial (restrict h N) := inferInstanceAs (Nontrivial N)
  have hlenS : IsFiniteLength S (restrict h M ⊗[S] restrict h N) := by
    apply Module.length_ne_top_iff.mp
    rw [← (tensorRestrictionEquiv h M N).length_eq,
      Module.length_eq_of_surjective (R := A) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top_iff.mpr hlen
  obtain ⟨P, hP⟩ := boundedFiniteFreeResolution M d hdA
  obtain ⟨Q, hQ⟩ := boundedFiniteFreeResolution (restrict h N) (d + 1) hdS
  have hz : intersectionEuler (restrict h M) (restrict h N) = 0 :=
    RegularElementEulerCancellation.intersection_euler_zero h hm hreg M N hlen
      P Q d (d + 1) hP hQ
  obtain ⟨hle, _, hpos⟩ := UnramifiedIntersection.unramifiedIntersection S p (d + 1) hp
    hdS hpS (restrict h M) (restrict h N) hlenS
  have hlt := lt_of_le_of_ne hle (fun he => (lt_irrefl (0 : ℤ)) (hz ▸ hpos he))
  rw [← dimension_restrict h M, ← dimension_restrict h N]
  exact le_of_lt_nat_succ hlt

private theorem complete_dimension_bound (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [CharZero R] [IsAdicComplete (maximalIdeal R) R]
    (p d : ℕ) (hp : p.Prime) [CharP (ResidueField R) p]
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hram : (p : R) ∈ maximalIdeal R ^ 2)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hlen : IsFiniteLength R (M ⊗[R] N)) :
    moduleDimensionValue R M + moduleDimensionValue R N ≤ (d : WithBot ℕ∞) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, _, _, _, _, _, _, _, _, _, _, _, hpowerSeries⟩ :=
    CoefficientRings.ramifiedRegularPresentation R p d hd hram
  let S := MvPowerSeries (Fin d) V
  obtain ⟨_, hregS, _, hcharS, hresS, hdS, _, hpS, hpresentation⟩ := hpowerSeries
  obtain ⟨_, _, _, _, _, _, _, _, f, _, hquotient⟩ := hpresentation
  let h : S := (p : S) - f
  let A := QuotientRing h
  obtain ⟨hhreg, hhm, _, _, hregA, _, hdA, E, _⟩ := hquotient
  let : IsRegularLocalRing S := hregS
  let : CharZero S := hcharS
  let : CharP (ResidueField S) p := hresS
  let : IsRegularLocalRing A := hregA
  let : Algebra R A := E.symm.toRingHom.toAlgebra
  have hb : Function.Bijective (algebraMap R A) := E.symm.bijective
  let M' := ModuleCat.of A (A ⊗[R] M)
  let N' := ModuleCat.of A (A ⊗[R] N)
  let : Module.Finite A M' := inferInstanceAs (Module.Finite A (A ⊗[R] M))
  let : Module.Finite A N' := inferInstanceAs (Module.Finite A (A ⊗[R] N))
  let : Nontrivial M' := (baseChangeEquiv hb M).injective.nontrivial
  let : Nontrivial N' := (baseChangeEquiv hb N).injective.nontrivial
  have hlen' : IsFiniteLength A (M' ⊗[A] N') := by
    apply Module.length_ne_top_iff.mp
    rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).length_eq,
      baseChange_length hb]
    exact Module.length_ne_top_iff.mpr hlen
  have hs := quotient_dimension_bound p d hp hdS hpS h hhm hhreg hdA M' N' hlen'
  have hdimM : moduleDimensionValue A M' = moduleDimensionValue R M :=
    baseChange_dimension E.symm rfl M
  have hdimN : moduleDimensionValue A N' = moduleDimensionValue R N :=
    baseChange_dimension E.symm rfl N
  change moduleDimensionValue A M' + moduleDimensionValue A N' ≤ (d : WithBot ℕ∞) at hs
  simpa only [hdimM, hdimN] using hs

/-- Serre's dimension bound for isolated intersections in the ramified case. -/
theorem ramifiedIntersectionDimension : Specs.ramifiedIntersectionDimensionType.{u,v,w} := by
  intro R _ _ _ p d hp _ hd hram M N _ _ _ _ hlen
  let C := CompletedRing R
  let : IsRegularLocalRing C := completion_regular_local R
  let : Module.FaithfullyFlat R C := AdvCommAlg.CohenMacaulay.completion_faithfullyFlat R
  let : CharZero C := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective R C)
  let : CharP (ResidueField C) p := charP_of_injective_ringHom
    (AdicCompletion.residueField_map_bijective R).injective p
  have hramC : (p : C) ∈ maximalIdeal C ^ 2 := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← map_natCast (algebraMap R C)]
    exact Ideal.mem_map_of_mem _ hram
  let Mc := completedModuleCat M
  let Nc := completedModuleCat N
  let : Module.Finite C Mc := completion_module_finite R M
  let : Module.Finite C Nc := completion_module_finite R N
  let : Nontrivial Mc := completion_nontrivial M
  let : Nontrivial Nc := completion_nontrivial N
  have hdimM : moduleDimensionValue C Mc = moduleDimensionValue R M :=
    (dimension_eq_support C Mc).trans
      ((completion_module_dimension R M).trans (dimension_eq_support R M).symm)
  have hdimN : moduleDimensionValue C Nc = moduleDimensionValue R N :=
    (dimension_eq_support C Nc).trans
      ((completion_module_dimension R N).trans (dimension_eq_support R N).symm)
  have hs := complete_dimension_bound C p d hp ((completion_ring_dimension R).trans hd)
    hramC Mc Nc (completion_tensor_finite_length M N hlen)
  simpa only [hdimM, hdimN] using hs

end CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension
