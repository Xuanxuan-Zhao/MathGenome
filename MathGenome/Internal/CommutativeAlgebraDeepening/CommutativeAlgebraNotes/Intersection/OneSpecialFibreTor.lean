import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.AlgebraCore.P103.Ch12.TorBaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.RegularQuotientProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.RegularLocalLowDimension

noncomputable section

open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch12.TorBaseChange
open P103.Ch12.TorBaseChange (additiveHomologyEquiv firstTorEquiv homologyIso)
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
open AdvCommAlg (regularQuotientFunctor)

namespace CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor

open OneSpecialFibreTor.Specs (SpecialFibre killedModule reduceModule reducedTor)

universe u
variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Reduce every term and the augmentation of a free resolution modulo a regular scalar. -/
private def quotientResolution (x : R) {N : ModuleCat.{u} R}
    (Q : LeftResolution R N) (hQ : Q.IsFree)
    (hxR : IsSMulRegular R x) (hxN : IsSMulRegular N x) :
    LeftResolution (SpecialFibre x) (reduceModule x N) where
  complex := ((regularQuotientFunctor x).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  ε := ((regularQuotientFunctor x).map (ModuleCat.ofHom Q.ε)).hom
  surjective := QuotSMulTop.map_surjective x Q.surjective
  exact_zero := by
    have h := QuotSMulTop.map_exact x (LinearMap.exact_iff.mpr Q.exact_zero.symm) Q.surjective
    ext z
    exact (h z).symm
  exact_succ n := by
    suffices hred : Function.Exact
        (QuotSMulTop.map x (Q.complex.d (n + 2) (n + 1)).hom)
        (QuotSMulTop.map x (Q.complex.d (n + 1) n).hom) by
      ext z
      exact (hred z).symm
    have h := LinearMap.exact_iff.mpr (Q.exact_succ n).symm
    cases n with
    | zero =>
      exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        h (LinearMap.exact_iff.mpr Q.exact_zero.symm) hxN
    | succ n =>
      letI := hQ n
      exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        h (LinearMap.exact_iff.mpr (Q.exact_succ n).symm) (AdvCommAlg.regular_on_free x hxR _)

theorem reduced_resolution : Specs.reducedResolution.{u} := by
  intro R _ x N Q b hxR hxN hQ hbounded
  refine ⟨quotientResolution x Q (fun i => (hQ i).2) hxR hxN, rfl, HEq.rfl, ?_, ?_⟩
  · intro i
    letI := (hQ i).1
    letI := (hQ i).2
    exact ⟨AdvCommAlg.regularQuotient_finite x (Q.complex.X i),
      inferInstanceAs (Module.Free (SpecialFibre x) (QuotSMulTop x (Q.complex.X i)))⟩
  · intro i hi
    letI := hbounded i hi
    exact inferInstanceAs (Subsingleton (QuotSMulTop x (Q.complex.X i)))

private theorem exists_bounded_free_resolution [IsRegularLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] :
    ∃ (Q : LeftResolution R N) (b : ℕ),
      (∀ i, Module.Finite R (Q.complex.X i) ∧ Module.Free R (Q.complex.X i)) ∧
        (∀ i, b < i → Subsingleton (Q.complex.X i)) := by
  obtain ⟨P, hP⟩ := AdvCommAlg.exists_minimalFreeResolution N
  let b := (IsLocalRing.maximalIdeal R).spanFinrank
  have hb : ringKrullDim R = (b : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hbound := AdvCommAlg.CohenMacaulay.regularLocal_projectiveDimension_le R N b hb
  let Q : LeftResolution R N :=
    { complex := P.complex
      ε := (P.π.f 0).hom
      surjective := (ModuleCat.epi_iff_surjective _).mp inferInstance
      exact_zero := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp P.exact₀
      exact_succ n := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (P.exact_succ n) }
  exact ⟨Q, b, fun i => ⟨hP.finite i, hP.free i⟩,
    AdvCommAlg.minimalFreeResolution_vanishes_above N P hP b hbound⟩

/-- Identify scalar extension with the actual termwise quotient. -/
private def quotientComplexIso (x : R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((regularQuotientFunctor x).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      extendComplex (SpecialFibre x) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((QuotSMulTop.equivQuotTensor x (K.X i)).extendScalarsOfSurjective
      (S := SpecialFibre x) Ideal.Quotient.mk_surjective).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact LinearMap.congr_fun (QuotSMulTop.equivQuotTensor_naturality x (K.d i j).hom).symm z)

private def restrictEquiv {S : Type u} [CommRing S] [Algebra R S]
    {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module S X] [Module S Y]
    (e : X ≃ₗ[S] Y) : RestrictScalars R S X ≃ₗ[R] RestrictScalars R S Y where
  toAddEquiv := e.toAddEquiv
  map_smul' r z := e.map_smul (algebraMap R S r) z

/-- Computing homology before or after restricting the coefficient action
uses the same cycles and boundaries. -/
private def coefficientHomologyEquiv {S : Type u} [CommRing S] [Algebra R S]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (C : Type u) [AddCommGroup C]
    [Module R C] [Module S C] [IsScalarTower R S C] (i : ℕ) :
    Homology (coefficientComplex (S := R) K C) i ≃ₗ[R]
      RestrictScalars R S (Homology (coefficientComplex (S := S) K C) i) := by
  let KR := coefficientComplex (S := R) K C
  let KS := coefficientComplex (S := S) K C
  let e : ∀ n, KR.X n ≃+ KS.X n := fun n => AddEquiv.refl (C ⊗[R] K.X n)
  have he : ∀ m n (z : KR.X m), e n ((KR.d m n).hom z) = (KS.d m n).hom (e m z) := by
    intro m n z
    rfl
  refine { toAddEquiv := additiveHomologyEquiv e he i, map_smul' := ?_ }
  intro r z
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (cycleBoundaries KR i) z
  change homologyClass KS i (P103.Ch12.TorBaseChange.additiveCyclesEquiv e he i (r • v)) =
    (algebraMap R S r) • homologyClass KS i (P103.Ch12.TorBaseChange.additiveCyclesEquiv e he i v)
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  let t : C ⊗[R] K.X i := v.val
  change r • t = (algebraMap R S r) • t
  exact (IsScalarTower.algebraMap_smul S r t).symm

private theorem prime_regular [IsRegularLocalRing R] [CharZero R] (p : ℕ) [Fact p.Prime] :
    IsSMulRegular R (p : R) := by
  letI := AdvCommAlg.Normality.regularLocal_isDomain R
  have hp : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  intro a b hab
  exact mul_left_cancel₀ hp hab

theorem tor_comparison : Specs.torComparison.{u} := by
  intro R _ _ _ p _ _ _ M N _ _ hM hN i
  obtain ⟨Q, _, hQ, _⟩ := exists_bounded_free_resolution N
  let x : R := p
  let A := SpecialFibre x
  let Q' := quotientResolution x Q (fun n => (hQ n).2) (prime_regular p) hN
  letI : Module A M := hM.module
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff x).mpr hM)
  have hproj : Q.IsProjective := fun n => by
    letI := (hQ n).2
    infer_instance
  have hproj' : Q'.IsProjective := fun n => by
    letI := (hQ n).2
    exact inferInstanceAs (Module.Projective A (QuotSMulTop x (Q.complex.X n)))
  let e := ((coefficientTensorFunctor A A M).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
    (quotientComplexIso x Q.complex)
  let eA := (torRightEquiv (killedModule hM) (reduceModule x N) Q' hproj' i).trans
    ((homologyIso e i).trans (firstTorEquiv Q M i))
  exact ⟨(torRightEquiv M N Q hproj i).trans
    ((coefficientHomologyEquiv (S := A) Q.complex M i).trans (restrictEquiv eA.symm))⟩

theorem tensor_comparison : Specs.tensorComparison.{u} := by
  intro R _ _ _ p _ _ hp M N _ _ hM hN
  obtain ⟨e⟩ := tor_comparison p hp M N hM hN 0
  exact ⟨(torZeroEquiv M N).symm.trans
    (e.trans (restrictEquiv (torZeroEquiv (killedModule hM) (reduceModule (p : R) N))))⟩

private theorem length_restriction (x : R) (T : Type u) [AddCommGroup T]
    [Module (SpecialFibre x) T] :
    Module.length R (RestrictScalars R (SpecialFibre x) T) = Module.length (SpecialFibre x) T := by
  letI := RestrictScalars.moduleOrig R (SpecialFibre x) T
  exact Module.length_eq_of_surjective (S := R) (R := SpecialFibre x)
    (M := RestrictScalars R (SpecialFibre x) T) Ideal.Quotient.mk_surjective

theorem length_comparison : Specs.lengthComparison.{u} := by
  intro R _ _ _ p _ _ hp M N _ _ hM hN hlength i
  obtain ⟨e⟩ := tor_comparison p hp M N hM hN i
  have h := tor_finite_length_of_tensor M N hlength i
  have he := e.length_eq.trans (length_restriction (p : R) (reducedTor hM N i))
  exact ⟨h, Module.length_ne_top_iff.mp (he ▸ Module.length_ne_top_iff.mpr h), he⟩

theorem dimension_comparison : Specs.dimensionComparison.{u} := by
  intro R _ _ _ p _ _ _ M N _ _ _ _ hM hN
  let x : R := p
  let A := SpecialFibre x
  letI : Module A M := hM.module
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff x).mpr hM)
  letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
  letI : Module.Finite A (QuotSMulTop x N) := AdvCommAlg.regularQuotient_finite x N
  have hx : x ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue R (p : R) = 0
    rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨hQ, hdrop⟩ := AdvCommAlg.CohenMacaulay.dimension_quotient_regular R N x hx hN
  have hMd := AdvCommAlg.CohenMacaulay.dimension_of_surjective (R := R) (S := A)
    M Ideal.Quotient.mk_surjective
  have hNd := AdvCommAlg.CohenMacaulay.dimension_of_surjective (R := R) (S := A)
    (QuotSMulTop x N) Ideal.Quotient.mk_surjective
  refine ⟨hQ, hMd.symm, hNd.symm, ?_⟩
  change AdvCommAlg.CohenMacaulay.dimension A (QuotSMulTop x N) + 1 = _
  rw [← hNd]
  exact hdrop

end CommutativeAlgebraNotes.Intersection.OneSpecialFibreTor
