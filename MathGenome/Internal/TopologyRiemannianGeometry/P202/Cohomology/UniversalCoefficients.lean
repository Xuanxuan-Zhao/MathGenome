import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficients
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.AlgebraCore.P103.Ch11.ArbitraryRankPIDSubmodules
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202.UniversalCoefficients
universe u v w t
open P202Specs.UniversalCoefficients P202Specs.SingularChains
  P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R]

/-- The basis is all singular simplices, with finite support. -/
theorem ordinary_free : Expected.ordinaryFree.{u,w} R := by
  intro X n
  change Module.Free R (Simplex X n →₀ R)
  infer_instance

/-- The existing outside-simplex basis works for every subspace. -/
theorem relative_free : Expected.relativeFree.{u,w} R := by
  intro P n
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P n
  exact Module.Free.of_basis b

theorem integer_free : Expected.integerFree.{u,w} R := by
  constructor
  · intro X n
    by_cases hn : 0 ≤ n
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      haveI := ordinary_free R X q
      exact Module.Free.of_equiv (ordinaryNonnegativeIso R R X q).toLinearEquiv.symm
    · have := ModuleCat.subsingleton_of_isZero
        (P202.SingularChains.ordinary_negative_chains R R X n (by omega))
      infer_instance
  · intro P n
    by_cases hn : 0 ≤ n
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      haveI := relative_free R P q
      exact Module.Free.of_equiv (ordinaryDegreeIso R R P q).toLinearEquiv.symm
    · have := ModuleCat.subsingleton_of_isZero
        (P202.RelativeSingularChains.ordinary_negative R R P n (by omega)).1
      infer_instance

/-- Arbitrary-rank PID freeness, with no finite generation assumption. -/
theorem pid_free [IsDomain R] [IsPrincipalIdealRing R] : Expected.pidFree.{u,w} R := by
  constructor
  · intro X n
    haveI := ordinary_free R X n
    exact ⟨P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule R _ _,
      P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule R _ _⟩
  · intro P n
    haveI := relative_free R P n
    exact ⟨P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule R _ _,
      P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule R _ _⟩

theorem projective_hypotheses [IsDomain R] [IsPrincipalIdealRing R] :
    Expected.projectiveHypotheses.{u,w} R := by
  constructor
  · intro X
    constructor
    · intro n
      haveI := ordinary_free R X n
      infer_instance
    · intro n
      haveI := (pid_free R).1 X n |>.2
      infer_instance
  · intro P
    constructor
    · intro n
      haveI := relative_free R P n
      infer_instance
    · intro n
      haveI := (pid_free R).2 P n |>.2
      infer_instance

variable (A : Type v) [AddCommGroup A] [Module R A]

theorem evaluation_formula : Expected.evaluationFormula.{u,v,t} R A :=
  P202.UniversalCoefficientsCohomology.evaluation_formula R A

/-- Over a field, a functional which vanishes on all cycles is a coboundary.
The annihilator/range identity is valid for arbitrary vector spaces. -/
theorem quotientEvaluation_bijective (K : Type u) [Field K]
    (C : ChainComplex (ModuleCat.{t} K) ℤ) (n : ℤ) :
    Function.Bijective (quotientEvaluation K K C n) := by
  have hz : ∀ x, quotientEvaluation K K C n x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := (Algebraic.cycleBoundaries (dualChain K K C) n).mkQ_surjective x
    let a' : C.X n →ₗ[K] K := a.val
    let d := (C.d n ((ComplexShape.down ℤ).next n)).hom
    have hann : a' ∈ (LinearMap.ker d).dualAnnihilator := by
      apply (LinearMap.ker d).mem_dualAnnihilator a' |>.mpr
      intro z hz
      let z' : Algebraic.cycles C n := ⟨z, hz⟩
      exact congrArg (fun f : Algebraic.Homology C n →ₗ[K] K =>
        f (Algebraic.homologyClass C n z')) hx
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker d] at hann
    obtain ⟨b, hb⟩ := hann
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change ∃ b, ((dualChain K K C).d ((ComplexShape.up ℤ).prev n) n).hom b = a.val
    exact ⟨b, hb⟩
  constructor
  · intro x y hxy
    exact sub_eq_zero.mp (hz (x-y) (by rw [map_sub, hxy, sub_self]))
  · intro h
    obtain ⟨a, ha⟩ := (h.comp (Algebraic.homologyClass C n)).exists_extend
    have hac : a ∈ Algebraic.cycles (dualChain K K C) n := by
      apply LinearMap.ext
      intro b
      change a ((C.d ((ComplexShape.down ℤ).prev n) n).hom b) = 0
      let z : Algebraic.cycles C n :=
        ⟨_, P103.Specs.Ch10.Complexes.boundaryInclusion C n ⟨b, rfl⟩⟩
      have hz : Algebraic.homologyClass C n z = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
      have he := LinearMap.congr_fun ha z
      change a z.val = h (Algebraic.homologyClass C n z) at he
      rw [hz, map_zero] at he
      exact he
    refine ⟨Algebraic.homologyClass _ n ⟨a, hac⟩, ?_⟩
    apply (Algebraic.cycleBoundaries C n).quot_hom_ext
    intro z
    exact LinearMap.congr_fun ha z

/-- The same statement on the project's categorical homology objects. -/
theorem evaluation_bijective (K : Type u) [Field K]
    (C : ChainComplex (ModuleCat.{t} K) ℤ) (n : ℤ) :
    Function.Bijective (P202Specs.UniversalCoefficients.evaluation K K C n) := by
  let e : (Algebraic.Homology C n →ₗ[K] K) ≃ₗ[K] (C.homology n →ₗ[K] K) :=
    LinearEquiv.arrowCongr (quotientHomologyEquiv K C n).symm
    (LinearEquiv.refl K K)
  exact e.bijective.comp ((quotientEvaluation_bijective K C n).comp
    (quotientHomologyEquiv K (dualChain K K C) n).bijective)

theorem field_duality : fieldDuality_type.{u,w} := by
  intro K _
  exact ⟨fun X n => evaluation_bijective K (ordinaryComplex K K X) n,
    fun P n => evaluation_bijective K (ordinary K K P) n⟩

/-- Both cohomological arrows commute with space/pair maps and coefficient
homomorphisms. The free singular chain modules supply the algebraic hypotheses;
the degree-zero Ext square follows from its zero domain. -/
theorem cohomology_natural : cohomology_natural_type.{u,v,w} := by
  intro R _ _ _ A B _ _ _ _
  constructor
  · intro X Y f g
    refine ⟨?_, ?_, ?_⟩
    · intro hY hX n α α' hα hα' x
      exact P202.UniversalCoefficientsCohomology.actual_natural R A B
        (ordinaryComplex R R Y) (ordinaryComplex R R X) hY hX
        (fun k => (integer_free R).1 Y k) (fun k => (integer_free R).1 X k)
        ((ordinaryFunctor R R).map f) g n α α' hα hα' x
    · intro α α' x
      have hx : x = 0 := @Subsingleton.elim _
        ((P202.UniversalCoefficientsCohomology.zero_tail R A).1 Y).2 x 0
      rw [hx]
      simp only [map_zero]
    · intro n a z
      exact P202.UniversalCoefficientsCohomology.evaluation_natural R A B
        ((ordinaryFunctor R R).map f) g n a z
  · intro P Q f g
    refine ⟨?_, ?_, ?_⟩
    · intro hQ hP n α α' hα hα' x
      exact P202.UniversalCoefficientsCohomology.actual_natural R A B
        (ordinary R R Q) (ordinary R R P) hQ hP
        (fun k => (integer_free R).2 Q k) (fun k => (integer_free R).2 P k)
        (relativeMap (ordinaryFunctor R R) f) g n α α' hα hα' x
    · intro α α' x
      have hx : x = 0 := @Subsingleton.elim _
        ((P202.UniversalCoefficientsCohomology.zero_tail R A).2 Q).2 x 0
      rw [hx]
      simp only [map_zero]
    · intro n a z
      exact P202.UniversalCoefficientsCohomology.evaluation_natural R A B
        (relativeMap (ordinaryFunctor R R) f) g n a z

/-- Both natural split PID sequences for every space and subspace pair,
including degree zero, with evaluation as the cohomological right arrow,
and the full-dual conclusion over a field. -/
theorem universal_coefficients : universal_coefficients_type.{u,v,w} := by
  exact ⟨P202.UniversalCoefficientsHomology.topological_uct,
    P202.UniversalCoefficientsCohomology.singular_uct,
    P202.UniversalCoefficientsCohomology.all_degrees,
    P202.UniversalCoefficientsCohomology.actual_natural,
    P202.UniversalCoefficientsCohomology.evaluation_natural,
    P202.UniversalCoefficientsCohomology.zero_tail,
    P202.UniversalCoefficientsCohomology.topological_zero,
    field_duality, cohomology_natural⟩

end P202.UniversalCoefficients
