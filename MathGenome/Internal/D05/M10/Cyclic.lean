import MathGenome.Internal.Specs.D05.M10.Cyclic
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.D05.Foundations.QuotientBasisUnits
import MathGenome.Internal.D05.M03.FirstIso

/-! Cyclic spaces and vector annihilators, K05.10.cyclic. -/

noncomputable section

namespace D05.M10.Cyclic

open Polynomial
open scoped BigOperators

abbrev cyclicSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) : Submodule K V :=
  Specs.D05.M10.Cyclic.cyclicSpace_value K V T v

abbrev cyclicModule (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) : Submodule K[X] (Module.AEval' T) :=
  Specs.D05.M10.Cyclic.cyclicModule_value K V T v

abbrev annihilator (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) : Ideal K[X] :=
  Specs.D05.M10.Cyclic.annihilator_value K V T v

abbrev vectorAnnihilator (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (v : V) : K[X] :=
  Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T v

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- In the AEval module, polynomial scalar multiplication is evaluation at T. -/
theorem orbit_evaluation : Specs.D05.M10.Cyclic.orbit_evaluation := by
  intro K V _ _ _ T v p
  rfl

theorem eval_mem_cyclic (T : Module.End K V) (v : V) (p : K[X]) :
    Polynomial.aeval T p v ∈ cyclicSpace K V T v := by
  change Specs.D05.M08.Evaluation.evaluation_value K V T p v ∈ _
  rw [M08.Evaluation.eval_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, rfl⟩)

/-- The range of the polynomial action is exactly the K-span of all iterates. -/
theorem module_bridge : Specs.D05.M10.Cyclic.module_bridge := by
  intro K V _ _ _ T v w
  constructor
  · rintro ⟨p, hp⟩
    have he : Polynomial.aeval T p v = w :=
      congrArg (Module.AEval'.of T).symm hp
    exact he ▸ eval_mem_cyclic T v p
  · intro hw
    have hr : ∀ w ∈ cyclicSpace K V T v,
        w ∈ LinearMap.range (((Module.AEval'.of T).symm.toLinearMap).comp
          ((Specs.D05.M10.Cyclic.orbitMap T v).restrictScalars K)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      refine ⟨X ^ j, ?_⟩
      change Polynomial.aeval T (X ^ j) v = (T ^ j) v
      rw [Polynomial.aeval_X_pow]
    obtain ⟨p, hp⟩ := hr w hw
    exact ⟨p, (Module.AEval'.of T).symm.injective hp⟩

theorem invariant : Specs.D05.M10.Cyclic.invariant := by
  intro K V _ _ _ T v w hw
  obtain ⟨p, hp⟩ := (module_bridge T v w).mpr hw
  apply (module_bridge T v (T w)).mp
  refine ⟨X * p, ?_⟩
  change (X * p) • Module.AEval'.of T v = Module.AEval'.of T (T w)
  change p • Module.AEval'.of T v = Module.AEval'.of T w at hp
  rw [mul_smul, hp, Module.AEval'.X_smul_of]

/-- The coordinate-free identification used to transport the quotient basis. -/
def moduleSpaceEquiv (T : Module.End K V) (v : V) :
    cyclicModule K V T v ≃ₗ[K] cyclicSpace K V T v where
  toFun w := ⟨(Module.AEval'.of T).symm w,
    (module_bridge T v _).mp (by simpa only [LinearEquiv.apply_symm_apply] using w.property)⟩
  invFun w := ⟨Module.AEval'.of T w, (module_bridge T v _).mpr w.property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem module_identification : Specs.D05.M10.Cyclic.module_identification := by
  intro K V _ _ _ T v
  refine ⟨moduleSpaceEquiv T v, fun _ => rfl, ?_⟩
  intro w
  change (Module.AEval'.of T).symm ((X : K[X]) • (w : Module.AEval' T)) =
    T ((Module.AEval'.of T).symm (w : Module.AEval' T))
  exact Module.AEval'.of_symm_X_smul T _

theorem evaluation_surjective : Specs.D05.M10.Cyclic.evaluation_surjective := by
  intro K V _ _ _ T v
  let f := (moduleSpaceEquiv T v).toLinearMap.comp
    ((Specs.D05.M10.Cyclic.orbitMap T v).rangeRestrict.restrictScalars K)
  refine ⟨f, ?_, fun _ => rfl⟩
  exact (moduleSpaceEquiv T v).surjective.comp
    (Specs.D05.M10.Cyclic.orbitMap T v).surjective_rangeRestrict

theorem mem_annihilator : Specs.D05.M10.Cyclic.mem_annihilator := by
  intro K V _ _ _ T v p
  change Specs.D05.M10.Cyclic.orbitMap T v p = 0 ↔ _
  exact (Module.AEval'.of T).symm.map_eq_zero_iff.symm

theorem nonzero_annihilator : Specs.D05.M10.Cyclic.nonzero_annihilator := by
  intro K V _ _ _ _ T v
  have hm : minpoly K T ∈ annihilator K V T v := by
    apply (mem_annihilator T v _).mpr
    have h := M08.Minpoly.annihilates T
    change Polynomial.aeval T (minpoly K T) = 0 at h
    simp only [Specs.D05.M08.Evaluation.evaluation_value, h, LinearMap.zero_apply]
  refine ⟨?_, hm⟩
  intro hbot
  have hz : minpoly K T = 0 := by
    change minpoly K T ∈ Specs.D05.M10.Cyclic.annihilator_value K V T v at hm
    rw [hbot] at hm
    exact hm
  exact M08.Minpoly.ne_zero T hz

theorem monic_generator : Specs.D05.M10.Cyclic.monic_generator := by
  intro K V _ _ _ _ T v
  classical
  let I := annihilator K V T v
  have hp : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro hp
    exact (nonzero_annihilator T v).1
      ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hp)
  refine ⟨Polynomial.monic_normalize hp, ?_⟩
  exact ((Foundations.IdealsGcd.span_normalize _).trans
    (Ideal.span_singleton_generator I)).symm

theorem unique_monic_generator : Specs.D05.M10.Cyclic.unique_monic_generator := by
  intro K V _ _ _ _ T v
  obtain ⟨hd, hI⟩ := monic_generator T v
  refine ⟨vectorAnnihilator K V T v, ⟨hd, hI⟩, ?_⟩
  intro p hp
  exact Foundations.IdealsGcd.monic_generators_eq hp.1 hd (hp.2.symm.trans hI)

theorem least_degree : Specs.D05.M10.Cyclic.least_degree := by
  intro K V _ _ _ _ T v p hp hp0
  have hd : Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T v ∣ p := by
    apply Ideal.mem_span_singleton.mp
    rwa [← (monic_generator T v).2]
  exact Polynomial.natDegree_le_of_dvd hd hp0

theorem divides_iff_annihilates : Specs.D05.M10.Cyclic.divides_iff_annihilates := by
  intro K V _ _ _ _ T v p
  have h : p ∈ Specs.D05.M10.Cyclic.annihilator_value K V T v ↔
      Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T v ∣ p := by
    rw [(monic_generator T v).2, Ideal.mem_span_singleton]
  exact h.symm.trans (mem_annihilator T v p)

theorem reduced_annihilator_eq_zero : Specs.D05.M10.Cyclic.reduced_annihilator_eq_zero := by
  intro K V _ _ _ _ T v p hp hmem
  by_contra hp0
  have hd : Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T v ∣ p := by
    exact (divides_iff_annihilates T v p).mpr ((mem_annihilator T v p).mp hmem)
  exact (not_lt_of_ge (Polynomial.degree_le_of_dvd hd hp0)) hp

theorem quotient_iso : Specs.D05.M10.Cyclic.quotient_iso := by
  intro K V _ _ _ _ T v
  let f := Specs.D05.M10.Cyclic.orbitMap T v
  let e := (Submodule.quotEquivOfEq _ _ (monic_generator T v).2.symm).trans
    f.quotKerEquivRange
  exact ⟨e, fun p => f.quotKerEquivRange_apply_mk p⟩

theorem representatives : Specs.D05.M10.Cyclic.representatives := by
  intro K V _ _ _ _ T v
  exact Foundations.QuotientBasisUnits.uniqueRepresentative K _ (monic_generator T v).1

/-- Transport the residue-class power basis through evaluation. -/
theorem iterate_basis : Specs.D05.M10.Cyclic.iterate_basis := by
  intro K V _ _ _ _ T v
  obtain ⟨e, he⟩ := quotient_iso T v
  obtain ⟨b, hb⟩ := Foundations.QuotientBasisUnits.residueBasis K
    (vectorAnnihilator K V T v) (monic_generator T v).1
  let eK : AdjoinRoot (vectorAnnihilator K V T v) ≃ₗ[K] cyclicSpace K V T v :=
    (e.restrictScalars K).trans (moduleSpaceEquiv T v)
  refine ⟨b.map eK, ?_⟩
  intro j
  change (eK (b j) : V) = (T ^ (j : ℕ)) v
  rw [hb j]
  change (Module.AEval'.of T).symm
    (e (Submodule.Quotient.mk (X ^ (j : ℕ)))) = (T ^ (j : ℕ)) v
  rw [he]
  change Polynomial.aeval T (X ^ (j : ℕ)) v = (T ^ (j : ℕ)) v
  rw [Polynomial.aeval_X_pow]

theorem dimension : Specs.D05.M10.Cyclic.dimension := by
  intro K V _ _ _ _ T v
  obtain ⟨b, _⟩ := iterate_basis T v
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b

theorem zero_vector : Specs.D05.M10.Cyclic.zero_vector := by
  intro K V _ _ _ T
  classical
  have hI : Specs.D05.M10.Cyclic.annihilator_value K V T 0 = ⊤ := by
    ext p
    constructor
    · intro _; trivial
    · intro _
      exact (mem_annihilator T 0 p).mpr (map_zero _)
  have hd : Specs.D05.M10.Cyclic.vectorAnnihilator_value K V T 0 = 1 := by
    change normalize (Submodule.IsPrincipal.generator
      (Specs.D05.M10.Cyclic.annihilator_value K V T 0)) = 1
    apply normalize_eq_one.mpr
    apply Ideal.span_singleton_eq_top.mp
    rw [Ideal.span_singleton_generator, hI]
  refine ⟨hd, ?_, ?_⟩
  · change Submodule.span K (Set.range (fun j : ℕ => (T ^ j) (0 : V))) = ⊥
    simp only [LinearMap.map_zero, Set.range_const, Submodule.span_zero_singleton]
  · exact congrArg Polynomial.natDegree hd |>.trans Polynomial.natDegree_one

end D05.M10.Cyclic
