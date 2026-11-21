import MathGenome.Internal.Specs.D05.M10.Rational.RelativeCyclic
import MathGenome.Internal.D05.M10.Rational
import MathGenome.Internal.D05.M10.Cyclic
import MathGenome.Internal.D05.M10.InvariantFactors
import MathGenome.Internal.D05.M06.Invariant

noncomputable section
open Polynomial
open scoped BigOperators
namespace D05.M10.Rational.RelativeCyclic

abbrev admissible := Specs.D05.M10.Rational.RelativeCyclic.admissible_value

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Invariance under T implies invariance under every polynomial in T. -/
lemma polynomial_mem (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (p : K[X]) (v : V) (hv : v ∈ W) :
    aeval T p v ∈ W := by
  change Specs.D05.M08.Evaluation.evaluation_value K V T p v ∈ W
  rw [D05.M08.Evaluation.eval_apply]
  apply W.sum_mem
  intro j hj
  apply W.smul_mem
  have hpow : ∀ j : ℕ, (T ^ j) v ∈ W := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ih => simpa [pow_succ', Module.End.mul_apply] using hW _ ih
  exact hpow j

/-- The quotient projection, with the polynomial actions induced by T and Tbar. -/
def quotientPolynomialMap (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) :
    Module.AEval' T →ₗ[K[X]] Module.AEval' (W.mapQ W T hW) :=
  LinearMap.ofAEval T ((Module.AEval'.of (W.mapQ W T hW)).toLinearMap.comp W.mkQ)
    (by
      intro v
      change (Module.AEval'.of (W.mapQ W T hW)) (W.mkQ (T v)) =
        (X : K[X]) • (Module.AEval'.of (W.mapQ W T hW)) (W.mkQ v)
      rw [Module.AEval'.X_smul_of]
      rfl)

@[simp] lemma quotientPolynomialMap_apply (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (v : V) :
    quotientPolynomialMap T W hW (Module.AEval'.of T v) =
      Module.AEval'.of (W.mapQ W T hW) (W.mkQ v) := rfl

lemma quotientPolynomialMap_surjective (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) :
    Function.Surjective (quotientPolynomialMap T W hW) := by
  intro z
  obtain ⟨v, hv⟩ := W.mkQ_surjective ((Module.AEval'.of (W.mapQ W T hW)).symm z)
  exact ⟨Module.AEval'.of T v, by simp [hv]⟩

lemma quotientPolynomialMap_eq_zero (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (v : V) :
    quotientPolynomialMap T W hW (Module.AEval'.of T v) = 0 ↔ v ∈ W := by
  rw [quotientPolynomialMap_apply, LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero W


/-- Correct a lift of a quotient vector without changing its coset. -/
lemma corrected_lift (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (hA : admissible K V T W)
    (d : K[X]) (z : Module.AEval' (W.mapQ W T hW)) (hz : d • z = 0) :
    ∃ u : V, quotientPolynomialMap T W hW (Module.AEval'.of T u) = z ∧
      aeval T d u = 0 := by
  obtain ⟨v, hv⟩ := quotientPolynomialMap_surjective T W hW z
  let v₀ := (Module.AEval'.of T).symm v
  have hmem : aeval T d v₀ ∈ W := by
    apply (quotientPolynomialMap_eq_zero T W hW _).mp
    change quotientPolynomialMap T W hW (d • v) = 0
    rw [map_smul, hv, hz]
  obtain ⟨w, hw⟩ := hA d v₀ hmem
  refine ⟨v₀ - w, ?_, by simpa [map_sub] using sub_eq_zero.mpr hw⟩
  rw [map_sub, map_sub]
  have hw0 := (quotientPolynomialMap_eq_zero T W hW (w : V)).mpr w.property
  simpa [v₀, hw0] using hv

open Specs.D05.M10.Rational (Residue)

/-- A residue class is the polynomial multiple of the class of one. -/
lemma residue_smul_one (d p : K[X]) :
    p • (Submodule.Quotient.mk (1 : K[X]) : Residue d) = Submodule.Quotient.mk p := by
  change Submodule.Quotient.mk (p * 1) = _
  rw [mul_one]

lemma residue_self_smul (d : K[X]) :
    d • (Submodule.Quotient.mk (1 : K[X]) : Residue d) = 0 := by
  rw [residue_smul_one]
  exact (Submodule.Quotient.mk_eq_zero (Ideal.span {d} : Submodule K[X] K[X])).mpr (Ideal.subset_span (Set.mem_singleton d))

/-- Factor evaluation at u through the residue quotient after proving d(T)u = 0. -/
def residueLift (T : Module.End K V) (d : K[X]) (u : V)
    (hu : aeval T d u = 0) : Residue d →ₗ[K[X]] Module.AEval' T :=
  (Ideal.span {d} : Submodule K[X] K[X]).liftQ
    (Specs.D05.M10.Cyclic.orbitMap T u) (by
      intro p hp
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
      change (d * q) • Module.AEval'.of T u = 0
      rw [mul_comm, mul_smul]
      have h : d • Module.AEval'.of T u = 0 := hu
      rw [h, smul_zero])

@[simp] lemma residueLift_mk (T : Module.End K V) (d p : K[X]) (u : V)
    (hu : aeval T d u = 0) :
    residueLift T d u hu (Submodule.Quotient.mk p) =
      Module.AEval'.of T (aeval T p u) := rfl

lemma residueLift_range (T : Module.End K V) (d : K[X]) (u : V)
    (hu : aeval T d u = 0) :
    LinearMap.range ((Module.AEval'.of T).symm.toLinearMap.comp
      ((residueLift T d u hu).restrictScalars K)) = Cyclic.cyclicSpace K V T u := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨p, rfl⟩ := (Ideal.span {d} : Submodule K[X] K[X]).mkQ_surjective z
    exact Cyclic.eval_mem_cyclic T u p
  · intro hv
    obtain ⟨p, hp⟩ := (Cyclic.module_bridge T u v).mpr hv
    exact ⟨Submodule.Quotient.mk p, congrArg (Module.AEval'.of T).symm hp⟩

/-- Lift a rational decomposition of the quotient, with the entire quotient
isomorphism as its composite with the projection. -/
lemma lift_residue_decomposition (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (hA : admissible K V T W)
    {r : ℕ} (d : Fin r → K[X])
    (e : (∀ i, Residue (d i)) ≃ₗ[K[X]] Module.AEval' (W.mapQ W T hW)) :
    ∃ (u : Fin r → V) (hu : ∀ i, aeval T (d i) (u i) = 0)
      (F : (∀ i, Residue (d i)) →ₗ[K[X]] Module.AEval' T),
      (∀ z, quotientPolynomialMap T W hW (F z) = e z) ∧
      (∀ z, F z = ∑ i, residueLift T (d i) (u i) (hu i) (z i)) ∧
      (∀ i z, F (Pi.single i z) = residueLift T (d i) (u i) (hu i) z) := by
  classical
  let g (i : Fin r) := e.toLinearMap.comp (LinearMap.single K[X] (fun i => Residue (d i)) i)
  have hz (i : Fin r) : d i • g i (Submodule.Quotient.mk (1 : K[X])) = 0 := by
    rw [← map_smul, residue_self_smul, map_zero]
  choose u hq hu using fun i => corrected_lift T W hW hA (d i) _ (hz i)
  let f (i : Fin r) := residueLift T (d i) (u i) (hu i)
  have hfg (i : Fin r) (z : Residue (d i)) :
      quotientPolynomialMap T W hW (f i z) = g i z := by
    obtain ⟨p, rfl⟩ := (Ideal.span {d i} : Submodule K[X] K[X]).mkQ_surjective z
    change quotientPolynomialMap T W hW (f i (Submodule.Quotient.mk p)) =
      g i (Submodule.Quotient.mk p)
    rw [← residue_smul_one (d i) p, map_smul, map_smul, map_smul]
    have hf1 : f i (Submodule.Quotient.mk 1) = Module.AEval'.of T (u i) := by
      change Module.AEval'.of T (aeval T 1 (u i)) = _
      simp
    rw [hf1, hq]
  let F : (∀ i, Residue (d i)) →ₗ[K[X]] Module.AEval' T :=
    ∑ i, (f i).comp (LinearMap.proj i)
  have hsingle (i : Fin r) (z : Residue (d i)) : F (Pi.single i z) = f i z := by
    simp [F, LinearMap.sum_apply, LinearMap.apply_single]
  refine ⟨u, hu, F, ?_, ?_, hsingle⟩
  · intro z
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    change quotientPolynomialMap T W hW (∑ i, f i (z i)) = e z
    rw [map_sum]
    simp_rw [hfg]
    change (∑ i, e (Pi.single i (z i))) = e z
    rw [← map_sum, LinearMap.sum_single_apply]
  · intro z
    simp only [F, f, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]



/-- A polynomial-linear lift of a quotient isomorphism gives an actual complement. -/
lemma complement_of_lift (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) {r : ℕ} (d : Fin r → K[X])
    (e : (∀ i, Residue (d i)) ≃ₗ[K[X]] Module.AEval' (W.mapQ W T hW))
    (F : (∀ i, Residue (d i)) →ₗ[K[X]] Module.AEval' T)
    (hq : ∀ z, quotientPolynomialMap T W hW (F z) = e z) :
    ∃ L : Submodule K V, (∀ v ∈ L, T v ∈ L) ∧ IsCompl W L := by
  let f : (∀ i, Residue (d i)) →ₗ[K] V :=
    (Module.AEval'.of T).symm.toLinearMap.comp (F.restrictScalars K)
  have hzero (z) (hz : f z ∈ W) : z = 0 := by
    apply e.injective
    rw [map_zero, ← hq]
    exact (quotientPolynomialMap_eq_zero T W hW (f z)).mpr hz
  refine ⟨f.range, ?_, ?_⟩
  · rintro v ⟨z, rfl⟩
    refine ⟨(X : K[X]) • z, ?_⟩
    change (Module.AEval'.of T).symm (F ((X : K[X]) • z)) = T (f z)
    rw [map_smul, Module.AEval'.of_symm_X_smul]
    rfl
  · constructor
    · apply Submodule.disjoint_def.mpr
      rintro v hv ⟨z, rfl⟩
      rw [hzero z hv, map_zero]
    · apply Submodule.codisjoint_iff_exists_add_eq.mpr
      intro v
      let z := e.symm (Module.AEval'.of (W.mapQ W T hW) (W.mkQ v))
      have hz : v - f z ∈ W := by
        apply (quotientPolynomialMap_eq_zero T W hW _).mp
        rw [map_sub, map_sub]
        change quotientPolynomialMap T W hW (Module.AEval'.of T v) -
          quotientPolynomialMap T W hW (F z) = 0
        rw [hq]
        simp [z]
      exact ⟨v - f z, f z, hz, ⟨z, rfl⟩, sub_add_cancel _ _⟩

/-- The sum with W is bijective because its projection is the given quotient
isomorphism. This includes the empty product. -/
lemma sum_bijective (T : Module.End K V) (W : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) {r : ℕ} (d : Fin r → K[X])
    (e : (∀ i, Residue (d i)) ≃ₗ[K[X]] Module.AEval' (W.mapQ W T hW))
    (F : (∀ i, Residue (d i)) →ₗ[K[X]] Module.AEval' T)
    (hq : ∀ z, quotientPolynomialMap T W hW (F z) = e z) :
    Function.Bijective
      (W.subtype.coprod ((Module.AEval'.of T).symm.toLinearMap.comp
        (F.restrictScalars K))) := by
  let f := (Module.AEval'.of T).symm.toLinearMap.comp (F.restrictScalars K)
  have hzero (z) (hz : f z ∈ W) : z = 0 := by
    apply e.injective
    rw [map_zero, ← hq]
    exact (quotientPolynomialMap_eq_zero T W hW (f z)).mpr hz
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨w, z⟩ hz
    change (w : V) + f z = 0 at hz
    have hzW : f z ∈ W := by
      have hf : f z = -(w : V) := eq_neg_of_add_eq_zero_right hz
      rw [hf]
      exact W.neg_mem w.property
    have hz0 := hzero z hzW
    subst z
    have hw0 : w = 0 := Subtype.ext (by simpa using hz)
    simp [hw0]
  · intro v
    let z := e.symm (Module.AEval'.of (W.mapQ W T hW) (W.mkQ v))
    have hz : v - f z ∈ W := by
      apply (quotientPolynomialMap_eq_zero T W hW _).mp
      rw [map_sub, map_sub]
      change quotientPolynomialMap T W hW (Module.AEval'.of T v) -
        quotientPolynomialMap T W hW (F z) = 0
      rw [hq]
      simp [z]
    exact ⟨(⟨v - f z, hz⟩, z), sub_add_cancel _ _⟩

lemma complement_admissible (T : Module.End K V) (W L : Submodule K V)
    (hW : ∀ v ∈ W, T v ∈ W) (hL : ∀ v ∈ L, T v ∈ L)
    (hc : IsCompl W L) : admissible K V T W := by
  intro p v hv
  obtain ⟨w, l, hw, hl, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
  have hpw := polynomial_mem T W hW p w hw
  have hpl := polynomial_mem T L hL p l hl
  have hplW : aeval T p l ∈ W := by
    have he : aeval T p l = aeval T p (w + l) - aeval T p w := by simp
    rw [he]
    exact W.sub_mem hv hpw
  have hz := Submodule.disjoint_def.mp hc.disjoint _ hplW hpl
  exact ⟨⟨w, hw⟩, by simp [hz]⟩

lemma annihilator_of_injective_residueLift [FiniteDimensional K V]
    (T : Module.End K V) (d : K[X]) (hd : d.Monic) (u : V)
    (hu : aeval T d u = 0) (hinj : Function.Injective (residueLift T d u hu)) :
    Cyclic.vectorAnnihilator K V T u = d := by
  apply Foundations.IdealsGcd.monic_generators_eq (Cyclic.monic_generator T u).1 hd
  apply (Cyclic.monic_generator T u).2.symm.trans
  ext p
  rw [Cyclic.mem_annihilator T u p]
  change aeval T p u = 0 ↔ p ∈ (Ideal.span {d} : Submodule K[X] K[X])
  rw [← Submodule.Quotient.mk_eq_zero (Ideal.span {d} : Submodule K[X] K[X])]
  constructor
  · intro hp
    apply hinj
    change (residueLift T d u hu) (Submodule.Quotient.mk p) =
      (residueLift T d u hu) 0
    rw [residueLift_mk, map_zero]
    exact (Module.AEval'.of T).map_eq_zero_iff.mpr hp
  · intro hp
    change (Submodule.Quotient.mk p : Residue d) = 0 at hp
    have hf := congrArg (residueLift T d u hu) hp
    rw [residueLift_mk, map_zero] at hf
    exact (Module.AEval'.of T).map_eq_zero_iff.mp hf

/-- Main lifting theorem, retaining the canonical quotient factor list. -/
theorem relative_decomposition : Specs.D05.M10.Rational.RelativeCyclic.relative_decomposition := by
  intro K V _ _ _ _ T W hW hA
  classical
  let Q := W.mapQ W T hW
  obtain ⟨r, d, hm, hp, hd, ⟨e⟩, hb⟩ := Rational.rational_form Q
  have hcanon := InvariantFactors.module_identification Q d hm hp hd ⟨e⟩
  obtain ⟨u, hu, F, hq, hsum, hsingle⟩ := lift_residue_decomposition T W hW hA d e.symm
  have hFinj : Function.Injective F := by
    intro z z' hz
    apply e.symm.injective
    rw [← hq, ← hq, hz]
  have hfi (i : Fin r) : Function.Injective (residueLift T (d i) (u i) (hu i)) := by
    intro z z' hz
    have h : (Pi.single i z : ∀ i, Residue (d i)) = Pi.single i z' :=
      hFinj (by rw [hsingle, hsingle]; exact hz)
    simpa using congrFun h i
  let f (i : Fin r) : Residue (d i) →ₗ[K] V :=
    (Module.AEval'.of T).symm.toLinearMap.comp
      ((residueLift T (d i) (u i) (hu i)).restrictScalars K)
  have hfinj (i : Fin r) : Function.Injective (f i) :=
    (Module.AEval'.of T).symm.injective.comp (hfi i)
  let ei (i : Fin r) : Residue (d i) ≃ₗ[K] Cyclic.cyclicSpace K V T (u i) :=
    (LinearEquiv.ofInjective (f i) (hfinj i)).trans
      (LinearEquiv.ofEq _ _ (residueLift_range T (d i) (u i) (hu i)))
  let E₀ := LinearEquiv.ofBijective
    (W.subtype.coprod ((Module.AEval'.of T).symm.toLinearMap.comp (F.restrictScalars K)))
    (sum_bijective T W hW d e.symm F hq)
  let E := ((LinearEquiv.refl K W).prodCongr (LinearEquiv.piCongrRight ei).symm).trans E₀
  refine ⟨r, d, u, hm, hp, hd, hcanon, ?_, ?_, E, ?_⟩
  · intro i
    exact annihilator_of_injective_residueLift T (d i) (hm i) (u i) (hu i) (hfi i)
  · intro i v hv
    exact Cyclic.invariant T (u i) v hv
  · intro z
    change (z.1 : V) + (Module.AEval'.of T).symm
      (F (fun i => (ei i).symm (z.2 i))) = _
    rw [hsum, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hei := congrArg (fun x : Cyclic.cyclicSpace K V T (u i) => (x : V))
      ((ei i).apply_symm_apply (z.2 i))
    exact hei

theorem admissible_iff_complement : Specs.D05.M10.Rational.RelativeCyclic.admissible_iff_complement := by
  intro K V _ _ _ _ T W hW
  constructor
  · intro hA
    obtain ⟨r, d, hm, hp, hd, ⟨e⟩, hb⟩ := Rational.rational_form (W.mapQ W T hW)
    obtain ⟨u, hu, F, hq, hsum, hsingle⟩ := lift_residue_decomposition T W hW hA d e.symm
    exact complement_of_lift T W hW d e.symm F hq
  · rintro ⟨L, hL, hc⟩
    exact complement_admissible T W L hW hL hc

theorem factor_uniqueness : Specs.D05.M10.Rational.RelativeCyclic.factor_uniqueness := by
  intro K V _ _ _ _ T W hW r s d e hd he
  exact InvariantFactors.rational_unique (W.mapQ W T hW) d e hd he

theorem full_subspace : Specs.D05.M10.Rational.RelativeCyclic.full_subspace := by
  intro K V _ _ _ _ T
  refine ⟨?_, isCompl_top_bot, ?_⟩
  · intro p v hv
    exact ⟨⟨v, trivial⟩, rfl⟩
  · exact (InvariantFactors.zero_case
      ((⊤ : Submodule K V).mapQ ⊤ T (fun _ _ => trivial)) (Module.finrank_zero_of_subsingleton)).1

end D05.M10.Rational.RelativeCyclic
