import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.CentralTraceIdeals
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.GroupAlgebraCenter
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.RelativeTrace
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section

open scoped MonoidAlgebra
open P103.Ch08.ClassSumIntegrality (classSum classSum_coeff)

namespace RepTheorySurvey.Modular.CentralTraceIdeals

open RelativeTrace GroupAlgebraCenter
open CentralTraceIdealsSpec (orbitStabilizer coeff_conjugation
  sylowConjugateInto eligibleClass)

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- The image of relative trace from `P` in the center of the group algebra. -/
def traceIdeal [Finite G] (P : Subgroup G) : Ideal (Subalgebra.center k k[G]) :=
  CentralTraceIdealsSpec.traceIdeal k P

theorem mem_traceIdeal_iff [Finite G] (P : Subgroup G) (z : Subalgebra.center k k[G]) :
    z ∈ traceIdeal k P ↔ ∃ a : fixedSubalgebra k P,
      (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]) = (z : k[G]) :=
  Iff.rfl

theorem trace_mem_center [Finite G] (P : Subgroup G) (a : fixedSubalgebra k P) :
    (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]) ∈ Subalgebra.center k k[G] := by
  let z := relativeTrace k (show P ≤ ⊤ from le_top) a
  apply (mem_center_iff (z : k[G])).mpr
  intro x y hxy
  obtain ⟨g, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hxy)
  have h := congrArg (fun b : k[G] => b.coeff (g * x * g⁻¹))
    (z.property ⟨g, Subgroup.mem_top g⟩)
  rw [coeff_conjugation] at h
  simpa [mul_assoc] using h

local instance (priority := high) subgroupConjugationAction (P : Subgroup G) : MulAction P G :=
  MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp P.subtype)

private abbrev fixedSingle {Q : Subgroup G} (x : G) (hQ : Q ≤ Subgroup.centralizer {x}) :
    fixedSubalgebra k Q := CentralTraceIdealsSpec.fixedSingle k x hQ

private abbrev orbitSum [Finite G] (P : Subgroup G) (x : G) : fixedSubalgebra k P :=
  CentralTraceIdealsSpec.orbitSum k P x

private theorem subgroup_smul (P : Subgroup G) (g : P) (x : G) :
    g • x = (g : G) * x * (g : G)⁻¹ := rfl

private theorem subgroup_stabilizer (P : Subgroup G) (x : G) :
    MulAction.stabilizer P x = (orbitStabilizer P x).subgroupOf P := by
  ext g
  change g • x = x ↔ (g : G) ∈ orbitStabilizer P x
  rw [subgroup_smul, mul_inv_eq_iff_eq_mul]
  change _ ↔ (g : G) ∈ P ∧ (g : G) ∈ Subgroup.centralizer {x}
  rw [Subgroup.mem_centralizer_singleton_iff, and_iff_right g.property, eq_comm]

section Finite

variable [Finite G]

noncomputable local instance (Q P : Subgroup G) : Fintype (LeftCosets Q P) := Fintype.ofFinite _

noncomputable local instance (P : Subgroup G) (x : G) : Fintype (MulAction.orbit P x) :=
  Fintype.ofFinite _

omit [Group G] [Finite G] in
private theorem coeff_sum_single (S : Set G) [Fintype S] (y : G) [Decidable (y ∈ S)] :
    (∑ z : S, MonoidAlgebra.single (z : G) (1 : k)).coeff y = if y ∈ S then 1 else 0 := by
  classical
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  split_ifs with hy
  · rw [Finset.sum_eq_single ⟨y, hy⟩]
    · simp
    · intro z _ hz
      have hzy : (z : G) ≠ y := fun h => hz (Subtype.ext h)
      simp [hzy]
    · simp
  · apply Finset.sum_eq_zero
    intro z _
    have hzy : (z : G) ≠ y := fun h => hy (h ▸ z.property)
    simp [hzy]

private theorem trace_fixedSingle_coeff {Q P : Subgroup G} (hQP : Q ≤ P) (x y : G)
    (hQ : Q ≤ Subgroup.centralizer {x})
    (hstab : Q.subgroupOf P = MulAction.stabilizer P x) [Decidable (y ∈ MulAction.orbit P x)] :
    (relativeTrace k hQP (fixedSingle k x hQ) : k[G]).coeff y =
      if y ∈ MulAction.orbit P x then 1 else 0 := by
  let e : LeftCosets Q P ≃ MulAction.orbit P x :=
    (Subgroup.quotientEquivOfEq hstab).trans (MulAction.orbitEquivQuotientStabilizer P x).symm
  have he (c : LeftCosets Q P) : (e c : G) = c.out • x := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    dsimp only [e, Equiv.trans_apply]
    rw [Subgroup.quotientEquivOfEq_mk,
      MulAction.orbitEquivQuotientStabilizer_symm_apply]
  have hsum : (relativeTrace k hQP (fixedSingle k x hQ) : k[G]) =
      ∑ z : MulAction.orbit P x, MonoidAlgebra.single (z : G) (1 : k) := by
    rw [relativeTrace_eq_sum k hQP _ Quotient.out QuotientGroup.out_eq',
      ← e.sum_comp (fun z => MonoidAlgebra.single (z : G) (1 : k))]
    apply Finset.sum_congr rfl
    intro c _
    change conjugation k (c.out : G) (MonoidAlgebra.single x 1) = _
    rw [conjugation_single, he, subgroup_smul]
  rw [hsum, coeff_sum_single]

private theorem orbitSum_coeff (P : Subgroup G) (x y : G) [Decidable (y ∈ MulAction.orbit P x)] :
    (orbitSum k P x : k[G]).coeff y = if y ∈ MulAction.orbit P x then 1 else 0 :=
  trace_fixedSingle_coeff k inf_le_left x y inf_le_right (subgroup_stabilizer P x).symm

omit [Finite G] in
private theorem mem_orbit_top_iff (x y : G) :
    y ∈ MulAction.orbit (⊤ : Subgroup G) x ↔ ConjClasses.mk y = ConjClasses.mk x := by
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
  simp_rw [subgroup_smul]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, Subgroup.mem_top g⟩, hg⟩⟩

private theorem trace_fixedSingle_within_centralizer {Q : Subgroup G} (x : G)
    (hQ : Q ≤ Subgroup.centralizer {x}) :
    relativeTrace k hQ (fixedSingle k x hQ) =
      ((Q.relIndex (Subgroup.centralizer {x}) : ℕ) : k) • fixedSingle k x le_rfl := by
  classical
  apply Subtype.ext
  rw [relativeTrace_eq_sum k hQ _ Quotient.out QuotientGroup.out_eq']
  have hfix (c : LeftCosets Q (Subgroup.centralizer {x})) :
      conjugation k (c.out : G) (MonoidAlgebra.single x 1) = MonoidAlgebra.single x 1 :=
    (fixedSingle k x (show Subgroup.centralizer {x} ≤ Subgroup.centralizer {x} from le_rfl)).property
      c.out
  change (∑ c : LeftCosets Q (Subgroup.centralizer {x}),
    conjugation k (c.out : G) (MonoidAlgebra.single x 1)) =
    ((Q.relIndex (Subgroup.centralizer {x}) : ℕ) : k) • MonoidAlgebra.single x 1
  rw [Finset.sum_congr rfl (fun c _ => hfix c), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k, ← Nat.card_eq_fintype_card]
  rfl

/-- The trace multiplier is the index of the orbit stabilizer in the full centralizer. -/
theorem orbit_index_ne_zero_iff (p : ℕ) [Fact p.Prime] [CharP k p]
    (P : Subgroup G) (hP : IsPGroup p P) (x : G) :
    ((P.relIndex (Subgroup.centralizer {x}) : ℕ) : k) ≠ 0 ↔
      ∃ D : Sylow p (Subgroup.centralizer ({x} : Set G)),
        (D : Subgroup _) = P.subgroupOf (Subgroup.centralizer {x}) := by
  rw [ne_eq, CharP.cast_eq_zero_iff k p]
  constructor
  · intro h
    exact ⟨hP.comap_subtype.toSylow h, rfl⟩
  · rintro ⟨D, hD⟩
    change ¬ p ∣ (P.subgroupOf (Subgroup.centralizer {x})).index
    rw [← hD]
    exact D.not_dvd_index

end Finite

variable [Fintype G]

private theorem trace_fixedSingle_centralizer (x : G) :
    (relativeTrace k (show Subgroup.centralizer {x} ≤ ⊤ from le_top)
      (fixedSingle k x le_rfl) : k[G]) = classSum k (ConjClasses.mk x) := by
  classical
  ext y
  have hstab : (Subgroup.centralizer ({x} : Set G)).subgroupOf (⊤ : Subgroup G) =
      MulAction.stabilizer (⊤ : Subgroup G) x := by
    simpa only [top_inf_eq] using (subgroup_stabilizer (⊤ : Subgroup G) x).symm
  rw [trace_fixedSingle_coeff k le_top x y le_rfl hstab, classSum_coeff, mem_orbit_top_iff]
  split_ifs <;> rfl

/-- The full trace of a subgroup orbit sum is an index times the canonical class sum. -/
theorem trace_orbitSum (P : Subgroup G) (x : G) :
    (relativeTrace k (show P ≤ ⊤ from le_top) (orbitSum k P x) : k[G]) =
      ((P.relIndex (Subgroup.centralizer {x}) : ℕ) : k) • classSum k (ConjClasses.mk x) := by
  let Q := orbitStabilizer P x
  let C := Subgroup.centralizer ({x} : Set G)
  have hQP : Q ≤ P := inf_le_left
  have hQC : Q ≤ C := inf_le_right
  change (relativeTrace k (show P ≤ ⊤ from le_top)
    (relativeTrace k hQP (fixedSingle k x hQC)) : k[G]) = _
  rw [← LinearMap.comp_apply, ← relativeTrace_trans,
    relativeTrace_trans k hQC (show C ≤ ⊤ from le_top), LinearMap.comp_apply,
    trace_fixedSingle_within_centralizer, map_smul]
  change ((Q.relIndex C : ℕ) : k) •
    (relativeTrace k (show C ≤ ⊤ from le_top) (fixedSingle k x le_rfl) : k[G]) = _
  rw [trace_fixedSingle_centralizer]
  change (((P ⊓ C).relIndex C : ℕ) : k) • _ = ((P.relIndex C : ℕ) : k) • _
  simp only [Subgroup.relIndex, Subgroup.inf_subgroupOf_right]

private abbrev Orbits (P : Subgroup G) := MulAction.orbitRel.Quotient P G

noncomputable local instance (P : Subgroup G) : Fintype (Orbits P) := Fintype.ofFinite _

omit [Fintype G] in
private theorem coeff_smul_of_fixed (P : Subgroup G) (a : fixedSubalgebra k P) (g : P) (y : G) :
    (a : k[G]).coeff (g • y) = (a : k[G]).coeff y := by
  rw [subgroup_smul]
  have h := congrArg (fun b : k[G] => b.coeff ((g : G) * y * (g : G)⁻¹)) (a.property g)
  rw [coeff_conjugation] at h
  simpa [mul_assoc] using h.symm

private theorem fixed_eq_sum_orbitSums (P : Subgroup G) (a : fixedSubalgebra k P) :
    a = ∑ q : Orbits P, (a : k[G]).coeff q.out • orbitSum k P q.out := by
  classical
  apply Subtype.ext
  ext y
  simp only [show (↑(∑ q : Orbits P, (a : k[G]).coeff q.out • orbitSum k P q.out) : k[G]) =
    ∑ q : Orbits P, (a : k[G]).coeff q.out • (orbitSum k P q.out : k[G]) from
      map_sum (fixedSubalgebra k P).val.toLinearMap _ _,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply]
  have hq (q : Orbits P) : y ∈ MulAction.orbit P q.out ↔ (Quotient.mk (MulAction.orbitRel P G) y : Orbits P) = q := by
    conv_rhs => rw [← Quotient.out_eq q]
    rw [Quotient.eq]
    rfl
  set qy : Orbits P := Quotient.mk (MulAction.orbitRel P G) y
  have hy : y ∈ MulAction.orbit P qy.out := (hq qy).2 rfl
  simp_rw [orbitSum_coeff k P, hq]
  rw [Finset.sum_eq_single qy]
  · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    simpa using (hg ▸ coeff_smul_of_fixed k P a g qy.out)
  · intro q _ hq'
    simp [Ne.symm hq']
  · simp

private theorem trace_eq_sum_classes (P : Subgroup G) (a : fixedSubalgebra k P) :
    (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]) =
      ∑ q : Orbits P, (a : k[G]).coeff q.out •
        (((P.relIndex (Subgroup.centralizer {q.out}) : ℕ) : k) •
          classSum k (ConjClasses.mk q.out)) := by
  let tr : fixedSubalgebra k P →ₗ[k] k[G] :=
    (fixedSubalgebra k (⊤ : Subgroup G)).val.toLinearMap.comp (relativeTrace k le_top)
  calc
    tr a = ∑ q : Orbits P, (a : k[G]).coeff q.out • tr (orbitSum k P q.out) := by
      rw [← (Finset.sum_congr rfl fun q _ => tr.map_smul _ _), ← map_sum]
      exact congrArg tr (fixed_eq_sum_orbitSums k P a)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [show tr (orbitSum k P q.out) = _ from trace_orbitSum k P q.out]

omit [Fintype G] in
private theorem centralizer_map_conj (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {MulAut.conj g x} := by
  let e := MulAut.conj g
  ext y
  change y ∈ (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom ↔
    y ∈ Subgroup.centralizer {e x}
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  rw [← e.injective.eq_iff (a := e.symm y * x) (b := x * e.symm y),
    map_mul, map_mul, e.apply_symm_apply]

variable (p : ℕ) [Fact p.Prime] [CharP k p]

private theorem exists_sylow_conj_le_iff (P : Subgroup G) (g x : G) (hP : IsPGroup p P) :
    (∃ D : Sylow p (Subgroup.centralizer ({x} : Set G)),
      ((D : Subgroup _).map (Subgroup.centralizer ({x} : Set G)).subtype).map
        (MulAut.conj g).toMonoidHom ≤ P) ↔
    (∃ E : Sylow p (Subgroup.centralizer ({MulAut.conj g x} : Set G)),
      (E : Subgroup _) = P.subgroupOf (Subgroup.centralizer {MulAut.conj g x})) := by
  let C := Subgroup.centralizer ({x} : Set G)
  let C' := Subgroup.centralizer ({MulAut.conj g x} : Set G)
  let e : C ≃* C' := ((MulAut.conj g).subgroupMap C).trans
    (MulEquiv.subgroupCongr (centralizer_map_conj g x))
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have he (D : Sylow p C) :
      ((D : Subgroup _).map C.subtype).map (MulAut.conj g).toMonoidHom =
        ((D.mapSurjective hsurj : Sylow p C') : Subgroup C').map C'.subtype := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    rfl
  constructor
  · rintro ⟨D, hD⟩
    let E : Sylow p C' := D.mapSurjective hsurj
    have hle : (E : Subgroup C') ≤ P.subgroupOf C' :=
      Subgroup.map_le_iff_le_comap.mp ((he D) ▸ hD)
    exact ⟨E, (E.is_maximal' hP.comap_subtype hle).symm⟩
  · rintro ⟨E, hE⟩
    obtain ⟨D, hD⟩ := Sylow.mapSurjective_surjective hsurj p E
    refine ⟨D, ?_⟩
    rw [he D, hD, hE, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left

private theorem sylowConjugateInto_iff_orbit_index (P : Subgroup G) (hP : IsPGroup p P) (x : G) :
    sylowConjugateInto p P x ↔
      ∃ y, ConjClasses.mk y = ConjClasses.mk x ∧
        ((P.relIndex (Subgroup.centralizer {y}) : ℕ) : k) ≠ 0 := by
  constructor
  · rintro ⟨D, g, hg⟩
    refine ⟨MulAut.conj g x, ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨g, rfl⟩).symm, (orbit_index_ne_zero_iff k p P hP _).2 ?_⟩
    exact (exists_sylow_conj_le_iff p P g x hP).1 ⟨D, hg⟩
  · rintro ⟨y, hy, h⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hy.symm)
    change ((P.relIndex (Subgroup.centralizer {MulAut.conj g x}) : ℕ) : k) ≠ 0 at h
    obtain ⟨D, hD⟩ := (exists_sylow_conj_le_iff p P g x hP).2 ((orbit_index_ne_zero_iff k p P hP _).1 h)
    exact ⟨D, g, hD⟩

private theorem trace_coeff_eq_zero (P : Subgroup G) (hP : IsPGroup p P) (x : G)
    (hx : ¬ sylowConjugateInto p P x) (a : fixedSubalgebra k P) :
    (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]).coeff x = 0 := by
  classical
  rw [trace_eq_sum_classes]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : ConjClasses.mk q.out = ConjClasses.mk x
  · have hz : ((P.relIndex (Subgroup.centralizer {q.out}) : ℕ) : k) = 0 := by
      by_contra hne
      exact hx ((sylowConjugateInto_iff_orbit_index k p P hP x).2 ⟨q.out, h, hne⟩)
    simp [hz]
  · simp [classSum_coeff, Ne.symm h]

/-- Each element in the support of a central trace satisfies the Sylow criterion. -/
theorem sylowConjugateInto_of_mem_traceIdeal (P : Subgroup G) (hP : IsPGroup p P) (x : G)
    (z : Subalgebra.center k k[G]) (hz : z ∈ traceIdeal k P) (hx : z.val.coeff x ≠ 0) :
    sylowConjugateInto p P x := by
  by_contra h
  obtain ⟨a, ha⟩ := (mem_traceIdeal_iff k P z).mp hz
  rw [← ha] at hx
  exact hx (trace_coeff_eq_zero k p P hP x h a)

/-- A class-sum basis vector lies in the trace ideal exactly under the centralizer-Sylow criterion. -/
theorem classBasis_mem_traceIdeal_iff (P : Subgroup G) (hP : IsPGroup p P) (x : G) :
    classSumBasis k (ConjClasses.mk x) ∈ traceIdeal k P ↔ sylowConjugateInto p P x := by
  classical
  constructor
  · intro h
    apply sylowConjugateInto_of_mem_traceIdeal k p P hP x _ h
    rw [classSumBasis_val, classSum_coeff, ite_eq_left rfl]
    exact one_ne_zero
  · intro h
    rw [mem_traceIdeal_iff]
    obtain ⟨y, hy, hn⟩ := (sylowConjugateInto_iff_orbit_index k p P hP x).1 h
    let t : k := (P.relIndex (Subgroup.centralizer {y}) : ℕ)
    change t ≠ 0 at hn
    refine ⟨t⁻¹ • orbitSum k P y, ?_⟩
    rw [map_smul, Subalgebra.coe_smul, trace_orbitSum, classSumBasis_val, hy]
    change t⁻¹ • (t • classSum k (ConjClasses.mk x)) = classSum k (ConjClasses.mk x)
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem classSum_mem_traceIdeal_iff (P : Subgroup G) (hP : IsPGroup p P) (x : G) :
    (∃ z : Subalgebra.center k k[G], z ∈ traceIdeal k P ∧
      (z : k[G]) = classSum k (ConjClasses.mk x)) ↔ sylowConjugateInto p P x := by
  rw [← classBasis_mem_traceIdeal_iff k p P hP x]
  constructor
  · rintro ⟨z, hz, hval⟩
    have he : z = classSumBasis k (ConjClasses.mk x) :=
      Subtype.ext (hval.trans (classSumBasis_val (R := k) _).symm)
    exact he ▸ hz
  · intro h
    exact ⟨_, h, classSumBasis_val (R := k) _⟩

/-- The indicated class sums give a basis of the trace ideal over the coefficient field. -/
theorem traceIdeal_basis (P : Subgroup G) (hP : IsPGroup p P) :
    ∃ b : Module.Basis {C : ConjClasses G // eligibleClass p P C} k (traceIdeal k P),
      ∀ C, (((b C).val) : k[G]) = classSum k C.val := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  let b := classSumBasis (G := G) k
  let v : {C : ConjClasses G // eligibleClass p P C} → Subalgebra.center k k[G] :=
    fun C => b C.val
  let I : Submodule k (Subalgebra.center k k[G]) := (traceIdeal k P).restrictScalars k
  have hI : Submodule.span k (Set.range v) = I := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨C, x, hx, hp⟩, rfl⟩
      change b C ∈ traceIdeal k P
      rw [← hx]
      exact (classBasis_mem_traceIdeal_iff k p P hP x).2 hp
    · intro z hz
      obtain ⟨a, ha⟩ := (mem_traceIdeal_iff k P z).mp hz
      rw [← b.sum_repr z]
      apply Submodule.sum_mem
      intro C _
      by_cases hC : eligibleClass p P C
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩)
      · obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
        have hcoeff : b.repr z (ConjClasses.mk x) = 0 := by
          change centerClassEquiv k z (ConjClasses.mk x) = 0
          rw [centerClassEquiv_apply_mk, ← ha]
          exact trace_coeff_eq_zero k p P hP x (fun hp => hC ⟨x, rfl, hp⟩) a
        rw [hcoeff, zero_smul]
        exact Submodule.zero_mem _
  have hv : LinearIndependent k v := b.linearIndependent.comp _ Subtype.val_injective
  let bI : Module.Basis {C : ConjClasses G // eligibleClass p P C} k I :=
    (Module.Basis.span hv).map (LinearEquiv.ofEq _ _ hI)
  refine ⟨bI, ?_⟩
  intro C
  change (((bI C : I) : Subalgebra.center k k[G]) : k[G]) = _
  have hval : (bI C : Subalgebra.center k k[G]) = v C := by
    dsimp only [bI]
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  rw [hval]
  exact classSumBasis_val (R := k) C.val

end RepTheorySurvey.Modular.CentralTraceIdeals
