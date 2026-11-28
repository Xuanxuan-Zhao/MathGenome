import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.RelativeTrace
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.BrauerHomomorphism

namespace RepTheorySurvey.Modular.BrauerHomomorphism

open RelativeTrace
open scoped BigOperators

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- The group algebra of the centralizer of `P` in `G`. -/
abbrev CentralizerAlgebra (P : Subgroup G) := BrauerHomomorphismSpec.CentralizerAlgebra k P

/-- Restrict coefficients of a conjugation invariant to the centralizer. -/
noncomputable def projection (P : Subgroup G) :
    fixedSubalgebra k P →ₗ[k] CentralizerAlgebra k P :=
  BrauerHomomorphismSpec.projection k P

@[simp]
theorem coeff_projection {P : Subgroup G} (a : fixedSubalgebra k P)
    (x : Subgroup.centralizer (P : Set G)) :
    (projection k P a).coeff x = a.val.coeff x := rfl

private theorem coeff_conjugation (g : G) (a : MonoidAlgebra k G) (x : G) :
    (conjugation k g a).coeff x = a.coeff ((MulAut.conj g).symm x) :=
  MonoidAlgebra.coeff_domCongr _ _ _

private theorem coeff_conj_of_mem_fixed {P : Subgroup G} (a : fixedSubalgebra k P)
    (g : P) (x : G) : a.val.coeff (MulAut.conj (g : G) x) = a.val.coeff x := by
  have ha : conjugation k (g : G) a.val = a.val := a.property g
  have h := congrArg (fun b : MonoidAlgebra k G => b.coeff (MulAut.conj (g : G) x)) ha
  simpa only [coeff_conjugation, MulEquiv.symm_apply_apply] using h.symm

-- Both action and scalar notation use conjugation in the orbit calculations below.
private local instance (priority := 2000) conjugationAction (P : Subgroup G) : MulAction P G :=
  MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp P.subtype)

private local instance (priority := 2000) conjugationSMul (P : Subgroup G) : SMul P G :=
  (conjugationAction P).toSMul

private theorem smul_eq_conj (P : Subgroup G) (g : P) (x : G) :
    g • x = MulAut.conj (g : G) x := rfl

private theorem fixedPoints_eq_centralizer (P : Subgroup G) :
    MulAction.fixedPoints P G = (Subgroup.centralizer (P : Set G) : Set G) := by
  ext x
  simp only [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    smul_eq_conj, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact Subtype.forall

private theorem coeff_mul_eq_sum [Fintype G] (a b : MonoidAlgebra k G) (z : G) :
    (a * b).coeff z = ∑ x : G, a.coeff x * b.coeff (x⁻¹ * z) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  exact fun x => zero_mul _

private theorem cast_eq_zero_of_dvd {p n : ℕ} [CharP k p] (h : p ∣ n) :
    (n : k) = 0 := (CharP.cast_eq_zero_iff k p n).mpr h

private noncomputable local instance orbitFintype {H X : Type*} [Group H] [MulAction H X]
    [Finite X] (x : X) : Fintype (MulAction.orbit H x) := Fintype.ofFinite _

private noncomputable local instance orbitQuotientFintype (H X : Type*) [Group H] [MulAction H X]
    [Finite X] : Fintype (MulAction.orbitRel.Quotient H X) := Fintype.ofFinite _

private theorem sum_eq_sum_orbits {H X M : Type*} [Group H] [MulAction H X]
    [Fintype X] [AddCommMonoid M] (w : X → M) :
    ∑ x : X, w x =
      ∑ o : MulAction.orbitRel.Quotient H X, ∑ x : MulAction.orbit H o.out, w x := by
  let e := MulAction.selfEquivSigmaOrbits H X
  calc
    _ = ∑ y : Σ o : MulAction.orbitRel.Quotient H X, MulAction.orbit H o.out, w (y.2 : X) :=
      (e.symm.sum_comp w).symm
    _ = _ := Fintype.sum_sigma _

/-- For a finite action of a `p`-group, only singleton orbits contribute to the sum of an
invariant weight in characteristic `p`. -/
private theorem sum_eq_sum_fixedPoints {H X : Type*} [Group H] [MulAction H X]
    [Fintype X] [Fintype (MulAction.fixedPoints H X)] {p : ℕ} [Fact p.Prime] [CharP k p]
    (hH : IsPGroup p H) (f : X → k) (hf : ∀ (g : H) x, f (g • x) = f x) :
    ∑ x : X, f x = ∑ x : MulAction.fixedPoints H X, f x := by
  classical
  have hsum : (∑ x : MulAction.fixedPoints H X, f x) =
      ∑ x : X, if x ∈ MulAction.fixedPoints H X then f x else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hsum, sum_eq_sum_orbits (H := H) f,
    sum_eq_sum_orbits (H := H) (fun x => if x ∈ MulAction.fixedPoints H X then f x else 0)]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hfix : o.out ∈ MulAction.fixedPoints H X
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hx := MulAction.mem_fixedPoints'.mp hfix x x.property
    simp [hx, hfix]
  · have hnot (x : MulAction.orbit H o.out) : (x : X) ∉ MulAction.fixedPoints H X := by
      intro hx
      apply hfix
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
      have h : (x : X) = o.out := by
        calc
          (x : X) = g⁻¹ • (x : X) := ((MulAction.mem_fixedPoints.mp hx) g⁻¹).symm
          _ = o.out := by rw [← hg, inv_smul_smul]
      rwa [h] at hx
    simp only [hnot, ite_false, Finset.sum_const_zero]
    have heq (x : MulAction.orbit H o.out) : f x = f o.out := by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
      rw [← hg, hf]
    simp only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    obtain ⟨n, hn⟩ := hH.card_orbit o.out
    have hn0 : n ≠ 0 := by
      intro h
      apply hfix
      apply MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr
      simpa [h, Nat.card_eq_fintype_card] using hn
    have hdvd : p ∣ Fintype.card (MulAction.orbit H o.out) := by
      rw [← Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self p hn0
    rw [cast_eq_zero_of_dvd k hdvd, zero_mul]

private theorem projection_one (P : Subgroup G) :
    projection k P 1 = 1 := by
  classical
  ext x
  simp only [coeff_projection, Subalgebra.coe_one, MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Subtype.ext_iff, Subgroup.coe_one]

/-- Every element of the centralizer group algebra lifts to a conjugation invariant. -/
theorem projection_surjective (P : Subgroup G) : Function.Surjective (projection k P) := by
  intro b
  change b ∈ LinearMap.range (projection k P)
  induction b using MonoidAlgebra.induction_on with
  | of x =>
      let a : fixedSubalgebra k P :=
        ⟨MonoidAlgebra.single x.val 1, fun g => by
          change conjugation k (g : G) (MonoidAlgebra.single x.val 1) = _
          rw [conjugation_single]
          congr 1
          exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp x.property g g.property)⟩
      exact ⟨a, MonoidAlgebra.comapDomain_single_map Subtype.val Subtype.val_injective x 1⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

private theorem coeff_conj_of_mem_center {a : MonoidAlgebra k G}
    (ha : a ∈ Subalgebra.center k (MonoidAlgebra k G)) (g x : G) :
    a.coeff (MulAut.conj g x) = a.coeff x := by
  have h := Subalgebra.mem_center_iff.mp ha (MonoidAlgebra.single g 1)
  have hcoeff := congrArg (fun b : MonoidAlgebra k G => b.coeff (g * x)) h
  simpa [MulAut.conj_apply] using hcoeff.symm

theorem center_le_fixedSubalgebra (P : Subgroup G) :
    Subalgebra.center k (MonoidAlgebra k G) ≤ fixedSubalgebra k P := by
  intro a ha
  rw [mem_fixedSubalgebra_iff]
  intro g
  ext x
  rw [coeff_conjugation, MulAut.conj_symm_apply]
  simpa [MulAut.conj_apply] using coeff_conj_of_mem_center k ha (g : G)⁻¹ x

theorem projection_maps_center (P : Subgroup G) (a : fixedSubalgebra k P)
    (ha : a.val ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    projection k P a ∈ Subalgebra.center k (CentralizerAlgebra k P) := by
  apply Subalgebra.mem_center_iff.mpr
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g =>
      ext x
      change (MonoidAlgebra.single g 1 * projection k P a).coeff x =
        (projection k P a * MonoidAlgebra.single g 1).coeff x
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        one_mul, mul_one, coeff_projection, Subgroup.coe_mul, Subgroup.coe_inv]
      have h := coeff_conj_of_mem_center k ha (g : G) ((g : G)⁻¹ * (x : G))
      simpa [MulAut.conj_apply, ← mul_assoc] using h.symm
  | add x y hx hy => simp only [add_mul, mul_add, hx, hy]
  | smul r x hx => simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hx]

private theorem conjugation_mem_conjugate_fixed (g : G) (P : Subgroup G)
    (a : fixedSubalgebra k P) :
    conjugation k g a.val ∈ fixedSubalgebra k (P.map (MulAut.conj g).toMonoidHom) := by
  rw [mem_fixedSubalgebra_iff]
  rintro ⟨_, x, hx, rfl⟩
  change conjugation k (MulAut.conj g x) (conjugation k g a.val) = conjugation k g a.val
  have hmul : MulAut.conj g x * g = g * x := by simp [MulAut.conj_apply, mul_assoc]
  have hfix : conjugation k x a.val = a.val := a.property ⟨x, hx⟩
  simp only [conjugation] at hfix ⊢
  rw [← RelativeTraceSpec.conjugation_mul_apply, hmul,
    RelativeTraceSpec.conjugation_mul_apply, hfix]

theorem projection_conjugation (g : G) (P : Subgroup G) (a : fixedSubalgebra k P) :
    ∃ b : fixedSubalgebra k (P.map (MulAut.conj g).toMonoidHom),
      b.val = conjugation k g a.val ∧
      projection k _ b =
        MonoidAlgebra.domCongr k k (BrauerHomomorphismSpec.centralizerConjugation g P)
          (projection k P a) := by
  let b : fixedSubalgebra k (P.map (MulAut.conj g).toMonoidHom) :=
    ⟨conjugation k g a.val, conjugation_mem_conjugate_fixed k g P a⟩
  refine ⟨b, rfl, ?_⟩
  let e := BrauerHomomorphismSpec.centralizerConjugation g P
  ext z
  obtain ⟨x, rfl⟩ := e.surjective z
  have hx : (e x : G) = MulAut.conj g x.val := rfl
  rw [coeff_projection, MonoidAlgebra.coeff_domCongr, e.symm_apply_apply, coeff_projection]
  change (conjugation k g a.val).coeff (e x : G) = _
  rw [coeff_conjugation, hx, MulEquiv.symm_apply_apply]

/-- The stabilizer of a basis element, viewed inside the ambient group. -/
private def stabilizerSubgroup (P : Subgroup G) (x : G) : Subgroup G :=
  P ⊓ Subgroup.centralizer ({x} : Set G)

private theorem stabilizerSubgroup_le (P : Subgroup G) (x : G) :
    stabilizerSubgroup P x ≤ P := inf_le_left

private theorem mem_stabilizerSubgroup_iff (P : Subgroup G) (x : G) (g : P) :
    g.val ∈ stabilizerSubgroup P x ↔ g • x = x := by
  change g.val ∈ P ∧ g.val ∈ Subgroup.centralizer ({x} : Set G) ↔ _
  simp only [g.property, true_and, Subgroup.mem_centralizer_singleton_iff, smul_eq_conj,
    MulAut.conj_apply, mul_inv_eq_iff_eq_mul]

private theorem stabilizerSubgroup_lt (P : Subgroup G) {x : G}
    (hx : x ∉ MulAction.fixedPoints P G) : stabilizerSubgroup P x < P := by
  refine lt_of_le_of_ne (stabilizerSubgroup_le P x) fun h => hx ?_
  apply MulAction.mem_fixedPoints.mpr
  intro g
  exact (mem_stabilizerSubgroup_iff P x g).mp (h.symm ▸ g.property)

private noncomputable def stabilizerSingle (P : Subgroup G) (x : G) (r : k) :
    fixedSubalgebra k (stabilizerSubgroup P x) :=
  ⟨MonoidAlgebra.single x r, fun g => by
    change conjugation k (g : G) (MonoidAlgebra.single x r) = _
    rw [conjugation_single]
    have hg : g.val ∈ P := stabilizerSubgroup_le P x g.property
    have hfix := (mem_stabilizerSubgroup_iff P x ⟨g.val, hg⟩).mp g.property
    exact congrArg (fun y => MonoidAlgebra.single y r) hfix⟩

variable [Finite G]

/-- Multiplicativity of the coefficient projection at a `p`-subgroup. -/
theorem projection_mul {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) (a b : fixedSubalgebra k P) :
    projection k P (a * b) = projection k P a * projection k P b := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
  let : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  ext z
  let f (x : G) := a.val.coeff x * b.val.coeff (x⁻¹ * z.val)
  have hz (g : P) : g • z.val = z.val := by
    have h : z.val ∈ MulAction.fixedPoints P G := by
      rw [fixedPoints_eq_centralizer]
      exact z.property
    exact h g
  have hf (g : P) (x : G) : f (g • x) = f x := by
    have he : (g • x)⁻¹ * z.val = g • (x⁻¹ * z.val) := by
      simp only [smul_eq_conj, map_mul, map_inv]
      exact congrArg ((MulAut.conj (g : G) x)⁻¹ * ·) (hz g).symm
    rw [show f (g • x) = a.val.coeff (g • x) * b.val.coeff ((g • x)⁻¹ * z.val) from rfl,
      he, smul_eq_conj, smul_eq_conj, coeff_conj_of_mem_fixed, coeff_conj_of_mem_fixed]
  -- The first coordinate parametrizes pairs `(x, x⁻¹ * z)` with product `z`.
  simp only [coeff_projection, Subalgebra.coe_mul, coeff_mul_eq_sum]
  change (∑ x : G, f x) = ∑ x : Subgroup.centralizer (P : Set G), f x
  rw [sum_eq_sum_fixedPoints k hP f hf]
  exact Fintype.sum_equiv (Set.equivOfEq (fixedPoints_eq_centralizer P)) _ _ (fun _ => rfl)

/-- The Brauer homomorphism for a finite-group `p`-subgroup in characteristic `p`. -/
noncomputable def brauerHom {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) : fixedSubalgebra k P →ₐ[k] CentralizerAlgebra k P :=
  AlgHom.ofLinearMap (projection k P) (projection_one k P) (projection_mul k hP)

@[simp]
theorem coeff_brauerHom {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) (a : fixedSubalgebra k P) (x : Subgroup.centralizer (P : Set G)) :
    (brauerHom k hP a).coeff x = a.val.coeff x := rfl

theorem projection_algebraHom {p : ℕ} [Fact p.Prime] [CharP k p] (P : Subgroup G)
    (hP : IsPGroup p P) :
    ∃ f : fixedSubalgebra k P →ₐ[k] CentralizerAlgebra k P,
      f.toLinearMap = projection k P :=
  ⟨brauerHom k hP, rfl⟩

noncomputable local instance (Q P : Subgroup G) : Fintype (LeftCosets Q P) :=
  Fintype.ofFinite _

private theorem projection_relativeTrace_eq_zero {p : ℕ} [Fact p.Prime] [CharP k p]
    {Q P : Subgroup G} (hP : IsPGroup p P) (hQP : Q < P) (a : fixedSubalgebra k Q) :
    projection k P (relativeTrace k hQP.le a) = 0 := by
  ext z
  have hcard : p ∣ Fintype.card (LeftCosets Q P) := by
    obtain ⟨n, hn⟩ := hP.index (Q.subgroupOf P)
    change p ∣ Fintype.card (P ⧸ Q.subgroupOf P)
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hn]
    refine dvd_pow_self p fun hz => hQP.not_ge ?_
    rw [hz, pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hn
    exact hn
  have hz (g : P) : (MulAut.conj (g : G)).symm z.val = z.val := by
    apply (MulAut.conj (g : G)).injective
    rw [MulEquiv.apply_symm_apply, MulAut.conj_apply]
    exact (mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp z.property g g.property)).symm
  rw [coeff_projection, relativeTrace_eq_sum k hQP.le a Quotient.out Quotient.out_eq']
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_conjugation, hz,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cast_eq_zero_of_dvd k hcard, zero_mul,
    MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

private theorem trace_stabilizerSingle (P : Subgroup G) (x : G) (r : k) :
    (relativeTrace k (stabilizerSubgroup_le P x) (stabilizerSingle k P x r)).val =
      ∑ y : MulAction.orbit P x, MonoidAlgebra.single y.val r := by
  let e₀ : LeftCosets (stabilizerSubgroup P x) P ≃ P ⧸ MulAction.stabilizer P x :=
    Quotient.congr (Equiv.refl P) fun g h => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      exact mem_stabilizerSubgroup_iff P x (g⁻¹ * h)
  let e := e₀.trans (MulAction.orbitEquivQuotientStabilizer P x).symm
  rw [relativeTrace_eq_sum k (stabilizerSubgroup_le P x) _ Quotient.out Quotient.out_eq']
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have hc : e₀ c = QuotientGroup.mk c.out := congrArg e₀ (QuotientGroup.out_eq' c).symm
  change conjugation k (c.out : G) (MonoidAlgebra.single x r) =
    MonoidAlgebra.single ((MulAction.orbitEquivQuotientStabilizer P x).symm (e₀ c) : G) r
  rw [hc, MulAction.orbitEquivQuotientStabilizer_symm_apply, smul_eq_conj, conjugation_single]
  rfl

/-- The kernel is the sum of the images of the traces from the proper subgroups of `P`. -/
theorem projection_kernel {p : ℕ} [Fact p.Prime] [CharP k p] (P : Subgroup G)
    (hP : IsPGroup p P) :
    LinearMap.ker (projection k P) =
      ⨆ Q : {Q : Subgroup G // Q < P}, LinearMap.range (relativeTrace k Q.property.le) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let R := ⨆ Q : {Q : Subgroup G // Q < P}, LinearMap.range (relativeTrace k Q.property.le)
  refine le_antisymm ?_ (iSup_le fun Q => ?_)
  · intro a ha
    let Ω := MulAction.orbitRel.Quotient P G
    let term (o : Ω) := relativeTrace k (stabilizerSubgroup_le P o.out)
      (stabilizerSingle k P o.out (a.val.coeff o.out))
    have hdecomp : a = ∑ o : Ω, term o := by
      apply Subtype.ext
      rw [show (∑ o : Ω, term o).val = ∑ o : Ω, (term o).val from
        map_sum (fixedSubalgebra k P).val _ _]
      simp only [term, trace_stabilizerSingle]
      have hsingle : a.val = ∑ x : G, MonoidAlgebra.single x (a.val.coeff x) := by
        rw [← Finsupp.sum_fintype _ _ (fun x => MonoidAlgebra.single_zero x)]
        exact (MonoidAlgebra.sum_coeff_single a.val).symm
      conv_lhs => rw [hsingle, sum_eq_sum_orbits (H := P)]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun x _ => ?_
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
      rw [← hg, smul_eq_conj, coeff_conj_of_mem_fixed]
    change a ∈ R
    rw [hdecomp]
    refine Submodule.sum_mem R fun o _ => ?_
    by_cases ho : o.out ∈ MulAction.fixedPoints P G
    · have hx : o.out ∈ Subgroup.centralizer (P : Set G) := by
        rwa [fixedPoints_eq_centralizer P] at ho
      have hz : a.val.coeff o.out = 0 := by
        have h := congrArg (fun b : CentralizerAlgebra k P => b.coeff ⟨o.out, hx⟩)
          (LinearMap.mem_ker.mp ha)
        exact h
      have hterm : term o = 0 := by
        dsimp only [term]
        rw [hz]
        have hzero : stabilizerSingle k P o.out 0 = 0 := by
          apply Subtype.ext
          exact MonoidAlgebra.single_zero _
        rw [hzero, map_zero]
      simpa only [hterm] using R.zero_mem
    · exact Submodule.mem_iSup_of_mem ⟨_, stabilizerSubgroup_lt P ho⟩ ⟨_, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact projection_relativeTrace_eq_zero k hP Q.property a

/-- Surjectivity of the bundled Brauer homomorphism. -/
theorem brauerHom_surjective {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) : Function.Surjective (brauerHom k hP) :=
  projection_surjective k P

@[simp]
theorem brauerHom_toLinearMap {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) : (brauerHom k hP).toLinearMap = projection k P := rfl

theorem brauerHom_kernel {p : ℕ} [Fact p.Prime] [CharP k p] {P : Subgroup G}
    (hP : IsPGroup p P) :
    LinearMap.ker (brauerHom k hP).toLinearMap =
      ⨆ Q : {Q : Subgroup G // Q < P}, LinearMap.range (relativeTrace k Q.property.le) :=
  projection_kernel k P hP

end RepTheorySurvey.Modular.BrauerHomomorphism
