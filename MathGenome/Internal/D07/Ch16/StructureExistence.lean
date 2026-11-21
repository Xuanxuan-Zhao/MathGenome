import MathGenome.Internal.Specs.D07.Ch16.StructureExistence
import MathGenome.Internal.D07.Ch16.Smith
import MathGenome.Internal.D07.Ch16.FinitePresentation
import MathGenome.Internal.D07.Ch10.UfdNotPid
import Mathlib.Data.Fintype.Sort
import Mathlib.Algebra.Module.PID

universe u v w
noncomputable section
namespace D07.Ch16.StructureExistence
open Module
open scoped DirectSum

/-- Restrict a finite product to its nontrivial coordinates. -/
def restrictProduct {R : Type u} [CommRing R] {ι : Type v}
    (A : ι → Type w) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (P : ι → Prop) [DecidablePred P] (h : ∀ i, ¬ P i → Subsingleton (A i)) :
    (∀ i, A i) ≃ₗ[R] (∀ i : {i // P i}, A i.val) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => LinearMap.proj i.val) (by
    constructor
    · intro x y hxy
      funext i
      by_cases hi : P i
      · exact congrArg (fun z => z ⟨i, hi⟩) hxy
      · let := h i hi
        exact Subsingleton.elim _ _
    · intro y
      refine ⟨fun i => if hi : P i then y ⟨i, hi⟩ else 0, ?_⟩
      funext i
      simp [i.property])

/-- Every element of a nonzero-annihilator cyclic quotient is killed by that
annihilator; the assertion includes the zero quotient of a unit. -/
theorem quotient_annihilated {R : Type u} [CommRing R] (d : R)
    (x : R ⧸ Ideal.span {d}) : d • x = 0 := by
  change Ideal.Quotient.mk _ d * x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d)), zero_mul]

/-- Finite products of cyclic quotients have a common nonzero annihilator. -/
theorem quotientProduct_torsion {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type v} [Fintype ι] (d : ι → R) (hd : ∀ i, d i ≠ 0) :
    Module.IsTorsion R (∀ i, R ⧸ Ideal.span {d i}) := by
  classical
  intro x
  refine ⟨⟨∏ i, d i, mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr
    (fun i _ => hd i))⟩, ?_⟩
  change (∏ i, d i) • x = 0
  ext i
  change (∏ j, d j) • x i = 0
  rw [Fintype.prod_eq_prod_compl_mul i, mul_smul, quotient_annihilated, smul_zero]

/-- Torsion is preserved by a linear isomorphism. -/
theorem torsion_equiv {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) :
    Module.IsTorsion R M ↔ Module.IsTorsion R N := by
  constructor
  · intro h x
    obtain ⟨a, ha⟩ := @h (E.symm x)
    refine ⟨a, ?_⟩
    change (a : R) • x = 0
    change (a : R) • E.symm x = 0 at ha
    calc
      (a : R) • x = E ((a : R) • E.symm x) := by rw [map_smul, E.apply_symm_apply]
      _ = 0 := by rw [ha, map_zero]
  · intro h x
    obtain ⟨a, ha⟩ := @h (E x)
    refine ⟨a, ?_⟩
    change (a : R) • E x = 0 at ha
    change (a : R) • x = 0
    apply E.injective
    rw [map_smul, map_zero]
    exact ha

/-- The free factor cannot have a coordinate if the product is torsion. -/
theorem product_freeRank {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type v} [Fintype ι] (r : ℕ) (d : ι → R) (hd : ∀ i, d i ≠ 0) :
    r = 0 ↔ Module.IsTorsion R ((Fin r → R) × (∀ i, R ⧸ Ideal.span {d i})) := by
  constructor
  · rintro rfl ⟨f, x⟩
    obtain ⟨a, ha⟩ := @quotientProduct_torsion R _ _ ι _ d hd x
    refine ⟨a, Prod.ext (Subsingleton.elim _ _) ha⟩
  · intro h
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    obtain ⟨a, ha⟩ := @h ((fun _ => 1), 0)
    have heq := congrArg (fun x => x.1 i) ha
    change (a : R) * 1 = 0 at heq
    have hz : (a : R) = 0 := by simpa only [mul_one] using heq
    exact nonZeroDivisors.coe_ne_zero a hz

theorem freeRankCriterion : Specs.D07.Ch16.StructureExistence.FreeRankCriterion.{u, v} := by
  intro R _ _ M _ _ r s d hd ⟨E⟩
  let F := DirectSum.linearEquivFunOnFintype R (Fin s) (fun i => R ⧸ Ideal.span {d i})
  exact (product_freeRank r d hd).trans
    (torsion_equiv (E.trans ((LinearEquiv.refl R _).prodCongr F))).symm

theorem freeIffTorsionFree : Specs.D07.Ch16.StructureExistence.FreeIffTorsionFree.{u, v} := by
  intro R _ _ _ M _ _ _
  exact Module.free_iff_isTorsionFree

theorem rational_not_free : ¬ Module.Free ℤ ℚ := by
  intro hf
  let := hf
  let b := Module.Free.chooseBasis ℤ ℚ
  let i := b.index_nonempty.some
  have h : (2 : ℤ) • (b i / 2) = b i := by
    simp only [zsmul_eq_mul]
    exact mul_div_cancel₀ _ (by norm_num : (2 : ℚ) ≠ 0)
  have hc := congrArg (fun x => b.repr x i) h
  have htwo : 2 * (b.repr (b i / 2) i) = (1 : ℤ) := by
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, Basis.repr_self,
      Finsupp.single_eq_same] using hc
  omega

theorem rationalCounterexample : Specs.D07.Ch16.StructureExistence.RationalCounterexample := by
  refine ⟨inferInstance, rational_not_free, ?_⟩
  intro hf
  let := hf
  exact rational_not_free ((freeIffTorsionFree ℤ ℚ).mpr (by infer_instance))

/-- Smith form followed by increasing reindexing of its nonunit entries. -/
theorem invariantFactors (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (r s : ℕ) (d : Fin s → R), (∀ i, d i ≠ 0 ∧ ¬ IsUnit (d i)) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧
      Nonempty (M ≃ₗ[R] ((Fin r → R) × (∀ i : Fin s, R ⧸ Ideal.span {d i}))) := by
  classical
  obtain ⟨_, n, m, A, ⟨E⟩⟩ := D07.Ch16.FinitePresentation.pidPresentation R M
  obtain ⟨s, k, r, _, _, a, _, _, hne, hchain, _, _, ⟨F⟩, _⟩ :=
    D07.Ch16.Smith.smithDecomposition R m n
      (Specs.D07.Ch16.FinitePresentation.matrixMap A)
  obtain ⟨U, _⟩ := D07.Ch16.Smith.unitCancellation R s a
  let J := {i : Fin s // ¬ IsUnit (a i)}
  let q : Fin (Fintype.card J) ≃o J := monoEquivOfFin J rfl
  let V := (LinearEquiv.piCongrLeft R
    (fun i : J => R ⧸ Ideal.span {a i.val}) q.toEquiv).symm
  refine ⟨r, Fintype.card J, fun i => a (q i).val, ?_, ?_,
    ⟨E.trans (F.trans ((LinearEquiv.refl R _).prodCongr (U.trans V)))⟩⟩
  · intro i
    exact ⟨hne _, (q i).property⟩
  · intro i j hij
    exact hchain _ _ (q.monotone hij)

/-- A free ideal has at most one basis vector: commuting its two underlying
ring elements gives a dependence relation. This works for infinite bases. -/
theorem freeIdealPrincipal : Specs.D07.Ch16.StructureExistence.FreeIdealPrincipal.{u} := by
  intro R _ _ I hfree
  classical
  let := hfree
  by_cases hI : I = ⊥
  · exact ⟨0, by simpa using hI⟩
  have : Nontrivial I := (Submodule.nontrivial_iff_ne_bot).mpr hI
  let b := Module.Free.chooseBasis R I
  let ι := Module.Free.ChooseBasisIndex R I
  have hsingle : Subsingleton ι := by
    constructor
    intro i j
    by_contra hij
    have heq : (b j : R) • b i = (b i : R) • b j := by
      apply Subtype.ext
      exact mul_comm _ _
    have hc := congrArg (fun x => b.repr x i) heq
    have hz : (b j : R) = 0 := by simpa [hij, Ne.symm hij] using hc
    exact b.ne_zero j (Subtype.ext hz)
  let := hsingle
  let i : ι := Classical.choice inferInstance
  refine ⟨(b i : R), le_antisymm ?_ ?_⟩
  · intro x hx
    let y : I := ⟨x, hx⟩
    have heq : b.repr y i • b i = y := by
      apply b.repr.injective
      ext j
      have hj : j = i := Subsingleton.elim _ _
      subst j
      simp
    exact Ideal.mem_span_singleton.mpr ⟨b.repr y i, by
      simpa [mul_comm] using congrArg Subtype.val heq.symm⟩
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (b i).property)

theorem nonprincipalIdealCounterexample :
    Specs.D07.Ch16.StructureExistence.NonprincipalIdealCounterexample := by
  intro h
  exact D07.Ch10.UfdNotPid.twoXIdealNotPrincipal
    (freeIdealPrincipal (Polynomial ℤ) _ h)

/-- The integer module is not torsion, so it cannot be any finite sum of
cyclic modules with nonzero annihilators. -/
theorem integerNeedsFreePart : Specs.D07.Ch16.StructureExistence.IntegerNeedsFreePart := by
  have hZ : ¬ Module.IsTorsion ℤ ℤ := by
    intro h
    obtain ⟨a, ha⟩ := @h 1
    change (a : ℤ) * 1 = 0 at ha
    exact nonZeroDivisors.coe_ne_zero a (by simpa only [mul_one] using ha)
  refine ⟨hZ, ?_⟩
  intro s d hd ⟨E⟩
  let F := DirectSum.linearEquivFunOnFintype ℤ (Fin s) (fun i => ℤ ⧸ Ideal.span {d i})
  exact hZ ((torsion_equiv (E.trans F)).mpr (quotientProduct_torsion d hd))

/-- Refine the finite cyclic torsion part into positive prime powers. The
library's torsion theorem permits exponent zero; those factors are deleted.
Normalizing prime bases chooses one representative of each associate class. -/
theorem elementaryDivisors (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (s : ℕ) (d : Fin s → R) (hd : ∀ i, d i ≠ 0) :
    ∃ (t : ℕ) (p : Fin t → R) (e : Fin t → ℕ),
      (∀ i, Prime (p i) ∧ 0 < e i) ∧
      (∀ i j, Associated (p i) (p j) → p i = p j) ∧
      Nonempty ((∀ i, R ⧸ Ideal.span {d i}) ≃ₗ[R]
        (⨁ i : Fin t, R ⧸ Ideal.span {p i ^ e i})) := by
  classical
  letI := UniqueFactorizationMonoid.strongNormalizationMonoid (α := R)
  obtain ⟨I, fI, p, hp, e, ⟨E⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (quotientProduct_torsion d hd)
  let J := {i : I // 0 < e i}
  let U := restrictProduct (R := R) (fun i => R ⧸ Ideal.span {p i ^ e i})
    (fun i => 0 < e i) (by
      intro i hi
      have he : e i = 0 := Nat.eq_zero_of_not_pos hi
      rw [he, pow_zero]
      exact (D07.Ch16.Smith.unitQuotient R 1).mpr isUnit_one)
  let W : (∀ i : J, R ⧸ Ideal.span {p i.val ^ e i.val}) ≃ₗ[R]
      (∀ i : J, R ⧸ Ideal.span {(normalize (p i.val)) ^ e i.val}) :=
    LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _
      (Ideal.span_singleton_eq_span_singleton.mpr
        ((associated_normalize (p i.val)).pow_pow)))
  let q : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let V := (LinearEquiv.piCongrLeft R
    (fun i : J => R ⧸ Ideal.span {(normalize (p i.val)) ^ e i.val}) q).symm
  refine ⟨Fintype.card J, fun i => normalize (p (q i).val),
    fun i => e (q i).val, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(associated_normalize _).prime (irreducible_iff_prime.mp (hp _)), (q i).property⟩
  · intro i j hij
    simpa only [normalize_idem] using normalize_eq_normalize_iff_associated.mpr hij
  · exact ⟨E.trans ((DirectSum.linearEquivFunOnFintype R I _).trans
      (U.trans (W.trans (V.trans
        (DirectSum.linearEquivFunOnFintype R (Fin (Fintype.card J)) _).symm))))⟩

theorem structureExistence : Specs.D07.Ch16.StructureExistence.Decompositions.{u, v} := by
  intro R _ _ _ M _ _ _
  obtain ⟨r, s, d, hd, hchain, ⟨E⟩⟩ := invariantFactors R M
  obtain ⟨t, p, e, hp, hrep, ⟨F⟩⟩ := elementaryDivisors R s d (fun i => (hd i).1)
  let U := (DirectSum.linearEquivFunOnFintype R (Fin s)
    (fun i => R ⧸ Ideal.span {d i})).symm
  let G := E.trans ((LinearEquiv.refl R _).prodCongr U)
  refine ⟨r, s, t, d, p, e, hd, hchain, hp, hrep,
    ⟨G⟩, ⟨E.trans ((LinearEquiv.refl R _).prodCongr F)⟩, ?_⟩
  exact freeRankCriterion R M r s d (fun i => (hd i).1) ⟨G⟩

end D07.Ch16.StructureExistence
