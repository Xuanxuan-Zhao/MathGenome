import MathGenome.Internal.Specs.D07.Ch13.FrobeniusRoots
import MathGenome.Internal.D07.Ch12.SimpleDegree
import MathGenome.Internal.D07.Ch13.PrimePowerCardinality
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Irreducible roots over a finite base (K07.13.frobenius_roots).
The simple-degree and cardinality results make K(a) a finite field.
Frobenius has order d there; homomorphisms out of K(a) are determined by a.
Normality of finite field extensions supplies splitting and conjugate roots.
The embedded-field identification is proved using X^(q^d)-X, without
identifying unrelated abstract finite-field copies.
-/

universe u v
namespace D07.Ch13.FrobeniusRoots
open Polynomial IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [Finite K]

lemma simple_field_data (f : K[X]) (a : L) (hf : Irreducible f) (ha : aeval a f = 0) :
    Finite (adjoin K {a}) ∧ Module.finrank K (adjoin K {a}) = f.natDegree ∧
      Nat.card (adjoin K {a}) = Nat.card K ^ f.natDegree := by
  have halg : IsAlgebraic K a := ⟨f, hf.ne_zero, ha⟩
  have hmin : (minpoly K a).natDegree = f.natDegree := by
    rw [← minpoly.eq_of_irreducible hf ha]
    exact natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hf.ne_zero))
  have hrank := D07.Ch12.SimpleDegree.simple_degree K L a halg
  rw [hmin] at hrank
  obtain ⟨hfinite, _, hcard⟩ :=
    D07.Ch13.PrimePowerCardinality.extension_cardinality_of_degree K (adjoin K {a})
      (Nat.card K) f.natDegree rfl hrank
  let := hfinite
  exact ⟨hfinite, Module.finrank_eq_of_rank_eq hrank, by
    simpa [Module.finrank_eq_of_rank_eq hrank] using hcard⟩

lemma splits_in_simple_field (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) : (f.map (algebraMap K (adjoin K {a}))).Splits := by
  obtain ⟨hfinite, _, _⟩ := simple_field_data f a hf ha
  let := hfinite
  let aE : adjoin K {a} := ⟨a, mem_adjoin_simple_self K a⟩
  have hmin : minpoly K aE = minpoly K a := by
    exact (minpoly.algHom_eq (adjoin K {a}).val (adjoin K {a}).val.injective aE).symm
  rw [minpoly.Irreducible.eq_minpoly hf ha, Polynomial.map_mul, Polynomial.map_C, ← hmin]
  exact Splits.mul (Splits.C _) (Normal.splits (inferInstance : Normal K (adjoin K {a})) aE)

lemma simple_field_isSplittingField (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) : IsSplittingField K (adjoin K {a}) f := by
  apply IntermediateField.isSplittingField_iff.mpr
  refine ⟨splits_in_simple_field f a hf ha, le_antisymm ?_ ?_⟩
  · apply adjoin_le_iff.mpr
    intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact subset_adjoin K _ (mem_rootSet.mpr ⟨hf.ne_zero, ha⟩)
  · apply adjoin_le_iff.mpr
    intro x hx
    have hs := (splits_in_simple_field f a hf ha).image_rootSet (adjoin K {a}).val
    rw [← hs] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property

omit [Finite K] in
lemma frobenius_pow_apply (F : Type*) [Field F] [Algebra K F] [Fintype K]
    (n : ℕ) (x : F) :
    (FiniteField.frobeniusAlgHom K F ^ n) x = x ^ (Nat.card K ^ n) := by
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
    Nat.card_eq_fintype_card]

omit [Finite K] in
lemma simple_hom_ext {a : L} {F : Type*} [Field F] [Algebra K F]
    {φ ψ : adjoin K {a} →ₐ[K] F}
    (h : φ ⟨a, mem_adjoin_simple_self K a⟩ = ψ ⟨a, mem_adjoin_simple_self K a⟩) :
    φ = ψ := by
  apply adjoin_algHom_ext K
  intro x hx
  obtain rfl : x = a := Set.mem_singleton_iff.mp hx
  exact h

lemma orbit_injective (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) :
    Function.Injective (fun i : Fin f.natDegree => a ^ (Nat.card K ^ i.val)) := by
  obtain ⟨hfinite, hdegree, _⟩ := simple_field_data f a hf ha
  let := hfinite
  let := Fintype.ofFinite K
  let E := adjoin K {a}
  let aE : E := ⟨a, mem_adjoin_simple_self K a⟩
  let Φ := FiniteField.frobeniusAlgHom K E
  have ho : orderOf Φ = f.natDegree :=
    (FiniteField.orderOf_frobeniusAlgHom K E).trans hdegree
  intro i j hij
  apply Fin.ext
  have hp : Φ ^ i.val = Φ ^ j.val := by
    apply simple_hom_ext
    change (Φ ^ i.val) aE = (Φ ^ j.val) aE
    rw [frobenius_pow_apply, frobenius_pow_apply]
    apply Subtype.ext
    exact hij
  exact pow_injOn_Iio_orderOf (ho.symm ▸ i.isLt) (ho.symm ▸ j.isLt) hp

lemma least_period (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) :
    a ^ (Nat.card K ^ f.natDegree) = a ∧
      ∀ j : ℕ, 0 < j → a ^ (Nat.card K ^ j) = a → f.natDegree ≤ j := by
  obtain ⟨hfinite, hdegree, hcard⟩ := simple_field_data f a hf ha
  let := hfinite
  let := Fintype.ofFinite K
  let E := adjoin K {a}
  let aE : E := ⟨a, mem_adjoin_simple_self K a⟩
  let Φ := FiniteField.frobeniusAlgHom K E
  have ho : orderOf Φ = f.natDegree :=
    (FiniteField.orderOf_frobeniusAlgHom K E).trans hdegree
  constructor
  · have h := congrArg (fun φ : E →ₐ[K] E => φ aE) (pow_orderOf_eq_one Φ)
    rw [ho, frobenius_pow_apply] at h
    exact congrArg (fun x : E => (x : L)) h
  · intro j hj heq
    have hp : Φ ^ j = 1 := by
      apply simple_hom_ext
      change (Φ ^ j) aE = aE
      rw [frobenius_pow_apply]
      exact Subtype.ext heq
    rw [← ho]
    exact orderOf_le_of_pow_eq_one hj hp

lemma roots_eq_orbit (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) (b : L) :
    aeval b f = 0 ↔ ∃ i : Fin f.natDegree, b = a ^ (Nat.card K ^ i.val) := by
  obtain ⟨hfinite, hdegree, _⟩ := simple_field_data f a hf ha
  let := hfinite
  let := Fintype.ofFinite K
  let E := adjoin K {a}
  let aE : E := ⟨a, mem_adjoin_simple_self K a⟩
  have haE : aeval aE f = 0 := by
    apply E.val.injective
    change E.val (aeval aE f) = E.val 0
    rw [← aeval_algHom_apply, map_zero]
    exact ha
  constructor
  · intro hb
    have hroot : b ∈ f.rootSet L := mem_rootSet.mpr ⟨hf.ne_zero, hb⟩
    rw [← (splits_in_simple_field f a hf ha).image_rootSet E.val] at hroot
    obtain ⟨bE, hbE, rfl⟩ := hroot
    have hbm : aeval bE (minpoly K aE) = 0 := by
      rw [← minpoly.eq_of_irreducible hf haE]
      simp only [aeval_mul, (mem_rootSet.mp hbE).2, zero_mul]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic aE) hbm
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgHom_pow K E).surjective σ.toAlgHom
    refine ⟨⟨i.val, hdegree ▸ i.isLt⟩, ?_⟩
    have h := congrArg (fun φ : E →ₐ[K] E => φ aE) hi
    rw [frobenius_pow_apply] at h
    change aE ^ (Nat.card K ^ i.val) = σ aE at h
    rw [hσ] at h
    exact (congrArg (fun x : E => (x : L)) h).symm
  · rintro ⟨i, rfl⟩
    let Φ := FiniteField.frobeniusAlgHom K E
    have h : aeval ((Φ ^ i.val) aE) f = 0 := by
      rw [aeval_algHom_apply, haE, map_zero]
    rw [frobenius_pow_apply] at h
    calc
      aeval (a ^ (Nat.card K ^ i.val)) f =
          E.val (aeval (aE ^ (Nat.card K ^ i.val)) f) := by
        rw [← aeval_algHom_apply]
        rfl
      _ = 0 := by rw [h, map_zero]

omit [Finite K] in
lemma finite_intermediate_mem_iff (S : IntermediateField K L) [Finite S] (x : L) :
    x ∈ S ↔ x ^ Nat.card S = x := by
  let := Fintype.ofFinite S
  constructor
  · intro hx
    have h := FiniteField.pow_card (⟨x, hx⟩ : S)
    simpa only [← Nat.card_eq_fintype_card, IntermediateField.coe_pow] using
      congrArg (fun y : S => (y : L)) h
  · intro hx
    let P : S[X] := X ^ Nat.card S - X
    have hP : P ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero S Finite.one_lt_card
    have hs : (P.map (algebraMap S S)).Splits := by
      simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
        (Polynomial.splits_X_pow_nat_card_sub_X (K := S))
    have hroot : x ∈ P.rootSet L := by
      apply mem_rootSet.mpr
      exact ⟨hP, by simpa only [P, aeval_sub, map_pow, aeval_X, sub_eq_zero] using hx⟩
    rw [← hs.image_rootSet (Algebra.ofId S L)] at hroot
    obtain ⟨y, _, hy⟩ := hroot
    exact hy ▸ y.property

lemma embedded_field_unique (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) (S : IntermediateField K L) (hS : Finite S)
    (hcard : Nat.card S = Nat.card K ^ f.natDegree) : S = adjoin K {a} := by
  obtain ⟨hfinite, _, hEcard⟩ := simple_field_data f a hf ha
  let := hS
  let := hfinite
  ext x
  rw [finite_intermediate_mem_iff, finite_intermediate_mem_iff, hcard, hEcard]

/-- The displayed orbit product is the monic associate of f, with the
leading coefficient retained for an arbitrary (not necessarily monic) f. -/
lemma orbit_factorization (f : K[X]) (a : L) (hf : Irreducible f)
    (ha : aeval a f = 0) :
    f.map (algebraMap K L) = C (algebraMap K L f.leadingCoeff) *
      ∏ i : Fin f.natDegree, ((X : L[X]) - C (a ^ (Nat.card K ^ i.val))) := by
  classical
  let r : Fin f.natDegree → L := fun i => a ^ (Nat.card K ^ i.val)
  have hinj : Function.Injective r := orbit_injective f a hf ha
  have hdvd : (∏ i, (X - C (r i))) ∣ f.map (algebraMap K L) := by
    apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
    intro i
    apply dvd_iff_isRoot.mpr
    change (f.map (algebraMap K L)).eval (r i) = 0
    rw [eval_map_algebraMap]
    exact (roots_eq_orbit f a hf ha (r i)).mpr ⟨i, rfl⟩
  have hdeg : (f.map (algebraMap K L)).natDegree ≤ (∏ i, (X - C (r i))).natDegree := by
    simp only [natDegree_map, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin, le_refl]
  have heq := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C r Finset.univ) hdvd hdeg
  simpa only [Polynomial.leadingCoeff_map, mul_comm] using heq

theorem frobenius_roots : Specs.D07.Ch13.FrobeniusRoots.FrobeniusRootsTheorem.{u, v} := by
  intro K L _ _ _ _ f a hf ha
  obtain ⟨hfinite, hdegree, hcard⟩ := simple_field_data f a hf ha
  let := hfinite
  obtain ⟨hperiod, hleast⟩ := least_period f a hf ha
  refine ⟨?_, hfinite, hdegree, hcard, simple_field_isSplittingField f a hf ha,
    ?_, embedded_field_unique f a hf ha, orbit_injective f a hf ha,
    roots_eq_orbit f a hf ha, hperiod, hleast,
    PerfectField.separable_of_irreducible hf, orbit_factorization f a hf ha⟩
  · rw [← hdegree]
    exact Module.finrank_pos
  · intro x
    rw [← hcard]
    exact finite_intermediate_mem_iff _ x

end D07.Ch13.FrobeniusRoots
