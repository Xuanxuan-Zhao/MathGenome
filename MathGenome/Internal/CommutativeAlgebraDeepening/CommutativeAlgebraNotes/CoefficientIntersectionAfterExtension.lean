import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteCoefficientSubrings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SeparableInseparableTower
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientIntersectionAfterExtension
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

namespace CommutativeAlgebraNotes

open IntermediateField Polynomial

noncomputable section

private theorem adjoin_singleton_toSubfield {L : Type*} [Field L] (A : Subfield L) (c : L) :
    (adjoin A {c}).toSubfield = A ⊔ Subfield.closure {c} := by
  rw [adjoin_toSubfield, Subfield.closure_union]
  have hrange : Set.range (algebraMap A L) = (A : Set L) := Subtype.range_coe
  rw [hrange, Subfield.closure_eq]

private theorem aeval_map_inclusion {L : Type*} [Field L] {A C : Subfield L}
    (h : A ≤ C) (c : L) (P : A[X]) :
    aeval c (P.map (Subfield.inclusion h)) = aeval c P := by
  simp only [aeval_def, eval₂_map]
  rfl

/-- A single minimal polynomial over the common field gives unique polynomial
coordinates for elements of the simple adjunction over each smaller field. -/
private theorem iInf_sup_closure_singleton {L ι : Type*} [Field L] [Nonempty ι]
    (D : ι → Subfield L) {A C : Subfield L} (hA : (⨅ i, D i) = A) (hAC : A ≤ C)
    (hC : ∀ i, ∃ j, D j ≤ D i ∧ D j ≤ C)
    (c : L) (P : A[X]) (hP : P.Monic)
    (hmin : P.map (Subfield.inclusion hAC) = minpoly C c) :
    (⨅ i, D i ⊔ Subfield.closure {c}) = A ⊔ Subfield.closure {c} := by
  classical
  have hAD (i) : A ≤ D i := hA ▸ iInf_le D i
  have hroot : aeval c P = 0 := by
    rw [← aeval_map_inclusion hAC c P, hmin]
    exact minpoly.aeval C c
  have hdeg : (minpoly C c).degree = P.degree := by
    rw [← hmin, degree_map_eq_of_injective (Subfield.inclusion hAC).injective]
  refine le_antisymm (fun x hx ↦ ?_) (le_iInf fun i ↦ sup_le_sup_right (hAD i) _)
  have choosePolynomial (i) :
      ∃ q : (D i)[X], q.degree < P.degree ∧ aeval c q = x := by
    have hx' : x ∈ adjoin (D i) {c} := by
      rw [← mem_toSubfield, adjoin_singleton_toSubfield]
      exact Subfield.mem_iInf.mp hx i
    let Q := P.map (Subfield.inclusion (hAD i))
    have hQ : Q.Monic := hP.map _
    have hQroot : aeval c Q = 0 := (aeval_map_inclusion _ _ _).trans hroot
    have hc : IsIntegral (D i) c := ⟨Q, hQ, hQroot⟩
    change x ∈ (adjoin (D i) {c}).toSubalgebra at hx'
    rw [adjoin_simple_toSubalgebra_of_isAlgebraic hc.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨q, hq⟩ := hx'
    refine ⟨q %ₘ Q, ?_, ?_⟩
    · rw [← degree_map_eq_of_injective (Subfield.inclusion (hAD i)).injective P]
      exact degree_modByMonic_lt q hQ
    · exact (eval₂_modByMonic_eq_self_of_root hQroot).trans hq
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀, _, hj₀⟩ := hC i₀
  obtain ⟨q₀, hd₀, hq₀⟩ := choosePolynomial j₀
  have hcoeff (n : ℕ) : ((q₀.coeff n : D j₀) : L) ∈ A := by
    rw [← hA, Subfield.mem_iInf]
    intro i
    obtain ⟨j, hji, hj⟩ := hC i
    obtain ⟨q, hd, hq⟩ := choosePolynomial j
    let R₀ : C[X] := q₀.map (Subfield.inclusion hj₀)
    let R : C[X] := q.map (Subfield.inclusion hj)
    have hzero : aeval c (R₀ - R) = 0 := by
      rw [map_sub, aeval_map_inclusion hj₀, aeval_map_inclusion hj, hq₀, hq, sub_self]
    have hlt : (R₀ - R).degree < (minpoly C c).degree := by
      rw [hdeg]
      apply (degree_sub_le _ _).trans_lt
      apply max_lt
      · simpa only [R₀, degree_map_eq_of_injective (Subfield.inclusion hj₀).injective] using hd₀
      · simpa only [R, degree_map_eq_of_injective (Subfield.inclusion hj).injective] using hd
    have heq : R₀ = R := by
      by_contra hne
      exact hlt.not_ge (minpoly.degree_le_of_ne_zero C c (sub_ne_zero.mpr hne) hzero)
    have he := congrArg (fun f : C[X] ↦ (f.coeff n : L)) heq
    simp only [R₀, R, coeff_map] at he
    change (q₀.coeff n : L) = (q.coeff n : L) at he
    rw [he]
    exact hji (q.coeff n).property
  let qA : A[X] := ∑ n ∈ q₀.support, monomial n ⟨(q₀.coeff n : L), hcoeff n⟩
  have hqA : qA.map A.subtype = q₀.map (D j₀).subtype := by
    change (mapRingHom A.subtype) (∑ n ∈ q₀.support,
      monomial n (⟨(q₀.coeff n : L), hcoeff n⟩ : A)) = _
    have hsum := congrArg (mapRingHom (D j₀).subtype) q₀.sum_monomial_eq
    change _ = (mapRingHom (D j₀).subtype) q₀
    rw [← hsum, Polynomial.sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    change (monomial n (_ : A)).map A.subtype =
      (monomial n (q₀.coeff n)).map (D j₀).subtype
    rw [map_monomial, map_monomial]
    rfl
  rw [← adjoin_singleton_toSubfield]
  change x ∈ adjoin A {c}
  have he : aeval c qA = x := by
    rw [aeval_def, show algebraMap A L = A.subtype from rfl, eval₂_eq_eval_map, hqA,
      ← eval₂_eq_eval_map, ← show algebraMap (D j₀) L = (D j₀).subtype from rfl,
      ← aeval_def]
    exact hq₀
  rw [← he]
  exact algebra_adjoin_le_adjoin A {c} (Polynomial.aeval_mem_adjoin_singleton A c)

section FrobeniusImages

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

omit [CharP K p] in
private theorem map_frobenius_adjoin {M N : IntermediateField K L} {b : L}
    (h : N = (adjoin M {b}).restrictScalars K) :
    N.toSubfield.map (frobenius L p) =
      M.toSubfield.map (frobenius L p) ⊔ Subfield.closure {b ^ p} := by
  have hrange : Set.range (algebraMap M L) = (M.toSubfield : Set L) := Subtype.range_coe
  rw [h, restrictScalars_toSubfield, adjoin_toSubfield, RingHom.map_field_closure,
    Set.image_union, hrange, Set.image_singleton, Subfield.closure_union]
  change Subfield.closure (M.toSubfield.map (frobenius L p) : Set L) ⊔
    Subfield.closure {b ^ p} = _
  rw [Subfield.closure_eq]

/-- A downward-directed intersection equal to the Frobenius image of the base
field stays equal to the Frobenius image after forming the composita in a finite extension. -/
theorem iInf_frobeniusSubfield_sup_map_eq [Module.Finite K L] {ι : Type*} [Nonempty ι]
    (E : ι → Subfield K) (hE : (⨅ i, E i) = frobeniusSubfield K p)
    (hdir : Directed (· ≥ ·) E) :
    (⨅ i, frobeniusSubfield L p ⊔ (E i).map (algebraMap K L)) = frobeniusSubfield L p := by
  classical
  let f := algebraMap K L
  let φ := frobenius L p
  let base (i : ι) := (E i).map f
  let powers (M : IntermediateField K L) := M.toSubfield.map φ
  let D (M : IntermediateField K L) (i : ι) := powers M ⊔ base i
  have hDdir (M) : Directed (· ≥ ·) (D M) := by
    intro i j
    obtain ⟨l, hli, hlj⟩ := hdir i j
    exact ⟨l, sup_le_sup_left ((Subfield.gc_map_comap f).monotone_l hli) _, sup_le_sup_left ((Subfield.gc_map_comap f).monotone_l hlj) _⟩
  have hbase (M : IntermediateField K L) (i : ι) : base i ≤ M.toSubfield := by
    rintro _ ⟨y, _, rfl⟩
    exact M.algebraMap_mem y
  have hpow (M : IntermediateField K L) : powers M ≤ M.toSubfield := by
    rintro _ ⟨y, hy, rfl⟩
    exact M.toSubfield.pow_mem hy p
  have hbot : (⨅ i, D ⊥ i) = powers ⊥ := by
    have hpowers : (frobeniusSubfield K p).map f = powers ⊥ := by
      change (frobeniusSubfield K p).map f =
        (⊥ : IntermediateField K L).toSubfield.map φ
      rw [bot_toSubfield]
      ext x
      change (∃ y, y ∈ frobeniusSubfield K p ∧ f y = x) ↔
        (∃ y, y ∈ f.fieldRange ∧ φ y = x)
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨f z, ⟨z, rfl⟩, (map_pow f z p).symm⟩
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z ^ p, ⟨z, rfl⟩, map_pow f z p⟩
    have hbaseInf : (⨅ i, base i) = powers ⊥ := by
      change (⨅ i, (E i).map f) = _
      rw [← Subfield.map_iInf, hE, hpowers]
    have heq (i) : D ⊥ i = base i := sup_eq_right.mpr
      (hbaseInf ▸ iInf_le base i)
    simp only [heq, hbaseInf]
  have hstep {M N : IntermediateField K L} (h : IsSimpleFieldStep p M N)
      (ih : (⨅ i, D M i) = powers M) : (⨅ i, D N i) = powers N := by
    obtain ⟨b, hbN, hbM, hcases⟩ := h
    have heq : powers N = powers M ⊔ Subfield.closure {b ^ p} := map_frobenius_adjoin hbN
    have heqD (i) : D N i = D M i ⊔ Subfield.closure {b ^ p} := by
      change powers N ⊔ base i = (powers M ⊔ base i) ⊔ _
      rw [heq, sup_right_comm]
    simp only [heqD, heq]
    rcases hcases with hsep | hpure
    · let C := M.toSubfield
      have hAC : powers M ≤ C := hpow M
      have hC (i) : D M i ≤ C := sup_le hAC (hbase M i)
      let φM : C →+* powers M := (φ.comp C.subtype).codRestrict _ fun y =>
        ⟨y, y.property, rfl⟩
      have hcomp : (Subfield.inclusion hAC).comp φM = frobenius C p := by
        ext y
        rfl
      have hsep' : IsSeparable C b := hsep
      refine iInf_sup_closure_singleton (D M) ih hAC
        (fun i => ⟨i, le_rfl, hC i⟩) (b ^ p) ((minpoly C b).map φM)
        ((minpoly.monic hsep'.isIntegral).map _) ?_
      rw [Polynomial.map_map, hcomp]
      exact (minpoly.frobenius_of_isSeparable p hsep').symm
    · have hc : b ^ p ∉ powers M := by
        rintro ⟨y, hy, he⟩
        have : y = b := frobenius_inj L p he
        exact hbM (this ▸ hy)
      obtain ⟨i₀, hi₀⟩ : ∃ i, b ^ p ∉ D M i := by
        by_contra! hAll
        exact hc (ih ▸ Subfield.mem_iInf.mpr hAll)
      have hAC : powers M ≤ D M i₀ := le_sup_left
      let a : powers M := ⟨(b ^ p) ^ p, ⟨b ^ p, hpure, rfl⟩⟩
      have hp : p.Prime := Fact.out
      refine iInf_sup_closure_singleton (D M) ih hAC
        (fun i => hDdir M i i₀) (b ^ p) (X ^ p - C a)
        (monic_X_pow_sub_C a hp.ne_zero) ?_
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
      refine minpoly.eq_of_irreducible_of_monic
        (X_pow_sub_C_irreducible_of_prime hp (fun y hy => hi₀ ?_))
        (by simp [aeval_def, show (algebraMap (D M i₀) L) (Subfield.inclusion hAC a) =
          (b ^ p) ^ p from rfl]) (monic_X_pow_sub_C _ hp.ne_zero)
      have h : (y : L) = b ^ p := by
        apply frobenius_inj L p
        exact congrArg Subtype.val hy
      exact h ▸ y.property
  have htower {M : IntermediateField K L}
      (ht : Relation.ReflTransGen (IsSimpleFieldStep p) ⊥ M) :
      (⨅ i, D M i) = powers M := by
    induction ht with
    | refl => exact hbot
    | tail _ h ih => exact hstep h ih
  have htopPow : powers (⊤ : IntermediateField K L) = frobeniusSubfield L p := by
    change (⊤ : IntermediateField K L).toSubfield.map φ = _
    rw [top_toSubfield]
    ext x
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, Subfield.mem_top y, hy⟩⟩
  simpa only [D, htopPow, base] using
    htower (finiteExtension_has_simpleTower K L p (Fact.out : p.Prime))

end FrobeniusImages

/-- The canonical coefficient fraction fields recover the subfield of p-th
powers after forming composita in any finite extension. -/
theorem finiteCoefficientSubring_fractionSubfield_compositum_iInf
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type*}
    (a : ι → k) (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a)
    (r s : ℕ) (F : Type*) [Field F] [Algebra (FractionRing (CoefficientTowerBase k r s)) F]
    [Module.Finite (FractionRing (CoefficientTowerBase k r s)) F] :
    let K := FractionRing (CoefficientTowerBase k r s)
    letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
    (⨅ J : Finset ι, frobeniusSubfield F p ⊔
      (fractionSubfieldOfSubring (finiteCoefficientSubring (p := p) a J r s)).map
        (algebraMap K F)) = frobeniusSubfield F p := by
  let K := FractionRing (CoefficientTowerBase k r s)
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  exact iInf_frobeniusSubfield_sup_map_eq _
    (finiteCoefficientSubring_fractionSubfield_iInf a ha r s)
    (finiteCoefficientSubring_fractionSubfield_directed (p := p) a r s).2

/-- Lemma 5.4. The finite coefficient subrings from a p-basis work
simultaneously for all finite extensions of the fraction field. -/
theorem finiteCoefficientApproximations (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (r s : ℕ) :
    let S := CoefficientTowerBase k r s
    let K := FractionRing S
    ∃ E : Set k,
      let a : E → k := Subtype.val
      let S_J := fun J : Finset E => finiteCoefficientSubring (p := p) a J r s
      let K_J := fun J => fractionSubfieldOfSubring (S_J J)
      IsPBasis p (frobeniusSubfield k p) le_rfl a ∧
      (∀ J, Module.Finite (S_J J) S ∧ Module.Free (S_J J) S ∧
        (frobenius S p).range ≤ S_J J) ∧
      (Set.range K_J).Nonempty ∧ Directed (· ≥ ·) K_J ∧
      ∀ (F : Type*) [Field F] [Algebra K F] [Module.Finite K F],
        letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
        (⨅ J, frobeniusSubfield F p ⊔ (K_J J).map (algebraMap K F)) =
          frobeniusSubfield F p := by
  obtain ⟨E, hE⟩ := exists_pBasis (p := p) (L := k) (H := frobeniusSubfield k p) le_rfl
  have hdir := finiteCoefficientSubring_fractionSubfield_directed (p := p)
    (fun x : E => (x : k)) r s
  refine ⟨E, hE, fun J => ?_, hdir.1, hdir.2, ?_⟩
  · obtain ⟨hfin, hfree⟩ := finiteCoefficientSubring_finite_free _ hE J r s
    exact ⟨hfin, hfree, frobenius_le_finiteCoefficientSubring (fun x : E => (x : k)) J r s⟩
  · intro F _ _ _
    exact finiteCoefficientSubring_fractionSubfield_compositum_iInf _ hE r s F

end

end CommutativeAlgebraNotes
