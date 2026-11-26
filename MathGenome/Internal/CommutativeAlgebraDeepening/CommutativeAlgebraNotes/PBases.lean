import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Order.Zorn

/-! Restricted monomials in extensions of exponent one.  The extension argument
uses maximal independent sets, and the coefficient-field results use the
factorization of monomials along a partition of the variables. -/

namespace CommutativeAlgebraNotes

universe u v w

noncomputable section

open Finsupp Polynomial

variable {L : Type u} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
variable {ι : Type v} {κ : Type w} {H : Subfield L}

private lemma prime_pos : 0 < p := (Fact.out : p.Prime).pos

private def zeroExponents (ι : Type v) (p : ℕ) (hp : 0 < p) :
    RestrictedExponents ι p :=
  ⟨0, fun _ => hp⟩

private def restrictEmbedding (hp : 0 < p) (f : ι ↪ κ) :
    RestrictedExponents ι p ↪ RestrictedExponents κ p where
  toFun e := ⟨e.val.embDomain f, fun j => by
    classical
    by_cases h : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := h
      rw [embDomain_apply_self]
      exact e.property i
    · rw [embDomain_of_notMem_range _ _ _ h]
      exact hp⟩
  inj' e d h := Subtype.ext (embDomain_injective f (congrArg Subtype.val h))

omit [Fact p.Prime] [CharP L p] in
private lemma monomial_restrictEmbedding (hp : 0 < p) (f : ι ↪ κ) (a : κ → L)
    (e : RestrictedExponents ι p) :
    restrictedMonomial a (restrictEmbedding hp f e) = restrictedMonomial (a ∘ f) e :=
  prod_embDomain

private lemma pIndependent_comp (hH : frobeniusSubfield L p ≤ H)
    {a : κ → L} (ha : PIndependent p H hH a) (f : ι ↪ κ) :
    PIndependent p H hH (a ∘ f) := by
  unfold PIndependent at *
  have he : restrictedMonomial (p := p) a ∘ restrictEmbedding prime_pos f =
      restrictedMonomial (a ∘ f) := funext (monomial_restrictEmbedding prime_pos f a)
  rw [← he]
  exact ha.comp _ (restrictEmbedding prime_pos f).injective

private def sumExponents :
    RestrictedExponents (ι ⊕ κ) p ≃ RestrictedExponents ι p × RestrictedExponents κ p where
  toFun e :=
    (⟨(sumFinsuppEquivProdFinsupp e.val).1, fun i => by simpa using e.property (Sum.inl i)⟩,
     ⟨(sumFinsuppEquivProdFinsupp e.val).2, fun i => by simpa using e.property (Sum.inr i)⟩)
  invFun e := ⟨sumFinsuppEquivProdFinsupp.symm (e.1.val, e.2.val), fun i => by
    cases i with
    | inl i => simpa using e.1.property i
    | inr i => simpa using e.2.property i⟩
  left_inv e := Subtype.ext (sumFinsuppEquivProdFinsupp.symm_apply_apply e.val)
  right_inv e := Prod.ext
    (Subtype.ext (congrArg Prod.fst (sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.val, e.2.val))))
    (Subtype.ext (congrArg Prod.snd (sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.val, e.2.val))))

omit [Fact p.Prime] [CharP L p] in
private lemma monomial_sum (a : ι → L) (b : κ → L)
    (e : RestrictedExponents ι p × RestrictedExponents κ p) :
    restrictedMonomial (Sum.elim a b) (sumExponents.symm e) =
      restrictedMonomial a e.1 * restrictedMonomial b e.2 := by
  classical
  let d := (sumExponents (p := p)).symm e
  have he : d.val = e.1.val.embDomain Function.Embedding.inl +
      e.2.val.embDomain Function.Embedding.inr := by
    ext i
    cases i <;> simp [d, sumExponents]
  change d.val.prod _ = _
  rw [he, prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add ..),
    prod_embDomain, prod_embDomain]
  rfl

private lemma powers_mem (hH : frobeniusSubfield L p ≤ H) (x : L) : x ^ p ∈ H :=
  hH ⟨x, rfl⟩

private lemma binomial_aeval (hH : frobeniusSubfield L p ≤ H) (x : L) :
    aeval x (X ^ p - C (⟨x ^ p, powers_mem hH x⟩ : H)) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  exact sub_self _

private lemma integral_of_powers_mem (hH : frobeniusSubfield L p ≤ H) (x : L) :
    IsIntegral H x :=
  ⟨_, monic_X_pow_sub_C _ (Nat.ne_of_gt prime_pos), binomial_aeval hH x⟩

private lemma power_independent (hH : frobeniusSubfield L p ≤ H) {x : L} (hx : x ∉ H) :
    LinearIndependent H (fun i : Fin p => x ^ (i : ℕ)) := by
  let c : H := ⟨x ^ p, powers_mem hH x⟩
  have hirr : Irreducible (X ^ p - C c) := by
    apply X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
    intro y hy
    have he : (y : L) ^ p = x ^ p := congrArg Subtype.val hy
    have he' : (y : L) = x := frobenius_inj L p he
    exact hx (he' ▸ y.property)
  have hmin : minpoly H x = X ^ p - C c :=
    (minpoly.eq_of_irreducible_of_monic hirr (binomial_aeval hH x)
      (monic_X_pow_sub_C _ (Nat.ne_of_gt prime_pos))).symm
  have hd : (minpoly H x).natDegree = p := by rw [hmin, natDegree_X_pow_sub_C]
  rw [← hd]
  exact linearIndependent_pow (K := H) x

private lemma pIndependent_constant [Unique ι] (hH : frobeniusSubfield L p ≤ H)
    {x : L} (hx : x ∉ H) : PIndependent p H hH (fun _ : ι => x) := by
  let f : RestrictedExponents ι p → Fin p := fun e => ⟨e.val default, e.property default⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact Finsupp.ext fun i => Subsingleton.elim i default ▸ congrArg Fin.val h
  unfold PIndependent
  have he : (fun i : Fin p => x ^ (i : ℕ)) ∘ f = restrictedMonomial (fun _ : ι => x) := by
    classical
    let : Fintype ι := Fintype.ofSubsingleton default
    funext e
    simp [f, restrictedMonomial, Finsupp.prod_pow]
  rw [← he]
  exact (power_independent hH hx).comp f hf

/-- An element outside the base field forms a (p)-independent singleton. -/
theorem singleton_pIndependent (hH : frobeniusSubfield L p ≤ H) {x : L} (hx : x ∉ H) :
    PIndependent p H hH (fun _ : Unit => x) :=
  pIndependent_constant hH hx

/-- The exponents in the multiplicative generators reduce modulo `p` over the base. -/
private lemma span_monomials_eq_adjoin (hH : frobeniusSubfield L p ≤ H) (a : ι → L) :
    Submodule.span H (Set.range (restrictedMonomial (p := p) a)) =
      (IntermediateField.adjoin H (Set.range a)).toSubalgebra.toSubmodule := by
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => (integral_of_powers_mem hH x).isAlgebraic), Algebra.adjoin_eq_span]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨e, rfl⟩
    exact Submonoid.mem_closure_range_iff.mpr ⟨e.val, rfl⟩
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨d, rfl⟩ := Submonoid.mem_closure_range_iff.mp hx
    let e : RestrictedExponents ι p := ⟨d.mapRange (· % p) (Nat.zero_mod p),
      fun i => Nat.mod_lt _ prime_pos⟩
    let c : L := d.prod fun i n => (a i ^ p) ^ (n / p)
    have hc : c ∈ H := H.prod_mem fun i _ => H.pow_mem (powers_mem hH (a i)) _
    have he : d.prod (fun i n => a i ^ n) = c * restrictedMonomial a e := by
      change _ = c * (d.mapRange (· % p) (Nat.zero_mod p)).prod _
      rw [prod_mapRange_index (fun _ => pow_zero _), ← prod_mul]
      apply prod_congr
      intro i _
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [he]
    exact Submodule.smul_mem _ (⟨c, hc⟩ : H) (Submodule.subset_span ⟨e, rfl⟩)

private def monomialAdjoinBasis (hH : frobeniusSubfield L p ≤ H) {a : ι → L}
    (ha : PIndependent p H hH a) :
    Module.Basis (RestrictedExponents ι p) H (IntermediateField.adjoin H (Set.range a)) :=
  (Module.Basis.span ha).map (LinearEquiv.ofEq _ _ (span_monomials_eq_adjoin hH a))

private lemma monomialAdjoinBasis_apply (hH : frobeniusSubfield L p ≤ H) {a : ι → L}
    (ha : PIndependent p H hH a) (e : RestrictedExponents ι p) :
    (monomialAdjoinBasis hH ha e : L) = restrictedMonomial a e := by
  change ((Module.Basis.span ha) e : L) = _
  exact Module.Basis.coe_span_apply ha e

/-- Expanding each coefficient in the intermediate-field basis preserves independence. -/
private lemma independent_product_iff {E : IntermediateField H L}
    (b : Module.Basis κ H E) (v : ι → L) :
    LinearIndependent H (fun i : ι × κ => (b i.2 : L) * v i.1) ↔
      LinearIndependent E v := by
  let c := Finsupp.curryLinearEquiv (α := ι) (β := κ) (M := H) H
  let g := Finsupp.linearCombination H b
  have hg : g = b.repr.symm.toLinearMap := by
    ext i
    simp [g]
  have hbg : Function.Bijective g := by
    rw [hg]
    exact b.repr.symm.bijective
  have he : (fun i : ι × κ => (b i.2 : L) * v i.1) = fun i => b i.2 • v i.1 := rfl
  rw [he, linearIndependent_iff_injective_finsuppLinearCombination,
    linearIndependent_iff_injective_finsuppLinearCombination,
    Finsupp.linearCombination_smul]
  let f := Finsupp.mapRange (α := ι) g (map_zero g)
  have hfc : Function.Bijective (f ∘ c) :=
    (Finsupp.mapRange_bijective g (map_zero g) hbg).comp c.bijective
  change Function.Injective ((Finsupp.linearCombination E v) ∘ (f ∘ c)) ↔ _
  exact ⟨fun h => h.of_comp_right hfc.surjective, fun h => h.comp hfc.injective⟩

private lemma pIndependent_sum_iff_product (hH : frobeniusSubfield L p ≤ H)
    (a : ι → L) (b : κ → L) :
    PIndependent p H hH (Sum.elim a b) ↔
      LinearIndependent H (fun e : RestrictedExponents ι p × RestrictedExponents κ p =>
        restrictedMonomial a e.1 * restrictedMonomial b e.2) := by
  unfold PIndependent
  exact (linearIndependent_equiv' sumExponents.symm (funext (monomial_sum a b))).symm

private lemma pIndependent_sum_iff (hH : frobeniusSubfield L p ≤ H)
    (a : ι → L) {b : κ → L} (hb : PIndependent p H hH b) :
    PIndependent p H hH (Sum.elim a b) ↔
      LinearIndependent (IntermediateField.adjoin H (Set.range b))
        (restrictedMonomial (p := p) a) := by
  rw [pIndependent_sum_iff_product]
  have he : (fun e : RestrictedExponents ι p × RestrictedExponents κ p =>
      ((monomialAdjoinBasis hH hb) e.2 : L) * restrictedMonomial a e.1) =
      fun e => restrictedMonomial a e.1 * restrictedMonomial b e.2 := by
    funext e
    rw [monomialAdjoinBasis_apply, mul_comm]
  rw [← he]
  exact independent_product_iff _ _

omit [Fact p.Prime] in
private lemma restrictEmbedding_mem_range (hp : 0 < p) (f : ι ↪ κ)
    (e : RestrictedExponents κ p) (he : (↑e.val.support : Set κ) ⊆ Set.range f) :
    e ∈ Set.range (restrictEmbedding hp f) := by
  let d : RestrictedExponents ι p :=
    ⟨e.val.comapDomain f f.injective.injOn, fun i => e.property (f i)⟩
  exact ⟨d, Subtype.ext (embDomain_comapDomain he)⟩

/-- Any finite family of monomials in the union uses variables from one chain member. -/
private lemma pIndependent_sUnion (hH : frobeniusSubfield L p ≤ H) {c : Set (Set L)}
    (hn : c.Nonempty) (hc : IsChain (· ⊆ ·) c)
    (hi : ∀ s ∈ c, PIndependent p H hH (fun x : s => (x : L))) :
    PIndependent p H hH (fun x : (⋃₀ c : Set L) => (x : L)) := by
  classical
  rw [PIndependent, linearIndependent_iff_finset_linearIndependent]
  intro t
  let s : Finset L := (t.biUnion fun e => e.val.support).map (.subtype _)
  have hs : (s : Set L) ⊆ ⋃₀ c := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact i.property
  obtain ⟨U, hUc, hU⟩ :=
    hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hn s.finite_toSet hs
  let f : U ↪ (⋃₀ c : Set L) := Set.embeddingOfSubset U _ (Set.subset_sUnion_of_mem hUc)
  have he (e : t) : (e.val : RestrictedExponents (↥(⋃₀ c)) p) ∈
      Set.range (restrictEmbedding prime_pos f) := by
    apply restrictEmbedding_mem_range
    intro i hi'
    have his : (i : L) ∈ s :=
      Finset.mem_map.mpr ⟨i, Finset.mem_biUnion.mpr ⟨e.val, e.property, hi'⟩, rfl⟩
    exact ⟨⟨i, hU his⟩, rfl⟩
  let d := fun e : t => (he e).choose
  have hd (e : t) : restrictEmbedding prime_pos f (d e) = e.val := (he e).choose_spec
  have hdi : Function.Injective d := by
    intro e e' h
    apply Subtype.ext
    rw [← hd e, ← hd e', h]
  have hmon : restrictedMonomial (p := p) (fun x : U => (x : L)) ∘ d =
      restrictedMonomial (fun x : (⋃₀ c : Set L) => (x : L)) ∘ Subtype.val := by
    funext e
    exact (monomial_restrictEmbedding prime_pos f _ (d e)).symm.trans
      (congrArg (restrictedMonomial (fun x : (⋃₀ c : Set L) => (x : L))) (hd e))
  rw [← hmon]
  exact (hi U hUc).comp d hdi

private lemma pIndependent_injective (hH : frobeniusSubfield L p ≤ H)
    {a : ι → L} (ha : PIndependent p H hH a) : Function.Injective a := by
  classical
  let e (i : ι) : RestrictedExponents ι p := ⟨single i 1, fun j => by
    by_cases h : i = j
    · subst j
      simpa using (Fact.out : p.Prime).one_lt
    · simpa [single_eq_of_ne (Ne.symm h)] using (prime_pos (p := p))⟩
  have hm (i : ι) : restrictedMonomial a (e i) = a i := by simp [restrictedMonomial, e]
  intro i j hij
  have h : e i = e j := ha.injective ((hm i).trans (hij.trans (hm j).symm))
  by_contra hne
  have he := congrArg (fun e : RestrictedExponents ι p => e.val i) h
  simp [e, single_eq_of_ne hne] at he

private lemma pIndependent_empty (hH : frobeniusSubfield L p ≤ H) :
    PIndependent p H hH (fun x : Empty => nomatch x) := by
  let e : RestrictedExponents Empty p := zeroExponents Empty p prime_pos
  have : Unique (RestrictedExponents Empty p) :=
    ⟨⟨e⟩, fun _ => Subtype.ext (Finsupp.ext fun x => nomatch x)⟩
  unfold PIndependent
  apply linearIndependent_unique_iff.mpr
  have he : (default : RestrictedExponents Empty p) = e :=
    Subtype.ext (Finsupp.ext fun x => nomatch x)
  rw [he]
  simp [restrictedMonomial, e, zeroExponents]

/-- Every (p)-independent family embeds, with its given values, into a (p)-basis. -/
theorem extend_pIndependent (hH : frobeniusSubfield L p ≤ H)
    (a : ι → L) (ha : PIndependent p H hH a) :
    ∃ (s : Set L) (e : ι ↪ s), (∀ i, (e i : L) = a i) ∧
      IsPBasis p H hH (fun x : s => (x : L)) := by
  classical
  let S : Set (Set L) := {s | PIndependent p H hH (fun x : s => (x : L))}
  let r := Equiv.ofInjective a (pIndependent_injective hH ha)
  have hr : Set.range a ∈ S := by
    change PIndependent p H hH (fun x : Set.range a => (x : L))
    have he : a ∘ r.symm = (fun x : Set.range a => (x : L)) := by
      funext x
      exact congrArg Subtype.val (r.apply_symm_apply x)
    rw [← he]
    exact pIndependent_comp hH ha r.symm.toEmbedding
  obtain ⟨s, hs, hm⟩ := zorn_subset_nonempty S (fun c hc hchain hn =>
    ⟨⋃₀ c, pIndependent_sUnion hH hn hchain (fun t ht => hc ht),
      fun _ ht => Set.subset_sUnion_of_mem ht⟩) (Set.range a) hr
  let b : s → L := Subtype.val
  have hb : PIndependent p H hH b := hm.1
  let E := IntermediateField.adjoin H (Set.range b)
  refine ⟨s, r.toEmbedding.trans (Set.embeddingOfSubset _ _ hs), fun _ => rfl, hb, ?_⟩
  rw [span_monomials_eq_adjoin hH b]
  apply top_unique
  intro x _
  change x ∈ E
  by_contra hx
  have hxs : x ∉ s := fun h => IntermediateField.subset_adjoin H _ ⟨⟨x, h⟩, rfl⟩ |> hx
  have hE : frobeniusSubfield L p ≤ E.toSubfield :=
    fun y hy => E.algebraMap_mem (⟨y, hH hy⟩ : H)
  let f : (insert x s : Set L) ≃ PUnit.{u + 1} ⊕ s :=
    (Equiv.Set.insert hxs).trans (Equiv.sumComm _ _)
  have hi : PIndependent p H hH (Sum.elim (fun _ : PUnit.{u + 1} => x) b) :=
    (pIndependent_sum_iff hH _ hb).mpr (pIndependent_constant hE hx)
  have he : Sum.elim (fun _ : PUnit.{u + 1} => x) b ∘ f = (fun y : (insert x s : Set L) => (y : L)) := by
    funext y
    obtain ⟨z, rfl⟩ := f.symm.surjective y
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    cases z <;> rfl
  apply hxs
  apply hm.mem_of_prop_insert
  change PIndependent p H hH (fun y : (insert x s : Set L) => (y : L))
  rw [← he]
  exact pIndependent_comp hH hi f.toEmbedding

/-- A field has a (p)-basis over any subfield containing its (p)-th powers. -/
theorem exists_pBasis (hH : frobeniusSubfield L p ≤ H) :
    ∃ s : Set L, IsPBasis p H hH (fun x : s => (x : L)) := by
  obtain ⟨s, _, _, hs⟩ := extend_pIndependent hH _ (pIndependent_empty hH)
  exact ⟨s, hs⟩

/-- The field generated by the (p)-th powers and the basis variables outside (J). -/
def pBasisComplementField (a : ι → L) (J : Finset ι) : Subfield L :=
  (IntermediateField.adjoin (frobeniusSubfield L p)
    (Set.range fun i : {i : ι // i ∉ J} => a i)).toSubfield

theorem frobenius_le_pBasisComplementField (a : ι → L) (J : Finset ι) :
    frobeniusSubfield L p ≤ pBasisComplementField (p := p) a J :=
  fun x hx => (IntermediateField.adjoin (frobeniusSubfield L p)
    (Set.range fun i : {i : ι // i ∉ J} => a i)).algebraMap_mem ⟨x, hx⟩

instance restrictedExponents_finite [Finite ι] : Finite (RestrictedExponents ι p) :=
  Finite.of_injective (fun e : RestrictedExponents ι p => fun i => (⟨e.val i, e.property i⟩ : Fin p))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun i => congrArg Fin.val (congrFun h i)))

/-- The restricted monomials on (J) form a basis over the complementary field. -/
theorem pBasis_over_complement (a : ι → L)
    (ha : IsPBasis p (frobeniusSubfield L p) le_rfl a) (J : Finset ι) :
    IsPBasis p (pBasisComplementField (p := p) a J)
      (frobenius_le_pBasisComplementField a J) (fun i : {i : ι // i ∈ J} => a i) := by
  classical
  let F := frobeniusSubfield L p
  let aJ : {i : ι // i ∈ J} → L := fun i => a i
  let b : {i : ι // i ∉ J} → L := fun i => a i
  let E := IntermediateField.adjoin F (Set.range b)
  let f := Equiv.sumCompl (· ∈ J)
  have hfun : a ∘ f = Sum.elim aJ b := by
    funext i
    cases i <;> rfl
  have hb : PIndependent p F le_rfl b :=
    pIndependent_comp le_rfl ha.1 (.subtype _)
  have hab : PIndependent p F le_rfl (Sum.elim aJ b) := by
    rw [← hfun]
    exact pIndependent_comp le_rfl ha.1 f.toEmbedding
  change LinearIndependent E (restrictedMonomial (p := p) aJ) ∧
    Submodule.span E (Set.range (restrictedMonomial (p := p) aJ)) = ⊤
  refine ⟨(pIndependent_sum_iff le_rfl aJ hb).mp hab, ?_⟩
  have hspan : Submodule.span F (Set.range (restrictedMonomial (p := p) a)) ≤
      (Submodule.span E (Set.range (restrictedMonomial (p := p) aJ))).restrictScalars F := by
    rw [Submodule.span_le]
    rintro x ⟨d, rfl⟩
    obtain ⟨e, he⟩ := restrictEmbedding_mem_range prime_pos f.toEmbedding d (by
      intro i _
      exact f.surjective i)
    obtain ⟨t, rfl⟩ := sumExponents.symm.surjective e
    rw [← he, monomial_restrictEmbedding]
    change restrictedMonomial (a ∘ f) (sumExponents.symm t) ∈ _
    rw [hfun, monomial_sum, mul_comm]
    let B := monomialAdjoinBasis le_rfl hb
    have ht : (B t.2 : L) = restrictedMonomial b t.2 :=
      monomialAdjoinBasis_apply le_rfl hb t.2
    rw [← ht]
    exact Submodule.smul_mem _ (B t.2) (Submodule.subset_span ⟨t.1, rfl⟩)
  rw [ha.2] at hspan
  exact top_unique fun x hx => hspan hx

/-- The intersection of the complementary fields is exactly the Frobenius image. -/
theorem pBasis_complement_intersection (a : ι → L)
    (ha : IsPBasis p (frobeniusSubfield L p) le_rfl a) :
    (⨅ J : Finset ι, pBasisComplementField (p := p) a J) = frobeniusSubfield L p := by
  classical
  let F := frobeniusSubfield L p
  let B := ha.basis
  let z := zeroExponents ι p prime_pos
  apply le_antisymm
  · intro x hx
    have hcoeff (e : RestrictedExponents ι p) (he : e ≠ z) : B.repr x e = 0 := by
      have hn : ∃ i, e.val i ≠ 0 := by
        by_contra! h
        exact he (Subtype.ext (Finsupp.ext h))
      obtain ⟨i, hi⟩ := hn
      let J : Finset ι := {i}
      let b : {j : ι // j ∉ J} → L := fun j => a j
      let f : {j : ι // j ∉ J} ↪ ι := .subtype _
      have hxJ : x ∈ Submodule.span F (Set.range (restrictedMonomial (p := p) b)) := by
        rw [span_monomials_eq_adjoin le_rfl]
        exact Subfield.mem_iInf.mp hx J
      let C := B.coord e
      have hs : Submodule.span F (Set.range (restrictedMonomial (p := p) b)) ≤ LinearMap.ker C := by
        rw [Submodule.span_le]
        rintro y ⟨d, rfl⟩
        have hd : restrictEmbedding prime_pos f d ≠ e := by
          intro h
          apply hi
          rw [← h]
          exact embDomain_of_notMem_range _ _ _ (by
            rintro ⟨j, hj⟩
            change (j : ι) = i at hj
            exact j.property (by simp [J, hj]))
        change ha.basis.repr (restrictedMonomial (a ∘ f) d) e = 0
        rw [← monomial_restrictEmbedding prime_pos f a d, ← ha.basis_apply,
          Module.Basis.repr_self, single_eq_of_ne (Ne.symm hd)]
      exact hs hxJ
    have hrepr : B.repr x = single z (B.repr x z) := by
      apply Finsupp.ext
      intro e
      by_cases he : e = z
      · subst e
        rw [single_eq_same]
      · rw [single_eq_of_ne he, hcoeff e he]
    have hz : B z = 1 := by simp [B, z, zeroExponents, restrictedMonomial]
    have heq : x = (B.repr x z : L) := by
      calc
        x = B.repr.symm (B.repr x) := (B.repr.symm_apply_apply x).symm
        _ = B.repr.symm (single z (B.repr x z)) := congrArg B.repr.symm hrepr
        _ = _ := by
          rw [Module.Basis.repr_symm_single, hz]
          exact mul_one _
    rw [heq]
    exact (B.repr x z).property
  · exact le_iInf (frobenius_le_pBasisComplementField a)

end

end CommutativeAlgebraNotes
