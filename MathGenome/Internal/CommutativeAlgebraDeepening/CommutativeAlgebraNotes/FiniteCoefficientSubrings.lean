import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PBases
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings

namespace CommutativeAlgebraNotes


open scoped BigOperators Classical
open Finsupp

noncomputable section

/-- The map (H[[u]][v] → k[[u]][v]) substituting the p-th powers of both sets of variables. -/
abbrev coefficientTowerEmbedding :=
  @Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.embedding

/-- The subring associated to a finite subset of the indices of the p-basis. -/
abbrev finiteCoefficientSubring :=
  @Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.coefficientSubring

/-- The fraction field of a subring, viewed inside the fraction field of the ambient domain. -/
abbrev fractionSubfieldOfSubring :=
  @Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.fractionSubfield

variable {k : Type*} [Field k] {p r s : ℕ}

private def exponentQuotient {σ : Type*} (p : ℕ) (n : σ →₀ ℕ) : σ →₀ ℕ :=
  n.mapRange (· / p) (Nat.zero_div p)

private def exponentResidue {σ : Type*} (hp : 0 < p) (n : σ →₀ ℕ) :
    RestrictedExponents σ p :=
  ⟨n.mapRange (· % p) (Nat.zero_mod p), fun i => Nat.mod_lt (n i) hp⟩

private def zeroResidue (σ : Type*) (hp : 0 < p) : RestrictedExponents σ p :=
  ⟨0, fun _ => hp⟩

private lemma exponent_split {σ : Type*} (hp : 0 < p) (n : σ →₀ ℕ) :
    p • exponentQuotient p n + (exponentResidue hp n).val = n := by
  ext i
  simpa [exponentQuotient, exponentResidue, nsmul_eq_mul] using Nat.div_add_mod (n i) p

private lemma exponentQuotient_add {σ : Type*} (hp : 0 < p) (n : σ →₀ ℕ)
    (e : RestrictedExponents σ p) :
    exponentQuotient p (p • n + e.val) = n := by
  ext i
  simp [exponentQuotient, nsmul_eq_mul, Nat.mul_add_div hp, Nat.div_eq_of_lt (e.property i)]

private lemma exponentResidue_add {σ : Type*} (hp : 0 < p) (n : σ →₀ ℕ)
    (e : RestrictedExponents σ p) :
    exponentResidue hp (p • n + e.val) = e := by
  apply Subtype.ext
  ext i
  simp [exponentResidue, nsmul_eq_mul, Nat.mod_eq_of_lt (e.property i)]

private lemma exists_not_dvd_sub {σ : Type*} (hp : 0 < p) (n : σ →₀ ℕ)
    {e d : RestrictedExponents σ p} (hne : e ≠ d) (hle : d.val ≤ p • n + e.val) :
    ∃ i, ¬ p ∣ (p • n + e.val - d.val) i := by
  by_contra! h
  let m := p • n + e.val - d.val
  have hm : (exponentResidue hp m).val = 0 := by
    ext i
    exact Nat.dvd_iff_mod_eq_zero.mp (h i)
  have hs : p • exponentQuotient p m + d.val = p • n + e.val := by
    have eq := exponent_split hp m
    rw [hm, add_zero] at eq
    rw [eq, tsub_add_cancel_of_le hle]
  exact hne (by simpa only [exponentResidue_add] using congrArg (exponentResidue hp) hs.symm)

private lemma coeff_expand_mul_polynomial {σ R : Type*} [CommSemiring R]
    (hp : 0 < p) (x : MvPolynomial σ R) (n : σ →₀ ℕ)
    (e d : RestrictedExponents σ p) (a : R) :
    (MvPolynomial.expand p x * MvPolynomial.monomial d.val a).coeff (p • n + e.val) =
      if e = d then x.coeff n * a else 0 := by
  classical
  by_cases h : e = d
  · subst d
    simp [MvPolynomial.coeff_expand_smul p hp.ne']
  · rw [ite_eq_right h, MvPolynomial.coeff_mul_monomial']
    split_ifs with hle
    · obtain ⟨i, hi⟩ := exists_not_dvd_sub hp n h hle
      rw [MvPolynomial.coeff_expand_of_not_dvd _ hi, zero_mul]
    · rfl

private lemma coeff_expand_mul_series {σ R : Type*} [CommRing R]
    (hp : 0 < p) (x : MvPowerSeries σ R) (n : σ →₀ ℕ)
    (e d : RestrictedExponents σ p) (a : R) :
    MvPowerSeries.coeff (p • n + e.val)
      (MvPowerSeries.expand p hp.ne' x * MvPowerSeries.monomial d.val a) =
      if e = d then MvPowerSeries.coeff n x * a else 0 := by
  classical
  by_cases h : e = d
  · subst d
    rw [ite_eq_left rfl, MvPowerSeries.coeff_add_mul_monomial, MvPowerSeries.coeff_expand_smul]
  · rw [ite_eq_right h, MvPowerSeries.coeff_mul_monomial]
    split_ifs with hle
    · obtain ⟨i, hi⟩ := exists_not_dvd_sub hp n h hle
      rw [MvPowerSeries.coeff_expand_of_not_dvd p hp.ne' _ hi, zero_mul]
    · rfl

private abbrev towerCoeff {R : Type*} [CommSemiring R] (x : CoefficientTowerBase R r s)
    (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ) : R :=
  MvPowerSeries.coeff u (x.coeff v)

private theorem tower_ext {R : Type*} [CommSemiring R] {x y : CoefficientTowerBase R r s}
    (h : ∀ v u, towerCoeff x v u = towerCoeff y v u) : x = y :=
  MvPolynomial.ext _ _ fun v => MvPowerSeries.ext (h v)

private abbrev towerMonomial {R : Type*} [CommSemiring R] (v : Fin s →₀ ℕ)
    (u : Fin r →₀ ℕ) (c : R) : CoefficientTowerBase R r s :=
  MvPolynomial.monomial v (MvPowerSeries.monomial u c)

private def expandTower {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (p : ℕ) (hp : p ≠ 0) (r s : ℕ) :
    CoefficientTowerBase R r s →+* CoefficientTowerBase T r s :=
  (MvPolynomial.expand p).toRingHom.comp
    (MvPolynomial.map ((MvPowerSeries.expand p hp).toRingHom.comp (MvPowerSeries.map f)))

private lemma towerCoeff_expand_mul {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (hp : 0 < p) (x : CoefficientTowerBase R r s)
    (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ)
    (ev dv : RestrictedExponents (Fin s) p) (eu du : RestrictedExponents (Fin r) p) (c : T) :
    towerCoeff (expandTower f p hp.ne' r s x * towerMonomial dv.val du.val c)
      (p • v + ev.val) (p • u + eu.val) =
      if ev = dv ∧ eu = du then f (towerCoeff x v u) * c else 0 := by
  classical
  unfold expandTower
  rw [RingHom.comp_apply]
  change MvPowerSeries.coeff _ ((MvPolynomial.expand p _ * _).coeff _) = _
  rw [coeff_expand_mul_polynomial hp]
  by_cases hv : ev = dv
  · simp only [hv, ite_true, MvPolynomial.coeff_map, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, true_and]
    rw [coeff_expand_mul_series hp]
    simp only [MvPowerSeries.coeff_map, towerCoeff]
    split <;> rfl
  · simp [hv]

private lemma towerCoeff_expand {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (hp : 0 < p) (x : CoefficientTowerBase R r s)
    (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ)
    (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p) :
    towerCoeff (expandTower f p hp.ne' r s x) (p • v + ev.val) (p • u + eu.val) =
      if ev = zeroResidue (Fin s) hp ∧ eu = zeroResidue (Fin r) hp then
        f (towerCoeff x v u) else 0 := by
  classical
  have h := towerCoeff_expand_mul f hp x v u ev (zeroResidue _ hp) eu (zeroResidue _ hp) 1
  change towerCoeff (expandTower f p hp.ne' r s x * towerMonomial 0 0 1) _ _ = _ at h
  have hunit : towerMonomial (r := r) (s := s) 0 0 (1 : T) = 1 := by
    change MvPolynomial.monomial 0 (MvPowerSeries.monomial 0 (1 : T)) = 1
    rw [MvPowerSeries.monomial_zero_eq_C_apply, map_one, ← MvPolynomial.one_def]
  rwa [hunit, mul_one, mul_one] at h

/-- Sample the coefficients at a fixed pair of residues and apply a zero-preserving function. -/
private def sampleTower {R T : Type*} [CommSemiring R] [CommSemiring T]
    (hp : 0 < p) (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p)
    (f : R → T) (hf : f 0 = 0) (x : CoefficientTowerBase R r s) :
    CoefficientTowerBase T r s := by
  classical
  refine .ofCoeff <| Finsupp.onFinset (x.support.image (exponentQuotient p))
    (fun v => (fun u => f (towerCoeff x (p • v + ev.val) (p • u + eu.val)) :
      MvPowerSeries (Fin r) T)) ?_
  intro v hv
  apply Finset.mem_image.mpr
  refine ⟨p • v + ev.val, ?_, exponentQuotient_add hp v ev⟩
  rw [MvPolynomial.mem_support_iff]
  contrapose! hv
  apply MvPowerSeries.ext
  intro u
  change f (towerCoeff x _ _) = 0
  simp only [towerCoeff, hv, map_zero, hf]

private lemma towerCoeff_sample {R T : Type*} [CommSemiring R] [CommSemiring T]
    (hp : 0 < p) (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p)
    (f : R → T) (hf : f 0 = 0) (x : CoefficientTowerBase R r s)
    (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ) :
    towerCoeff (sampleTower hp ev eu f hf x) v u =
      f (towerCoeff x (p • v + ev.val) (p • u + eu.val)) := rfl

/-- The coefficient-and-exponent embedding is injective. -/
theorem coefficientTowerEmbedding_injective (H : Subfield k) (p : ℕ) (hp : p ≠ 0)
    (r s : ℕ) : Function.Injective (coefficientTowerEmbedding H p hp r s) := by
  classical
  have hp' := Nat.pos_of_ne_zero hp
  intro x y h
  apply tower_ext
  intro v u
  apply Subtype.val_injective
  let ev := zeroResidue (Fin s) hp'
  let eu := zeroResidue (Fin r) hp'
  have he := congrArg (fun z => towerCoeff z (p • v + ev.val) (p • u + eu.val)) h
  change towerCoeff (expandTower H.subtype p hp r s x) _ _ =
    towerCoeff (expandTower H.subtype p hp r s y) _ _ at he
  simpa only [towerCoeff_expand H.subtype hp' _ v u ev eu, ev, eu, eq_self, and_self,
    ite_true, Subfield.subtype_apply] using he

private theorem tower_ext_residues {R : Type*} [CommSemiring R] (hp : 0 < p)
    {x y : CoefficientTowerBase R r s}
    (h : ∀ v u (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p),
      towerCoeff x (p • v + ev.val) (p • u + eu.val) =
        towerCoeff y (p • v + ev.val) (p • u + eu.val)) : x = y := by
  apply tower_ext
  intro v u
  simpa only [exponent_split] using
    h (exponentQuotient p v) (exponentQuotient p u) (exponentResidue hp v) (exponentResidue hp u)

private theorem mem_coefficientTowerEmbedding_range (H : Subfield k) (hp : 0 < p)
    (x : CoefficientTowerBase k r s) :
    x ∈ (coefficientTowerEmbedding H p hp.ne' r s).range ↔
      ∀ v u (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p),
        if ev = zeroResidue (Fin s) hp ∧ eu = zeroResidue (Fin r) hp then
          towerCoeff x (p • v + ev.val) (p • u + eu.val) ∈ H
        else towerCoeff x (p • v + ev.val) (p • u + eu.val) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ v u ev eu
    change (if _ then towerCoeff (expandTower H.subtype p hp.ne' r s y) _ _ ∈ H
      else towerCoeff (expandTower H.subtype p hp.ne' r s y) _ _ = 0)
    rw [towerCoeff_expand H.subtype hp]
    split_ifs <;> simp
  · intro hx
    let cut (c : k) : H := if h : c ∈ H then ⟨c, h⟩ else 0
    have hcut : cut 0 = 0 := dite_eq_left H.zero_mem
    let ev₀ := zeroResidue (Fin s) hp
    let eu₀ := zeroResidue (Fin r) hp
    let y := sampleTower hp ev₀ eu₀ cut hcut x
    use y
    change expandTower H.subtype p hp.ne' r s y = x
    apply tower_ext_residues hp
    intro v u ev eu
    rw [towerCoeff_expand H.subtype hp]
    have h := hx v u ev eu
    by_cases he : ev = ev₀ ∧ eu = eu₀
    · rcases he with ⟨rfl, rfl⟩
      simp only [ev₀, eu₀, eq_self, and_self, ite_true] at h ⊢
      rw [towerCoeff_sample]
      exact congrArg Subtype.val (dite_eq_left h :
        cut (towerCoeff x (p • v + ev₀.val) (p • u + eu₀.val)) = ⟨_, h⟩)
    · rw [ite_eq_right he] at h ⊢
      exact h.symm

private lemma towerCoeff_sum {R α : Type*} [CommSemiring R] (I : Finset α)
    (x : α → CoefficientTowerBase R r s) (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ) :
    towerCoeff (∑ i ∈ I, x i) v u = ∑ i ∈ I, towerCoeff (x i) v u := by
  simp only [towerCoeff, MvPolynomial.coeff_sum, map_sum]

private abbrev TowerBasisIndices (β : Type*) (p r s : ℕ) :=
  β × RestrictedExponents (Fin r) p × RestrictedExponents (Fin s) p

private theorem exists_coefficientTowerBasis {β : Type*} [Fintype β] (H : Subfield k)
    (hp : 0 < p) (B : Module.Basis β H k) :
    ∃ D : Module.Basis (TowerBasisIndices β p r s)
        (coefficientTowerEmbedding H p hp.ne' r s).range (CoefficientTowerBase k r s),
      ∀ i, D i = towerMonomial i.2.2.val i.2.1.val (B i.1) := by
  let : Fintype (RestrictedExponents (Fin r) p) := Fintype.ofFinite _
  let : Fintype (RestrictedExponents (Fin s) p) := Fintype.ofFinite _
  let E := coefficientTowerEmbedding H p hp.ne' r s
  let T := E.range
  let I := TowerBasisIndices β p r s
  let mon (i : I) := towerMonomial i.2.2.val i.2.1.val (B i.1)
  let G : (I → T) →ₗ[T] CoefficientTowerBase k r s := Fintype.linearCombination T mon
  have hG (z : I → CoefficientTowerBase H r s) (v : Fin s →₀ ℕ) (u : Fin r →₀ ℕ)
      (ev : RestrictedExponents (Fin s) p) (eu : RestrictedExponents (Fin r) p) :
      towerCoeff (G (fun i => E.rangeRestrict (z i))) (p • v + ev.val) (p • u + eu.val) =
        B.equivFun.symm (fun b => towerCoeff (z (b, eu, ev)) v u) := by
    simp only [G, Fintype.linearCombination_apply, towerCoeff_sum]
    calc
      _ = ∑ i : I, if eu = i.2.1 ∧ ev = i.2.2 then
          H.subtype (towerCoeff (z i) v u) * B i.1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        change towerCoeff (expandTower H.subtype p hp.ne' r s (z i) *
          towerMonomial i.2.2.val i.2.1.val (B i.1)) _ _ = _
        simpa only [and_comm] using
          towerCoeff_expand_mul H.subtype hp (z i) v u ev i.2.2 eu i.2.1 (B i.1)
      _ = ∑ b : β, (towerCoeff (z (b, eu, ev)) v u) • B b := by
        simp only [I, Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel,
          Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ, ite_true]
        rfl
      _ = _ := (B.equivFun_symm_apply _).symm
  have hsurj : Function.Surjective (E.rangeRestrict : CoefficientTowerBase H r s → T) :=
    E.rangeRestrict_surjective
  have hinj : Function.Injective G := by
    intro w w' h
    choose z hz using fun i => hsurj (w i)
    choose z' hz' using fun i => hsurj (w' i)
    have hw : (fun i => E.rangeRestrict (z i)) = w := funext hz
    have hw' : (fun i => E.rangeRestrict (z' i)) = w' := funext hz'
    rw [← hw, ← hw'] at h ⊢
    funext i
    congr 1
    apply tower_ext
    intro v u
    have he := congrArg (fun x => towerCoeff x (p • v + i.2.2.val) (p • u + i.2.1.val)) h
    rw [hG, hG] at he
    exact congrFun (B.equivFun.symm.injective he) i.1
  have hspan : Function.Surjective G := by
    intro x
    let z (i : I) := sampleTower hp i.2.2 i.2.1 (fun c => B.equivFun c i.1)
      (by rw [map_zero]; rfl) x
    use fun i => E.rangeRestrict (z i)
    apply tower_ext_residues hp
    intro v u ev eu
    rw [hG]
    change B.equivFun.symm (fun b => towerCoeff (sampleTower hp ev eu
      (fun c => B.equivFun c b) _ x) v u) = _
    simp_rw [towerCoeff_sample]
    exact B.equivFun.symm_apply_apply _
  let Q := LinearEquiv.ofBijective G ⟨hinj, hspan⟩
  refine ⟨Module.Basis.ofEquivFun Q.symm, ?_⟩
  intro i
  rw [Module.Basis.coe_ofEquivFun]
  change G (Pi.single i 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

variable [Fact p.Prime] [CharP k p] {ι : Type*}

private lemma prime_pos : 0 < p := (Fact.out : p.Prime).pos

private lemma finiteCoefficientSubring_eq (a : ι → k) (J : Finset ι) :
    finiteCoefficientSubring (p := p) a J r s =
      (coefficientTowerEmbedding (pBasisComplementField (p := p) a J)
        p prime_pos.ne' r s).range := rfl

/-- The restricted coefficient and variable monomials form a finite basis containing (1). -/
theorem finiteCoefficientSubring_basis (a : ι → k)
    (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a) (J : Finset ι) (r s : ℕ) :
    ∃ B : Module.Basis (TowerBasisIndices (RestrictedExponents (↥J) p) p r s)
        (finiteCoefficientSubring (p := p) a J r s) (CoefficientTowerBase k r s),
      (∀ i, B i = Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.basisMonomial
        (p := p) a J i) ∧ 1 ∈ Set.range B := by
  let H := pBasisComplementField (p := p) a J
  let : Fintype (RestrictedExponents (↥J) p) := Fintype.ofFinite _
  let B := (pBasis_over_complement a ha J).basis
  obtain ⟨D, hD⟩ := exists_coefficientTowerBasis (r := r) (s := s) H (prime_pos (p := p)) B
  have hd (i : TowerBasisIndices (RestrictedExponents (↥J) p) p r s) :
      D i = Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.basisMonomial
        (p := p) a J i := by
    rw [hD]
    dsimp [B, Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.basisMonomial, towerMonomial]
    rw [IsPBasis.basis_apply]
    rfl
  refine ⟨D, hd, ?_⟩
  let i : TowerBasisIndices (RestrictedExponents (↥J) p) p r s :=
    (zeroResidue _ prime_pos, zeroResidue _ prime_pos, zeroResidue _ prime_pos)
  refine ⟨i, (hd i).trans ?_⟩
  change towerMonomial 0 0 (restrictedMonomial (fun j : ↥J => a j)
    (zeroResidue _ prime_pos)) = 1
  have hi : restrictedMonomial (fun j : ↥J => a j) (zeroResidue _ (prime_pos (p := p))) = 1 := by
    simp [restrictedMonomial, zeroResidue]
  rw [hi]
  change MvPolynomial.monomial 0 (MvPowerSeries.monomial 0 (1 : k)) = 1
  rw [MvPowerSeries.monomial_zero_eq_C_apply, map_one, ← MvPolynomial.one_def]

/-- The tower is finite free over the coefficient subring. -/
theorem finiteCoefficientSubring_finite_free (a : ι → k)
    (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a) (J : Finset ι) (r s : ℕ) :
    Module.Finite (finiteCoefficientSubring (p := p) a J r s) (CoefficientTowerBase k r s) ∧
      Module.Free (finiteCoefficientSubring (p := p) a J r s) (CoefficientTowerBase k r s) := by
  obtain ⟨B, _, _⟩ := finiteCoefficientSubring_basis a ha J r s
  exact ⟨Module.Finite.of_basis B, Module.Free.of_basis B⟩

private theorem expandTower_frobenius (x : CoefficientTowerBase k r s) :
    expandTower (frobenius k p) p (prime_pos (p := p)).ne' r s x = x ^ p := by
  let hp := (prime_pos (p := p)).ne'
  let : CharP (MvPowerSeries (Fin r) k) p :=
    charP_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective p
  let f : MvPowerSeries (Fin r) k →+* MvPowerSeries (Fin r) k :=
    (MvPowerSeries.expand p hp).toRingHom.comp (MvPowerSeries.map (frobenius k p))
  have hf : f = frobenius (MvPowerSeries (Fin r) k) p := by
    ext1 y
    change MvPowerSeries.expand p hp (MvPowerSeries.map (frobenius k p) y) = y ^ p
    rw [← MvPowerSeries.map_expand, MvPowerSeries.map_frobenius_expand]
  change MvPolynomial.expand p (MvPolynomial.map f x) = _
  rw [← MvPolynomial.map_expand, hf, MvPolynomial.map_frobenius_expand]

private theorem frobenius_range_eq_embedding :
    (frobenius (CoefficientTowerBase k r s) p).range =
      (coefficientTowerEmbedding (frobeniusSubfield k p) p
        (prime_pos (p := p)).ne' r s).range := by
  let hp := prime_pos (p := p)
  apply SetLike.ext
  intro x
  rw [mem_coefficientTowerEmbedding_range _ hp]
  constructor
  · rintro ⟨y, rfl⟩
    intro v u ev eu
    change (if _ then towerCoeff (y ^ p) _ _ ∈ frobeniusSubfield k p
      else towerCoeff (y ^ p) _ _ = 0)
    rw [← expandTower_frobenius, towerCoeff_expand (frobenius k p) hp]
    split_ifs
    · exact ⟨towerCoeff y v u, rfl⟩
    · rfl
  · intro hx
    let root (c : k) : k :=
      if h : c ∈ frobeniusSubfield k p then Classical.choose (mem_frobeniusSubfield.mp h) else 0
    have hroot (c : k) (hc : c ∈ frobeniusSubfield k p) : root c ^ p = c := by
      simp only [root, dite_eq_left hc]
      exact Classical.choose_spec (mem_frobeniusSubfield.mp hc)
    have hroot₀ : root 0 = 0 := by simpa [hp.ne'] using hroot 0 (zero_mem _)
    let ev₀ := zeroResidue (Fin s) hp
    let eu₀ := zeroResidue (Fin r) hp
    let y := sampleTower hp ev₀ eu₀ root hroot₀ x
    use y
    change y ^ p = x
    rw [← expandTower_frobenius]
    apply tower_ext_residues hp
    intro v u ev eu
    rw [towerCoeff_expand (frobenius k p) hp]
    have h := hx v u ev eu
    by_cases he : ev = ev₀ ∧ eu = eu₀
    · rcases he with ⟨rfl, rfl⟩
      simp only [ev₀, eu₀, eq_self, and_self, ite_true] at h ⊢
      rw [towerCoeff_sample]
      exact hroot _ h
    · rw [ite_eq_right he] at h ⊢
      exact h.symm

omit [Fact p.Prime] [CharP k p] in
private theorem coefficientTowerEmbedding_range_mono (hp : 0 < p) {H H' : Subfield k}
    (h : H ≤ H') : (coefficientTowerEmbedding H p hp.ne' r s).range ≤
      (coefficientTowerEmbedding H' p hp.ne' r s).range := by
  intro x hx
  rw [mem_coefficientTowerEmbedding_range _ hp] at hx ⊢
  intro v u ev eu
  specialize hx v u ev eu
  split_ifs at hx ⊢ <;> solve | exact h hx | exact hx

/-- The p-th power of every element of the tower lies in every coefficient subring. -/
theorem frobenius_le_finiteCoefficientSubring (a : ι → k) (J : Finset ι) (r s : ℕ) :
    (frobenius (CoefficientTowerBase k r s) p).range ≤ finiteCoefficientSubring (p := p) a J r s := by
  rw [frobenius_range_eq_embedding, finiteCoefficientSubring_eq]
  exact coefficientTowerEmbedding_range_mono (prime_pos (p := p))
    (frobenius_le_pBasisComplementField a J)

/-- The intersection of all coefficient subrings is the Frobenius image. -/
theorem finiteCoefficientSubring_iInf (a : ι → k)
    (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a) (r s : ℕ) :
    (⨅ J : Finset ι, finiteCoefficientSubring (p := p) a J r s) =
      (frobenius (CoefficientTowerBase k r s) p).range := by
  refine le_antisymm ?_ (le_iInf fun J => frobenius_le_finiteCoefficientSubring a J r s)
  intro x hx
  let hp := prime_pos (p := p)
  rw [frobenius_range_eq_embedding, mem_coefficientTowerEmbedding_range _ hp]
  simp only [Subring.mem_iInf, finiteCoefficientSubring_eq,
    mem_coefficientTowerEmbedding_range _ hp] at hx
  intro v u ev eu
  split_ifs with he
  · have h : towerCoeff x (p • v + ev.val) (p • u + eu.val) ∈
        ⨅ J : Finset ι, pBasisComplementField (p := p) a J :=
      Subfield.mem_iInf.mpr fun J => by simpa only [he, and_self, ite_true] using hx J v u ev eu
    rwa [pBasis_complement_intersection a ha] at h
  · simpa only [he, ite_false] using hx ∅ v u ev eu

/-- Enlarging the finite set of excluded p-basis indices shrinks the coefficient subring. -/
theorem finiteCoefficientSubring_antitone (a : ι → k) (r s : ℕ) :
    Antitone (fun J => finiteCoefficientSubring (p := p) a J r s) := by
  intro J J' h
  change finiteCoefficientSubring (p := p) a J' r s ≤ finiteCoefficientSubring (p := p) a J r s
  rw [finiteCoefficientSubring_eq, finiteCoefficientSubring_eq]
  apply coefficientTowerEmbedding_range_mono (prime_pos (p := p))
  change (IntermediateField.adjoin (frobeniusSubfield k p) _).toSubfield ≤
    (IntermediateField.adjoin (frobeniusSubfield k p) _).toSubfield
  apply IntermediateField.adjoin.mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i, fun hi => i.property (h hi)⟩, rfl⟩

section FractionSubfields

variable {S : Type*} [CommRing S] [IsDomain S]

/-- The embedded fraction field is the subfield generated by the image of the subring. -/
theorem fractionSubfieldOfSubring_eq_closure (T : Subring S) :
    fractionSubfieldOfSubring T =
      Subfield.closure ((algebraMap S (FractionRing S)) '' (T : Set S)) := by
  unfold fractionSubfieldOfSubring
    Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings.fractionSubfield
  rw [IsFractionRing.lift_fieldRange]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The image in the ambient fraction field of an element of the subring. -/
theorem algebraMap_mem_fractionSubfieldOfSubring {T : Subring S} {x : S} (hx : x ∈ T) :
    algebraMap S (FractionRing S) x ∈ fractionSubfieldOfSubring T := by
  rw [fractionSubfieldOfSubring_eq_closure]
  exact Subfield.subset_closure ⟨x, hx, rfl⟩

/-- The fraction subfield construction preserves inclusions. -/
theorem fractionSubfieldOfSubring_mono :
    Monotone (fractionSubfieldOfSubring (S := S)) := by
  intro T U h
  rw [fractionSubfieldOfSubring_eq_closure, fractionSubfieldOfSubring_eq_closure]
  exact Subfield.closure_mono (Set.image_mono h)

private theorem exists_div_of_mem_fractionSubfieldOfSubring {T : Subring S}
    {x : FractionRing S} (hx : x ∈ fractionSubfieldOfSubring T) :
    ∃ a b : T, b ≠ 0 ∧
      algebraMap S (FractionRing S) (a : S) / algebraMap S (FractionRing S) (b : S) = x := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective T z
  refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← hz, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  rfl

private theorem fractionSubfieldOfSubring_comap_of_basis {β : Type*} {T : Subring S}
    (B : Module.Basis β T S) (hB : 1 ∈ Set.range B) :
    (fractionSubfieldOfSubring T).toSubring.comap (algebraMap S (FractionRing S)) = T := by
  apply SetLike.ext
  intro x
  change algebraMap S (FractionRing S) x ∈ fractionSubfieldOfSubring T ↔ x ∈ T
  refine ⟨fun hx => ?_, algebraMap_mem_fractionSubfieldOfSubring⟩
  obtain ⟨a, b, hb, hab⟩ := exists_div_of_mem_fractionSubfieldOfSubring hx
  have hb' : (b : S) ≠ 0 := fun h => hb (Subtype.ext h)
  have hmap := IsFractionRing.injective S (FractionRing S)
  have hprod : (b : S) * x = a := by
    apply hmap
    rw [map_mul, mul_comm]
    exact ((div_eq_iff ((map_eq_zero_iff _ hmap).not.mpr hb')).mp hab).symm
  obtain ⟨i, hi⟩ := hB
  have hmul : b • x = a • B i := by
    change (b : S) * x = (a : S) * B i
    rwa [hi, mul_one]
  have hrepr := congrArg (fun y => B.repr y i) hmul
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at hrepr
  have hx' : x = (B.repr x i : S) := by
    apply mul_left_cancel₀ hb'
    exact hprod.trans (congrArg Subtype.val hrepr).symm
  rw [hx']
  exact (B.repr x i).property

end FractionSubfields

/-- The elements of the tower lying in the smaller fraction field form exactly (S_J). -/
theorem finiteCoefficientSubring_fractionSubfield_comap (a : ι → k)
    (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a) (J : Finset ι) (r s : ℕ) :
    (fractionSubfieldOfSubring (finiteCoefficientSubring (p := p) a J r s)).toSubring.comap
      (algebraMap (CoefficientTowerBase k r s) (FractionRing (CoefficientTowerBase k r s))) =
        finiteCoefficientSubring (p := p) a J r s := by
  obtain ⟨B, _, hB⟩ := finiteCoefficientSubring_basis a ha J r s
  exact fractionSubfieldOfSubring_comap_of_basis B hB

/-- The intersection of the embedded fraction fields consists of the p-th powers. -/
theorem finiteCoefficientSubring_fractionSubfield_iInf (a : ι → k)
    (ha : IsPBasis p (frobeniusSubfield k p) le_rfl a) (r s : ℕ) :
    (⨅ J : Finset ι, fractionSubfieldOfSubring (finiteCoefficientSubring (p := p) a J r s)) =
      frobeniusSubfield (FractionRing (CoefficientTowerBase k r s)) p := by
  let S := CoefficientTowerBase k r s
  let K := FractionRing S
  let f := algebraMap S K
  let T := fun J => finiteCoefficientSubring (p := p) a J r s
  let E := fun J => fractionSubfieldOfSubring (T J)
  change (⨅ J, E J) = frobeniusSubfield K p
  apply le_antisymm
  · intro x hx
    obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective S x
    have hc' : f c ≠ 0 := (map_eq_zero_iff f (IsFractionRing.injective S K)).not.mpr
      (nonZeroDivisors.ne_zero hc)
    let n := b * c ^ (p - 1)
    have hn : f n = x * f (c ^ p) := by
      calc
        f n = f b * (f c) ^ (p - 1) := by rw [map_mul, map_pow]
        _ = (x * f c) * (f c) ^ (p - 1) := by
          rw [(div_eq_iff hc').mp hbc]
        _ = x * f (c ^ p) := by
          rw [mul_assoc, mul_pow_sub_one (prime_pos (p := p)).ne', map_pow]
    have hnall : n ∈ ⨅ J, T J := by
      apply Subring.mem_iInf.mpr
      intro J
      have hcp : c ^ p ∈ T J :=
        frobenius_le_finiteCoefficientSubring a J r s ⟨c, rfl⟩
      have hmem : f n ∈ E J := hn ▸
        (E J).mul_mem (Subfield.mem_iInf.mp hx J) (algebraMap_mem_fractionSubfieldOfSubring hcp)
      have hcomap : n ∈ (E J).toSubring.comap f := hmem
      rwa [finiteCoefficientSubring_fractionSubfield_comap a ha J r s] at hcomap
    change n ∈ ⨅ J, finiteCoefficientSubring (p := p) a J r s at hnall
    rw [finiteCoefficientSubring_iInf a ha] at hnall
    obtain ⟨d, hd⟩ := hnall
    refine mem_frobeniusSubfield.mpr ⟨f d / f c, ?_⟩
    rw [div_pow, ← map_pow, ← map_pow, show d ^ p = n from hd, hn]
    exact mul_div_cancel_right₀ _ (by rw [map_pow]; exact pow_ne_zero _ hc')
  · intro x hx
    obtain ⟨y, rfl⟩ := mem_frobeniusSubfield.mp hx
    obtain ⟨b, c, _, rfl⟩ := IsFractionRing.div_surjective S y
    apply Subfield.mem_iInf.mpr
    intro J
    rw [div_pow, ← map_pow, ← map_pow]
    exact (E J).div_mem
      (algebraMap_mem_fractionSubfieldOfSubring
        (frobenius_le_finiteCoefficientSubring a J r s ⟨b, rfl⟩))
      (algebraMap_mem_fractionSubfieldOfSubring
        (frobenius_le_finiteCoefficientSubring a J r s ⟨c, rfl⟩))

/-- The fraction subfields form a nonempty family directed downwards by inclusion. -/
theorem finiteCoefficientSubring_fractionSubfield_directed (a : ι → k) (r s : ℕ) :
    (Set.range (fun J => fractionSubfieldOfSubring (finiteCoefficientSubring (p := p) a J r s))).Nonempty ∧
      Directed (· ≥ ·) (fun J => fractionSubfieldOfSubring (finiteCoefficientSubring (p := p) a J r s)) := by
  refine ⟨Set.range_nonempty _, fun J J' => ⟨J ∪ J', ?_, ?_⟩⟩
  · exact fractionSubfieldOfSubring_mono
      (finiteCoefficientSubring_antitone a r s Finset.subset_union_left)
  · exact fractionSubfieldOfSubring_mono
      (finiteCoefficientSubring_antitone a r s Finset.subset_union_right)

end

end CommutativeAlgebraNotes
