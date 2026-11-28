import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedCenter
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Polynomiality and the ordered free basis over the p-center. -/

namespace LieNotes.SuperRestricted.RestrictedPolynomialBasis

open _root_.Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis
open _root_.Shared.Lie (U inclusion word filtration)
open _root_.Shared.Lie.PBW (OrderedWord orderedMonomial boundedSpan)
open RestrictedCenter ReducedEnveloping RestrictedLie
open scoped BigOperators

universe u v

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
  {n p : ℕ}

noncomputable abbrev restrictedMonomial := @restrictedMonomialValue

private def exponentWord (a : Fin n → ℕ) : OrderedWord (Fin n) :=
  ⟨(List.finRange n).flatMap (fun i => List.replicate (a i) i), by
    refine List.pairwise_flatMap.mpr ⟨by simp, ?_⟩
    exact (List.pairwise_le_finRange n).imp (by
      intro i j hij x hx y hy
      have hxi := (List.mem_replicate.mp hx).2
      have hyj := (List.mem_replicate.mp hy).2
      rwa [hxi, hyj])⟩

private theorem count_replicate_flatMap (l : List (Fin n)) (a : Fin n → ℕ) (i : Fin n) :
    (l.flatMap (fun j => List.replicate (a j) j)).count i = l.count i * a i := by
  induction l with
  | nil => simp
  | cons j l ih =>
    by_cases h : j = i
    · subst j
      simp [ih, Nat.add_mul, Nat.add_comm]
    · simp [ih, List.count_replicate, h]

private theorem exponentWord_count (a : Fin n → ℕ) (i : Fin n) :
    (exponentWord a).val.count i = a i := by
  rw [exponentWord, count_replicate_flatMap, List.count_eq_one_of_mem
    (List.nodup_finRange n) (List.mem_finRange i), one_mul]

private def exponentWordEquiv (n : ℕ) : (Fin n → ℕ) ≃ OrderedWord (Fin n) where
  toFun := exponentWord
  invFun l i := l.val.count i
  left_inv a := funext (exponentWord_count a)
  right_inv l := by
    apply Subtype.ext
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (exponentWord _).property l.property
    exact List.perm_iff_count.mpr (exponentWord_count _)

private noncomputable def splitExponents (n p : ℕ) [NeZero p] :
    ((Fin n → Fin p) × (Fin n →₀ ℕ)) ≃ (Fin n → ℕ) where
  toFun t i := p * t.2 i + (t.1 i).val
  invFun a := (fun i => ⟨a i % p, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩,
    Finsupp.equivFunOnFinite.symm fun i => a i / p)
  left_inv := by
    rintro ⟨r, d⟩
    apply Prod.ext
    · funext i
      apply Fin.ext
      change (p * d i + (r i).val) % p = (r i).val
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (r i).isLt]
    · ext i
      change (p * d i + (r i).val) / p = d i
      rw [Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne p)), Nat.div_eq_of_lt (r i).isLt,
        add_zero]
  right_inv a := by
    funext i
    change p * (a i / p) + a i % p = a i
    rw [Nat.add_comm, Nat.mod_add_div]

private theorem orderedMonomial_exponentWord (b : Module.Basis (Fin n) k G)
    (a : Fin n → ℕ) :
    orderedMonomial b (exponentWord a) =
      ((List.finRange n).map fun i => inclusion k G (b i) ^ a i).prod := by
  change word k G (((List.finRange n).flatMap (fun i => List.replicate (a i) i)).map b) = _
  simp only [word, List.map_map, Function.comp_def]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons, ih]

private theorem exponentWord_length (a : Fin n → ℕ) :
    (exponentWord a).val.length = ((List.finRange n).map a).sum := by
  simp [exponentWord, List.length_flatMap]

private abbrev FiltrationCertificate (k : Type u) [Field k] (G : Type v)
    [LieRing G] [LieAlgebra k G] := _root_.Specs.Shared.Lie.filtrationType k G

private def SameLeading (m : ℤ) (a b : U k G) : Prop :=
  b ∈ filtration k G m ∧ a - b ∈ filtration k G (m - 1)

private theorem SameLeading.mul (hf : FiltrationCertificate k G)
    {i j : ℤ} {a b c d : U k G} (h : SameLeading i a b) (h' : SameLeading j c d) :
    SameLeading (i + j) (a * c) (b * d) := by
  have hc : c ∈ filtration k G j := by
    have hcd := (filtration k G j).add_mem (hf.1 (by omega : j - 1 ≤ j) h'.2) h'.1
    simpa only [sub_add_cancel] using hcd
  refine ⟨hf.2.2.2.2.1 i j b d h.1 h'.1, ?_⟩
  have h₁ := hf.2.2.2.2.1 (i - 1) j (a - b) c h.2 hc
  have h₂ := hf.2.2.2.2.1 i (j - 1) b (c - d) h.1 h'.2
  rw [show i - 1 + j = i + j - 1 by omega] at h₁
  rw [show i + (j - 1) = i + j - 1 by omega] at h₂
  simpa only [sub_mul, mul_sub, sub_add_sub_cancel] using
    (filtration k G (i + j - 1)).add_mem h₁ h₂

private theorem SameLeading.pow (hf : FiltrationCertificate k G)
    {i : ℤ} {a b : U k G} (h : SameLeading i a b) (q : ℕ) :
    SameLeading (i * q) (a ^ q) (b ^ q) := by
  induction q with
  | zero => simpa [SameLeading] using hf.2.2.1
  | succ q ih =>
    simpa only [pow_succ, Nat.cast_succ, Int.mul_add, Int.mul_one] using ih.mul hf h

private theorem sameLeading_listProd (hf : FiltrationCertificate k G)
    (l : List (Fin n)) {m : Fin n → ℕ} {a b : Fin n → U k G}
    (h : ∀ i, SameLeading (m i : ℤ) (a i) (b i)) :
    SameLeading ((l.map m).sum : ℕ) (l.map a).prod (l.map b).prod := by
  induction l with
  | nil => simpa [SameLeading] using hf.2.2.1
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, List.sum_cons, Nat.cast_add] using
      (h i).mul hf ih

private theorem listProd_mul_central {a b : Fin n → U k G} (l : List (Fin n))
    (h : ∀ i x, Commute (a i) x) :
    (l.map fun i => a i * b i).prod = (l.map a).prod * (l.map b).prod := by
  have commuteProd : ∀ l' : List (Fin n), ∀ x, Commute (l'.map a).prod x := by
    intro l' x
    apply Commute.list_prod_left
    intro y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    exact h i x
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    calc
      (a i * b i) * ((l.map a).prod * (l.map b).prod) =
          a i * ((b i * (l.map a).prod) * (l.map b).prod) := by simp only [mul_assoc]
      _ = (a i * (l.map a).prod) * (b i * (l.map b).prod) := by
        rw [(commuteProd l (b i)).symm.eq]
        simp only [mul_assoc]

section
variable [CharP k p] [NeZero p]

private theorem mixed_sameLeading (hf : FiltrationCertificate k G)
    (power : RestrictedPower k p G) (b : Module.Basis (Fin n) k G)
    (t : (Fin n → Fin p) × (Fin n →₀ ℕ)) :
    let l := exponentWord (splitExponents n p t)
    SameLeading (l.val.length : ℤ)
      (((List.finRange n).map fun i => pCenterElement power (b i) ^ t.2 i).prod *
        restrictedMonomial b t.1) (orderedMonomial b l) := by
  dsimp
  rw [orderedMonomial_exponentWord, exponentWord_length]
  change SameLeading _ (_ * ((List.finRange n).map fun i => inclusion k G (b i) ^ (t.1 i).val).prod) _
  rw [← listProd_mul_central _ (fun i x =>
    (pCenterElement_commute power (b i) x).pow_left _)]
  apply sameLeading_listProd hf
  intro i
  change SameLeading ((p * t.2 i + (t.1 i).val : ℕ) : ℤ)
    (pCenterElement power (b i) ^ t.2 i * inclusion k G (b i) ^ (t.1 i).val)
    (inclusion k G (b i) ^ (p * t.2 i + (t.1 i).val))
  have hx (x : G) : SameLeading 1 (inclusion k G x) (inclusion k G x) :=
    ⟨hf.2.2.2.1 x, by simp⟩
  have hz : SameLeading (p : ℤ) (pCenterElement power (b i)) (inclusion k G (b i) ^ p) := by
    refine ⟨by simpa using ((hx (b i)).pow hf p).1, ?_⟩
    have hp : Nat.Prime p := (CharP.char_is_prime_of_pos k p).out
    change inclusion k G (b i) ^ p - inclusion k G (power.val (b i)) -
      inclusion k G (b i) ^ p ∈ _
    rw [sub_sub_cancel_left]
    exact hf.1 (by have := hp.two_le; omega)
      ((filtration k G 1).neg_mem (hf.2.2.2.1 _))
  simpa only [Nat.cast_add, Nat.cast_mul, ← pow_mul, ← pow_add, Int.one_mul] using
    (hz.pow hf (t.2 i)).mul hf ((hx (b i)).pow hf (t.1 i).val)

end


private theorem triangularBasis (b : Module.Basis (Fin n) k G)
    (hf : FiltrationCertificate k G) (f : OrderedWord (Fin n) → U k G)
    (h : ∀ l, SameLeading (l.val.length : ℤ) (f l) (orderedMonomial b l)) :
    ∃ C : Module.Basis (OrderedWord (Fin n)) k (U k G), ∀ l, C l = f l := by
  obtain ⟨B, hB, -⟩ := LieAlgebrasAndRepresentations.PBW.orderedBasis_spec k G (Fin n) b
  let T : U k G →ₗ[k] U k G := B.constr k f
  have hT (l) : T (B l) = f l := B.constr_basis k f l
  let D : U k G →ₗ[k] U k G := T - LinearMap.id
  have hD (m : ℤ) (x : U k G) (hx : x ∈ filtration k G m) :
      D x ∈ filtration k G (m - 1) := by
    have hm := LieAlgebrasAndRepresentations.PBW.filteredBasis_spec k G (Fin n) b m
    rw [hm] at hx
    have hle : boundedSpan b m ≤ (filtration k G (m - 1)).comap D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨l, hl, rfl⟩
      change T (orderedMonomial b l) - orderedMonomial b l ∈ filtration k G (m - 1)
      rw [← hB l, hT, hB]
      exact hf.1 (by omega) (h l).2
    exact hle hx
  have hex (x : U k G) : ∃ d : ℕ, x ∈ filtration k G (d : ℤ) := by
    obtain ⟨m, hm⟩ := hf.2.2.2.2.2 x
    exact ⟨m.toNat, hf.1 (by omega) hm⟩
  have hinj : Function.Injective T := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    change T x = 0 at hx
    obtain ⟨d, hd⟩ := hex x
    have hdown (m : ℤ) (hm : x ∈ filtration k G m) : x ∈ filtration k G (m - 1) := by
      have hd' := hD m x hm
      change T x - x ∈ _ at hd'
      rw [hx, zero_sub] at hd'
      simpa using (filtration k G (m - 1)).neg_mem hd'
    induction d with
    | zero =>
      have hx' := hdown 0 hd
      rw [hf.2.1 _ (by omega)] at hx'
      exact (Submodule.mem_bot k).mp hx'
    | succ d ih =>
      apply ih
      have hx' := hdown (d + 1) (by simpa using hd)
      simpa using hx'
  have hsurj : Function.Surjective T := by
    intro x
    have hmem (d : ℕ) (y : U k G) (hy : y ∈ filtration k G (d : ℤ)) : y ∈ T.range := by
      induction d generalizing y with
      | zero =>
        have hy' := hD 0 y hy
        rw [hf.2.1 _ (by omega)] at hy'
        have he : T y - y = 0 := (Submodule.mem_bot k).mp hy'
        exact ⟨y, sub_eq_zero.mp he⟩
      | succ d ih =>
        have hy' := hD (d + 1) y (by simpa using hy)
        have hr : D y ∈ T.range := ih _ (by simpa using hy')
        have hTy : T y ∈ T.range := ⟨y, rfl⟩
        simpa [D] using T.range.sub_mem hTy hr
    obtain ⟨d, hd⟩ := hex x
    exact hmem d x hd
  refine ⟨B.map (LinearEquiv.ofBijective T ⟨hinj, hsurj⟩), ?_⟩
  intro l
  exact hT l

section

variable [CharP k p] [NeZero p]

private theorem mixedBasis (power : RestrictedPower k p G) (b : Module.Basis (Fin n) k G) :
    ∃ C : Module.Basis ((Fin n → Fin p) × (Fin n →₀ ℕ)) k (U k G),
      ∀ t, C t = ((List.finRange n).map fun i => pCenterElement power (b i) ^ t.2 i).prod *
        restrictedMonomial b t.1 := by
  obtain ⟨hf, -⟩ := LieAlgebrasAndRepresentations.PBW.graded_spec k G (Fin n) b
  let e := (splitExponents n p).trans (exponentWordEquiv n)
  let f : ((Fin n → Fin p) × (Fin n →₀ ℕ)) → U k G := fun t =>
    ((List.finRange n).map fun i => pCenterElement power (b i) ^ t.2 i).prod *
      restrictedMonomial b t.1
  obtain ⟨C, hC⟩ := triangularBasis b hf (fun l => f (e.symm l)) (by
    intro l
    have hl := mixed_sameLeading hf power b (e.symm l)
    change SameLeading ((e (e.symm l)).val.length : ℤ) (f (e.symm l))
      (orderedMonomial b (e (e.symm l))) at hl
    simpa only [e.apply_symm_apply] using hl)
  refine ⟨C.reindex e.symm, ?_⟩
  intro t
  simpa [Module.Basis.reindex_apply] using hC (e t)

end


/-- The actual p-center is polynomial on the basis corrections, and the bounded
ordered monomials form a basis over it via multiplication. -/
theorem polynomialBasis : polynomialBasisType.{u, v} := by
  classical
  intro k _ G _ _ n p _ _ power b
  let P := MvPolynomial (Fin n) k
  let Z := pCenter power
  let R := Fin n → Fin p
  let : CommSemiring Z :=
    { (inferInstance : Semiring Z) with
      mul_comm := by
        intro a b
        apply Subtype.ext
        exact Subalgebra.mem_center_iff.mp (pCenter_le_center power b.property) a.val }
  let z (i : Fin n) : Z := ⟨pCenterElement power (b i),
    Algebra.subset_adjoin (Set.mem_range_self (b i))⟩
  let ev : P →ₐ[k] Z := MvPolynomial.aeval z
  let ψ : P →ₐ[k] U k G := Z.val.comp ev
  let : Module P (U k G) := ψ.toRingHom.toModule
  let : IsScalarTower k P (U k G) := ⟨by
    intro c q x
    change ψ (c • q) * x = c • (ψ q * x)
    rw [map_smul, Algebra.smul_mul_assoc]⟩
  have hmonomial (d : Fin n →₀ ℕ) :
      ψ (MvPolynomial.monomial d 1) =
        ((List.finRange n).map fun i => pCenterElement power (b i) ^ d i).prod := by
    change Z.val (MvPolynomial.aeval z (MvPolynomial.monomial d 1)) = _
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    rw [← List.toFinset_finRange n, List.prod_toFinset _ (List.nodup_finRange n),
      map_list_prod, List.map_map]
    simp only [Function.comp_def, map_pow]
    rfl
  obtain ⟨C, hC⟩ := mixedBasis power b
  let L : (R →₀ P) →ₗ[P] U k G := Finsupp.linearCombination P (restrictedMonomial b)
  have hsingle (r : R) (q : P) :
      L (Finsupp.single r q) = ψ q * restrictedMonomial b r := by
    exact Finsupp.linearCombination_single _ _ _
  let D : Module.Basis (Σ _ : R, Fin n →₀ ℕ) k (R →₀ P) :=
    Finsupp.basis fun _ => MvPolynomial.basisMonomials (Fin n) k
  let eIndex := Equiv.sigmaEquivProd R (Fin n →₀ ℕ)
  have heq : L.restrictScalars k = (D.equiv C eIndex).toLinearMap := by
    apply D.ext
    rintro ⟨r, d⟩
    change L (D ⟨r, d⟩) = D.equiv C eIndex (D ⟨r, d⟩)
    rw [D.equiv_apply, hC]
    simp only [D, Finsupp.coe_basis, hsingle]
    change ψ (MvPolynomial.monomial d 1) * restrictedMonomial b r = _
    rw [hmonomial]
    rfl
  have hL : Function.Bijective L := by
    change Function.Bijective (L.restrictScalars k)
    rw [heq]
    exact (D.equiv C eIndex).bijective
  have hev_inj : Function.Injective ev := by
    intro a q he
    let r : R := fun _ => 0
    have h := hL.1 (a₁ := Finsupp.single r a) (a₂ := Finsupp.single r q) (by
      rw [hsingle, hsingle]
      exact congrArg (fun v : Z => Z.val v * restrictedMonomial b r) he)
    simpa only [Finsupp.single_eq_same] using congrArg (fun f : R →₀ P => f r) h
  have hψ_range : ψ.range = Z := by
    have hz : Z.val ∘ z = fun i => pCenterElement power (b i) := rfl
    change (Z.val.comp (MvPolynomial.aeval z)).range = _
    rw [AlgHom.range_comp, MvPolynomial.aeval_range, AlgHom.map_adjoin, ← Set.range_comp, hz]
    exact (pCenter_eq_adjoin_basis power b).symm
  have hev_surj : Function.Surjective ev := by
    intro a
    have ha : (a : U k G) ∈ ψ.range := hψ_range.symm ▸ a.property
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, Subtype.ext hq⟩
  let e : P ≃ₐ[k] Z := AlgEquiv.ofBijective ev ⟨hev_inj, hev_surj⟩
  refine ⟨e, ?_, ?_⟩
  · intro i
    change (ev (MvPolynomial.X i) : U k G) = _
    change (MvPolynomial.aeval z (MvPolynomial.X i) : U k G) = _
    rw [MvPolynomial.aeval_X]
  · let L' : (R →₀ P) ≃ₗ[P] U k G := LinearEquiv.ofBijective L hL
    refine ⟨Module.Basis.ofRepr L'.symm, ?_⟩
    intro r
    change L (Finsupp.single r 1) = _
    rw [hsingle, map_one, one_mul]

/-- Transport the basis along the polynomial presentation to the p-center itself. -/
theorem centerBasis : centerBasisType.{u, v} := by
  intro k _ G _ _ n p _ _ power b
  obtain ⟨e, -, B, hB⟩ := polynomialBasis power b
  let Z := pCenter power
  let : Module (MvPolynomial (Fin n) k) (U k G) :=
    (Z.val.comp e.toAlgHom).toRingHom.toModule
  let : Module Z (U k G) := Z.val.toRingHom.toModule
  have h (q : MvPolynomial (Fin n) k) (x : U k G) :
      e.toRingEquiv q • x = q • x := rfl
  exact ⟨B.mapCoeffs e.toRingEquiv h, fun r => (B.mapCoeffs_apply e.toRingEquiv h r).trans (hB r)⟩

end LieNotes.SuperRestricted.RestrictedPolynomialBasis
