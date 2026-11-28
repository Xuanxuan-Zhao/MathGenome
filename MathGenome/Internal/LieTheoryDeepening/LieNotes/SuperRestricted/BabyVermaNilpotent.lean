import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaNilpotent
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaQuotients
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! The simple modules at the normalized nonzero nilpotent character of restricted `sl₂`. -/

namespace LieNotes.SuperRestricted.BabyVermaNilpotent

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaNilpotent
open private induction_property matrix_basis_powers from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

private theorem primeFieldEmbedding_injective (k : Type u) [Field k] (p : ℕ) [CharP k p] :
    Function.Injective (primeFieldEmbedding k p) :=
  ZMod.castHom_injective k

private theorem exists_primeFieldEmbedding_eq_iff
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (weight : k) :
    (∃ m, primeFieldEmbedding k p m = weight) ↔ weight ^ p - weight = 0 := by
  rw [sub_eq_zero, ← Subfield.mem_bot_iff_pow_eq_self k p,
    ← ZMod.fieldRange_castHom_eq_bot p]
  rfl

private theorem natCast_fin_injective (k : Type u) [Field k] (p : ℕ) [CharP k p] :
    Function.Injective (fun i : Fin p => (i.val : k)) :=
  fun i j hij => Fin.ext (CharP.natCast_injOn_Iio k p i.isLt j.isLt hij)

private theorem two_ne_zero_of_lt_char (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (hp : 2 < p) : (2 : k) ≠ 0 := by
  intro h
  have heq : (2 : ℕ) = 0 :=
    CharP.natCast_injOn_Iio k p hp (lt_trans Nat.zero_lt_two hp) (by simpa using h)
  omega

section DiagonalAction

variable {k A M ι : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] [SMulCommClass A k M]

/-- For an operator diagonal in a basis with distinct eigenvalues, every nonzero eigenvector
lies on one of the basis lines. -/
private theorem eigenvector_eq_smul_basis (b : Module.Basis ι k M) (a : A) (d : ι → k)
    (hd : Function.Injective d) (hb : ∀ i, a • b i = d i • b i)
    {x : M} {weight : k} (hx : x ≠ 0) (hax : a • x = weight • x) :
    ∃ (i : ι) (c : k), c ≠ 0 ∧ weight = d i ∧ x = c • b i := by
  classical
  have eq_coord (i : ι) :
      (b.coord i).comp (Algebra.lsmul k k M a) = d i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : j = i
    · subst j
      simp [hb, Module.Basis.coord_apply, Module.Basis.repr_self]
    · simp [hb, Module.Basis.coord_apply, Module.Basis.repr_self, hij]
  have coord_eigen (i : ι) (hi : b.repr x i ≠ 0) : weight = d i := by
    have h := DFunLike.congr_fun (eq_coord i) x
    change b.coord i (a • x) = d i * b.coord i x at h
    rw [hax, map_smul, smul_eq_mul] at h
    exact mul_right_cancel₀ hi h
  have exists_nonzero : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := exists_nonzero
  refine ⟨i, b.repr x i, hi, coord_eigen i hi, ?_⟩
  apply b.repr.injective
  ext j
  rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self]
  by_cases hji : j = i
  · subst j
    simp
  · have hj : b.repr x j = 0 := by
      by_contra hj
      exact hji (hd ((coord_eigen j hj).symm.trans (coord_eigen i hi)))
    simp [Ne.symm hji, hj]

end DiagonalAction

section Induced

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
  {χ : Model k →ₗ[k] k} {j : BorelAlgebra Q χ →ₐ[k] Ambient P χ}
  {θ : BorelAlgebra Q χ →ₐ[k] k}

omit [NeZero p] in
private theorem weight_injective (hp : 2 < p) (weight : k) :
    Function.Injective (fun i : Fin p => weight - 2 * (i.val : k)) := by
  intro i l hil
  apply natCast_fin_injective k p
  exact mul_left_cancel₀ (two_ne_zero_of_lt_char k p hp) (sub_right_injective hil)

private theorem nilpotent_babyVerma_simple [IsAlgClosed k] (hp : 2 < p)
    (hP : MatrixPower P) (hf : χ (F k) = 1) {weight : k}
    (ha : BasisAndActions j θ weight) : IsSimpleModule (Ambient P χ) (BabyVerma j θ) := by
  obtain ⟨b, hb, hh, _, _, _, _⟩ := ha
  let A := Ambient P χ
  let M := BabyVerma j θ
  let f := generator P χ (F k)
  let h := generator P χ (H k)
  have f_pow : f ^ p = 1 := by
    have heq := BabyVermaInduction.generator_pow P χ (F k)
    have hzero : generator P χ (0 : Model k) = 0 := by simp [generator]
    rw [(matrix_basis_powers hP).2.1, hzero, hf, one_pow, map_one, zero_add] at heq
    exact heq
  let : Nontrivial M := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  let : Module.Finite k M := Module.Finite.of_basis b
  refine (isSimpleModule_iff A M).mpr ⟨?_⟩
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  let Wk := W.restrictScalars k
  have : Nontrivial Wk := Submodule.nontrivial_iff_ne_bot.mpr
    (fun hwk => hW ((Submodule.restrictScalars_eq_bot_iff k A M).mp hwk))
  let : Module.Finite k Wk := Module.Finite.of_injective Wk.subtype Subtype.val_injective
  let hWk : Module.End k Wk :=
    (Algebra.lsmul k k M h).restrict (fun x hx => W.smul_mem h hx)
  obtain ⟨weight', hw⟩ := hWk.exists_eigenvalue
  obtain ⟨x, hx⟩ := hw.exists_hasEigenvector
  have hx₀ : (x : M) ≠ 0 := fun hzero => hx.2 (Subtype.ext hzero)
  have hax : h • (x : M) = weight' • (x : M) :=
    congrArg (fun y : Wk => (y : M)) hx.apply_eq_smul
  obtain ⟨i, c, hc, _, hxi⟩ :=
    eigenvector_eq_smul_basis b h _ (weight_injective hp weight) hh hx₀ hax
  have hbi : b i ∈ Wk := by
    have hcx : c⁻¹ • (x : M) ∈ Wk := Wk.smul_mem c⁻¹ x.property
    rwa [hxi, smul_smul, inv_mul_cancel₀ hc, one_smul] at hcx
  have hhighest : highest j θ ∈ W := by
    have hmem := W.smul_mem (f ^ (p - i.val)) hbi
    rwa [hb, ← mul_smul, ← pow_add, Nat.sub_add_cancel i.isLt.le, f_pow, one_smul] at hmem
  have hall (l : Fin p) : b l ∈ Wk := by
    change b l ∈ W
    rw [hb]
    exact W.smul_mem _ hhighest
  have htop : Wk = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hall)
  exact (Submodule.restrictScalars_eq_top_iff k A M).mp htop

private theorem highest_weights (hp : 2 < p) (m : ZMod p)
    (ha : BasisAndActions j θ (primeFieldEmbedding k p m)) (weight : k) :
    (∃ x : BabyVerma j θ, x ≠ 0 ∧ generator P χ (E k) • x = 0 ∧
      generator P χ (H k) • x = weight • x) ↔
      weight = primeFieldEmbedding k p m ∨
        weight = primeFieldEmbedding k p (labelInvolution m) := by
  obtain ⟨b, hb, hh, he₀, he, _, _⟩ := ha
  let C := primeFieldEmbedding k p
  let e := generator P χ (E k)
  let h := generator P χ (H k)
  have e_zero_iff (i : Fin p) : e • b i = 0 ↔ i.val = 0 ∨ (i.val : k) = C m + 1 := by
    by_cases hi : i.val = 0
    · have hv : b i = highest j θ := by simp [hb, hi]
      simp [hv, he₀, hi, e]
    · let l : Fin p := ⟨i.val - 1, by omega⟩
      have hil : i.val = l.val + 1 := by
        change i.val = i.val - 1 + 1
        omega
      have hcast : (i.val : k) ≠ 0 := by
        intro hz
        apply hi
        exact CharP.natCast_injOn_Iio k p i.isLt (NeZero.pos p) (by simpa using hz)
      change generator P χ (E k) • b i = 0 ↔ _
      rw [he i l hil, smul_eq_zero, or_iff_left (b.ne_zero l), mul_eq_zero,
        or_iff_right hcast, or_iff_right hi]
      change C m - (i.val : k) + 1 = 0 ↔ (i.val : k) = C m + 1
      rw [sub_add_eq_add_sub, sub_eq_zero, eq_comm]
  have partner : C (labelInvolution m) = C m - 2 * (C m + 1) := by
    rw [labelInvolution, map_sub, map_neg, map_ofNat]
    ring
  constructor
  · rintro ⟨x, hx, hex, hhx⟩
    obtain ⟨i, c, hc, hweight, rfl⟩ :=
      eigenvector_eq_smul_basis b h _ (weight_injective hp (C m)) hh hx hhx
    change e • (c • b i) = 0 at hex
    rw [smul_comm e, smul_eq_zero, or_iff_right hc, e_zero_iff] at hex
    rcases hex with hi | hi
    · left
      simpa [hi] using hweight
    · right
      rw [partner, hweight, hi]
  · rintro (rfl | rfl)
    · let i : Fin p := 0
      have hi : i.val = 0 := Fin.val_zero p
      exact ⟨b i, b.ne_zero i, (e_zero_iff i).2 (Or.inl hi), by simpa [hi] using hh i⟩
    · let i : Fin p := ⟨(m + 1).val, (m + 1).val_lt⟩
      have hi : (i.val : k) = C m + 1 := by
        change (((m + 1).val : ℕ) : k) = _
        rw [← map_natCast C, ZMod.natCast_zmod_val, map_add, map_one]
      exact ⟨b i, b.ne_zero i, (e_zero_iff i).2 (Or.inr hi), by
        rw [hh, partner, hi]⟩

end Induced

private theorem labelInvolution_add_one {p : ℕ} (m : ZMod p) :
    labelInvolution m + 1 = -(m + 1) := by
  unfold labelInvolution
  ring

private theorem labelInvolution_fixed_iff {p : ℕ} [Fact p.Prime] (hp : 2 < p) (m : ZMod p) :
    labelInvolution m = m ↔ m = -1 := by
  constructor
  · intro h
    have heq : -(m + 1) = m + 1 := (labelInvolution_add_one m).symm.trans
      (congrArg (· + 1) h)
    have hz : (2 : ZMod p) * (m + 1) = 0 := calc
      _ = (m + 1) + (m + 1) := two_mul _
      _ = -(m + 1) + (m + 1) := congrArg (· + (m + 1)) heq.symm
      _ = 0 := neg_add_cancel _
    have hm := (mul_eq_zero.mp hz).resolve_left (two_ne_zero_of_lt_char (ZMod p) p hp)
    exact eq_neg_of_add_eq_zero_left hm
  · rintro rfl
    simp [labelInvolution, show (1 : ZMod p) - 2 = -1 by ring]

/-- Translating a label by one makes the involution negation. The absolute value of the
least absolute integer representative identifies each orbit with one element of
`Fin (p / 2 + 1)`. -/
private theorem card_labelOrbits {p : ℕ} [NeZero p] (hp : p.Prime) (hp₂ : 2 < p) :
    Nat.card (Quotient (labelSetoid p)) = (p + 1) / 2 := by
  have hcount : p / 2 + 1 = (p + 1) / 2 := by
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
    omega
  rw [← hcount]
  let rep (m : ZMod p) : Fin (p / 2 + 1) :=
    ⟨(m + 1).valMinAbs.natAbs, Nat.lt_succ_of_le (ZMod.natAbs_valMinAbs_le _)⟩
  let f : Quotient (labelSetoid p) → Fin (p / 2 + 1) :=
    Quotient.lift rep (by
      intro m n h
      change n = m ∨ n = labelInvolution m at h
      rcases h with rfl | rfl
      · rfl
      · apply Fin.ext
        change (m + 1).valMinAbs.natAbs = (labelInvolution m + 1).valMinAbs.natAbs
        rw [labelInvolution_add_one, ZMod.natAbs_valMinAbs_neg])
  apply Nat.card_eq_of_equiv_fin (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro m n h
    have heq : (n + 1).valMinAbs.natAbs = (m + 1).valMinAbs.natAbs :=
      (congrArg Fin.val h).symm
    apply Quotient.sound
    change n = m ∨ n = labelInvolution m
    rcases ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp heq with heq | heq
    · exact Or.inl (add_right_cancel heq)
    · exact Or.inr (add_right_cancel (heq.trans (labelInvolution_add_one m).symm))
  · intro i
    let m : ZMod p := i.val
    refine ⟨Quotient.mk _ (m - 1), Fin.ext ?_⟩
    change (m - 1 + 1).valMinAbs.natAbs = i.val
    rw [sub_add_cancel]
    have hm : m.valMinAbs = (i.val : ℤ) := by
      apply (ZMod.valMinAbs_spec _ _).2
      refine ⟨by simp [m], ?_⟩
      have hi := i.isLt
      constructor <;> omega
    simp [hm]

/-- The prime-field baby Verma modules give all simple modules at the normalized
nilpotent character, with precisely the stated identifications. -/
theorem babyVermaNilpotent : babyVermaNilpotentType.{u, w} := by
  intro k _ _ p _ hp
  let : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  intro P hP χ hE hH hF
  obtain ⟨Q, j, hQ, hj, hjInj, _, characters, hcharacters, hquotient⟩ :=
    BabyVermaQuotients.babyVermaQuotients.{u, w} (k := k) hp P hP χ hE
  let C := primeFieldEmbedding k p
  let root (m : ZMod p) : {weight : k // weight ^ p - weight = χ (H k) ^ p} :=
    ⟨C m, by
      rw [hH, zero_pow (NeZero.ne p)]
      exact (exists_primeFieldEmbedding_eq_iff k p (C m)).mp ⟨m, rfl⟩⟩
  let θ (m : ZMod p) := characters (root m)
  have hline (m : ZMod p) : LineCharacter Q χ (C m) (θ m) := (hcharacters (root m)).1
  have hacts (m : ZMod p) : BasisAndActions j (θ m) (C m) := (hcharacters (root m)).2.1
  have hsimple (m : ZMod p) : IsSimpleModule (Ambient P χ) (BabyVerma j (θ m)) :=
    nilpotent_babyVerma_simple hp hP hF (hacts m)
  refine ⟨Q, j, hQ, hj, hjInj, θ, ?_, fun m => highest_weights hp m (hacts m), ?_, ?_,
    labelInvolution_fixed_iff hp, card_labelOrbits (Fact.out : p.Prime) hp⟩
  · intro m
    obtain ⟨b, _⟩ := hacts m
    refine ⟨hline m, hacts m, hsimple m, ?_⟩
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  · intro m n
    change Nonempty (BabyVerma j (θ m) ≃ₗ[Ambient P χ] BabyVerma j (θ n)) ↔
      n = m ∨ n = labelInvolution m
    constructor
    · rintro ⟨iso⟩
      obtain ⟨x, hx, hex, hhx⟩ :=
        (highest_weights hp n (hacts n) (C n)).2 (Or.inl rfl)
      have hne : iso.symm x ≠ 0 := fun hz => hx (iso.symm.injective (hz.trans (map_zero _).symm))
      have he : generator P χ (E k) • iso.symm x = 0 := by
        rw [← iso.symm.map_smul, hex, map_zero]
      have hh : generator P χ (H k) • iso.symm x = C n • iso.symm x := by
        rw [← iso.symm.map_smul, hhx]
        exact (iso.symm.restrictScalars k).map_smul (C n) x
      exact ((highest_weights hp m (hacts m) (C n)).mp ⟨iso.symm x, hne, he, hh⟩).imp
        ((primeFieldEmbedding_injective k p) ·) ((primeFieldEmbedding_injective k p) ·)
    · rintro (rfl | hmn)
      · exact ⟨LinearEquiv.refl _ _⟩
      obtain ⟨x, hx, hex, hhx⟩ :=
        (highest_weights hp m (hacts m) (C n)).2 (Or.inr (congrArg C hmn))
      obtain ⟨g, hg, _⟩ :=
        ((induction_property.{u, u} χ j hj (θ n) (C n) (hline n))
          (BabyVerma j (θ m)) x hhx hex).1
      have hnonzero : g ≠ 0 := by
        intro hz
        apply hx
        simpa [hz] using hg.symm
      have := hsimple m
      have := hsimple n
      exact ⟨(LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hnonzero)).symm⟩
  · intro V _ _ _
    obtain ⟨weight, g, hg⟩ := hquotient V
    have hw : weight.val ^ p - weight.val = 0 := by
      simpa [hH, NeZero.ne p] using weight.property
    obtain ⟨m, hm⟩ := (exists_primeFieldEmbedding_eq_iff k p weight.val).mpr hw
    have heq : root m = weight := Subtype.ext hm
    subst weight
    refine ⟨m, ⟨LinearEquiv.ofBijective g ⟨?_, hg⟩⟩⟩
    have := hsimple m
    apply LinearMap.injective_of_ne_zero
    intro hz
    have : Nontrivial V := IsSimpleModule.nontrivial (Ambient P χ) V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨x, rfl⟩ := hg v
    exact hv (by simp [hz])

end LieNotes.SuperRestricted.BabyVermaNilpotent
