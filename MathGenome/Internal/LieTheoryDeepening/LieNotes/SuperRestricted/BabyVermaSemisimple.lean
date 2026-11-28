import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaSemisimple
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaQuotients
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Separable

/-! Simplicity and classification of the baby Verma modules at a nonzero
semisimple character of restricted `sl₂`. -/

namespace LieNotes.SuperRestricted.BabyVermaSemisimple

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaSemisimple
open private matrix_basis_powers from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

private theorem weight_count {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ}
    [CharP k p] (hp : 2 < p) (χ : Model k →ₗ[k] k) :
    Nonempty (Weights p χ ≃ Fin p) := by
  classical
  open Polynomial in
  let poly : k[X] := X ^ p - X - C (χ (H k) ^ p)
  have hdeg₁ : (Polynomial.X ^ p - Polynomial.X : Polynomial k).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    simpa using (show 1 < p by omega)
  have hdeg : poly.natDegree = p := by
    dsimp [poly]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, hdeg₁]
    simp [hdeg₁, show 0 < p by omega]
  have hder : poly.derivative = -1 := by
    simp only [poly, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, Polynomial.derivative_C, CharP.cast_eq_zero k p,
      Polynomial.C_0, zero_mul, zero_sub, sub_zero]
  have hsep : poly.Separable := by
    refine ⟨0, -1, ?_⟩
    rw [hder]
    simp
  have hroots : ∀ x : k, (x ^ p - x = χ (H k) ^ p) ↔ x ∈ poly.rootSet k := by
    intro x
    rw [Polynomial.mem_rootSet_of_ne hsep.ne_zero]
    simp [poly, sub_eq_zero]
  have hcard : Fintype.card (poly.rootSet k) = p :=
    (Polynomial.card_rootSet_eq_natDegree hsep (IsAlgClosed.splits_domain _)).trans hdeg
  exact ⟨(Equiv.subtypeEquivRight hroots).trans (Fintype.equivFinOfCardEq hcard)⟩

section Basis

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
variable {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
variable {χ : Model k →ₗ[k] k} {j : BorelAlgebra Q χ →ₐ[k] Ambient P χ}
variable {θ : BorelAlgebra Q χ →ₐ[k] k}

private theorem raising_coefficient_ne_zero (weight : Weights p χ)
    (hη : χ (H k) ≠ 0) (i : Fin p) (hi : 0 < i.val) :
    (i.val : k) * (weight.val - (i.val : k) + 1) ≠ 0 := by
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  apply mul_ne_zero
  · intro hz
    exact (Nat.not_le_of_lt i.isLt) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff k p _).mp hz))
  · intro hz
    have hw : weight.val = (i.val : k) - 1 := by
      rwa [sub_add_eq_add_sub, sub_eq_zero, ← eq_sub_iff_add_eq] at hz
    have hfix : ((i.val : k) - 1) ^ p = (i.val : k) - 1 := by
      change (frobenius k p) ((i.val : k) - 1) = (i.val : k) - 1
      rw [map_sub, map_natCast, map_one]
    have hroot := weight.property
    change weight.val ^ p - weight.val = χ (H k) ^ p at hroot
    rw [hw, hfix, sub_self] at hroot
    exact pow_ne_zero p hη hroot.symm

private theorem classification_of_basis (weight : Weights p χ) (hη : χ (H k) ≠ 0)
    (he_pow : generator P χ (E k) ^ p = 0) (hB : BasisAndActions j θ weight.val) :
    IsSimpleModule (Ambient P χ) (BabyVerma j θ) ∧
      Module.finrank k (BabyVerma j θ) = p ∧ HighestWeightLine j θ weight.val := by
  classical
  let e := generator P χ (E k)
  let f := generator P χ (F k)
  let h := generator P χ (H k)
  let v₀ := highest j θ
  let c (i : Fin p) := (i.val : k) * (weight.val - (i.val : k) + 1)
  obtain ⟨b, hb, hh, he, he_step, _, _⟩ := hB
  have hzero : b (0 : Fin p) = v₀ := by simpa [f, v₀] using hb (0 : Fin p)
  have hv₀ : v₀ ≠ 0 := hzero ▸ b.ne_zero 0
  have hv₀h : h • v₀ = weight.val • v₀ := by
    simpa [h, hzero] using hh (0 : Fin p)

  -- Each noninitial coordinate is recovered from the preceding coordinate
  -- of the image under the raising operator.
  let raise : Module.End k (BabyVerma j θ) := Algebra.lsmul k k (BabyVerma j θ) e
  have coord_step (i l : Fin p) (hil : i.val = l.val + 1) :
      (b.coord l).comp raise = c i • b.coord i := by
    apply b.ext
    intro r
    change b.coord l (e • b r) = c i * b.coord i (b r)
    by_cases hr : r = 0
    · subst r
      have hi : i ≠ 0 := by
        intro hz
        subst i
        simp at hil
      have he_zero : e • b (0 : Fin p) = 0 := by
        rw [hzero]
        exact he
      rw [he_zero, map_zero]
      simp [Module.Basis.coord, hi.symm]
    · have hrval : r.val ≠ 0 := fun hz => hr (Fin.ext (by simpa using hz))
      let s : Fin p := ⟨r.val - 1, by have := r.isLt; omega⟩
      have hrs : r.val = s.val + 1 := by dsimp [s]; omega
      rw [show e • b r = c r • b s from he_step r s hrs, map_smul]
      have hsr : s = l ↔ r = i := by
        constructor
        · intro heq
          apply Fin.ext
          rw [hrs, heq, hil]
        · intro heq
          apply Fin.ext
          rw [heq, hil] at hrs
          omega
      by_cases hri : r = i
      · have hsl : s = l := hsr.mpr hri
        simp [Module.Basis.coord, hri, hsl]
      · have hsl : s ≠ l := mt hsr.mp hri
        simp [Module.Basis.coord, hri, hsl]

  have hker (v : BabyVerma j θ) : e • v = 0 ↔ ∃ a : k, v = a • v₀ := by
    constructor
    · intro hv
      have hoff (i : Fin p) (hi : i ≠ 0) : b.repr v i = 0 := by
        have hival : i.val ≠ 0 := fun hz => hi (Fin.ext (by simpa using hz))
        let l : Fin p := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hil : i.val = l.val + 1 := by dsimp [l]; omega
        have hc := LinearMap.congr_fun (coord_step i l hil) v
        change b.coord l (e • v) = c i * b.repr v i at hc
        rw [hv, map_zero] at hc
        exact (mul_eq_zero.mp hc.symm).resolve_left
          (raising_coefficient_ne_zero weight hη i (by omega))
      refine ⟨b.repr v 0, ?_⟩
      calc
        v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
        _ = b.repr v 0 • v₀ := by
          rw [Finset.sum_eq_single (0 : Fin p), hzero]
          · intro i _ hi
            rw [hoff i hi, zero_smul]
          · simp
    · rintro ⟨a, rfl⟩
      rw [smul_comm e a, show e • v₀ = 0 from he, smul_zero]

  refine ⟨?_, ?_, hv₀, hker, hv₀h⟩
  · have : Nontrivial (BabyVerma j θ) := ⟨⟨v₀, 0, hv₀⟩⟩
    apply (isSimpleModule_iff _ _).mpr
    refine IsSimpleOrder.of_forall_eq_top fun S hS => ?_
    obtain ⟨x, hx, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    -- A nonzero submodule meets the highest line because e is nilpotent.
    have killed : ∃ n : ℕ, e ^ n • x = 0 := ⟨p, by rw [he_pow, zero_smul]⟩
    have hn_ne : Nat.find killed ≠ 0 := by
      intro hz
      have hz' := Nat.find_spec killed
      rw [hz, pow_zero, one_smul] at hz'
      exact hx_ne hz'
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
    have hy_ne : e ^ n • x ≠ 0 := Nat.find_min killed (by omega)
    have hy_e : e • (e ^ n • x) = 0 := by
      rw [← mul_smul, ← pow_succ']
      simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec killed
    obtain ⟨a, ha⟩ := (hker _).mp hy_e
    have ha_ne : a ≠ 0 := fun hz => hy_ne (by simp [ha, hz])
    have hv₀_mem : v₀ ∈ S := by
      have hmem := (S.restrictScalars k).smul_mem a⁻¹ (S.smul_mem (e ^ n) hx)
      change a⁻¹ • (e ^ n • x) ∈ S at hmem
      rwa [ha, inv_smul_smul₀ ha_ne] at hmem
    have hspan : Submodule.span k (Set.range b) ≤ S.restrictScalars k := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change b i ∈ S
      rw [hb i]
      exact S.smul_mem _ hv₀_mem
    rw [b.span_eq] at hspan
    exact top_unique fun v hv => hspan (show v ∈ (⊤ : Submodule k (BabyVerma j θ)) from hv)
  · simpa using Module.finrank_eq_card_basis b

end Basis

/-- The modules at the `p` Artin–Schreier labels give all simple modules
of the reduced algebra at a nonzero semisimple character. -/
theorem babyVermaSemisimple : babyVermaSemisimpleType.{u, w} := by
  intro k _ _ p _ hp
  let : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
  intro P hP χ hχe _ hη
  obtain ⟨Q, j, hQ, hj, hj_inj, _, θ, hθ, hquotient⟩ :=
    BabyVermaQuotients.babyVermaQuotients.{u, w} (k := k) hp P hP χ hχe
  have he_pow : generator P χ (E k) ^ p = 0 := by
    have h := BabyVermaInduction.generator_pow P χ (E k)
    rw [(matrix_basis_powers hP).1, hχe, zero_pow (NeZero.ne p), map_zero] at h
    exact h.trans (by simp [generator])
  have hmodules (weight : Weights p χ) :=
    classification_of_basis weight hη he_pow (hθ weight).2.1
  refine ⟨weight_count hp χ, Q, j, hQ, hj, hj_inj, θ,
    fun weight => ⟨(hθ weight).1, hmodules weight⟩, ?_, ?_⟩
  · intro weight weight'
    constructor
    · rintro ⟨g⟩
      have hl := (hmodules weight).2.2
      have hl' := (hmodules weight').2.2
      have hx_ne : g (highest j (θ weight)) ≠ 0 := fun hz =>
        hl.1 (g.injective (hz.trans g.map_zero.symm))
      have hx_e : generator P χ (E k) • g (highest j (θ weight)) = 0 := by
        rw [← g.map_smul, (hl.2.1 _).mpr ⟨1, (one_smul _ _).symm⟩, map_zero]
      obtain ⟨a, ha⟩ := (hl'.2.1 _).mp hx_e
      have hx_h : generator P χ (H k) • g (highest j (θ weight)) =
          weight.val • g (highest j (θ weight)) := by
        rw [← g.map_smul, hl.2.2]
        exact (g.restrictScalars k).map_smul _ _
      have hx_h' : generator P χ (H k) • g (highest j (θ weight)) =
          weight'.val • g (highest j (θ weight)) := by
        rw [ha, smul_comm (generator P χ (H k)) a, hl'.2.2, smul_comm a weight'.val]
      exact Subtype.ext (smul_left_injective k hx_ne (hx_h.symm.trans hx_h'))
    · rintro rfl
      exact ⟨LinearEquiv.refl _ _⟩
  · intro V _ _ _
    obtain ⟨weight, g, hg⟩ := hquotient V
    have := (hmodules weight).1
    have hg_ne : g ≠ 0 := by
      intro hz
      have hV : Nontrivial V := IsSimpleModule.nontrivial (Ambient P χ) V
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨x, hx⟩ := hg v
      rw [hz, LinearMap.zero_apply] at hx
      exact hv hx.symm
    exact ⟨weight, ⟨LinearEquiv.ofBijective g ⟨g.injective_of_ne_zero hg_ne, hg⟩⟩⟩

end LieNotes.SuperRestricted.BabyVermaSemisimple
