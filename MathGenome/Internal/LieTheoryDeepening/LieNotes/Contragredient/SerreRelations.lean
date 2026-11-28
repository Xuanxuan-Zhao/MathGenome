import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.SerreRelations
import Mathlib.Algebra.Lie.Sl2
import Batteries.Tactic.OpenPrivate

namespace LieNotes.Contragredient.SerreRelations

open CartanQuotient

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exponent_pos {I : Type u} [Finite I] {A : Matrix I I ℤ}
    (hA : IsGeneralizedCartanMatrix A) {i j : I} (hij : i ≠ j) :
    0 < (1 - A i j).toNat := by
  have := hA.2.1 i j hij
  omega

variable {I : Type u} [Finite I] {A : Matrix I I ℤ}
  {H : Type v} [AddCommGroup H] [Module ℂ H] (R : Realization A H)

open private adjointStabilizer from MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.TriangularGrading
open private simpleCoroot_ne_zero from MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanQuotient

local notation "ad" => LieAlgebra.ad ℂ _

private theorem lie_ad_pow_of_commute {x a b : Algebra R} (h : ⁅x, a⁆ = 0) (n : ℕ) :
    ⁅x, (ad a ^ n) b⁆ = (ad a ^ n) ⁅x, b⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
    rw [leibniz_lie, h, zero_lie, zero_add, ih]

private theorem serre_lie_f_eq_zero (hA : IsGeneralizedCartanMatrix A) {i j : I}
    (hij : i ≠ j) (k : I) :
    ⁅f R k, (ad (e R i) ^ (1 - A i j).toNat) (e R j)⁆ = 0 := by
  classical
  let n : ℕ := (-A i j).toNat
  have hle := hA.2.1 i j hij
  have hn : (n : ℤ) = -A i j := by dsimp [n]; omega
  have hexp : (1 - A i j).toNat = n + 1 := by omega
  have hcast : -(A i j : ℂ) = (n : ℂ) := by exact_mod_cast hn.symm
  rw [hexp]
  have hf (l k : I) (hlk : l ≠ k) : ⁅f R k, e R l⁆ = 0 := by
    rw [← lie_skew, (definingRelations R).e_f, ite_eq_right hlk, neg_zero]
  by_cases hki : k = i
  · subst k
    have t : IsSl2Triple (cartan R (R.h i)) (e R i) (f R i) :=
      { h_ne_zero := simpleCoroot_ne_zero R i
        lie_e_f := by simpa using (definingRelations R).e_f i i
        lie_h_e_nsmul := by
          rw [(definingRelations R).cartan_e, R.pairing, hA.1]
          simp [two_smul]
        lie_h_f_nsmul := by
          rw [(definingRelations R).cartan_f, R.pairing, hA.1]
          simp [two_smul] }
    have hp : t.symm.HasPrimitiveVectorWith (e R j) (n : ℂ) :=
      { ne_zero := e_ne_zero R j
        lie_e := hf j i hij.symm
        lie_h := by
          rw [neg_lie, (definingRelations R).cartan_e, R.pairing, ← neg_smul, hcast] }
    simpa only [LieAlgebra.ad, sub_self, mul_zero, zero_smul] using hp.lie_e_pow_succ_toEnd_f n
  · rw [lie_ad_pow_of_commute R (hf i k (Ne.symm hki))]
    by_cases hkj : k = j
    · subst k
      rw [← lie_skew, (definingRelations R).e_f, ite_eq_left rfl]
      have heh : ⁅e R i, -cartan R (R.h j)⁆ = (A j i : ℂ) • e R i := by
        rw [lie_neg, ← lie_skew, neg_neg, (definingRelations R).cartan_e, R.pairing]
      rw [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply, heh, map_smul]
      by_cases hn0 : n = 0
      · have hij0 : A i j = 0 := by omega
        have hji0 := (hA.2.2 i j).mp hij0
        simp [hji0]
      · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        simp [hs, pow_succ, Module.End.mul_apply]
    · rw [hf j k (Ne.symm hkj), map_zero]

private inductive Raised (x : Algebra R) : Algebra R → Prop
  | base : Raised x x
  | step {y : Algebra R} (i : I) : Raised x y → Raised x ⁅e R i, y⁆

private theorem e_mem_positive (i : I) : e R i ∈ positive R := by
  exact ⟨Presentation.e R i, LieSubalgebra.subset_lieSpan (Set.mem_range_self i), rfl⟩

-- A homogeneous vector on the positive side killed by the negative generators
-- generates a Cartan-disjoint ideal, hence vanishes in the quotient.
private theorem positive_primitive_eq_zero {x : Algebra R} {q : Q I}
    (hx : x ∈ positive R) (hq : x ∈ grade R q) (hf : ∀ k, ⁅f R k, x⁆ = 0) :
    x = 0 := by
  classical
  let W : Submodule ℂ (Algebra R) := Submodule.span ℂ {y | Raised R x y}
  have hW {y : Algebra R} (hy : Raised R x y) : y ∈ W := Submodule.subset_span hy
  have hspan (a : Algebra R) (ha : ∀ y, Raised R x y → ⁅a, y⁆ ∈ W) :
      ∀ y ∈ W, ⁅a, y⁆ ∈ W := by
    have hle : W ≤ W.comap (ad a) := Submodule.span_le.mpr ha
    exact fun y hy ↦ hle hy
  have hweight {y : Algebra R} (hy : Raised R x y) : ∃ p, y ∈ grade R p := by
    induction hy with
    | base => exact ⟨q, hq⟩
    | step i _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨_, lie_mem_grade R (e_mem_grade R i) hp⟩
  have hcartan (h : H) : ∀ y ∈ W, ⁅cartan R h, y⁆ ∈ W := by
    apply hspan
    intro y hy
    obtain ⟨p, hp⟩ := hweight hy
    rw [(mem_grade R).mp hp h]
    exact W.smul_mem _ (hW hy)
  have he (i : I) : ∀ y ∈ W, ⁅e R i, y⁆ ∈ W :=
    hspan _ fun _ hy ↦ hW (.step i hy)
  have hneg (k : I) : ∀ y ∈ W, ⁅f R k, y⁆ ∈ W := by
    apply hspan
    intro y hy
    induction hy with
    | base => rw [hf k]; exact W.zero_mem
    | step i hy ih =>
      rw [leibniz_lie, ← lie_skew (f R k) (e R i), (definingRelations R).e_f, neg_lie]
      apply W.add_mem _ (he i _ ih)
      split_ifs with hik
      · exact W.neg_mem (hcartan (R.h i) _ (hW hy))
      · simpa only [zero_lie, neg_zero] using W.zero_mem
  have hstable : adjointStabilizer W = ⊤ := by
    apply top_unique
    rw [← generated R]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ((⟨h, rfl⟩ | ⟨i, rfl⟩) | ⟨k, rfl⟩)
    · exact hcartan h
    · exact he i
    · exact hneg k
  let J : LieIdeal ℂ (Algebra R) :=
    { W with
      lie_mem := fun {a y} hy ↦
        (show a ∈ adjointStabilizer W by rw [hstable]; trivial) y hy }
  have hle : W ≤ (positive R).toSubmodule := by
    apply Submodule.span_le.mpr
    intro y hy
    change Raised R x y at hy
    induction hy with
    | base => exact hx
    | step i _ ih => exact (positive R).lie_mem (e_mem_positive R i) ih
  have hd : Disjoint (positive R).toSubmodule (cartan R).range := by
    rw [← iSup_positive_grade, ← grade_zero]
    exact ((grade_iSupIndep R).disjoint_biSup
      (show (0 : Q I) ∉ {p | PositiveDegree p} from fun hp ↦ hp.1 rfl)).symm
  have hJ := eq_bot_of_disjoint_cartan R J (hd.mono_left hle)
  have hxJ : x ∈ J := hW .base
  rw [hJ] at hxJ
  exact hxJ

theorem positive_serre (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    {i j : I} (hij : i ≠ j) :
    (ad (e R i) ^ (1 - A i j).toNat) (e R j) = 0 := by
  have hm (n : ℕ) :
      (ad (e R i) ^ n) (e R j) ∈ positive R ∧
        ∃ q, (ad (e R i) ^ n) (e R j) ∈ grade R q := by
    induction n with
    | zero => exact ⟨e_mem_positive R j, simpleDegree j, e_mem_grade R j⟩
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      obtain ⟨hp, q, hq⟩ := ih
      exact ⟨(positive R).lie_mem (e_mem_positive R i) hp, _,
        lie_mem_grade R (e_mem_grade R i) hq⟩
  obtain ⟨hmem, q, hq⟩ := hm (1 - A i j).toNat
  exact positive_primitive_eq_zero R hmem hq (serre_lie_f_eq_zero R hA hij)

theorem negative_serre (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    {i j : I} (hij : i ≠ j) :
    (ad (f R i) ^ (1 - A i j).toNat) (f R j) = 0 := by
  obtain ⟨τ, _, _, hτ, _⟩ := hasInterchange R
  have hmap (n : ℕ) : τ ((ad (e R i) ^ n) (e R j)) = (ad (f R i) ^ n) (f R j) := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hτ j
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieEquiv.map_lie,
        hτ, ih]
  rw [← hmap, positive_serre hA R hij, map_zero]

end LieNotes.Contragredient.SerreRelations
