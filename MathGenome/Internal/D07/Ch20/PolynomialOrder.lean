import MathGenome.Internal.Specs.D07.Ch20.PolynomialOrder
import MathGenome.Internal.D07.Ch20.PolynomialOrderRepeatedFactorOrder
import MathGenome.Internal.D07.Ch11.QuotientNormalForm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.SpecificDegree

universe u v
namespace D07.Ch20.PolynomialOrder
open Polynomial
open Specs.D07.Ch20.PolynomialOrder

/-- The multiplicative order of X in the canonical quotient. -/
noncomputable def polynomialOrder : OrderFunctionType.{u} := orderValue

/-- Nonzero constant term makes X invertible, even for reducible f. -/
theorem root_isUnit {F : Type u} [Field F] (f : F[X]) (hf : f.eval 0 ≠ 0) :
    IsUnit (AdjoinRoot.root f) := by
  have hcop : IsCoprime (X : F[X]) f :=
    irreducible_X.coprime_iff_not_dvd.mpr
      (fun h => hf (by simpa only [coeff_zero_eq_eval_zero] using X_dvd_iff.mp h))
  obtain ⟨a, b, hab⟩ := hcop
  have heq := congrArg (AdjoinRoot.mk f) hab
  have hinv : AdjoinRoot.mk f a * AdjoinRoot.root f = 1 := by
    simpa only [map_add, map_mul, map_one, AdjoinRoot.mk_self, mul_zero, add_zero,
      AdjoinRoot.mk_X] using heq
  exact isUnit_iff_exists_inv.mpr ⟨AdjoinRoot.mk f a, by simpa only [mul_comm] using hinv⟩

theorem quotient_unit_order : QuotientUnitOrder.{u} := by
  intro F _ f hf
  obtain ⟨a, ha⟩ := root_isUnit f hf
  refine ⟨a, ha, ?_⟩
  change orderOf (AdjoinRoot.root f) = orderOf a
  rw [← ha, orderOf_units]

theorem order_exists : OrderExists.{u} := by
  intro F _ _ f _hfdeg hf0
  have hf : f ≠ 0 := by intro h; subst f; simp at hf0
  have : Finite (AdjoinRoot f) := (Ch11.QuotientNormalForm.finiteCardinality F f hf).1
  have : Finite (AdjoinRoot f)ˣ := Finite.of_injective _ Units.val_injective
  have hpos : 0 < polynomialOrder F f := orderOf_pos_iff.mpr (root_isUnit f hf0).isOfFinOrder
  refine ⟨⟨hpos, ?_⟩, ?_⟩
  · exact (PolynomialOrderRepeatedFactorOrder.order_dvd_iff f _).mp dvd_rfl
  · intro h hh
    exact orderOf_le_of_pow_eq_one hh.1
      ((PolynomialOrderRepeatedFactorOrder.root_pow_eq_one_iff f h).mpr hh.2)

theorem order_divisibility : OrderDivisibility.{u} := by
  intro F _ _ f _ _ h
  exact (PolynomialOrderRepeatedFactorOrder.order_dvd_iff f h).symm

theorem root_order : RootOrder.{u,v} := by
  intro F _ _ g hg _ _ L _ _ a ha
  exact (PolynomialOrderRepeatedFactorOrder.root_order F g hg L a ha).symm

theorem irreducible_order_bound : IrreducibleOrderBound.{u} := by
  intro F _ _ g hg hg0
  let : Fact (Irreducible g) := ⟨hg⟩
  obtain ⟨hfin, hcard⟩ := Ch11.QuotientNormalForm.finiteCardinality F g hg.ne_zero
  let : Finite (AdjoinRoot g) := hfin
  let : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hroot : AdjoinRoot.root g ≠ 0 := by
    intro h
    have he := AdjoinRoot.eval₂_root g
    rw [h] at he
    exact hg0 (by simpa [← Polynomial.coeff_zero_eq_eval_zero] using he)
  have hpow := FiniteField.pow_card_sub_one_eq_one (AdjoinRoot.root g) hroot
  have hd := orderOf_dvd_of_pow_eq_one hpow
  change orderOf (AdjoinRoot.root g) ∣ _
  have hcard' : Nat.card (AdjoinRoot g) = Nat.card F ^ g.natDegree := hcard
  rwa [← Nat.card_eq_fintype_card, hcard'] at hd

theorem repeated_factor_order : RepeatedFactorOrder.{u,v} :=
  PolynomialOrderRepeatedFactorOrder.repeated_factor_order

/-- A concrete least divisibility exponent identifies the canonical order. -/
theorem order_eq_of_isLeast {F : Type u} [Field F] (f : F[X]) (n : ℕ)
    (hn : IsLeast {h : ℕ | 0 < h ∧ f ∣ X ^ h - 1} n) :
    polynomialOrder F f = n := by
  have hd : polynomialOrder F f ∣ n :=
    (PolynomialOrderRepeatedFactorOrder.order_dvd_iff f n).mpr hn.1.2
  have hp : 0 < polynomialOrder F f := Nat.pos_of_dvd_of_pos hd hn.1.1
  apply Nat.le_antisymm (Nat.le_of_dvd hn.1.1 hd)
  exact hn.2 ⟨hp, (PolynomialOrderRepeatedFactorOrder.order_dvd_iff f _).mp dvd_rfl⟩

theorem binary_example : BinaryExample := by
  let g : (ZMod 2)[X] := X ^ 2 + X + 1
  have hgm : g.Monic := by dsimp [g]; monicity; norm_num
  have hgd : g.natDegree = 2 := by dsimp [g]; compute_degree; norm_num
  have hgi : Irreducible g := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hgd]
    · intro x
      have hx : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hx with rfl | rfl <;> norm_num [Polynomial.IsRoot, g] <;> decide
  have hg0 : g.eval 0 ≠ 0 := by simp [g]
  have hgt : g ∣ X ^ 3 - 1 := by
    refine ⟨X - 1, ?_⟩
    dsimp [g]
    ring
  have ho : polynomialOrder (ZMod 2) g = 3 := by
    let : Fact (Irreducible g) := ⟨hgi⟩
    change orderOf (AdjoinRoot.root g) = 3
    apply orderOf_eq_prime
    · exact (PolynomialOrderRepeatedFactorOrder.root_pow_eq_one_iff g 3).mpr hgt
    · intro h
      have hdiv : g ∣ X - 1 := by
        simpa only [pow_one] using
          (PolynomialOrderRepeatedFactorOrder.root_pow_eq_one_iff g 1).mp
            (by simpa only [pow_one] using h)
      have hdeg := Polynomial.natDegree_le_of_dvd hdiv
        (by simpa only [C_1] using (X_sub_C_ne_zero (1 : ZMod 2)))
      simp only [hgd, ← C_1, natDegree_X_sub_C] at hdeg
      omega
  have hleast : IsLeast {u : ℕ | 3 ≤ 2 ^ u} 2 := by
    refine ⟨by decide, ?_⟩
    intro h hh
    change 3 ≤ 2 ^ h at hh
    by_contra hlt
    have : h = 0 ∨ h = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hh
  have hd : (g ^ 3).natDegree = 6 := by rw [natDegree_pow, hgd]
  have h0 : (g ^ 3).eval 0 ≠ 0 := by simp [g]
  have hfac : g ^ 3 = C (1 : ZMod 2) * ∏ _i : Unit, g ^ (3 : ℕ) := by simp
  have hrep := repeated_factor_order (ZMod 2) 2 Unit (fun _ => g) (fun _ => 3)
    1 (g ^ 3) (fun _ => hgm) (fun _ => hgi)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => by decide)
    (by decide) (by omega) h0 hfac
  have hc := (hrep.2.2 2 (fun _ => by decide)
    (fun u hu => hleast.2 (hu ()))).1
  change polynomialOrder (ZMod 2) (g ^ 3) =
    Finset.univ.lcm (fun _ : Unit => polynomialOrder (ZMod 2) g) * 2 ^ 2 at hc
  have hocube : polynomialOrder (ZMod 2) (g ^ 3) = 12 := by
    simpa [ho] using hc
  change orderValue (ZMod 2) g = 3 ∧ orderValue (ZMod 2) (g ^ 3) = 12 ∧ _
  refine ⟨ho, hocube, hd, h0, ?_, hleast⟩
  change ¬polynomialOrder (ZMod 2) (g ^ 3) ∣ _
  rw [hocube, hd]
  decide

end D07.Ch20.PolynomialOrder
