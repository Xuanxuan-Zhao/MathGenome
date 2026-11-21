import MathGenome.Internal.Specs.D07.Ch20.PolynomialOrderRepeatedFactorOrder
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.PrincipalIdealDomain

universe u v
namespace D07.Ch20.PolynomialOrderRepeatedFactorOrder
open Polynomial
open Specs.D07.Ch20.PolynomialOrderRepeatedFactorOrder

/-- Equality of powers in the quotient is exactly polynomial divisibility. -/
theorem root_pow_eq_one_iff {F : Type u} [Field F] (f : F[X]) (n : ℕ) :
    AdjoinRoot.root f ^ n = 1 ↔ f ∣ X ^ n - 1 := by
  rw [← sub_eq_zero, ← AdjoinRoot.mk_X, ← map_pow, ← map_one (AdjoinRoot.mk f),
    ← map_sub, AdjoinRoot.mk_eq_zero]

/-- This statement holds even when the quotient has zero divisors. -/
theorem order_dvd_iff {F : Type u} [Field F] (f : F[X]) (n : ℕ) :
    orderOf (AdjoinRoot.root f) ∣ n ↔ f ∣ X ^ n - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, root_pow_eq_one_iff]

theorem frobenius_multiplicity : FrobeniusMultiplicity.{u} := by
  intro F _ p _ _ u v
  rw [mul_comm (p ^ u), pow_mul, sub_pow_char_pow, one_pow]

theorem root_order : RootOrder.{u,v} := by
  intro F _ g hg L _ _ a ha
  let : Fact (Irreducible g) := ⟨hg⟩
  let φ : AdjoinRoot g →ₐ[F] L := AdjoinRoot.liftAlgHom g (Algebra.ofId F L) a ha
  have hφ : φ (AdjoinRoot.root g) = a := AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← hφ]
  exact orderOf_injective φ.toMonoidHom φ.injective _

/-- Monic irreducibles with nonzero constant term have positive root order. -/
theorem root_order_pos {F : Type u} [Field F] [Finite F] (g : F[X])
    (hm : g.Monic) (hg : Irreducible g) (h0 : g.eval 0 ≠ 0) :
    0 < orderOf (AdjoinRoot.root g) := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : Module.Finite F (AdjoinRoot g) := hm.finite_adjoinRoot
  have : Finite (AdjoinRoot g) := Module.finite_of_finite F
  have hroot : AdjoinRoot.root g ≠ 0 := by
    intro h
    have he := AdjoinRoot.eval₂_root g
    rw [h] at he
    exact h0 (by simpa [← Polynomial.coeff_zero_eq_eval_zero] using he)
  exact Nat.pos_of_ne_zero (orderOf_eq_zero_iff_eq_zero.not.mpr hroot)

/-- An order in a characteristic-p field cannot be divisible by p. -/
theorem root_order_coprime {F : Type u} [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (g : F[X])
    (hm : g.Monic) (hg : Irreducible g) (h0 : g.eval 0 ≠ 0) :
    Nat.Coprime (orderOf (AdjoinRoot.root g)) p := by
  let : Fact (Irreducible g) := ⟨hg⟩
  have : NeZero (orderOf (AdjoinRoot.root g)) := ⟨(root_order_pos g hm hg h0).ne'⟩
  have : CharP (AdjoinRoot g) p := charP_of_injective_ringHom (AdjoinRoot.of g).injective p
  have hn := (IsPrimitiveRoot.orderOf (AdjoinRoot.root g)).neZero'
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hn.out ((CharP.cast_eq_zero_iff (AdjoinRoot g) p _).mpr h))).symm

/-- A prime can occur at most n times in the nth power of a squarefree element. -/
theorem prime_pow_dvd_squarefree_pow {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {g H : R} (hg : Prime g) (hH : Squarefree H)
    {b n : ℕ} (hb : 0 < b) :
    g ^ b ∣ H ^ n ↔ g ∣ H ∧ b ≤ n := by
  have bound : ∀ n b : ℕ, g ^ b ∣ H ^ n → b ≤ n := by
    intro n
    induction n with
    | zero =>
      intro b hd
      by_contra h
      have hb : 0 < b := Nat.lt_of_not_ge h
      have hgu : g ∣ 1 := (dvd_pow_self g hb.ne').trans (by simpa using hd)
      exact hg.not_isUnit (isUnit_iff_dvd_one.mpr hgu)
    | succ n ih =>
      intro b hd
      cases b with
      | zero => exact Nat.zero_le _
      | succ b =>
        have hd' : g ^ b ∣ H ^ n :=
          hH.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hg
            (by simpa only [pow_succ'] using hd)
        exact Nat.succ_le_succ (ih b hd')
  constructor
  · intro hd
    exact ⟨hg.dvd_of_dvd_pow ((dvd_pow_self g hb.ne').trans hd), bound n b hd⟩
  · rintro ⟨hd, hbn⟩
    exact (pow_dvd_pow g hbn).trans (pow_dvd_pow_of_dvd hd n)

/-- Distinct monic irreducibles are pairwise coprime, as are their powers. -/
theorem irreducible_powers_pairwise_coprime {F : Type*} [Field F]
    {ι : Type*} (g : ι → F[X]) (b : ι → ℕ)
    (hm : ∀ i, (g i).Monic) (hg : ∀ i, Irreducible (g i))
    (hinj : Function.Injective g) : Pairwise (fun i j => IsCoprime (g i ^ b i) (g j ^ b j)) := by
  intro i j hij
  apply IsCoprime.pow
  apply (hg i).coprime_iff_not_dvd.mpr
  intro hd
  exact hij (hinj (eq_of_monic_of_associated (hm i) (hm j)
    ((hg i).associated_of_dvd (hg j) hd)))

/-- The scalar does not change divisibility; coprimality lets us reassemble
all the irreducible powers from their individual divisibilities. -/
theorem factor_product_dvd_iff {F : Type*} [Field F]
    {ι : Type*} [Fintype ι] (g : ι → F[X]) (b : ι → ℕ) (c : F)
    (hm : ∀ i, (g i).Monic) (hg : ∀ i, Irreducible (g i))
    (hinj : Function.Injective g) (hc : c ≠ 0) (H : F[X]) :
    C c * ∏ i, g i ^ b i ∣ H ↔ ∀ i, g i ^ b i ∣ H := by
  classical
  have hu : IsUnit (C c : F[X]) := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))
  rw [hu.mul_left_dvd]
  constructor
  · intro hd i
    exact (Finset.dvd_prod_of_mem (fun i => g i ^ b i) (Finset.mem_univ i)).trans hd
  · exact Fintype.prod_dvd_of_coprime (irreducible_powers_pairwise_coprime g b hm hg hinj)

theorem divisibility_multiplicity : DivisibilityMultiplicity.{u,v} := by
  intro F _ _ p _ _ ι _ g b c hm hg hinj hb hc u v hv
  rw [frobenius_multiplicity F p u v,
    factor_product_dvd_iff g b c hm hg hinj hc]
  have hH : Squarefree (X ^ v - 1 : F[X]) := by
    exact (Polynomial.X_pow_sub_one_separable_iff.mpr
      (fun h => hv ((CharP.cast_eq_zero_iff F p v).mp h))).squarefree
  apply forall_congr'
  intro i
  rw [prime_pow_dvd_squarefree_pow (irreducible_iff_prime.mp (hg i)) hH (hb i),
    ← order_dvd_iff]

/-- Every finite list of multiplicities has a least bounding p-power. -/
theorem exists_least_multiplicity_exponent {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 2 ≤ p) (b : ι → ℕ) :
    ∃ t : ℕ, IsLeast {u : ℕ | ∀ i, b i ≤ p ^ u} t := by
  classical
  let M := Finset.univ.sup b
  have hex : ∃ t : ℕ, ∀ i, b i ≤ p ^ t := by
    refine ⟨M, fun i => ?_⟩
    exact (Finset.le_sup (f := b) (Finset.mem_univ i)).trans
      ((Nat.le_of_lt (Nat.lt_two_pow_self : M < 2 ^ M)).trans (Nat.pow_le_pow_left hp M))
  exact ⟨Nat.find hex, Nat.find_spec hex, fun u hu => Nat.find_min' hex hu⟩

/-- The lcm formula, including its characterization as the least positive
exponent, follows from the exact multiplicity test. -/
theorem repeated_factor_order : RepeatedFactorOrder.{u,v} := by
  classical
  intro F _ _ p _ _ ι _ _ g b c f hm hg hinj hb hc _hfdeg hf0 hfac
  have hgdvd (i : ι) : g i ∣ f := by
    rw [hfac]
    exact (dvd_pow_self (g i) (hb i).ne').trans
      ((Finset.dvd_prod_of_mem (fun i => g i ^ b i) (Finset.mem_univ i)).trans
        (dvd_mul_left _ _))
  have hg0 (i : ι) : (g i).eval 0 ≠ 0 := by
    intro h
    exact hf0 (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (hgdvd i) h)
  have hcop (i : ι) : Nat.Coprime (orderOf (AdjoinRoot.root (g i))) p :=
    root_order_coprime p (g i) (hm i) (hg i) (hg0 i)
  refine ⟨hcop, exists_least_multiplicity_exponent p (Fact.out : p.Prime).two_le b, ?_⟩
  intro t ht htmin
  let e := Finset.univ.lcm (fun i => orderOf (AdjoinRoot.root (g i)))
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro i _
    exact (root_order_pos (g i) (hm i) (hg i) (hg0 i)).ne'
  have hecop : Nat.Coprime e p := by
    exact (Nat.coprime_prod_left_iff.mpr (fun i _ => hcop i)).of_dvd_left
      (Finset.lcm_dvd_prod _ _)
  have hep : ¬p ∣ e := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hecop.symm
  have hedvd (i : ι) : orderOf (AdjoinRoot.root (g i)) ∣ e :=
    Finset.dvd_lcm (Finset.mem_univ i)
  have hnpos : 0 < e * p ^ t := Nat.mul_pos hepos (pow_pos (Fact.out : p.Prime).pos t)
  have hndvd : f ∣ X ^ (e * p ^ t) - 1 := by
    rw [hfac, mul_comm e]
    exact (divisibility_multiplicity F p ι g b c hm hg hinj hb hc t e hep).mpr
      (fun i => ⟨hedvd i, ht i⟩)
  have hleast : IsLeast {h : ℕ | 0 < h ∧ f ∣ X ^ h - 1} (e * p ^ t) := by
    refine ⟨⟨hnpos, hndvd⟩, ?_⟩
    intro h hh
    obtain ⟨u, v, hv, hdecomp⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hh.1.ne' p (Fact.out : p.Prime).ne_one
    have hall := (divisibility_multiplicity F p ι g b c hm hg hinj hb hc u v hv).mp
      (show C c * ∏ i, g i ^ b i ∣ X ^ (p ^ u * v) - 1 by rw [← hfac, ← hdecomp]; exact hh.2)
    have hev : e ∣ v := Finset.lcm_dvd (fun i _ => (hall i).1)
    have htu : t ≤ u := htmin u (fun i => (hall i).2)
    apply Nat.le_of_dvd hh.1
    rw [hdecomp, mul_comm (p ^ u)]
    exact Nat.mul_dvd_mul hev (pow_dvd_pow p htu)
  refine ⟨?_, hleast⟩
  apply Nat.le_antisymm
  · exact orderOf_le_of_pow_eq_one hnpos ((root_pow_eq_one_iff f _).mpr hndvd)
  · apply hleast.2
    exact ⟨Nat.pos_of_dvd_of_pos ((order_dvd_iff f _).mpr hndvd) hnpos,
      (order_dvd_iff f _).mp dvd_rfl⟩

end D07.Ch20.PolynomialOrderRepeatedFactorOrder
