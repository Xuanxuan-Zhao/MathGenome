import MathGenome.Internal.Specs.D07.Ch12.PrimitiveElementInseparableNonsimpleExample
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D07.Ch12.PrimitiveElementInseparableNonsimpleExample

noncomputable section
open Specs.D07.Ch12.PrimitiveElementInseparableNonsimpleExample
open MvPolynomial

variable (p : ℕ) [Fact p.Prime]

private theorem prime_pos : 0 < p := (Fact.out : p.Prime).pos

/-- Independence follows from the injective polynomial-to-fraction map;
the fraction presentation proves field generation. -/
theorem rational_function_model : RationalFunctionModel := by
  intro p _
  constructor
  · exact ((IsScalarTower.toAlgHom (ZMod p) (P p) (E p)).algebraicIndependent_iff
      (IsFractionRing.injective (P p) (E p))).mpr
        (MvPolynomial.algebraicIndependent_X _ _)
  · let L := IntermediateField.adjoin (ZMod p) (Set.range (indeterminate p))
    have hpoly (f : P p) : algebraMap (P p) (E p) f ∈ L := by
      induction f using MvPolynomial.induction_on with
      | C c =>
        change algebraMap (P p) (E p) (algebraMap (ZMod p) (P p) c) ∈ L
        rw [← IsScalarTower.algebraMap_apply]
        exact L.algebraMap_mem c
      | add a b ha hb => simpa only [map_add] using L.add_mem ha hb
      | mul_X a i ha =>
        rw [map_mul]
        exact L.mul_mem ha (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
    apply top_unique
    intro x hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (P p) x
    exact L.div_mem (hpoly a) (hpoly b)

private theorem constant_mem (c : ZMod p) : algebraMap (ZMod p) (E p) c ∈ K p :=
  Subfield.subset_closure (Or.inl ⟨c, rfl⟩)

private theorem variable_pow_mem (i : Fin 2) : indeterminate p i ^ p ∈ K p := by
  fin_cases i <;> apply Subfield.subset_closure <;> simp

private theorem expand_eq_pow (f : P p) : expand p f = f ^ p := by
  simpa only [ZMod.card] using FiniteField.MvPolynomial.expand_card f

private theorem polynomial_pow_mem (f : P p) :
    algebraMap (P p) (E p) f ^ p ∈ K p := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    change (algebraMap (P p) (E p)) ((algebraMap (ZMod p) (P p)) c) ^ p ∈ K p
    rw [← IsScalarTower.algebraMap_apply]
    exact (K p).pow_mem (constant_mem p c) p
  | add a b ha hb => simpa only [map_add, add_pow_char] using (K p).add_mem ha hb
  | mul_X f i hf =>
    simpa only [map_mul, mul_pow, indeterminate] using (K p).mul_mem hf (variable_pow_mem p i)

theorem powers_in_base : PowersInBase := by
  intro p _ x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (P p) x
  rw [div_pow]
  exact (K p).div_mem (polynomial_pow_mem p a) (polynomial_pow_mem p b)

private theorem base_le_powers : K p ≤ (frobenius (E p) p).fieldRange := by
  apply Subfield.closure_le.mpr
  rintro x (⟨c, rfl⟩ | hx)
  · refine ⟨algebraMap (ZMod p) (E p) c, ?_⟩
    simp only [frobenius_def, ← map_pow]
    rw [ZMod.pow_card]

  · rcases hx with rfl | hx
    · exact ⟨indeterminate p 0, rfl⟩
    · rcases hx with rfl | hx
      · exact ⟨indeterminate p 1, rfl⟩

/-- The exponent vector corresponding to one residue class modulo p. -/
private def residue (ij : Fin p × Fin p) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val

omit [Fact p.Prime] in
private theorem residue_lt (ij : Fin p × Fin p) (k : Fin 2) : residue p ij k < p := by
  fin_cases k <;> simp [residue]

omit [Fact p.Prime] in
private theorem residue_injective : Function.Injective (residue p) := by
  intro i j h
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  simp [residue] at h0 h1
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

omit [Fact p.Prime] in
/-- Two exponent vectors in distinct residue classes cannot coincide. -/
private theorem residue_unique (i j : Fin p × Fin p) (n d : Fin 2 →₀ ℕ)
    (h : p • n + residue p i = p • d + residue p j) : i = j := by
  apply residue_injective p
  ext k
  have hk := congrArg (fun a : Fin 2 →₀ ℕ => a k % p) h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt (residue_lt p i k),
    Nat.mod_eq_of_lt (residue_lt p j k)] using hk

private theorem coefficient_residue (a : Fin p × Fin p → P p)
    (i : Fin p × Fin p) (n : Fin 2 →₀ ℕ) :
    (∑ j, expand p (a j) * monomial (residue p j) 1).coeff
      (p • n + residue p i) = (a i).coeff n := by
  classical
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [coeff_mul_monomial, mul_one, coeff_expand_smul p (prime_pos p).ne']
  · intro j hj hji
    rw [coeff_mul_monomial']
    split_ifs with hle
    · rw [mul_one]
      by_contra hn
      have hd (k : Fin 2) : p ∣ (p • n + residue p i - residue p j) k := by
        by_contra h
        exact hn (coeff_expand_of_not_dvd (a j) h)
      let d : Fin 2 →₀ ℕ := Finsupp.mapRange (fun k => k / p) (Nat.zero_div p)
        (p • n + residue p i - residue p j)
      have heq : p • n + residue p i = p • d + residue p j := by
        ext k
        have hk := congrArg (fun a : Fin 2 →₀ ℕ => a k) (tsub_add_cancel_of_le hle)
        have hkdiv : p * d k = (p • n + residue p i - residue p j) k := by
          change p * ((p • n + residue p i - residue p j) k / p) = _
          exact Nat.mul_div_cancel' (hd k)
        simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hkdiv] using hk.symm
      exact hji (residue_unique p i j n d heq).symm
    · rfl
  · simp

private theorem map_residue (ij : Fin p × Fin p) :
    algebraMap (P p) (E p) (monomial (residue p ij) 1) = monomials p ij := by
  simp [residue, monomial_add_single, ← X_pow_eq_monomial, monomials, indeterminate]

/-- Clearing denominators reduces independence over K to disjoint polynomial
exponent classes. No separability is used. -/
theorem monomials_linearIndependent : LinearIndependent (K p) (monomials p) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hroot (j : Fin p × Fin p) : ∃ d : E p, d ^ p = (c j : E p) :=
    base_le_powers p (c j).property
  choose d hd using hroot
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (P p)) d
  choose a ha using hq
  have ha' (j : Fin p × Fin p) :
      algebraMap (P p) (E p) (a j) = algebraMap (P p) (E p) q * d j := by
    simpa only [Algebra.smul_def] using ha j
  have hpzero : (∑ j, expand p (a j) * monomial (residue p j) 1) = 0 := by
    apply IsFractionRing.injective (P p) (E p)
    rw [map_zero, map_sum]
    simp_rw [map_mul, expand_eq_pow, map_pow, ha', mul_pow, hd, map_residue]
    have hc' : ∑ j, (c j : E p) * monomials p j = 0 := by
      change (∑ j, (c j : E p) * monomials p j) = 0 at hc
      exact hc
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc', mul_zero]
  have hai : a i = 0 := by
    ext n
    have hh := congrArg (fun f : P p => f.coeff (p • n + residue p i)) hpzero
    rw [coefficient_residue] at hh
    simpa using hh
  have hdi : d i = 0 := by
    have hqne : algebraMap (P p) (E p) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.property
    have hz := ha' i
    rw [hai, map_zero] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left hqne
  apply Subtype.ext
  change (c i : E p) = 0
  simpa only [hdi, zero_pow (prime_pos p).ne'] using (hd i).symm

private theorem exponent_two (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext k
  fin_cases k <;> simp

private theorem map_monomial_two (d : Fin 2 →₀ ℕ) (c : ZMod p) :
    algebraMap (P p) (E p) (monomial d c) =
      algebraMap (ZMod p) (E p) c * indeterminate p 0 ^ d 0 * indeterminate p 1 ^ d 1 := by
  conv_lhs => rw [exponent_two d, monomial_add_single, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, indeterminate]
  rw [show algebraMap (P p) (E p) (C c) = algebraMap (ZMod p) (E p) c from
    (IsScalarTower.algebraMap_apply (ZMod p) (P p) (E p) c).symm]

private theorem polynomial_mem_span (f : P p) :
    algebraMap (P p) (E p) f ∈ Submodule.span (K p) (Set.range (monomials p)) := by
  let W := Submodule.span (K p) (Set.range (monomials p))
  have hmono (d : Fin 2 →₀ ℕ) (c : ZMod p) :
      algebraMap (P p) (E p) (monomial d c) ∈ W := by
    let r : Fin p × Fin p :=
      (⟨d 0 % p, Nat.mod_lt _ (prime_pos p)⟩, ⟨d 1 % p, Nat.mod_lt _ (prime_pos p)⟩)
    let k : K p := ⟨algebraMap (ZMod p) (E p) c *
        (indeterminate p 0 ^ p) ^ (d 0 / p) * (indeterminate p 1 ^ p) ^ (d 1 / p),
      (K p).mul_mem ((K p).mul_mem (constant_mem p c)
        ((K p).pow_mem (variable_pow_mem p 0) _))
        ((K p).pow_mem (variable_pow_mem p 1) _)⟩
    have hpow (x : E p) (n : ℕ) : (x ^ p) ^ (n / p) * x ^ (n % p) = x ^ n := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have heq : algebraMap (P p) (E p) (monomial d c) = k • monomials p r := by
      rw [map_monomial_two, Algebra.smul_def]
      change _ = (algebraMap (ZMod p) (E p) c *
        (indeterminate p 0 ^ p) ^ (d 0 / p) * (indeterminate p 1 ^ p) ^ (d 1 / p)) *
        (indeterminate p 0 ^ (d 0 % p) * indeterminate p 1 ^ (d 1 % p))
      calc
        _ = algebraMap (ZMod p) (E p) c *
            ((indeterminate p 0 ^ p) ^ (d 0 / p) * indeterminate p 0 ^ (d 0 % p)) *
            ((indeterminate p 1 ^ p) ^ (d 1 / p) * indeterminate p 1 ^ (d 1 % p)) := by
              rw [hpow, hpow]
        _ = _ := by ring
    rw [heq]
    exact W.smul_mem k (Submodule.subset_span (Set.mem_range_self r))
  induction f using MvPolynomial.induction_on' with
  | monomial d c => exact hmono d c
  | add a b ha hb => simpa only [map_add] using W.add_mem ha hb

theorem monomials_span : Submodule.span (K p) (Set.range (monomials p)) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (P p) x
  have hbne : algebraMap (P p) (E p) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  let k : K p := ⟨(algebraMap (P p) (E p) b ^ p)⁻¹,
    (K p).inv_mem (polynomial_pow_mem p b)⟩
  have hmem := (Submodule.span (K p) (Set.range (monomials p))).smul_mem k
    (polynomial_mem_span p (a * b ^ (p - 1)))
  have heq : k • algebraMap (P p) (E p) (a * b ^ (p - 1)) =
      algebraMap (P p) (E p) a / algebraMap (P p) (E p) b := by
    simp only [Algebra.smul_def, map_mul, map_pow]
    change (algebraMap (P p) (E p) b ^ p)⁻¹ *
      (algebraMap (P p) (E p) a * algebraMap (P p) (E p) b ^ (p - 1)) = _
    rw [← pow_sub_one_mul (prime_pos p).ne' (algebraMap (P p) (E p) b)]
    field_simp
  rwa [heq] at hmem

/-- The basis is exactly the family specified in the source. -/
theorem monomial_basis : MonomialBasis := by
  intro p _
  exact ⟨Module.Basis.mk (monomials_linearIndependent p) (by rw [monomials_span]),
    fun _ => Module.Basis.mk_apply _ _ _⟩

private noncomputable def basis : Module.Basis (Fin p × Fin p) (K p) (E p) :=
  (monomial_basis p).choose

theorem degree_and_algebraicity : DegreeAndAlgebraicity := by
  intro p _
  let : FiniteDimensional (K p) (E p) := Module.Finite.of_basis (basis p)
  have hfin : Module.finrank (K p) (E p) = p ^ 2 := by
    simpa [pow_two] using Module.finrank_eq_card_basis (basis p)
  refine ⟨inferInstance, Algebra.IsAlgebraic.of_finite (K p) (E p), hfin, ?_⟩
  rw [← Module.finrank_eq_rank, hfin]

private theorem integral_element (x : E p) : IsIntegral (K p) x := by
  let a : K p := ⟨x ^ p, powers_in_base p x⟩
  refine ⟨Polynomial.X ^ p - Polynomial.C a,
    Polynomial.monic_X_pow_sub_C a (prime_pos p).ne', ?_⟩
  change Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C a) = 0
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  exact sub_self _

theorem simple_degree_bound : SimpleDegreeBound := by
  intro p _ x
  have hx := integral_element p x
  refine ⟨IntermediateField.adjoin.finiteDimensional hx, ?_⟩
  rw [IntermediateField.adjoin.finrank hx]
  let a : K p := ⟨x ^ p, powers_in_base p x⟩
  have hm := minpoly.min (K p) x
    (Polynomial.monic_X_pow_sub_C a (prime_pos p).ne')
    (show Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C a) = 0 by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      exact sub_self _)
  exact (Polynomial.natDegree_le_natDegree hm).trans (by simp)

theorem not_simple : NotSimple := by
  intro p _ h
  obtain ⟨x, hx⟩ := h
  have hbound := (simple_degree_bound p x).2
  have heq : Module.finrank (K p) (IntermediateField.adjoin (K p) {x}) =
      Module.finrank (K p) (E p) := by
    rw [hx]
    exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq
  rw [heq, (degree_and_algebraicity p).2.2.1] at hbound
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  nlinarith

end
end D07.Ch12.PrimitiveElementInseparableNonsimpleExample
