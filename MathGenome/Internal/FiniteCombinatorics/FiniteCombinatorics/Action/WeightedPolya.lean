import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.WeightedPolya
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.WeightedFixedColorings
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.Burnside
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators

namespace FiniteCombinatorics.Action
attribute [local instance] Classical.propDecidable

/-- The Burnside bijection retains the orbit of the fixed point. -/
theorem sigmaFixedByEquiv_orbit {G Y : Type*} [Group G] [MulAction G Y]
    (p : Σ g : G, MulAction.fixedBy Y g) :
    (MulAction.sigmaFixedByEquivOrbitsProdGroup G Y p).1 =
      Quotient.mk (MulAction.orbitRel G Y) p.2.val := by
  rfl

/-- Weighted Burnside for any function on the orbit quotient, in an additive
commutative monoid. No division or cancellation is needed. -/
theorem sum_fixed_orbit_weight {G Y A : Type*} [Group G] [MulAction G Y]
    [Fintype G] [∀ g : G, Fintype (MulAction.fixedBy Y g)]
    [Fintype (MulAction.orbitRel.Quotient G Y)] [AddCommMonoid A]
    (v : MulAction.orbitRel.Quotient G Y → A) :
    (∑ g : G, ∑ y : MulAction.fixedBy Y g,
      v (Quotient.mk (MulAction.orbitRel G Y) y.val)) =
      Fintype.card G • ∑ O, v O := by
  classical
  calc
    _ = ∑ p : Σ g : G, MulAction.fixedBy Y g,
        v (Quotient.mk (MulAction.orbitRel G Y) p.2.val) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ p : MulAction.orbitRel.Quotient G Y × G, v p.1 := by
      exact Fintype.sum_equiv (MulAction.sigmaFixedByEquivOrbitsProdGroup G Y)
        _ _ (fun p => congrArg v (sigmaFixedByEquiv_orbit p).symm)
    _ = _ := by simp [Fintype.sum_prod_type, Finset.smul_sum]

universe u v w z
variable (G : Type u) (X : Type v) (C : Type w) [Group G] [MulAction G X]
attribute [local instance] coloringAction Classical.propDecidable
variable [Fintype X] [Fintype C]
noncomputable local instance orbitsFintype :
    Fintype (MulAction.orbitRel.Quotient G (X → C)) := Fintype.ofFinite _

noncomputable def orbitEnumerator : MvPolynomial C ℕ :=
  ∑ O : MulAction.orbitRel.Quotient G (X → C), orbitWeight G X C O

noncomputable def colorMultiplicity (f : X → C) : C →₀ ℕ :=
  ∑ x, Finsupp.single (f x) 1

noncomputable def orbitMultiplicity (O : MulAction.orbitRel.Quotient G (X → C)) : C →₀ ℕ :=
  colorMultiplicity X C O.out

noncomputable def substitutedCycleIndex [Fintype G] : MvPolynomial C ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (Fintype.card X) => ∑ c : C, MvPolynomial.X c ^ (i.val + 1))
    (cycleIndex G X)

omit [Fintype C] in
theorem colorMultiplicity_apply (f : X → C) (c : C) :
    colorMultiplicity X C f c = (Finset.univ.filter (fun x => f x = c)).card := by
  classical
  simp [colorMultiplicity, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_boole, eq_comm]

omit [Fintype C] in
theorem colorMultiplicity_smul (g : G) (f : X → C) :
    colorMultiplicity X C (g • f) = colorMultiplicity X C f :=
  Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun x => Finsupp.single (f x) 1)

omit [Fintype C] in
@[simp] theorem orbitMultiplicity_mk (f : X → C) :
    orbitMultiplicity G X C (Quotient.mk (MulAction.orbitRel G (X → C)) f) =
      colorMultiplicity X C f := by
  have h := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel G (X → C)) f))
  obtain ⟨g, hg⟩ := h
  change colorMultiplicity X C _ = _
  rw [← hg, colorMultiplicity_smul]

omit [Fintype C] in
theorem coloringWeight_eq_monomial (f : X → C) :
    coloringWeight X C f = MvPolynomial.monomial (colorMultiplicity X C f) 1 := by
  classical
  simp [coloringWeight, colorMultiplicity, MvPolynomial.monomial_sum_one,
    MvPolynomial.X]

theorem orbitEnumerator_coeff (d : C →₀ ℕ) :
    (orbitEnumerator G X C).coeff d =
      (Finset.univ.filter (fun O : MulAction.orbitRel.Quotient G (X → C) =>
        orbitMultiplicity G X C O = d)).card := by
  classical
  simp [orbitEnumerator, orbitWeight,
    coloringWeight_eq_monomial, MvPolynomial.coeff_monomial, orbitMultiplicity,
    Finset.sum_boole, eq_comm]

/-- Integral weighted Burnside, including nonfaithful actions. -/
theorem integral_weighted_burnside [Fintype G] :
    Fintype.card G • orbitEnumerator G X C = ∑ g : G, fixedWeightSum G X C g := by
  classical
  symm
  calc
    _ = ∑ g : G, ∑ f : MulAction.fixedBy (X → C) g,
        orbitWeight G X C (Quotient.mk (MulAction.orbitRel G (X → C)) f.val) := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [orbitWeight_mk]
      exact Finset.sum_subtype _ (by intro f; simp) _
    _ = _ := sum_fixed_orbit_weight (orbitWeight G X C)

/-- Evaluation of the natural inventory uses only addition and multiplication. -/
theorem orbitEnumerator_specialize (R : Type z) [CommSemiring R] (weights : C → R) :
    MvPolynomial.eval₂ (Nat.castRingHom R) weights (orbitEnumerator G X C) =
      ∑ O : MulAction.orbitRel.Quotient G (X → C), ∏ x : X, weights (O.out x) := by
  classical
  change MvPolynomial.eval₂Hom (Nat.castRingHom R) weights _ = _
  simp [orbitEnumerator, orbitWeight, coloringWeight, map_sum, map_prod]

@[simp] theorem orbitEnumerator_empty_positions [IsEmpty X] :
    orbitEnumerator G X C = 1 := by
  classical
  simp [orbitEnumerator, orbitWeight]

@[simp] theorem orbitEnumerator_empty_colors [Nonempty X] [IsEmpty C] :
    orbitEnumerator G X C = 0 := by
  classical
  simp [orbitEnumerator]

/-- Reindex the positive cycle lengths by the variables of the cycle index. -/
theorem prod_fin_positive {R : Type*} [CommMonoid R] (n : ℕ) (a : ℕ → R) :
    (∏ i : Fin n, a (i.val + 1)) = ∏ k ∈ Finset.Icc 1 n, a k := by
  classical
  apply Finset.prod_bij (fun (i : Fin n) _ => i.val + 1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos _, i.isLt⟩
  · intro i _ j _ h
    exact Fin.ext (Nat.add_right_cancel h)
  · intro k hk
    obtain ⟨h1, hn⟩ := Finset.mem_Icc.mp hk
    exact ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by change k - 1 + 1 = k; omega⟩
  · intro i _
    rfl

/-- Substitution in one group element's monomial gives its fixed-coloring sum. -/
theorem elementMonomial_substitute (g : G) :
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin (Fintype.card X) => ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ (i.val + 1))
      (elementMonomial G X g) =
    MvPolynomial.map (Nat.castRingHom ℚ) (fixedWeightSum G X C g) := by
  classical
  rw [fixedWeightSum_factorization]
  simp only [elementMonomial, permutationMonomial, map_prod, map_pow, map_sum,
    MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]
  exact prod_fin_positive (Fintype.card X)
    (fun k => (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k) ^ countCycles G X g k)

/-- The rational substitution is the rational image of the natural inventory. -/
theorem weighted_polya [Fintype G] :
    MvPolynomial.map (Nat.castRingHom ℚ) (orbitEnumerator G X C) =
      substitutedCycleIndex G X C := by
  classical
  have h := congrArg (MvPolynomial.map (Nat.castRingHom ℚ))
    (integral_weighted_burnside G X C)
  simp only [map_nsmul, map_sum] at h
  have hc : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold substitutedCycleIndex cycleIndex
  rw [MvPolynomial.eval₂Hom_smul, map_sum]
  simp_rw [elementMonomial_substitute]
  rw [← h, smul_eq_mul, MvPolynomial.C_mul']
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Each rational coefficient is the number of orbits of that multiplicity. -/
theorem substitutedCycleIndex_coeff [Fintype G] (d : C →₀ ℕ) :
    (substitutedCycleIndex G X C).coeff d =
      ((Finset.univ.filter (fun O : MulAction.orbitRel.Quotient G (X → C) =>
        orbitMultiplicity G X C O = d)).card : ℚ) := by
  rw [← weighted_polya, MvPolynomial.coeff_map, orbitEnumerator_coeff]
  rfl

end FiniteCombinatorics.Action
