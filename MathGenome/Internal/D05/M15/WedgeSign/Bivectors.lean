import MathGenome.Internal.Specs.D05.M15.WedgeSign.Bivectors
import MathGenome.Internal.D05.M15.WedgeSign.BivectorNormalForm
import MathGenome.Internal.D05.M15.ExteriorBasis
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

noncomputable section
namespace D05.M15.WedgeSign.Bivectors
open Module
open Specs.D05.M15.WedgeSign.BivectorNormalForm
open Specs.D05.M15.WedgeSign.Bivectors
open scoped BigOperators
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

private lemma wedge_zero : wedge (K := K) (0 : V) 0 = 0 := by
  exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![0, 0]
    (i := 0) (j := 1) rfl (by decide)

theorem decomposable_iff_rank : Specs.D05.M15.WedgeSign.Bivectors.decomposable_iff_rank := by
  intro K V _ _ _ _ z
  constructor
  · rintro ⟨u, v, rfl⟩
    exact BivectorNormalForm.decomposable_rank_le_two u v
  · intro h
    obtain ⟨r, u, v, hi, he, hr, hm⟩ := BivectorNormalForm.normal_form z
    have : r ≤ 1 := by omega
    interval_cases r
    · refine ⟨0, 0, ?_⟩
      simpa [wedge_zero] using he
    · exact ⟨u 0, v 0, by simpa using he⟩

theorem decomposable_iff_matrix_rank :
    Specs.D05.M15.WedgeSign.Bivectors.decomposable_iff_matrix_rank := by
  intro K V _ _ _ n b z
  have := Module.Finite.of_basis b
  rw [BivectorNormalForm.matrix_rank]
  exact decomposable_iff_rank z

theorem nonzero_iff_rank_two : Specs.D05.M15.WedgeSign.Bivectors.nonzero_iff_rank_two := by
  intro K V _ _ _ _ z hz
  constructor
  · rintro ⟨u, v, rfl⟩
    exact BivectorNormalForm.nonzero_decomposable_rank u v hz
  · intro h
    exact (decomposable_iff_rank z).mpr (by omega)

lemma wedge_coe (u v : V) :
    (wedge (K := K) u v : ExteriorAlgebra K V) = ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  simp [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]

lemma elementary_square_zero (u v : V) : square (wedge (K := K) u v) = 0 := by
  change (wedge (K := K) u v : ExteriorAlgebra K V) * (wedge (K := K) u v) = 0
  simp only [wedge_coe]
  calc
    _ = ExteriorAlgebra.ι K u * (ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u) *
        ExteriorAlgebra.ι K v := by simp only [mul_assoc]
    _ = 0 := by
      have hs : ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u =
        -(ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)
      rw [hs]; simp [← mul_assoc]

lemma elementary_commute (u v x y : V) :
    (wedge (K := K) u v : ExteriorAlgebra K V) * (wedge (K := K) x y) =
      (wedge (K := K) x y : ExteriorAlgebra K V) * (wedge (K := K) u v) := by
  have hp : (-1 : K) ^ (2 * 2) = 1 := by ring
  simpa only [wedge, exteriorPower.ιMulti_apply_coe, hp, one_smul] using
    D05.M15.WedgeSign.elementary_sign (K := K) 2 2 ![u, v] ![x, y]

theorem square_normal_sum : Specs.D05.M15.WedgeSign.Bivectors.square_normal_sum := by
  intro K V _ _ _ r u v
  classical
  let f : Fin r → ExteriorAlgebra K V := fun i => wedge (K := K) (u i) (v i)
  change (↑(∑ i, wedge (K := K) (u i) (v i)) : ExteriorAlgebra K V) *
      (↑(∑ i, wedge (K := K) (u i) (v i)) : ExteriorAlgebra K V) = _
  simp only [Submodule.coe_sum]
  change (∑ i, f i) * (∑ i, f i) = (2 : K) • ∑ i, ∑ j ∈ _ , f i * f j
  rw [Finset.sum_mul_sum]
  have ht (i j : Fin r) : f i * f j =
      (if i < j then f i * f j else 0) + (if j < i then f j * f i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simpa only [f, square, lt_self_iff_false, ite_false, zero_add] using elementary_square_zero (K := K) (u i) (v i)
    · simp only [h, not_lt_of_ge h.le, ite_true, ite_false, zero_add]
      exact elementary_commute _ _ _ _
  trans ∑ i, ∑ j, ((if i < j then f i * f j else 0) +
    (if j < i then f j * f i else 0))
  · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ht i j))
  simp only [Finset.sum_add_distrib]
  have hs : (∑ i, ∑ j, if j < i then f j * f i else 0) =
      ∑ i, ∑ j, if i < j then f i * f j else 0 := Finset.sum_comm
  rw [hs, ← two_smul K]
  congr 1
  simp only [Finset.sum_filter]

theorem skew_iff_alternating : Specs.D05.M15.WedgeSign.Bivectors.skew_iff_alternating := by
  intro K V _ _ _ b hb h2
  ext T
  change (∀ x y, b (T x) y = -b x (T y)) ↔ ∀ x, b (T x) x = 0
  constructor
  · intro h x
    have hs := h x x
    rw [← hb.eq (T x) x] at hs
    have he : (2 : K) * b (T x) x = 0 := by
      rw [two_mul, ← neg_eq_iff_add_eq_zero.mp hs.symm]
    exact (mul_eq_zero.mp he).resolve_left h2
  · intro h x y
    have he := h (x + y)
    simp only [map_add, LinearMap.add_apply, h x, h y, zero_add, add_zero] at he
    rw [hb.eq (T y) x] at he
    exact eq_neg_of_add_eq_zero_right he

/-- Alternating bilinear forms on the dual are represented by actual bivectors.
This is the flipped perfect exterior pairing, followed by the alternating
universal property. -/
lemma form_surjective [FiniteDimensional K V]
    (B : LinearMap.BilinForm K (Dual K V)) (hB : B.IsAlt) :
    ∃ z : ⋀[K]^2 V, form z = B := by
  let A : AlternatingMap K (Dual K V) K (Fin 2) :=
    { toFun := fun f => B (f 0) (f 1)
      map_update_add' := by intro _ f i x y; fin_cases i <;> simp [map_add]
      map_update_smul' := by intro _ f i c x; fin_cases i <;> simp [map_smul]
      map_eq_zero_of_eq' := by
        intro f i j he hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change f 0 = f 1 at he
          rw [he]; exact hB (f 1)
        · change f 1 = f 0 at he
          rw [← he]; exact hB (f 1)
        · exact (hij rfl).elim }
  let L := exteriorPower.alternatingMapLinearEquiv A
  obtain ⟨e, he⟩ := D05.M15.ExteriorPairing.perfect (K := K) (V := V) 2
  change e.toLinearMap = exteriorPower.pairingDual K V 2 at he
  have hp : (exteriorPower.pairingDual K V 2).IsPerfPair :=
    LinearMap.IsPerfPair.of_bijective _ (by rw [← he]; exact e.bijective)
  let := hp
  obtain ⟨z, hz⟩ := (LinearMap.IsPerfPair.bijective_right
    (exteriorPower.pairingDual K V 2)).surjective L
  refine ⟨z, ?_⟩
  ext phi psi
  have hh := LinearMap.congr_fun hz (wedge phi psi)
  change exteriorPower.pairingDual K V 2 (wedge phi psi) z = _ at hh
  rw [wedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at hh
  exact hh

/-- The bivector-to-form construction is linear in the bivector. -/
def formLinear : (⋀[K]^2 V) →ₗ[K] LinearMap.BilinForm K (Dual K V) where
  toFun := form
  map_add' z t := by ext phi psi; simp [BivectorNormalForm.form_apply]
  map_smul' a z := by ext phi psi; simp [BivectorNormalForm.form_apply]

/-- Recover an operator from its bilinear form using the inverse metric map. -/
def metricOperator (e : V ≃ₗ[K] Dual K V) : (⋀[K]^2 V) →ₗ[K] (V →ₗ[K] V) where
  toFun z := e.symm.toLinearMap.comp ((form z).compl₁₂ e.toLinearMap e.toLinearMap)
  map_add' z t := by
    ext x
    apply e.injective
    ext y
    simp [BivectorNormalForm.form_apply]
  map_smul' a z := by
    ext x
    apply e.injective
    ext y
    simp [BivectorNormalForm.form_apply]

@[simp] lemma metricOperator_form (e : V ≃ₗ[K] Dual K V) (z : ⋀[K]^2 V) (x y : V) :
    e (metricOperator e z x) y = form z (e x) (e y) := by
  simp [metricOperator]

theorem alternating_operator_bridge :
    Specs.D05.M15.WedgeSign.Bivectors.alternating_operator_bridge := by
  intro K V _ _ _ _ b hb hn
  classical
  have hi : Function.Injective b := LinearMap.ker_eq_bot.mp
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp hn.1)
  have hs : Function.Surjective b :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hi
  let e : V ≃ₗ[K] Dual K V := LinearEquiv.ofBijective b ⟨hi, hs⟩
  have he (x : V) : e x = b x := rfl
  let P : (⋀[K]^2 V) →ₗ[K] alternatingOperators b :=
    (metricOperator e).codRestrict (alternatingOperators b) (fun z x => by
      change b (metricOperator e z x) x = 0
      rw [← he, metricOperator_form]
      exact BivectorNormalForm.alternating z (e x))
  have hP (z : ⋀[K]^2 V) (x y : V) : b ((P z).val x) y = form z (b x) (b y) := by
    exact metricOperator_form e z x y
  have hPi : Function.Injective P := by
    intro z t h
    apply BivectorNormalForm.ext_pairing
    intro phi psi
    obtain ⟨x, rfl⟩ := hs phi
    obtain ⟨y, rfl⟩ := hs psi
    rw [← hP, ← hP, h]
  have hPs : Function.Surjective P := by
    intro T
    let B : LinearMap.BilinForm K (Dual K V) :=
      (LinearMap.comp b T.val).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
    have hB : B.IsAlt := fun phi => T.prop (e.symm phi)
    obtain ⟨z, hz⟩ := form_surjective B hB
    refine ⟨z, ?_⟩
    apply Subtype.ext
    ext x
    apply hi
    ext y
    rw [hP, hz]
    change b (T.val (e.symm (e x))) (e.symm (e y)) = b (T.val x) y
    rw [e.symm_apply_apply, e.symm_apply_apply]
  let E : (⋀[K]^2 V) ≃ₗ[K] alternatingOperators b := LinearEquiv.ofBijective P ⟨hPi, hPs⟩
  refine ⟨E, ?_, hP⟩
  intro u v x
  apply hi
  ext y
  change b ((P (wedge u v)).val x) y = _
  rw [hP, BivectorNormalForm.elementary]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hb.eq x u, hb.eq y v, hb.eq x v, hb.eq y u]

theorem skew_operator_bridge : Specs.D05.M15.WedgeSign.Bivectors.skew_operator_bridge := by
  intro K V _ _ _ _ b hb hn h2
  obtain ⟨E, hE, hF⟩ := alternating_operator_bridge b hb hn
  let e := LinearEquiv.ofEq (alternatingOperators b) (skewOperators b)
    (skew_iff_alternating b hb h2).symm
  exact ⟨E.trans e, hE, hF⟩

theorem skew_dimension : Specs.D05.M15.WedgeSign.Bivectors.skew_dimension := by
  intro K V _ _ _ _ b hb hn h2
  obtain ⟨E, _, _⟩ := skew_operator_bridge b hb hn h2
  rw [← E.finrank_eq]
  exact D05.M15.ExteriorBasis.dimension 2

theorem square_characteristic_two :
    Specs.D05.M15.WedgeSign.Bivectors.square_characteristic_two := by
  intro K V _ _ _ _ h2 z
  obtain ⟨r, u, v, _, he, _, _⟩ := BivectorNormalForm.normal_form z
  rw [he, square_normal_sum, h2, zero_smul]

/-- Extend the coefficient maps of an independent family to the whole space. -/
lemma independent_dual {I : Type*} [DecidableEq I] (f : I → V) (hi : LinearIndependent K f) :
    ∃ d : I → Dual K V, ∀ i j, d i (f j) = if i = j then 1 else 0 := by
  classical
  let F := Finsupp.linearCombination K f
  have hF : LinearMap.ker F = ⊥ := linearIndependent_iff_ker.mp hi
  obtain ⟨g, hg⟩ := F.exists_leftInverse_of_injective hF
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have he := LinearMap.congr_fun hg (Finsupp.single j 1)
  simp only [LinearMap.comp_apply, F, Finsupp.linearCombination_single, one_smul,
    LinearMap.id_apply] at he
  simp only [LinearMap.comp_apply, he, Finsupp.lapply_apply, Finsupp.single_apply,
    eq_comm]

lemma product_four (u v x y : V) :
    exteriorPower.wedge K V 2 2 (wedge (K := K) u v) (wedge x y) =
      exteriorPower.ιMulti K 4 ![u, v, x, y] := by
  apply Subtype.ext
  change (wedge (K := K) u v : ExteriorAlgebra K V) * (wedge (K := K) x y) =
    (exteriorPower.ιMulti K 4 ![u, v, x, y] : ExteriorAlgebra K V)
  simp only [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  ext i; fin_cases i <;> rfl

lemma square_normal_sum_power (r : ℕ) (u v : Fin r → V) :
    exteriorPower.wedge K V 2 2 (∑ i, wedge (u i) (v i)) (∑ i, wedge (u i) (v i)) =
      (2 : K) • ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        exteriorPower.ιMulti K 4 ![u i, v i, u j, v j] := by
  apply Subtype.ext
  change square (∑ i, wedge (u i) (v i)) = _
  rw [square_normal_sum]
  simp only [SetLike.val_smul, Submodule.coe_sum, ← product_four]
  rfl

/-- A degree-four coordinate isolates the first two normal blocks.
Its value on their square is exactly the scalar 2. -/
lemma normal_square_detects_two {r : ℕ} (u v : Fin r → V)
    (hi : LinearIndependent K (fun ij : Fin r × Fin 2 =>
      if ij.2 = 0 then u ij.1 else v ij.1)) (hr : 2 ≤ r)
    (hz : square (∑ i, wedge (K := K) (u i) (v i)) = 0) : (2 : K) = 0 := by
  classical
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  have h01 : i0 < i1 := by change (0 : ℕ) < 1; omega
  have hn : i0 ≠ i1 := ne_of_lt h01
  obtain ⟨d, hd⟩ := independent_dual _ hi
  have hdU (i : Fin r) (s : Fin 2) (j : Fin r) :
      d (i, s) (u j) = if i = j ∧ s = 0 then 1 else 0 := by
    simpa using hd (i, s) (j, 0)
  have hdV (i : Fin r) (s : Fin 2) (j : Fin r) :
      d (i, s) (v j) = if i = j ∧ s = 1 then 1 else 0 := by
    simpa using hd (i, s) (j, 1)
  let ds : Fin 4 → Dual K V := ![d (i0, 0), d (i0, 1), d (i1, 0), d (i1, 1)]
  let L : (⋀[K]^4 V) →ₗ[K] K :=
    exteriorPower.pairingDual K V 4 (exteriorPower.ιMulti K 4 ds)
  have hL (k l : Fin r) (hkl : k < l) :
      L (exteriorPower.ιMulti K 4 ![u k, v k, u l, v l]) =
        if k = i0 ∧ l = i1 then 1 else 0 := by
    change D05.M15.ExteriorPairing.pairing K V 4
      (exteriorPower.ιMulti K 4 ds) (exteriorPower.ιMulti K 4 ![u k, v k, u l, v l]) = _
    rw [D05.M15.ExteriorPairing.elementary]
    by_cases hk : k = i0
    · subst k
      by_cases hl : l = i1
      · subst l
        rw [ite_eq_left ⟨rfl, rfl⟩]
        have hm : (fun a b : Fin 4 => ds a (![u i0, v i0, u i1, v i1] b)) =
            (1 : Matrix (Fin 4) (Fin 4) K) := by
          ext a b; fin_cases a <;> fin_cases b <;>
            simp [ds, hdU, hdV, hn, hn.symm]
        rw [hm, Matrix.det_one]
      · rw [ite_eq_right (by simp [hl])]
        apply Matrix.det_eq_zero_of_column_eq_zero 2
        intro a
        have hl0 : i0 ≠ l := ne_of_lt hkl
        fin_cases a <;> simp [ds, hdU, hl0, Ne.symm hl]
    · rw [ite_eq_right (by simp [hk])]
      by_cases hk1 : k = i1
      · subst k
        apply Matrix.det_eq_zero_of_column_eq_zero 2
        intro a
        have hl1 : i1 ≠ l := ne_of_lt hkl
        have hl0 : i0 ≠ l := ne_of_lt (h01.trans hkl)
        fin_cases a <;> simp [ds, hdU, hl0, hl1]
      · apply Matrix.det_eq_zero_of_column_eq_zero 0
        intro a
        fin_cases a <;> simp [ds, hdU, Ne.symm hk, Ne.symm hk1]
  have hz' : exteriorPower.wedge K V 2 2 (∑ i, wedge (u i) (v i))
      (∑ i, wedge (u i) (v i)) = 0 := Subtype.ext hz
  rw [square_normal_sum_power] at hz'
  have he := congrArg L hz'
  simp only [map_smul, map_sum, smul_eq_mul, map_zero] at he
  have hh : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      L (exteriorPower.ιMulti K 4 ![u i, v i, u j, v j])) = 1 := by
    trans ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (if i = i0 ∧ j = i1 then (1 : K) else 0)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact hL i j (Finset.mem_filter.mp hj).2
    · simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp [h01]
  rw [hh, mul_one] at he
  exact he

theorem square_criterion : Specs.D05.M15.WedgeSign.Bivectors.square_criterion := by
  intro K V _ _ _ _ h2 z
  constructor
  · intro hz
    obtain ⟨r, u, v, hi, he, hr, hm⟩ := BivectorNormalForm.normal_form z
    have hsmall : r ≤ 1 := by
      by_contra h
      exact h2 (normal_square_detects_two u v hi (by omega) (he ▸ hz))
    apply (decomposable_iff_rank z).mpr
    omega
  · rintro ⟨u, v, rfl⟩
    exact elementary_square_zero u v

/-- The sum of two disjoint elementary coordinate bivectors has rank four,
in every characteristic. -/
lemma coordinate_two_block_rank (K : Type u) [Field K] :
    let b := Pi.basisFun K (Fin 4)
    let z := wedge (K := K) (b 0) (b 1) + wedge (b 2) (b 3)
    finrank K (LinearMap.range (form z)) = 4 := by
  classical
  dsimp only
  let b := Pi.basisFun K (Fin 4)
  let z := wedge (K := K) (b 0) (b 1) + wedge (b 2) (b 3)
  change finrank K (LinearMap.range (form z)) = 4
  have hf (phi psi : Dual K (Fin 4 → K)) : form z phi psi =
      (phi (b 0) * psi (b 1) - phi (b 1) * psi (b 0)) +
      (phi (b 2) * psi (b 3) - phi (b 3) * psi (b 2)) := by
    have ha : form z = form (wedge (K := K) (b 0) (b 1)) + form (wedge (b 2) (b 3)) :=
      formLinear.map_add _ _
    rw [ha]
    simp only [LinearMap.add_apply]
    rw [BivectorNormalForm.elementary, BivectorNormalForm.elementary]
  have hker : LinearMap.ker (form z) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro phi h
    have he (j : Fin 4) := LinearMap.congr_fun h (b.coord j)
    simp only [hf, LinearMap.zero_apply] at he
    have h0 := he 1
    have h1 := he 0
    have h2 := he 3
    have h3 := he 2
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, sub_zero, zero_sub,
      add_zero, zero_add, neg_eq_zero] at h0 h1 h2 h3
    apply b.ext
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  rw [LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker), Subspace.dual_finrank_eq]
  simp

theorem characteristic_two_counterexample :
    Specs.D05.M15.WedgeSign.Bivectors.characteristic_two_counterexample := by
  intro K _ h2
  let b := Pi.basisFun K (Fin 4)
  let z := wedge (K := K) (b 0) (b 1) + wedge (b 2) (b 3)
  have hr : finrank K (LinearMap.range (form z)) = 4 := coordinate_two_block_rank K
  refine ⟨z, square_characteristic_two h2 z, ?_, hr⟩
  intro hd
  have hh := (decomposable_iff_rank z).mp hd
  omega

theorem characteristic_two_skew_counterexample :
    Specs.D05.M15.WedgeSign.Bivectors.characteristic_two_skew_counterexample := by
  intro K _ h2
  let b : LinearMap.BilinForm K K := LinearMap.mul K K
  have hneg (a : K) : a = -a := by
    apply eq_neg_of_add_eq_zero_left
    rw [← two_mul, h2, zero_mul]
  refine ⟨b, LinearMap.id, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun x y => mul_comm x y⟩
  · constructor
    · intro x hx
      have h := hx 1
      simpa [b] using h
    · intro x hx
      have h := hx 1
      simpa [b] using h
  · intro x y
    change x * y = -(x * y)
    exact hneg _
  · intro h
    have he := h 1
    change 1 * 1 = (0 : K) at he
    simp at he

end D05.M15.WedgeSign.Bivectors
