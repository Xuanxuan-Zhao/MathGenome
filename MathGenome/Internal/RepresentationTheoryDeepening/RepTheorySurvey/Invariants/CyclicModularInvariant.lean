import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.CyclicModularInvariant
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace RepTheorySurvey.Invariants.CyclicModularInvariant

open Polynomial
open Specs.CyclicModularInvariant (Bivariate x y generator parameter generated)

universe u

noncomputable section

abbrev action (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p] :
    GroupAlgebraAction k (Multiplicative (ZMod p)) (Bivariate k) :=
  Specs.CyclicModularInvariant.action k p
abbrev norm := @Specs.CyclicModularInvariant.norm

variable (k : Type u) [Field k] (p : ℕ)

private theorem action_apply [CharP k p] [NeZero p] (g : Multiplicative (ZMod p)) (f : Bivariate k) :
    action k p g f = taylor (parameter k p g) f := rfl

theorem generator_coordinates [CharP k p] [NeZero p] :
    action k p (generator p) (x k) = x k ∧ action k p (generator p) (y k) = y k + x k := by
  constructor
  · simp [action_apply]
  · simp [action_apply, parameter]

theorem group_cardinality [NeZero p] : Fintype.card (Multiplicative (ZMod p)) = p := by
  rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]

theorem generator_order [CharP k p] [NeZero p] : orderOf (action k p (generator p)) = p := by
  have hinj : Function.Injective (action k p) := by
    intro g h he
    have hy := DFunLike.congr_fun he (y k)
    rw [action_apply, action_apply, taylor_X, taylor_X, add_right_inj] at hy
    have ha := C_injective hy
    have hc := congrArg (fun f : Polynomial k => f.coeff 1) ha
    simp only [parameter, coeff_C_mul_X] at hc
    exact Multiplicative.toAdd.injective (ZMod.castHom_injective k hc)
  rw [orderOf_injective _ hinj, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private theorem x_mem_fixed [CharP k p] [NeZero p] : x k ∈ (action k p).fixedSubalgebra := by
  change ∀ g, action k p g (x k) = x k
  intro g
  simp [action_apply]

private theorem norm_monic [Fact p.Prime] : (norm k p).Monic := by
  have hp := (Fact.out : p.Prime).one_lt
  apply (monic_X_pow p).sub_of_left
  apply degree_lt_degree
  change natDegree (C (X : Polynomial k) ^ (p - 1) * X) <
    natDegree ((X : Bivariate k) ^ p)
  rwa [← C_pow, natDegree_C_mul_X _ (pow_ne_zero _ X_ne_zero), natDegree_X_pow]

private theorem norm_natDegree [Fact p.Prime] : (norm k p).natDegree = p := by
  have hp := (Fact.out : p.Prime).one_lt
  change natDegree ((y k) ^ p - (x k) ^ (p - 1) * y k) = p
  rw [sub_eq_add_neg,
    natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · change natDegree (-(C (X : Polynomial k) ^ (p - 1) * X)) < natDegree ((X : Bivariate k) ^ p)
    rw [natDegree_neg, ← C_pow, natDegree_C_mul_X _ (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
    exact hp

theorem norm_fixed [CharP k p] [NeZero p] : norm k p ∈ (action k p).fixedSubalgebra := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos (R := k) p
  change ∀ g, action k p g (norm k p) = norm k p
  intro g
  let a : ZMod p := g.toAdd
  let ι : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hpow : (ι a) ^ p = ι a := by rw [← map_pow, ZMod.pow_card]
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le
  have hpar : C (parameter k p g) = C (C (ι a)) * x k := by simp [parameter, ι, a]
  have hparpow : C (parameter k p g) ^ p = x k ^ (p - 1) * C (parameter k p g) := by
    rw [hpar, mul_pow, ← C_pow, ← C_pow, hpow]
    calc
      C (C (ι a)) * x k ^ p = C (C (ι a)) * (x k ^ (p - 1) * x k) := by
        rw [← pow_succ, hp]
      _ = x k ^ (p - 1) * (C (C (ι a)) * x k) := by ac_rfl
  change action k p g (y k ^ p - x k ^ (p - 1) * y k) =
    y k ^ p - x k ^ (p - 1) * y k
  rw [map_sub, map_mul, map_pow, map_pow,
    show action k p g (x k) = x k from x_mem_fixed k p g,
    show action k p g (y k) = y k + C (parameter k p g) from by simp [action_apply],
    add_pow_char, hparpow]
  ring

private theorem generator_apply [CharP k p] [NeZero p] (f : Bivariate k) :
    action k p (generator p) f = taylor (X : Polynomial k) f := by
  simp [action_apply, parameter]

/-- The coefficient just below the leading term changes by the linear term of the binomial
expansion of the leading monomial. -/
private theorem coeff_taylor_below_top {R : Type*} [CommRing R] (a : R)
    (f : Polynomial R) (n : ℕ) (hn : f.natDegree = n + 1) :
    (taylor a f).coeff n = f.coeff n + (n + 1 : ℕ) * f.coeff (n + 1) * a := by
  have hd := natDegree_hasseDeriv_le f n
  rw [hn, Nat.add_sub_cancel_left] at hd
  rw [taylor_coeff, eval_eq_sum_range' (n := 2) (by omega), Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [hasseDeriv_coeff, Nat.choose_succ_self_right, Nat.add_comm 1 n]

private theorem natDegree_eq_zero_of_fixed_small [CharP k p] [NeZero p] (f : Bivariate k)
    (hfixed : action k p (generator p) f = f) (hsmall : f.natDegree < p) :
    f.natDegree = 0 := by
  by_contra hpos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  change f.natDegree = n + 1 at hn
  rw [generator_apply] at hfixed
  have hc := coeff_taylor_below_top (X : Polynomial k) f n hn
  rw [hfixed, eq_comm, add_eq_left] at hc
  have hf : f.coeff (n + 1) ≠ 0 := by
    rw [← hn, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (by intro hf; simp [hf] at hpos)
  have hcast : ((n + 1 : ℕ) : Polynomial k) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff (Polynomial k) p]
    intro hd
    exact (not_le_of_gt hsmall) (hn ▸ Nat.le_of_dvd (Nat.succ_pos n) hd)
  exact (mul_ne_zero (mul_ne_zero hcast hf) X_ne_zero) hc

private theorem aeval_bivariate_norm : (MvPolynomial.aeval ![x k, norm k p]).comp
      (Polynomial.Bivariate.equivMvPolynomial k).toAlgHom =
        (aeval (R := Polynomial k) (norm k p)).restrictScalars k := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp [x, Polynomial.algebraMap_eq]
  · simp

private theorem generated_range :
    generated k p = ((aeval (R := Polynomial k) (norm k p)).restrictScalars k).range := by
  have hrange : Set.range ![x k, norm k p] = ({x k, norm k p} : Set (Bivariate k)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [generated, ← hrange, Algebra.adjoin_range_eq_range_aeval, ← aeval_bivariate_norm]
  ext z
  simp only [AlgHom.mem_range, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  exact ⟨fun ⟨f, hf⟩ => ⟨_, (Polynomial.Bivariate.equivMvPolynomial k).apply_symm_apply f ▸ hf⟩,
    fun ⟨f, hf⟩ => ⟨_, hf⟩⟩

private theorem C_mem_generated (a : Polynomial k) : C a ∈ generated k p := by
  rw [generated_range]
  exact ⟨C a, by simp [Polynomial.algebraMap_eq]⟩

private theorem norm_mem_generated : norm k p ∈ generated k p :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem fixed_subalgebra [CharP k p] [NeZero p] :
    (action k p).fixedSubalgebra = generated k p := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos (R := k) p
  apply le_antisymm
  · intro f hf
    have hfix : action k p (generator p) f = f := hf (generator p)
    clear hf
    induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n ih =>
      by_cases hsmall : f.natDegree < p
      · have hzero := natDegree_eq_zero_of_fixed_small k p f hfix hsmall
        rw [eq_C_of_natDegree_le_zero hzero.le]
        exact C_mem_generated k p _
      -- The substitution preserves degree, so uniqueness of monic division makes
      -- the quotient and remainder fixed as well.
      let N := norm k p
      let q := f /ₘ N
      let r := f %ₘ N
      have hm : N.Monic := norm_monic k p
      have hNd : N.natDegree = p := norm_natDegree k p
      have he : r + N * q = f := modByMonic_add_div f N
      let g := action k p (generator p)
      have hNfix : g N = N := norm_fixed k p (generator p)
      have hgfix : g f = f := hfix
      have hrd : r.degree < N.degree := degree_modByMonic_lt f hm
      have hdiv : q = g q ∧ r = g r := div_modByMonic_unique (g q) (g r) hm ⟨by
        simpa only [map_add, map_mul, hNfix, hgfix] using congrArg g he, by
        change (action k p (generator p) r).degree < N.degree
        rwa [generator_apply, degree_taylor]⟩
      have hrsmall : r.natDegree < p := by
        by_cases hr : r = 0
        · simpa [hr] using (Fact.out : p.Prime).pos
        · rw [natDegree_lt_iff_degree_lt hr, ← hNd]
          simpa [degree_eq_natDegree hm.ne_zero] using hrd
      have hrzero := natDegree_eq_zero_of_fixed_small k p r hdiv.2.symm hrsmall
      have hrmem : r ∈ generated k p := by
        rw [eq_C_of_natDegree_le_zero hrzero.le]
        exact C_mem_generated k p _
      have hqlt : q.natDegree < n := by
        change (f /ₘ N).natDegree < n
        rw [natDegree_divByMonic f hm, hNd, hd]
        have hp := (Fact.out : p.Prime).pos
        omega
      rw [← he]
      exact (generated k p).add_mem hrmem
        ((generated k p).mul_mem (norm_mem_generated k p) (ih _ hqlt hdiv.1.symm rfl))
  · apply Algebra.adjoin_le
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact x_mem_fixed k p
    · exact norm_fixed k p

theorem algebraic_independence [CharP k p] [NeZero p] :
    AlgebraicIndependent k ![x k, norm k p] := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos (R := k) p
  rw [algebraicIndependent_iff_injective_aeval]
  have hi : Function.Injective (aeval (R := Polynomial k) (norm k p)) :=
    transcendental_iff_injective.mp (Polynomial.transcendental _ (by
      rw [norm_natDegree]
      exact (Fact.out : p.Prime).ne_zero) (by simp [(norm_monic k p).leadingCoeff]))
  have hh : Function.Injective ((MvPolynomial.aeval ![x k, norm k p]).comp
      (Polynomial.Bivariate.equivMvPolynomial k).toAlgHom) :=
    (aeval_bivariate_norm k p).symm ▸ hi
  intro a b hab
  let e := Polynomial.Bivariate.equivMvPolynomial k
  have h := hh (show (MvPolynomial.aeval ![x k, norm k p]) (e (e.symm a)) =
      (MvPolynomial.aeval ![x k, norm k p]) (e (e.symm b)) by simpa using hab)
  exact e.symm.injective h

private theorem generated_dvd_natDegree [Fact p.Prime] (b : generated k p) :
    p ∣ (b : Bivariate k).natDegree := by
  let a : Bivariate k := b
  have hb : a ∈ ((aeval (R := Polynomial k) (norm k p)).restrictScalars k).range :=
    (generated_range k p) ▸ (show a ∈ generated k p from b.property)
  obtain ⟨f, hf⟩ := hb
  have hcomp : f.comp (norm k p) = a := hf
  change p ∣ a.natDegree
  rw [← hcomp, natDegree_comp, norm_natDegree]
  exact dvd_mul_left p _

private theorem powers_linearIndependent [Fact p.Prime] :
    LinearIndependent (generated k p) (fun i : Fin p => y k ^ (i : ℕ)) := by
  classical
  refine (Fintype.linearIndependent_iff (R := ↥(generated k p))
    (v := fun i : Fin p => y k ^ (i : ℕ))).2 ?_
  intro b hb i
  by_contra hi
  let s := Finset.univ.filter (fun j => b j ≠ 0)
  let term (j : Fin p) : Bivariate k := (b j : Bivariate k) * y k ^ (j : ℕ)
  have his : i ∈ s := by simp [s, hi]
  have hnonzero (j : Fin p) (hj : j ∈ s) : (b j : Bivariate k) ≠ 0 := by
    have hj' : b j ≠ 0 := (Finset.mem_filter.mp hj).2
    exact fun hz => hj' (Subtype.ext hz)
  -- Nonzero summands have distinct degrees because their residues are the basis indices.
  have hmod (j : Fin p) (hj : j ∈ s) : (term j).natDegree % p = (j : ℕ) := by
    obtain ⟨d, hd⟩ := generated_dvd_natDegree k p (b j)
    change natDegree ((b j : Bivariate k) * X ^ (j : ℕ)) % p = (j : ℕ)
    rw [natDegree_mul_X_pow _ (hnonzero j hj), hd, Nat.mul_add_mod,
      Nat.mod_eq_of_lt j.isLt]
  obtain ⟨j, hjs, hjmax⟩ := Finset.exists_max_image s (fun j => (term j).natDegree) ⟨i, his⟩
  have hlt (l : Fin p) (hls : l ∈ s) (hlj : l ≠ j) :
      (term l).natDegree < (term j).natDegree := by
    refine lt_of_le_of_ne (hjmax l hls) fun he => hlj (Fin.ext ?_)
    rw [← hmod l hls, ← hmod j hjs, he]
  have hsum : ∑ l ∈ s, term l = 0 := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    · simpa only [term, Subalgebra.smul_def, smul_eq_mul] using hb
    · intro l _ hl
      have hz : b l = 0 := by simpa [s] using hl
      simp [term, hz]
  have hc := congrArg (fun f : Bivariate k => f.coeff (term j).natDegree) hsum
  change (∑ l ∈ s, term l).coeff (term j).natDegree = 0 at hc
  rw [finsetSum_coeff, Finset.sum_eq_single_of_mem j hjs
    (fun l hls hlj => coeff_eq_zero_of_natDegree_lt (hlt l hls hlj)), coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr (mul_ne_zero (hnonzero j hjs) (pow_ne_zero _ X_ne_zero))) hc

private theorem powers_aeval_surjective :
    Function.Surjective (aeval (R := ↥(generated k p)) (y k)) := by
  intro f
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨q, rfl⟩ := hf
    obtain ⟨r, rfl⟩ := hg
    exact ⟨q + r, map_add (aeval (y k)) q r⟩
  | monomial n c =>
    let b : generated k p := ⟨C c, C_mem_generated k p c⟩
    refine ⟨C b * X ^ n, ?_⟩
    rw [map_mul, map_pow, aeval_C, aeval_X, ← C_mul_X_pow_eq_monomial]
    rfl

private theorem span_powers_of_relation
    {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A]
    (z : A) (hsurj : Function.Surjective (aeval (R := R) z)) (a b : R)
    (hp : 1 < p) (hrel : z ^ p = algebraMap R A a * z + algebraMap R A b) :
    ⊤ ≤ Submodule.span R (Set.range fun i : Fin p => z ^ (i : ℕ)) := by
  let Q : Polynomial R := X ^ p - (C a * X + C b)
  have hl : (C a * X + C b : Polynomial R).natDegree < p := by
    rw [natDegree_add_C]
    exact (by simpa only [pow_one] using natDegree_C_mul_X_pow_le a 1 : _ ≤ 1).trans_lt hp
  have hm : Q.Monic := by
    apply (monic_X_pow p).sub_of_left
    apply degree_lt_degree
    rwa [natDegree_X_pow]
  have hd : Q.natDegree = p := by
    change (X ^ p - (C a * X + C b) : Polynomial R).natDegree = p
    rw [sub_eq_add_neg, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rwa [natDegree_neg, natDegree_X_pow]
  have hQ : aeval z Q = 0 := by
    simp only [Q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hrel, sub_self]
  -- Replace a polynomial representative by its remainder modulo the monic relation.
  intro f _
  obtain ⟨q, rfl⟩ := hsurj f
  apply PowerBasis.mem_span_pow'.mpr
  refine ⟨q %ₘ Q, (degree_modByMonic_lt q hm).trans_le (hd ▸ degree_le_natDegree), ?_⟩
  have h := congrArg (aeval z) (modByMonic_add_div q Q)
  simpa only [map_add, map_mul, hQ, zero_mul, add_zero] using h.symm

private theorem powers_span [Fact p.Prime] :
    ⊤ ≤ Submodule.span (generated k p) (Set.range fun i : Fin p => y k ^ (i : ℕ)) := by
  let a : generated k p := ⟨x k ^ (p - 1), by
    rw [show x k = C (X : Polynomial k) from rfl, ← C_pow]
    exact C_mem_generated k p _⟩
  let b : generated k p := ⟨norm k p, norm_mem_generated k p⟩
  let : CommRing (generated k p) := (generated k p).toCommRing
  refine span_powers_of_relation p (R := ↥(generated k p)) (A := Bivariate k)
    (y k) (powers_aeval_surjective k p) a b
    (Fact.out : p.Prime).one_lt ?_
  change y k ^ p = x k ^ (p - 1) * y k + (y k ^ p - x k ^ (p - 1) * y k)
  rw [add_comm (x k ^ (p - 1) * y k), sub_add_cancel]

theorem powers_basis [CharP k p] [NeZero p] :
    ∃ b : Module.Basis (Fin p) (generated k p) (Bivariate k),
      ∀ i, b i = y k ^ (i : ℕ) := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos (R := k) p
  exact ⟨Module.Basis.mk (powers_linearIndependent k p) (powers_span k p),
    Module.Basis.mk_apply _ _⟩

theorem no_equivariant_retraction [CharP k p] [NeZero p] :
    ¬ ∃ P : Bivariate k →ₗ[k] (action k p).fixedSubalgebra,
      (action k p).toRepresentation.IsIntertwiningMap
        (Representation.trivial k (Multiplicative (ZMod p)) (action k p).fixedSubalgebra) P ∧
      ∀ a : (action k p).fixedSubalgebra, P (a : Bivariate k) = a := by
  rintro ⟨P, hP, hret⟩
  have hg := hP.isIntertwining (generator p) (y k)
  change P (action k p (generator p) (y k)) = P (y k) at hg
  rw [(generator_coordinates k p).2, map_add, add_eq_left] at hg
  let a : (action k p).fixedSubalgebra := ⟨x k, x_mem_fixed k p⟩
  have ha : a = 0 := (hret a).symm.trans hg
  have hx : x k = 0 := congrArg Subtype.val ha
  exact X_ne_zero (C_injective (hx.trans C_0.symm))

theorem no_reynolds_operator [CharP k p] [NeZero p] :
    ¬ ∃ P : Bivariate k →ₗ[k] (action k p).fixedSubalgebra, (action k p).IsReynolds P := by
  rintro ⟨P, hP⟩
  exact no_equivariant_retraction k p ⟨P, hP.1, hP.2.2⟩

end

end RepTheorySurvey.Invariants.CyclicModularInvariant
