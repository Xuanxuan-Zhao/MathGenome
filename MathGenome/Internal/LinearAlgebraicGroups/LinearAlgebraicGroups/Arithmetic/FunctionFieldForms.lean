import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.PowerSeries.Evaluation
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm

noncomputable section

set_option maxHeartbeats 1000000

open scoped Polynomial RatFunc PowerSeries LaurentSeries WithZero PowerSeries.WithPiTopology
open ValuativeRel Filter
open scoped Topology ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldForms

universe u v w

/-- List each monomial as a product of exactly `d` variables, with repetitions. -/
private theorem homogeneous_monomial_terms {K : Type u} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    ∃ (r : ℕ) (c : Fin r → K) (i : Fin r → Fin d → Fin n),
      ∀ x : Fin n → K, MvPolynomial.eval x f = ∑ j, c j * ∏ l, x (i j l) := by
  classical
  let e := Fintype.equivFin f.support
  let r := Fintype.card f.support
  let c (j : Fin r) := f.coeff (e.symm j).val
  have hlen (j : Fin r) : (e.symm j).val.toMultiset.toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hf.degree_eq_sum_deg_support (e.symm j).property |>.symm
  let i (j : Fin r) (l : Fin d) :=
    (e.symm j).val.toMultiset.toList.get (Fin.cast (hlen j).symm l)
  refine ⟨r, c, i, fun x => ?_⟩
  calc
    MvPolynomial.eval x f =
        ∑ j ∈ f.support, f.coeff j * j.prod (fun k m => x k ^ m) := by
      conv_lhs => rw [← f.support_sum_monomial_coeff]
      rw [map_sum]
      simp only [MvPolynomial.eval_monomial]
    _ = ∑ j : f.support, f.coeff j.val * j.val.prod (fun k m => x k ^ m) :=
      (Finset.sum_attach f.support _).symm
    _ = ∑ j : Fin r, c j * ∏ l, x (i j l) := by
      rw [← e.symm.sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      let m := (e.symm j).val
      have he : List.ofFn (i j) = m.toMultiset.toList := by
        have aux (l : List (Fin n)) (h : l.length = d) :
            List.ofFn (fun j => l.get (Fin.cast h.symm j)) = l := by
          subst d
          exact List.ofFn_get _
        exact aux _ (hlen j)
      rw [← Finsupp.prod_mapDomain_index (h := fun (a : K) b => a ^ b)
          (f := x) (s := m) (fun _ => pow_zero _) (fun _ _ _ => pow_add ..),
        ← Finsupp.prod_toMultiset, ← Finsupp.toMultiset_map, ← Multiset.prod_map_toList,
        ← he, List.map_ofFn, List.prod_ofFn]
      rfl

private theorem eval_scaled {K : Type u} [Field K] {n d : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) (a : K) (x : Fin n → K) :
    MvPolynomial.eval (fun i => a * x i) f = a ^ d * MvPolynomial.eval x f := by
  obtain ⟨r, c, i, h⟩ := homogeneous_monomial_terms f hf
  rw [h, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.prod_mul_distrib]
  simp [mul_left_comm]

private theorem chevalley_warning_nonzero {k : Type v} [Field k] [Finite k]
    {ι σ : Type} [Fintype ι] [Fintype σ] (f : ι → MvPolynomial σ k)
    (h : (∑ i, (f i).totalDegree) < Fintype.card σ)
    (h₀ : ∀ i, MvPolynomial.eval (0 : σ → k) (f i) = 0) :
    ∃ x : σ → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  classical
  let : Fintype k := Fintype.ofFinite k
  let S := {x : σ → k // ∀ i, MvPolynomial.eval x (f i) = 0}
  let z : S := ⟨0, h₀⟩
  have hd : ringChar k ∣ Fintype.card S :=
    char_dvd_card_solutions_of_fintype_sum_lt (f := f) (ringChar k) h
  have hcard : 1 < Fintype.card S := by
    have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨z⟩
    exact lt_of_lt_of_le (CharP.char_is_prime k (ringChar k)).one_lt (Nat.le_of_dvd hpos hd)
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  exact ⟨x.1, fun h => hx (Subtype.ext h), x.2⟩

private theorem coeff_homogeneous_mul {k : Type v} [CommSemiring k] {σ : Type}
    {f g : (MvPolynomial σ k)[X]} {d e : ℕ}
    (hf : ∀ j, (f.coeff j).IsHomogeneous d) (hg : ∀ j, (g.coeff j).IsHomogeneous e)
    (j : ℕ) : ((f * g).coeff j).IsHomogeneous (d + e) := by
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun a _ => (hf a.1).mul (hg a.2))

private theorem coeff_homogeneous_prod {k : Type v} [CommSemiring k] {σ ι : Type}
    (s : Finset ι) (f : ι → (MvPolynomial σ k)[X])
    (hf : ∀ i ∈ s, ∀ j, ((f i).coeff j).IsHomogeneous 1) (j : ℕ) :
    ((∏ i ∈ s, f i).coeff j).IsHomogeneous s.card := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, Polynomial.coeff_one]
    split
    · exact MvPolynomial.isHomogeneous_one _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm]
    exact coeff_homogeneous_mul (hf i (Finset.mem_insert_self ..))
      (fun _ => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) _) j

theorem global_bound : GlobalBound.{u,v} := by
  classical
  intro K _ k _ _ _ _ d hd n hn f hf
  by_cases hzero : f = 0
  · refine ⟨fun _ => 1, ?_, by simp [hzero]⟩
    intro h
    exact one_ne_zero (congrFun h ⟨0, by omega⟩)
  obtain ⟨r, c, i, hi⟩ := homogeneous_monomial_terms f hf
  have hs₀ : 0 < Module.finrank k⟮X⟯ K := Module.finrank_pos
  let b₀ := Module.finBasis k⟮X⟯ K
  generalize hdim : Module.finrank k⟮X⟯ K = s at hs₀
  let b : Module.Basis (Fin s) k⟮X⟯ K := b₀.reindex (finCongr hdim)
  clear_value b
  -- Each choice of basis vectors for the factors of a monomial has a fixed denominator.
  let T := Fin r × (Fin d → Fin s)
  let w (a : T) := c a.1 * ∏ l, b (a.2 l)
  let A : k[X] →+* k⟮X⟯ := algebraMap _ _
  obtain ⟨den, hden⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors k[X])
    (Finset.univ : Finset (T × Fin s)) (fun a => b.repr (w a.1) a.2)
  have hnz : A den ≠ 0 := RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero den.property)
  have hq (a : T) (j : Fin s) :
      ∃ q : k[X], A q = A den * b.repr (w a) j := by
    obtain ⟨q, h⟩ := hden (a, j) (Finset.mem_univ _)
    exact ⟨q, by simpa [A, Algebra.smul_def] using h⟩
  let q (a : T) (j : Fin s) := (hq a j).choose
  have hq_eq (a : T) (j : Fin s) : A (q a j) = A den * b.repr (w a) j :=
    (hq a j).choose_spec
  clear_value q
  let C := (Finset.univ : Finset (T × Fin s)).sup fun a => (q a.1 a.2).natDegree
  have hC (a : T) (j : Fin s) : (q a j).natDegree ≤ C :=
    Finset.le_sup (f := fun a : T × Fin s => (q a.1 a.2).natDegree) (Finset.mem_univ (a, j))
  clear_value C
  -- The basis coordinates of every substituted input have degree at most `N`.
  let N := d * C + 1
  let D := C + d * N
  let V := Fin n × Fin s × Fin (N + 1)
  let P (h : Fin n) (j : Fin s) : (MvPolynomial V k)[X] :=
    ∑ l : Fin (N+1), Polynomial.monomial l.val (MvPolynomial.X (h,j,l))
  let G (j : Fin s) : (MvPolynomial V k)[X] :=
    ∑ a : T, (q a j).map MvPolynomial.C * ∏ l : Fin d, P (i a.1 l) (a.2 l)
  have hPdeg (h : Fin n) (j : Fin s) : (P h j).natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ l.isLt)
  have hGdeg (j : Fin s) : (G j).natDegree ≤ D := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    refine Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_map_le.trans (hC a j)) ?_)
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc
      _ ≤ ∑ _l : Fin d, N := Finset.sum_le_sum fun l _ => hPdeg _ _
      _ = _ := by simp
  have hPhom (h : Fin n) (j : Fin s) (m : ℕ) : ((P h j).coeff m).IsHomogeneous 1 := by
    rw [show (P h j).coeff m = ∑ l : Fin (N+1),
        (Polynomial.monomial l.val (MvPolynomial.X (h,j,l))).coeff m by
      exact map_sum (Polynomial.lcoeff _ m) _ _]
    apply MvPolynomial.IsHomogeneous.sum
    intro l _
    rw [Polynomial.coeff_monomial]
    split
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hGhom (j : Fin s) (m : ℕ) : ((G j).coeff m).IsHomogeneous d := by
    rw [show (G j).coeff m = ∑ a : T,
        ((q a j).map MvPolynomial.C * ∏ l : Fin d, P (i a.1 l) (a.2 l)).coeff m by
      exact map_sum (Polynomial.lcoeff _ m) _ _]
    apply MvPolynomial.IsHomogeneous.sum
    intro a _
    have hp (l : ℕ) :
        ((∏ t : Fin d, P (i a.1 t) (a.2 t)).coeff l).IsHomogeneous d := by
      have hh := coeff_homogeneous_prod (Finset.univ : Finset (Fin d))
        (fun t => P (i a.1 t) (a.2 t)) (fun t _ l => hPhom (i a.1 t) (a.2 t) l) l
      simpa using hh
    have hc (l : ℕ) : (((q a j).map (MvPolynomial.C : k →+* MvPolynomial V k)).coeff l).IsHomogeneous 0 := by
      rw [Polynomial.coeff_map]
      exact MvPolynomial.isHomogeneous_C _ _
    simpa only [zero_add] using coeff_homogeneous_mul hc hp m
  -- The coefficient equations have total degree at most `d` in the scalar unknowns.
  let E (a : Fin s × Fin (D+1)) := (G a.1).coeff a.2
  have hcount : (∑ a, (E a).totalDegree) < Fintype.card V := by
    refine (Finset.sum_le_sum (fun a _ => (hGhom a.1 a.2).totalDegree_le)).trans_lt ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_fin, V]
    change s * (D + 1) * d < n * (s * (N + 1))
    rw [mul_assoc, mul_left_comm n s]
    apply Nat.mul_lt_mul_of_pos_left _ hs₀
    have h₁ : d ^ 2 + 1 ≤ n := hn
    have h₂ := Nat.mul_le_mul_right (N + 1) h₁
    dsimp [D, N] at h₂ ⊢
    nlinarith
  have hE₀ a : MvPolynomial.eval (0 : V → k) (E a) = 0 := by
    rw [MvPolynomial.eval_zero]
    apply (hGhom a.1 a.2).coeff_eq_zero
    simpa using hd.ne
  obtain ⟨x, hx, hE⟩ := chevalley_warning_nonzero E hcount hE₀
  let p (h : Fin n) (j : Fin s) : k[X] :=
    ∑ l : Fin (N+1), Polynomial.monomial l.val (x (h,j,l))
  let y (h : Fin n) : K := ∑ j, A (p h j) • b j
  have hy : y ≠ 0 := by
    intro hz
    apply hx
    funext a
    rcases a with ⟨h,j,l⟩
    have hz' := congrArg (fun y : Fin n → K => b.repr (y h) j) hz
    have he : A (p h j) = 0 := by
      simpa [y, Finsupp.single_apply, Finset.sum_ite_eq'] using hz'
    have hp : p h j = 0 := RatFunc.algebraMap_injective k (he.trans (map_zero A).symm)
    have hc := congrArg (fun p : k[X] => p.coeff l.val) hp
    simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Fin.val_inj, Finset.sum_ite_eq'] using hc
  let ev := Polynomial.mapRingHom (MvPolynomial.eval x)
  have hevP (h : Fin n) (j : Fin s) : ev (P h j) = p h j := by
    simp [ev, P, p, Polynomial.map_monomial]
  have hevG (j : Fin s) : ev (G j) = 0 := by
    ext m
    rw [Polynomial.coeff_zero, show (ev (G j)).coeff m =
      MvPolynomial.eval x ((G j).coeff m) from MvPolynomial.coeff_eval_eq_eval_coeff V x _ _]
    by_cases hm : m ≤ D
    · exact hE (j, ⟨m, Nat.lt_succ_of_le hm⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hGdeg j).trans_lt (lt_of_not_ge hm)),
        map_zero]
  have hterm (j : Fin s) : A (ev (G j)) = ∑ a : T,
      (A den * b.repr (w a) j) * ∏ l, A (p (i a.1 l) (a.2 l)) := by
    have hmap (q : k[X]) : ev (q.map MvPolynomial.C) = q := by
      ext l
      simp [ev, Polynomial.coeff_map]
    simp only [G, map_sum, map_mul, map_prod, hevP, hmap, hq_eq]
  refine ⟨y, hy, ?_⟩
  have hy_exp : MvPolynomial.eval y f = ∑ a : T,
      (∏ l, A (p (i a.1 l) (a.2 l))) • w a := by
    rw [hi, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    simp only [y, Fintype.prod_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [w, Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
    ring
  have hzero : A den • MvPolynomial.eval y f = 0 := by
    apply b.repr.injective
    ext j
    simp only [hy_exp, map_zero, Finsupp.zero_apply, map_smul, map_sum,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← show A (ev (G j)) = 0 by rw [hevG, map_zero], hterm]
    apply Finset.sum_congr rfl
    intro a _
    ring
  exact (smul_eq_zero.mp hzero).resolve_left hnz

/-- Apply the quadratic bound to the reduced norm minus a scalar times a square. -/
private theorem quaternion_norm_of_bound {K : Type u} [Field K]
    {B : Type v} [DivisionRing B] [Algebra K B]
    (hB : RM03.CSA.IsCentralSimple K B)
    (hdeg : RM03.CSA.degree K B = 2)
    (hbound : HasIsotropyBound K 2) (a : K) (ha : a ≠ 0) :
    ∃ x : Bˣ, RM03.CSA.reducedNorm hB (x : B) = a := by
  classical
  let : FiniteDimensional K B := hB.2.2
  have hrank : Module.finrank K B = 4 := by
    rw [RM03.CSA.finrank_eq_degree_sq hB, hdeg]
    decide
  let b : Module.Basis (Fin 4) K B := (Module.finBasis K B).reindex (finCongr hrank)
  clear_value b
  let c : Fin 5 → B := Fin.cases (motive := fun _ => B) 0 (fun i => b i)
  let g : MvPolynomial (Fin 5) K := RM03.CSA.genericReducedNorm hB c
  let f := g - MvPolynomial.C a * MvPolynomial.X (0 : Fin 5) ^ 2
  have hg : g.IsHomogeneous 2 := by
    have hg' : g.IsHomogeneous (RM03.CSA.degree K B) :=
      RM03.CSA.genericReducedNorm_homogeneous hB c
    exact (congrArg (fun d => g.IsHomogeneous d) hdeg).mp hg'
  have hf : f.IsHomogeneous 2 :=
    hg.sub (by simpa using ((MvPolynomial.isHomogeneous_X K (0 : Fin 5)).pow 2).C_mul a)
  have heval (x : Fin 5 → K) :
      MvPolynomial.eval x g = RM03.CSA.reducedNorm hB (∑ i : Fin 4, x i.succ • b i) := by
    change MvPolynomial.eval x (RM03.CSA.genericReducedNorm hB c) = _
    rw [RM03.CSA.genericReducedNorm_eval, Fin.sum_univ_succ]
    simp [c]
  obtain ⟨x, hx, hfx⟩ := hbound 5 (by decide) f hf
  have hnorm : RM03.CSA.reducedNorm hB (∑ i : Fin 4, x i.succ • b i) =
      a * x 0 ^ 2 := by
    simpa [f, heval, sub_eq_zero] using hfx
  have hz : x 0 ≠ 0 := by
    intro hz
    have hn : RM03.CSA.reducedNorm hB (∑ i : Fin 4, x i.succ • b i) = 0 := by
      simpa [hz] using hnorm
    have hsum : (∑ i : Fin 4, x i.succ • b i) = 0 := by
      by_contra h
      exact (RM03.CSA.reducedNorm_ne_zero_iff_isUnit hB _).2 (isUnit_iff_ne_zero.mpr h) hn
    apply hx
    funext i
    refine Fin.cases hz (fun j => ?_) i
    have h := congrArg (fun y => b.repr y j) hsum
    simpa [Finsupp.single_apply, Finset.sum_ite_eq'] using h
  let y : B := ∑ i : Fin 4, ((x 0)⁻¹ * x i.succ) • b i
  have hy : RM03.CSA.reducedNorm hB y = a := by
    change RM03.CSA.reducedNorm hB (∑ i : Fin 4, ((x 0)⁻¹ * x i.succ) • b i) = a
    rw [← heval (fun i => (x 0)⁻¹ * x i), eval_scaled g hg, heval, hnorm]
    field_simp
  obtain ⟨u, hu⟩ := (RM03.CSA.reducedNorm_ne_zero_iff_isUnit hB y).1 (hy.symm ▸ ha)
  exact ⟨u, hu ▸ hy⟩

/-- The roots of `X^q - X` lift the residue field and are closed under ring operations. -/
private theorem exists_coefficient_field (R : Type u) [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] (p : ℕ) [Fact p.Prime] [CharP R p]
    [Finite (IsLocalRing.ResidueField R)] :
    ∃ s : IsLocalRing.ResidueField R →+* R,
      (IsLocalRing.residue R).comp s = RingHom.id _ := by
  classical
  let k := IsLocalRing.ResidueField R
  let : Fintype k := Fintype.ofFinite k
  let q := Fintype.card k
  let res := IsLocalRing.residue R
  have hp : p.Prime := Fact.out
  let : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    change (p : IsLocalRing.ResidueField R) = 0
    rw [← map_natCast res, CharP.cast_eq_zero R p, map_zero])
  obtain ⟨m, _, hq⟩ := FiniteField.card k p
  have hq' : q = p ^ (m : ℕ) := hq
  have hq₁ : 1 < q := Fintype.one_lt_card
  have hcast : (q : R) = 0 := by
    rw [hq', Nat.cast_pow, CharP.cast_eq_zero R p, zero_pow (PNat.ne_zero m)]
  have hf : ∀ a : k, ∃ b : R, res b = a ∧ b ^ q = b := by
    intro a
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (R := R) a
    let f : Polynomial R := Polynomial.X ^ q - Polynomial.X
    have hmonic : f.Monic := Polynomial.monic_X_pow_sub (by simpa using hq₁)
    have hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        map_sub, map_pow, ha₀, sub_eq_zero]
      exact @FiniteField.pow_card k _ (Fintype.ofFinite k) a
    have hderiv : f.derivative = -1 := by
      simp [f, Polynomial.derivative_X_pow, hcast]
    obtain ⟨b, hb, hb₀⟩ := HenselianRing.is_henselian f hmonic a₀ hroot (by simp [hderiv])
    refine ⟨b, ?_, by simpa [Polynomial.IsRoot, f, sub_eq_zero] using hb⟩
    have h := (IsLocalRing.residue_eq_zero_iff (b - a₀)).2 hb₀
    simpa [map_sub, sub_eq_zero, ha₀] using h
  let s : k → R := fun a => (hf a).choose
  have hs (a : k) : res (s a) = a ∧ s a ^ q = s a := (hf a).choose_spec
  have huniq {x y : R} (hx : x ^ q = x) (hy : y ^ q = y) (hxy : res x = res y) : x = y := by
    have hpow : (x - y) ^ q = x - y := by rw [hq', sub_pow_char_pow, ← hq', hx, hy]
    have hfac : (x - y) * (1 - (x - y) ^ (q - 1)) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq₁.le, hpow, sub_self]
    have hunit : IsUnit (1 - (x - y) ^ (q - 1)) := by
      apply IsUnit.of_map res
      simp [map_sub, hxy, zero_pow (by omega : q - 1 ≠ 0)]
    exact sub_eq_zero.mp ((hunit.mul_left_inj).mp (by simpa using hfac))
  let sHom : k →+* R :=
    { toFun := s
      map_zero' := huniq (hs 0).2 (zero_pow (by omega : q ≠ 0)) (by simpa using (hs 0).1)
      map_one' := huniq (hs 1).2 (one_pow _) (by simpa using (hs 1).1)
      map_add' := fun a b => huniq (hs (a+b)).2
        (by rw [hq', add_pow_char_pow, ← hq', (hs a).2, (hs b).2]) (by simp [hs, res])
      map_mul' := fun a b => huniq (hs (a*b)).2
        (by rw [mul_pow, (hs a).2, (hs b).2]) (by simp [hs, res]) }
  exact ⟨sHom, RingHom.ext fun a => (hs a).1⟩

private theorem power_series_equiv
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)]
    (s : IsLocalRing.ResidueField R →+* R)
    (hs : (IsLocalRing.residue R).comp s = RingHom.id _)
    (t : R) (ht : Irreducible t) :
    ∃ e : (IsLocalRing.ResidueField R)⟦X⟧ ≃+* R,
      e PowerSeries.X = t ∧ ∀ a, e (PowerSeries.C a) = s a := by
  classical
  let k := IsLocalRing.ResidueField R
  let I := IsLocalRing.maximalIdeal R
  let : WithIdeal R := ⟨I⟩
  let : UniformSpace k := ⊥
  have : DiscreteTopology k := ⟨rfl⟩
  have : DiscreteUniformity k := ⟨rfl⟩
  have : IsUniformAddGroup k := inferInstance
  have : IsTopologicalRing k := inferInstance
  have : IsAdic I := rfl
  have hcomplete := this.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I R)
  let : CompleteSpace R := hcomplete.1
  let : T2Space R := hcomplete.2
  have hI : I = Ideal.span {t} := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have htI : t ∈ I := hI ▸ Ideal.subset_span (Set.mem_singleton t)
  have hnil : PowerSeries.HasEval t := WithIdeal.isTopologicallyNilpotent_of_mem htI
  have hc : Continuous s := continuous_of_discreteTopology
  let ev : k⟦X⟧ →+* R := PowerSeries.eval₂Hom hc hnil
  have hX : ev PowerSeries.X = t := by
    simpa only [ev, PowerSeries.coe_eval₂Hom] using (PowerSeries.eval₂_X s t)
  have hC (a : k) : ev (PowerSeries.C a) = s a := by
    simpa only [ev, PowerSeries.coe_eval₂Hom] using (PowerSeries.eval₂_C s t a)
  have hXirr : Irreducible (PowerSeries.X : k⟦X⟧) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 PowerSeries.maximalIdeal_eq_span_X
  have hev_inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).2
    intro f hf
    by_contra h
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hXirr
    rw [map_mul, map_pow, hX] at hf
    exact (mul_ne_zero (u.isUnit.map ev).ne_zero (pow_ne_zero _ ht.ne_zero)) hf
  -- Subtract the lifted residue and divide by the uniformizer to find the next digit.
  have happrox (n : ℕ) : ∀ x : R, ∃ f : k⟦X⟧, x - ev f ∈ I ^ n := by
    induction n with
    | zero => exact fun x => ⟨0, by simp⟩
    | succ n ih =>
      intro x
      let a : k := IsLocalRing.residue R x
      have hres : IsLocalRing.residue R (s a) = a := RingHom.congr_fun hs a
      have hdiff : x - s a ∈ I := (IsLocalRing.residue_eq_zero_iff _).mp (by simp [a, hres])
      rw [hI, Ideal.mem_span_singleton] at hdiff
      obtain ⟨y, hy⟩ := hdiff
      obtain ⟨f, hf⟩ := ih y
      refine ⟨PowerSeries.C a + PowerSeries.X * f, ?_⟩
      rw [map_add, map_mul, hC, hX,
        show x - (s a + t * ev f) = t * (y - ev f) by linear_combination hy,
        pow_succ']
      exact Ideal.mul_mem_mul htI hf
  have hcompact : CompactSpace k⟦X⟧ :=
    inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → k))
  have hclosed : IsClosed (Set.range ev) := by
    simpa only [ev, PowerSeries.coe_eval₂Hom] using
      (isCompact_range (PowerSeries.continuous_eval₂ hc hnil)).isClosed
  have hsurj : Function.Surjective ev := by
    intro x
    change x ∈ Set.range ev
    rw [← hclosed.closure_eq, mem_closure_iff_nhds]
    intro U hU
    obtain ⟨n, -, hn⟩ := (show IsAdic I from rfl).hasBasis_nhds x |>.mem_iff.mp hU
    obtain ⟨f, hf⟩ := happrox n x
    refine ⟨ev f, hn ?_, Set.mem_range_self _⟩
    refine ⟨ev f - x, ?_, by abel_nf⟩
    change ev f - x ∈ (I ^ n : Ideal R)
    simpa only [neg_sub] using (I ^ n).neg_mem hf
  exact ⟨RingEquiv.ofBijective ev ⟨hev_inj, hsurj⟩, hX, hC⟩

theorem laurent_presentation : LaurentPresentation.{u} := by
  classical
  intro F _ _ _ _ p _ _
  let O := (valuation F).valuationSubring
  let k := IsLocalRing.ResidueField O
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal O) O :=
    inferInstanceAs (IsAdicComplete 𝓂[F] 𝒪[F])
  have : Finite k := inferInstanceAs (Finite 𝓀[F])
  let : CharP O p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
    apply Subtype.ext
    change O.subtype (p : O) = O.subtype 0
    rw [map_natCast, map_zero, CharP.cast_eq_zero F p])
  obtain ⟨s, hs⟩ := exists_coefficient_field O p
  let eV := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let vF := LocalDivisionRamification.normalizedValuation F
  obtain ⟨t, ht⟩ := (eV.surjective.comp (valuation_surjective (K := F))) (WithZero.exp (-1))
  change vF t = WithZero.exp (-1) at ht
  have ht₀ : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  have htval : vF t < 1 := by
    rw [ht, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by decide)
  have htval' : valuation F t < 1 := by
    apply eV.strictMono.lt_iff_lt.mp
    rw [map_one]
    exact htval
  let tO : O := ⟨t, htval'.le⟩
  have htI : tO ∈ IsLocalRing.maximalIdeal O :=
    (Valuation.mem_maximalIdeal_iff F (valuation F)).2 htval'
  have hirr : Irreducible tO := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer tO).2
    apply le_antisymm _ (((IsLocalRing.maximalIdeal O).span_singleton_le_iff_mem.mpr htI))
    intro x hx
    have hx' := (Valuation.mem_maximalIdeal_iff F (valuation F)).1 hx
    have hxt : (valuation F) (x : F) ≤ valuation F t := by
      apply eV.strictMono.le_iff_le.mp
      change vF (x : F) ≤ vF t
      rw [ht]
      have h : vF (x : F) < 1 := by
        change eV (valuation F (x : F)) < 1
        rw [← map_one eV]
        exact eV.strictMono hx'
      by_cases hx₀ : vF (x : F) = 0
      · simp [hx₀]
      let z := WithZero.log (vF (x : F))
      have hz : WithZero.exp z = vF (x : F) := WithZero.exp_log hx₀
      rw [← hz, ← WithZero.exp_zero] at h
      rw [← hz]
      have hzlt := WithZero.exp_lt_exp.mp h
      exact WithZero.exp_le_exp.mpr (by omega)
    have hy : valuation F ((x : F) / t) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one₀ (pos_iff_ne_zero.mpr (((Valuation.ne_zero_iff (valuation F)).2 ht₀)))).mpr hxt
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(x : F) / t, hy⟩, Subtype.ext ?_⟩
    change (x : F) = t * ((x : F) / t)
    field_simp
  obtain ⟨eO, heX, heC⟩ := power_series_equiv s hs tO hirr
  let e : k⸨X⸩ ≃+* F := IsFractionRing.ringEquivOfRingEquiv eO
  have he (x : k⟦X⟧) :
      e (algebraMap k⟦X⟧ k⸨X⸩ x) = (eO x : F) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap eO x
  refine ⟨s, hs, t, e, ht, ?_, ?_, ?_⟩
  · simpa [LaurentSeries.coe_algebraMap, PowerSeries.coe_X, heX] using he PowerSeries.X
  · intro a
    simpa [LaurentSeries.coe_algebraMap, PowerSeries.coe_C, heC] using he (PowerSeries.C a)
  intro a
  have hvP (x : k⟦X⟧) :
      vF (eO x : F) = Valued.v (algebraMap k⟦X⟧ k⸨X⸩ x) := by
    by_cases hx : x = 0
    · subst x
      simp
    have hXirr : Irreducible (PowerSeries.X : k⟦X⟧) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 PowerSeries.maximalIdeal_eq_span_X
    obtain ⟨n, a, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hXirr
    have hu : vF (eO (a : k⟦X⟧) : F) = 1 := by
      have hj := (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation F))).mp (a.isUnit.map eO.toRingHom)
      change eV (valuation F (eO (a : k⟦X⟧) : F)) = 1
      change valuation F (eO (a : k⟦X⟧) : F) = 1 at hj
      rw [hj, map_one]
    have hu' : Valued.v (algebraMap k⟦X⟧ k⸨X⸩ (a : k⟦X⟧)) = 1 := by
      rw [LaurentSeries.valuation_def, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (PowerSeries.idealX k).intValuation_eq_one_iff.mpr
        (fun h => (PowerSeries.idealX k).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h a.isUnit))
    rw [map_mul, map_pow, heX]
    change vF ((eO (a : k⟦X⟧) : F) * t ^ n) = _
    simp only [map_mul, map_pow, hu, hu', one_mul]
    rw [ht, LaurentSeries.valuation_def,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, PowerSeries.intValuation_X]
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := k⟦X⟧) a
  change vF (e (_ / _)) = _
  rw [map_div₀, he, he, map_div₀, hvP, hvP, map_div₀]

private theorem laurent_unit_ball_compact (k : Type u) [Field k] [Finite k] :
    IsCompact {x : k⸨X⸩ | Valued.v x ≤ (1 : ℤᵐ⁰)} := by
  let w := Polynomial.idealX k
  let : Finite (k[X] ⧸ w.asIdeal) := by
    change Finite (k[X] ⧸ Ideal.span {(Polynomial.X : k[X])})
    rw [← Polynomial.ker_constantCoeff]
    exact Finite.of_injective _ (RingHom.quotientKerEquivOfSurjective
      (f := Polynomial.constantCoeff (R := k)) Polynomial.constantCoeff_surjective).injective
  have hc := adicIntegers_isCompact (K := k⟮X⟯) w
  convert hc.image (LaurentSeries.comparePkg k).uniformContinuous_toFun.continuous using 1
  ext x
  constructor
  · intro hx
    refine ⟨LaurentSeries.LaurentSeriesRingEquiv k x, ?_, (LaurentSeries.comparePkg k).apply_symm_apply x⟩
    change Valued.v (LaurentSeries.LaurentSeriesRingEquiv k x) ≤ (1 : ℤᵐ⁰)
    rwa [LaurentSeries.valuation_compare]
  · rintro ⟨y, hy, rfl⟩
    have hh : Valued.v y ≤ (1 : ℤᵐ⁰) := hy
    have he : LaurentSeries.LaurentSeriesRingEquiv k (LaurentSeries.comparePkg k y) = y :=
      (LaurentSeries.comparePkg k).symm_apply_apply y
    change Valued.v (LaurentSeries.comparePkg k y) ≤ (1 : ℤᵐ⁰)
    rwa [← LaurentSeries.valuation_compare, he]

theorem laurent_quadratic_bound : LaurentQuadraticBound.{u} := by
  classical
  intro k _ _ n hn f hf
  let L := k⸨X⸩
  let R := k⟮X⟯
  let emb : R →+* L := algebraMap R L
  let w : Valuation L ℤᵐ⁰ := Valued.v
  obtain ⟨r, c, i, hi⟩ := homogeneous_monomial_terms f hf
  let sphere : Set (Fin n → L) :=
    {x | (∀ j, w (x j) ≤ 1) ∧ ∃ j, w (x j) = 1}
  have hle : IsClosed {x : L | w x ≤ 1} := (laurent_unit_ball_compact k).isClosed
  have hlt : IsOpen {x : L | w x < 1} := by
    convert Valued.isOpen_ball L (1 : w.ValueGroup₀) using 1
    ext x
    change w x < 1 ↔ w.restrict x < 1
    rw [← (map_one w.restrict), Valuation.restrict_lt_iff, map_one]
  have heq : IsClosed {x : L | w x = 1} := by
    convert hle.inter hlt.isClosed_compl using 1
    ext x
    change w x = 1 ↔ w x ≤ 1 ∧ ¬ w x < 1
    exact ⟨fun h => ⟨h.le, h.not_lt⟩, fun h => le_antisymm h.1 (le_of_not_gt h.2)⟩
  have hclosed : IsClosed sphere := by
    have H₁ : IsClosed (⋂ j : Fin n, (fun x : Fin n → L => x j) ⁻¹' {x | w x ≤ 1}) :=
      isClosed_iInter fun j => hle.preimage (continuous_apply j)
    have H₂ : IsClosed (⋃ j : Fin n, (fun x : Fin n → L => x j) ⁻¹' {x | w x = 1}) :=
      isClosed_iUnion_of_finite fun j => heq.preimage (continuous_apply j)
    convert H₁.inter H₂ using 1
    ext x
    simp [sphere]
  have hcompact : IsCompact sphere := by
    apply (isCompact_univ_pi fun _ : Fin n => laurent_unit_ball_compact k).of_isClosed_subset hclosed
    intro x hx
    exact Set.mem_pi.mpr fun j _ => hx.1 j
  let : CompactSpace sphere := isCompact_iff_compactSpace.mp hcompact
  have norm_exists (y : Fin n → L) (hy : y ≠ 0) :
      ∃ a : L, (fun j => a * y j) ∈ sphere := by
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      contrapose! hy
      exact funext hy
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j => w (y j)) ⟨j, Finset.mem_univ _⟩
    have hm₀ : y m ≠ 0 := by
      intro h
      have h' := hm j (Finset.mem_univ j)
      rw [h, map_zero, le_zero_iff, map_eq_zero] at h'
      exact hj h'
    have hhit : w ((y m)⁻¹ * y m) = 1 := by rw [inv_mul_cancel₀ hm₀, map_one]
    refine ⟨(y m)⁻¹, ⟨fun l => ?_, ⟨m, hhit⟩⟩⟩
    change w ((y m)⁻¹ * y l) ≤ 1
    rw [map_mul, map_inv₀, inv_mul_le_one₀ (pos_iff_ne_zero.mpr (((Valuation.ne_zero_iff w).2 hm₀)))]
    exact hm l (Finset.mem_univ _)
  -- Compactness makes the locus admitting a normalized zero closed in coefficient space.
  let Z : Set ((Fin r → L) × sphere) :=
    {p | (∑ j : Fin r, p.1 j * ∏ l : Fin 2, (p.2 : Fin n → L) (i j l)) = 0}
  have hZ : IsClosed Z := by
    apply isClosed_eq _ continuous_const
    apply continuous_finsetSum
    intro j _
    apply ((continuous_apply j).comp continuous_fst).mul
    apply continuous_finsetProd
    intro l _
    exact (continuous_apply (i j l)).comp (continuous_subtype_val.comp continuous_snd)
  have hclosed_image : IsClosed (Prod.fst '' Z) := isClosedMap_fst_of_compactSpace Z hZ
  have hDense : DenseRange (fun d : Fin r → R => fun j => emb (d j)) :=
    DenseRange.piMap (fun _ => LaurentSeries.coe_range_dense)
  have hd (d : Fin r → R) : (fun j => emb (d j)) ∈ Prod.fst '' Z := by
    let g : MvPolynomial (Fin n) R :=
      ∑ j, MvPolynomial.C (d j) * ∏ l : Fin 2, MvPolynomial.X (i j l)
    have hg : g.IsHomogeneous 2 := by
      apply MvPolynomial.IsHomogeneous.sum
      intro j _
      apply MvPolynomial.IsHomogeneous.C_mul
      simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun l : Fin 2 => MvPolynomial.X (i j l)) (fun _ => 1)
        (fun _ _ => MvPolynomial.isHomogeneous_X _ _)
    obtain ⟨y, hy, hy₀⟩ := global_bound (K := R) (k := k) 2 (by decide) n hn g hg
    have hy' : (fun j => emb (y j)) ≠ 0 := by
      intro h
      apply hy
      funext j
      exact emb.injective (by simpa using congrFun h j)
    obtain ⟨a, ha⟩ := norm_exists _ hy'
    refine ⟨⟨_, ⟨_, ha⟩⟩, ?_, rfl⟩
    have hmap := congrArg emb hy₀
    simp only [g, map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_zero] at hmap
    change (∑ j : Fin r, emb (d j) * ∏ l : Fin 2, (a * emb (y (i j l)))) = 0
    have he : (∑ j : Fin r, emb (d j) * ∏ l : Fin 2, (a * emb (y (i j l)))) =
        a ^ 2 * ∑ j : Fin r, emb (d j) * ∏ l : Fin 2, emb (y (i j l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.prod_mul_distrib]
      simp [mul_left_comm]
    rw [he, hmap, mul_zero]
  obtain ⟨⟨_, x⟩, hx, rfl⟩ := hclosed_image.closure_subset_iff.mpr
    (Set.range_subset_iff.mpr hd) (hDense c)
  refine ⟨x, ?_, (hi _).trans hx⟩
  intro h
  obtain ⟨j, hj⟩ := x.property.2
  rw [h, Pi.zero_apply, map_zero] at hj
  exact zero_ne_one hj

private theorem isotropy_ringEquiv {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) (d : ℕ) (h : HasIsotropyBound K d) : HasIsotropyBound L d := by
  intro n hn f hf
  obtain ⟨x, hx, hfx⟩ := h n hn (MvPolynomial.map e.symm.toRingHom f) (hf.map _)
  refine ⟨fun j => e (x j), fun h => hx (funext fun j => e.injective (by simpa using congrFun h j)), ?_⟩
  rw [MvPolynomial.eval_map] at hfx
  have hh := congrArg e.toRingHom hfx
  rw [map_zero, MvPolynomial.hom_eval₂, RingEquiv.toRingHom_comp_symm_toRingHom,
    MvPolynomial.eval₂_id] at hh
  exact hh

theorem local_quadratic_bound : LocalQuadraticBound.{u} := by
  intro F _ _ _ _ p _ _
  obtain ⟨s, hs, t, e, he⟩ := laurent_presentation F p
  have : Finite (LocalDivisionAlgebras.BaseResidue F) := inferInstanceAs (Finite 𝓀[F])
  exact isotropy_ringEquiv e 2 (laurent_quadratic_bound _)

theorem completion_quadratic_bound : CompletionQuadraticBound.{u,v} := by
  intro K _ k _ _ _ t w
  let p := ringChar k
  let : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let : CharP w.Completion p :=
    charP_of_injective_ringHom (w.embedding.comp (algebraMap k K)).injective p
  let : IsNonarchimedeanLocalField w.Completion := FunctionPlace.completion_isLocalField t w
  exact local_quadratic_bound w.Completion p

theorem global_quaternion_norm : GlobalQuaternionNorm.{u,v,w} := by
  intro K _ k _ _ _ _ B _ _ hB hdeg a ha
  exact quaternion_norm_of_bound hB hdeg (global_bound (K := K) (k := k) 2 (by decide)) a ha

theorem local_quaternion_norm : LocalQuaternionNorm.{u,v} := by
  intro F _ _ _ _ p _ _ B _ _ hB hdeg a ha
  exact quaternion_norm_of_bound hB hdeg (local_quadratic_bound F p) a ha

end LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
