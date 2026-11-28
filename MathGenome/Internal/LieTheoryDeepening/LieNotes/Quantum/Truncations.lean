import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Truncations

noncomputable section

namespace LieNotes.Quantum.Truncations

abbrev truncationIdeal := Specs.LieNotes.Quantum.Truncations.truncationIdeal
abbrev A := Specs.LieNotes.Quantum.Truncations.A
abbrev mk := Specs.LieNotes.Quantum.Truncations.mk
abbrev h := Specs.LieNotes.Quantum.Truncations.h
abbrev reduce := @Specs.LieNotes.Quantum.Truncations.reduce
abbrev truncate := @Specs.LieNotes.Quantum.Truncations.truncate
abbrev evalTrunc := @Specs.LieNotes.Quantum.Truncations.evalTrunc
abbrev cartanTruncate := @Specs.LieNotes.Quantum.Truncations.cartanTruncate
abbrev coeff := @Specs.LieNotes.Quantum.Truncations.coeff
abbrev ofCoeffs := @Specs.LieNotes.Quantum.Truncations.ofCoeffs
abbrev expH := @Specs.LieNotes.Quantum.Truncations.expH

variable {R : Type*} [CommRing R] {L M N : ℕ}

@[simp]
theorem h_pow (N : ℕ) : h R N ^ N = 0 := by
  change mk R N Polynomial.X ^ N = 0
  rw [← map_pow]
  have hp : (Polynomial.X : Polynomial R) ^ N ∈ truncationIdeal R N :=
    Ideal.subset_span (Set.mem_singleton _)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

@[simp]
theorem reduce_mk (e : M ≤ N) (p : Polynomial R) :
    reduce e (mk R N p) = mk R M p := rfl

@[simp]
theorem reduce_h (e : M ≤ N) : reduce e (h R N) = h R M := rfl

@[simp]
theorem reduce_refl (N : ℕ) :
    reduce (R := R) (le_refl N) = AlgHom.id R (A R N) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) a
  rfl

theorem reduce_comp (e : M ≤ N) (d : L ≤ M) :
    (reduce (R := R) d).comp (reduce e) = reduce (d.trans e) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) a
  rfl

@[simp]
theorem coeff_mk (p : Polynomial R) (j : Fin N) :
    coeff j (mk R N p) = p.coeff j := rfl

@[simp]
theorem coeff_reduce (e : M ≤ N) (j : Fin M) (a : A R N) :
    coeff j (reduce e a) = coeff (Fin.castLE e j) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) a
  rfl

theorem ext_of_coeff {a b : A R N} (e : ∀ j : Fin N, coeff j a = coeff j b) : a = b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) b
  change Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ q
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change p - q ∈ Ideal.span {Polynomial.X ^ N}
  rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro j hj
  rw [Polynomial.coeff_sub, sub_eq_zero]
  exact e ⟨j, hj⟩

@[simp]
theorem coeff_ofCoeffs (a : Fin N → R) (i : Fin N) : coeff i (ofCoeffs a) = a i := by
  have hmon (j : Fin N) :
      algebraMap R (A R N) (a j) * h R N ^ (j : ℕ) =
        mk R N (Polynomial.monomial j (a j)) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    rfl
  change coeff i (∑ j : Fin N, algebraMap R (A R N) (a j) * h R N ^ (j : ℕ)) = _
  simp only [map_sum, hmon, coeff_mk]
  rw [Finset.sum_eq_single i]
  · exact Polynomial.coeff_monomial_same _ _
  · intro j _ hj
    exact Polynomial.coeff_monomial_of_ne _ (fun hval => hj (Fin.ext hval.symm))
  · simp

@[simp]
theorem ofCoeffs_coeff (a : A R N) : ofCoeffs (fun j => coeff j a) = a :=
  ext_of_coeff (coeff_ofCoeffs _)

theorem existsUnique_coeffs (a : A R N) : ∃! c : Fin N → R, ofCoeffs c = a := by
  refine ⟨fun j => coeff j a, ofCoeffs_coeff a, ?_⟩
  intro c hc
  funext j
  rw [← hc, coeff_ofCoeffs]

@[simp]
theorem coeff_truncate (f : PowerSeries R) (j : Fin N) :
    coeff j (truncate N f) = PowerSeries.coeff j f := by
  change coeff j (mk R N (PowerSeries.trunc N f)) = _
  rw [coeff_mk, PowerSeries.coeff_trunc, ite_eq_left j.isLt]

theorem reduce_comp_truncate (e : M ≤ N) :
    (reduce (R := R) e).comp (truncate N) = truncate M := by
  ext f
  apply ext_of_coeff
  intro j
  rw [AlgHom.comp_apply, coeff_reduce, coeff_truncate, coeff_truncate]
  rfl

theorem truncate_eq_sum (N : ℕ) (f : PowerSeries R) :
    truncate N f =
      ∑ j : Fin N, algebraMap R (A R N) (PowerSeries.coeff j f) * h R N ^ (j : ℕ) := by
  change truncate N f = ofCoeffs (fun j : Fin N => PowerSeries.coeff j f)
  simpa only [coeff_truncate] using (ofCoeffs_coeff (truncate N f)).symm

@[simp]
theorem truncate_polynomial (N : ℕ) (p : Polynomial R) :
    truncate N (p : PowerSeries R) = mk R N p := by
  apply ext_of_coeff
  intro j
  rw [coeff_truncate, coeff_mk, Polynomial.coeff_coe]

@[simp]
theorem truncate_X (N : ℕ) : truncate N (PowerSeries.X : PowerSeries R) = h R N := by
  rw [← Polynomial.coe_X, truncate_polynomial]
  rfl

theorem truncate_surjective (N : ℕ) : Function.Surjective (truncate (R := R) N) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (truncationIdeal R N) a
  exact ⟨(p : PowerSeries R), truncate_polynomial N p⟩

theorem truncate_eq_zero_iff (N : ℕ) (f : PowerSeries R) :
    truncate N f = 0 ↔ (PowerSeries.X : PowerSeries R) ^ N ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro e j hj
    simpa using congrArg (coeff ⟨j, hj⟩) e
  · intro e
    apply ext_of_coeff
    intro j
    rw [coeff_truncate, map_zero]
    exact e j j.isLt

theorem evalTrunc_eq_sum {S : Type*} [CommRing S] (N : ℕ) (f : R →+* S) (z : S)
    (hz : z ^ N = 0) (p : PowerSeries R) :
    evalTrunc N f z hz p = ∑ j ∈ Finset.range N, f (PowerSeries.coeff j p) * z ^ j := by
  change (PowerSeries.trunc N p).eval₂ f z = _
  exact PowerSeries.eval₂_trunc_eq_sum_range z f N p

@[simp]
theorem evalTrunc_polynomial {S : Type*} [CommRing S] (N : ℕ) (f : R →+* S) (z : S)
    (hz : z ^ N = 0) (p : Polynomial R) :
    evalTrunc N f z hz (p : PowerSeries R) = p.eval₂ f z := by
  have hp : (truncate N).toRingHom (p : PowerSeries R) = mk R N p :=
    truncate_polynomial N p
  unfold evalTrunc Specs.LieNotes.Quantum.Truncations.evalTrunc
  rw [RingHom.comp_apply, hp]
  rfl

theorem cartanTruncate_eq_sum (σ : Type*) (N : ℕ) (p : PowerSeries (MvPolynomial σ R)) :
    cartanTruncate σ N p =
      ∑ j ∈ Finset.range N,
        MvPolynomial.map (algebraMap R (A R N)) (PowerSeries.coeff j p) *
          MvPolynomial.C (h R N) ^ j :=
  evalTrunc_eq_sum _ _ _ _ _

@[simp]
theorem cartanTruncate_C (N : ℕ) {σ : Type*} (p : MvPolynomial σ R) :
    cartanTruncate σ N (PowerSeries.C p) = MvPolynomial.map (algebraMap R (A R N)) p := by
  rw [← Polynomial.coe_C]
  exact (evalTrunc_polynomial _ _ _ _ _).trans (Polynomial.eval₂_C ..)

@[simp]
theorem cartanTruncate_X (σ : Type*) (N : ℕ) :
    cartanTruncate σ N PowerSeries.X = MvPolynomial.C (h R N) := by
  rw [← Polynomial.coe_X]
  exact (evalTrunc_polynomial _ _ _ _ _).trans (Polynomial.eval₂_X ..)

theorem cartanTruncate_scalar (σ : Type*) (N : ℕ) (p : PowerSeries R) :
    cartanTruncate σ N (p.map MvPolynomial.C) = MvPolynomial.C (truncate N p) := by
  simp only [cartanTruncate_eq_sum, truncate_eq_sum, map_sum, map_mul, map_pow,
    PowerSeries.coeff_map, MvPolynomial.map_C]
  exact (Fin.sum_univ_eq_sum_range (fun j =>
    MvPolynomial.C (σ := σ) (algebraMap R (A R N) (PowerSeries.coeff j p)) *
      MvPolynomial.C (h R N) ^ j) N).symm

theorem cartanTruncate_reduce (σ : Type*) (e : M ≤ N)
    (p : PowerSeries (MvPolynomial σ R)) :
    MvPolynomial.map (reduce (R := R) e).toRingHom (cartanTruncate σ N p) =
      cartanTruncate σ M p := by
  have hr : (reduce (R := R) e).toRingHom (h R N) = h R M := reduce_h e
  simp only [cartanTruncate_eq_sum, map_sum, map_mul, map_pow, MvPolynomial.map_map,
    MvPolynomial.map_C, hr]
  have hcomp :
      (reduce (R := R) e).toRingHom.comp (algebraMap R (A R N)) =
        algebraMap R (A R M) := by
    ext r
    exact (reduce e).commutes r
  rw [hcomp]
  symm
  refine Finset.sum_subset (Finset.range_mono e) ?_
  intro j _ hj
  have hj' : M ≤ j := Nat.le_of_not_lt (fun hlt => hj (Finset.mem_range.mpr hlt))
  have hz : MvPolynomial.C (σ := σ) (h R M) ^ M = 0 := by
    rw [← map_pow, h_pow, map_zero]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj'
  rw [hd, pow_add, hz, zero_mul, mul_zero]

section Exponential

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra ℚ S] [Algebra ℚ T]

@[simp]
theorem coeff_expH (a : S) (j : ℕ) :
    PowerSeries.coeff j (expH a) = a ^ j * algebraMap ℚ S (1 / (j.factorial : ℚ)) := by
  change PowerSeries.coeff j (PowerSeries.rescale a (PowerSeries.exp S)) = _
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

@[simp]
theorem expH_zero : expH (0 : S) = 1 := by
  change PowerSeries.rescale (0 : S) (PowerSeries.exp S) = 1
  simp

theorem expH_add (a b : S) : expH (a + b) = expH a * expH b :=
  (PowerSeries.exp_mul_exp_eq_exp_add a b).symm

theorem expH_mul_neg (a : S) : expH a * expH (-a) = 1 := by
  rw [← expH_add, add_neg_cancel, expH_zero]

@[simp]
theorem map_expH (f : S →+* T) (a : S) : (expH a).map f = expH (f a) := by
  change (PowerSeries.rescale a (PowerSeries.exp S)).map f =
    PowerSeries.rescale (f a) (PowerSeries.exp T)
  rw [← PowerSeries.rescale_map, PowerSeries.map_exp]

end Exponential

end LieNotes.Quantum.Truncations
