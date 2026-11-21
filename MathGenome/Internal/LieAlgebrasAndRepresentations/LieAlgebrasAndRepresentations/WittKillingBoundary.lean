import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WittKillingBoundary
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
The Witt example of LA-J09 over arbitrary fields of prime characteristic p > 3.
The polynomial derivative descends to k[t]/(t^p), and evaluation on t identifies
its actual derivation algebra with the quotient as a vector space. The basis
is indexed by Fin p, where n denotes the source's e_{n-1}.

Simplicity uses the distinct ad(e₀)-weights in a quotient by an actual ideal,
followed by the source's lowering and final raising brackets. For the Killing
form, its invariant radical contains e₀ by the sum of squared weights, and
these same ideal arguments force the radical to be the whole algebra.
-/

noncomputable section

open Module Polynomial

universe u

namespace LieAlgebrasAndRepresentations.Witt

variable (k : Type u) [Field k] (p : ℕ) [CharP k p]

/-- The ideal (X^p) is stable under differentiation in characteristic p. -/
lemma derivative_preserves_relation (f : Polynomial k)
    (hf : AdjoinRoot.mk (X ^ p : Polynomial k) f = 0) :
    AdjoinRoot.mk (X ^ p : Polynomial k) (Polynomial.derivative' f) = 0 := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hf
  apply AdjoinRoot.mk_eq_zero.mpr
  change X ^ p ∣ derivative (X ^ p * g)
  simp [derivative_mul, derivative_X_pow]

/-- The usual derivative descends to the quotient; no separability is used. -/
def derivative : Derivation k (Truncated k p) (Truncated k p) :=
  Polynomial.derivative'.liftOfSurjective
    (f := AdjoinRoot.mkₐ (X ^ p : Polynomial k))
    (by intro x; induction x using AdjoinRoot.induction_on with
        | ih f => exact ⟨f, rfl⟩)
    (derivative_preserves_relation k p)

@[simp] lemma derivative_mk (f : Polynomial k) :
    derivative k p (AdjoinRoot.mk (X ^ p : Polynomial k) f) =
      AdjoinRoot.mk (X ^ p : Polynomial k) (Polynomial.derivative' f) :=
  Derivation.liftOfSurjective_apply
    (f := AdjoinRoot.mkₐ (X ^ p : Polynomial k)) _ (derivative_preserves_relation k p) f

@[simp] lemma derivative_t : derivative k p (t k p) = 1 := by
  rw [t, AdjoinRoot.root, derivative_mk]
  simp [Polynomial.derivative']

omit [CharP k p] in
/-- Every derivation of this monogenic algebra is determined by its value on t. -/
lemma ext_t {d e : Algebra k p} (h : d (t k p) = e (t k p)) : d = e := by
  apply Derivation.ext_of_adjoin_eq_top {t k p}
    (AdjoinRoot.adjoinRoot_eq_top)
  exact Set.eqOn_singleton.mpr h

/-- The free rank-one module of derivations, realized as actual derivations. -/
def coefficientEquiv : Truncated k p ≃ₗ[k] Algebra k p where
  toFun f := f • derivative k p
  invFun d := d (t k p)
  left_inv f := by simp [Derivation.smul_apply]
  right_inv d := by apply ext_t; simp [Derivation.smul_apply]
  map_add' f g := add_smul f g _
  map_smul' a f := by
    ext x
    simp only [Derivation.smul_apply]
    exact smul_assoc a f _

@[simp] lemma coefficientEquiv_apply (f : Truncated k p) :
    coefficientEquiv k p f = f • derivative k p := rfl

/-- The polynomial power basis, with Fin p rather than Fin (natDegree X^p). -/
def truncatedBasis : Basis (Fin p) k (Truncated k p) :=
  ((AdjoinRoot.powerBasis' (monic_X_pow p : (X ^ p : Polynomial k).Monic)).basis).reindex
    (finCongr (natDegree_X_pow p))

omit [CharP k p] in
@[simp] lemma truncatedBasis_apply (i : Fin p) :
    truncatedBasis k p i = t k p ^ (i : ℕ) := by
  simp only [truncatedBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- e_{i-1} = t^i D. -/
def basis : Basis (Fin p) k (Algebra k p) :=
  (truncatedBasis k p).map (coefficientEquiv k p)

@[simp] lemma basis_apply (i : Fin p) :
    basis k p i = t k p ^ (i : ℕ) • derivative k p := by
  simp [basis]

@[simp] lemma basis_apply_t (i : Fin p) :
    basis k p i (t k p) = t k p ^ (i : ℕ) := by
  simp [Derivation.smul_apply]

lemma basis_apply_eq (i : Fin p) (hp : 0 < p) (x : Truncated k p) :
    basis k p i x = t k p ^ (i : ℕ) * basis k p ⟨0, hp⟩ x := by
  simp [basis_apply, Derivation.smul_apply, smul_eq_mul]

omit [CharP k p] in
lemma t_pow_p : t k p ^ p = 0 := by
  have h := (AdjoinRoot.mk_self (f := (X ^ p : Polynomial k)))
  simpa only [map_pow, AdjoinRoot.mk_X, t] using h

omit [CharP k p] in
lemma t_pow_eq_zero {n : ℕ} (h : p ≤ n) : t k p ^ n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, t_pow_p, zero_mul]

lemma mul_derivative_pow (i j : ℕ) :
    t k p ^ i * derivative k p (t k p ^ j) =
      (j : k) • t k p ^ (i + j - 1) := by
  by_cases hj : j = 0
  · simp [hj]
  · rw [(derivative k p).leibniz_pow, derivative_t]
    simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
    rw [mul_left_comm, ← pow_add]
    have he : i + (j - 1) = i + j - 1 := by omega
    rw [he]
    simp [Algebra.smul_def]

lemma basis_bracket_t (i j : Fin p) :
    ⁅basis k p i, basis k p j⁆ (t k p) =
      ((j : ℕ) - (i : ℕ) : k) • t k p ^ ((i : ℕ) + (j : ℕ) - 1) := by
  rw [Derivation.commutator_apply, basis_apply_t, basis_apply_t]
  simp only [basis_apply, Derivation.smul_apply, smul_eq_mul]
  rw [mul_derivative_pow, mul_derivative_pow]
  rw [Nat.add_comm (j : ℕ) (i : ℕ), ← sub_smul]

lemma basis_bracket (i j : Fin p) :
    ⁅basis k p i, basis k p j⁆ =
      ((j : ℕ) - (i : ℕ) : k) •
        basisAt (basis k p) ((i : ℕ) + (j : ℕ) - 2 : ℤ) := by
  apply ext_t k p
  rw [basis_bracket_t, Derivation.smul_apply]
  unfold basisAt
  split_ifs with h
  · rw [basis_apply_t]
    congr 2
    dsimp only
    omega
  · by_cases hzero : (i : ℕ) + (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by omega
      have hj : (j : ℕ) = 0 := by omega
      simp [hi, hj]
    · have hp : p ≤ (i : ℕ) + (j : ℕ) - 1 := by omega
      rw [t_pow_eq_zero k p hp]
      simp

lemma basis_bracket_of_bounds (i j : Fin p) (_hpos : 0 < (i : ℕ) + (j : ℕ))
    (hlt : (i : ℕ) + (j : ℕ) - 1 < p) :
    ⁅basis k p i, basis k p j⁆ =
      ((j : ℕ) - (i : ℕ) : k) • basis k p ⟨(i : ℕ) + (j : ℕ) - 1, hlt⟩ := by
  apply ext_t k p
  simp only [basis_bracket_t, Derivation.smul_apply, basis_apply_t]

lemma basis_weight (hp : 1 < p) (i : Fin p) :
    ⁅basis k p ⟨1, hp⟩, basis k p i⁆ = ((i : ℕ) - 1 : k) • basis k p i := by
  apply ext_t k p
  rw [basis_bracket_t, Derivation.smul_apply, basis_apply_t]
  simp

lemma weights_injective : Function.Injective (fun i : Fin p => ((i : ℕ) - 1 : k)) := by
  intro i j h
  apply Fin.ext
  exact CharP.natCast_injOn_Iio k p i.isLt j.isLt (by simpa using congrArg (fun a : k => a + 1) h)

/-- If an ideal contains no basis vector, its quotient still has p independent
weight vectors; hence the ideal is zero. This uses distinct ad(e₀)-weights. -/
lemma exists_basis_mem (hp : 1 < p) (I : LieIdeal k (Algebra k p)) (hI : I ≠ ⊥) :
    ∃ i, basis k p i ∈ I := by
  classical
  by_contra hn
  push Not at hn
  let q := I.toSubmodule.mkQ
  let f := LieSubmodule.Quotient.actionAsEndoMap I (basis k p ⟨1, hp⟩)
  have hli : LinearIndependent k (fun i => q (basis k p i)) := by
    apply Module.End.eigenvectors_linearIndependent' f _ (weights_injective k p)
    intro i
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      change q ⁅basis k p ⟨1, hp⟩, basis k p i⁆ = _
      rw [basis_weight, map_smul]
    · exact fun h => hn i ((Submodule.Quotient.mk_eq_zero _).mp h)
  apply hI
  apply le_antisymm _ bot_le
  intro x hx
  have hrel : ∑ i : Fin p, (basis k p).repr x i • q (basis k p i) = 0 := by
    simp only [← map_smul, ← map_sum]
    rw [(basis k p).sum_repr]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hc := Fintype.linearIndependent_iff.mp hli _ hrel
  have hx0 : x = 0 := by
    apply (basis k p).repr.injective
    ext i
    simpa using hc i
  simp [hx0]

lemma natCast_ne_zero {n : ℕ} (hn : n < p) (hpos : 0 < n) : (n : k) ≠ 0 := by
  intro h
  have hh := CharP.natCast_injOn_Iio k p hn (by omega : 0 < p) (by simpa using h)
  omega

lemma basis_zero_mem (hp : 1 < p) (I : LieIdeal k (Algebra k p))
    (i : Fin p) (hi : basis k p i ∈ I) : basis k p ⟨0, by omega⟩ ∈ I := by
  have hdown : ∀ n (hn : n < p), basis k p ⟨n, hn⟩ ∈ I →
      basis k p ⟨0, by omega⟩ ∈ I := by
    intro n
    induction n with
    | zero => intro hn hm; exact hm
    | succ n ih =>
      intro hn hm
      apply ih (by omega)
      have hbr := basis_bracket_of_bounds k p ⟨0, by omega⟩ ⟨n+1, hn⟩
        (by simp) (by simpa using (show n < p by omega))
      simp only [Nat.zero_add, Nat.add_sub_cancel,
        Nat.cast_zero, sub_zero] at hbr
      have hmem := I.lie_mem (x := basis k p ⟨0, by omega⟩) hm
      rw [hbr] at hmem
      exact (I.toSubmodule.smul_mem_iff (natCast_ne_zero k p hn (by omega))).mp hmem
  exact hdown i i.isLt hi

lemma ideal_eq_top [Fact p.Prime] (hp : 3 < p) (I : LieIdeal k (Algebra k p))
    (hzero : basis k p ⟨0, by omega⟩ ∈ I) : I = ⊤ := by
  have hlow : ∀ (n : ℕ) (hn : n + 1 < p), basis k p ⟨n, by omega⟩ ∈ I := by
    intro n hn
    have hbr := basis_bracket_of_bounds k p ⟨0, by omega⟩ ⟨n+1, hn⟩
      (by simp) (by simpa using (show n < p by omega))
    simp only [Nat.zero_add, Nat.add_sub_cancel,
      Nat.cast_zero, sub_zero] at hbr
    have hmem := lie_mem_left k (Algebra k p) I _ (basis k p ⟨n+1, hn⟩) hzero
    rw [hbr] at hmem
    exact (I.toSubmodule.smul_mem_iff (natCast_ne_zero k p hn (by omega))).mp hmem
  have hlast : basis k p ⟨p-1, by omega⟩ ∈ I := by
    have hbr := basis_bracket_of_bounds k p ⟨2, by omega⟩ ⟨p-2, by omega⟩
      (by simp) (by simp; omega)
    have hidx : 2 + (p-2) - 1 = p-1 := by omega
    simp only [hidx] at hbr
    have hmem := I.lie_mem (x := basis k p ⟨2, by omega⟩) (hlow (p-2) (by omega))
    rw [hbr] at hmem
    apply (I.toSubmodule.smul_mem_iff ?_).mp hmem
    have hc : ((p-2 : ℕ) : k) - (2 : k) = ((p-4 : ℕ) : k) := by
      have hnat : p - 2 = (p - 4) + 2 := by omega
      simp [hnat]
    simp only [Nat.cast_ofNat] at *
    rw [hc]
    exact natCast_ne_zero k p (by omega) (by
      have hprime : p.Prime := Fact.out
      have hp4 : p ≠ 4 := by
        intro h
        exact (by decide : ¬ Nat.Prime 4) (h ▸ hprime)
      omega)
  apply top_unique
  intro x _
  rw [← (basis k p).sum_repr x]
  apply I.toSubmodule.sum_mem
  intro i _
  apply I.smul_mem
  by_cases hi : (i : ℕ) + 1 < p
  · exact hlow i hi
  · have he : i = ⟨p-1, by omega⟩ := by apply Fin.ext; dsimp; omega
    simpa [he] using hlast

/-- A division-free sum-of-squares identity, valid in every coefficient field. -/
lemma sum_weights_sq_aux (n : ℕ) :
    (6 : k) * (∑ i ∈ Finset.range n, ((i : k) - 1)^2) =
      (n : k) * (2 * (n : k)^2 - 9 * (n : k) + 13) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

lemma sum_weights_sq (hp : 3 < p) :
    ∑ i : Fin p, ((i : ℕ) - 1 : k)^2 = 0 := by
  have hh := sum_weights_sq_aux k p
  have hsum : (6 : k) * (∑ i : Fin p, ((i : ℕ) - 1 : k)^2) = 0 := by
    simpa only [← Fin.sum_univ_eq_sum_range, CharP.cast_eq_zero k p, zero_mul] using hh
  have h2 : (2 : k) ≠ 0 := natCast_ne_zero k p (by omega : 2 < p) (by decide)
  have h3 : (3 : k) ≠ 0 := natCast_ne_zero k p (by omega : 3 < p) (by decide)
  have h6 : (6 : k) ≠ 0 := by
    have : (2 : k) * 3 ≠ 0 := mul_ne_zero h2 h3
    norm_num at this ⊢
    exact this
  exact (mul_eq_zero.mp hsum).resolve_left h6

lemma killing_weight_zero (hp : 3 < p) :
    killingForm k (Algebra k p) (basis k p ⟨1, by omega⟩)
      (basis k p ⟨1, by omega⟩) = 0 := by
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace k (basis k p)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, LieAlgebra.ad_apply, basis_weight k p (by omega),
    map_smul, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_apply, ite_true, smul_eq_mul, mul_one]
  simpa only [pow_two] using sum_weights_sq k p hp

lemma killing_basis_weight_zero (hp : 3 < p) (i : Fin p) :
    killingForm k (Algebra k p) (basis k p i) (basis k p ⟨1, by omega⟩) = 0 := by
  by_cases hi : i = ⟨1, by omega⟩
  · subst i; exact killing_weight_zero k p hp
  · have hne : ((i : ℕ) - 1 : k) ≠ 0 := by
      intro h
      apply hi
      apply weights_injective k p
      simpa using h
    have hh := LieModule.traceForm_apply_lie_apply' k (Algebra k p) (Algebra k p)
      (basis k p ⟨1, by omega⟩) (basis k p i) (basis k p ⟨1, by omega⟩)
    have hprod : ((i : ℕ) - 1 : k) *
        killingForm k (Algebra k p) (basis k p i) (basis k p ⟨1, by omega⟩) = 0 := by
      simpa only [basis_weight k p (by omega), lie_self, map_smul,
        LinearMap.smul_apply, smul_eq_mul, map_zero, neg_zero, Nat.cast_one,
        sub_self, zero_mul] using hh
    exact (mul_eq_zero.mp hprod).resolve_left hne

lemma killing_eq_zero [Fact p.Prime] (hp : 3 < p) (x y : Algebra k p) :
    killingForm k (Algebra k p) x y = 0 := by
  let I : LieIdeal k (Algebra k p) := LieIdeal.killingCompl k (Algebra k p) ⊤
  have hweight : basis k p ⟨1, by omega⟩ ∈ I := by
    apply (LieIdeal.mem_killingCompl k (Algebra k p) ⊤).mpr
    intro z _
    rw [← (basis k p).sum_repr z]
    simp only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, killing_basis_weight_zero k p hp,
      mul_zero, Finset.sum_const_zero]
  have htop : I = ⊤ := ideal_eq_top k p hp I
    (basis_zero_mem k p (by omega) I _ hweight)
  have hy : y ∈ I := by rw [htop]; trivial
  exact ((LieIdeal.mem_killingCompl k (Algebra k p) ⊤).mp hy) x (by trivial)

end LieAlgebrasAndRepresentations.Witt

namespace LieAlgebrasAndRepresentations

open Witt

theorem witt_presentation (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (_hp : 3 < p) :
    ∃ b : Basis (Fin p) k (Witt.Algebra k p), IsPresentation b :=
  ⟨Witt.basis k p, basis_apply_t k p, basis_apply_eq k p, basis_bracket k p⟩

theorem witt_simplicity (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hp : 3 < p) :
    (∃ x y : Witt.Algebra k p, ⁅x, y⁆ ≠ 0) ∧
      ∀ I : LieIdeal k (Witt.Algebra k p), I = ⊥ ∨ I = ⊤ := by
  constructor
  · refine ⟨Witt.basis k p ⟨0, by omega⟩, Witt.basis k p ⟨1, by omega⟩, ?_⟩
    have hbr := basis_bracket_of_bounds k p ⟨0, by omega⟩ ⟨1, by omega⟩
      (by simp) (by simp; omega)
    simp only [Nat.cast_zero, Nat.cast_one, sub_zero, one_smul] at hbr
    rw [hbr]
    exact (Witt.basis k p).ne_zero _
  · intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · obtain ⟨i, hi⟩ := exists_basis_mem k p (by omega) I hI
      exact Or.inr (ideal_eq_top k p hp I (basis_zero_mem k p (by omega) I i hi))

theorem witt_killing (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hp : 3 < p) (x y : Witt.Algebra k p) :
    killingForm k (Witt.Algebra k p) x y = 0 := killing_eq_zero k p hp x y

theorem witt_boundary (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hp : 3 < p) :
    Module.finrank k (Witt.Algebra k p) = p ∧ ¬ LieAlgebra.IsSolvable (Witt.Algebra k p) := by
  constructor
  · simpa using Module.finrank_eq_card_basis (Witt.basis k p)
  · intro hs
    let : LieAlgebra.IsSolvable (Witt.Algebra k p) := hs
    obtain ⟨⟨x, y, hxy⟩, hsimple⟩ := witt_simplicity k p hp
    let : Nontrivial (Witt.Algebra k p) :=
      ⟨⟨⁅x, y⁆, 0, hxy⟩⟩
    have hlt := LieAlgebra.derivedSeries_lt_top_of_solvable k (Witt.Algebra k p)
    have hbot := (hsimple (LieAlgebra.derivedSeries k (Witt.Algebra k p) 1)).resolve_right
      (ne_of_lt hlt)
    have hmem : ⁅x, y⁆ ∈ LieAlgebra.derivedSeries k (Witt.Algebra k p) 1 :=
      LieSubmodule.lie_mem_lie (by trivial) (by trivial)
    rw [hbot] at hmem
    exact hxy hmem

end LieAlgebrasAndRepresentations

