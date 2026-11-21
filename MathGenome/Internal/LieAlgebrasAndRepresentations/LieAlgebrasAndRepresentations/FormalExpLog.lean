import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalExpLog
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompletedPrimitives
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.Polynomial.Div

noncomputable section
namespace LieAlgebrasAndRepresentations.FormalExpLog
open CompletedPrimitives
open scoped TensorProduct
universe u v

/-- The tensor-degree exponential, defined for all inputs and used on the
positive-degree domain. -/
def formalExp (k : Type u) (V : Type v) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] : Completion k V → Completion k V :=
  exponential (generators k V)

/-- The tensor-degree logarithm, used on series with constant coefficient one. -/
def formalLog (k : Type u) (V : Type v) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] : Completion k V → Completion k V :=
  logarithm (generators k V)

section Evaluation
variable {k B C : Type*} [CommRing k] [Ring B] [Ring C]
    [Algebra k B] [Algebra k C]

@[simp] theorem seriesEval_coeff (G : Submodule k B) (c : ℕ → k)
    (p : degreeSeries G) (n : ℕ) :
    PowerSeries.coeff n (seriesEval G c p).val =
      ∑ m ∈ Finset.range (n+1), c m • PowerSeries.coeff n (p.val ^ m) :=
  by simp only [seriesEval, PowerSeries.coeff_mk]

/-- Positivity implies local finiteness, over a noncommutative coefficient
ring. No domain or characteristic assumption is used here. -/
theorem coeff_pow_eq_zero {p : PowerSeries B} (hp : PowerSeries.coeff 0 p = 0)
    {n m : ℕ} (h : n < m) : PowerSeries.coeff n (p ^ m) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  apply lt_of_lt_of_le (show (n : ℕ∞) < m by exact_mod_cast h)
  exact PowerSeries.le_order_pow_of_constantCoeff_eq_zero m (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hp)

/-- The finite formula is unchanged by increasing the cutoff past the degree
being computed. This explicitly justifies every infinite sum degreewise. -/
theorem seriesEval_coeff_cutoff (G : Submodule k B) (c : ℕ → k)
    (p : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0)
    (n N : ℕ) (hN : n < N) :
    PowerSeries.coeff n (seriesEval G c p).val =
      ∑ m ∈ Finset.range N, c m • PowerSeries.coeff n (p.val ^ m) := by
  rw [seriesEval_coeff]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro m hm hm'
  have hnm : n < m := by
    simp only [Finset.mem_range, not_lt] at hm'
    omega
  rw [coeff_pow_eq_zero hp hnm, smul_zero]

@[simp] theorem seriesEval_constant (G : Submodule k B) (c : ℕ → k)
    (p : degreeSeries G) :
    PowerSeries.coeff 0 (seriesEval G c p).val = algebraMap k B (c 0) := by
  simp [seriesEval_coeff, Algebra.algebraMap_eq_smul_one]

/-- Coefficientwise extension of an algebra map commutes with scalar-series
evaluation. Hence it commutes with both formal exp and formal log. -/
theorem map_seriesEval (G : Submodule k B) (H : Submodule k C)
    (f : B →ₐ[k] C) (hf : G.map f.toLinearMap ≤ H)
    (c : ℕ → k) (p : degreeSeries G) :
    completionMap G H f hf (seriesEval G c p) =
      seriesEval H c (completionMap G H f hf p) := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  rw [completionMap_coeff, seriesEval_coeff, seriesEval_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_smul]
  congr 1
  change f (PowerSeries.coeff n (p.val ^ m)) =
    PowerSeries.coeff n ((PowerSeries.map f.toRingHom p.val) ^ m)
  rw [← map_pow, PowerSeries.coeff_map]
  rfl

end Evaluation

section Field
variable {k B C : Type*} [Field k] [Ring B] [Ring C]
    [Algebra k B] [Algebra k C]

@[simp] theorem exponential_constant (G : Submodule k B) (p : degreeSeries G) :
    PowerSeries.coeff 0 (exponential G p).val = 1 := by
  simp [exponential, expCoefficients]

@[simp] theorem logarithm_constant (G : Submodule k B) (g : degreeSeries G) :
    PowerSeries.coeff 0 (logarithm G g).val = 0 := by
  simp [logarithm, logCoefficients]

theorem map_exponential (G : Submodule k B) (H : Submodule k C)
    (f : B →ₐ[k] C) (hf : G.map f.toLinearMap ≤ H) (p : degreeSeries G) :
    completionMap G H f hf (exponential G p) =
      exponential H (completionMap G H f hf p) := map_seriesEval G H f hf _ p

theorem map_logarithm (G : Submodule k B) (H : Submodule k C)
    (f : B →ₐ[k] C) (hf : G.map f.toLinearMap ≤ H) (g : degreeSeries G) :
    completionMap G H f hf (logarithm G g) =
      logarithm H (completionMap G H f hf g) := by
  unfold logarithm
  rw [map_seriesEval, map_sub, map_one]

end Field

/-- Degreewise convergence statement for the original tensor completion. -/
theorem degreewise_spec :
    Specs.LieAlgebrasAndRepresentations.FormalExpLog.degreewiseExpected.{u,v} := by
  intro k V _ _ _ _ p hp
  exact ⟨fun n m h => coeff_pow_eq_zero hp h,
    fun c n N h => seriesEval_coeff_cutoff _ c p hp n N h⟩

namespace NilpotentEvaluation
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Nilpotent polynomial evaluation ignores all terms at and above the
nilpotence exponent. -/
theorem aeval_trunc (N : ℕ) (a : B) (ha : a ^ (N+1) = 0) (p : Polynomial k) :
    Polynomial.aeval a (PowerSeries.trunc (N+1) (p : PowerSeries k)) =
      Polynomial.aeval a p := by
  have hd : Polynomial.X ^ (N+1) ∣ p - PowerSeries.trunc (N+1) (p : PowerSeries k) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    simp [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hd]
  symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  obtain ⟨q, hq⟩ := hd
  rw [hq, map_mul, map_pow, Polynomial.aeval_X, ha, zero_mul]

/-- Evaluate a scalar power series at a nilpotent element of an arbitrary
associative algebra, using a finite truncation. -/
def hom (N : ℕ) (a : B) (ha : a ^ (N+1) = 0) : PowerSeries k →ₐ[k] B where
  toFun f := Polynomial.aeval a (PowerSeries.trunc (N+1) f)
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp
  map_mul' f g := by
    rw [← map_mul, ← aeval_trunc N a ha
      (PowerSeries.trunc (N+1) f * PowerSeries.trunc (N+1) g)]
    congr 1
    simp only [Polynomial.coe_mul, PowerSeries.trunc_trunc_mul_trunc]
  commutes' c := by simp

@[simp] theorem hom_X (N : ℕ) (a : B) (ha : a ^ (N+1) = 0) :
    hom N a ha (PowerSeries.X : PowerSeries k) = a := by
  change Polynomial.aeval a (PowerSeries.trunc (N+1) (PowerSeries.X : PowerSeries k)) = a
  rw [← Polynomial.coe_X, aeval_trunc N a ha]
  simp

/-- Explicit finite evaluation formula. -/
theorem hom_eq_sum (N : ℕ) (a : B) (ha : a ^ (N+1) = 0) (f : PowerSeries k) :
    hom N a ha f = ∑ m ∈ Finset.range (N+1), PowerSeries.coeff m f • a ^ m := by
  change Polynomial.aeval a (PowerSeries.trunc (N+1) f) = _
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  exact (Algebra.smul_def _ _).symm

/-- Substitution has a finite coefficient formula below every fixed cutoff. -/
theorem trunc_subst (N : ℕ) (f g : PowerSeries k)
    (hg : PowerSeries.coeff 0 g = 0) :
    PowerSeries.trunc (N+1) (f.subst g) =
      PowerSeries.trunc (N+1)
        (∑ m ∈ Finset.range (N+1), PowerSeries.coeff m f • g ^ m) := by
  ext n
  simp only [PowerSeries.coeff_trunc]
  split_ifs with hn
  · rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero'
      (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg))]
    rw [map_sum]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro m hm
    by_contra h
    have hnm : n < m := by
      have hmN : N+1 ≤ m := by simpa using h
      omega
    exact hm (by dsimp; rw [coeff_pow_eq_zero hg hnm, mul_zero])
  · rfl

/-- Scalar substitution may be evaluated at a nilpotent element even when
the target coefficient algebra is noncommutative. -/
theorem hom_subst (N : ℕ) (a : B) (ha : a ^ (N+1) = 0)
    (f g : PowerSeries k) (hg : PowerSeries.coeff 0 g = 0) :
    hom N a ha (f.subst g) =
      ∑ m ∈ Finset.range (N+1), PowerSeries.coeff m f • (hom N a ha g) ^ m := by
  have ht := trunc_subst N f g hg
  change Polynomial.aeval a (PowerSeries.trunc (N+1) (f.subst g)) = _
  rw [ht]
  change hom N a ha (∑ m ∈ Finset.range (N+1), PowerSeries.coeff m f • g ^ m) = _
  simp only [map_sum, map_smul, map_pow]

theorem hom_positive_power_zero (N : ℕ) (a : B) (ha : a ^ (N+1) = 0)
    (g : PowerSeries k) (hg : PowerSeries.coeff 0 g = 0) :
    (hom N a ha g) ^ (N+1) = 0 := by
  rw [← map_pow]
  have ht : PowerSeries.trunc (N+1) (g ^ (N+1)) = 0 := by
    ext n
    simp only [PowerSeries.coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hn
    · exact coeff_pow_eq_zero hg hn
    · rfl
  change Polynomial.aeval a (PowerSeries.trunc (N+1) (g ^ (N+1))) = 0
  rw [ht, map_zero]

theorem hom_comp (N : ℕ) (a : B) (ha : a ^ (N+1) = 0)
    (f g : PowerSeries k) (hg : PowerSeries.coeff 0 g = 0)
    (hga : (hom N a ha g) ^ (N+1) = 0) :
    hom N (hom N a ha g) hga f = hom N a ha (f.subst g) := by
  rw [hom_eq_sum, hom_subst N a ha f g hg]

end NilpotentEvaluation


namespace Jets

/-- Equality of all coefficients below a fixed cutoff is a ring congruence,
also for noncommutative coefficient rings. -/
def congruence (B : Type*) [Ring B] (N : ℕ) : RingCon (PowerSeries B) where
  r := fun p q => ∀ n < N, PowerSeries.coeff n p = PowerSeries.coeff n q
  iseqv := ⟨fun _ _ _ => rfl, fun h n hn => (h n hn).symm,
    fun h h' n hn => (h n hn).trans (h' n hn)⟩
  add' := by
    intro p q r s h h' n hn
    simp only [map_add, h n hn, h' n hn]
  mul' := by
    intro p q r s h h' n hn
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have hsum := Finset.mem_antidiagonal.mp hij
    rw [h ij.1 (by omega), h' ij.2 (by omega)]

abbrev Jet (B : Type*) [Ring B] (N : ℕ) := (congruence B N).Quotient

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Quotient to a finite jet, retaining the k-algebra structure. -/
def project (N : ℕ) : PowerSeries B →ₐ[k] Jet B N := (congruence B N).mkₐ k

theorem project_eq_iff (N : ℕ) (p q : PowerSeries B) :
    project (k := k) N p = project (k := k) N q ↔
      ∀ n < N, PowerSeries.coeff n p = PowerSeries.coeff n q :=
  (congruence B N).eq

theorem project_power_zero (N : ℕ) (p : PowerSeries B)
    (hp : PowerSeries.coeff 0 p = 0) : (project (k := k) N p) ^ N = 0 := by
  rw [← map_pow, ← map_zero (project (k := k) N)]
  apply (project_eq_iff (k := k) N _ _).mpr
  intro n hn
  rw [coeff_pow_eq_zero hp hn, map_zero]

/-- Scalar-series evaluation is a finite polynomial evaluation in each jet. -/
theorem project_seriesEval (N : ℕ) (G : Submodule k B) (c : ℕ → k)
    (p : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0) :
    project (k := k) N (seriesEval G c p).val =
      ∑ m ∈ Finset.range N, c m • (project (k := k) N p.val) ^ m := by
  rw [show (∑ m ∈ Finset.range N, c m • (project (k := k) N p.val) ^ m) =
      project (k := k) N (∑ m ∈ Finset.range N, c m • p.val ^ m) by simp]
  apply (project_eq_iff (k := k) N _ _).mpr
  intro n hn
  rw [seriesEval_coeff_cutoff G c p hp n N hn, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact (PowerSeries.coeff_smul n (p.val ^ m) (c m)).symm

/-- Projecting any evaluated scalar series agrees with nilpotent evaluation
of the scalar power series in the finite jet algebra. -/
theorem project_eval (N : ℕ) (G : Submodule k B) (f : PowerSeries k)
    (p : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0) :
    project (k := k) (N+1) (seriesEval G (fun m => PowerSeries.coeff m f) p).val =
      NilpotentEvaluation.hom N (project (k := k) (N+1) p.val)
        (project_power_zero _ _ hp) f := by
  rw [project_seriesEval _ _ _ _ hp, NilpotentEvaluation.hom_eq_sum]


variable [CharZero k]

private theorem exp_coeff_eq (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.exp k) = expCoefficients k m := by
  simp [PowerSeries.coeff_exp, expCoefficients]

private theorem log_coeff_eq (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.log k) = logCoefficients k m := by
  simp only [PowerSeries.coeff_log, logCoefficients]
  split_ifs
  · rfl
  · simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]

theorem project_exp_eval (N : ℕ) (G : Submodule k B)
    (p : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0) :
    project (k := k) (N+1) (exponential G p).val =
      NilpotentEvaluation.hom N (project (k := k) (N+1) p.val)
        (project_power_zero _ _ hp) (PowerSeries.exp k) := by
  have h := project_eval N G (PowerSeries.exp k) p hp
  simpa only [exp_coeff_eq, exponential] using h

theorem project_log_eval (N : ℕ) (G : Submodule k B)
    (g : degreeSeries G) (hg : PowerSeries.coeff 0 g.val = 1) :
    project (k := k) (N+1) (logarithm G g).val =
      NilpotentEvaluation.hom N (project (k := k) (N+1) (g-1).val)
        (project_power_zero _ _ (by
          change PowerSeries.coeff 0 (g.val-1) = 0
          rw [map_sub, hg]
          simp))
        (PowerSeries.log k) := by
  have h0 : PowerSeries.coeff 0 (g-1).val = 0 := by
    change PowerSeries.coeff 0 (g.val-1) = 0
    rw [map_sub, hg, PowerSeries.coeff_one, ite_eq_left rfl, sub_self]
  have h := project_eval N G (PowerSeries.log k) (g-1) h0
  simpa only [log_coeff_eq, logarithm] using h


/-- Compatibility with the existing nilpotent exponential, after restricting
scalars from the characteristic-zero field to the rationals. -/
theorem project_exponential (N : ℕ) (G : Submodule k B)
    (p : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0) :
    letI : Algebra ℚ (Jet B N) := Algebra.compHom (Jet B N) (algebraMap ℚ k)
    project (k := k) N (exponential G p).val =
      IsNilpotent.exp (project (k := k) N p.val) := by
  letI : Algebra ℚ (Jet B N) := Algebra.compHom (Jet B N) (algebraMap ℚ k)
  rw [IsNilpotent.exp_eq_sum (project_power_zero N p.val hp)]
  rw [exponential, project_seriesEval N G _ p hp]
  apply Finset.sum_congr rfl
  intro m hm
  change (m.factorial : k)⁻¹ • (project (k := k) N p.val) ^ m =
    algebraMap ℚ k ((m.factorial : ℚ)⁻¹) • (project (k := k) N p.val) ^ m
  congr 1
  simp

/-- The commuting exponential identity in the full degree completion follows
by testing in every finite jet. -/
theorem commutingExp_laws (G : Submodule k B) : CommutingExpLaws G := by
  intro p q hp hq hcomm
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  apply (project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
  letI : Algebra ℚ (Jet B (n+1)) := Algebra.compHom (Jet B (n+1)) (algebraMap ℚ k)
  have hpq : PowerSeries.coeff 0 ((p+q).val) = 0 := by
    change PowerSeries.coeff 0 (p.val + q.val) = 0
    rw [map_add, hp, hq, add_zero]
  change project (k := k) (n+1) (exponential G (p+q)).val =
    project (k := k) (n+1) ((exponential G p).val * (exponential G q).val)
  rw [map_mul, project_exponential _ _ _ hpq, project_exponential _ _ _ hp,
    project_exponential _ _ _ hq]
  change IsNilpotent.exp (project (k := k) (n+1) (p.val+q.val)) = _
  rw [map_add]
  apply IsNilpotent.exp_add_of_commute
  · exact ((show Commute p.val q.val from congrArg Subtype.val hcomm).map
      (project (k := k) (n+1)))
  · exact ⟨n+1, project_power_zero _ _ hp⟩
  · exact ⟨n+1, project_power_zero _ _ hq⟩

/-- The scalar inverse identities lift to a noncommutative completion by
finite nilpotent evaluation. -/
theorem inverse_laws (G : Submodule k B) : InverseLaws G := by
  constructor
  · intro p hp
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    apply (project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    let a := project (k := k) (n+1) p.val
    have ha : a ^ (n+1) = 0 := project_power_zero _ _ hp
    let E := NilpotentEvaluation.hom (k := k) n a ha
    have h0 : PowerSeries.coeff 0 (PowerSeries.exp k - 1) = 0 := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
    have hz : (E (PowerSeries.exp k - 1)) ^ (n+1) = 0 :=
      NilpotentEvaluation.hom_positive_power_zero n a ha _ h0
    have he : project (k := k) (n+1) (exponential G p - 1).val =
        E (PowerSeries.exp k - 1) := by
      change project (k := k) (n+1) ((exponential G p).val - 1) = _
      rw [map_sub, map_one, project_exp_eval _ _ _ hp]
      simp only [map_sub, map_one]
      rfl
    rw [project_log_eval n G _ (exponential_constant _ _)]
    calc
      _ = NilpotentEvaluation.hom n (E (PowerSeries.exp k - 1)) hz (PowerSeries.log k) := by
        congr 2
      _ = E ((PowerSeries.log k).subst (PowerSeries.exp k - 1)) :=
        NilpotentEvaluation.hom_comp n a ha _ _ h0 hz
      _ = a := by rw [PowerSeries.subst_log_exp_sub_one]; exact NilpotentEvaluation.hom_X _ _ _
  · intro g hg
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    apply (project_eq_iff (k := k) (n+1) _ _).mp ?_ n (by omega)
    have hg0 : PowerSeries.coeff 0 (g-1).val = 0 := by
      change PowerSeries.coeff 0 (g.val-1) = 0
      rw [map_sub, hg]
      simp
    let a := project (k := k) (n+1) (g-1).val
    have ha : a ^ (n+1) = 0 := project_power_zero _ _ hg0
    let E := NilpotentEvaluation.hom (k := k) n a ha
    have h0 : PowerSeries.coeff 0 (PowerSeries.log k) = 0 := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
    have hz : (E (PowerSeries.log k)) ^ (n+1) = 0 :=
      NilpotentEvaluation.hom_positive_power_zero n a ha _ h0
    rw [project_exp_eval n G _ (logarithm_constant _ _)]
    calc
      _ = NilpotentEvaluation.hom n (E (PowerSeries.log k)) hz (PowerSeries.exp k) := by
        congr 2
        exact project_log_eval n G g hg
      _ = E ((PowerSeries.exp k).subst (PowerSeries.log k)) :=
        NilpotentEvaluation.hom_comp n a ha _ _ h0 hz
      _ = 1 + a := by
        rw [PowerSeries.subst_exp_log, map_add, map_one]
        rw [NilpotentEvaluation.hom_X]
      _ = project (k := k) (n+1) g.val := by
        change 1 + project (k := k) (n+1) (g.val - 1) = _
        rw [map_sub, map_one]
        abel

end Jets

section Reduction
variable (k : Type u) (V : Type v) [Field k] [CharZero k] [AddCommGroup V] [Module k V]

/-- The two completed tensor factors commute, without any commutativity
assumption on the tensor algebra. -/
theorem completedLeft_right_commute (p q : Completion k V) :
    Commute (completedLeft k V p) (completedRight k V q) := by
  change completedLeft k V p * completedRight k V q =
    completedRight k V q * completedLeft k V p
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  simp only [Subalgebra.coe_mul, PowerSeries.coeff_mul,
    completedLeft_coeff, completedRight_coeff, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  exact Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun ij => PowerSeries.coeff ij.2 p.val ⊗ₜ[k] PowerSeries.coeff ij.1 q.val)

private theorem exponential_injective_positive {B : Type*} [Ring B] [Algebra k B]
    (G : Submodule k B) (hI : InverseLaws G)
    (p q : degreeSeries G) (hp : PowerSeries.coeff 0 p.val = 0)
    (hq : PowerSeries.coeff 0 q.val = 0)
    (h : exponential G p = exponential G q) : p = q := by
  rw [← hI.1 p hp, ← hI.1 q hq, h]

@[simp] theorem completedCoproduct_exponential (p : Completion k V) :
    completedCoproduct k V (exponential (generators k V) p) =
      exponential (squareGenerators k V) (completedCoproduct k V p) :=
  map_exponential _ _ _ _ p

@[simp] theorem completedLeft_exponential (p : Completion k V) :
    completedLeft k V (exponential (generators k V) p) =
      exponential (squareGenerators k V) (completedLeft k V p) :=
  map_exponential _ _ _ _ p

@[simp] theorem completedRight_exponential (p : Completion k V) :
    completedRight k V (exponential (generators k V) p) =
      exponential (squareGenerators k V) (completedRight k V p) :=
  map_exponential _ _ _ _ p

private theorem left_positive (p : Completion k V) (h : PowerSeries.coeff 0 p.val = 0) :
    PowerSeries.coeff 0 (completedLeft k V p).val = 0 := by
  rw [completedLeft_coeff, h, TensorProduct.zero_tmul]

private theorem right_positive (p : Completion k V) (h : PowerSeries.coeff 0 p.val = 0) :
    PowerSeries.coeff 0 (completedRight k V p).val = 0 := by
  rw [completedRight_coeff, h, TensorProduct.tmul_zero]

/-- Assembly of the two algebraic formal-series identities into the primitive
and group-like assertions for the actual completed coproduct. The premises are the formal-series laws proved by the finite-jet
arguments above. -/
theorem hopf_of_formal_laws
    (hI : InverseLaws (generators k V))
    (hIS : InverseLaws (squareGenerators k V))
    (hC : CommutingExpLaws (squareGenerators k V)) :
    (∀ p, IsCompletedPrimitive k V p →
      IsGroupLike k V (completedCoproduct k V) (completedLeft k V) (completedRight k V)
        (exponential (generators k V) p)) ∧
    (∀ g, IsGroupLike k V (completedCoproduct k V) (completedLeft k V) (completedRight k V) g →
      IsCompletedPrimitive k V (logarithm (generators k V) g)) := by
  constructor
  · intro p hp
    have hp0 : PowerSeries.coeff 0 p.val = 0 := (completed_spec k V).1 p hp
    refine ⟨exponential_constant _ p, ?_⟩
    have hΔ := (completed_primitive_iff k V p).mp hp
    rw [completedCoproduct_exponential, hΔ]
    rw [hC _ _ (left_positive k V p hp0) (right_positive k V p hp0)
      (completedLeft_right_commute k V p p)]
    rw [completedLeft_exponential, completedRight_exponential]
  · intro g hg
    apply (completed_primitive_iff k V _).mpr
    apply exponential_injective_positive k (squareGenerators k V) hIS
    · change PowerSeries.coeff 0 (completionMap _ _ _ _ (logarithm _ g)).val = 0
      rw [completionMap_coeff, logarithm_constant, map_zero]
    · change PowerSeries.coeff 0
        ((completedLeft k V (logarithm _ g)).val + (completedRight k V (logarithm _ g)).val) = 0
      rw [map_add, left_positive k V _ (logarithm_constant _ _),
        right_positive k V _ (logarithm_constant _ _), add_zero]
    · have he : exponential (generators k V) (logarithm (generators k V) g) = g := hI.2 g hg.1
      rw [hC _ _ (left_positive k V _ (logarithm_constant _ _))
        (right_positive k V _ (logarithm_constant _ _)) (completedLeft_right_commute k V _ _)]
      rw [← completedCoproduct_exponential, ← completedLeft_exponential,
        ← completedRight_exponential, he]
      exact hg.2

/-- Building the required equivalence from the inverse laws and the two
coproduct assertions involves no extra finiteness condition. -/
theorem correspondence_of_formal_laws
    (hI : InverseLaws (generators k V))
    (hIS : InverseLaws (squareGenerators k V))
    (hC : CommutingExpLaws (squareGenerators k V)) :
    ∃ e : {p : Completion k V // Positive k V p ∧ IsCompletedPrimitive k V p} ≃
      {g : Completion k V // IsGroupLike k V (completedCoproduct k V)
        (completedLeft k V) (completedRight k V) g},
      (∀ p, (e p).val = exponential (generators k V) p.val) ∧
      (∀ g, (e.symm g).val = logarithm (generators k V) g.val) := by
  have hH := hopf_of_formal_laws k V hI hIS hC
  let e : {p : Completion k V // Positive k V p ∧ IsCompletedPrimitive k V p} ≃
      {g : Completion k V // IsGroupLike k V (completedCoproduct k V)
        (completedLeft k V) (completedRight k V) g} :=
    { toFun := fun p => ⟨exponential (generators k V) p.val, hH.1 _ p.property.2⟩
      invFun := fun g => ⟨logarithm (generators k V) g.val,
        logarithm_constant _ _, hH.2 _ g.property⟩
      left_inv := fun p => Subtype.ext (hI.1 _ p.property.1)
      right_inv := fun g => Subtype.ext (hI.2 _ g.property.1) }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end Reduction

/-- Inverse identities on all positive series and all series with constant
coefficient one, in the original tensor completion. -/
theorem inverse_spec :
    Specs.LieAlgebrasAndRepresentations.FormalExpLog.inverseExpected.{u,v} := by
  intro k V _ _ _ _
  exact Jets.inverse_laws (generators k V)

private theorem coefficient_maps_unique
    (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (Δ l r : Completion k V →ₐ[k] CompletedSquare k V)
    (hΔ : ∀ p n, PowerSeries.coeff n (Δ p).val =
      tensorCoproduct k V (PowerSeries.coeff n p.val))
    (hl : ∀ p n, PowerSeries.coeff n (l p).val = PowerSeries.coeff n p.val ⊗ₜ[k] 1)
    (hr : ∀ p n, PowerSeries.coeff n (r p).val = 1 ⊗ₜ[k] PowerSeries.coeff n p.val) :
    Δ = completedCoproduct k V ∧ l = completedLeft k V ∧ r = completedRight k V := by
  refine ⟨?_, ?_, ?_⟩
  · ext p : 1
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    rw [hΔ]
    exact (completionMap_coeff _ _ _ _ p n).symm
  · ext p : 1
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    rw [hl, completedLeft_coeff]
  · ext p : 1
    apply Subtype.ext
    apply PowerSeries.ext
    intro n
    rw [hr, completedRight_coeff]

/-- The coproduct of exp(p) is its completed tensor square, and the logarithm
of every group-like element with constant coefficient one is primitive. -/
theorem hopf_spec :
    Specs.LieAlgebrasAndRepresentations.FormalExpLog.hopfExpected.{u,v} := by
  intro k V _ _ _ _ Δ l r hΔ hl hr
  obtain ⟨rfl, rfl, rfl⟩ := coefficient_maps_unique k V Δ l r hΔ hl hr
  exact hopf_of_formal_laws k V (Jets.inverse_laws _) (Jets.inverse_laws _)
    (Jets.commutingExp_laws _)

/-- Formal exp and log give the asserted mutually inverse correspondence. -/
theorem correspondence_spec :
    Specs.LieAlgebrasAndRepresentations.FormalExpLog.correspondenceExpected.{u,v} := by
  intro k V _ _ _ _ Δ l r hΔ hl hr
  obtain ⟨rfl, rfl, rfl⟩ := coefficient_maps_unique k V Δ l r hΔ hl hr
  exact correspondence_of_formal_laws k V (Jets.inverse_laws _) (Jets.inverse_laws _)
    (Jets.commutingExp_laws _)

end LieAlgebrasAndRepresentations.FormalExpLog
