import MathGenome.Internal.MultivariableAnalysis.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.PolynomialUniqueness
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Finite polynomial uniqueness for the canonical Euclidean spaces. The proof
restricts each scalar coordinate to t ↦ t • v, removes its constant term by
continuity, and divides by t inductively. Polynomial extensionality over ℝ
then recovers every coefficient. Dimension zero is treated by evaluation. -/
noncomputable section
open Filter Topology Asymptotics
open scoped Polynomial BigOperators
namespace D04

theorem realPolynomial_zero_of_isLittleO (k : ℕ) (p : ℝ[X]) (hd : p.natDegree ≤ k)
    (ho : p.eval =o[𝓝[≠] (0 : ℝ)] (fun t => t^k)) : p = 0 := by
  have hz : p.eval 0 = 0 := by
    exact tendsto_nhds_unique (p.continuous.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
      (ho.tendsto_zero_of_tendsto ((continuous_id.pow k).tendsto 0 |>.mono_left nhdsWithin_le_nhds))
  induction k generalizing p with
  | zero =>
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hd)]
    simpa only [Polynomial.C_0, Polynomial.C_eq_zero, Polynomial.coeff_zero_eq_eval_zero] using hz
  | succ k ih =>
    obtain ⟨q, rfl⟩ := (Polynomial.X_dvd_iff (f := p)).mpr (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hz)
    by_cases hq : q = 0
    · simp [hq]
    have hqd : q.natDegree ≤ k := by
      rw [Polynomial.natDegree_X_mul hq] at hd
      omega
    have he : (fun t : ℝ => t * q.eval t) =o[𝓝[≠] (0 : ℝ)] (fun t => t^(k+1)) := by
      simpa using ho
    have hn : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
      exact (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ ({0} : Set ℝ)ᶜ).mono fun _ ht => ht
    have hh := (isLittleO_mul_iff_isLittleO_div hn).mp he
    have hsmall : q.eval =o[𝓝[≠] (0 : ℝ)] (fun t => t^k) := by
      apply hh.congr' (Filter.EventuallyEq.rfl)
      filter_upwards [hn] with t ht
      simp [pow_succ, ht]
    rw [ih q hqd hsmall (by simpa using (tendsto_nhds_unique
      (q.continuous.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
      (hsmall.tendsto_zero_of_tendsto ((continuous_id.pow k).tendsto 0 |>.mono_left nhdsWithin_le_nhds))))]
    simp

private def linePolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (v : E n) : ℝ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) p

private theorem linePolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (v : E n) (t : ℝ) :
    (linePolynomial p v).eval t = MvPolynomial.eval (fun i => (t • v) i) p := by
  have he : (Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X)) =
      MvPolynomial.eval (fun i => (t • v) i) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_evalRingHom, Polynomial.eval_C, MvPolynomial.eval_C]
    · intro i; simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, MvPolynomial.eval_X]
      change v i * t = t * v i
      exact mul_comm _ _
  exact DFunLike.congr_fun he p

private theorem linePolynomial_degree {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (v : E n) :
    (linePolynomial p v).natDegree ≤ p.totalDegree := by
  classical
  unfold linePolynomial
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  apply le_trans (Polynomial.natDegree_mul_le) ?_
  simp only [Polynomial.natDegree_C, zero_add]
  rw [Finsupp.prod]
  apply le_trans (Polynomial.natDegree_prod_le _ _) ?_
  apply le_trans (Finset.sum_le_sum fun i hi => ?_) (MvPolynomial.le_totalDegree hd)
  exact (Polynomial.natDegree_pow_le).trans (by
    have hh : (Polynomial.C (v i) * (Polynomial.X : ℝ[X])).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    simpa using Nat.mul_le_mul_left (d i) hh)

private theorem mvPolynomial_zero_of_isLittleO {n : ℕ} (hn : 0 < n) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hd : p.totalDegree ≤ k)
    (ho : (fun x : E n => MvPolynomial.eval (fun i => x i) p)
      =o[𝓝[≠] 0] (fun x => ‖x‖^k)) : p = 0 := by
  have H (v : E n) (hv : v ≠ 0) : linePolynomial p v = 0 := by
    have ht : Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝[≠] (0 : E n)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [eventually_mem_nhdsWithin] with t ht
        change t • v ≠ 0
        exact smul_ne_zero ht hv
    have hh := ho.comp_tendsto ht
    have hline : (linePolynomial p v).eval =o[𝓝[≠] (0 : ℝ)] (fun t => t^k) := by
      have hh' : (linePolynomial p v).eval =o[𝓝[≠] (0 : ℝ)] (fun t => ‖v‖^k * ‖t^k‖) := by
        simpa only [Function.comp_def, linePolynomial_eval, norm_smul, mul_pow, norm_pow,
          mul_comm (‖v‖^k)] using hh
      have hz := hh'.of_const_mul_right
      simpa only [isLittleO_norm_right] using hz
    exact realPolynomial_zero_of_isLittleO k _ ((linePolynomial_degree p v).trans hd) hline
  let i : Fin n := ⟨0, hn⟩
  let v : E n := standardBasis n i
  have hv : v ≠ 0 := (standardBasis n).ne_zero i
  have hz : MvPolynomial.eval (fun _ => 0) p = 0 := by
    have hh := linePolynomial_eval p v 0
    rw [H v hv] at hh
    simpa using hh.symm
  apply MvPolynomial.funext
  intro x
  let w : E n := WithLp.toLp 2 x
  by_cases hw : w = 0
  · have hx : x = 0 := by
      funext j
      exact congrArg (fun z : E n => z j) hw
    simpa [hx] using hz
  · have hh := linePolynomial_eval p w 1
    rw [H w hw] at hh
    simpa [w] using hh.symm


abbrev CoordinatePolynomial : Specs.D04.C03.PolynomialUniqueness.CoordinatePolynomialType :=
  Specs.D04.C03.PolynomialUniqueness.Model.CoordinatePolynomial
abbrev coordinatePolynomialEval : Specs.D04.C03.PolynomialUniqueness.coordinatePolynomialEvalType :=
  @Specs.D04.C03.PolynomialUniqueness.Model.coordinatePolynomialEval
abbrev PolynomialFunctionDegreeLE : Specs.D04.C03.PolynomialUniqueness.PolynomialFunctionDegreeLEType :=
  @Specs.D04.C03.PolynomialUniqueness.Model.PolynomialFunctionDegreeLE

@[simp] theorem coordinatePolynomialEval_apply {n m : ℕ} (p : CoordinatePolynomial n m)
    (h : E n) (i : Fin m) :
    coordinatePolynomialEval p h i = MvPolynomial.eval (fun j => h j) (p i) := rfl

 theorem coordinatePolynomialEval_injective {n m : ℕ} :
    Function.Injective (@coordinatePolynomialEval n m) := by
  intro p q he
  funext i
  apply MvPolynomial.funext
  intro x
  exact congrArg (fun f : E n → E m => f (WithLp.toLp 2 x) i) he

 theorem coordinatePolynomial_coeff_unique {n m : ℕ} (p q : CoordinatePolynomial n m)
    (he : coordinatePolynomialEval p = coordinatePolynomialEval q)
    (i : Fin m) (α : Fin n →₀ ℕ) : (p i).coeff α = (q i).coeff α := by
  rw [coordinatePolynomialEval_injective he]

 theorem coordinatePolynomial_zero_of_isLittleO {n m : ℕ} (hn : 0 < n) (k : ℕ)
    (p : CoordinatePolynomial n m) (hd : ∀ i, (p i).totalDegree ≤ k)
    (ho : coordinatePolynomialEval p =o[𝓝[≠] 0] (fun h => ‖h‖^k)) : p = 0 := by
  funext i
  apply mvPolynomial_zero_of_isLittleO hn k (p i) (hd i)
  have hc : (fun h : E n => coordinatePolynomialEval p h i) =O[𝓝[≠] 0]
      coordinatePolynomialEval p := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Filter.Eventually.of_forall fun h => by
      simpa only [one_mul] using PiLp.norm_apply_le (coordinatePolynomialEval p h) i
  exact hc.trans_isLittleO ho

 theorem polynomialFunction_zero_of_isLittleO {n m : ℕ} (hn : 0 < n) (k : ℕ)
    (Q : E n → E m) (hQ : PolynomialFunctionDegreeLE k Q)
    (ho : Q =o[𝓝[≠] 0] (fun h => ‖h‖^k)) : Q = 0 := by
  obtain ⟨p, hd, rfl⟩ := hQ
  rw [coordinatePolynomial_zero_of_isLittleO hn k p hd ho]
  funext h
  ext i
  simp [coordinatePolynomialEval_apply]

 theorem polynomialFunction_eq_of_sub_isLittleO {n m : ℕ} (hn : 0 < n) (k : ℕ)
    (P Q : E n → E m) (hP : PolynomialFunctionDegreeLE k P)
    (hQ : PolynomialFunctionDegreeLE k Q)
    (ho : (fun h => P h - Q h) =o[𝓝[≠] 0] (fun h => ‖h‖^k)) : P = Q := by
  obtain ⟨p, hp, rfl⟩ := hP
  obtain ⟨q, hq, rfl⟩ := hQ
  have hs : (fun h => coordinatePolynomialEval p h - coordinatePolynomialEval q h) =
      coordinatePolynomialEval (p - q) := by
    funext h
    ext i
    simp [coordinatePolynomialEval_apply]
  rw [hs] at ho
  have hd : ∀ i, ((p-q) i).totalDegree ≤ k := by
    intro i
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hp i) (hq i))
  have he := coordinatePolynomial_zero_of_isLittleO hn k (p-q) hd ho
  rw [sub_eq_zero.mp he]

 theorem functions_dimension_zero_eq_iff {Y : Type} (P Q : E 0 → Y) :
    P = Q ↔ P 0 = Q 0 := by
  constructor
  · intro he; rw [he]
  · intro he; funext h
    have hh : h = 0 := Subsingleton.elim _ _
    simpa only [hh] using he

 theorem taylorPolynomial_dimension_zero_add {m : ℕ} (k : ℕ)
    (f g : E 0 → E m) (a h : E 0) :
    taylorPolynomial k (fun x => f x + g x) a h =
      taylorPolynomial k f a h + taylorPolynomial k g a h := by
  simp only [taylorPolynomial_dimension_zero]

 theorem taylorPolynomial_dimension_zero_operation {m p q : ℕ} (k : ℕ)
    (B : E m → E p → E q) (f : E 0 → E m) (g : E 0 → E p) (a h : E 0) :
    taylorPolynomial k (fun x => B (f x) (g x)) a h =
      B (taylorPolynomial k f a h) (taylorPolynomial k g a h) := by
  simp only [taylorPolynomial_dimension_zero]

 theorem taylorPolynomial_dimension_zero_comp {m p : ℕ} (k : ℕ)
    (f : E 0 → E m) (g : E m → E p) (a h : E 0) :
    taylorPolynomial k (g ∘ f) a h =
      taylorPolynomial k g (f a) (taylorPolynomial k f a h - f a) := by
  simp only [taylorPolynomial_dimension_zero, sub_self, taylorPolynomial_zero_increment,
    Function.comp_apply]

 theorem taylorPolynomial_dimension_zero_reciprocal (k : ℕ)
    (f : E 0 → ℝ) (a h : E 0) (_hf : f a ≠ 0) :
    taylorPolynomial k (fun x => (f x)⁻¹) a h =
      ∑ j ∈ Finset.range (k+1), (-(taylorPolynomial k f a h - f a))^j / (f a)^(j+1) := by
  simp only [taylorPolynomial_dimension_zero, sub_self, neg_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

/-- A multilinear diagonal is an ordinary coordinate polynomial, without a
symmetry assumption. This connects the uniqueness theorem to higher tensors. -/
theorem polynomialFunctionDegreeLE_diagonal {n m : ℕ} (r : ℕ)
    (T : Differential (E n) (E m) r) :
    PolynomialFunctionDegreeLE r (differentialDiagonal T) := by
  classical
  let p : CoordinatePolynomial n m := fun i => ∑ j : Fin r → Fin n,
    MvPolynomial.C (differentialCoefficients r T j i) *
      ∏ s : Fin r, MvPolynomial.X (j s)
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_finsetProd _ _).trans (by simp)
  · funext h
    ext i
    change (T (fun _ => h)) i = MvPolynomial.eval (fun j => h j) (p i)
    rw [differential_expansion]
    simp [p, map_sum, mul_comm]

 theorem PolynomialFunctionDegreeLE.mono {n m k l : ℕ} {Q : E n → E m}
    (hQ : PolynomialFunctionDegreeLE k Q) (hkl : k ≤ l) : PolynomialFunctionDegreeLE l Q := by
  obtain ⟨p, hp, rfl⟩ := hQ
  exact ⟨p, fun i => (hp i).trans hkl, rfl⟩

 theorem PolynomialFunctionDegreeLE.zero {n m : ℕ} (k : ℕ) :
    PolynomialFunctionDegreeLE k (0 : E n → E m) := by
  refine ⟨0, by simp, ?_⟩
  funext h
  ext i
  simp

 theorem PolynomialFunctionDegreeLE.add {n m k : ℕ} {P Q : E n → E m}
    (hP : PolynomialFunctionDegreeLE k P) (hQ : PolynomialFunctionDegreeLE k Q) :
    PolynomialFunctionDegreeLE k (fun h => P h + Q h) := by
  obtain ⟨p, hp, rfl⟩ := hP
  obtain ⟨q, hq, rfl⟩ := hQ
  refine ⟨p+q, fun i => (MvPolynomial.totalDegree_add _ _).trans (max_le (hp i) (hq i)), ?_⟩
  funext h
  ext i
  simp

 theorem PolynomialFunctionDegreeLE.smul {n m k : ℕ} {P : E n → E m}
    (hP : PolynomialFunctionDegreeLE k P) (c : ℝ) :
    PolynomialFunctionDegreeLE k (fun h => c • P h) := by
  obtain ⟨p, hp, rfl⟩ := hP
  refine ⟨fun i => MvPolynomial.C c * p i, ?_, ?_⟩
  · intro i
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hp i)
  · funext h
    ext i
    simp [PiLp.smul_apply]

 theorem PolynomialFunctionDegreeLE.sum {ι : Type} {n m k : ℕ} (s : Finset ι)
    (P : ι → E n → E m) (hP : ∀ i ∈ s, PolynomialFunctionDegreeLE k (P i)) :
    PolynomialFunctionDegreeLE k (fun h => ∑ i ∈ s, P i h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : (fun h : E n => ∑ i ∈ (∅ : Finset ι), P i h) = (0 : E n → E m) := by
      funext h; simp
    rw [he]
    exact PolynomialFunctionDegreeLE.zero k
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (hP i (by simp)).add (ih (fun j hj => hP j (by simp [hj])))

/-- In particular, the actual upstream Taylor polynomial has the degree needed
by polynomial uniqueness, including k=0 and n=0. -/
theorem polynomialFunctionDegreeLE_taylorPolynomial {n m : ℕ} (k : ℕ)
    (f : E n → E m) (a : E n) :
    PolynomialFunctionDegreeLE k (taylorPolynomial k f a) := by
  apply PolynomialFunctionDegreeLE.sum
  intro j hj
  exact ((polynomialFunctionDegreeLE_diagonal j (higherDifferential j f a)).mono
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).smul ((j.factorial : ℝ)⁻¹)

end D04
