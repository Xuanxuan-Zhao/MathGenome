import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.TaylorPolynomial
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.MeanInequality
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Peano
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Taylor's theorem with Peano remainder

K03.06.peano, paper.tex:2769–2780. Real increments are used for both
canonical scalar fields. The neighborhood hypothesis supplies derivatives
through order n-1; the last derivative is taken only at a.

Subtract the finite Taylor polynomial's jet. Its highest relevant rung
has derivative zero at a, so the first-order Peano characterization makes
it o(x-a). `Convex.isLittleO_pow_succ_real`, proved by the norm mean
inequality, descends the remaining rungs on a small ball. No continuity
or off-center existence of the nth derivative is used.
-/

noncomputable section
namespace SingleVariableAnalysis
open Set Filter Asymptotics
open scoped Topology
universe u

/-- Descending the derivative ladder by the norm mean inequality. Only the
lower rungs are differentiated on the neighborhood. -/
theorem peano_jet_descent {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℕ → ℝ → E) (m : ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ j ≤ m, D j a = 0)
    (hder : ∀ j < m, ∀ x ∈ Metric.ball a δ,
      HasDerivAt (D j) (D (j+1) x) x)
    (htop : IsLittleO (𝓝 a) (D m) (fun x : ℝ => x-a)) :
    IsLittleO (𝓝 a) (D 0) (fun x : ℝ => (x-a)^(m+1)) := by
  induction m generalizing D with
  | zero => simpa using htop
  | succ m ih =>
    have hshift := ih (fun j => D (j+1))
      (fun j hj => hzero (j+1) (by omega))
      (fun j hj x hx => hder (j+1) (by omega) x hx) htop
    have h := (convex_ball a δ).isLittleO_pow_succ_real
      (Metric.mem_ball_self hδ)
      (fun x hx => (hder 0 (by omega) x hx).hasDerivWithinAt)
      (hshift.mono nhdsWithin_le_nhds)
    rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds a hδ)] at h
    simpa [hzero 0 (by omega)] using h

variable {K : Type u} [RCLike K]

/-- Taylor-Peano on the unshifted neighborhood. We subtract the polynomial
jet, whose derivatives at a agree with those of f. -/
theorem taylorRemainder_peano_nhds (f : ℝ → K) (m : ℕ) (a : ℝ)
    (hnear : ∃ U ∈ 𝓝 a, KTimesDifferentiableOn m f U)
    (htop : DifferentiableAt ℝ (RealIteratedDerivative m f) a) :
    IsLittleO (𝓝 a) (TaylorRemainder f (m+1) a)
      (fun x : ℝ => (x-a)^(m+1)) := by
  obtain ⟨U, hU, hf⟩ := hnear
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  let P := TaylorPolynomialEval f (m+1) a
  let D : ℕ → ℝ → K := fun j x =>
    RealIteratedDerivative j f x - RealIteratedDerivative j P x
  have hP (j : ℕ) (x : ℝ) :
      HasDerivAt (RealIteratedDerivative j P)
        (RealIteratedDerivative (j+1) P x) x := by
    change HasDerivAt
      (RealIteratedDerivative j (RealPolynomialEval (TaylorPolynomial f (m+1) a)))
      (RealIteratedDerivative (j+1) (RealPolynomialEval (TaylorPolynomial f (m+1) a)) x) x
    rw [realPolynomial_iteratedDerivative, realPolynomial_iteratedDerivative,
      Function.iterate_succ_apply']
    exact realPolynomial_hasDerivAt _ x
  have hzero (j : ℕ) (hj : j ≤ m+1) : D j a = 0 := by
    dsimp [D, P]
    rw [taylorPolynomial_derivatives_match f (m+1) a j hj, sub_self]
  have htopD : HasDerivAt (D m) 0 a := by
    have h := htop.hasDerivAt.sub (hP m a)
    rw [← realIteratedDerivative_succ] at h
    convert h using 1
    exact (hzero (m+1) le_rfl).symm
  have hsmall : IsLittleO (𝓝 a) (D m) (fun x : ℝ => x-a) := by
    simpa [hzero m (by omega)] using htopD.isLittleO
  have h := peano_jet_descent D m a δ hδ
    (fun j hj => hzero j (by omega)) (fun j hj x hx => by
      have hd := (hf j hj x (hball hx)).hasDerivAt.sub (hP j x)
      simpa only [D, Pi.sub_apply, ← realIteratedDerivative_succ] using! hd) hsmall
  simpa [D, P, TaylorRemainder] using! h

/-- The canonical remainder is o(h^n) for real increments. -/
theorem taylorRemainder_peano (f : ℝ → K) (n : ℕ) (a : ℝ) (hn : 1 ≤ n)
    (hnear : ∃ U ∈ 𝓝 a, KTimesDifferentiableOn (n-1) f U)
    (htop : DifferentiableAt ℝ (RealIteratedDerivative (n-1) f) a) :
    IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => TaylorRemainder f n a (a+h)) (fun h : ℝ => h^n) := by
  have h := taylorRemainder_peano_nhds f (n-1) a hnear htop
  have hc : Tendsto (fun h : ℝ => a+h) (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    simpa using!
      (continuousAt_const.add continuousAt_id : ContinuousAt (fun h : ℝ => a+h) 0).tendsto.mono_left
        nhdsWithin_le_nhds
  simpa only [Nat.sub_add_cancel hn, Function.comp_def, add_sub_cancel_left] using h.comp_tendsto hc

/-- The displayed finite-sum formulation in K03.06.peano. -/
theorem taylor_peano (f : ℝ → K) (n : ℕ) (a : ℝ) (hn : 1 ≤ n)
    (hnear : ∃ U ∈ 𝓝 a, KTimesDifferentiableOn (n-1) f U)
    (htop : DifferentiableAt ℝ (RealIteratedDerivative (n-1) f) a) :
    IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a+h) -
        ∑ k ∈ Finset.range (n+1),
          (RealIteratedDerivative k f a / (k.factorial : K)) * (algebraMap ℝ K h)^k)
      (fun h : ℝ => h^n) := by
  simpa only [TaylorRemainder, taylorPolynomialEval_formula, add_sub_cancel_left] using
    taylorRemainder_peano f n a hn hnear htop

/-- The zeroth-order Peano assertion is equivalent to continuity. -/
theorem taylor_peano_zero_iff (f : ℝ → K) (a : ℝ) :
    IsLittleO (𝓝[≠] (0 : ℝ)) (fun h => f (a+h) - f a)
      (fun h : ℝ => h^0) ↔ ContinuousAt f a := by
  simp only [pow_zero, isLittleO_one_iff, tendsto_sub_nhds_zero_iff]
  constructor
  · intro h
    have hfull : Tendsto (fun h : ℝ => f (a+h)) (𝓝 (0 : ℝ)) (𝓝 (f a)) := by
      have hc : ContinuousAt (fun h : ℝ => f (a+h)) 0 := by
        apply continuousAt_iff_punctured_nhds.mpr
        simpa using! h
      simpa using! hc.tendsto
    have hc := hfull.comp
      (show Tendsto (fun x : ℝ => x-a) (𝓝 a) (𝓝 0) from by
        simpa using! (continuousAt_id.sub continuousAt_const :
          ContinuousAt (fun x : ℝ => x-a) a).tendsto)
    change Tendsto f (𝓝 a) (𝓝 (f a))
    simpa [Function.comp_def] using! hc
  · intro h
    simpa using!
      h.tendsto.comp (show Tendsto (fun h : ℝ => a+h) (𝓝[≠] (0 : ℝ)) (𝓝 a) from by
        simpa using! ((continuousAt_const.add continuousAt_id :
        ContinuousAt (fun h : ℝ => a+h) 0).tendsto.mono_left nhdsWithin_le_nhds))

end SingleVariableAnalysis
