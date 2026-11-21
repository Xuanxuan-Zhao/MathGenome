import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.GradientIntegral
import MathGenome.Internal.MultivariableAnalysis.D04.C09.LineIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond

/-! The gradient theorem is proved on each closed smooth piece by the scalar
FTC, then summed. Differentiation at joins is only within the relevant piece.
No potential theorem, regularity of the path, or topological restriction on U
is used. -/
noncomputable section
open Set
open scoped BigOperators
namespace D04.C09
open SingleVariableAnalysis.Riemann

/-- The Euclidean metric correspondence uses the shared derivative and gradient. -/
theorem differential_gradient {n} (f : E n → ℝ) (x v : E n) :
    totalDerivative f x v = inner ℝ (scalarGradient f x) v :=
  scalarGradient_represents f x v

lemma differential_eq_workCovector {n} (f : E n → ℝ) :
    totalDerivative f = workCovector (scalarGradient f) := by
  funext x
  ext v
  exact differential_gradient f x v

/-- Both kinds of integrability follow from C¹, with no extra path hypothesis. -/
theorem gradient_integrable {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (hγ : trace γ ⊆ U) :
    CovectorIntegrable d (totalDerivative f) ∧ WorkIntegrable d (scalarGradient f) := by
  have hc : CovectorIntegrable d (totalDerivative f) :=
    covector_integrable d _ (hf.2.mono hγ)
  refine ⟨hc, ?_⟩
  rw [differential_eq_workCovector] at hc
  exact hc

/-- Chain rule on a smooth piece, retaining the one-sided endpoint derivatives. -/
lemma potential_piece_derivative {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hγ : trace γ ⊆ U)
    (i : Fin d.partition.n) (t : ℝ) (ht : t ∈ cell d.partition i) :
    HasDerivWithinAt (fun s => f (γ s)) (totalDerivative f (γ t) (d.velocity i t))
      (cell d.partition i) t := by
  have hx : γ t ∈ U := hγ ⟨t, cell_subset_interval d.partition i ht, rfl⟩
  obtain ⟨A, hA⟩ := hf.1 (γ t) hx
  have hd : HasFDerivAt f (totalDerivative f (γ t)) (γ t) := by
    rw [totalDerivative_eq U f A (γ t) hA]
    exact (hasTotalDerivative_iff_hasFDerivAt U f A (γ t) hU hx).mp hA
  exact hd.comp_hasDerivWithinAt t ((d.smooth i).2 t ht)

/-- On every positive-length smooth piece the proper scalar FTC applies. -/
lemma potential_piece_integral {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hγ : trace γ ⊆ U)
    (hc : CovectorIntegrable d (totalDerivative f)) (i : Fin d.partition.n) :
    realIntegral (fun t => totalDerivative f (γ t) (d.velocity i t)) (hc i) =
      f (γ (d.partition.point i.succ)) - f (γ (d.partition.point i.castSucc)) := by
  have hcomp : ContinuousOn (fun t => f (γ t)) (cell d.partition i) := by
    intro t ht
    exact (potential_piece_derivative d U f hU hf hγ i t ht).continuousWithinAt
  apply real_ftc_second _ _ _ _
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le hcomp
  intro t ht
  exact (potential_piece_derivative d U f hU hf hγ i t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- The sum of the FTC endpoint differences cancels at every internal join. -/
theorem covector_gradient_integral {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hγ : trace γ ⊆ U)
    (hc : CovectorIntegrable d (totalDerivative f)) :
    covectorLineIntegral d (totalDerivative f) hc = f (γ b) - f (γ a) := by
  change (∑ i, realIntegral _ (hc i)) = _
  simp_rw [potential_piece_integral d U f hU hf hγ hc]
  simpa only [d.partition.first, d.partition.last] using
    sum_cell_differences (fun j => f (γ (d.partition.point j)))

/-- Gradient line integral, with existence of both integrals in the conclusion. -/
theorem gradient_integral {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hγ : trace γ ⊆ U) :
    ∃ hc : CovectorIntegrable d (totalDerivative f),
      ∃ hw : WorkIntegrable d (scalarGradient f),
        covectorLineIntegral d (totalDerivative f) hc =
          workLineIntegral d (scalarGradient f) hw ∧
        workLineIntegral d (scalarGradient f) hw = f (γ b) - f (γ a) := by
  obtain ⟨hc, hw⟩ := gradient_integrable d U f hU hf hγ
  have he : covectorLineIntegral d (totalDerivative f) hc =
      workLineIntegral d (scalarGradient f) hw := by
    have hc' : CovectorIntegrable d (workCovector (scalarGradient f)) := by
      rw [← differential_eq_workCovector]
      exact hc
    simpa only [← differential_eq_workCovector] using
      (covector_eq_work d (scalarGradient f) hc' hw)
  exact ⟨hc, hw, he, he.symm.trans (covector_gradient_integral d U f hU hf hγ hc)⟩

/-- Degenerate paths require no regularity of f: the partition sum is empty. -/
theorem gradient_integral_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) :
    ∃ hc : CovectorIntegrable d (totalDerivative f),
      ∃ hw : WorkIntegrable d (scalarGradient f),
        covectorLineIntegral d (totalDerivative f) hc = 0 ∧
        workLineIntegral d (scalarGradient f) hw = 0 ∧ f (γ a) - f (γ a) = 0 := by
  have hc : CovectorIntegrable d (totalDerivative f) := pieceIntegrable_degenerate d _
  have hw : WorkIntegrable d (scalarGradient f) := pieceIntegrable_degenerate d _
  exact ⟨hc, hw, covectorLineIntegral_degenerate d _ hc,
    pieceIntegral_degenerate d _ hw, sub_self _⟩

end D04.C09
