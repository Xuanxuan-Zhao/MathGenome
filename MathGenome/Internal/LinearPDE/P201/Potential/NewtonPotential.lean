import MathGenome.Internal.LinearPDE.P201Specs.Potential.NewtonPotential
import MathGenome.Internal.LinearPDE.P201.Potential.Fundamental
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff
namespace P201

abbrev newtonPotential : P201Specs.newtonPotentialType := @P201Specs.newtonPotential
abbrev newtonDistribution : P201Specs.newtonDistributionType := @P201Specs.newtonDistribution

theorem newtonIntegrable : P201Specs.newtonIntegrableStatement := by
  intro n hn f x
  exact (fundamentalLocalIntegrability n hn).integrable_smul_right_of_hasCompactSupport
    (P102.U4.translatedKernel f x).continuous
    (P102.U4.translatedKernel f x).hasCompactSupport

/-- The integral is exactly the library regularization, rather than merely an a.e. representative. -/
theorem newtonPotential_eq_localConvolution {n : ℕ} (hn : 1 ≤ n)
    (f : Test ℝ (⊤ : Domain n)) :
    newtonPotential f = P102.U4.localConvolution
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) f := by
  funext x
  symm
  simpa [newtonPotential, P201Specs.newtonPotential] using
    P102.U4.localConvolution_regularIntegral n ℝ ⊤ (fundamentalKernel n)
      ((fundamentalLocalIntegrability n hn).locallyIntegrableOn _) f x
      (by simp [P102.U4.convolutionDomain])

theorem newtonSmooth : P201Specs.newtonSmoothStatement := by
  intro n hn f
  change ContDiff ℝ (⊤ : ℕ∞) (newtonPotential f)
  rw [newtonPotential_eq_localConvolution hn f]
  exact P102.U4.localConvolution_contDiff _ _

/-- Transposition through the compactly supported inner test commutes with the Laplacian. -/
theorem laplacian_rightCompactConvolution {n : ℕ}
    (T F : Distribution ℝ (⊤ : Domain n))
    (hF : IsCompact (P102.U4.relativeSupport F)) :
    distributionLaplacian (P102.U4.rightCompactConvolution T F hF) =
      P102.U4.rightCompactConvolution (distributionLaplacian T) F hF := by
  unfold distributionLaplacian P201Specs.distributionLaplacian
  simp_rw [P102.U4.rightCompactConvolution_partial_left]
  ext φ
  simp [P102.U4.rightCompactConvolution_apply]

/-- Dirac convolution is the identity, on the same genuine test-space convolution. -/
theorem originDirac_rightCompactConvolution {n : ℕ}
    (F : Distribution ℝ (⊤ : Domain n))
    (hF : IsCompact (P102.U4.relativeSupport F)) :
    P102.U4.rightCompactConvolution (originDirac n) F hF = F := by
  ext φ
  change F (P102.U4.additionTest φ 0) = F φ
  congr 1
  ext y
  exact congrArg φ (zero_add y)

theorem newtonDistributionEquation : P201Specs.newtonDistributionEquationStatement := by
  intro n hn F hF
  change -distributionLaplacian (P102.U4.rightCompactConvolution
    (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) F hF) = F
  rw [laplacian_rightCompactConvolution]
  have hneg (T : Distribution ℝ (⊤ : Domain n)) :
      -P102.U4.rightCompactConvolution T F hF =
        P102.U4.rightCompactConvolution (-T) F hF := by
    ext φ
    rfl
  rw [hneg, fundamentalSolution n hn, originDirac_rightCompactConvolution]

/-- Ordinary derivatives of the smooth regularization can fall on the distribution. -/
theorem laplacian_localConvolution {n : ℕ}
    (T : Distribution ℝ (⊤ : Domain n)) (f : Test ℝ (⊤ : Domain n)) (x : Space n) :
    laplacian (P102.U4.localConvolution T f) x =
      P102.U4.localConvolution (distributionLaplacian T) f x := by
  unfold laplacian P201Specs.laplacian distributionLaplacian P201Specs.distributionLaplacian
  simp_rw [show ∀ α : MultiIndex n,
      multiPartial (P102.U4.localConvolution T f) α =
        P102.U4.localConvolution (distributionDerivative α T) f from
    fun α => P102.U4.localConvolution_distributionPartial P102.U4.distributionConvolution T f α]
  simp [P102.U4.localConvolution, P102.U4.convolutionDomain]

theorem newtonEquation : P201Specs.newtonEquationStatement := by
  intro n hn f x
  change -laplacian (newtonPotential f) x = f x
  rw [newtonPotential_eq_localConvolution hn f, laplacian_localConvolution]
  have hneg (T : Distribution ℝ (⊤ : Domain n)) :
      -P102.U4.localConvolution T f x = P102.U4.localConvolution (-T) f x := by
    simp [P102.U4.localConvolution, P102.U4.convolutionDomain]
  rw [hneg, fundamentalSolution n hn]
  simp only [P102.U4.localConvolution, P102.U4.convolutionDomain, Set.mem_ofPred_eq,
    Opens.mem_top, implies_true, ↓reduceDIte]
  change f (x - 0) = f x
  rw [sub_zero]

theorem normalizedNewtonTheorem : P201Specs.normalizedNewtonTheoremStatement := by
  intro n hn
  exact ⟨fundamentalLocalIntegrability n hn, fundamentalSolution n hn,
    fun f => ⟨newtonSmooth n hn f, newtonEquation n hn f⟩,
    newtonDistributionEquation n hn⟩

end P201
