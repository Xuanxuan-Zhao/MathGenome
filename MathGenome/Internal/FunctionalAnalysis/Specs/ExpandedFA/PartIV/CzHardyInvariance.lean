import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMolecules
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyCZEndpoint

/-! Independent statements for `fa2:p4:cz-hardy-invariance`.
The original C¹ standard convolution setting, both scalar fields, and d = 0
are retained. No continuity of a Fourier multiplier at zero is assumed.
Atoms, Hardy norms and the L¹ embedding are the accepted quotient objects.
The estimates are uniform over all centers and positive radii. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace ExpandedFA.PartIV.CzHardyInvarianceSpec
open SingularIntegrals StandardConvolution Hardy.AtomicHardySpaceSpec
open Hardy.HardyCZEndpointSpec

/-- The canonical class of a single original atom in the quotient. -/
def atomClass {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (a : Atoms 𝕜 d) : Hardy 𝕜 d :=
  by
    classical
    exact (KernelValue volume).mkQ (lp.single 1 a (1 : 𝕜))

/-- A convenient homogeneous bound for both normalized L² size and tail. -/
def operatorSize {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) : ℝ :=
  ‖T.operator‖ * (volume.real (Metric.ball (0 : Space d) 1)) ^ (-1 / 2 : ℝ) +
    (d : ℝ) * T.kernel.constant * 2 ^ (d + 1)

/-- The Fourier cancellation argument assumes only essential boundedness,
not continuity of the multiplier at zero. -/
def BoundedMultiplierCancellation : Prop :=
  ∀ {d : ℕ} (f g m : Fourier.Euclidean d → ℂ),
    Integrable f → Integrable g → (∫ x, f x) = 0 →
    ∀ M : ℝ, (∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ M) →
    (Fourier.integralFourier g =ᵐ[volume]
      fun ξ => m ξ * Fourier.integralFourier f ξ) → (∫ x, g x) = 0

/-- The image of every atom under the original L² map has zero integral. -/
def AtomCancellation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (a : Atoms 𝕜 d) (h2 : MemLp (a.val : Space d → 𝕜) 2),
    Integrable (T.operator (h2.toLp a.val) : Space d → 𝕜) ∧
      (∫ x, T.operator (h2.toLp a.val) x) = 0

/-- The normalized estimates on arbitrary translated and dilated atoms. -/
def NormalizedBounds : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (a : Atoms 𝕜 d),
    ∃ (c : Space d) (r : ℝ) (h2 : MemLp (a.val : Space d → 𝕜) 2),
      0 < r ∧
      (eLpNorm (T.operator (h2.toLp a.val) : Space d → 𝕜) 2 volume).toReal ≤
        operatorSize T * r ^ (-(d : ℝ) / 2) ∧
      ∀ᵐ x ∂volume, 2 * r ≤ ‖x - c‖ →
        ‖T.operator (h2.toLp a.val) x‖ ≤ operatorSize T * r / ‖x - c‖ ^ (d + 1)

/-- An actual molecule, including its cancellation, in every center and scale. -/
def AtomMolecule : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (T : StandardConvolutionOperator 𝕜 d)
    (a : Atoms 𝕜 d),
    ∃ (c : Space d) (r : ℝ) (h2 : MemLp (a.val : Space d → 𝕜) 2),
      HardyMoleculesSpec.IsMolecule
        (T.operator (h2.toLp a.val) : Space d → 𝕜) c r (operatorSize T)

/-- A uniform bound in the genuine Hardy norm, with equality of L¹ classes. -/
def AtomBound : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (T : StandardConvolutionOperator 𝕜 d)
      (a : Atoms 𝕜 d),
      ∃ (h2 : MemLp (a.val : Space d → 𝕜) 2)
        (hi : Integrable (T.operator (h2.toLp a.val) : Space d → 𝕜))
        (h : Hardy 𝕜 d),
        EmbeddingValue volume h = hi.toL1 (T.operator (h2.toLp a.val)) ∧
          ‖h‖ ≤ C * operatorSize T

/-- The bounded extension agrees with the previously defined endpoint on
all Hardy inputs. Absolute atomic series converge in Hardy norm and give that
same extension, independently of their representation. -/
def Invariance : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (T : StandardConvolutionOperator 𝕜 d),
    ∃ U : Hardy 𝕜 d →L[𝕜] Hardy 𝕜 d,
      ‖U‖ ≤ C * operatorSize T ∧
      (∀ E : Hardy 𝕜 d →L[𝕜] CZWeak.L1 𝕜 d,
        (∀ (a : Atoms 𝕜 d) (h2 : MemLp (a.val : Space d → 𝕜) 2),
          (E (atomClass a) : Space d → 𝕜) =ᵐ[volume]
            (T.operator (h2.toLp a.val) : Space d → 𝕜)) →
        (EmbeddingValue volume).comp U = E) ∧
      (∀ (S : CZWeak.L1 𝕜 d →ₗ[𝕜] CZWeak.MeasurableClasses 𝕜 d),
        CZWeak.IsCompatibleExtension T S → ∀ h : Hardy 𝕜 d,
          (EmbeddingValue volume (U h) : Space d → 𝕜) =ᵐ[volume]
            (S (EmbeddingValue volume h) : Space d → 𝕜)) ∧
      (∀ (a : ℕ → Atoms 𝕜 d) (b : ℕ → 𝕜),
        Summable (fun j => ‖b j‖) → ∀ h : Hardy 𝕜 d,
        HasSum (fun j => b j • (a j).val) (EmbeddingValue volume h) →
        HasSum (fun j => b j • U
          (atomClass (a j))) (U h))

end ExpandedFA.PartIV.CzHardyInvarianceSpec
