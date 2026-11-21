import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation

/-!
Proximal definitions (paper.tex:8443–8459).

The proximal map is a total Hilbert-epsilon choice of a finite-energy global
minimizer, not a function taking an assumed existence certificate. Its proved
selection theorem applies as soon as existence is established. Under uniqueness
it is exactly the unique minimizer. The analytic theorem for proper convex
norm-lsc functions and positive parameters belongs to the separately allocated
downstream existence module; no such analytic conclusion is assumed here.

The Hilbert subdifferential and conjugate are identified with the accepted
Banach definitions by the actual real Riesz equivalence, including surjectivity
for subgradients. The infimum is taken in EReal; it is proved finite whenever
there is a finite-energy minimizer.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Proximal

open P1.ExtendedConvexFunctions

universe u

/-- φ(v) + ‖f-v‖²/(2μ). -/
def proximalObjective : Spec.ProximalObjectiveType.{u} := Spec.ProximalObjectiveValue

/-- e_μ^φ(f), as an actual extended-real infimum. -/
def moreauEnvelope : Spec.MoreauEnvelopeType.{u} := Spec.MoreauEnvelopeValue

/-- A global minimizer in the finite domain of φ. -/
def IsProximalMinimizer : Spec.IsProximalMinimizerType.{u} := Spec.IsProximalMinimizerValue

/-- P_μ^φ f, also denoted prox_{μφ} f in the manuscript. The choice obligation
is `proximalMap_isMinimizer`; uniqueness gives `minimizer_iff_eq_proximalMap`. -/
def proximalMap : Spec.ProximalMapType.{u} := Spec.ProximalMapValue

/-- The Hilbert subdifferential, with value ∅ outside D(φ). -/
def hilbertSubdifferential : Spec.HilbertSubdifferentialType.{u} :=
  Spec.HilbertSubdifferentialValue

/-- The conjugate for the real scalar product. -/
def hilbertConjugate : Spec.HilbertConjugateType.{u} := Spec.HilbertConjugateValue

theorem proximalObjective_finite_iff : Spec.ObjectiveFiniteIff.{u} := by
  intro H _ _ φ μ f u
  simp [Spec.ProximalObjectiveValue, P1.ExtendedConvexFunctions.Spec.finiteDomainValue]

theorem isProximalMinimizer_iff_of_proper : Spec.MinimizerIffOfProper.{u} := by
  intro H _ _ φ hφ μ f u
  constructor
  · exact fun hu => hu.2
  · intro h
    obtain ⟨v, hv⟩ := hφ
    refine ⟨(proximalObjective_finite_iff H φ μ f u).mp ?_, h⟩
    exact ne_top_of_le_ne_top ((proximalObjective_finite_iff H φ μ f v).mpr hv) (h v)

theorem moreauEnvelope_formula : Spec.EnvelopeFormula.{u} := by
  intro H _ _ φ μ f
  apply iInf_congr
  intro v
  rfl

theorem moreauEnvelope_isGLB : Spec.EnvelopeIsGLB.{u} := by
  intro H _ _ φ μ f
  exact isGLB_iInf

theorem proximalMap_isMinimizer : Spec.ProximalMapSelection.{u} := by
  intro H _ _ φ μ f hex
  exact Classical.epsilon_spec hex

theorem minimizer_iff_eq_proximalMap : Spec.ProximalMapOfUniqueMinimizer.{u} := by
  intro H _ _ φ μ f hex u
  have hP := proximalMap_isMinimizer H φ μ f hex.exists
  constructor
  · intro hu
    exact (hex.unique hu hP)
  · intro hu
    simpa only [hu] using hP

theorem moreauEnvelope_eq_objective : Spec.EnvelopeAtMinimizer.{u} := by
  intro H _ _ φ μ f u hu
  apply le_antisymm (iInf_le _ u)
  exact le_iInf fun v => WithBot.coe_le_coe.mpr (hu.2 v)

theorem moreauEnvelope_finite_of_minimizer : Spec.EnvelopeFiniteOfMinimizer.{u} := by
  intro H _ _ φ μ f hex
  obtain ⟨u, hu⟩ := hex
  have hfin := (proximalObjective_finite_iff H φ μ f u).mpr hu.1
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
  refine ⟨r, ?_⟩
  rw [moreauEnvelope_eq_objective H φ μ f u hu, ← hr]
  rfl

theorem hilbertSubdifferential_at_finite_value :
    Spec.HilbertSubdifferentialAtFiniteValue.{u} := by
  intro H _ _ φ u r hu
  ext w
  simp [Spec.HilbertSubdifferentialValue,
    P1.ExtendedConvexFunctions.Spec.finiteDomainValue, hu, WithTop.coe_add]

theorem hilbertSubdifferential_at_infinity :
    Spec.HilbertSubdifferentialAtInfinity.{u} := by
  intro H _ _ φ u hu
  ext w
  simp [Spec.HilbertSubdifferentialValue,
    P1.ExtendedConvexFunctions.Spec.finiteDomainValue, hu]

theorem hilbertSubdifferential_riesz_preimage : Spec.SubdifferentialRieszPreimage.{u} := by
  intro H _ _ _ φ u
  rfl

theorem hilbertSubdifferential_riesz_image : Spec.SubdifferentialRieszImage.{u} := by
  intro H _ _ _ φ u
  rw [hilbertSubdifferential_riesz_preimage H φ u]
  exact ((InnerProductSpace.toDual ℝ H).surjective.image_preimage _).symm

theorem hilbertConjugate_eq_banachConjugate : Spec.ConjugateRieszIdentification.{u} := by
  intro H _ _ _ φ w
  rfl

theorem hilbertConjugate_isLUB : Spec.HilbertConjugateIsLUB.{u} := by
  intro H _ _ φ w
  exact isLUB_iSup

theorem hilbertConjugate_ne_bot : Spec.HilbertConjugateNeverBottom.{u} := by
  intro H _ _ _ φ hφ w
  rw [hilbertConjugate_eq_banachConjugate H φ w]
  exact P1.C06Conjugates.convexConjugate_ne_bot H φ hφ (InnerProductSpace.toDual ℝ H w)

end ExpandedFA.Proximal
