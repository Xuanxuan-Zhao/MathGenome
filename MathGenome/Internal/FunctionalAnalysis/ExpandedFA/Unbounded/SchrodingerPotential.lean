import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SchrodingerPotential
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SchrodingerFreeLaplacian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.KatoRellich

/-! The Schrödinger operator on genuine real and complex L²(ℝ),
with its exact H² domain, lower bound and C∞_c graph core.
The shared definitions and multiplication estimates come from the potential
bounds module; the free-operator module supplies self-adjointness and its core. -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.Unbounded.SchrodingerPotential
variable {𝕜 : Type} [RCLike 𝕜]

section AbstractGraph
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A relative bound explicitly constructs a continuous map from the graph
norm domain, as required by the accepted graph-core perturbation theorem. -/
def relativeGraphMap (A B : Operator 𝕜 H H) (hD : A.domain ≤ B.domain)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ u : A.domain, ‖B ⟨u.val, hD u.prop⟩‖ ≤
      a * ‖A u‖ + b * ‖u.val‖) : GraphDomain A →L[𝕜] H := by
  let F : GraphDomain A →ₗ[𝕜] H :=
    { toFun := fun u => B ⟨(GraphDomain.toDomain A u).val, hD u.prop⟩
      map_add' := fun u v => by
        calc
          _ = B (⟨(GraphDomain.toDomain A u).val, hD u.prop⟩ +
              ⟨(GraphDomain.toDomain A v).val, hD v.prop⟩) := by
            congr 1
          _ = _ := B.map_add _ _
      map_smul' := fun c u => by
        calc
          _ = B (c • ⟨(GraphDomain.toDomain A u).val, hD u.prop⟩) := by
            congr 1
          _ = _ := B.map_smul c _ }
  refine F.mkContinuous (a + b) (fun u => ?_)
  change ‖B ⟨(GraphDomain.toDomain A u).val, hD u.prop⟩‖ ≤
    (a + b) * (‖(GraphDomain.toDomain A u).val‖ + ‖A (GraphDomain.toDomain A u)‖)
  apply (hbound (GraphDomain.toDomain A u)).trans
  nlinarith [mul_nonneg ha (norm_nonneg (GraphDomain.toDomain A u).val),
    mul_nonneg hb (norm_nonneg (A (GraphDomain.toDomain A u)))]

/-- Restriction commutes with the perturbation when the core lies in D(B). -/
theorem restrict_sum (A B : Operator 𝕜 H H) (D : Submodule 𝕜 H)
    : (A + B).domRestrict D = A.domRestrict D + B := by
  apply LinearPMap.ext
  · ext u
    change (u ∈ D ∧ u ∈ A.domain ∧ u ∈ B.domain) ↔
      ((u ∈ D ∧ u ∈ A.domain) ∧ u ∈ B.domain)
    tauto
  · intro u hu hv
    rfl

end AbstractGraph

/-- All lower-bound work reduces to the proved analytic form estimate and
the actual free energy identity. -/
theorem lower_bound_of_form_bound (hf : Spec.FreeFacts 𝕜) (hform : Spec.FormBound)
    (q : ℝ → ℝ) (hq : Admissible q) :
    ∃ c : ℝ, ∀ u : (schrodinger 𝕜 q).domain,
      c * ‖u.val‖ ^ 2 ≤ RCLike.re (inner 𝕜 u.val (schrodinger 𝕜 q u)) := by
  obtain ⟨C, hC, hb⟩ := hform 𝕜 q hq (1 / 2) (by norm_num)
  refine ⟨-C, fun u => ?_⟩
  let uA : (freeLaplacian 𝕜).domain := ⟨u.val, u.prop.1⟩
  let uB : (potential 𝕜 q).domain := ⟨u.val, u.prop.2⟩
  obtain ⟨v, hv, he⟩ := hf.2.2 uA
  have hh := (hb u.val v hv).2
  have hi := potential_quadratic q uB
  have hs : RCLike.re (inner 𝕜 u.val (schrodinger 𝕜 q u)) =
      ‖v‖ ^ 2 + ∫ x, q x * ‖u.val x‖ ^ 2 := by
    change RCLike.re (inner 𝕜 u.val (freeLaplacian 𝕜 uA + potential 𝕜 q uB)) = _
    rw [inner_add_right, map_add, he, hi]
  rw [hs]
  have hh' := (abs_le.mp hh).1
  nlinarith [sq_nonneg ‖v‖]

/-- The complex self-adjointness conclusion follows from the accepted
Kato–Rellich theorem once the concrete analytic estimates are proved. -/
theorem complex_selfAdjoint (hf : Spec.FreeFacts ℂ) (hrel : Spec.RelativeBound)
    (q : ℝ → ℝ) (hq : Admissible q) : SelfAdjoint (schrodinger ℂ q) := by
  have hD := domain_le_of_relative_bound (𝕜 := ℂ) hrel q hq
  have hdB : Dense ((potential ℂ q).domain : Set (L2 ℂ)) := hf.1.1.mono hD
  have hB := potential_symmetric q hdB
  obtain ⟨C, hC, hb⟩ := bound_on_domain (𝕜 := ℂ) hrel q hq (1 / 2) (by norm_num)
  exact (kato_rellich (freeLaplacian ℂ) (potential ℂ q) hf.1 hB hD
    (1 / 2) C (by norm_num) hb).1

/-- The real proof uses the genuine real perturbation theorem. -/
theorem real_selfAdjoint (hf : Spec.FreeFacts ℝ) (hrel : Spec.RelativeBound)
    (q : ℝ → ℝ) (hq : Admissible q) : SelfAdjoint (schrodinger ℝ q) := by
  have hD := domain_le_of_relative_bound (𝕜 := ℝ) hrel q hq
  have hdB : Dense ((potential ℝ q).domain : Set (L2 ℝ)) := hf.1.1.mono hD
  have hB := potential_symmetric q hdB
  obtain ⟨C, hC, hb⟩ := bound_on_domain (𝕜 := ℝ) hrel q hq (1 / 2) (by norm_num)
  exact (RealPerturbation.kato_rellich_real (freeLaplacian ℝ) (potential ℝ q) hf.1 hB hD
    (1 / 2) C (by norm_num) hb).1

/-- The original C∞_c core survives the complex multiplication perturbation. -/
theorem complex_core (hf : Spec.FreeFacts ℂ) (hrel : Spec.RelativeBound)
    (q : ℝ → ℝ) (hq : Admissible q) :
    OperatorDomainsSpec.coreValue (schrodinger ℂ q) (smoothCompact ℂ) := by
  let A := freeLaplacian ℂ
  let B := potential ℂ q
  let D := smoothCompact ℂ
  have hA : IsSelfAdjoint A := hf.1
  have hD : A.domain ≤ B.domain := domain_le_of_relative_bound hrel q hq
  have hsum : IsSelfAdjoint (A + B) := complex_selfAdjoint hf hrel q hq
  obtain ⟨C, hC, hb⟩ := bound_on_domain (𝕜 := ℂ) hrel q hq (1 / 2) (by norm_num)
  let F := relativeGraphMap A B hD (1 / 2) C (by norm_num) hC hb
  have hcore : (A.domRestrict D).graph.topologicalClosure = A.graph := by
    rw [hf.2.1.2]
    exact hA.isClosed_operator.submodule_topologicalClosure_eq
  have hCD : (A.domRestrict D).domain ≤ B.domain := fun x hx => hD hx.2
  obtain ⟨hc, he⟩ := graph_core_sum_closure A (A.domRestrict D) B B
    LinearPMap.domRestrict_le hcore le_rfl hCD hD F (fun _ => rfl) hsum.isClosed_operator
  refine ⟨fun x hx => ⟨hf.2.1.1 hx, hD (hf.2.1.1 hx)⟩, ?_⟩
  change ((A + B).domRestrict D).graph.topologicalClosure = (A + B).graph.topologicalClosure
  rw [restrict_sum, hc.graph_closure_eq_closure_graph, he,
    hsum.isClosed_operator.submodule_topologicalClosure_eq]

/-- Core transfer on the actual real L² space. -/
theorem real_core (hf : Spec.FreeFacts ℝ) (hrel : Spec.RelativeBound)
    (q : ℝ → ℝ) (hq : Admissible q) :
    OperatorDomainsSpec.coreValue (schrodinger ℝ q) (smoothCompact ℝ) := by
  let A := freeLaplacian ℝ
  let B := potential ℝ q
  let D := smoothCompact ℝ
  have hD : A.domain ≤ B.domain := domain_le_of_relative_bound hrel q hq
  have hsum : KatoRellichSpec.realSelfAdjointValue (A + B) := real_selfAdjoint hf hrel q hq
  obtain ⟨C, hC, hb⟩ := bound_on_domain (𝕜 := ℝ) hrel q hq (1 / 2) (by norm_num)
  let F := relativeGraphMap A B hD (1 / 2) C (by norm_num) hC hb
  have hcore : (A.domRestrict D).graph.topologicalClosure = A.graph := by
    rw [hf.2.1.2]
    exact (RealPerturbation.real_selfAdjoint_closed hf.1).submodule_topologicalClosure_eq
  have hCD : (A.domRestrict D).domain ≤ B.domain := fun x hx => hD hx.2
  obtain ⟨hc, he⟩ := RealPerturbation.graph_core_sum_closure A (A.domRestrict D) B B
    LinearPMap.domRestrict_le hcore le_rfl hCD hD F (fun _ => rfl)
      (RealPerturbation.real_selfAdjoint_closed hsum)
  refine ⟨fun x hx => ⟨hf.2.1.1 hx, hD (hf.2.1.1 hx)⟩, ?_⟩
  change ((A + B).domRestrict D).graph.topologicalClosure = (A + B).graph.topologicalClosure
  rw [restrict_sum, hc.graph_closure_eq_closure_graph, he,
    (RealPerturbation.real_selfAdjoint_closed hsum).submodule_topologicalClosure_eq]

/-- Exact domain identification, retaining every H² vector. -/
theorem schrodinger_domain (hrel : Spec.RelativeBound) (q : ℝ → ℝ)
    (hq : Admissible q) : (schrodinger 𝕜 q).domain = H2 𝕜 := by
  change (freeLaplacian 𝕜).domain ⊓ (potential 𝕜 q).domain = _
  rw [inf_eq_left.mpr (domain_le_of_relative_bound hrel q hq)]
  rfl

/-- Assemble the complete conclusion from the concrete free-operator facts
and quantitative multiplication estimates. -/
theorem assemble (hreal : Spec.FreeFacts ℝ) (hcomplex : Spec.FreeFacts ℂ)
    (hrel : Spec.RelativeBound) (hform : Spec.FormBound) : Spec.Schrodinger := by
  intro q hq
  constructor
  · exact ⟨real_selfAdjoint hreal hrel q hq, schrodinger_domain hrel q hq,
      lower_bound_of_form_bound hreal hform q hq, real_core hreal hrel q hq⟩
  · exact ⟨complex_selfAdjoint hcomplex hrel q hq, schrodinger_domain hrel q hq,
      lower_bound_of_form_bound hcomplex hform q hq, complex_core hcomplex hrel q hq⟩

/-- The quantitative hypotheses used in the perturbation argument are theorems
for every admissible potential and every positive epsilon. -/
theorem schrodinger_estimates : Spec.PotentialEstimates :=
  ⟨relative_bound, form_bound⟩

/-- A real L² + L∞ potential gives a self-adjoint, bounded-below Schrödinger
operator on exactly H², with C∞_c as a graph core, over both scalar fields. -/
theorem schrodinger_theorem : Spec.Schrodinger :=
  assemble SchrodingerFreeLaplacian.free_real SchrodingerFreeLaplacian.free_complex
    relative_bound form_bound

end ExpandedFA.Unbounded.SchrodingerPotential
