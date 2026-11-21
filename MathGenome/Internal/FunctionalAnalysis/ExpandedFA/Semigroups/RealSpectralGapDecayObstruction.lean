import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.RealSpectralGapDecayObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SpectralGapDecayObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.RealSpectralGapDecay
open Unbounded
open TraceIdeals.RealComplexification (Space)
open TraceIdeals.RealComplexification.Spec (inclusion realPart imagPart conjugation)
open RealOperatorComplexification (complexify)
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (complexPair ip)
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace
local instance : ContinuousSMul ℝ (Space H) := IsScalarTower.continuousSMul ℂ

/-- The real part of the complex quadratic form is the sum of the two real forms. -/
theorem form_upper_complexification (G : Operator ℝ H H) (ω : ℝ)
    (hω : FormUpperBound G ω) (p : (complexify G).domain) :
    (inner ℂ (p : Space H) (complexify G p)).re ≤ ω * ‖(p : Space H)‖ ^ 2 := by
  have hr := hω ⟨p.1.1, p.2.1⟩
  have hi := hω ⟨p.1.2, p.2.2⟩
  rw [TraceIdeals.RealComplexification.Spec.norm_sq]
  change inner ℝ p.1.1 (G ⟨p.1.1, p.2.1⟩) +
    inner ℝ p.1.2 (G ⟨p.1.2, p.2.2⟩) ≤ _
  nlinarith

theorem spectral_transport : Spec.SpectralTransport.{u} := by
  intro H _ _ _ G hd ha ω hω
  have hdc := (RealOperatorComplexification.denselyDefined_iff G).mpr hd
  have hac := (RealOperatorComplexification.selfAdjoint_iff G hd).mpr ha
  exact ⟨hdc, hac, form_upper_complexification G ω hω,
    SpectralGapDecay.spectrum_real (complexify G) hdc hac,
    RealSelfAdjointSpectralTheorem.spectrum_complexification H G⟩

@[simp] theorem complexify_inclusion (G : Operator ℝ H H) (x : G.domain) :
    complexify G ⟨inclusion (x : H), ⟨x.2, G.domain.zero_mem⟩⟩ = inclusion (G x) := by
  change complexPair H (G x) (G (0 : G.domain)) = complexPair H (G x) 0
  rw [G.map_zero]

lemma inclusion_continuous : Continuous (inclusion (H := H)) := inclusion.continuous
lemma inclusion_norm (x : H) : ‖inclusion x‖ = ‖x‖ := inclusion.norm_map x
lemma inclusion_sub (x y : H) : inclusion (x - y) = inclusion x - inclusion y := inclusion.map_sub x y
lemma inclusion_add (x y : H) : inclusion (x + y) = inclusion x + inclusion y := inclusion.map_add x y

/-- The same inclusion, linear for the real action used in complex trajectory
calculus. The metric and its values remain the canonical Hilbert ones. -/
def inclusionMap :
    letI : Module ℝ (Space H) := Module.restrictScalars ℝ ℂ (Space H)
    H →L[ℝ] Space H := by
  letI : Module ℝ (Space H) := Module.restrictScalars ℝ ℂ (Space H)
  exact
    { toFun := inclusion
      map_add' := inclusion_add
      map_smul' := fun r x => by
        change inclusion (r • x) = (r : ℂ) • inclusion x
        rw [Hilbert.PreHilbertCompactSpectral.Spec.Complexification.csmul]
        change complexPair H (r • x) 0 = complexPair H (r • x - 0 • (0 : H)) (0 • x + r • 0)
        simp only [zero_smul, smul_zero, sub_zero, zero_add]
      cont := inclusion_continuous }

theorem trajectory_transport : Spec.TrajectoryTransport.{u} := by
  intro H _ _ _ G u du hCu hCd hder hD hgraph
  have hg (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      complexify G ⟨inclusion (u t), inclusionDomain G u hD t ht⟩ =
        inclusion (G ⟨u t, hD t ht⟩) := complexify_inclusion G ⟨u t, hD t ht⟩
  letI : Module ℝ (Space H) := Module.restrictScalars ℝ ℂ (Space H)
  letI : NormedSpace ℝ (Space H) := NormedSpace.restrictScalars ℝ ℂ (Space H)
  refine ⟨inclusion_continuous.comp_continuousOn hCu,
    inclusion_continuous.comp_continuousOn hCd, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (inclusionMap (H := H)).hasFDerivAt.comp_hasDerivWithinAt t (hder t ht)
  · have he : (fun t : Ici (0 : ℝ) => complexify G ⟨inclusion (u t), inclusionDomain G u hD t t.property⟩) =
        (fun t : Ici (0 : ℝ) => inclusion (G ⟨u t, hD t t.property⟩)) := by
      funext t
      exact hg t t.property
    rw [he]
    exact inclusion_continuous.comp hgraph
  · intro t ht
    rw [hg t ht, ← inclusion_sub, inclusion_norm]
  · exact fun t => inclusion_norm (u t)
  · intro b
    simp only [inclusion_norm]

theorem spectral_gap_decay_obstruction : Spec.DecayObstruction.{u} := by
  intro H _ _ _ G hd ha hupper ξ hξ d hdpos hgap u du hCu hCd hder hD hgraph k hk hres
  obtain ⟨ω, hω⟩ := hupper
  obtain ⟨hdc, hac, hωc, _, hspec⟩ := spectral_transport G hd ha ω hω
  have hgapc : ∀ n (s : ℝ), s ∈ Ioo (ξ n - d) (ξ n + d) →
      (s : ℂ) ∉ UnboundedNormalSpectralTheorem.operatorSpectrum (complexify G) := by
    intro n s hs h
    exact hgap n s hs (by rw [hspec]; exact h)
  obtain ⟨hCuc, hCdc, hderc, hgraphc, hnormres, hnorm, hint⟩ :=
    trajectory_transport G u du hCu hCd hder hD hgraph
  have hresc : ∀ t (ht : t ∈ Ici (0 : ℝ)),
      ‖inclusion (du t) - complexify G ⟨inclusion (u t), inclusionDomain G u hD t ht⟩‖ ≤
        k * ‖inclusion (u t)‖ := by
    intro t ht
    rw [hnormres t ht, hnorm]
    exact hres t ht
  have h := SpectralGapDecay.spectral_gap_decay_obstruction (complexify G) hdc hac
    ⟨ω, hωc⟩ ξ hξ d hdpos hgapc (fun t => inclusion (u t)) (fun t => inclusion (du t))
    hCuc hCdc hderc (inclusionDomain G u hD) hgraphc k hk hresc
  rcases h with hz | ⟨b, hb, hi⟩
  · left
    intro t ht
    exact inclusion.injective (by simpa only [map_zero] using hz t ht)
  · exact Or.inr ⟨b, hb, (hint b) ▸ hi⟩

lemma restriction_inclusion_spec (A : Space H →L[ℂ] Space H)
    (hA : ∀ p, conjugation (A p) = A (conjugation p)) (x : H) :
    inclusion (RealSelfAdjointSpectralTheorem.restrictOperator A x) = A (inclusion x) :=
  RealSelfAdjointSpectralTheorem.restriction_inclusion A hA x

open RealSelfAdjointSpectralTheorem (conjugateOperator conjugation_involutive
  conjugation_smul restrictOperator restriction_inclusion)

/-- Conjugating a semigroup twice gives complex-linear operators. -/
def conjugateSemigroup (S : C0Semigroup ℂ (Space H)) : C0Semigroup ℂ (Space H) where
  operators t := conjugateOperator (S.operators t)
  at_zero := by
    ext p
    change conjugation (S.operators 0 (conjugation p)) = p
    rw [S.at_zero, ContinuousLinearMap.id_apply, conjugation_involutive]
  add_time t s := by
    ext p
    change conjugation (S.operators (t + s) (conjugation p)) =
      conjugation (S.operators t (conjugation (conjugation (S.operators s (conjugation p)))))
    rw [conjugation_involutive, S.add_time]
    rfl
  strong_zero p := by
    have hh := conjugation.continuous.tendsto (conjugation p) |>.comp
      (S.strong_zero (conjugation p))
    simpa only [Function.comp_def, conjugation_involutive, RealSelfAdjointSpectralTheorem.conjugateOperator_apply] using hh

lemma conjugate_quotient (S : C0Semigroup ℂ (Space H)) (h : ℝ) (p : Space H) :
    differenceQuotient (conjugateSemigroup S) h p =
      conjugation (differenceQuotient S h (conjugation p)) := by
  change (h : ℂ)⁻¹ • (conjugation (S.operators h.toNNReal (conjugation p)) - p) =
    conjugation ((h : ℂ)⁻¹ • (S.operators h.toNNReal (conjugation p) - conjugation p))
  rw [conjugation_smul, map_sub, conjugation_involutive]
  simp only [map_inv₀, Complex.star_def, Complex.conj_ofReal]

lemma conjugate_generator_limit (S : C0Semigroup ℂ (Space H)) (p q : Space H) :
    HasGeneratorLimit (conjugateSemigroup S) p q ↔
      HasGeneratorLimit S (conjugation p) (conjugation q) := by
  change Tendsto (fun h => differenceQuotient (conjugateSemigroup S) h p) _ (𝓝 q) ↔
    Tendsto (fun h => differenceQuotient S h (conjugation p)) _ (𝓝 (conjugation q))
  constructor
  · intro hh
    have h := conjugation.continuous.tendsto q |>.comp hh
    simpa only [Function.comp_def, conjugate_quotient, conjugation_involutive] using h
  · intro hh
    have h := conjugation.continuous.tendsto (conjugation q) |>.comp hh
    simpa only [Function.comp_def, ← conjugate_quotient, conjugation_involutive] using h

lemma conjugation_graph (G : Operator ℝ H H) (p q : Space H) :
    (conjugation p, conjugation q) ∈ (complexify G).graph ↔ (p, q) ∈ (complexify G).graph := by
  rw [RealOperatorComplexification.graph_iff, RealOperatorComplexification.graph_iff]
  change ((p.1, q.1) ∈ G.graph ∧ -(p.2, q.2) ∈ G.graph) ↔
    ((p.1, q.1) ∈ G.graph ∧ (p.2, q.2) ∈ G.graph)
  rw [Submodule.neg_mem_iff]

/-- Invariance follows from equality of the full generators and semigroup
uniqueness; it is not supplied as an additional certificate. -/
theorem semigroup_conjugation (G : Operator ℝ H H) (S : C0Semigroup ℂ (Space H))
    (hS : complexify G = generator S) (t : ℝ≥0) (p : Space H) :
    conjugation (S.operators t p) = S.operators t (conjugation p) := by
  have hgen : C0SemigroupSpec.generatorValue (conjugateSemigroup S) = C0SemigroupSpec.generatorValue S := by
    apply LinearPMap.eq_of_eq_graph
    ext ⟨p, q⟩
    rw [mem_generator_graph_iff]
    change HasGeneratorLimit (conjugateSemigroup S) p q ↔ (p, q) ∈ (C0SemigroupSpec.generatorValue S).graph
    rw [conjugate_generator_limit, mem_generator_graph_iff]
    change C0SemigroupSpec.hasGeneratorLimitValue S (conjugation p) (conjugation q) ↔
      C0SemigroupSpec.hasGeneratorLimitValue S p q
    rw [← mem_generator_graph_iff, ← mem_generator_graph_iff]
    change (conjugation p, conjugation q) ∈ (C0SemigroupSpec.generatorValue S).graph ↔ (p, q) ∈ (C0SemigroupSpec.generatorValue S).graph
    change complexify G = C0SemigroupSpec.generatorValue S at hS
    rw [← hS]
    exact conjugation_graph G p q
  have heq := GeneratorDeterminesSemigroup.generator_determines_semigroup
    (conjugateSemigroup S) S hgen t
  have h := congrArg (fun A : Space H →L[ℂ] Space H => A (conjugation p)) heq
  change conjugation (S.operators t (conjugation (conjugation p))) = _ at h
  simpa only [conjugation_involutive] using h

/-- Restriction acts on the original real Hilbert space. -/
def restrictSemigroup (S : C0Semigroup ℂ (Space H))
    (hS : ∀ t p, conjugation (S.operators t p) = S.operators t (conjugation p)) :
    C0Semigroup ℝ H where
  operators t := restrictOperator (S.operators t)
  at_zero := by
    ext x
    change realPart (S.operators 0 (inclusion x)) = x
    rw [S.at_zero]
    rfl
  add_time t s := by
    ext x
    change realPart (S.operators (t + s) (inclusion x)) =
      realPart (S.operators t (inclusion (restrictOperator (S.operators s) x)))
    rw [restriction_inclusion_spec _ (hS s) x, S.add_time]
    rfl
  strong_zero x := by
    exact realPart.continuous.tendsto (inclusion x) |>.comp (S.strong_zero (inclusion x))

lemma restrict_quotient (S : C0Semigroup ℂ (Space H))
    (hS : ∀ t p, conjugation (S.operators t p) = S.operators t (conjugation p))
    (h : ℝ) (x : H) :
    inclusion (differenceQuotient (restrictSemigroup S hS) h x) =
      differenceQuotient S h (inclusion x) := by
  rw [C0Semigroup.differenceQuotient_real, C0Semigroup.differenceQuotient_real,
    map_smul, map_sub]
  rw [show inclusion ((restrictSemigroup S hS).operators h.toNNReal x) =
    S.operators h.toNNReal (inclusion x) from restriction_inclusion_spec _ (hS _) x]
  exact (IsScalarTower.algebraMap_smul ℂ (h⁻¹) _).symm

/-- Limits are transported in both directions, so no extra real generator
vectors are lost in the domain identification. -/
theorem restriction_generator_graph (S : C0Semigroup ℂ (Space H))
    (hS : ∀ t p, conjugation (S.operators t p) = S.operators t (conjugation p))
    (x y : H) :
    (x, y) ∈ (generator (restrictSemigroup S hS)).graph ↔
      (inclusion x, inclusion y) ∈ (generator S).graph := by
  change (x, y) ∈ (C0SemigroupSpec.generatorValue (restrictSemigroup S hS)).graph ↔
    (inclusion x, inclusion y) ∈ (C0SemigroupSpec.generatorValue S).graph
  rw [mem_generator_graph_iff, mem_generator_graph_iff]
  change Tendsto (fun h => differenceQuotient (restrictSemigroup S hS) h x) _ (𝓝 y) ↔
    Tendsto (fun h => differenceQuotient S h (inclusion x)) _ (𝓝 (inclusion y))
  constructor
  · intro hh
    have h := inclusion.continuous.tendsto y |>.comp hh
    simpa only [Function.comp_def, restrict_quotient] using h
  · intro hh
    have h := realPart.continuous.tendsto (inclusion y) |>.comp hh
    have he (r : ℝ) : realPart (differenceQuotient S r (inclusion x)) =
        differenceQuotient (restrictSemigroup S hS) r x := by
      rw [← restrict_quotient S hS]
      rfl
    have hry : realPart (inclusion y) = y := rfl
    rw [hry] at h
    simpa only [Function.comp_def, he] using h

theorem generation_and_lines : Spec.GenerationAndLines.{u} := by
  intro H _ _ _ G hd ha hupper ξ hξ d hdpos hgap
  obtain ⟨ω, hω⟩ := hupper
  obtain ⟨hdc, hac, hωc, _, hspec⟩ := spectral_transport G hd ha ω hω
  have hgapc : ∀ n (s : ℝ), s ∈ Ioo (ξ n - d) (ξ n + d) →
      (s : ℂ) ∉ UnboundedNormalSpectralTheorem.operatorSpectrum (complexify G) := by
    intro n s hs h
    exact hgap n s hs (by rw [hspec]; exact h)
  obtain ⟨⟨S, hS⟩, hlines⟩ := SpectralGapDecay.generation_and_lines
    (complexify G) hdc hac ⟨ω, hωc⟩ ξ hξ d hdpos hgapc
  change complexify G = C0SemigroupSpec.generatorValue S at hS
  have hconj := semigroup_conjugation G S hS
  let T := restrictSemigroup S hconj
  have hT : G = generator T := by
    apply LinearPMap.eq_of_eq_graph
    ext ⟨x, y⟩
    rw [restriction_generator_graph]
    change (x, y) ∈ G.graph ↔ (inclusion x, inclusion y) ∈ (C0SemigroupSpec.generatorValue S).graph
    rw [← hS, RealOperatorComplexification.graph_iff]
    change (x, y) ∈ G.graph ↔ ((x, y) ∈ G.graph ∧ (0, 0) ∈ G.graph)
    simp only [show ((0 : H), (0 : H)) = (0 : H × H) from rfl,
      G.graph.zero_mem, and_true]
  exact ⟨T, S, hT, hS, hconj,
    fun t x => (restriction_inclusion_spec _ (hconj t) x).symm,
    restriction_generator_graph S hconj, hlines⟩

theorem full_scalar_corollary : Spec.FullScalarCorollary.{u} :=
  ⟨SpectralGapDecay.generation_and_lines, SpectralGapDecay.spectral_gap_decay_obstruction,
    generation_and_lines, spectral_gap_decay_obstruction⟩

end ExpandedFA.Semigroups.RealSpectralGapDecay
