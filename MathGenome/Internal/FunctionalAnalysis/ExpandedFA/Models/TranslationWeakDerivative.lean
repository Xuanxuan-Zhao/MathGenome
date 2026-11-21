import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationWeakDerivative
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.TranslationFourierModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.StoneTheorem
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ContDiff SchwartzMap Convolution

namespace ExpandedFA.Models.TranslationWeakDerivative
open FullTranslationModel ExpandedFA.Semigroups.Stone ExpandedFA.Unbounded
open ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

-- Match Stone's real derivative structure on the complex L² Hilbert space.
local instance : NormedSpace ℝ (L2 M) := NormedSpace.restrictScalars ℝ ℂ (L2 M)
local instance : IsScalarTower ℝ ℂ (L2 M) := IsScalarTower.restrictScalars ℝ ℂ (L2 M)

/-- Unconjugated Bochner pairing against an L² scalar function. -/
def testIntegral (φ : L2 ℂ) : L2 M →L[ℂ] M :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := M)).lpPairing volume 2 2 φ

theorem testIntegral_apply (φ : L2 ℂ) (f : L2 M) :
    testIntegral φ f = ∫ s : ℝ, φ s • f s := by
  exact ContinuousLinearMap.lpPairing_eq_integral _ φ f

/-- A smooth compact test gives a bounded linear map on the actual L² quotient. -/
def compactTestIntegral (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : L2 M →L[ℂ] M :=
  testIntegral ((hc.toSchwartzMap hφ).toLp 2 volume)

theorem compactTestIntegral_apply (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : L2 M) :
    compactTestIntegral φ hφ hc f = ∫ s : ℝ, φ s • f s := by
  rw [compactTestIntegral, testIntegral_apply]
  apply integral_congr_ae
  filter_upwards [(hc.toSchwartzMap hφ).coeFn_toLp 2 volume] with s hs
  rw [hs]
  rfl

theorem weakDerivative_unique : Spec.WeakDerivativeUnique.{u} := by
  intro M _ _ _ f w z hw hz
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp w).locallyIntegrable (by norm_num))
    ((Lp.memLp z).locallyIntegrable (by norm_num))
  intro φ hφ hc
  have hφc : ContDiff ℝ ∞ (fun s => (φ s : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hcc : HasCompactSupport (fun s => (φ s : ℂ)) :=
    hc.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hw' := hw _ hφc hcc
  have hz' := hz _ hφc hcc
  have he := neg_injective (hw'.symm.trans hz')
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! he

/-- The test integrals separate L² vectors without separability of M. -/
theorem eq_of_compactTestIntegral_eq (f g : L2 M)
    (h : ∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      compactTestIntegral φ hφ hc f = compactTestIntegral φ hφ hc g) : f = g := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (by norm_num))
    ((Lp.memLp g).locallyIntegrable (by norm_num))
  intro φ hφ hc
  have hφc : ContDiff ℝ ∞ (fun s => (φ s : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hcc : HasCompactSupport (fun s => (φ s : ℂ)) := hc.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  simpa only [compactTestIntegral_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! h _ hφc hcc

/-- The change of variables is on the a.e. quotient, rather than on a selected
continuous representative. -/
theorem compactTestIntegral_translate (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : L2 M) (t : ℝ) :
    compactTestIntegral φ hφ hc (translate t f) =
      ∫ s : ℝ, φ (s - t) • f s := by
  rw [compactTestIntegral_apply]
  calc
    (∫ s : ℝ, φ s • (translate t f) s) = ∫ s : ℝ, φ s • f (s + t) := by
      apply integral_congr_ae
      filter_upwards [translation_representative t f] with s hs
      rw [hs]
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun s : ℝ => φ (s - t) • f s) t

/-- Differentiate a translated L² vector only after testing. Local
integrability and the compact support of the test justify convolution calculus. -/
theorem compactTestIntegral_orbit_hasDerivAt (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (f : L2 M) (t : ℝ) :
    HasDerivAt (fun r : ℝ => compactTestIntegral φ hφ hc (translate r f))
      (-(∫ s : ℝ, deriv φ (s - t) • f s)) t := by
  let ψ : ℝ → ℂ := fun s => φ (-s)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp contDiff_neg
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.neg ℝ)
  have hdψ (s : ℝ) : deriv ψ s = -deriv φ (-s) := by
      simpa only [Function.comp_def, neg_one_smul] using
        ((hφ.differentiable (by simp) (-s)).hasDerivAt.scomp s
          (hasDerivAt_neg s)).deriv
  have hd := hcψ.hasDerivAt_convolution_right
    ((ContinuousLinearMap.lsmul ℝ ℂ (E := M)).flip)
    ((Lp.memLp f).locallyIntegrable (by norm_num)) (hψ.of_le (by simp)) t
  have he : (fun r : ℝ => compactTestIntegral φ hφ hc (translate r f)) =
      (f ⋆[((ContinuousLinearMap.lsmul ℝ ℂ (E := M)).flip), volume] ψ) := by
    funext r
    rw [compactTestIntegral_translate, convolution_def]
    apply integral_congr_ae
    filter_upwards [] with s
    simp [ψ, sub_eq_add_neg]
  rw [he]
  convert hd using 1
  rw [convolution_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with s
  simp [hdψ, sub_eq_add_neg]


/-- A norm derivative necessarily is the unconjugated weak derivative. -/
theorem weakDerivative_of_hasDerivative {f w : L2 M}
    (hd : HasDerivative (translationGroup (M := M)) f w) : HasWeakDerivative f w := by
  intro φ hφ hc
  let L := compactTestIntegral (M := M) φ hφ hc
  have hd₀ := (translationGroup.hasDerivative_iff_hasDerivAt f w).mp hd
  have hd₁ := ((L.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hd₀
  have hd₂ := compactTestIntegral_orbit_hasDerivAt φ hφ hc f 0
  have he := hd₁.unique hd₂
  change L w = -(∫ s : ℝ, deriv φ (s - 0) • f s) at he
  have he' : (∫ s : ℝ, φ s • w s) = -(∫ s : ℝ, deriv φ s • f s) := by
    simpa only [L, compactTestIntegral_apply, sub_zero] using! he
  exact neg_injective (by simpa using he'.symm)

/-- A weak derivative differentiates every tested translation orbit at every
real time. The compact test is shifted before the weak identity is used. -/
theorem compactTestIntegral_orbit_hasDerivAt_of_weak {f w : L2 M}
    (hw : HasWeakDerivative f w) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => compactTestIntegral φ hφ hc (translate r f))
      (compactTestIntegral φ hφ hc (translate t w)) t := by
  have hshift : ContDiff ℝ ∞ (fun s : ℝ => φ (s - t)) :=
    hφ.comp (contDiff_id.sub contDiff_const)
  have hcshift : HasCompactSupport (fun s : ℝ => φ (s - t)) := hc.comp_homeomorph (Homeomorph.subRight t)
  have hderiv (s : ℝ) : deriv (fun s : ℝ => φ (s - t)) s = deriv φ (s - t) := by
    simpa only [Function.comp_def, id_eq, one_smul] using!
      ((hφ.differentiable (by simp) (s - t)).hasDerivAt.scomp s
        ((hasDerivAt_id s).sub_const t)).deriv
  have he := hw _ hshift hcshift
  simp only [hderiv] at he
  have hd := compactTestIntegral_orbit_hasDerivAt φ hφ hc f t
  rw [he, neg_neg, ← compactTestIntegral_translate φ hφ hc w t] at hd
  exact hd

/-- Integrated identity in L², recovered from bounded test integrals.
This avoids any pointwise assertion about representatives of f. -/
theorem translation_sub_eq_integral {f w : L2 M} (hw : HasWeakDerivative f w) (t : ℝ) :
    translate t f - f = ∫ s in (0 : ℝ)..t, translate s w := by
  apply eq_of_compactTestIntegral_eq
  intro φ hφ hc
  let L := compactTestIntegral (M := M) φ hφ hc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => compactTestIntegral_orbit_hasDerivAt_of_weak hw φ hφ hc s)
    ((L.continuous.comp (continuous_translation w)).intervalIntegrable 0 t)
  rw [translation_zero] at hi
  change L (translate t f - f) = L (∫ s in (0 : ℝ)..t, translate s w)
  rw [map_sub, ← L.intervalIntegral_comp_comm ((continuous_translation w).intervalIntegrable 0 t)]
  exact hi.symm

/-- Sufficiency uses strong continuity of the translated weak derivative and
the fundamental theorem for the L²-valued integral. -/
theorem hasDerivative_of_weakDerivative {f w : L2 M} (hw : HasWeakDerivative f w) :
    HasDerivative (translationGroup (M := M)) f w := by
  have hc := continuous_translation w
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).add_const f
  have he : (fun t : ℝ => (∫ s in (0 : ℝ)..t, translate s w) + f) =
      fun t : ℝ => translate t f := by
    funext t
    rw [← translation_sub_eq_integral hw t, sub_add_cancel]
  rw [he] at hd
  apply (translationGroup.hasDerivative_iff_hasDerivAt f w).mpr
  simpa only [translation_zero] using! hd

/-- Entire graph equivalence, including necessity and sufficiency of the domain. -/
theorem differenceQuotient_criterion : Spec.DifferenceQuotientCriterion.{u} := by
  intro M _ _ _ f w
  change HasDerivative translationGroup f w ↔ HasWeakDerivative f w
  exact ⟨weakDerivative_of_hasDerivative, hasDerivative_of_weakDerivative⟩

/-- The Stone operator has exactly the distributional domain and value -i f'. -/
theorem spatial_stone : Spec.SpatialStone.{u} := by
  intro M _ _ _
  obtain ⟨A, hA, hexp, hgraph, _⟩ := stone_forward (L2 M) translationGroup
  refine ⟨translationGroup, A, (fun _ _ => rfl), hA, hexp, hgraph, ?_⟩
  intro f g
  change (f, g) ∈ A.graph ↔ HasWeakDerivative f (Complex.I • g)
  rw [← differenceQuotient_criterion M f (Complex.I • g)]
  change (f, g) ∈ A.graph ↔ HasDerivative translationGroup f (Complex.I • g)
  rw [hgraph]
  constructor
  · intro h
    obtain ⟨hf, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff A _).mp h
    apply (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr
    exact ⟨hf, by change Complex.I • A ⟨f, hf⟩ = Complex.I • g; rw [he]⟩
  · intro h
    obtain ⟨hf, he⟩ := (ExpandedFA.Unbounded.mem_graph_iff _ _).mp h
    apply (ExpandedFA.Unbounded.mem_graph_iff _ _).mpr
    refine ⟨hf, ?_⟩
    exact (smul_right_injective _ Complex.I_ne_zero) he


/-- The weak derivative graph is an intersection of equalizers of bounded
linear test maps. -/
theorem weakDerivative_graph_closed : Spec.WeakDerivativeGraphClosed.{u} := by
  intro M _ _ _
  let derivativeSmooth : ∀ (φ : ℝ → ℂ), ContDiff ℝ ∞ φ →
      ContDiff ℝ ∞ (deriv φ) := fun _ hφ => (contDiff_infty_iff_deriv.mp hφ).2
  have he : {p : L2 M × L2 M | HasWeakDerivative p.1 p.2} =
      ⋂ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
        {p : L2 M × L2 M |
          compactTestIntegral (deriv φ) (derivativeSmooth φ hφ) hc.deriv p.1 =
            -compactTestIntegral φ hφ hc p.2} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter, compactTestIntegral_apply, HasWeakDerivative]
  rw [he]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_iInter
  intro hc
  exact isClosed_eq
    ((compactTestIntegral (M := M) (deriv φ) (derivativeSmooth φ hφ) hc.deriv).continuous.comp
      continuous_fst)
    (((compactTestIntegral (M := M) φ hφ hc).continuous.comp continuous_snd).neg)

end ExpandedFA.Models.TranslationWeakDerivative
