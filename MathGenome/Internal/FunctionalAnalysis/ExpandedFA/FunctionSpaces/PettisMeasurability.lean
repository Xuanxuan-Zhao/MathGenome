import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PettisMeasurability
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
Pettis measurability and weak integrals, paper.tex:17078–17105.

On the closure of the essential separable subspace, a dense sequence and
Hahn–Banach give a countable separating family of ambient linear functionals.
The coordinate map into a countable scalar product is continuous and injective.
Lusin–Souslin makes it a measurable embedding, so measurable coordinates imply
Borel measurability on this subspace. Modifying the function on its exceptional
null set preserves scalar measurability because the measure is complete.
-/

noncomputable section
open Filter MeasureTheory TopologicalSpace
open scoped Topology
universe w u v

namespace ExpandedFA.FunctionSpaces
open PettisMeasurabilitySpec

def WeaklyMeasurable : WeaklyMeasurableType.{w,u,v} := WeaklyMeasurableValue

def EssentiallySeparablyValued : EssentiallySeparablyValuedType.{w,u,v} :=
  EssentiallySeparablyValuedValue

def IsWeakIntegral : IsWeakIntegralType.{w,u,v} := IsWeakIntegralValue

/-- A separable subspace is separated by countably many functionals defined on
its ambient normed space. Neither subspace closedness nor nontriviality is needed. -/
theorem exists_countable_separating_on_submodule (𝕜 : Type w) [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (S : Submodule 𝕜 E) [SeparableSpace S] :
    ∃ ℓ : ℕ → E →L[𝕜] 𝕜, ∀ x : S, (∀ n, ℓ n (x : E) = 0) → x = 0 := by
  choose ℓ hℓ hval using fun n => exists_dual_vector'' 𝕜 ((denseSeq S n : S) : E)
  refine ⟨ℓ, ?_⟩
  intro x hx
  have hd (n : ℕ) : ‖denseSeq S n‖ ≤ ‖denseSeq S n - x‖ := by
    calc
      ‖denseSeq S n‖ = ‖ℓ n ((denseSeq S n : S) : E)‖ := by
        simp only [hval n, RCLike.norm_ofReal, abs_norm]
        rfl
      _ = ‖ℓ n (((denseSeq S n : S) : E) - (x : E))‖ := by
        rw [map_sub, hx n, sub_zero]
      _ ≤ ‖ℓ n‖ * ‖((denseSeq S n : S) : E) - (x : E)‖ := (ℓ n).le_opNorm _
      _ ≤ ‖denseSeq S n - x‖ := by
        exact mul_le_of_le_one_left (norm_nonneg _) (hℓ n)
  have h : ‖x‖ ≤ ‖x - x‖ := (denseRange_denseSeq S).induction_on (p := fun y : S => ‖y‖ ≤ ‖y - x‖) x
    (isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm)) hd
  simpa using h

/-- The Pettis measurability criterion with the paper's a.e. convention. -/
theorem pettis_measurability : PettisCriterion.{w,u,v} := by
  intro 𝕜 _ X E _ _ _ _ μ _ f
  classical
  let : MeasurableSpace 𝕜 := borel 𝕜
  constructor
  · intro hf
    have hfm := (strongMeasurable_identification μ f).mp hf
    refine ⟨?_, ?_⟩
    · intro ℓ
      exact aemeasurable_iff_measurable.mp
        (ℓ.continuous.comp_aestronglyMeasurable hfm).aemeasurable
    · obtain ⟨g, hg, hfg⟩ := hfm
      refine ⟨Submodule.span 𝕜 (Set.range g), hg.isSeparable_range.span, ?_⟩
      filter_upwards [hfg] with x hx
      rw [hx]
      exact Submodule.subset_span (Set.mem_range_self x)
  · rintro ⟨hf, S, hS, hmem⟩
    let T := S.topologicalClosure
    have hT : IsSeparable (T : Set E) := hS.closure
    let : SeparableSpace T := hT.separableSpace
    let : MeasurableSpace T := borel T
    let : BorelSpace T := ⟨rfl⟩
    let g : X → T := fun x => if hx : f x ∈ T then ⟨f x, hx⟩ else 0
    have hgf : (fun x => (g x : E)) =ᵐ[μ] f := by
      filter_upwards [hmem] with x hx
      have hxT : f x ∈ T := S.le_topologicalClosure hx
      simp [g, hxT]
    obtain ⟨ℓ, hℓ⟩ := exists_countable_separating_on_submodule 𝕜 T
    let J : T → ℕ → 𝕜 := fun y n => ℓ n (y : E)
    have hJ : Continuous J :=
      continuous_pi fun n => (ℓ n).continuous.comp continuous_subtype_val
    have hJi : Function.Injective J := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply hℓ (x - y)
      intro n
      have hn := congrFun hxy n
      simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using hn
    have hJg : Measurable (J ∘ g) := by
      apply Measurable.of_eval
      intro n
      exact (hf (ℓ n)).congr_ae (hgf.symm.fun_comp (ℓ n))
    have hg : MeasureTheory.StronglyMeasurable g :=
      ((hJ.measurableEmbedding hJi).measurable_comp_iff.mp hJg).stronglyMeasurable
    apply (strongMeasurable_identification μ f).mpr
    exact (continuous_subtype_val.comp_stronglyMeasurable hg).aestronglyMeasurable.congr
      hgf

/-- Bochner integration supplies every scalar weak integral and its representing vector. -/
theorem bochnerIntegral_isWeakIntegral : BochnerIsWeakIntegral.{w,u,v} := by
  intro 𝕜 _ X E _ _ _ _ μ f
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro hf ℓ
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  exact ⟨ℓ.integrable_comp hfi, (ℓ.integral_comp_comm hfi).symm⟩

end ExpandedFA.FunctionSpaces
