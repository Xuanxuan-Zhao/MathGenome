import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBasisCoefficients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBasisBoundedComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension

/-! Assembly of `fa2:p1:dual-bases` and the reflexivity criterion.
The restricted evaluation E → F' is onto exactly for boundedly complete bases.
Reflexivity makes it onto by Hahn–Banach extension. It also forces F = E':
a separating bidual functional would be evaluation at a vector with all
coordinates zero. Conversely F = E' and surjectivity of restricted evaluation
represent every bidual functional by evaluation. -/

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBases
open DualBasisBasicity.Spec (dualSpan dualVector IsShrinking IsBoundedlyComplete)
open DualBasisCoefficients.Spec (evaluation)
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance : NormedAddCommGroup (E →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (E →L[𝕜] 𝕜) := inferInstance

/-- Hahn–Banach turns reflexivity into surjectivity of restricted evaluation. -/
theorem evaluation_surjective_of_reflexive (b : SchauderBasis 𝕜 E)
    (hr : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) :
    Function.Surjective (evaluation b) := by
  intro Φ
  obtain ⟨Ψ, hΨ, _⟩ := C05NormExtension.norm_preserving_extension
    𝕜 (E →L[𝕜] 𝕜) (dualSpan b) Φ
  obtain ⟨x, hx⟩ := hr Ψ
  refine ⟨x, ?_⟩
  ext f
  exact (congrArg (fun T : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => T f.val) hx).trans (hΨ f)

/-- No proper closed coordinate span is possible in the dual of a reflexive space. -/
theorem shrinking_of_reflexive [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hr : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) : IsShrinking b := by
  apply (DualBasisBasicity.shrinking_iff_dualSpan b).mpr
  apply eq_top_iff.mpr
  intro f _
  by_contra hf
  have hclosed : IsClosed (dualSpan b : Set (E →L[𝕜] 𝕜)) :=
    Submodule.isClosed_topologicalClosure _
  obtain ⟨Φ, hzero, _, hΦ, hpos⟩ := C05Norming.distance_norming_functional
    𝕜 (E →L[𝕜] 𝕜) (dualSpan b) f (by rwa [hclosed.closure_eq])
  obtain ⟨x, hx⟩ := hr Φ
  have hc (i : ℕ) : b.coord i x = 0 := by
    have hi := congrArg (fun T : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 => T (b.coord i)) hx
    exact hi.trans (hzero _ (dualVector b i).property)
  have hx0 : x = 0 := by
    have ht := b.tendsto_proj x
    have hz : (fun N => b.proj N x) = fun _ => 0 := by
      funext N
      simp [SchauderBasis.proj_apply, hc]
    rw [hz] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hΦ0 : Φ f = 0 := by
    rw [← hx]
    change f x = 0
    simp [hx0]
  rw [hΦ0] at hΦ
  exact (ne_of_gt hpos) (RCLike.ofReal_eq_zero.mp hΦ.symm)

theorem reflexivity_characterization : Spec.ReflexivityCriterion := by
  intro 𝕜 E _ _ _ _ b
  constructor
  · intro hr
    exact ⟨shrinking_of_reflexive b hr,
      (DualBasisCoefficients.evaluation_surjective_iff b).mp
        (evaluation_surjective_of_reflexive b hr)⟩
  · rintro ⟨hs, hb⟩ Φ
    obtain ⟨x, hx⟩ := (DualBasisCoefficients.evaluation_surjective_iff b).mpr hb
      (Φ.comp (dualSpan b).subtypeL)
    refine ⟨x, ?_⟩
    ext f
    have hf : f ∈ dualSpan b := by
      have he : dualSpan b = ⊤ := (DualBasisBasicity.shrinking_iff_dualSpan b).mp hs
      rw [he]
      exact Submodule.mem_top
    exact congrArg (fun T : dualSpan b →L[𝕜] 𝕜 => T ⟨f, hf⟩) hx

theorem dual_bases : Spec.DualBases := by
  intro 𝕜 E _ _ _ _ b
  obtain ⟨hspan, htail⟩ := DualBasisBasicity.shrinking_characterization b
  obtain ⟨d, hd, hc, hbc⟩ := DualBasisCoefficients.dual_shrinking_criterion b
  refine ⟨DualBasisBasicity.dual_basicity b, hspan, htail, d, hd, hc, ?_, hbc,
    reflexivity_characterization b⟩
  rw [hd]
  exact DualBasisBoundedComplete.dual_boundedlyComplete_iff_shrinking b

theorem raw_dual_bases : Spec.RawDualBases := by
  intro 𝕜 E _ _ _ _ e h
  obtain ⟨b, he, hc, _⟩ := C15CoordinateContinuity.raw_native_basis h
  exact ⟨b, he, hc, dual_bases b⟩

/-- Every finite ordered series is eventually its full synthesis. -/
theorem finite_boundedly_complete {n : ℕ} (e : Fin n → E) :
    Spec.finiteBoundedlyComplete (𝕜 := 𝕜) e := by
  classical
  intro a _
  refine ⟨∑ i, a i • e i, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop n] with N hN
  have hs : Finset.univ.filter (fun i : Fin n => i.val < N) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt.trans_le hN
  rw [hs]

theorem finite_shrinking {n : ℕ} (b : UnconditionalSchauderBasis (Fin n) 𝕜 E) :
    Spec.finiteShrinking b := by
  intro f
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  exact ((DualBasisBasicity.finite_dual_facts b).2.2.1 f N hN).symm

/-- Finite bases represent every element of the bidual by finite synthesis. -/
theorem finite_reflexive {n : ℕ} (b : UnconditionalSchauderBasis (Fin n) 𝕜 E) :
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E := by
  intro Φ
  refine ⟨∑ i, Φ (b.coord i) • b i, ?_⟩
  ext f
  have hf : ∑ i, f (b i) • b.coord i = f := by
    have h := (DualBasisBasicity.finite_dual_facts b).2.2.1 f n le_rfl
    simpa using h
  change f (∑ i, Φ (b.coord i) • b i) = Φ f
  calc
    _ = Φ (∑ i, f (b i) • b.coord i) := by simp [map_sum, map_smul, mul_comm]
    _ = Φ f := congrArg Φ hf

theorem finite_dual_bases : Spec.FiniteDualBases := by
  intro 𝕜 E _ _ _ n b
  classical
  let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
  let e' : Fin n → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i))⟩
  let ev (i : Fin n) : F →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.apply 𝕜 𝕜 (b i)).comp F.subtypeL
  have hdual (f : E →L[𝕜] 𝕜) : ∑ i, f (b i) • b.coord i = f := by
    have h := (DualBasisBasicity.finite_dual_facts b).2.2.1 f n le_rfl
    simpa using h
  let d : UnconditionalSchauderBasis (Fin n) 𝕜 F :=
    { basis := e'
      coord := ev
      ortho := by
        intro i j
        simp only [ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          Submodule.subtypeL_apply, e']
        simp [b.ortho, Pi.single_apply, eq_comm]
      expansion := by
        intro f
        have hf : ∑ i, ev i f • e' i = f := by
          apply Subtype.ext
          simpa only [Submodule.coe_sum, Submodule.coe_smul, ev,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
            Submodule.subtypeL_apply] using hdual f.val
        simpa only [hf] using (hasSum_fintype (fun i : Fin n => ev i f • e' i)) }
  obtain ⟨hbasic, htop, _, htail, _⟩ := DualBasisBasicity.finite_dual_facts b
  refine ⟨hbasic, ⟨fun _ => htop, fun _ => finite_shrinking b⟩,
    ⟨fun _ => htail, fun _ => finite_shrinking b⟩, d, rfl, (fun _ _ => rfl),
    ⟨fun _ => finite_shrinking b, fun _ => finite_boundedly_complete d.basis⟩,
    ⟨fun _ => finite_boundedly_complete b.basis, fun _ => finite_shrinking d⟩,
    ⟨fun _ => ⟨finite_shrinking b, finite_boundedly_complete b.basis⟩,
      fun _ => finite_reflexive b⟩⟩

theorem raw_finite_dual_bases : Spec.RawFiniteDualBases := by
  intro 𝕜 E _ _ _ _ n e h
  obtain ⟨b, he, hc, _⟩ := C15CoordinateContinuity.finite_native_basis h
  exact ⟨b, he, hc, finite_dual_bases b⟩

end ExpandedFA.P1.DualBases
