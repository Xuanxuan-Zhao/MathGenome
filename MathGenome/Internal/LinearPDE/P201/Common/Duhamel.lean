import MathGenome.Internal.LinearPDE.P201Specs.Common.Duhamel
import MathGenome.Internal.LinearPDE.P201.Common.IntegratedMild

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal

namespace P201.Common.Duhamel
open ExpandedFA ExpandedFA.Semigroups
open P201.Common.IntegratedMild

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- The L¹ part of Duhamel, for the identical generator and formula. -/
theorem integrated_duhamel : Expected.IntegratedDuhamel :=
  IntegratedMild.integrated_well_posedness

/-- Classical existence uses the same exact-domain graph norm and the same
formula as the integrated theorem. -/
theorem classical_duhamel : Expected.ClassicalDuhamel := by
  intro 𝕜 X _ _ _ _ S T _ x₀ f hf
  exact InhomogeneousEvolution.classical_existence S T x₀ f hf

/-- Integrate the graph-valued classical curve in the complete graph space.
Both graph coordinates are bounded linear maps, so the integral is in D(A)
and its A-coordinate is the integral of Au. This justifies the passage to the
integrated equation without commuting an unbounded operator with an integral. -/
theorem classical_isIntegrated (S : C0Semigroup 𝕜 X) (T : ℝ≥0) (x₀ : X)
    {f u : ℝ → X} (hf : IntegrableOn f (Icc 0 (T : ℝ)))
    (hsol : InhomogeneousEvolutionSpec.IsClassicalSolution S T x₀ f u) :
    IsIntegratedSolution S T x₀ f u := by
  obtain ⟨hu0, hu, huc, hud, hug⟩ := hsol
  let : CompleteSpace (Unbounded.GraphDomain (Generator S)) := graph_complete S
  let : NormedSpace ℝ (Unbounded.GraphDomain (Generator S)) :=
    NormedSpace.restrictScalars ℝ 𝕜 _
  let : IsScalarTower ℝ 𝕜 (Unbounded.GraphDomain (Generator S)) :=
    IsScalarTower.restrictScalars ℝ 𝕜 _
  let G : ℝ → Unbounded.GraphDomain (Generator S) :=
    IccExtend T.coe_nonneg (fun t => ⟨u t, hu t⟩)
  have hGc : Continuous G := hug.Icc_extend'
  have hGe (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      G r = (⟨u r, hu ⟨r, hr⟩⟩ : Unbounded.GraphDomain (Generator S)) :=
    IccExtend_of_mem T.coe_nonneg _ hr
  have hAc : Continuous (fun r => graphGenerator (Generator S) (G r)) :=
    (graphGenerator (Generator S)).continuous.comp hGc
  refine ⟨huc.continuousOn, ?_⟩
  intro t ht
  have hGi : IntervalIntegrable G volume 0 t := hGc.intervalIntegrable _ _
  have hAi : IntervalIntegrable (fun r => graphGenerator (Generator S) (G r))
      volume 0 t := hAc.intervalIntegrable _ _
  have hfi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      (hf.mono_set (Icc_subset_Icc le_rfl ht.2))
  let z : Unbounded.GraphDomain (Generator S) := ∫ r in (0 : ℝ)..t, G r
  have hz : (Unbounded.GraphDomain.toDomain _ z : X) = primitive (𝕜 := 𝕜) u t := by
    change graphInclusion (Generator S) (∫ r in (0 : ℝ)..t, G r) = _
    rw [← (graphInclusion (Generator S)).intervalIntegral_comp_comm hGi]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    dsimp only
    rw [hGe r ⟨hr.1, hr.2.trans ht.2⟩]
    rfl
  have hAz : Generator S (Unbounded.GraphDomain.toDomain _ z) =
      ∫ r in (0 : ℝ)..t, graphGenerator (Generator S) (G r) :=
    ((graphGenerator (Generator S)).intervalIntegral_comp_comm hGi).symm
  have hint : (∫ r in (0 : ℝ)..t, graphGenerator (Generator S) (G r) + f r) =
      u t - x₀ := by
    rw [← hu0]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (huc.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)) _ (hAi.add hfi)
    intro r hr
    rw [hGe r ⟨hr.1.le, hr.2.le.trans ht.2⟩]
    exact (hud ⟨r, hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))
  have hm : primitive (𝕜 := 𝕜) u t ∈ (Generator S).domain :=
    hz ▸ (Unbounded.GraphDomain.toDomain _ z).2
  refine ⟨hm, ?_⟩
  have hA : Generator S ⟨primitive (𝕜 := 𝕜) u t, hm⟩ =
      Generator S (Unbounded.GraphDomain.toDomain _ z) :=
    congrArg _ (Subtype.ext hz.symm)
  rw [intervalIntegral.integral_add hAi hfi, ← hAz] at hint
  rw [hA]
  change u t = x₀ + Generator S (Unbounded.GraphDomain.toDomain _ z) +
    ∫ r in (0 : ℝ)..t, f r
  rw [add_assoc, hint]
  abel

/-- A classical solution for arbitrary L¹ forcing obeys the formula. -/
theorem classical_converse : Expected.ClassicalConverse := by
  intro 𝕜 X _ _ _ _ S T hT x₀ f hf u hu
  have hi := classical_isIntegrated S T x₀ hf hu
  exact ⟨hi, ((IntegratedMild.integrated_well_posedness S T hT x₀ f hf).2.2.2 u).mp hi⟩

end P201.Common.Duhamel
