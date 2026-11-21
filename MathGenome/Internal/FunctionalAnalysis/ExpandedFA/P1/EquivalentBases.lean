import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EquivalentBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03Neumann
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

open Filter Topology
open scoped BigOperators Classical
noncomputable section
universe u v w
namespace ExpandedFA.P1.EquivalentBases
open Spec
open ExpandedFA.P1.C15Basis ExpandedFA.P1.C15CoordinateContinuity

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Synthesis of finite combinations, with values in the inherited closed span. -/
def synthesis {ι : Type*} (x : ι → E) : (ι →₀ 𝕜) →ₗ[𝕜] closedSpan (𝕜 := 𝕜) x :=
  Finsupp.linearCombination 𝕜 (spanVector (𝕜 := 𝕜) x)

@[simp] theorem synthesis_coe {ι : Type*} (x : ι → E) (a : ι →₀ 𝕜) :
    (synthesis x a : E) = Finsupp.linearCombination 𝕜 x a := by
  simp [synthesis, Finsupp.linearCombination_apply, Finsupp.sum, spanVector]

@[simp] theorem norm_synthesis {ι : Type*} (x : ι → E) (a : ι →₀ 𝕜) :
    ‖synthesis x a‖ = ‖Finsupp.linearCombination 𝕜 x a‖ := by
  change ‖(synthesis x a : E)‖ = _
  rw [synthesis_coe]

/-- Finite synthesis is dense even when the vectors are linearly dependent. -/
theorem synthesis_dense {ι : Type*} (x : ι → E) : DenseRange (synthesis (𝕜 := 𝕜) x) := by
  let S := Submodule.span 𝕜 (Set.range x)
  have hd : DenseRange (Submodule.inclusion S.le_topologicalClosure) := by
    exact (denseRange_inclusion_iff S.le_topologicalClosure).mpr (by rfl)
  have hs : ∀ z : S, ∃ a, synthesis (𝕜 := 𝕜) x a = Submodule.inclusion S.le_topologicalClosure z := by
    intro z
    have hz : z.val ∈ (Finsupp.linearCombination 𝕜 x).range := by
      rw [Finsupp.range_linearCombination]
      exact z.property
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  exact hd.mono (by rintro _ ⟨z, rfl⟩; exact hs z)

/-- The criterion holds in fact for arbitrary indexed families: the two norm
bounds make finite synthesis descend and extend in both directions. -/
theorem equivalentFamilies_iff {ι : Type*} [CompleteSpace E] [CompleteSpace F]
    (x : ι → E) (y : ι → F) :
    EquivalentFamilies (𝕜 := 𝕜) x y ↔ FiniteSumBounds (𝕜 := 𝕜) x y := by
  constructor
  · rintro ⟨U, hU⟩
    have hmap (a : ι →₀ 𝕜) : U (synthesis x a) = synthesis y a := by
      simp [synthesis, Finsupp.linearCombination_apply, Finsupp.sum, hU]
    let c : ℝ := (‖U.symm.toContinuousLinearMap‖ + 1)⁻¹
    let C : ℝ := max c ‖U.toContinuousLinearMap‖
    have hc : 0 < c := inv_pos.mpr (by positivity)
    refine ⟨c, C, hc, le_max_left _ _, fun a => ⟨?_, ?_⟩⟩
    · have hi := U.symm.toContinuousLinearMap.le_opNorm (synthesis y a)
      change ‖U.symm (synthesis y a)‖ ≤ _ at hi
      rw [← hmap, U.symm_apply_apply, hmap] at hi
      have hh : ‖synthesis x a‖ ≤ (‖U.symm.toContinuousLinearMap‖ + 1) * ‖synthesis y a‖ := by
        nlinarith [norm_nonneg (synthesis y a)]
      have := (inv_mul_le_iff₀ (by positivity : 0 < ‖U.symm.toContinuousLinearMap‖ + 1)).mpr hh
      simpa only [c, norm_synthesis] using this
    · have hh := U.toContinuousLinearMap.le_opNorm (synthesis x a)
      change ‖U (synthesis x a)‖ ≤ _ at hh
      rw [hmap] at hh
      exact (show ‖Finsupp.linearCombination 𝕜 y a‖ ≤ ‖U.toContinuousLinearMap‖ *
        ‖Finsupp.linearCombination 𝕜 x a‖ from (by simpa only [norm_synthesis] using hh)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rintro ⟨c, C, hc, _, hbound⟩
    have h₁ : ∃ C, ∀ a, ‖synthesis (𝕜 := 𝕜) y a‖ ≤ C * ‖synthesis (𝕜 := 𝕜) x a‖ :=
      ⟨C, fun a => by simpa only [norm_synthesis] using (hbound a).2⟩
    have h₂ : ∃ C, ∀ a, ‖synthesis (𝕜 := 𝕜) x a‖ ≤ C * ‖synthesis (𝕜 := 𝕜) y a‖ := by
      refine ⟨c⁻¹, fun a => ?_⟩
      simpa only [norm_synthesis] using (le_inv_mul_iff₀ hc).mpr (hbound a).1
    let U := (LinearEquiv.refl 𝕜 (ι →₀ 𝕜)).extend (synthesis x) (synthesis y)
      (synthesis_dense x) h₁ (synthesis_dense y) h₂
    refine ⟨U, fun i => ?_⟩
    have hh := LinearEquiv.extend_eq (LinearEquiv.refl 𝕜 (ι →₀ 𝕜))
      (synthesis x) (synthesis y) (synthesis_dense x) h₁ (synthesis_dense y) h₂
      (Finsupp.single i 1)
    simpa [U, synthesis] using hh

theorem equivalence_criterion : Spec.EquivalenceCriterion := by
  intro 𝕜 E F _ _ _ _ _ _ _ x y _ _
  exact equivalentFamilies_iff x y

/-- Unique ordered expansions are preserved by a bounded linear isomorphism. -/
theorem raw_basis_image {x : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) x)
    (U : E ≃L[𝕜] F) : IsRawSchauderBasis (𝕜 := 𝕜) (fun i => U (x i)) := by
  refine ⟨fun i hi => h.1 i (U.injective (by simpa using hi)), fun z => ?_⟩
  obtain ⟨a, ha, hu⟩ := h.2 (U.symm z)
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · change Tendsto (fun N => ∑ i ∈ Finset.range N, a i • U (x i)) atTop (𝓝 z)
    have hh := (U.continuous.tendsto (U.symm z)).comp ha
    simpa [orderedPartialSum, C15Basis.Spec.orderedPartialSum, Function.comp_def, map_sum, map_smul] using hh
  · change Tendsto (fun N => ∑ i ∈ Finset.range N, b i • x i) atTop (𝓝 (U.symm z))
    have hh := (U.symm.continuous.tendsto z).comp hb
    simpa [orderedPartialSum, C15Basis.Spec.orderedPartialSum, Function.comp_def, map_sum, map_smul] using hh

/-- Finite unique expansions, including the empty family, are also preserved. -/
theorem finite_basis_image {d : ℕ} {x : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) x) (U : E ≃L[𝕜] F) :
    IsRawFiniteBasis (𝕜 := 𝕜) (fun i => U (x i)) := by
  refine ⟨fun i hi => h.1 i (U.injective (by simpa using hi)), fun z => ?_⟩
  obtain ⟨a, ha, hu⟩ := h.2 (U.symm z)
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · simpa [finiteSynthesis, C15Basis.Spec.finiteSynthesis, map_sum, map_smul] using congrArg U ha
  · simpa [finiteSynthesis, C15Basis.Spec.finiteSynthesis, map_sum, map_smul] using congrArg U.symm hb

/-- A homeomorphic linear map carries a closed span onto the closed span of
its images; this is the bridge from ambient automorphisms to equivalence. -/
theorem map_closedSpan {ι : Type*} (U : E ≃L[𝕜] F) (x : ι → E) :
    (closedSpan (𝕜 := 𝕜) x).map U.toLinearMap = closedSpan (fun i => U (x i)) := by
  apply SetLike.coe_injective
  change U '' closure (Submodule.span 𝕜 (Set.range x) : Set E) = _
  rw [← ContinuousLinearEquiv.coe_toHomeomorph, U.toHomeomorph.image_closure]
  simp only [ContinuousLinearEquiv.coe_toHomeomorph]
  have hh := Submodule.map_span U.toLinearMap (Set.range x)
  change closure (↑((Submodule.span 𝕜 (Set.range x)).map U.toLinearMap) : Set F) = _
  rw [hh]
  congr 3
  exact (Set.range_comp U x).symm

theorem basic_image {x : ℕ → E} (h : IsBasicSequence (𝕜 := 𝕜) x)
    (U : E ≃L[𝕜] F) :
    IsBasicSequence (𝕜 := 𝕜) (fun i => U (x i)) ∧
      EquivalentFamilies (𝕜 := 𝕜) x (fun i => U (x i)) := by
  let V := U.ofSubmodules (closedSpan x) (closedSpan (fun i => U (x i))) (map_closedSpan U x)
  have hv (i) : V (spanVector x i) = spanVector (fun i => U (x i)) i := rfl
  refine ⟨?_, V, hv⟩
  have hh := raw_basis_image h V
  change IsRawSchauderBasis (𝕜 := 𝕜) (spanVector (fun i => U (x i)))
  simpa only [hv] using hh

/-- An absolutely summable family of rank-one corrections with total operator
norm less than one gives an ambient automorphism with the prescribed images.
This lemma works for both finite and countably infinite index types. -/
theorem perturbation_automorphism {ι : Type*} [CompleteSpace E]
    (x y : ι → E) (f : ι → E →L[𝕜] 𝕜)
    (hbio : ∀ i j, f i (x j) = (Pi.single j (1 : 𝕜) : ι → 𝕜) i)
    (hs : Summable (fun i => ‖f i‖ * ‖y i - x i‖))
    (hsmall : (∑' i, ‖f i‖ * ‖y i - x i‖) < 1) :
    ∃ U : E ≃L[𝕜] E, ∀ i, U (x i) = y i := by
  classical
  let A : E →L[𝕜] E := ∑' i, (f i).smulRight (y i - x i)
  have hsn : Summable (fun i => ‖(f i).smulRight (y i - x i)‖) := by
    simpa only [ContinuousLinearMap.norm_smulRight_apply] using hs
  have hsa := hsn.of_norm
  have hA : ‖A‖ < 1 := by
    exact (norm_tsum_le_tsum_norm hsn).trans_lt (by
      simpa only [ContinuousLinearMap.norm_smulRight_apply] using hsmall)
  have hAx (j) : A (x j) = y j - x j := by
    rw [show A (x j) = ∑' i, (f i).smulRight (y i - x i) (x j) from
      (ContinuousLinearMap.apply 𝕜 E (x j)).map_tsum hsa]
    simp [ContinuousLinearMap.smulRight_apply, hbio, Pi.single_apply]
  obtain ⟨S, _, _, _, hleft, hright, _⟩ :=
    C03Neumann.neumann_inversion 𝕜 E (-A) (by simpa using hA)
  let B : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - (-A)
  let U : E ≃L[𝕜] E :=
    { toLinearMap := B.toLinearMap
      invFun := S
      left_inv := fun z => by
        have hh := DFunLike.congr_fun hright z
        simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          LinearMap.toFun_eq_coe, ContinuousLinearMap.coe_coe] using hh
      right_inv := fun z => by
        have hh := DFunLike.congr_fun hleft z
        simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          LinearMap.toFun_eq_coe, ContinuousLinearMap.coe_coe] using hh
      continuous_toFun := B.continuous
      continuous_invFun := S.continuous }
  refine ⟨U, fun j => ?_⟩
  change x j - (-A) (x j) = y j
  simp [hAx]

/-- Hahn–Banach extends the actual coordinates of a basic sequence to the
ambient space, preserving the precise `2K / ‖xₙ‖` estimate. -/
theorem extended_coordinates [CompleteSpace E] {x : ℕ → E}
    (h : IsBasicSequence (𝕜 := 𝕜) x)
    (T : ℕ → closedSpan (𝕜 := 𝕜) x →L[𝕜] closedSpan (𝕜 := 𝕜) x)
    (hT : ∀ N z, T N z = C15Basis.Spec.rawPartialSum h N z) :
    0 ≤ C15PartialSums.Spec.basisConstant T ∧
    ∃ f : ℕ → E →L[𝕜] 𝕜,
      (∀ i j, f i (x j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i) ∧
      (∀ i, ‖f i‖ ≤ 2 * C15PartialSums.Spec.basisConstant T / ‖x i‖) := by
  obtain ⟨T₀, H, _, hcoord⟩ := C15PartialSums.raw_partial_sum_bounds h
  have hTeq : T₀ = T := by
    funext N
    apply ContinuousLinearMap.ext
    intro z
    exact (H.agrees N z).trans (hT N z).symm
  subst T₀
  obtain ⟨b, hbe, hba, _⟩ := raw_native_basis h
  have hb (i) : b i = spanVector x i := congrFun hbe i
  have hpos (i) : 0 < ‖x i‖ := by
    apply norm_pos_iff.mpr
    intro hi
    exact h.1 i (Subtype.ext hi)
  choose f hf hnorm using fun i =>
    C05NormExtension.norm_preserving_extension 𝕜 E (closedSpan x) (b.coord i)
  refine ⟨H.nonneg, f, ?_, fun i => ?_⟩
  · intro i j
    rw [← show (spanVector (𝕜 := 𝕜) x j : E) = x j from rfl, hf, ← hb]
    by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using b.ortho i j
  · rw [hnorm]
    apply (b.coord i).opNorm_le_bound (div_nonneg (by nlinarith [H.nonneg]) (norm_nonneg _))
    intro z
    rw [hba]
    calc
      ‖C15Basis.Spec.rawCoordinates h z i‖ ≤
          (2 * C15PartialSums.Spec.basisConstant T * ‖z‖) / ‖x i‖ :=
        (le_div_iff₀ (hpos i)).mpr (hcoord i z)
      _ = (2 * C15PartialSums.Spec.basisConstant T / ‖x i‖) * ‖z‖ := by ring

/-- The source's quantitative small-perturbation theorem; the second sequence
is proved basic rather than assumed basic. -/
theorem small_perturbation : Spec.SmallPerturbation := by
  intro 𝕜 E _ _ _ _ x y h T hT hs hsmall
  obtain ⟨hK, f, hf, hfnorm⟩ := extended_coordinates h T hT
  have hmajor (i) : ‖f i‖ * ‖y i - x i‖ ≤
      (2 * C15PartialSums.Spec.basisConstant T) * (‖y i - x i‖ / ‖x i‖) := by
    calc
      _ ≤ (2 * C15PartialSums.Spec.basisConstant T / ‖x i‖) * ‖y i - x i‖ :=
        mul_le_mul_of_nonneg_right (hfnorm i) (norm_nonneg _)
      _ = _ := by ring
  have hm := hs.mul_left (2 * C15PartialSums.Spec.basisConstant T)
  have hsf := Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmajor hm
  have hsum : (∑' i, ‖f i‖ * ‖y i - x i‖) < 1 := by
    apply (hsf.tsum_le_tsum hmajor hm).trans_lt
    simpa only [tsum_mul_left] using hsmall
  obtain ⟨U, hU⟩ := perturbation_automorphism x y f (fun i j => by by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using hf i j) hsf hsum
  have hy : (fun i => U (x i)) = y := funext hU
  have hh := basic_image h U
  rw [hy] at hh
  exact ⟨hh.1, hh.2, U, hU⟩

/-- Choose a perturbation in a dense set using any strictly positive summable
error budget of total mass less than one. -/
theorem dense_perturbation {ι : Type*} [CompleteSpace E]
    (x : ι → E) (f : ι → E →L[𝕜] 𝕜)
    (hbio : ∀ i j, f i (x j) = (Pi.single j (1 : 𝕜) : ι → 𝕜) i)
    (g : ι → ℝ) (hgpos : ∀ i, 0 < g i) (hg : Summable g) (hgs : (∑' i, g i) < 1)
    (D : Set E) (hD : Dense D) :
    ∃ y : ι → E, (∀ i, y i ∈ D) ∧ ∃ U : E ≃L[𝕜] E, ∀ i, U (x i) = y i := by
  have hex (i) : ∃ y ∈ D, ‖y - x i‖ < g i / (‖f i‖ + 1) := by
    obtain ⟨y, hy, hdist⟩ := hD.exists_dist_lt (x i) (ε := g i / (‖f i‖ + 1)) (div_pos (hgpos i) (by positivity))
    exact ⟨y, hy, by simpa only [dist_eq_norm, norm_sub_rev] using hdist⟩
  choose y hy herr using hex
  have hmajor (i) : ‖f i‖ * ‖y i - x i‖ ≤ g i := by
    have hh := (lt_div_iff₀ (by positivity : 0 < ‖f i‖ + 1)).mp (herr i)
    nlinarith [norm_nonneg (y i - x i)]
  have hs := Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmajor hg
  obtain ⟨U, hU⟩ := perturbation_automorphism x y f hbio hs ((hs.tsum_le_tsum hmajor hg).trans_lt hgs)
  exact ⟨y, hy, U, hU⟩

/-- An equivalent Schauder basis can be chosen inside any dense subset. -/
theorem dense_basis : Spec.DenseBasis := by
  intro 𝕜 E _ _ _ _ x h D hD
  obtain ⟨b, hbe, _, _⟩ := raw_native_basis h
  have hbio (i j) : b.coord i (x j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    rw [← congrFun hbe j]
    by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using b.ortho i j
  let g : ℕ → ℝ := fun n => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n
  have hg : HasSum g (1 / 2 : ℝ) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 4 : ℝ) using 1 <;> norm_num
  obtain ⟨y, hy, U, hU⟩ := dense_perturbation x b.coord (fun i j => by by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using hbio i j) g
    (fun n => by dsimp [g]; positivity) hg.summable (by rw [hg.tsum_eq]; norm_num) D hD
  refine ⟨y, hy, ?_, U, hU⟩
  have hh := raw_basis_image h U
  rwa [show (fun i => U (x i)) = y from funext hU] at hh

/-- The finite-dimensional conclusion includes a list of length zero. -/
theorem dense_finite_basis : Spec.DenseFiniteBasis := by
  intro 𝕜 E _ _ _ _ d x h D hD
  obtain ⟨b, hbe, _, _⟩ := finite_native_basis h
  have hbio (i j) : b.coord i (x j) = (Pi.single j (1 : 𝕜) : Fin d → 𝕜) i := by
    rw [← congrFun hbe j]
    by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using b.ortho i j
  let g : Fin d → ℝ := fun _ => 1 / (2 * ((d : ℝ) + 1))
  have hgpos (i) : 0 < g i := by dsimp [g]; positivity
  have hgs : (∑' i, g i) < 1 := by
    simp only [g, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← div_eq_mul_one_div]
    apply (div_lt_one (by positivity : 0 < 2 * ((d : ℝ) + 1))).mpr
    linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨y, hy, U, hU⟩ := dense_perturbation x b.coord (fun i j => by by_cases hij : i = j <;> simpa [Pi.single_apply, hij] using hbio i j) g hgpos
    (hasSum_fintype g).summable hgs D hD
  refine ⟨y, hy, ?_, U, hU⟩
  have hh := finite_basis_image h U
  rwa [show (fun i => U (x i)) = y from funext hU] at hh

end ExpandedFA.P1.EquivalentBases
