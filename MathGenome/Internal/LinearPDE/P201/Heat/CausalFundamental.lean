import MathGenome.Internal.LinearPDE.P201.Heat.GaussianKernel
import MathGenome.Internal.LinearPDE.P201Specs.Heat.CausalFundamental
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HeatFundamental
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology
namespace P201.Heat

abbrev causalKernel : P201Specs.Heat.causalKernelType :=
  P201Specs.Heat.causalKernel

/-- Splitting the time coordinate and restoring the spatial Euclidean norm. -/
def heatCoordinates (n : ℕ) : (Fin (n + 1) → ℝ) ≃L[ℝ] Space n × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => (WithLp.toLp 2 (Fin.tail z), z 0)
      invFun := fun p => Fin.cons p.2 (WithLp.ofLp p.1)
      left_inv := by intro z; exact Fin.cons_self_tail z
      right_inv := by intro p; rfl
      map_add' := by intro z w; rfl
      map_smul' := by intro c z; rfl }

lemma heatCoordinates_apply (n : ℕ) (z : Fin (n + 1) → ℝ) :
    heatCoordinates n z = (WithLp.toLp 2 (Fin.tail z), z 0) := rfl

lemma heatCoordinates_measurePreserving (n : ℕ) : MeasurePreserving (heatCoordinates n) := by
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have h₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  have h₃ := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Space n)))).comp (h₂.comp h₁)
  convert h₃ using 1
  ext z
  simp [heatCoordinates_apply, Function.comp_def, MeasurableEquiv.piFinSuccAbove,
    Fin.insertNthEquiv, Fin.tail]
  rfl

lemma causalKernel_coordinates (n : ℕ) (z : Fin (n + 1) → ℝ) :
    causalKernel n (heatCoordinates n z) =
      ExpandedFA.PartIV.HeatFundamental.heatKernel n z := by
  change (if 0 < z 0 then P201Specs.Heat.gaussianKernel n (z 0)
    (WithLp.toLp 2 (Fin.tail z)) else 0) =
    (if 0 < z 0 then ExpandedFA.PartIV.HeatFundamental.gaussianSlice n (z 0)
      (Fin.tail z) else 0)
  split_ifs
  · unfold P201Specs.Heat.gaussianKernel ExpandedFA.PartIV.HeatFundamental.gaussianSlice
    congr 2
    rw [PiLp.norm_sq_eq_of_L2]
    simp [ExpandedFA.PartIV.HeatFundamental.spatialSquare, Real.norm_eq_abs, sq_abs]
  · rfl

theorem causalLocallyIntegrable : P201Specs.Heat.causalLocallyIntegrableStatement := by
  intro n _
  apply locallyIntegrable_iff.2
  intro K hK
  apply ((heatCoordinates_measurePreserving n).integrableOn_comp_preimage
    (heatCoordinates n).toHomeomorph.measurableEmbedding).1
  have heq : causalKernel n ∘ heatCoordinates n =
      ExpandedFA.PartIV.HeatFundamental.heatKernel n :=
    funext (causalKernel_coordinates n)
  rw [heq]
  exact (ExpandedFA.PartIV.HeatFundamental.heatKernel_locallyIntegrable_real n).integrableOn_isCompact ((heatCoordinates n).toHomeomorph.isCompact_preimage.mpr hK)

/-- Pull back any smooth compactly supported test, with no extra hypotheses. -/
def heatTestPullback {n : ℕ} (φ : Space n × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ExpandedFA.PartIV.HeatFundamental.SpaceTimeTests ℝ n :=
  ⟨φ ∘ heatCoordinates n, hφ.comp (heatCoordinates n).contDiff,
    hc.comp_homeomorph (heatCoordinates n).toHomeomorph, by intro x _; trivial⟩

lemma heatCoordinates_time (n : ℕ) :
    heatCoordinates n (ExpandedFA.Distributions.coordinateVector (0 : Fin (n + 1))) =
      (0, 1) := by
  ext i <;> simp [heatCoordinates_apply, ExpandedFA.Distributions.coordinateVector, Fin.tail]

lemma heatCoordinates_spatial (n : ℕ) (i : Fin n) :
    heatCoordinates n (ExpandedFA.Distributions.coordinateVector i.succ) =
      (coordinate n i, 0) := by
  ext j <;> simp [heatCoordinates_apply, ExpandedFA.Distributions.coordinateVector,
    Fin.tail, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma fderiv_heatCoordinates {n : ℕ} {f : Space n × ℝ → ℝ}
    (hf : Differentiable ℝ f) (z v : Fin (n + 1) → ℝ) :
    fderiv ℝ (f ∘ heatCoordinates n) z v =
      fderiv ℝ f (heatCoordinates n z) (heatCoordinates n v) := by
  rw [fderiv_comp z (hf _) (heatCoordinates n).differentiableAt,
    (heatCoordinates n).hasFDerivAt.fderiv]
  rfl

lemma fderiv_spatialSlice {n : ℕ} {f : Space n × ℝ → ℝ}
    (hf : Differentiable ℝ f) (x v : Space n) (t : ℝ) :
    fderiv ℝ (fun y => f (y, t)) x v = fderiv ℝ f (x, t) (v, 0) := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) t x)
  have hd := (hf (x, t)).hasFDerivAt.comp x hi
  change HasFDerivAt (fun y => f (y, t)) _ x at hd
  rw [hd.fderiv]
  rfl

lemma deriv_timeSlice {n : ℕ} {f : Space n × ℝ → ℝ}
    (hf : Differentiable ℝ f) (x : Space n) (t : ℝ) :
    deriv (fun s => f (x, s)) t = fderiv ℝ f (x, t) (0, 1) := by
  exact ((hf (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv

lemma heat_time_partial {n : ℕ} {φ : Space n × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (z : Fin (n + 1) → ℝ) :
    ExpandedFA.Distributions.partialFunction [0] (φ ∘ heatCoordinates n) z =
      deriv (fun t => φ ((heatCoordinates n z).1, t)) (heatCoordinates n z).2 := by
  change fderiv ℝ (φ ∘ heatCoordinates n) z
    (ExpandedFA.Distributions.coordinateVector 0) = _
  rw [fderiv_heatCoordinates (hφ.differentiable (by simp)), heatCoordinates_time,
    deriv_timeSlice (hφ.differentiable (by simp))]

lemma heat_spatial_partial {n : ℕ} {φ : Space n × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin n) (z : Fin (n + 1) → ℝ) :
    ExpandedFA.Distributions.partialFunction [i.succ, i.succ]
      (φ ∘ heatCoordinates n) z =
      fderiv ℝ (fun y => fderiv ℝ (fun x => φ (x, (heatCoordinates n z).2)) y
        (coordinate n i)) (heatCoordinates n z).1 (coordinate n i) := by
  let g : Space n × ℝ → ℝ := fun p => fderiv ℝ φ p (coordinate n i, 0)
  have hg : ContDiff ℝ ∞ g :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have heq : ExpandedFA.Distributions.partialFunction [i.succ]
      (φ ∘ heatCoordinates n) = g ∘ heatCoordinates n := by
    funext w
    change fderiv ℝ (φ ∘ heatCoordinates n) w
      (ExpandedFA.Distributions.coordinateVector i.succ) = _
    rw [fderiv_heatCoordinates (hφ.differentiable (by simp)), heatCoordinates_spatial]
    rfl
  change fderiv ℝ (ExpandedFA.Distributions.partialFunction [i.succ]
    (φ ∘ heatCoordinates n)) z (ExpandedFA.Distributions.coordinateVector i.succ) = _
  rw [heq, fderiv_heatCoordinates (hg.differentiable (by simp)), heatCoordinates_spatial]
  have hslice : (fun y => fderiv ℝ (fun x => φ (x, (heatCoordinates n z).2)) y
      (coordinate n i)) = (fun y => g (y, (heatCoordinates n z).2)) := by
    funext y
    exact fderiv_spatialSlice (hφ.differentiable (by simp)) _ _ _
  rw [hslice, fderiv_spatialSlice (hg.differentiable (by simp))]

/-- The transported operator is precisely the common time derivative minus
spatial Laplacian, with the distributional transpose signs. -/
lemma adjointHeatTest_coordinates {n : ℕ} {φ : Space n × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (z : Fin (n + 1) → ℝ) :
    -(ExpandedFA.Distributions.testPartialCLM [0] (heatTestPullback φ hφ hc)) z -
      ∑ i : Fin n, (ExpandedFA.Distributions.testPartialCLM [i.succ, i.succ]
        (heatTestPullback φ hφ hc)) z =
      P201Specs.Heat.adjointHeatTest φ (heatCoordinates n z) := by
  have hp (w : List (Fin (n + 1))) (y : Fin (n + 1) → ℝ) :
      (ExpandedFA.Distributions.testPartialCLM w (heatTestPullback φ hφ hc)) y =
        ExpandedFA.Distributions.partialFunction w (φ ∘ heatCoordinates n) y :=
    congrFun (ExpandedFA.Distributions.testPartial_formula ℝ (n + 1) ⊤ w
      (heatTestPullback φ hφ hc)) y
  simp_rw [hp]
  rw [heat_time_partial hφ]
  unfold P201Specs.Heat.adjointHeatTest P201Specs.laplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [heat_spatial_partial hφ]
  change _ = P102.U4.partialWord (fun x => φ (x, (heatCoordinates n z).2))
    (({i, i} : Multiset (Fin n)).sort (· ≤ ·)) (heatCoordinates n z).1
  have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·))
      (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
  rw [hs]
  rfl

/-- Absolute integrability and the delta source at the space-time origin. -/
theorem causalFundamental : P201Specs.Heat.causalFundamentalStatement := by
  intro n hn φ hφ hc
  let ψ := heatTestPullback φ hφ hc
  let χ := -ExpandedFA.Distributions.testPartialCLM [0] ψ -
    ∑ i : Fin n, ExpandedFA.Distributions.testPartialCLM [i.succ, i.succ] ψ
  let f : Space n × ℝ → ℝ := fun z => causalKernel n z * P201Specs.Heat.adjointHeatTest φ z
  have heq (z : Fin (n + 1) → ℝ) :
      f (heatCoordinates n z) =
        ExpandedFA.PartIV.HeatFundamental.heatKernel n z * χ z := by
    dsimp only [f]
    rw [causalKernel_coordinates, ← adjointHeatTest_coordinates hφ hc]
    congr 1
    simp [χ, ψ]
  have hi : Integrable (f ∘ heatCoordinates n) := by
    have h := χ.integrable_smul (locallyIntegrableOn_univ.mpr
      (ExpandedFA.PartIV.HeatFundamental.heatKernel_locallyIntegrable_real n))
    simpa only [Function.comp_def, heq, smul_eq_mul, mul_comm] using h
  have hf : Integrable f :=
    ((heatCoordinates_measurePreserving n).integrable_comp_emb
      (heatCoordinates n).toHomeomorph.measurableEmbedding).1 hi
  have hw := ExpandedFA.PartIV.HeatFundamental.weak_identity ℝ n ψ
  have hvalue : (∫ z, f z) = φ (0, 0) := by
    rw [← (heatCoordinates_measurePreserving n).integral_comp
      (heatCoordinates n).toHomeomorph.measurableEmbedding f]
    simp_rw [heq]
    convert hw using 1
    · congr 1
      funext z
      congr 1
      simp [χ]
    · rfl
  refine ⟨hf, hvalue, ?_⟩
  change (∫ t : ℝ, ∫ x : Space n, f (x, t)) = φ (0, 0)
  rw [← integral_prod_symm f hf]
  exact hvalue

end P201.Heat
