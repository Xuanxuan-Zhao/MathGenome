import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.CoordinateCurves
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u

theorem uniqueDiffCurveDomain :
    Specs.SmoothManifolds.Tangent.CoordinateCurves.uniqueDiffCurveDomainType := by
  intro J hJ
  rcases hJ with rfl | rfl | rfl
  · exact uniqueDiffWithinAt_univ
  · exact uniqueDiffWithinAt_Ici 0
  · exact uniqueDiffWithinAt_Iic 0

theorem scalarDerivativeAlongCurve :
    Specs.SmoothManifolds.Tangent.CoordinateCurves.scalarDerivativeAlongCurveType.{u} := by
  intro n kind M _ p e J _hJ c hc hcont v hv F U hU hpU hF f hf
  have hd : DifferentiableAt ℝ F (e p).val :=
    (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hchain := hd.hasFDerivAt.comp_hasDerivWithinAt_of_eq (0 : ℝ) hv
    (by rw [hc])
  have heq : (f ∘ c) =ᶠ[𝓝[J] 0] (fun t => F (e (c t)).val) :=
    hf.comp_tendsto (by simpa only [ContinuousWithinAt, hc] using hcont)
  have h0 : (f ∘ c) 0 = F (e (c 0)).val := by
    simpa only [Function.comp_apply, hc] using hf.eq_of_nhds
  exact hchain.congr_of_eventuallyEq heq h0

/-- A full half-ray stays in the model; no sign condition is placed on v. -/
theorem exists_modelLine_domain {n : ℕ} {kind : ModelKind}
    (a : ModelSpace n kind) (v : Euclidean n) :
    ∃ J : Set ℝ, (J = univ ∨ J = Ici 0 ∨ J = Iic 0) ∧ 0 ∈ J ∧
      ∀ t ∈ J, a.val + t • v ∈ modelSet n kind := by
  cases kind with
  | euclidean => exact ⟨univ, Or.inl rfl, mem_univ _, fun _ _ => mem_univ _⟩
  | halfSpace =>
    cases n with
    | zero => exact ⟨univ, Or.inl rfl, mem_univ _, fun _ _ => mem_univ _⟩
    | succ n =>
      have ha : 0 ≤ a.val (Fin.last n) := a.property
      by_cases hv : 0 ≤ v (Fin.last n)
      · refine ⟨Ici 0, Or.inr (Or.inl rfl), by simp, ?_⟩
        intro t ht
        change 0 ≤ a.val (Fin.last n) + t * v (Fin.last n)
        exact add_nonneg ha (mul_nonneg ht hv)
      · refine ⟨Iic 0, Or.inr (Or.inr rfl), by simp, ?_⟩
        intro t ht
        change 0 ≤ a.val (Fin.last n) + t * v (Fin.last n)
        exact add_nonneg ha (mul_nonneg_of_nonpos_of_nonpos ht (le_of_not_ge hv))

/-- Realization of an arbitrary coordinate velocity, smooth in every atlas chart. -/
theorem existsCoordinateCurve :
    Specs.SmoothManifolds.Tangent.CoordinateCurves.existsCoordinateCurveType.{u} := by
  classical
  intro n kind M _ S p e he hp v
  obtain ⟨J, hJ, h0J, hline⟩ := exists_modelLine_domain (e p) v
  let L : ℝ → Euclidean n := fun t => (e p).val + t • v
  have hL0 : L 0 = (e p).val := by simp [L]
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hLs : ContDiff ℝ (⊤ : ℕ∞) L :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hLd : HasDerivAt L v 0 := by
    simpa [L] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (e p).val
  let q : ℝ → ModelSpace n kind := fun t =>
    if h : L t ∈ modelSet n kind then ⟨L t, h⟩ else e p
  have hqval (t : ℝ) (ht : t ∈ J) : (q t).val = L t := by
    have htL : L t ∈ modelSet n kind := hline t ht
    simp only [q, dite_eq_left htL]
  have hq0 : q 0 = e p := Subtype.ext ((hqval 0 h0J).trans hL0)
  have hqval_ev : (fun t => (q t).val) =ᶠ[𝓝[J] 0] L := by
    filter_upwards [self_mem_nhdsWithin] with t ht using hqval t ht
  have hqc : ContinuousWithinAt q J 0 := by
    apply tendsto_subtype_rng.mpr
    have hh : ContinuousWithinAt L J 0 := hLc.continuousAt.continuousWithinAt
    exact hh.congr_of_eventuallyEq hqval_ev (hqval 0 h0J)
  let c : ℝ → M := fun t => e.symm (q t)
  have hc0 : c 0 = p := by
    change e.symm (q 0) = p
    rw [hq0, e.left_inv hp]
  have hcc : ContinuousWithinAt c J 0 :=
    (e.symm.continuousAt (by rw [hq0]; exact e.map_source hp)).comp_continuousWithinAt hqc
  have hct : Tendsto c (𝓝[J] 0) (𝓝 p) := by
    simpa only [ContinuousWithinAt, hc0] using hcc
  have hec : (fun t => (e (c t)).val) =ᶠ[𝓝[J] 0] L := by
    have hqt : ∀ᶠ t in 𝓝[J] 0, q t ∈ e.target :=
      (show Tendsto q (𝓝[J] 0) (𝓝 (q 0)) from hqc).eventually
        (e.open_target.mem_nhds (by rw [hq0]; exact e.map_source hp))
    filter_upwards [hqt, hqval_ev] with t ht hval
    change (e (e.symm (q t))).val = L t
    rw [e.right_inv ht, hval]
  refine ⟨J, hJ, c, hc0, hcc,
    hLd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hec h0J, ?_⟩
  intro d hd hpd
  have hcompat := S.smoothStructure.property.1.2 e he d hd
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := chartContDiffAt_of_compatible hcompat hp hpd
  refine ⟨L ⁻¹' U, hU.preimage hLc, ?_, F ∘ L,
    hF.comp hLs.contDiffOn (fun t ht => ht), ?_⟩
  · change L 0 ∈ U
    rwa [hL0]
  · exact (heF.comp_tendsto hct).symm.trans (hec.fun_comp F)

end SmoothManifolds
