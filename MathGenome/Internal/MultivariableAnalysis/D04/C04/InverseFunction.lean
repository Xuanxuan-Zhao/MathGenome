import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InverseFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C04.QuantitativeInverseBall
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open Set Filter Topology
open scoped ContDiff NNReal
namespace D04
open Specs.D04.C04.InverseFunction (InverseNeighborhood)

/-- Shrink a C^r local inverse to an open neighborhood in U where all
forward derivatives are invertible and the inverse has one Lipschitz constant.
This works for finite r and infinity, including the zero-dimensional space. -/
private theorem inverse_neighborhood {n : ℕ} {r : ℕ∞ω}
    (U : Set (E n)) (f : E n → E n) (a : E n) (A : E n ≃L[ℝ] E n)
    (hr : 1 ≤ r) (hU : IsOpen U) (hf : ContDiffOn ℝ r f U) (ha : a ∈ U)
    (hA : A.toContinuousLinearMap = fderiv ℝ f a) :
    ∃ X Y g, InverseNeighborhood U f a X Y g ∧ ContDiffOn ℝ r g Y := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hfa : ContDiffAt ℝ r f a := hf.contDiffAt (hU.mem_nhds ha)
  have hda : HasFDerivAt f A.toContinuousLinearMap a := by
    rw [hA]
    exact (hfa.differentiableAt hr0).hasFDerivAt
  let e := hfa.toOpenPartialHomeomorph f hda hr0
  have he : (e : E n → E n) = f := rfl
  have hae : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hda _
  have hfae : f a ∈ e.target := e.map_source hae
  have hega : e.symm (f a) = a := e.left_inv hae
  have hdcont : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hU hr).continuousAt (hU.mem_nhds ha)
  have hInv : {x : E n | ∃ B : E n ≃L[ℝ] E n,
      B.toContinuousLinearMap = fderiv ℝ f x} ∈ 𝓝 a := by
    have ht := hdcont.preimage_mem_nhds (by rw [← hA]; exact A.nhds)
    exact ht
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hInv)
  have hWU : W ⊆ U := fun x hx => (hWsub hx).1
  have hWB (x : E n) (hx : x ∈ W) :
      ∃ B : E n ≃L[ℝ] E n, B.toContinuousLinearMap = fderiv ℝ f x := (hWsub hx).2
  have hg0 : ContDiffAt ℝ r e.symm (f a) := by
    apply e.contDiffAt_symm hfae (f₀' := A)
    · simpa only [he, hega] using hda
    · simpa only [he, hega] using hfa
  obtain ⟨K, t, ht, hKt⟩ := (hg0.of_le hr).exists_lipschitzOnWith
  let Z := e.target ∩ e.symm ⁻¹' W
  have hZ : IsOpen Z := e.isOpen_inter_preimage_symm hW
  have hfaZ : f a ∈ Z := ⟨hfae, by simpa only [mem_preimage, hega] using haW⟩
  obtain ⟨Y, hYsub, hY, hfaY⟩ := mem_nhds_iff.mp (inter_mem (hZ.mem_nhds hfaZ) ht)
  let X := (e.source ∩ f ⁻¹' Y) ∩ W
  have hX : IsOpen X := (e.isOpen_inter_preimage hY).inter hW
  have haX : a ∈ X := ⟨⟨hae, hfaY⟩, haW⟩
  have hYT : Y ⊆ e.target := fun y hy => (hYsub hy).1.1
  have hgX : MapsTo e.symm Y X := by
    intro y hy
    refine ⟨⟨e.map_target (hYT hy), ?_⟩, (hYsub hy).1.2⟩
    change f (e.symm y) ∈ Y
    rw [show f (e.symm y) = y from e.right_inv (hYT hy)]
    exact hy
  have hXY : MapsTo f X Y := fun x hx => hx.1.2
  have hBij : BijOn f X Y := by
    refine ⟨hXY, e.injOn.mono (fun _ hx => hx.1.1), ?_⟩
    intro y hy
    exact ⟨e.symm y, hgX hy, e.right_inv (hYT hy)⟩
  have hgder (y : E n) (hy : y ∈ Y) :
      ∃ B : E n ≃L[ℝ] E n, B.toContinuousLinearMap = totalDerivative f (e.symm y) ∧
        HasTotalDerivative Y e.symm B.symm.toContinuousLinearMap y ∧
        totalDerivative e.symm y = B.symm.toContinuousLinearMap := by
    obtain ⟨B, hB⟩ := hWB (e.symm y) (hgX hy).2
    have hd : HasFDerivAt f B.toContinuousLinearMap (e.symm y) := by
      rw [hB]
      exact ((hf.contDiffAt (hU.mem_nhds (hWU (hgX hy).2))).differentiableAt
        hr0).hasFDerivAt
    have hgd := e.hasFDerivAt_symm (hYT hy) (f' := B) (by simpa only [he] using hd)
    exact ⟨B, hB, (hasTotalDerivative_iff_hasFDerivAt Y _ _ y hY hy).mpr hgd,
      hgd.fderiv⟩
  refine ⟨X, Y, e.symm, ?_, ?_⟩
  · refine ⟨hX, hY, haX, hfaY, fun x hx => hWU hx.2, hBij, hgX,
      fun x hx => e.left_inv hx.1.1, fun y hy => e.right_inv (hYT hy),
      fun x hx => hWB x hx.2, hgder, ⟨K, hKt.mono (fun y hy => (hYsub hy).2)⟩, ?_⟩
    intro y hy x hx
    constructor
    · intro hxy
      rw [← hxy]
      exact (e.left_inv hx.1.1).symm
    · intro hxy
      rw [hxy]
      exact e.right_inv (hYT hy)
  · intro y hy
    obtain ⟨B, hB⟩ := hWB (e.symm y) (hgX hy).2
    have hfd := hf.contDiffAt (hU.mem_nhds (hWU (hgX hy).2))
    apply (e.contDiffAt_symm (hYT hy) (f₀' := B) ?_ (by simpa only [he] using hfd)).contDiffWithinAt
    change HasFDerivAt f B.toContinuousLinearMap (e.symm y)
    rw [hB]
    exact (hfd.differentiableAt hr0).hasFDerivAt

/-- Local inverse with each positive finite order of regularity. -/
theorem inverse_function_finite : Specs.D04.C04.InverseFunction.inverse_function_finiteType := by
  intro n r U f a A hr hU hf ha hA
  obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_neighborhood U f a A.toContinuousLinearEquiv
    (by exact_mod_cast hr) hU ((crOn_iff_contDiffOn r U f hU).mp hf) ha hA
  exact ⟨X, Y, g, hgeom, (crOn_iff_contDiffOn r Y g hgeom.2.1).mpr hg⟩

/-- The same construction with C^∞ data supplies a C^∞ inverse. -/
theorem inverse_function_smooth : Specs.D04.C04.InverseFunction.inverse_function_smoothType := by
  intro n U f a A hU hf ha hA
  obtain ⟨X, Y, g, hgeom, hg⟩ := inverse_neighborhood (r := ∞) U f a A.toContinuousLinearEquiv
    (by simp) hU ((smoothOn_iff_contDiffOn U f hU).mp hf) ha hA
  exact ⟨X, Y, g, hgeom, (smoothOn_iff_contDiffOn Y g hgeom.2.1).mpr hg⟩

/-- The quantitative assertion retains the exact A^{-1}-norm, all admissible
targets, uniqueness on the closed ball, and strict interior membership. -/
theorem inverse_function_quantitative :
    Specs.D04.C04.InverseFunction.inverse_function_quantitativeType := by
  intro n U f a A ρ q hU hf ha hA hρ hball hq hbound
  have hq0 : 0 ≤ q := (norm_nonneg _).trans
    (hbound a (Metric.mem_closedBall_self hρ.le))
  exact quantitative_inverse_ball U f a A ρ q hU hf ha hA hρ hball hq0 hq hbound

end D04
