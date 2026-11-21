import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ConstrainedHessianBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C04.RegularLevel
import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.ConstrainedHessianBridge
open Specs.D04.C04.RegularLevel.Model

abbrev lagrangian : Specs.D04.C05.ConstrainedHessianBridge.lagrangianType :=
  @Specs.D04.C05.ConstrainedHessianBridge.Model.lagrangian

theorem lagrangian_coordinates :
    Specs.D04.C05.ConstrainedHessianBridge.lagrangian_coordinatesType := by
  intro n q f g lam x
  change f x - lam (g x) = _
  congr 1
  have he : g x = ∑ i : Fin q, g x i • standardBasis q i := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using
      ((standardBasis q).sum_repr (g x)).symm
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Twice differentiating composition, retaining the chart acceleration term. -/
theorem second_chain_rule {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S : Set X} {T : Set Y} {θ : X → Y} {f : Y → Z} {x : X}
    (hS : IsOpen S) (hT : IsOpen T) (hθ : ContDiffOn ℝ 2 θ S)
    (hf : ContDiffOn ℝ 2 f T) (hmap : MapsTo θ S T) (hx : x ∈ S) (u v : X) :
    higherDifferential 2 (f ∘ θ) x ![u,v] =
      higherDifferential 2 f (θ x) ![fderiv ℝ θ x u, fderiv ℝ θ x v] +
        fderiv ℝ f (θ x) (higherDifferential 2 θ x ![u,v]) := by
  have hθx := hθ.contDiffAt (hS.mem_nhds hx)
  have hfx := hf.contDiffAt (hT.mem_nhds (hmap hx))
  have hθ₁ := hθx.differentiableAt (by norm_num)
  have hθ₂ := (hθx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf₂ := (hfx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (f ∘ θ) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ f (θ y)).comp (fderiv ℝ θ y)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact fderiv_comp y
      (hf.contDiffAt (hT.mem_nhds (hmap hy)) |>.differentiableAt (by norm_num))
      (hθ.contDiffAt (hS.mem_nhds hy) |>.differentiableAt (by norm_num))
  have hd := (hf₂.hasFDerivAt.comp x hθ₁.hasFDerivAt).clm_comp hθ₂.hasFDerivAt
  have hh := (hd.congr_of_eventuallyEq he).fderiv
  change iteratedFDeriv ℝ 2 (f ∘ θ) x ![u,v] =
    iteratedFDeriv ℝ 2 f (θ x) ![fderiv ℝ θ x u, fderiv ℝ θ x v] +
      fderiv ℝ f (θ x) (iteratedFDeriv ℝ 2 θ x ![u,v])
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hh]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- Differentiation treats the multiplier as a fixed linear map. -/
theorem lagrangian_second {n q : ℕ} {f : E n → ℝ} {g : E n → E q}
    (lam : E q →L[ℝ] ℝ) {a : E n}
    (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a) (u v : E n) :
    higherDifferential 2 (lagrangian f g lam) a ![u,v] =
      higherDifferential 2 f a ![u,v] - lam (higherDifferential 2 g a ![u,v]) := by
  change iteratedFDeriv ℝ 2 (f - lam ∘ g) a ![u,v] = _
  rw [iteratedFDeriv_sub_apply hf (lam.contDiff.contDiffAt.comp a hg),
    lam.iteratedFDeriv_comp_left hg le_rfl]
  rfl

theorem chart_tangent_isomorphism :
    Specs.D04.C05.ConstrainedHessianBridge.chart_tangent_isomorphismType := by
  intro n q U g c hU hg d u hu
  let T := fderiv ℝ d.θ u
  let K := LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap
  have hk := RegularLevel.LevelGraph.kernel_eq d (by norm_num) hU hg u hu
  have hmem (w : E (n-q)) : T w ∈ K := by
    change T w ∈ LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap
    rw [← hk]
    exact ⟨w,rfl⟩
  let t : E (n-q) →ₗ[ℝ] K := T.toLinearMap.codRestrict K hmem
  have ht : Function.Bijective t := by
    constructor
    · intro v w hvw
      exact RegularLevel.LevelGraph.derivative_injective d (by norm_num) u hu
        (congrArg Subtype.val hvw)
    · intro v
      have hv : (v : E n) ∈ LinearMap.range T.toLinearMap := by
        rw [hk]
        exact v.property
      obtain ⟨w,hw⟩ := hv
      exact ⟨w, Subtype.ext hw⟩
  exact ⟨(LinearEquiv.ofBijective t ht).toContinuousLinearEquiv, fun _ => rfl⟩

theorem chart_second_variation :
    Specs.D04.C05.ConstrainedHessianBridge.chart_second_variationType := by
  intro n q U f g c hU hf hg lam d u a hu hea _hsurj hstat
  subst a
  have hmap : MapsTo d.θ d.A U := fun v hv =>
    (RegularLevel.LevelGraph.theta_mem d v hv).1.1
  have ht : ContDiffOn ℝ 2 d.θ d.A := RegularLevel.LevelGraph.theta_regular d
  have hta := ht.contDiffAt (d.open_A.mem_nhds hu)
  have hfa := hf.contDiffAt (hU.mem_nhds (hmap hu))
  have hga := hg.contDiffAt (hU.mem_nhds (hmap hu))
  have htd := hta.differentiableAt (by norm_num)
  have hfd := hfa.differentiableAt (by norm_num)
  have hgd := hga.differentiableAt (by norm_num)
  have hconst : (g ∘ d.θ) =ᶠ[𝓝 u] (fun _ => c) := by
    filter_upwards [d.open_A.mem_nhds hu] with v hv
    exact (RegularLevel.LevelGraph.theta_mem d v hv).1.2
  have hz : (fderiv ℝ g (d.θ u)).comp (fderiv ℝ d.θ u) = 0 := by
    exact ((hgd.hasFDerivAt.comp u htd.hasFDerivAt).congr_of_eventuallyEq hconst.symm).unique
      (hasFDerivAt_const c u)
  refine ⟨?_, ?_, ?_⟩
  · change fderiv ℝ (f - lam ∘ g) (d.θ u) = 0
    rw [fderiv_sub hfd (lam.differentiableAt.comp _ hgd),
      (lam.hasFDerivAt.comp _ hgd.hasFDerivAt).fderiv, hstat, sub_self]
  · rw [fderiv_comp u hfd htd, hstat, ContinuousLinearMap.comp_assoc, hz]
    simp
  · intro w
    have hfchain := second_chain_rule d.open_A hU ht hf hmap hu w w
    have hgchain := second_chain_rule d.open_A hU ht hg hmap hu w w
    have hzero : higherDifferential 2 (g ∘ d.θ) u ![w,w] = 0 := by
      change iteratedFDeriv ℝ 2 (g ∘ d.θ) u ![w,w] = 0
      rw [(hconst.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_const_of_ne (by decide)]
      rfl
    rw [hzero] at hgchain
    rw [hfchain, lagrangian_second lam hfa hga, hstat]
    change _ + lam ((fderiv ℝ g (d.θ u)) _) = _ - lam _
    have he := congrArg lam hgchain
    simp only [map_zero, map_add] at he
    linarith

open private hessian_basis from MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry

/-- The multiplier's coordinate weights multiply the component Hessians. -/
theorem fixed_multiplier_hessian :
    Specs.D04.C05.ConstrainedHessianBridge.fixed_multiplier_hessianType := by
  intro n q U f g hU hf hg lam a ha
  change hessian (lagrangian f g lam) a = hessian f a -
    ∑ k : Fin q, lam (standardBasis q k) • hessian (fun x => g x k) a
  have hl : ContDiffOn ℝ 2 (lagrangian f g lam) U :=
    hf.sub (lam.contDiff.comp_contDiffOn hg)
  have hgi (k : Fin q) : ContDiffOn ℝ 2 (fun x => g x k) U := by
    change ContDiffOn ℝ 2 ((PiLp.proj 2 (fun _ : Fin q => ℝ) k : E q →L[ℝ] ℝ) ∘ g) U
    exact (PiLp.proj 2 (fun _ : Fin q => ℝ) k : E q →L[ℝ] ℝ).contDiff.comp_contDiffOn hg
  have hfl := crOn_timesDifferentiableAt 2 U _ hU
    ((crOn_iff_contDiffOn 2 U _ hU).mpr hl) a ha
  have hff := crOn_timesDifferentiableAt 2 U _ hU
    ((crOn_iff_contDiffOn 2 U _ hU).mpr hf) a ha
  have hfg (k : Fin q) := crOn_timesDifferentiableAt 2 U _ hU
    ((crOn_iff_contDiffOn 2 U _ hU).mpr (hgi k)) a ha
  have hfa := hf.contDiffAt (hU.mem_nhds ha)
  have hga := hg.contDiffAt (hU.mem_nhds ha)
  ext i j
  change hessian (lagrangian f g lam) a i j = hessian f a i j -
    (∑ k : Fin q, lam (standardBasis q k) • hessian (fun x => g x k) a) i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← hessian_basis U _ a hfl i j, ← hessian_basis U f a hff i j,
    lagrangian_second lam hfa hga]
  congr 1
  let y := higherDifferential 2 g a ![standardBasis n i,standardBasis n j]
  have hy : y = ∑ k : Fin q, y k • standardBasis q k := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using
      ((standardBasis q).sum_repr y).symm
  change lam y = _
  rw [hy, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  change y k * lam (standardBasis q k) = lam (standardBasis q k) * _
  rw [mul_comm]
  congr 1
  rw [← hessian_basis U _ a (hfg k) i j]
  have hp := (PiLp.proj 2 (fun _ : Fin q => ℝ) k).iteratedFDeriv_comp_left hga
    (i := 2) le_rfl
  exact (congrArg (fun T => T ![standardBasis n i,standardBasis n j]) hp).symm

end D04.ConstrainedHessianBridge
