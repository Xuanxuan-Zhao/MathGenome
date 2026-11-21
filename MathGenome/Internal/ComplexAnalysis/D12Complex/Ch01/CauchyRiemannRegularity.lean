import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.CauchyRiemannRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
Regular sufficiency in d12:01-03. The real differentiability step uses
continuous coordinate partials on a neighbourhood, via the bivariate real
calculus theorem. The CR step then uses the pointwise theorem from d12:01-02.
-/
noncomputable section
open Complex Filter
open scoped Topology
namespace D12Complex

private theorem sliceX_hasDerivAt (u : ℂ → ℝ) (x y : ℝ)
    (h : DifferentiableAt ℝ (fun t : ℝ => u ((x : ℂ) + (y : ℂ) * I + t)) 0) :
    HasDerivAt (fun t : ℝ => u ((t : ℂ) + (y : ℂ) * I))
      (partialX u ((x : ℂ) + (y : ℂ) * I)) x := by
  have hd : HasDerivAt (fun t : ℝ => u ((x : ℂ) + (y : ℂ) * I + t))
      (partialX u ((x : ℂ) + (y : ℂ) * I)) (x - x) := by
    simpa [partialX] using h.hasDerivAt
  convert hd.comp_sub_const x x using 1
  ext t
  congr 1
  push_cast
  ring

private theorem sliceY_hasDerivAt (u : ℂ → ℝ) (x y : ℝ)
    (h : DifferentiableAt ℝ (fun t : ℝ => u ((x : ℂ) + (y : ℂ) * I + t * I)) 0) :
    HasDerivAt (fun t : ℝ => u ((x : ℂ) + (t : ℂ) * I))
      (partialY u ((x : ℂ) + (y : ℂ) * I)) y := by
  have hd : HasDerivAt (fun t : ℝ => u ((x : ℂ) + (y : ℂ) * I + t * I))
      (partialY u ((x : ℂ) + (y : ℂ) * I)) (y - y) := by
    simpa [partialY] using h.hasDerivAt
  convert hd.comp_sub_const y y using 1
  ext t
  congr 1
  push_cast
  ring

theorem realDifferentiableAt_of_continuousPartials (Ω : Set ℂ) (u : ℂ → ℝ)
    (hΩ : IsOpen Ω)
    (hx : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ))) 0)
    (hy : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ) * I)) 0)
    (cx : ContinuousOn (partialX u) Ω) (cy : ContinuousOn (partialY u) Ω)
    (a : ℂ) (ha : a ∈ Ω) : DifferentiableAt ℝ u a := by
  let e := Complex.equivRealProdCLM
  let g : ℝ → ℝ → ℝ := fun x y => u ((x : ℂ) + (y : ℂ) * I)
  let gx : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (partialX u ((x : ℂ) + (y : ℂ) * I))
  let gy : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (partialY u ((x : ℂ) + (y : ℂ) * I))
  have he : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) (e a) :=
    ((continuous_ofReal.comp continuous_fst).add
      ((continuous_ofReal.comp continuous_snd).mul continuous_const)).continuousAt
  have heq : ((e a).1 : ℂ) + ((e a).2 : ℂ) * I = a := by
    simpa only [e, Complex.equivRealProdCLM_symm_apply] using e.symm_apply_apply a
  have hmem : ∀ᶠ p : ℝ × ℝ in 𝓝 (e a), (p.1 : ℂ) + (p.2 : ℂ) * I ∈ Ω :=
    he.eventually (by simpa [heq] using hΩ.mem_nhds ha)
  have dx : ∀ᶠ p : ℝ × ℝ in 𝓝 (e a), HasFDerivAt (g · p.2) (gx p.1 p.2) p.1 := by
    filter_upwards [hmem] with p hp
    exact (sliceX_hasDerivAt u p.1 p.2 (hx _ hp)).hasFDerivAt
  have dy : ∀ᶠ p : ℝ × ℝ in 𝓝 (e a), HasFDerivAt (g p.1 ·) (gy p.1 p.2) p.2 := by
    filter_upwards [hmem] with p hp
    exact (sliceY_hasDerivAt u p.1 p.2 (hy _ hp)).hasFDerivAt
  have cpx : ContinuousAt (fun p : ℝ × ℝ => partialX u ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (e a) := by
    exact (cx.continuousAt (hΩ.mem_nhds ha)).comp_of_eq he heq
  have cpy : ContinuousAt (fun p : ℝ × ℝ => partialY u ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (e a) := by
    exact (cy.continuousAt (hΩ.mem_nhds ha)).comp_of_eq he heq
  have cgx : ContinuousAt (Function.uncurry gx) (e a) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp cpx
  have cgy : ContinuousAt (Function.uncurry gy) (e a) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp cpy
  have hd := (hasStrictFDerivAt_uncurry_coprod (f := g) (f₁ := gx) (f₂ := gy)
    (u := e a) dx dy cgx cgy).hasFDerivAt.differentiableAt
  have hc := hd.comp a e.differentiableAt
  change DifferentiableAt ℝ (fun z => u ((z.re : ℂ) + (z.im : ℂ) * I)) a at hc
  simpa only [Complex.re_add_im] using hc

theorem cauchyRiemann_of_holomorphicOn (Ω : Set ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (a : ℂ) (ha : a ∈ Ω) :
    partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a ∧
    partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a := by
  have hd := hf.2 a ha
  exact (complexDifferentiableAt_iff_CR f a (hd.restrictScalars ℝ)).mp
    ((complexDifferentiableAt_iff f a).mpr hd)

theorem holomorphicOn_iff_CR_of_continuousPartials (Ω : Set ℂ) (u v : ℂ → ℝ)
    (hΩ : IsOpen Ω)
    (hux : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ))) 0)
    (huy : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => u (a + (t : ℂ) * I)) 0)
    (hvx : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => v (a + (t : ℂ))) 0)
    (hvy : ∀ a ∈ Ω, DifferentiableAt ℝ (fun t : ℝ => v (a + (t : ℂ) * I)) 0)
    (cux : ContinuousOn (partialX u) Ω) (cuy : ContinuousOn (partialY u) Ω)
    (cvx : ContinuousOn (partialX v) Ω) (cvy : ContinuousOn (partialY v) Ω) :
    HolomorphicOn Ω (fun z => (u z : ℂ) + I * (v z : ℂ)) ↔
      ∀ a ∈ Ω, partialX u a = partialY v a ∧ partialY u a = -partialX v a := by
  let f : ℂ → ℂ := fun z => (u z : ℂ) + I * (v z : ℂ)
  have hre : (fun z => (f z).re) = u := by ext z; simp [f]
  have him : (fun z => (f z).im) = v := by ext z; simp [f]
  constructor
  · intro hf a ha
    simpa only [hre, him] using cauchyRiemann_of_holomorphicOn Ω f hf a ha
  · intro hCR
    refine ⟨hΩ, fun a ha => ?_⟩
    have hu := realDifferentiableAt_of_continuousPartials Ω u hΩ hux huy cux cuy a ha
    have hv := realDifferentiableAt_of_continuousPartials Ω v hΩ hvx hvy cvx cvy a ha
    have huf := ofRealCLM.differentiableAt.comp a hu
    have hvf := ofRealCLM.differentiableAt.comp a hv
    have hreal : DifferentiableAt ℝ f a := huf.add (hvf.const_mul I)
    apply (complexDifferentiableAt_iff f a).mp
    apply (complexDifferentiableAt_iff_CR f a hreal).mpr
    simpa only [hre, him] using hCR a ha

end D12Complex
