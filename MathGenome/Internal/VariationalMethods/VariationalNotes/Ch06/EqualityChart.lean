import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.EqualityChart
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Differential.ImplicitFunction
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace VariationalNotes.Ch06.EqualityChart

/-! Local equality chart, `paper.tex`, Lemma 6.2 (lines 2721–2750),
and the finite-target right inverse in the following paragraph (lines 2767–2776).
The library implicit theorem supplies one exact open product chart, with the
same chart retaining every available order of differentiability. -/

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The projection onto the kernel along the specified right inverse. -/
def kernelProjection (B : X →L[ℝ] Y) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) : X →L[ℝ] B.ker :=
  (ContinuousLinearMap.id ℝ X - R.comp B).codRestrict B.ker (by
    intro x
    change B (x - R (B x)) = 0
    have h (y : Y) : B (R y) = y := congrArg (fun f : Y →L[ℝ] Y => f y) hBR
    simp [h])

@[simp] lemma kernelProjection_apply (B : X →L[ℝ] Y) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) (x : X) :
    (kernelProjection B R hBR x : X) = x - R (B x) := rfl

/-- Explicit topological splitting; no completeness assumption is needed. -/
def splittingEquiv (B : X →L[ℝ] Y) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) : (B.ker × Y) ≃L[ℝ] X where
  toFun p := (p.1 : X) + R p.2
  invFun x := (kernelProjection B R hBR x, B x)
  map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' := by intros; simp
  left_inv := by
    intro ⟨k, y⟩
    have h (z : Y) : B (R z) = z := congrArg (fun f : Y →L[ℝ] Y => f z) hBR
    apply Prod.ext
    · apply Subtype.ext
      simp [h]
    · simp [h]
  right_inv := by intro x; simp
  continuous_toFun := (B.ker.subtypeL.continuous.comp continuous_fst).add
    (R.continuous.comp continuous_snd)
  continuous_invFun := (kernelProjection B R hBR).continuous.prodMk B.continuous

theorem splitting : Specs.SplittingType := by
  intro X Y _ _ _ _ B R hBR
  have h (y : Y) : B (R y) = y := congrArg (fun f : Y →L[ℝ] Y => f y) hBR
  refine ⟨?_, ?_, splittingEquiv B R hBR, fun _ => rfl⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hxR
      obtain ⟨y, rfl⟩ := hxR
      have : y = 0 := by simpa [h] using hx
      simp [this]
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro x
      exact ⟨x - R (B x), R (B x), (by simp [h]), ⟨B x, rfl⟩, sub_add_cancel x _⟩
  · have : (R.range : Set X) = {x | R (B x) - x = 0} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩; simp [h]
      · intro hx
        exact ⟨B x, sub_eq_zero.mp hx⟩
    rw [this]
    exact isClosed_eq (R.continuous.comp B.continuous |>.sub continuous_id) continuous_const

theorem finiteTargetRightInverse : Specs.FiniteTargetRightInverseType := by
  intro X Y _ _ _ _ _ B hB
  exact B.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hB)

variable [CompleteSpace X] [CompleteSpace Y]

/-- Apply the Banach implicit theorem in the explicit right-inverse coordinates. -/
theorem localEqualityGraph (r : ℕ∞ω) (hr : 1 ≤ r) (U : Set X) (hU : IsOpen U)
    (h : X → Y) (hh : ContDiffOn ℝ r h U) (a : X) (ha : a ∈ U) (hzero : h a = 0)
    (B : X →L[ℝ] Y) (hB : HasFDerivAt h B a) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) :
    Specs.LocalEqualityGraph B R r U h a := by
  let A : B.ker × Y →L[ℝ] X := B.ker.subtypeL.coprod R
  let H : B.ker × Y → Y := fun p => h (a + A p)
  let Ω : Set (B.ker × Y) := (fun p => a + A p) ⁻¹' U
  have hΩ : IsOpen Ω := hU.preimage (continuous_const.add A.continuous)
  have hH : ContDiffOn ℝ r H Ω :=
    hh.comp (contDiff_const.add A.contDiff).contDiffOn (fun _ hp => hp)
  have hp : (0 : B.ker × Y) ∈ Ω := by simpa [Ω] using ha
  have hHzero : H (0 : B.ker × Y) = 0 := by simpa [H] using hzero
  have hd : HasFDerivAt H (B.comp A) (0 : B.ker × Y) := by
    have hB' : HasFDerivAt h B (a + A 0) := by simpa using hB
    exact hB'.comp 0 (A.hasFDerivAt.const_add a)
  have hpart : (fderiv ℝ H (0 : B.ker × Y)).comp (ContinuousLinearMap.inr ℝ B.ker Y) =
      (ContinuousLinearEquiv.refl ℝ Y : Y →L[ℝ] Y) := by
    rw [hd.fderiv]
    ext y
    simpa [A] using congrArg (fun f : Y →L[ℝ] Y => f y) hBR
  have hker : (fderiv ℝ H (0 : B.ker × Y)).comp (ContinuousLinearMap.inl ℝ B.ker Y) = 0 := by
    rw [hd.fderiv]
    ext k
    simp [A]
  obtain ⟨V, W, η, hV, hW, h0V, h0W, hprod, hη0, hηW, _, hgraph,
      hderiv, _, _, hregular⟩ :=
    ExpandedFA.Differential.ImplicitFunction.implicit_function ℝ B.ker Y Y Ω hΩ H
      (hH.of_le hr) 0 0 hp hHzero (ContinuousLinearEquiv.refl ℝ Y) hpart
  have hηd : HasFDerivAt η (0 : B.ker →L[ℝ] Y) 0 := by
    have hdη := (hderiv 0 h0V).2.1
    convert hdη using 1
    rw [hη0]
    change (0 : B.ker →L[ℝ] Y) =
      (-((fderiv ℝ H 0).comp (ContinuousLinearMap.inr ℝ B.ker Y)).inverse).comp
        ((fderiv ℝ H 0).comp (ContinuousLinearMap.inl ℝ B.ker Y))
    rw [hker, ContinuousLinearMap.comp_zero]
  refine ⟨V, W, η, hV, hW, h0V, h0W, ?_, hη0, hηW, hregular r hH,
    hηd, R.contDiff.comp_contDiffOn (hregular r hH), ?_, ?_⟩
  · intro k hk y hy
    simpa [Ω, A, add_assoc] using hprod (show (k, y) ∈ V ×ˢ W from ⟨hk, hy⟩)
  · convert R.hasFDerivAt.comp 0 hηd using 1
    all_goals first | rfl | simp
  · intro k hk y hy
    simpa [H, A, add_assoc] using hgraph k hk y hy

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Transport the open product cylinder through the splitting and the translation. -/
theorem ambientEqualityGraph_of_graph (B : X →L[ℝ] Y) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) (r : ℕ∞ω)
    (U : Set X) (h : X → Y) (a : X)
    (hg : Specs.LocalEqualityGraph B R r U h a) :
    Specs.AmbientEqualityGraph B R r U h a := by
  obtain ⟨V, W, η, hV, hW, h0V, h0W, hprod, hη0, hηW, _, _, hψC, hψd, hgraph⟩ := hg
  let T : (B.ker × Y) ≃ₜ X :=
    (splittingEquiv B R hBR).toHomeomorph.trans (Homeomorph.addLeft a)
  have hT (p : B.ker × Y) : T p = a + (p.1 : X) + R p.2 := by
    change a + ((p.1 : X) + R p.2) = _
    rw [add_assoc]
  let N : Set X := T '' (V ×ˢ W)
  have hN : IsOpen N := T.isOpen_image.mpr (hV.prod hW)
  have haN : a ∈ N := by
    refine ⟨(0, 0), ⟨h0V, h0W⟩, ?_⟩
    simp [hT]
  have hNU : N ⊆ U := by
    rintro x ⟨⟨k, y⟩, ⟨hk, hy⟩, rfl⟩
    rw [hT]
    exact hprod k hk y hy
  refine ⟨V, N, (fun k => R (η k)), hV, h0V, hN, haN, hNU, hψC,
    ?_, hψd, ?_, ?_⟩
  · simp [hη0]
  · intro k hk
    refine ⟨⟨η k, rfl⟩, ?_, (hgraph k hk (η k) (hηW hk)).mpr rfl⟩
    exact ⟨(k, η k), ⟨hk, hηW hk⟩, hT _⟩
  · rintro x ⟨⟨k, y⟩, ⟨hk, hy⟩, rfl⟩
    rw [hT]
    constructor
    · intro hx
      have hyη := (hgraph k hk y hy).mp hx
      exact ⟨k, hk, by rw [hyη]⟩
    · rintro ⟨k', hk', heq⟩
      rw [heq]
      exact (hgraph k' hk' (η k') (hηW hk')).mpr rfl

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Restrict the graph to a kernel line on an open interval about zero. -/
theorem feasibleCurves_of_graph (B : X →L[ℝ] Y) (R : Y →L[ℝ] X) (r : ℕ∞ω)
    (U : Set X) (h : X → Y) (a : X)
    (hg : Specs.LocalEqualityGraph B R r U h a) : Specs.FeasibleCurves B r U h a := by
  obtain ⟨V, W, η, hV, hW, h0V, h0W, hprod, hη0, hηW, hηC, hηd, hψC, hψd, hgraph⟩ := hg
  intro d
  let l : ℝ →L[ℝ] B.ker := (ContinuousLinearMap.id ℝ ℝ).smulRight d
  let γ : ℝ → X := fun t => a + (l t : X) + R (η (l t))
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), l t ∈ V := by
    apply l.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hV.mem_nhds h0V
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hlV : MapsTo l (Ioo (-ε) ε) V := by
    intro t ht
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht
  have hlD : HasDerivAt (fun t => l t) d 0 := by
    simpa [l] using (hasDerivAt_id (0 : ℝ)).smul_const d
  have hlineD : HasDerivAt (fun t => (l t : X)) (d : X) 0 :=
    B.ker.subtypeL.hasFDerivAt.comp_hasDerivAt 0 hlD
  have hcorrD : HasDerivAt (fun t => R (η (l t))) 0 0 := by
    have hψd' : HasFDerivAt (fun k => R (η k)) (0 : B.ker →L[ℝ] X) (l 0) := by
      simpa only [map_zero] using hψd
    convert hψd'.comp_hasDerivAt 0 hlD using 1
    rfl
  refine ⟨ε, γ, hε, ?_, ?_, ?_, ?_⟩
  · simp [γ, hη0]
  · exact (contDiffOn_const.add
      (B.ker.subtypeL.contDiff.comp l.contDiff).contDiffOn).add
        (hψC.comp l.contDiff.contDiffOn hlV)
  · convert (hlineD.const_add a).add hcorrD using 1
    simp
  · intro t ht
    exact ⟨hprod (l t) (hlV ht) (η (l t)) (hηW (hlV ht)),
      (hgraph (l t) (hlV ht) (η (l t)) (hηW (hlV ht))).mpr rfl⟩

/-- Lemma 6.2, including exactness, zero correction derivative and two-sided curves. -/
theorem localEqualityChart : Specs.LocalEqualityChartType := by
  intro X Y _ _ _ _ _ _ r hr U hU h hh a ha hzero B hB R hBR
  have hg := localEqualityGraph r hr U hU h hh a ha hzero B hB R hBR
  exact ⟨hg, ambientEqualityGraph_of_graph B R hBR r U h a hg,
    feasibleCurves_of_graph B R r U h a hg⟩

/-- The domain can remain infinite-dimensional when the target is finite-dimensional. -/
theorem finiteTargetEqualityChart : Specs.FiniteTargetEqualityChartType := by
  intro X Y _ _ _ _ _ _ _ r hr U hU h hh a ha hzero B hB hsurj
  obtain ⟨R, hR⟩ := finiteTargetRightInverse X Y B hsurj
  exact ⟨R, hR, localEqualityChart X Y r hr U hU h hh a ha hzero B hB R hR⟩

end VariationalNotes.Ch06.EqualityChart
