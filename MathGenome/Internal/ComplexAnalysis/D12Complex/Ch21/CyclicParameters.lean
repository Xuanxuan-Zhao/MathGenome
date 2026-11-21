import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.CyclicParameters
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AlgebraicCovering
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.PunctureCompletion
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-! Local cyclic parameters for algebraic branches (D12.21.04).
The parameter lives on a punctured disk. Its root coordinate is obtained
from actual local holomorphic branches, without an extension at zero.
-/
noncomputable section
open Set Filter Topology
open D12Complex D12Complex.Surfaces D12Complex.AlgebraicCovering
open D12Complex.Ch20 D12Complex.Ch20.PuncturedDiskLoops
open D12Complex.Ch20.PunctureCompletion

namespace D12Complex.Surfaces

universe u

lemma coordinate_charts_compatible {E : Type u} [TopologicalSpace E]
    (q : E → ℂ) (e f : ComplexChart E)
    (he : ∀ x ∈ e.val.source, e.val x = q x)
    (hf : ∀ x ∈ f.val.source, f.val x = q x) :
    CompatibleCharts e f := by
  have hid (e f : ComplexChart E)
      (he : ∀ x ∈ e.val.source, e.val x = q x)
      (hf : ∀ x ∈ f.val.source, f.val x = q x) :
      ∀ z ∈ (e.val.symm.trans f.val).source, (e.val.symm.trans f.val) z = z := by
    intro z hz
    change f.val (e.val.symm z) = z
    calc
      _ = q (e.val.symm z) := hf _ hz.2
      _ = e.val (e.val.symm z) := (he _ (e.val.map_target hz.1)).symm
      _ = z := e.val.right_inv hz.1
  let t := e.val.symm.trans f.val
  refine ⟨⟨t.open_source,?_⟩,⟨t.open_target,?_⟩,t.mapsTo,t.symm.mapsTo,t.leftInvOn,t.rightInvOn⟩
  · intro z hz
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [t.open_source.mem_nhds hz] with y hy
    exact hid e f he hf y hy
  · intro z hz
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [t.open_target.mem_nhds hz] with y hy
    exact hid f e hf he y hy

lemma localHomeomorph_complex_atlas {E : Type u} [TopologicalSpace E]
    (q : E → ℂ) (hq : IsLocalHomeomorph q) :
    ∃ A : Set (ComplexChart E), IsAtlas A ∧
      ∀ e ∈ A, (∀ x ∈ e.val.source, e.val x = q x) ∧
        ∃ z : ℂ, ∃ r : ℝ, 0 < r ∧ e.val.target = Metric.ball z r := by
  classical
  let A : Set (ComplexChart E) := {e | (∀ x ∈ e.val.source, e.val x = q x) ∧
    ∃ z : ℂ, ∃ r : ℝ, 0 < r ∧ e.val.target = Metric.ball z r}
  refine ⟨A,⟨?_,?_⟩,fun e he => he⟩
  · intro x
    obtain ⟨h, hx, hq'⟩ := hq x
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp h.open_target (h x) (h.map_source hx)
    let e := h.trans (OpenPartialHomeomorph.ofSet (Metric.ball (h x) r) Metric.isOpen_ball)
    have het : e.target = Metric.ball (h x) r := by
      change Metric.ball (h x) r ∩ h.target = Metric.ball (h x) r
      exact inter_eq_left.mpr hb
    have hed : IsDomain e.target := by
      rw [het]
      exact ⟨⟨h x, Metric.mem_ball_self hr⟩, Metric.isOpen_ball, Metric.isPreconnected_ball⟩
    let c : ComplexChart E := ⟨e, hed⟩
    refine ⟨c,⟨?_, h x, r, hr, het⟩,?_⟩
    · intro y hy
      change h y = q y
      exact congrFun hq' y |>.symm
    · change x ∈ h.source ∩ h ⁻¹' Metric.ball (h x) r
      exact ⟨hx, Metric.mem_ball_self hr⟩
  · intro e he f hf
    exact coordinate_charts_compatible q e f he.1 hf.1

end D12Complex.Surfaces

namespace D12Complex.CyclicParameters.Pullbacks
universe u v w
variable {E : Type u} {B : Type v} {A : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]

abbrev Pullback (p : E → B) (g : A → B) := {x : A × E // g x.1 = p x.2}
def pullbackProjection (p : E → B) (g : A → B) (x : Pullback p g) : A := x.val.1

def pullbackSheetHomeomorph (p : E → B) (g : A → B) (hg : Continuous g)
    (U : Set B) (V : Set E) (h : V ≃ₜ U) (hh : ∀ x : V, (h x : B) = p x) :
    {x : Pullback p g // x.val.2 ∈ V} ≃ₜ (g ⁻¹' U) where
  toFun x := ⟨x.val.val.1, by
    have hx := (h ⟨x.val.val.2, x.property⟩).property
    rw [hh] at hx
    simpa only [mem_preimage, x.val.property] using hx⟩
  invFun a := ⟨⟨(a.val, (h.symm ⟨g a.val, a.property⟩).val), by
    rw [← hh]
    exact (congrArg Subtype.val (h.apply_symm_apply ⟨g a.val, a.property⟩)).symm⟩, (h.symm ⟨g a.val, a.property⟩).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    have hxU : g x.val.val.1 ∈ U := by
      rw [x.val.property, ← hh ⟨x.val.val.2, x.property⟩]
      exact (h ⟨x.val.val.2, x.property⟩).property
    have hbase : (⟨g x.val.val.1, hxU⟩ : U) = h ⟨x.val.val.2,x.property⟩ := by
      apply Subtype.ext
      exact x.val.property.trans (hh ⟨x.val.val.2,x.property⟩).symm
    change (h.symm _).val = x.val.val.2
    rw [hbase, h.symm_apply_apply]
  right_inv a := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).fst
  continuous_invFun := by
    have hc : Continuous (fun a : g ⁻¹' U => h.symm ⟨g a.val, a.property⟩) :=
      h.symm.continuous.comp ((hg.comp continuous_subtype_val).subtype_mk _)
    exact ((continuous_subtype_val.prodMk (continuous_subtype_val.comp hc)).subtype_mk _).subtype_mk _

lemma isCovering_pullback {p : E → B} (hp : D12Complex.Ch20.IsCovering p)
    (g : A → B) (hg : Continuous g) :
    D12Complex.Ch20.IsCovering (pullbackProjection p g) := by
  intro a
  obtain ⟨U,ha,hU, sheets, hopen,hdisj,hunion,hhomeo⟩ := hp (g a)
  refine ⟨g ⁻¹' U,ha,hU.preimage hg,
    Set.range (fun V : sheets => {x : Pullback p g | x.val.2 ∈ V.val}), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨V,rfl⟩
    exact (hopen V.val V.property).preimage continuous_subtype_val.snd
  · rintro _ ⟨V,rfl⟩ _ ⟨W,rfl⟩ hneq
    have hvw : V.val ≠ W.val := by
      intro heq
      apply hneq
      exact congrArg (fun Z : Set E => {x : Pullback p g | x.val.2 ∈ Z}) heq
    exact Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp (hdisj V.property W.property hvw) hx hy)
  · ext x
    constructor
    · rintro ⟨_,⟨V,rfl⟩,hx⟩
      change g x.val.1 ∈ U
      rw [x.property]
      have : x.val.2 ∈ ⋃₀ sheets := ⟨V.val,V.property,hx⟩
      simpa only [hunion, mem_preimage] using this
    · intro hx
      have hpx : x.val.2 ∈ ⋃₀ sheets := by
        rw [hunion]
        change p x.val.2 ∈ U
        rwa [← x.property]
      obtain ⟨V,hV,hxV⟩ := hpx
      exact ⟨_,⟨⟨V,hV⟩,rfl⟩,hxV⟩
  · rintro _ ⟨V,rfl⟩
    obtain ⟨h,hh⟩ := hhomeo V.val V.property
    exact ⟨pullbackSheetHomeomorph p g hg U V.val h hh,fun _ => rfl⟩
end D12Complex.CyclicParameters.Pullbacks

namespace D12Complex.CyclicParameters

def curvePoint {P : Polynomial (Polynomial ℂ)} {g : ℂ → ℂ} {r : ℝ}
    (x : CurveOver P g r) : Curve P := x.val.2
def baseLift (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hadm : ∀ t : Disk r, g t ∈ baseSet P) (t : Disk r) : Base P := ⟨g t,hadm t⟩

def curveOverHomeomorph (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hadm : ∀ t : Disk r, g t ∈ baseSet P) :
    CurveOver P g r ≃ₜ Pullbacks.Pullback (projection P) (baseLift P g r hadm) where
  toFun x := ⟨x.val,Subtype.ext x.property⟩
  invFun x := ⟨x.val, congrArg Subtype.val x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

lemma curveOver_covering (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (g : ℂ → ℂ) (r : ℝ) (hadm : ∀ t : Disk r, g t ∈ baseSet P)
    (hg : Continuous (fun t : Disk r => g t)) :
    IsCoveringMap (diskProjection P g r) := by
  have hc := Pullbacks.isCovering_pullback (covering P d hP hdeg hd).1
    (baseLift P g r hadm) (hg.subtype_mk _)
  have hm := D12Complex.Ch20.CoveringPaths.covering_bridge _ hc
  exact hm.comp_homeomorph (curveOverHomeomorph P g r hadm)

lemma root_differentiable_of_first_coordinate
    (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (F : ℂ → Curve P) (g : ℂ → ℂ) (z : ℂ)
    (hF : ContinuousAt F z) (hg : DifferentiableAt ℂ g z)
    (hfirst : (fun y => (F y).val.1) =ᶠ[𝓝 z] g) :
    DifferentiableAt ℂ (fun y => (F y).val.2) z := by
  classical
  let L := Classical.choice (local_branches P d hP hdeg hd (F z).val.1 (F z).property.1)
  have hz : (F z).val.1 ∈ Metric.ball (F z).val.1 L.radius :=
    Metric.mem_ball_self L.radius_pos
  obtain ⟨i,hi⟩ := (L.exhaustive _ hz (F z).val.2).mp (F z).property.2
  have hV : (F z).val.2 ∈ L.V i := hi ▸ L.center_mem i
  have hFroot : ContinuousAt (fun y => (F y).val.2) z :=
    continuous_subtype_val.snd.continuousAt.comp hF
  have hFbase : ContinuousAt (fun y => (F y).val.1) z :=
    continuous_subtype_val.fst.continuousAt.comp hF
  have hball : ∀ᶠ y in 𝓝 z, (F y).val.1 ∈ Metric.ball (F z).val.1 L.radius :=
    hFbase.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hz)
  have hvals : ∀ᶠ y in 𝓝 z, (F y).val.2 ∈ L.V i :=
    hFroot.preimage_mem_nhds ((L.open_V i).mem_nhds hV)
  have hcenter : (F z).val.1 = g z := hfirst.eq_of_nhds
  apply ((L.holomorphic i).2 _ (hcenter ▸ hz)).comp z hg |>.congr_of_eventuallyEq
  filter_upwards [hfirst,hball,hvals] with y hy hyball hyvals
  exact ((L.unique _ hyball i _ hyvals).mp (F y).property.2).trans (congrArg (L.branch i) hy)

lemma rootCoordinate_chart_holomorphic
    (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (g : ℂ → ℂ) (r : ℝ) (hg : HolomorphicOn {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} g)
    (e : Surfaces.ComplexChart (CurveOver P g r))
    (he : ∀ x ∈ e.val.source, e.val x = (diskProjection P g r x : ℂ)) :
    HolomorphicOn e.val.target (rootCoordinate P g r ∘ e.val.symm) := by
  refine ⟨e.val.open_target,?_⟩
  intro z hz
  have hF : ContinuousAt (fun y => curvePoint (e.val.symm y)) z :=
    (continuous_subtype_val.snd).continuousAt.comp
      ((e.val.symm.continuousOn _ hz).continuousAt (e.val.open_target.mem_nhds hz))
  have hbase : ∀ y ∈ e.val.target, (diskProjection P g r (e.val.symm y) : ℂ) = y := by
    intro y hy
    rw [← he _ (e.val.map_target hy), e.val.right_inv hy]
  have hzDisk : 0 < ‖z‖ ∧ ‖z‖ < r := (hbase z hz) ▸ (diskProjection P g r (e.val.symm z)).property
  have hfirst : (fun y => (curvePoint (e.val.symm y)).val.1) =ᶠ[𝓝 z] g := by
    filter_upwards [e.val.open_target.mem_nhds hz] with y hy
    change (e.val.symm y).val.2.val.1 = g y
    exact (e.val.symm y).property.symm.trans (congrArg g (hbase y hy))
  exact root_differentiable_of_first_coordinate P d hP hdeg hd
    (fun y => curvePoint (e.val.symm y)) g z hF (hg.2 z hzDisk) hfirst
def curveOverFiberEquiv (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hadm : ∀ t : Disk r, g t ∈ baseSet P) (b : Disk r) :
    (diskProjection P g r ⁻¹' {b}) ≃
      (projection P ⁻¹' {baseLift P g r hadm b}) where
  toFun x := ⟨x.val.val.2, by
    apply Subtype.ext
    have hb : x.val.val.1 = b := x.property
    exact x.val.property.symm.trans (congrArg (fun t : Disk r => g t) hb)⟩
  invFun x := ⟨⟨(b,x.val), (congrArg Subtype.val x.property).symm⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (show b = x.val.val.1 from x.property.symm) rfl
  right_inv _ := rfl

lemma curveOver_finite_fibers
    (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (g : ℂ → ℂ) (r : ℝ) (hadm : ∀ t : Disk r, g t ∈ baseSet P) (b : Disk r) :
    Finite (diskProjection P g r ⁻¹' {b}) := by
  obtain ⟨e⟩ := fiber_cardinality P d hP hdeg hd (baseLift P g r hadm b)
  exact Finite.of_equiv (Fin d) ((curveOverFiberEquiv P g r hadm b).trans e).symm

lemma curveOver_root_germs
    (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (g : ℂ → ℂ) (r : ℝ) (hadm : ∀ t : Disk r, g t ∈ baseSet P) (b : Disk r) :
    ∃ e : RootGerm P (g b) ≃ (diskProjection P g r ⁻¹' {b}),
      ∀ a, rootCoordinate P g r (e a) = a.val.value := by
  obtain ⟨e,he⟩ := root_germs P d hP hdeg hd (baseLift P g r hadm b)
  exact ⟨e.trans (curveOverFiberEquiv P g r hadm b).symm,he⟩


lemma componentSurface_coordinates {r : ℝ}
    {E : Type*} [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    [LocallyConnectedSpace E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A) (p : E → Disk r)
    (hcoords : ∀ e ∈ A, ∀ x ∈ e.val.source, e.val x = (p x : ℂ))
    (j : ConnectedComponents E) :
    ∀ e ∈ (componentSurface A hA j).atlas,
      ∀ x ∈ e.val.source, e.val x = (p x : ℂ) := by
  rintro d ⟨e, he, hec, rfl⟩ x hx
  rw [componentChart_source] at hx
  exact hcoords e he x.val hx

theorem component_parameters {r : ℝ} (hr : 0 < r)
    {E : Type*} [TopologicalSpace E] [T2Space E] [SecondCountableTopology E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A)
    (p : E → Disk r)
    (hcoords : ∀ e ∈ A, ∀ x ∈ e.val.source, e.val x = (p x : ℂ))
    (cov : IsCoveringMap p)
    (hfin : ∀ b, Finite (p ⁻¹' {b}))
    (hp : Continuous (fun x => (p x : ℂ)) ∧
      ∀ e ∈ A, HolomorphicOn e.val.target (fun z => (p (e.val.symm z) : ℂ)))
    (w : E → ℂ)
    (hw : Continuous w ∧ ∀ e ∈ A, HolomorphicOn e.val.target (w ∘ e.val.symm))
    (b : Disk r) (γ : Path b b) (hγ : HasWinding γ 1) :
    let := atlas_locallyPathConnected A hA
    let n : ConnectedComponents E → ℕ := fun j =>
      Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}
    Finite (ConnectedComponents E) ∧
    (∀ x y : p ⁻¹' {b},
      ConnectedComponents.mk (x : E) = ConnectedComponents.mk (y : E) ↔
        ∃ k : ℤ, (cov.monodromyPerm b
          (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) ^ k) x = y) ∧
    (∀ j, 0 < n j) ∧
    ∀ j, ∃ (hn : 0 < n j)
      (S : RiemannSurface (componentSet j))
      (T : RiemannSurface (Disk (rootRadius r (n j))))
      (Φ : Disk (rootRadius r (n j)) ≃ₜ componentSet j)
      (c : ComplexChart (componentSet j)) (W : ℂ → ℂ),
      (∀ e ∈ S.atlas, ∀ x ∈ e.val.source, e.val x = (p x : ℂ)) ∧
      ScalarHolomorphic S (fun x => w x) ∧
      (∀ e ∈ T.atlas, ∀ t ∈ e.val.source, e.val t = (t : ℂ)) ∧
      HolomorphicMap T S Φ ∧ HolomorphicMap S T Φ.symm ∧
      ScalarHolomorphic S (fun x => (Φ.symm x : ℂ)) ∧
      c ∈ maximalAtlas S.atlas ∧ c.val.source = univ ∧
      c.val.target = {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < rootRadius r (n j)} ∧
      HolomorphicOn {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < rootRadius r (n j)} W ∧
      ∀ t, p (Φ t) = powerMap hr hn t ∧
        c.val (Φ t) = (t : ℂ) ∧ W t = w (Φ t) := by
  let := atlas_locallyPathConnected A hA
  let n : ConnectedComponents E → ℕ := fun j =>
    Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}
  obtain ⟨hf, ho, hn⟩ := monodromy_components hr A hA cov b γ hγ (hfin b)
  refine ⟨hf, ho, hn, ?_⟩
  intro j
  let S := componentSurface A hA j
  let pj : componentSet j → Disk r := fun x => p x
  have hpj : ScalarHolomorphic S (fun x => (pj x : ℂ)) :=
    component_scalarHolomorphic A hA hp j
  have hwj : ScalarHolomorphic S (fun x => w x) :=
    component_scalarHolomorphic A hA hw j
  have hcovj : IsCovering pj := ModelCoverings.covering_of_isCoveringMap _
    (covering_restrict_clopen cov hfin (componentSet_clopen j))
  obtain ⟨T, Φ, hT, hΦ, hΦi, hcomm⟩ := connected_classification hr S pj hcovj hpj
    (hn j) (fun z => component_cover_card hr cov j b z)
  have hinv := inverse_parameter_holomorphic hr S pj hpj (hn j) Φ hcomm
  let hD := disk_isDomain (rootRadius_pos hr (n j))
  let c := parameterChart hD Φ
  have hc : c ∈ maximalAtlas S.atlas := parameterChart_mem_maximalAtlas S hD Φ hinv
  let W : ℂ → ℂ := (fun x : componentSet j => w x) ∘ c.val.symm
  have hW : HolomorphicOn {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < rootRadius r (n j)} W := by
    have h := scalarHolomorphic_chart_independent S (fun x : componentSet j => w x) hwj c hc
    simpa only [c, parameterChart_target] using h
  refine ⟨hn j, S, T, Φ, c, W,
    componentSurface_coordinates A hA p hcoords j, hwj, hT, hΦ, hΦi, hinv, hc,
    parameterChart_source hD Φ, parameterChart_target hD Φ, hW, ?_⟩
  intro t
  have hct : c.val (Φ t) = (t : ℂ) := by
    simp [c, parameterChart_apply]
  refine ⟨congrFun hcomm t, hct, ?_⟩
  change w (c.val.symm (t : ℂ)) = w (Φ t)
  rw [← hct, c.val.left_inv (by rw [parameterChart_source]; trivial)]


def finiteRestrictionHomeomorph (P : Polynomial (Polynomial ℂ)) (c : ℂ) (r : ℝ) :
    CurveOver P (fun u => c + u) r ≃ₜ FiniteRestriction P c r where
  toFun x := ⟨x.val.2, by
    rw [← x.property]
    simpa using x.val.1.property⟩
  invFun x := ⟨(⟨x.val.val.1 - c, x.property⟩, x.val), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change x.val.2.val.1 - c = (x.val.1 : ℂ)
      rw [← x.property]
      simp
    · rfl
  right_inv x := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).sub continuous_const
    · exact continuous_subtype_val

def infinityRestrictionHomeomorph (P : Polynomial (Polynomial ℂ)) (r : ℝ) :
    CurveOver P (fun u => u⁻¹) r ≃ₜ InfinityRestriction P r where
  toFun x := ⟨x.val.2, by
    rw [← x.property]
    simpa using x.val.1.property⟩
  invFun x := ⟨(⟨x.val.val.1⁻¹, x.property⟩, x.val), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change x.val.2.val.1⁻¹ = (x.val.1 : ℂ)
      rw [← x.property]
      simp
    · rfl
  right_inv x := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply Continuous.inv₀
      · exact (continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val
      · intro x hx
        exact (norm_pos_iff.mp x.property.1) (by rw [hx, inv_zero])
    · exact continuous_subtype_val


lemma finite_set_punctured_radius (E : Set ℂ) (hE : E.Finite) (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z - c‖ → ‖z - c‖ < r → z ∉ E := by
  have hc : c ∈ (E \ {c})ᶜ := by simp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hE.sdiff (t := {c})).isClosed.isOpen_compl c hc
  refine ⟨r, hr, ?_⟩
  intro z hz0 hzr hzE
  have hzc : z ≠ c := fun he => by simp [he] at hz0
  have hmem := hball (show z ∈ Metric.ball c r by simpa [Metric.mem_ball, dist_eq_norm] using hzr)
  exact hmem ⟨hzE, by simpa only [mem_singleton_iff] using hzc⟩

lemma finite_set_infinity_radius (E : Set ℂ) (hE : E.Finite) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r → z⁻¹ ∉ E := by
  obtain ⟨r, hr, hav⟩ := finite_set_punctured_radius ((fun z : ℂ => z⁻¹) '' E) (hE.image _) 0
  refine ⟨r, hr, ?_⟩
  intro z hz0 hzr hzE
  have hznot := hav z (by simpa using hz0) (by simpa using hzr)
  apply hznot
  exact ⟨z⁻¹, hzE, inv_inv z⟩


lemma orbit_fiber_full_cycle {F J : Type*} [Finite F]
    (τ : Equiv.Perm F) (component : F → J)
    (hinv : ∀ x, component (τ x) = component x)
    (horbit : ∀ x y, component x = component y ↔ ∃ k : ℤ, (τ ^ k) x = y)
    (j : J) :
    ∃ σ : Equiv.Perm {x : F // component x = j},
      (∀ x, (σ x).val = τ x) ∧
      σ ^ Nat.card {x : F // component x = j} = 1 ∧
      ∀ x, Function.Bijective
        (fun i : Fin (Nat.card {x : F // component x = j}) => (σ ^ i.val) x) := by
  classical
  let C := {x : F // component x = j}
  let := Fintype.ofFinite C
  let h : ∀ x, component (τ x) = j ↔ component x = j := fun x => by rw [hinv x]
  let σ : Equiv.Perm C := τ.subtypePerm h
  have ht : ∀ x y : C, ∃ k : ℤ, (σ ^ k) x = y := by
    intro x y
    obtain ⟨k, hk⟩ := (horbit x.val y.val).mp (x.property.trans y.property.symm)
    refine ⟨k, Subtype.ext ?_⟩
    change ((τ.subtypePerm h ^ k) x).val = y.val
    rw [Equiv.Perm.subtypePerm_zpow]
    exact hk
  obtain ⟨heq, hb⟩ := full_cycle_of_transitive σ ht
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro x
    rfl
  · simpa only [Nat.card_eq_fintype_card] using heq
  · change ∀ x : C, Function.Bijective (fun i : Fin (Nat.card C) => (σ ^ i.val) x)
    rw [Nat.card_eq_fintype_card]
    exact hb


/-- Apply the punctured-disk classification to the actual pulled-back curve. -/
theorem cyclic_parameters :
    Specs.D12Complex.Ch21.CyclicParameters.cyclic_parameters_type := by
  intro P d hP hdeg hd g r hr hg hadm
  classical
  have hgcont : Continuous (fun u : Disk r => g (u : ℂ)) := by
    apply continuousOn_iff_continuous_domRestrict.mp
    exact fun z hz => (hg.2 z hz).continuousAt.continuousWithinAt
  let p := diskProjection P g r
  let w := rootCoordinate P g r
  let cov : IsCoveringMap p := curveOver_covering P d hP hdeg hd g r hadm hgcont
  have hfin : ∀ b, Finite (p ⁻¹' {b}) := curveOver_finite_fibers P d hP hdeg hd g r hadm
  have hopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := hg.1
  have hq : IsLocalHomeomorph (fun x : CurveOver P g r => (p x : ℂ)) :=
    hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp cov.isLocalHomeomorph
  obtain ⟨A,hA,hcoords⟩ := localHomeomorph_complex_atlas _ hq
  have hcoord : ∀ e ∈ A, ∀ x ∈ e.val.source, e.val x = (p x : ℂ) :=
    fun e he => (hcoords e he).1
  have hp : Continuous (fun x => (p x : ℂ)) ∧
      ∀ e ∈ A, HolomorphicOn e.val.target (fun z => (p (e.val.symm z) : ℂ)) := by
    refine ⟨continuous_subtype_val.comp cov.continuous, ?_⟩
    intro e he
    refine ⟨e.val.open_target, fun z hz => ?_⟩
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [e.val.open_target.mem_nhds hz] with y hy
    exact (hcoord e he _ (e.val.map_target hy)).symm.trans (e.val.right_inv hy)
  have hw : Continuous w ∧ ∀ e ∈ A, HolomorphicOn e.val.target (w ∘ e.val.symm) := by
    refine ⟨?_, fun e he => rootCoordinate_chart_holomorphic P d hP hdeg hd g r hg e (hcoord e he)⟩
    exact (continuous_subtype_val.comp continuous_subtype_val.snd).snd
  have hnDisk : Nonempty (Disk r) := (disk_isDomain hr).1.to_subtype
  let b₀ : Disk r := Classical.choice hnDisk
  refine ⟨cov, finite_components hr cov b₀ (hfin b₀),
    curveOver_root_germs P d hP hdeg hd g r hadm, ?_⟩
  intro b γ hγ
  obtain ⟨_, horbit, hpositive, hcomponents⟩ :=
    component_parameters hr A hA p hcoord cov hfin hp w hw b γ hγ
  refine ⟨horbit,hpositive,?_,?_⟩
  · intro j
    let := hfin b
    apply orbit_fiber_full_cycle
      (cov.monodromyPerm b (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)))
      (fun x : p ⁻¹' {b} => ConnectedComponents.mk (x : CurveOver P g r))
      (fun x => monodromy_component cov γ x) horbit j
  intro j
  obtain ⟨hn,S,T,Φ,c,W,hS,hwS,hT,hΦ,hΦi,_,_,_,_,hW,hident⟩ := hcomponents j
  refine ⟨hn,S,T,Φ,W,hS,hwS,hT,hΦ,hΦi,hW,?_⟩
  intro t
  have hprojection := (hident t).1
  have hbase : (Φ t).val.val.2.val.1 = g ((t : ℂ) ^
      Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : CurveOver P g r) = j}) := by
    have hpow := congrArg (fun u : Disk r => (u : ℂ)) hprojection
    exact (Φ t).val.property.symm.trans (congrArg g hpow)
  have hwvalue := (hident t).2.2
  refine ⟨hprojection,hbase,hwvalue,?_⟩
  rw [hwvalue, ← hbase]
  exact (Φ t).val.val.2.property.2

/-- The translated punctured disk gives z=c+t^h. -/
theorem finite_parameters :
    Specs.D12Complex.Ch21.CyclicParameters.finite_parameters_type := by
  intro P d hP hdeg hd c _ r hr hav
  refine ⟨cyclic_parameters P d hP hdeg hd (fun u => c + u) r hr ?_ ?_,
    finiteRestrictionHomeomorph P c r, fun _ => rfl⟩
  · exact ⟨(isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const),
      fun z _ => (differentiableAt_const c).add differentiableAt_id⟩
  · intro u
    apply hav (c + (u : ℂ))
    · simpa using u.property.1
    · simpa using u.property.2

/-- In the inverse base coordinate the same power parameter gives z=t^(-h). -/
theorem infinity_parameters :
    Specs.D12Complex.Ch21.CyclicParameters.infinity_parameters_type := by
  intro P d hP hdeg hd r hr hav
  refine ⟨cyclic_parameters P d hP hdeg hd (fun u => u⁻¹) r hr ?_ hav,
    infinityRestrictionHomeomorph P r, fun _ => rfl⟩
  exact ⟨(isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const),
    fun z hz => differentiableAt_id.inv (norm_pos_iff.mp hz.1)⟩

theorem admissible_radii :
    Specs.D12Complex.Ch21.CyclicParameters.admissible_radii_type := by
  intro P d hP hdeg hd
  have hE := (D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd).2.1
  refine ⟨fun c => finite_set_punctured_radius _ hE c, ?_⟩
  obtain ⟨r,hr,hav⟩ := finite_set_infinity_radius _ hE
  exact ⟨r,hr,fun u => hav u u.property.1 u.property.2⟩

end D12Complex.CyclicParameters

namespace D12Complex.CyclicParameters.CoveringMorphisms
universe u v w z
variable {E : Type u} {B : Type v} {E' : Type w} {B' : Type z}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {p : E → B} {q : E' → B'}

def fiberMap (F : E → E') (g : B → B')
    (hcomm : ∀ e, q (F e) = g (p e)) (b : B) (x : p ⁻¹' {b}) : q ⁻¹' {g b} :=
  ⟨F x, (hcomm x).trans (congrArg g x.property)⟩

lemma monodromy_natural
    (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (F : E → E') (g : B → B') (hF : Continuous F) (hg : Continuous g)
    (hcomm : ∀ e, q (F e) = g (p e))
    {a b : B} (γ : Path a b) (x : p ⁻¹' {a}) :
    fiberMap F g hcomm b (cov.monodromy (.mk γ) x) =
      cov'.monodromy (.mk (γ.map hg)) (fiberMap F g hcomm a x) := by
  let Γ := cov.liftPath γ x (γ.source.trans x.property.symm)
  let Γ' : C(unitInterval, E') := ⟨fun t => F (Γ t), hF.comp Γ.continuous⟩
  have hΓ : p ∘ Γ = γ := cov.liftPath_lifts γ x (γ.source.trans x.property.symm)
  have hΓ' : q ∘ Γ' = γ.map hg := by
    funext t
    change q (F (Γ t)) = g (γ t)
    rw [hcomm]
    exact congrArg g (congrFun hΓ t)
  have h0 : Γ' 0 = fiberMap F g hcomm a x := by
    change F (Γ 0) = F x
    rw [show Γ 0 = x from cov.liftPath_zero γ x (γ.source.trans x.property.symm)]
  have heq := cov'.monodromy_eq_apply_one hΓ' h0
  apply Subtype.ext
  change F (cov.monodromy (.mk γ) x) = _
  rw [cov.coe_monodromy_mk]
  exact heq.symm
end D12Complex.CyclicParameters.CoveringMorphisms

namespace D12Complex.CyclicParameters
open D12Complex.AlgebraicCovering D12Complex.Ch20.PuncturedDiskLoops

lemma curveOver_monodromy_natural
    (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hadm : ∀ t : Disk r, g t ∈ baseSet P)
    (hg : Continuous (fun t : Disk r => g t))
    (cov : IsCoveringMap (diskProjection P g r)) (globalCov : IsCoveringMap (projection P))
    {a b : Disk r} (γ : Path a b) (x : diskProjection P g r ⁻¹' {a}) :
    curveOverFiberEquiv P g r hadm b (cov.monodromy (.mk γ) x) =
      globalCov.monodromy (.mk (γ.map (hg.subtype_mk (hadm ·))))
        (curveOverFiberEquiv P g r hadm a x) := by
  exact CoveringMorphisms.monodromy_natural cov globalCov
    curvePoint (baseLift P g r hadm) continuous_subtype_val.snd
    (hg.subtype_mk _) (fun x => Subtype.ext x.property.symm) γ x

theorem monodromy_naturality :
    Specs.D12Complex.Ch21.CyclicParameters.monodromy_naturality_type := by
  intro P g r hadm hg cov globalCov a b γ x
  exact congrArg Subtype.val
    (curveOver_monodromy_natural P g r hadm hg cov globalCov γ x).symm

end D12Complex.CyclicParameters
