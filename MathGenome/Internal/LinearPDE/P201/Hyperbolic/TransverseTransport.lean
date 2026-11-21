import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.TransverseTransport
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.Transport
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.ContinuityEquation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace P201.Hyperbolic
open P201Specs P201Specs.Hyperbolic

/-- The elapsed map is C¹ on the original chart and the actual flow domain. -/
theorem transverseFlowMap_regular {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) (S : HypersurfaceChart b) :
    IsOpen ((univ ×ˢ S.parameterDomain) ∩
      transverseFlowDomain b S.parametrization) ∧
    ContDiffOn ℝ 1 (transverseFlowMap b S.parametrization)
      ((univ ×ˢ S.parameterDomain) ∩ transverseFlowDomain b S.parametrization) := by
  let D := (univ ×ˢ S.parameterDomain) ∩ transverseFlowDomain b S.parametrization
  have hσ : ContDiffOn ℝ 1 (fun p : ℝ × Space n => S.parametrization p.2)
      (univ ×ˢ S.parameterDomain) :=
    S.regular.comp contDiffOn_snd (fun _ hp => hp.2)
  have hσD := hσ.mono (inter_subset_left (t := transverseFlowDomain b S.parametrization))
  have hc := (hσ.fst.add contDiffOn_fst).prodMk hσ
  have hdo : IsOpen D := by
    exact hc.continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod S.open_parameterDomain) hX.open_domain
  refine ⟨hdo, ?_⟩
  exact (hσD.fst.add contDiffOn_fst).prodMk
    (hX.regular.comp ((hσD.fst.add contDiffOn_fst).prodMk hσD)
      (fun _ hp => hp.2))

/-- The zero elapsed-time map is the prescribed hypersurface itself. -/
theorem transverseFlowMap_initial {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) (S : HypersurfaceChart b)
    {y : Space n} (hy : y ∈ S.parameterDomain) :
    (0, y) ∈ transverseFlowDomain b S.parametrization ∧
    transverseFlowMap b S.parametrization (0, y) = S.parametrization y := by
  have hi := hX.initial _ _ (S.in_domain hy)
  constructor
  · simpa [transverseFlowDomain] using hi.1
  · apply Prod.ext
    · simp [transverseFlowMap]
    · simpa [transverseFlowMap] using hi.2

/-- The elapsed-time curve solves the original space-time ODE. -/
theorem transverseFlowMap_hasDerivAt {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) (σ : Space n → ℝ × Space n)
    {p : ℝ × Space n} (hp : p ∈ transverseFlowDomain b σ) :
    HasDerivAt (fun τ => transverseFlowMap b σ (τ, p.2))
      (1, b.velocity (transverseFlowMap b σ p)) p.1 := by
  have ht : HasDerivAt (fun τ : ℝ => (σ p.2).1 + τ) 1 p.1 := by
    convert! (hasDerivAt_id (𝕜 := ℝ) p.1).const_add (σ p.2).1 using 1
  have hx := (hX.equation _ _ _ hp).2.hasFDerivAt.comp_hasDerivAt p.1 ht
  simpa [Function.comp_def, transverseFlowMap]
    using ht.prodMk hx

/-- The differential at the initial surface has exactly the transverse and
chart tangent columns. This also checks the meaning of the transversality
hypothesis independently of the inverse function theorem. -/
theorem transverseFlowMap_hasFDerivAt_base {n : ℕ} {b : LocalField n}
    (hX : LocalFlowProperties b) (S : HypersurfaceChart b)
    {y : Space n} (hy : y ∈ S.parameterDomain) :
    HasFDerivAt (transverseFlowMap b S.parametrization)
      (transverseFrame b S.parametrization y) (0, y) := by
  let G := transverseFlowMap b S.parametrization
  have h0 := transverseFlowMap_initial hX S hy
  have hR := transverseFlowMap_regular hX S
  have hmem : (0, y) ∈ ((univ ×ˢ S.parameterDomain) ∩
      transverseFlowDomain b S.parametrization) := ⟨⟨mem_univ _, hy⟩, h0.1⟩
  have hd := (hR.2.contDiffAt (hR.1.mem_nhds hmem)).differentiableAt_one.hasFDerivAt
  change HasFDerivAt G (fderiv ℝ G (0, y)) (0, y) at hd
  have ht := hd.comp (0 : ℝ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) y)
  have hx := hd.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ) y)
  have ht' := (transverseFlowMap_hasDerivAt hX S.parametrization h0.1).hasFDerivAt
  rw [h0.2] at ht'
  have hx' : HasFDerivAt (fun z => G (0, z)) (fderiv ℝ S.parametrization y) y := by
    apply ((S.regular.contDiffAt (S.open_parameterDomain.mem_nhds hy)).differentiableAt_one.hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [S.open_parameterDomain.mem_nhds hy] with z hz
    exact (transverseFlowMap_initial hX S hz).2
  have he : fderiv ℝ G (0, y) = transverseFrame b S.parametrization y := by
    have hte := ht.unique ht'
    have hxe := hx.unique hx'
    apply ContinuousLinearMap.ext
    intro p
    have ha := congrArg (fun L : ℝ →L[ℝ] (ℝ × Space n) => L p.1) hte
    have hb := congrArg (fun L : Space n →L[ℝ] (ℝ × Space n) => L p.2) hxe
    rw [show p = (p.1, 0) + (0, p.2) by simp, map_add]
    simpa [transverseFrame, ContinuousLinearMap.coprod_apply] using congrArg₂ (· + ·) ha hb
  simpa only [he] using hd

/-- Construct C¹ flow coordinates for the prescribed transverse hypersurface.
No boundedness, completeness of the flow, or assumed coordinate certificate
is used. -/
theorem transverseCoordinates : transverseCoordinatesStatement := by
  intro n hn b S y₀ hy₀ htrans
  have hX := P201.Hyperbolic.localFlow n hn b
  let G := transverseFlowMap b S.parametrization
  let D := (univ ×ˢ S.parameterDomain) ∩ transverseFlowDomain b S.parametrization
  have h0 := transverseFlowMap_initial hX S hy₀
  have hR := transverseFlowMap_regular hX S
  have hd0 : (0, y₀) ∈ D := ⟨⟨mem_univ _, hy₀⟩, h0.1⟩
  have hgAt : ContDiffAt ℝ 1 G (0, y₀) := hR.2.contDiffAt (hR.1.mem_nhds hd0)
  let A : (ℝ × Space n) ≃L[ℝ] (ℝ × Space n) :=
    (LinearEquiv.ofInjectiveEndo (transverseFrame b S.parametrization y₀).toLinearMap
      htrans).toContinuousLinearEquiv
  have hgDer : HasFDerivAt G (A : (ℝ × Space n) →L[ℝ] (ℝ × Space n)) (0, y₀) :=
    transverseFlowMap_hasFDerivAt_base hX S hy₀
  let e := hgAt.toOpenPartialHomeomorph G hgDer one_ne_zero
  have he0 : (0, y₀) ∈ e.source := hgAt.mem_toOpenPartialHomeomorph_source hgDer one_ne_zero
  have hinv : ContDiffAt ℝ 1 e.symm (S.parametrization y₀) := by
    change ContDiffAt ℝ 1 (hgAt.localInverse hgDer one_ne_zero) _
    simpa only [G, h0.2] using hgAt.to_localInverse hgDer one_ne_zero
  obtain ⟨U, hUp, hU⟩ := hinv.contDiffOn le_rfl (by simp)
  have hgood : e.source ∩ D ∩ G ⁻¹' U ∈ 𝓝 (0, y₀) := by
    refine inter_mem (inter_mem (e.open_source.mem_nhds he0) (hR.1.mem_nhds hd0)) ?_
    apply hgAt.continuousAt.preimage_mem_nhds
    simpa only [G, h0.2] using hUp
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hgood
  let V := Metric.ball y₀ r
  let B := Ioo (-r) r ×ˢ V
  have hBo : IsOpen B := isOpen_Ioo.prod Metric.isOpen_ball
  have hB0 : (0, y₀) ∈ B := by simp [B, V, hr]
  have hBgood : B ⊆ e.source ∩ D ∩ G ⁻¹' U := by
    apply Subset.trans _ hrs
    rw [← ball_prod_same]
    exact prod_mono (by simp [Real.ball_eq_Ioo]) Subset.rfl
  let c := e.restrOpen B hBo
  have hcsource : c.source = B := by
    change e.source ∩ B = B
    exact inter_eq_right.mpr (fun p hp => (hBgood hp).1.1)
  have hccoe : (c : (ℝ × Space n) → ℝ × Space n) = G := rfl
  have hcD : c.source ⊆ D := fun p hp => (hBgood (hcsource ▸ hp)).1.2
  have hcReg : ContDiffOn ℝ 1 c c.source := hR.2.mono hcD
  refine ⟨{
    radius := r
    radius_pos := hr
    parameters := V
    open_parameters := Metric.isOpen_ball
    base_parameter := Metric.mem_ball_self hr
    parameters_subset := ?_
    coord := c
    source_eq := hcsource
    formula := hccoe
    actual_domain := fun p hp => (hcD hp).2
    target_domain := ?_
    base_point := ?_
    regular := hcReg
    inverse_regular := ?_
    initial := ?_
    velocity := ?_ }⟩
  · intro y hy
    have hp : (0, y) ∈ B := ⟨⟨by linarith, hr⟩, hy⟩
    exact ((hBgood hp).1.2).1.2
  · intro p hp
    have hcd := (hcD (c.map_target hp)).2
    have hg := (hX.equation _ _ _ hcd).1
    change G (c.symm p) ∈ b.domain at hg
    simpa only [← hccoe, c.right_inv hp] using hg
  · rw [← h0.2]
    exact c.map_source (hcsource.symm ▸ hB0)
  · apply hU.mono
    intro p hp
    have hu := (hBgood (hcsource ▸ c.map_target hp)).2
    change G (c.symm p) ∈ U at hu
    simpa only [← hccoe, c.right_inv hp] using hu
  · intro y hy
    exact (transverseFlowMap_initial hX S (((hBgood
      (show (0, y) ∈ B from ⟨⟨by linarith, hr⟩, hy⟩)).1.2).1.2)).2
  · intro p hp
    have hd := (hcReg.contDiffAt (c.open_source.mem_nhds hp)).differentiableAt_one
    have ht := hd.hasFDerivAt.comp p.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
    have ht' := (transverseFlowMap_hasDerivAt hX S.parametrization (hcD hp).2).hasFDerivAt
    have heq := ht.unique ht'
    have := congrArg (fun L : ℝ →L[ℝ] (ℝ × Space n) => L 1) heq
    simpa [Function.comp_def, hccoe, G] using this

/-- The global density and Jacobian conclusions are retained unchanged from
the upstream density theorem; their hypotheses are independent of the local
transverse construction. -/
theorem transverse_global_density : continuityEquationStatement := continuityEquation

/-- A product restriction preserves every actual-domain and regularity clause. -/
def restrictTransverseCoordinates {n : ℕ} {b : LocalField n}
    {S : HypersurfaceChart b} {y₀ : Space n} (C : TransverseCoordinates b S y₀)
    {r : ℝ} (hr : 0 < r) {V : Set (Space n)} (hV : IsOpen V) (hy : y₀ ∈ V)
    (hsub : Ioo (-r) r ×ˢ V ⊆ C.coord.source) : TransverseCoordinates b S y₀ := by
  let B := Ioo (-r) r ×ˢ V
  let c := C.coord.restrOpen B (isOpen_Ioo.prod hV)
  have hsrc : c.source = B := inter_eq_right.mpr hsub
  have htarget : c.target ⊆ C.coord.target := by
    intro p hp
    have he : C.coord (c.symm p) = p := c.right_inv hp
    exact he ▸ C.coord.map_source (c.map_target hp).1
  refine {
    radius := r
    radius_pos := hr
    parameters := V
    open_parameters := hV
    base_parameter := hy
    parameters_subset := ?_
    coord := c
    source_eq := hsrc
    formula := C.formula
    actual_domain := fun p hp => C.actual_domain hp.1
    target_domain := fun p hp => C.target_domain (htarget hp)
    base_point := ?_
    regular := C.regular.mono inter_subset_left
    inverse_regular := C.inverse_regular.mono htarget
    initial := ?_
    velocity := fun p hp => C.velocity p hp.1 }
  · intro y hy
    exact C.parameters_subset ((C.source_eq ▸ hsub (show (0, y) ∈ Ioo (-r) r ×ˢ V from ⟨⟨by linarith, hr⟩, hy⟩)).2)
  · rw [← C.initial y₀ C.base_parameter]
    exact c.map_source (hsrc.symm ▸ ⟨⟨by linarith, hr⟩, hy⟩)
  · intro y hy
    exact C.initial y ((C.source_eq ▸ hsub (show (0, y) ∈ Ioo (-r) r ×ˢ V from ⟨⟨by linarith, hr⟩, hy⟩)).2)

/-- Directional transport becomes exactly the scalar characteristic ODE. -/
theorem transverse_pullback_hasDerivAt {n : ℕ} {b : LocalField n}
    {S : HypersurfaceChart b} {y₀ : Space n} (C : TransverseCoordinates b S y₀)
    {𝕜 : Type} [RCLike 𝕜] {q f u : ℝ × Space n → 𝕜}
    (hu : IsTransportSolutionOn C.coord.target b.velocity q f u)
    {p : ℝ × Space n} (hp : p ∈ C.coord.source) :
    HasDerivAt (fun τ => u (C.coord (τ, p.2)))
      (-q (C.coord p) * u (C.coord p) + f (C.coord p)) p.1 := by
  obtain ⟨du, hdu, heq⟩ := hu.2 (C.coord p) (C.coord.map_source hp)
  have hdc := (C.regular.contDiffAt (C.coord.open_source.mem_nhds hp)).differentiableAt_one
  have ht : HasDerivAt (fun τ => C.coord (τ, p.2))
      (1, b.velocity (C.coord p)) p.1 := by
    have h := hdc.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    convert! h using 1
    exact (C.velocity p hp).symm
  have h := (hdu.hasFDerivAt (C.coord.open_target.mem_nhds
    (C.coord.map_source hp))).comp_hasDerivAt p.1 ht
  have he : du (1, b.velocity (C.coord p)) =
      -q (C.coord p) * u (C.coord p) + f (C.coord p) := by
    rw [eq_sub_of_add_eq heq]
    ring
  simpa only [Function.comp_def, he] using h

/-- Uniqueness on the entire chosen coordinate box needs only continuity
of the lower order coefficients, not their spatial differentiability. -/
theorem transverse_solution_unique {n : ℕ} {b : LocalField n}
    {S : HypersurfaceChart b} {y₀ : Space n} (C : TransverseCoordinates b S y₀)
    {𝕜 : Type} [RCLike 𝕜] {q f u v : ℝ × Space n → 𝕜}
    (hq : ContinuousOn q b.domain) (hf : ContinuousOn f b.domain)
    (hu : IsTransportSolutionOn C.coord.target b.velocity q f u)
    (hv : IsTransportSolutionOn C.coord.target b.velocity q f v)
    (hinit : ∀ y ∈ C.parameters, u (S.parametrization y) = v (S.parametrization y)) :
    EqOn u v C.coord.target := by
  intro p hp
  let z := C.coord.symm p
  have hz : z ∈ C.coord.source := C.coord.map_target hp
  have hzy : z.2 ∈ C.parameters := (C.source_eq ▸ hz).2
  let I : D13Unified.TimeInterval := {
    carrier := Ioo (-C.radius) C.radius
    nonempty := ⟨0, by constructor <;> linarith [C.radius_pos]⟩
    ordConnected := ordConnected_Ioo }
  have hzero : (0 : ℝ) ∈ I.carrier := by constructor <;> linarith [C.radius_pos]
  have htime : z.1 ∈ I.carrier := (C.source_eq ▸ hz).1
  have hsrc (t : ℝ) (ht : t ∈ I.carrier) : (t, z.2) ∈ C.coord.source :=
    C.source_eq.symm ▸ ⟨ht, hzy⟩
  have hc : ContinuousOn (fun t => C.coord (t, z.2)) I.carrier :=
    C.regular.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) hsrc
  have hmap : MapsTo (fun t => C.coord (t, z.2)) I.carrier b.domain :=
    fun t ht => C.target_domain (C.coord.map_source (hsrc t ht))
  have hQ := (hq.comp hc hmap).neg
  have hF := hf.comp hc hmap
  have hui : D13Unified.ScalarLinear.IsIVP I
      (fun t => -q (C.coord (t, z.2))) (fun t => f (C.coord (t, z.2)))
      0 (u (S.parametrization z.2)) (fun t => u (C.coord (t, z.2))) := by
    refine ⟨hu.1.continuousOn.comp hc (fun t ht => C.coord.map_source (hsrc t ht)),
      hzero, ?_, ?_⟩
    · change u (C.coord (0, z.2)) = _
      rw [C.initial _ hzy]
    · intro t ht
      exact (transverse_pullback_hasDerivAt C hu (hsrc t ht)).hasDerivWithinAt
  have hvi : D13Unified.ScalarLinear.IsIVP I
      (fun t => -q (C.coord (t, z.2))) (fun t => f (C.coord (t, z.2)))
      0 (u (S.parametrization z.2)) (fun t => v (C.coord (t, z.2))) := by
    refine ⟨hv.1.continuousOn.comp hc (fun t ht => C.coord.map_source (hsrc t ht)),
      hzero, ?_, ?_⟩
    · change v (C.coord (0, z.2)) = _
      rw [C.initial _ hzy, hinit _ hzy]
    · intro t ht
      exact (transverse_pullback_hasDerivAt C hv (hsrc t ht)).hasDerivWithinAt
  have he := (D13Unified.ScalarLinear.eq_variation_of_isIVP I _ _ _ _ hQ hF hui htime).trans
    (D13Unified.ScalarLinear.eq_variation_of_isIVP I _ _ _ _ hQ hF hvi htime).symm
  simpa only [z, C.coord.right_inv hp] using he

/-- A product flow box can be chosen inside any two prescribed open
neighborhoods of the surface point and its parameter. -/
theorem transverseCoordinates_within {n : ℕ} {b : LocalField n}
    {S : HypersurfaceChart b} {y₀ : Space n} (C : TransverseCoordinates b S y₀)
    {W : Set (ℝ × Space n)} (hW : IsOpen W) (hw : S.parametrization y₀ ∈ W)
    {P : Set (Space n)} (hP : IsOpen P) (hp : y₀ ∈ P) :
    ∃ C' : TransverseCoordinates b S y₀,
      C'.coord.target ⊆ C.coord.target ∩ W ∧ C'.parameters ⊆ C.parameters ∩ P := by
  have hzero : (0, y₀) ∈ C.coord.source := C.source_eq.symm ▸
    ⟨⟨by linarith [C.radius_pos], C.radius_pos⟩, C.base_parameter⟩
  have hcont := C.regular.contDiffAt (C.coord.open_source.mem_nhds hzero)
  have hgood : C.coord.source ∩ C.coord ⁻¹' W ∩ (univ ×ˢ P) ∈ 𝓝 (0, y₀) := by
    refine inter_mem (inter_mem (C.coord.open_source.mem_nhds hzero) ?_) ?_
    · apply hcont.continuousAt.preimage_mem_nhds
      rw [C.initial _ C.base_parameter]
      exact hW.mem_nhds hw
    · exact (isOpen_univ.prod hP).mem_nhds ⟨mem_univ _, hp⟩
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hgood
  have hsub : Ioo (-r) r ×ˢ Metric.ball y₀ r ⊆
      C.coord.source ∩ C.coord ⁻¹' W ∩ (univ ×ˢ P) := by
    apply Subset.trans _ hrs
    rw [← ball_prod_same]
    exact prod_mono (by simp [Real.ball_eq_Ioo]) Subset.rfl
  let C' := restrictTransverseCoordinates C hr Metric.isOpen_ball
    (Metric.mem_ball_self hr) (fun p hp => (hsub hp).1.1)
  refine ⟨C', ?_, ?_⟩
  · intro p hp
    have hz := C'.coord.map_target hp
    have hz' : C'.coord.symm p ∈ Ioo (-r) r ×ˢ Metric.ball y₀ r := C'.source_eq ▸ hz
    have he : C.coord (C'.coord.symm p) = p := C'.coord.right_inv hp
    exact he ▸ (show C.coord (C'.coord.symm p) ∈ C.coord.target ∩ W from
      ⟨C.coord.map_source (hsub hz').1.1, (hsub hz').1.2⟩)
  · intro y hy
    have hz : (0, y) ∈ Ioo (-r) r ×ˢ Metric.ball y₀ r := ⟨⟨by linarith, hr⟩, hy⟩
    exact ⟨(C.source_eq ▸ (hsub hz).1.1).2, (hsub hz).2.2⟩

/-- Restriction of the classical PDE requires no new differential choice. -/
theorem transportSolution_mono {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {D E : Set (ℝ × Space n)} {b : ℝ × Space n → Space n}
    {q f u : ℝ × Space n → 𝕜} (hu : IsTransportSolutionOn D b q f u)
    (hED : E ⊆ D) : IsTransportSolutionOn E b q f u := by
  refine ⟨hu.1.mono hED, ?_⟩
  intro p hp
  obtain ⟨du, hd, he⟩ := hu.2 p (hED hp)
  exact ⟨du, hd.mono hED, he⟩

/-- Uniqueness is local as a germ, not just a comparison on one fixed box. -/
theorem transverse_germ_unique {n : ℕ} {b : LocalField n}
    {S : HypersurfaceChart b} {y₀ : Space n} (C : TransverseCoordinates b S y₀)
    {𝕜 : Type} [RCLike 𝕜] {q f u v : ℝ × Space n → 𝕜}
    (hq : ContinuousOn q b.domain) (hf : ContinuousOn f b.domain)
    (hu : IsTransportSolutionOn C.coord.target b.velocity q f u)
    {W : Set (ℝ × Space n)} (hW : IsOpen W) (hw : S.parametrization y₀ ∈ W)
    (hv : IsTransportSolutionOn W b.velocity q f v)
    (hinit : ∀ y ∈ S.parameterDomain, S.parametrization y ∈ W →
      v (S.parametrization y) = u (S.parametrization y)) :
    ∃ N : Set (ℝ × Space n), IsOpen N ∧ S.parametrization y₀ ∈ N ∧
      N ⊆ C.coord.target ∩ W ∧ EqOn v u N := by
  obtain ⟨C', htarget, _⟩ := transverseCoordinates_within C hW hw isOpen_univ (mem_univ _)
  refine ⟨C'.coord.target, C'.coord.open_target, C'.base_point, htarget, ?_⟩
  exact transverse_solution_unique C' hq hf
    (transportSolution_mono hv (fun p hp => (htarget hp).2))
    (transportSolution_mono hu (fun p hp => (htarget hp).1))
    (fun y hy => hinit y (C'.parameters_subset hy) (htarget
      (C'.initial y hy ▸ C'.coord.map_source
        (C'.source_eq.symm ▸ ⟨⟨by linarith [C'.radius_pos], C'.radius_pos⟩, hy⟩))).2)

/-- Constant lower order data meet exactly the shared spatial C¹ interface. -/
theorem spatialC1_const {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (D : Set (ℝ × Space n)) (c : 𝕜) : SpatialC1 D (fun _ => c) := by
  refine ⟨continuousOn_const, fun _ => 0, continuousOn_const, ?_⟩
  intro p hp
  exact (hasFDerivAt_const c p.2).hasFDerivWithinAt

/-- Existence when the base point has time zero. The initial surface itself
need not be a time slice. Two already proved C¹ transport solutions provide
the correction of the time-zero datum, so no time derivative of q or f is
introduced by a change of the hypersurface parameters. -/
theorem transverse_existence_time_zero {n : ℕ} (hn : 1 ≤ n) (b : LocalField n)
    (S : HypersurfaceChart b) (y₀ : Space n) (hy₀ : y₀ ∈ S.parameterDomain)
    (htrans : IsTransverseAt b S.parametrization y₀)
    (ht₀ : (S.parametrization y₀).1 = 0)
    {𝕜 : Type} [RCLike 𝕜] (g : Space n → 𝕜)
    (hg : ContDiffOn ℝ 1 g S.parameterDomain) (q f : ℝ × Space n → 𝕜)
    (hq : SpatialC1 b.domain q) (hf : SpatialC1 b.domain f) :
    ∃ C : TransverseCoordinates b S y₀, ∃ u : ℝ × Space n → 𝕜,
      IsTransportSolutionOn C.coord.target b.velocity q f u ∧
      ∀ y ∈ C.parameters, u (S.parametrization y) = g y := by
  obtain ⟨C⟩ := transverseCoordinates n hn b S y₀ hy₀ htrans
  have hX := P201.Hyperbolic.localFlow n hn b
  let A : Set (Space n) := {x | (0, x) ∈ C.coord.target}
  have hA : IsOpen A := C.coord.open_target.preimage (continuous_const.prodMk continuous_id)
  have hA0 : ∀ x ∈ A, (0, x) ∈ b.domain := fun x hx => C.target_domain hx
  let D := transportDomain b A
  have hD : IsOpen D := isOpen_transportDomain hX hA
  let Y : Space n → Space n := fun x => (C.coord.symm (0, x)).2
  let Z : Space n → ℝ × Space n := fun x => S.parametrization (Y x)
  have hYm : MapsTo Y A S.parameterDomain := by
    intro x hx
    exact C.parameters_subset ((C.source_eq ▸ C.coord.map_target hx).2)
  have hYr : ContDiffOn ℝ 1 Y A :=
    (C.inverse_regular.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)).snd
  have hZr : ContDiffOn ℝ 1 Z A := S.regular.comp hYr hYm
  have hZD : MapsTo Z A D := by
    intro x hx
    have hz := C.coord.map_target hx
    have he := C.coord.right_inv hx
    rw [C.formula] at he
    have ht := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    change (S.parametrization (Y x)).1 + (C.coord.symm (0, x)).1 = 0 at ht
    change P201Specs.Hyperbolic.localFlow b
      ((S.parametrization (Y x)).1 + (C.coord.symm (0, x)).1)
      (S.parametrization (Y x)).1 (S.parametrization (Y x)).2 = x at hv
    rw [ht] at hv
    have hd := C.actual_domain hz
    change ((S.parametrization (Y x)).1 + (C.coord.symm (0, x)).1,
      (S.parametrization (Y x)).1, (S.parametrization (Y x)).2) ∈ localFlowDomain b at hd
    rw [ht] at hd
    exact ⟨hd, hv.symm ▸ hx⟩
  let X := P201Specs.Hyperbolic.localFlow b
  let a : ℝ × Space n → 𝕜 := transportFormula X q (fun _ => 0) (fun _ => 1)
  let v : ℝ × Space n → 𝕜 := transportFormula X q f (fun _ => 0)
  have ha : IsTransportIVPOn D A b.velocity q (fun _ => 0) (fun _ => 1) a :=
    (((transportFlow.2 n hn b).2 A hA hA0 𝕜 (fun _ => 1) contDiffOn_const).2
      q (fun _ => 0) hq (spatialC1_const _ _)).1
  have hv : IsTransportIVPOn D A b.velocity q f (fun _ => 0) v :=
    (((transportFlow.2 n hn b).2 A hA hA0 𝕜 (fun _ => 0) contDiffOn_const).2 q f hq hf).1
  have hane (p : ℝ × Space n) : a p ≠ 0 := by
    simp only [a, transportFormula, mul_one, mul_zero, intervalIntegral.integral_zero, add_zero]
    intro he
    have hc := D13Unified.ScalarLinear.factor_cancel
      (-(∫ r in (0 : ℝ)..p.1, q (r, X r p.1 p.2)))
    rw [he, zero_mul] at hc
    exact zero_ne_one hc
  let h : Space n → 𝕜 := fun x => (g (Y x) - v (Z x)) * (a (Z x))⁻¹
  have hhr : ContDiffOn ℝ 1 h A :=
    ((hg.comp hYr hYm).sub (hv.1.1.comp hZr hZD)).mul
      ((ha.1.1.comp hZr hZD).inv (fun x hx => hane (Z x)))
  have hu : IsTransportIVPOn D A b.velocity q f h (transportFormula X q f h) :=
    (((transportFlow.2 n hn b).2 A hA hA0 𝕜 h hhr).2 q f hq hf).1
  have hpointA : (S.parametrization y₀).2 ∈ A := by
    change (0, (S.parametrization y₀).2) ∈ C.coord.target
    simpa only [← ht₀, Prod.mk.eta] using C.base_point
  have hpointD : S.parametrization y₀ ∈ D := by
    have hi := hX.initial 0 (S.parametrization y₀).2 (hA0 _ hpointA)
    exact ⟨by simpa only [ht₀] using hi.1, by simpa only [ht₀, hi.2] using hpointA⟩
  let P : Set (Space n) := S.parameterDomain ∩
    (fun y => (S.parametrization y).1) ⁻¹' Ioo (-C.radius) C.radius
  have hP : IsOpen P := S.regular.fst.continuousOn.isOpen_inter_preimage
    S.open_parameterDomain isOpen_Ioo
  have hp : y₀ ∈ P := by
    refine ⟨hy₀, ?_⟩
    change (S.parametrization y₀).1 ∈ Ioo (-C.radius) C.radius
    rw [ht₀]
    constructor <;> linarith [C.radius_pos]
  obtain ⟨C', htarget, hparams⟩ := transverseCoordinates_within C hD hpointD hP hp
  refine ⟨C', transportFormula X q f h,
    transportSolution_mono hu.1 (fun p hp => (htarget hp).2), ?_⟩
  intro y hy
  have hyC := (hparams hy).1
  have ht := (hparams hy).2.2
  have hback : (-(S.parametrization y).1, y) ∈ C.coord.source := by
    rw [C.source_eq]
    exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hyC⟩
  let x := X 0 (S.parametrization y).1 (S.parametrization y).2
  have he : C.coord (-(S.parametrization y).1, y) = (0, x) := by
    rw [C.formula]
    simp [transverseFlowMap, x, X]
  have hxA : x ∈ A := by
    change (0, x) ∈ C.coord.target
    exact he ▸ C.coord.map_source hback
  have hY : Y x = y := by
    have hi := C.coord.left_inv hback
    rw [he] at hi
    exact congrArg Prod.snd hi
  have hZ : Z x = S.parametrization y := by simp only [Z, hY]
  have hval : transportFormula X q f h (S.parametrization y) =
      a (S.parametrization y) * h x + v (S.parametrization y) := by
    simp only [transportFormula, a, v, mul_one, mul_zero, intervalIntegral.integral_zero,
      add_zero, zero_add, x]
  rw [hval]
  dsimp only [h]
  rw [hY, hZ]
  calc
    a (S.parametrization y) * ((g y - v (S.parametrization y)) * (a (S.parametrization y))⁻¹) +
        v (S.parametrization y) =
      (g y - v (S.parametrization y)) *
        (a (S.parametrization y) * (a (S.parametrization y))⁻¹) + v (S.parametrization y) := by ring
    _ = g y := by rw [mul_inv_cancel₀ (hane _), mul_one, sub_add_cancel]

/-- Time translation preserves continuity and continuous spatial derivatives;
it imposes no time differentiability on the scalar coefficients. -/
theorem spatialC1_time_translate {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {D : Set (ℝ × Space n)} {h : ℝ × Space n → 𝕜} (hh : SpatialC1 D h) (s : ℝ) :
    SpatialC1 ((fun p : ℝ × Space n => p + (s, 0)) ⁻¹' D)
      (fun p => h (p + (s, 0))) := by
  have ht : Continuous (fun p : ℝ × Space n => p + (s, 0)) := continuous_id.add continuous_const
  obtain ⟨dh, hdc, hd⟩ := hh.spatial
  refine ⟨hh.continuous.comp ht.continuousOn (fun p hp => hp),
    fun p => dh (p + (s, 0)), hdc.comp ht.continuousOn (fun p hp => hp), ?_⟩
  intro p hp
  change HasFDerivWithinAt (fun y => h (p.1 + s, y + 0)) (dh (p + (s, 0)))
    {y | (p.1 + s, y + 0) ∈ D} p.2
  simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hd (p + (s, 0)) hp

/-- Translation of a classical transport solution back to the original clock. -/
theorem transportSolution_time_translate {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {D : Set (ℝ × Space n)} (s : ℝ) {b : ℝ × Space n → Space n}
    {q f u : ℝ × Space n → 𝕜}
    (hu : IsTransportSolutionOn D (fun p => b (p + (s, 0)))
      (fun p => q (p + (s, 0))) (fun p => f (p + (s, 0))) u) :
    IsTransportSolutionOn ((fun p : ℝ × Space n => p - (s, 0)) ⁻¹' D)
      b q f (fun p => u (p - (s, 0))) := by
  refine ⟨hu.1.comp (contDiffOn_id.sub contDiffOn_const) (fun p hp => hp), ?_⟩
  intro p hp
  obtain ⟨du, hd, he⟩ := hu.2 (p - (s, 0)) hp
  refine ⟨du, ?_, ?_⟩
  · have hc := hd.comp p ((hasFDerivAt_id p).sub_const (s, 0)).hasFDerivWithinAt
      (fun p hp => hp)
    convert! hc using 1
  · simpa only [sub_add_cancel] using he

/-- The arbitrary-time local existence theorem, obtained by translating the
clock and then restricting the original elapsed-flow coordinates. -/
theorem transverse_existence {n : ℕ} (hn : 1 ≤ n) (b : LocalField n)
    (S : HypersurfaceChart b) (y₀ : Space n) (hy₀ : y₀ ∈ S.parameterDomain)
    (htrans : IsTransverseAt b S.parametrization y₀)
    {𝕜 : Type} [RCLike 𝕜] (g : Space n → 𝕜)
    (hg : ContDiffOn ℝ 1 g S.parameterDomain) (q f : ℝ × Space n → 𝕜)
    (hq : SpatialC1 b.domain q) (hf : SpatialC1 b.domain f) :
    ∃ C : TransverseCoordinates b S y₀, ∃ u : ℝ × Space n → 𝕜,
      IsTransportSolutionOn C.coord.target b.velocity q f u ∧
      ∀ y ∈ C.parameters, u (S.parametrization y) = g y := by
  let s := (S.parametrization y₀).1
  let b₀ : LocalField n := {
    domain := (fun p : ℝ × Space n => p + (s, 0)) ⁻¹' b.domain
    isOpen_domain := b.isOpen_domain.preimage (continuous_id.add continuous_const)
    velocity := fun p => b.velocity (p + (s, 0))
    regular := b.regular.comp (contDiffOn_id.add contDiffOn_const) (fun p hp => hp) }
  let S₀ : HypersurfaceChart b₀ := {
    parameterDomain := S.parameterDomain
    open_parameterDomain := S.open_parameterDomain
    parametrization := fun y => S.parametrization y - (s, 0)
    regular := S.regular.sub contDiffOn_const
    in_domain := fun y hy => by
      change (S.parametrization y - (s, 0) + (s, 0)) ∈ b.domain
      simpa only [sub_add_cancel] using S.in_domain hy }
  have htrans₀ : IsTransverseAt b₀ S₀.parametrization y₀ := by
    have he : transverseFrame b₀ S₀.parametrization y₀ =
        transverseFrame b S.parametrization y₀ := by
      simp only [transverseFrame, S₀, b₀, fderiv_sub_const, sub_add_cancel]
    change Function.Injective (transverseFrame b₀ S₀.parametrization y₀)
    rw [he]
    exact htrans
  have ht₀ : (S₀.parametrization y₀).1 = 0 := by simp [S₀, s]
  obtain ⟨C₀, u₀, hu₀, hi₀⟩ := transverse_existence_time_zero hn b₀ S₀ y₀ hy₀ htrans₀ ht₀
    g hg (fun p => q (p + (s, 0))) (fun p => f (p + (s, 0)))
    (spatialC1_time_translate hq s) (spatialC1_time_translate hf s)
  let W := (fun p : ℝ × Space n => p - (s, 0)) ⁻¹' C₀.coord.target
  have hW : IsOpen W := C₀.coord.open_target.preimage (continuous_id.sub continuous_const)
  have hw : S.parametrization y₀ ∈ W := C₀.base_point
  let u : ℝ × Space n → 𝕜 := fun p => u₀ (p - (s, 0))
  have hu : IsTransportSolutionOn W b.velocity q f u := transportSolution_time_translate s hu₀
  obtain ⟨C⟩ := transverseCoordinates n hn b S y₀ hy₀ htrans
  obtain ⟨C', htarget, hparams⟩ := transverseCoordinates_within C hW hw
    C₀.open_parameters C₀.base_parameter
  exact ⟨C', u, transportSolution_mono hu (fun p hp => (htarget hp).2),
    fun y hy => hi₀ y (hparams hy).2⟩

/-- Local transverse data determine a unique classical transport solution,
including the zero-order term and source with the stated spatial regularity. -/
theorem transverseTransport : transverseTransportStatement := by
  intro n hn b S y₀ hy₀ htrans 𝕜 _ g hg q f hq hf
  obtain ⟨C, u, hu, hi⟩ := transverse_existence hn b S y₀ hy₀ htrans g hg q f hq hf
  refine ⟨C, u, hu, hi, ?_, ?_⟩
  · intro v hv hvi
    exact transverse_solution_unique C hq.continuous hf.continuous hv hu
      (fun y hy => (hvi y hy).trans (hi y hy).symm)
  · intro W v hW hw hv hvi
    -- Shrink the parameter neighborhood as well, so the prescribed data for
    -- u are available throughout the germ comparison.
    obtain ⟨C', htarget, hparams⟩ := transverseCoordinates_within C hW hw
      isOpen_univ (mem_univ _)
    refine ⟨C'.coord.target, C'.coord.open_target, C'.base_point, htarget, ?_⟩
    apply transverse_solution_unique C' hq.continuous hf.continuous
      (transportSolution_mono hv (fun p hp => (htarget hp).2))
      (transportSolution_mono hu (fun p hp => (htarget hp).1))
    intro y hy
    have hσ : S.parametrization y ∈ C'.coord.target :=
      C'.initial y hy ▸ C'.coord.map_source (C'.source_eq.symm ▸
        ⟨⟨by linarith [C'.radius_pos], C'.radius_pos⟩, hy⟩)
    exact (hvi y (C'.parameters_subset hy) (htarget hσ).2).trans
      (hi y (hparams hy).1).symm

/-- The full source proposition, with separate global and local hypotheses. -/
theorem continuityAndTransverseData : continuityAndTransverseDataStatement :=
  ⟨continuityEquation, transverseCoordinates, transverseTransport⟩

end P201.Hyperbolic
