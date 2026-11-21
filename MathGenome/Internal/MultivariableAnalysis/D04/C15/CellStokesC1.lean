import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC2
import MathGenome.Internal.MultivariableAnalysis.D04.C14.SmoothApproximationInC1
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SubdivisionUniformVector
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators ContDiff Classical
namespace D04.Cells
namespace C1

/-- Uniform convergence is preserved by a function continuous at every point
of the compact limiting image. The approximants need not stay in that image. -/
theorem uniform_comp_of_compact {X Y Z : Type*} [TopologicalSpace X]
    [UniformSpace Y] [UniformSpace Z] {K : Set X} {f : X → Y}
    {F : ℕ → X → Y} {g : Y → Z} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ∀ y ∈ f '' K, ContinuousAt g y)
    (hF : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun j x => g (F j x)) (fun x => g (f x)) atTop K := by
  intro u hu
  have hv := (hK.image_of_continuousOn hf).uniformContinuousAt_of_continuousAt g hg hu
  filter_upwards [hF _ hv] with j hj x hx
  exact hj x hx ⟨x, hx, rfl⟩

/-- Uniformly close maps eventually take their compact domain into any open
neighborhood of the limiting image. -/
theorem eventually_mapsTo {m n : ℕ} {K : Set (E m)} {V : Set (E n)}
    {f : E m → E n} {F : ℕ → E m → E n} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hV : IsOpen V) (hmap : MapsTo f K V)
    (hF : TendstoUniformlyOn F f atTop K) :
    ∀ᶠ j in atTop, MapsTo (F j) K V := by
  obtain ⟨δ, hδ, hsub⟩ := (hK.image_of_continuousOn hf).exists_thickening_subset_open
    hV (by rintro _ ⟨x,hx,rfl⟩; exact hmap hx)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) δ hδ] with j hj x hx
  apply hsub
  exact Metric.mem_thickening_iff.mpr ⟨f x, ⟨x,hx,rfl⟩, by
    simpa only [dist_comm] using hj x hx⟩

/-- Evaluation on finitely many fixed vectors is continuous jointly in the
basepoint and the derivative, even for degree zero. -/
theorem evaluation_continuousAt {m n p : ℕ} {V : Set (E n)}
    (omega : FormField n p) (homega : IsCrForm (some 0) V omega)
    (v : Fin p → E m) (y : E n) (hy : y ∈ V) (A : E m →L[ℝ] E n) :
    ContinuousAt (fun z : E n × (E m →L[ℝ] E n) =>
      omega z.1 (fun i => z.2 (v i))) (y,A) := by
  simp_rw [formField_evaluation]
  apply tendsto_finsetSum
  intro I _
  apply ContinuousAt.mul
  · exact ((homega.2 I).continuousAt (homega.1.mem_nhds hy)).comp (x := (y,A)) continuousAt_fst
  · have hd := finiteDimensional_multilinear_continuous p (fun _ => E n)
      (dx (standardBasis n) I).toMultilinearMap
    apply hd.continuousAt.comp (x := (y,A))
    exact (continuous_pi (fun i => continuous_snd.clm_apply
      (continuous_const : Continuous (fun _ : E n × (E m →L[ℝ] E n) => v i)))).continuousAt

/-- The top evaluation converges uniformly for every fixed input tuple.
Applied to the full basis this is the bulk coefficient; applied to the
basis with one vector omitted it is the coefficient on each face. -/
theorem pullback_evaluation_tendsto {m n p : ℕ} {K : Set (E m)}
    {V : Set (E n)} {f : E m → E n} {F : ℕ → E m → E n}
    (omega : FormField n p) (homega : IsCrForm (some 0) V omega)
    (v : Fin p → E m) (hK : IsCompact K) (hf : ContinuousOn f K)
    (hd : ContinuousOn (fderiv ℝ f) K) (hmap : MapsTo f K V)
    (hF : TendstoUniformlyOn F f atTop K)
    (hD : TendstoUniformlyOn (fun j => fderiv ℝ (F j)) (fderiv ℝ f) atTop K) :
    TendstoUniformlyOn (fun j x => pullback (F j) omega x v)
      (fun x => pullback f omega x v) atTop K := by
  have hpair : TendstoUniformlyOn
      (fun j x => (F j x, fderiv ℝ (F j) x))
      (fun x => (f x, fderiv ℝ f x)) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) ε hε,
      (Metric.tendstoUniformlyOn_iff.mp hD) ε hε] with j hj hj' x hx
    exact max_lt (hj x hx) (hj' x hx)
  exact uniform_comp_of_compact hK (hf.prodMk hd) (by
    rintro _ ⟨x,hx,rfl⟩
    exact evaluation_continuousAt omega homega v (f x) (hmap hx) _) hpair

/-- Uniform limits pass through the existing proper Riemann integral. -/
theorem lowerIntegral_tendsto {k : ℕ} {Q : Darboux.Box k}
    {g : E k → ℝ} {G : ℕ → E k → ℝ}
    (hG : ∀ j, Darboux.Integrable (G j) Q)
    (hu : TendstoUniformlyOn G g atTop (Darboux.carrier Q)) :
    Tendsto (fun j => Darboux.lowerIntegral (G j) Q) atTop
      (𝓝 (Darboux.lowerIntegral g Q)) := by
  obtain ⟨hg, hlim⟩ := Darboux.uniform_limit G g hG hu
  exact hlim

/-- Package a smooth approximant as an actual canonical C² cell. -/
def smoothCell {m n : ℕ} (f : E m → E n) (V : Set (E n))
    (hV : IsOpen V)
    (hs : ∃ U : Set (E m), IsOpen U ∧ cube m ⊆ U ∧ ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo f (cube m) V) : Cell 2 m V where
  toFun x := ⟨f x, hmap x.property⟩
  open_target := hV
  positive := by norm_num
  hasExtension := by
    obtain ⟨U,hU,hsub,hf⟩ := hs
    exact ⟨f,U,hU,hsub,hf.of_le (by norm_num),fun _ => rfl⟩

/-- Every pullback evaluation on the cube is independent of the extension,
not just the top coefficient. -/
theorem pullback_extension_eq {r m n p} {O : Set (E n)} (c : Cell r m O)
    (f : E m → E n) (U : Set (E m)) (hU : IsOpen U) (hsub : cube m ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube m, f x = (c.toFun x).val)
    (omega : FormField n p) (x : cube m) (v : Fin p → E m) :
    pullback (cellExtension c) omega x v = pullback f omega x v := by
  simp only [pullback_apply]
  rw [extension_derivative_unique c f U hU hsub hf heq x,
    extension_on_cube c x, heq x]

theorem smoothCell_evaluation {m n p} (f : E m → E n) (V : Set (E n))
    (hV : IsOpen V)
    (hs : ∃ U : Set (E m), IsOpen U ∧ cube m ⊆ U ∧ ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo f (cube m) V) (omega : FormField n p)
    (x : cube m) (v : Fin p → E m) :
    pullback (cellExtension (smoothCell f V hV hs hmap)) omega x v = pullback f omega x v := by
  obtain ⟨U,hU,hsub,hf⟩ := hs
  exact pullback_extension_eq _ f U hU hsub (hf.of_le (by norm_num)) (fun _ => rfl) omega x v

/-- A face coefficient uses exactly the original derivative columns with
one column omitted, with their original order. -/
theorem face_integral_eq_evaluation {r k n} {O : Set (E n)}
    (c : Cell r (k+1) O) (omega : FormField n k) (i : Fin (k+1)) (ε : Bool) :
    cellIntegral (cellFace c i ε) omega = Darboux.lowerIntegral
      (fun x => pullback (cellExtension c) omega (faceInsertion i ε x)
        (fun j => standardBasis (k+1) (i.succAbove j))) (cubeBox k) := by
  rw [cellFace_integral_pullback]
  congr 1
  funext x
  simp only [pullback_apply, faceInsertion_derivative]

/-- Continuity of each coefficient follows directly from continuity of the
ambient form, the map, and its first derivative. -/
theorem pullback_evaluation_continuousOn {m n p : ℕ} {K : Set (E m)}
    {V : Set (E n)} {f : E m → E n} (omega : FormField n p)
    (homega : IsCrForm (some 0) V omega) (v : Fin p → E m)
    (hf : ContinuousOn f K) (hd : ContinuousOn (fderiv ℝ f) K)
    (hmap : MapsTo f K V) : ContinuousOn (fun x => pullback f omega x v) K := by
  intro x hx
  exact (evaluation_continuousAt omega homega v (f x) (hmap hx) (fderiv ℝ f x)).comp_continuousWithinAt
    (f := fun x => (f x, fderiv ℝ f x)) ((hf x hx).prodMk (hd x hx))

/-- The integrals of a smooth cell are computed with the given approximant,
rather than with its existentially chosen extension. -/
theorem smoothCell_integral {m n} (f : E m → E n) (V : Set (E n))
    (hV : IsOpen V)
    (hs : ∃ U : Set (E m), IsOpen U ∧ cube m ⊆ U ∧ ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo f (cube m) V) (omega : FormField n m) :
    cellIntegral (smoothCell f V hV hs hmap) omega = Darboux.lowerIntegral
      (fun x => pullback f omega x (fun j => standardBasis m j)) (cubeBox m) := by
  apply lowerIntegral_congr
  intro x hx
  exact smoothCell_evaluation f V hV hs hmap omega ⟨x,hx⟩ _

theorem smoothCell_face_integral {k n} (f : E (k+1) → E n) (V : Set (E n))
    (hV : IsOpen V)
    (hs : ∃ U : Set (E (k+1)), IsOpen U ∧ cube (k+1) ⊆ U ∧ ContDiffOn ℝ ∞ f U)
    (hmap : MapsTo f (cube (k+1)) V) (omega : FormField n k)
    (i : Fin (k+1)) (ε : Bool) :
    cellIntegral (cellFace (smoothCell f V hV hs hmap) i ε) omega = Darboux.lowerIntegral
      (fun x => pullback f omega (faceInsertion i ε x)
        (fun j => standardBasis (k+1) (i.succAbove j))) (cubeBox k) := by
  rw [face_integral_eq_evaluation]
  apply lowerIntegral_congr
  intro x hx
  exact smoothCell_evaluation f V hV hs hmap omega
    ⟨_, Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε hx⟩ _

end C1
/-- Stokes for C¹ cells follows by uniform convergence of the bulk and all
face coefficients. No derivative of the pulled-back form is taken. -/
theorem cell_stokes_c1 : Specs.D04.C15.CellStokesC1.cell_stokesType := by
  intro k n O c V omega homega hcV
  let f := cellExtension c
  have hc1 := extension_C1 c
  have hdom := (Specs.D04.C15.CellsChainsAndIntegrals.Model.extension_spec c).1
  have hsub := (Specs.D04.C15.CellsChainsAndIntegrals.Model.extension_spec c).2.1
  have hf : ContinuousOn f (cube (k+1)) := hc1.continuousOn.mono hsub
  have hd : ContinuousOn (fderiv ℝ f) (cube (k+1)) :=
    (hc1.continuousOn_fderiv_of_isOpen hdom le_rfl).mono hsub
  have hmap : MapsTo f (cube (k+1)) V := by
    intro x hx
    change cellExtension c x ∈ V
    rw [extension_on_cube c ⟨x,hx⟩]
    exact hcV ⟨x,hx⟩
  have hK : IsCompact (cube (k+1)) := DiscontinuityCriterion.carrier_compact _
  have homega0 : IsCrForm (some 0) V omega :=
    ⟨homega.1, fun I => ((crOn_iff_contDiffOn 1 V _ homega.1).mp (homega.2 I)).continuousOn⟩
  have hdomega := exteriorDerivative_continuous V omega homega
  obtain ⟨F,hF⟩ := SmoothApproximationInC1.smooth_approximation_in_C1
    (cubeBox (k+1)) (extensionDomain c) f hdom hsub
    ((crOn_iff_contDiffOn 1 _ _ hdom).mpr hc1)
  change Specs.D04.C14.SmoothApproximationInC1.Model.C1ApproximationOn
    (cube (k+1)) f F at hF
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (C1.eventually_mapsTo hK hf homega.1 hmap hF.2.1)
  let G : ℕ → E (k+1) → E n := fun j => F (j+N)
  have hsG (j : ℕ) : ∃ U : Set (E (k+1)), IsOpen U ∧ cube (k+1) ⊆ U ∧
      ContDiffOn ℝ ∞ (G j) U := hF.1 (j+N)
  have hmapG (j : ℕ) : MapsTo (G j) (cube (k+1)) V :=
    hN (j+N) (Nat.le_add_left N j)
  have hG : TendstoUniformlyOn G f atTop (cube (k+1)) :=
    hF.2.1.seq_tendstoUniformlyOn (fun j => j+N) (tendsto_add_atTop_nat N)
  have hDG : TendstoUniformlyOn (fun j => fderiv ℝ (G j)) (fderiv ℝ f)
      atTop (cube (k+1)) :=
    hF.2.2.1.seq_tendstoUniformlyOn (fun j => j+N) (tendsto_add_atTop_nat N)
  have hcontG (j : ℕ) : ContinuousOn (G j) (cube (k+1)) ∧
      ContinuousOn (fderiv ℝ (G j)) (cube (k+1)) := by
    obtain ⟨U,hU,hsubU,hgj⟩ := hsG j
    have hj1 : ContDiffOn ℝ 1 (G j) U := hgj.of_le (by norm_num)
    exact ⟨hj1.continuousOn.mono hsubU,
      (hj1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hsubU⟩
  have hraw {p : ℕ} (eta : FormField n p) (heta : IsCrForm (some 0) V eta)
      (v : Fin p → E (k+1)) (j : ℕ) :
      ContinuousOn (fun x => pullback (G j) eta x v) (cube (k+1)) :=
    C1.pullback_evaluation_continuousOn eta heta v (hcontG j).1 (hcontG j).2 (hmapG j)
  have hbulk := C1.lowerIntegral_tendsto
    (fun j => integrable_cube_of_continuous _
      (hraw (exteriorDerivative omega) hdomega (fun a => standardBasis (k+1) a) j))
    (C1.pullback_evaluation_tendsto (exteriorDerivative omega) hdomega
      (fun a => standardBasis (k+1) a) hK hf hd hmap hG hDG)
  have hface (i : Fin (k+1)) (eps : Bool) :
      Tendsto (fun j => Darboux.lowerIntegral
        (fun x => pullback (G j) omega (faceInsertion i eps x)
          (fun a => standardBasis (k+1) (i.succAbove a))) (cubeBox k)) atTop
        (𝓝 (cellIntegral (cellFace c i eps) omega)) := by
    rw [C1.face_integral_eq_evaluation]
    have hu := (C1.pullback_evaluation_tendsto omega homega0
      (fun a => standardBasis (k+1) (i.succAbove a)) hK hf hd hmap hG hDG).comp
        (faceInsertion i eps)
    apply C1.lowerIntegral_tendsto
    · intro j
      exact integrable_cube_of_continuous _ ((hraw omega homega0 _ j).comp
        (Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_contDiff i eps).continuous.continuousOn
        (fun x hx => Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i eps hx))
    · exact hu.mono (fun x hx =>
        Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i eps hx)
  have heq (j : ℕ) :
      Darboux.lowerIntegral (fun x => pullback (G j) (exteriorDerivative omega) x
        (fun a => standardBasis (k+1) a)) (cubeBox (k+1)) =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        (Darboux.lowerIntegral (fun x => pullback (G j) omega (faceInsertion i true x)
          (fun a => standardBasis (k+1) (i.succAbove a))) (cubeBox k) -
         Darboux.lowerIntegral (fun x => pullback (G j) omega (faceInsertion i false x)
          (fun a => standardBasis (k+1) (i.succAbove a))) (cubeBox k)) := by
    have hj := cell_stokes (C1.smoothCell (G j) V homega.1 (hsG j) (hmapG j))
      V omega homega (fun x => hmapG j x.property)
    change cellIntegral (C1.smoothCell (G j) V homega.1 (hsG j) (hmapG j))
      (exteriorDerivative omega) = chainIntegral omega
        (cellBoundary (C1.smoothCell (G j) V homega.1 (hsG j) (hmapG j))) at hj
    rw [C1.smoothCell_integral (G j) V homega.1 (hsG j) (hmapG j),
      boundaryIntegral_eq_sum] at hj
    simpa only [C1.smoothCell_face_integral] using hj
  have hboundary : Tendsto
      (fun j => ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        (Darboux.lowerIntegral (fun x => pullback (G j) omega (faceInsertion i true x)
          (fun a => standardBasis (k+1) (i.succAbove a))) (cubeBox k) -
         Darboux.lowerIntegral (fun x => pullback (G j) omega (faceInsertion i false x)
          (fun a => standardBasis (k+1) (i.succAbove a))) (cubeBox k))) atTop
        (𝓝 (chainIntegral omega (cellBoundary c))) := by
    rw [boundaryIntegral_eq_sum]
    exact tendsto_finsetSum _ (fun i _ =>
      tendsto_const_nhds.mul ((hface i true).sub (hface i false)))
  exact tendsto_nhds_unique hbulk (hboundary.congr (fun j => (heq j).symm))

/-- The complete finite integer-chain theorem is the linear extension of
the cell theorem, with the form-domain condition only on supported cells. -/
theorem chain_stokes_c1 : Specs.D04.C15.CellStokesC1.chain_stokesType := by
  intro k n O C V omega homega hCV
  classical
  rw [← C.sum_single]
  simp only [map_finsuppSum, boundary_single, map_zsmul, chainIntegral_single]
  apply Finset.sum_congr rfl
  intro c hc
  change C c • cellIntegral c (exteriorDerivative omega) = _
  exact congrArg (fun t : ℝ => C c • t) (cell_stokes_c1 c V omega homega (hCV c hc))

end D04.Cells
