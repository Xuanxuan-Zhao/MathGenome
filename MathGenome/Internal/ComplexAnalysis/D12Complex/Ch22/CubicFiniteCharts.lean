import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.CubicFiniteCharts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.ProjectivePlaneTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.HalfPeriodValues
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.SimpleRootBranches
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped Topology
namespace D12Complex.CubicFiniteCharts
open ProjectivePlaneTopology
open D12Complex.Ch22
open Specs.D12Complex.Ch22.HalfPeriodValues (branchValue)
open WeierstrassEquations (g₂ g₃)

theorem homogeneousEquation_smul (g₂ g₃ t : ℂ) (v : Fin 3 → ℂ) :
    homogeneousEquation g₂ g₃ (t • v) = t ^ 3 * homogeneousEquation g₂ g₃ v := by
  simp only [homogeneousEquation, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem onCubic_projection_iff (g₂ g₃ : ℂ) (v : HomogeneousVector) :
    OnCubic g₂ g₃ (projection v) ↔ homogeneousEquation g₂ g₃ v.val = 0 := by
  constructor
  · rintro ⟨w, he, hw⟩
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ w.property v.property).mp he
    have hscale := homogeneousEquation_smul g₂ g₃ (t : ℂ) v.val
    rw [← ht] at hw
    change homogeneousEquation g₂ g₃ ((t : ℂ) • v.val) = 0 at hw
    rw [hscale] at hw
    exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ t.ne_zero)
  · intro hv
    exact ⟨v, rfl, hv⟩

theorem homogeneousEquation_zero_iff_of_projection_eq (g₂ g₃ : ℂ)
    (v w : HomogeneousVector) (h : projection v = projection w) :
    homogeneousEquation g₂ g₃ v.val = 0 ↔ homogeneousEquation g₂ g₃ w.val = 0 := by
  rw [← onCubic_projection_iff g₂ g₃ v, h, onCubic_projection_iff]

@[simp] theorem onCubic_affineParam_zero_iff (g₂ g₃ : ℂ) (z : Fin 2 → ℂ) :
    OnCubic g₂ g₃ (affineParam 0 z) ↔
      z 1 ^ 2 = 4 * z 0 ^ 3 - g₂ * z 0 - g₃ := by
  simp only [affineParam, onCubic_projection_iff, homogeneousEquation]
  change z 1 ^ 2 * 1 - 4 * z 0 ^ 3 + g₂ * z 0 * 1 ^ 2 + g₃ * 1 ^ 3 = 0 ↔ _
  constructor <;> intro h <;> linear_combination h

theorem onCubic_isClosed (g₂ g₃ : ℂ) : IsClosed {p | OnCubic g₂ g₃ p} := by
  apply projection_quotient.isClosed_preimage.mp
  have he : projection ⁻¹' {p | OnCubic g₂ g₃ p} =
      {v : HomogeneousVector | homogeneousEquation g₂ g₃ v.val = 0} := by
    ext v
    exact onCubic_projection_iff g₂ g₃ v
  rw [he]
  apply isClosed_eq _ continuous_const
  unfold homogeneousEquation
  have hc (i : Fin 3) : Continuous (fun v : HomogeneousVector => v.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact (((hc 2).pow 2 |>.mul (hc 0)).sub (continuous_const.mul ((hc 1).pow 3)) |>.add
    ((continuous_const.mul (hc 1)).mul ((hc 0).pow 2))) |>.add
      (continuous_const.mul ((hc 0).pow 3))

instance cubicCompactSpace (g₂ g₃ : ℂ) : CompactSpace (Cubic g₂ g₃) :=
  isCompact_iff_compactSpace.mp (onCubic_isClosed g₂ g₃).isCompact

instance cubicT2Space (g₂ g₃ : ℂ) : T2Space (Cubic g₂ g₃) :=
  inferInstanceAs (T2Space {p : ComplexProjectivePlane // OnCubic g₂ g₃ p})
instance cubicSecondCountableTopology (g₂ g₃ : ℂ) :
    SecondCountableTopology (Cubic g₂ g₃) :=
  TopologicalSpace.Subtype.secondCountableTopology {p : ComplexProjectivePlane | OnCubic g₂ g₃ p}

@[simp] theorem finiteX_affinePoint (x y : ℂ) : finiteX (affinePoint x y) = x := by
  change affineCoordinate 0 (affineParam 0 ![x,y]) 0 = x
  rw [affineCoordinate_param]
  rfl
@[simp] theorem finiteY_affinePoint (x y : ℂ) : finiteY (affinePoint x y) = y := by
  change affineCoordinate 0 (affineParam 0 ![x,y]) 1 = y
  rw [affineCoordinate_param]
  rfl

theorem affinePoint_mem_patch (x y : ℂ) : affinePoint x y ∈ coordinatePatch 0 :=
  affineParam_mem_patch 0 ![x,y]

theorem affinePoint_coordinates {p : ComplexProjectivePlane}
    (hp : p ∈ coordinatePatch 0) : affinePoint (finiteX p) (finiteY p) = p := by
  have h : ![finiteX p, finiteY p] = affineCoordinate 0 p := by
    ext i
    fin_cases i <;> rfl
  simpa only [affinePoint, h] using affineParam_coordinate 0 hp

@[simp] theorem onCubic_affinePoint_iff (g₂ g₃ x y : ℂ) :
    OnCubic g₂ g₃ (affinePoint x y) ↔ y ^ 2 = q g₂ g₃ x :=
  onCubic_affineParam_zero_iff g₂ g₃ ![x,y]

theorem affine_equation : Specs.D12Complex.Ch22.CubicFiniteCharts.affine_equation_type := by
  intro g₂ g₃ p hp
  rw [← affinePoint_coordinates hp, onCubic_affinePoint_iff]
  simp

theorem continuous_affinePoint :
    Continuous (fun z : ℂ × ℂ => affinePoint z.1 z.2) := by
  apply (continuous_affineParam 0).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

theorem continuousOn_finiteX : ContinuousOn finiteX (coordinatePatch 0) := by
  change ContinuousOn (fun p => affineCoordinate 0 p 0) (coordinatePatch 0)
  exact (continuous_apply 0).comp_continuousOn (continuousOn_affineCoordinate 0)

theorem continuousOn_finiteY : ContinuousOn finiteY (coordinatePatch 0) := by
  change ContinuousOn (fun p => affineCoordinate 0 p 1) (coordinatePatch 0)
  exact (continuous_apply 1).comp_continuousOn (continuousOn_affineCoordinate 0)

theorem continuousOn_finiteX_cubic (g₂ g₃ : ℂ) :
    ContinuousOn (fun p : Cubic g₂ g₃ => finiteX p.val) (finitePatch g₂ g₃) :=
  continuousOn_finiteX.comp continuous_subtype_val.continuousOn (fun _ hp => hp)

theorem continuousOn_finiteY_cubic (g₂ g₃ : ℂ) :
    ContinuousOn (fun p : Cubic g₂ g₃ => finiteY p.val) (finitePatch g₂ g₃) :=
  continuousOn_finiteY.comp continuous_subtype_val.continuousOn (fun _ hp => hp)

theorem finitePatch_isOpen (g₂ g₃ : ℂ) : IsOpen (finitePatch g₂ g₃) :=
  (coordinatePatch_isOpen 0).preimage continuous_subtype_val

theorem well_defined : Specs.D12Complex.Ch22.CubicFiniteCharts.well_defined_type :=
  onCubic_projection_iff

theorem closed : Specs.D12Complex.Ch22.CubicFiniteCharts.closed_type := onCubic_isClosed

theorem topology : Specs.D12Complex.Ch22.CubicFiniteCharts.topology_type :=
  fun g₂ g₃ => ⟨cubicCompactSpace g₂ g₃, cubicT2Space g₂ g₃,
    cubicSecondCountableTopology g₂ g₃⟩


lemma x_graph (g₂ g₃ a b : ℂ) (hab : b ^ 2 = q g₂ g₃ a) (hb : b ≠ 0) :
    ∃ (U V : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧
      HolomorphicOn U f ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, w ^ 2 = q g₂ g₃ z ↔ w = f z := by
  have hP : ContDiffAt ℂ 1
      (fun p : ℂ × ℂ => p.2 ^ 2 - q g₂ g₃ p.1) (a, b) := by
    unfold q
    fun_prop
  have hzero : b ^ 2 - q g₂ g₃ a = 0 := sub_eq_zero.mpr hab
  have hD : HasDerivAt (fun w : ℂ => w ^ 2 - q g₂ g₃ a) (2 * b) b := by
    convert ((hasDerivAt_id' b).pow 2).sub_const (q g₂ g₃ a) using 1 <;> ring
  obtain ⟨U, V, f, hU, hV, haU, hbV, hf, hfa, hmap, hgraph⟩ :=
    SimpleRootBranches.local_simple_root_hasDerivAt hP hzero hD (mul_ne_zero (by norm_num) hb)
  exact ⟨U, V, f, hU, hV, haU, hbV, ⟨hU, hf⟩, hfa, hmap,
    fun z hz w hw => by simpa only [sub_eq_zero] using hgraph z hz w hw⟩

lemma y_graph (g₂ g₃ a : ℂ) (ha : q g₂ g₃ a = 0) (hqa : 12 * a ^ 2 - g₂ ≠ 0) :
    ∃ (U V : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ a ∈ V ∧
      HolomorphicOn U f ∧ f 0 = a ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, z ^ 2 = q g₂ g₃ w ↔ w = f z := by
  have hP : ContDiffAt ℂ 1
      (fun p : ℂ × ℂ => q g₂ g₃ p.2 - p.1 ^ 2) (0, a) := by
    unfold q
    fun_prop
  have hzero : q g₂ g₃ a - (0 : ℂ) ^ 2 = 0 := by simpa using ha
  have hD : HasDerivAt (fun w : ℂ => q g₂ g₃ w - (0 : ℂ) ^ 2)
      (12 * a ^ 2 - g₂) a := by
    unfold q
    convert ((((hasDerivAt_id' a).pow 3).const_mul 4).sub
      ((hasDerivAt_id' a).const_mul g₂)).sub_const g₃ |>.sub_const ((0 : ℂ) ^ 2) using 1 <;> ring
  obtain ⟨U, V, f, hU, hV, hU0, haV, hf, hfa, hmap, hgraph⟩ :=
    SimpleRootBranches.local_simple_root_hasDerivAt hP hzero hD hqa
  exact ⟨U, V, f, hU, hV, hU0, haV, ⟨hU, hf⟩, hfa, hmap,
    fun z hz w hw => by
      have hg : q g₂ g₃ w = z ^ 2 ↔ w = f z := by
        simpa only [sub_eq_zero] using hgraph z hz w hw
      exact eq_comm.trans hg⟩


theorem hasDerivAt_q (G H a : ℂ) : HasDerivAt (q G H) (12*a^2-G) a := by
  change HasDerivAt (fun x : ℂ => 4*x^3-G*x-H) (12*a^2-G) a
  convert (((hasDerivAt_id a).pow 3).const_mul 4 |>.sub
    ((hasDerivAt_id a).const_mul G)).sub_const H using 1 <;> dsimp [q] <;> ring

theorem cubic_derivative_ne_zero {G H a : ℂ} (hdisc : G^3 - 27*H^2 ≠ 0)
    (hroot : q G H a = 0) : 12*a^2-G ≠ 0 := by
  intro hd
  apply hdisc
  have hG : G = 12*a^2 := by linear_combination -hd
  have hH : H = -8*a^3 := by
    dsimp [q] at hroot
    linear_combination -hroot + a*hd
  rw [hG, hH]
  ring

theorem finite_nonsingular {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {a b : ℂ} (hcurve : b^2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a) :
    b ≠ 0 ∨ 12*a^2-g₂ ω₁ ω₂ ≠ 0 := by
  by_cases hb : b = 0
  · right
    apply cubic_derivative_ne_zero (HalfPeriodValues.discriminant ω₁ ω₂ h₁ h₂)
    simpa [hb] using hcurve.symm
  · exact Or.inl hb

theorem branch_derivative_ne_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (i : Fin 3) :
    12 * branchValue ω₁ ω₂ i ^ 2 - g₂ ω₁ ω₂ ≠ 0 := by
  exact cubic_derivative_ne_zero (HalfPeriodValues.discriminant ω₁ ω₂ h₁ h₂)
    (HalfPeriodValues.branch_roots h₁ h₂ i)

theorem root_iff_branchValue {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (a : ℂ) :
    q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a = 0 ↔ ∃ i, a = branchValue ω₁ ω₂ i := by
  unfold q
  rw [HalfPeriodValues.factorization ω₁ ω₂ h₁ h₂ a]
  simp only [mul_eq_zero, (by norm_num : (4 : ℂ) ≠ 0), false_or,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]

theorem zero_y_iff_branchValue {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) {a b : ℂ}
    (hcurve : b^2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) a) :
    b = 0 ↔ ∃ i, a = branchValue ω₁ ω₂ i := by
  rw [← root_iff_branchValue h₁ h₂, ← hcurve]
  simp


lemma inverse_coordinate_holomorphic {g₂ g₃ : ℂ} {axis₁ : Bool}
    {e : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ}
    (he : IsFiniteChart g₂ g₃ axis₁ e) (axis₂ : Bool) :
    HolomorphicOn e.target (fun z => coordinate axis₂ (e.symm z).val) := by
  cases axis₂
  · simpa only [coordinate, Bool.false_eq_true, ↓reduceIte] using he.2.2.2
  · simpa only [coordinate, ↓reduceIte] using he.2.2.1

lemma transition_holomorphic {g₂ g₃ : ℂ} {axis₁ axis₂ : Bool}
    {e f : OpenPartialHomeomorph (Cubic g₂ g₃) ℂ}
    (he : IsFiniteChart g₂ g₃ axis₁ e) (hf : IsFiniteChart g₂ g₃ axis₂ f) :
    HolomorphicOn (e.symm.trans f).source (e.symm.trans f) := by
  refine ⟨(e.symm.trans f).open_source, ?_⟩
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ f.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage] using hz
  apply ((inverse_coordinate_holomorphic he axis₂).2 z hz'.1).congr_of_eventuallyEq
  filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
  have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage] using hw
  exact hf.2.1 (e.symm w) hw'.2

theorem transitions : Specs.D12Complex.Ch22.CubicFiniteCharts.transitions_type := by
  intro g₂ g₃ axis₁ axis₂ e f he hf
  dsimp only
  let t := e.symm.trans f
  have ht : HolomorphicOn t.source t := transition_holomorphic he hf
  have hts : HolomorphicOn t.target t.symm := by
    change HolomorphicOn t.symm.source t.symm
    simpa only [t, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source] using
      transition_holomorphic hf he
  exact ⟨ht, hts, t.mapsTo, t.mapsTo_symm, t.leftInvOn, t.rightInvOn⟩


/-- A continuous graph over an open coordinate rectangle is an open chart. -/
def chartOfParametrization {X : Type*} [TopologicalSpace X]
    (c d : X → ℂ) (S : Set X) (U V : Set ℂ) (g : ℂ → X)
    (hS : IsOpen S) (hU : IsOpen U) (hV : IsOpen V)
    (hc : ContinuousOn c S) (hd : ContinuousOn d S) (hg : ContinuousOn g U)
    (hgc : ∀ t ∈ U, c (g t) = t) (hgd : ∀ t ∈ U, d (g t) ∈ V)
    (hgs : MapsTo g U S)
    (hcg : ∀ p ∈ S, c p ∈ U → d p ∈ V → g (c p) = p) :
    OpenPartialHomeomorph X ℂ where
  toFun := c
  invFun := g
  source := {p | p ∈ S ∧ c p ∈ U ∧ d p ∈ V}
  target := U
  map_source' := fun _ hp => hp.2.1
  map_target' := fun t ht => ⟨hgs ht, (hgc t ht).symm ▸ ht, hgd t ht⟩
  left_inv' := fun p hp => hcg p hp.1 hp.2.1 hp.2.2
  right_inv' := fun t ht => hgc t ht
  open_source := by
    have h := (hc.isOpen_inter_preimage hS hU).inter (hd.isOpen_inter_preimage hS hV)
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto
  open_target := hU
  continuousOn_toFun := hc.mono (fun _ hp => hp.1)
  continuousOn_invFun := hg



theorem nonsingular : Specs.D12Complex.Ch22.CubicFiniteCharts.nonsingular_type := by
  intro ω₁ ω₂ h₁ h₂ x y hxy
  exact finite_nonsingular h₁ h₂ hxy

theorem branch_simple : Specs.D12Complex.Ch22.CubicFiniteCharts.branch_simple_type := by
  intro ω₁ ω₂ h₁ h₂
  exact ⟨root_iff_branchValue h₁ h₂, branch_derivative_ne_zero h₁ h₂⟩

private lemma holo_congr {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : HolomorphicOn U f) (heq : EqOn g f U) : HolomorphicOn U g := by
  refine ⟨hf.1, fun z hz => ?_⟩
  apply (hf.2 z hz).congr_of_eventuallyEq
  filter_upwards [hf.1.mem_nhds hz] with w hw
  exact heq hw

theorem x_chart : Specs.D12Complex.Ch22.CubicFiniteCharts.x_chart_type := by
  classical
  intro g₂ g₃ a b hab hb
  obtain ⟨U, V, f, hU, hV, haU, hbV, hf, hfa, hmap, hgraph⟩ :=
    x_graph g₂ g₃ a b hab hb
  have hpoint (t : ℂ) (ht : t ∈ U) : OnCubic g₂ g₃ (affinePoint t (f t)) :=
    (onCubic_affinePoint_iff g₂ g₃ t (f t)).mpr ((hgraph t ht (f t) (hmap ht)).mpr rfl)
  let center : Cubic g₂ g₃ := ⟨affinePoint a b, (onCubic_affinePoint_iff g₂ g₃ a b).mpr hab⟩
  let g : ℂ → Cubic g₂ g₃ := fun t => if ht : t ∈ U then
    ⟨affinePoint t (f t), hpoint t ht⟩ else center
  have hgval (t : ℂ) (ht : t ∈ U) : (g t).val = affinePoint t (f t) := by
    simp [g, ht]
  have hgc (t : ℂ) (ht : t ∈ U) : finiteX (g t).val = t := by
    rw [hgval t ht, finiteX_affinePoint]
  have hgy (t : ℂ) (ht : t ∈ U) : finiteY (g t).val = f t := by
    rw [hgval t ht, finiteY_affinePoint]
  have hgd (t : ℂ) (ht : t ∈ U) : finiteY (g t).val ∈ V := by
    rw [hgy t ht]
    exact hmap ht
  have hgs : MapsTo g U (finitePatch g₂ g₃) := by
    intro t ht
    change (g t).val ∈ ProjectivePlaneTopology.coordinatePatch 0
    rw [hgval t ht]
    exact affinePoint_mem_patch t (f t)
  have hfcont : ContinuousOn f U := fun t ht => (hf.2 t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g U := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (continuous_affinePoint.comp_continuousOn (continuousOn_id.prodMk hfcont)).congr
      (fun t ht => hgval t ht)
  have hcg (p : Cubic g₂ g₃) (hp : p ∈ finitePatch g₂ g₃)
      (hx : finiteX p.val ∈ U) (hy : finiteY p.val ∈ V) :
      g (finiteX p.val) = p := by
    apply Subtype.ext
    rw [hgval _ hx]
    have hcurve : finiteY p.val ^ 2 = q g₂ g₃ (finiteX p.val) :=
      (affine_equation g₂ g₃ p.val hp).mp p.property
    have hyf := (hgraph _ hx _ hy).mp hcurve
    rw [← hyf]
    exact affinePoint_coordinates hp
  let e := chartOfParametrization
    (fun p : Cubic g₂ g₃ => finiteX p.val) (fun p => finiteY p.val)
    (finitePatch g₂ g₃) U V g (finitePatch_isOpen g₂ g₃) hU hV
    (continuousOn_finiteX_cubic g₂ g₃) (continuousOn_finiteY_cubic g₂ g₃)
    hgcont hgc hgd hgs hcg
  have he : IsFiniteChart g₂ g₃ true e := by
    refine ⟨fun p hp => hp.1, fun p hp => rfl, ?_, ?_⟩
    · exact holo_congr ⟨hU, fun z hz => differentiableAt_id⟩ hgc
    · exact holo_congr hf hgy
  exact ⟨U, V, f, e, hU, haU, hV, hbV, hf, hfa, hmap, hgraph,
    he, rfl, rfl, hgval⟩


theorem y_chart : Specs.D12Complex.Ch22.CubicFiniteCharts.y_chart_type := by
  classical
  intro g₂ g₃ a ha hqa
  obtain ⟨U, V, f, hU, hV, hU0, haV, hf, hfa, hmap, hgraph⟩ :=
    y_graph g₂ g₃ a ha hqa
  have hpoint (t : ℂ) (ht : t ∈ U) : OnCubic g₂ g₃ (affinePoint (f t) t) :=
    (onCubic_affinePoint_iff g₂ g₃ (f t) t).mpr ((hgraph t ht (f t) (hmap ht)).mpr rfl)
  let center : Cubic g₂ g₃ := ⟨affinePoint a 0,
    (onCubic_affinePoint_iff g₂ g₃ a 0).mpr (by simpa using ha.symm)⟩
  let g : ℂ → Cubic g₂ g₃ := fun t => if ht : t ∈ U then
    ⟨affinePoint (f t) t, hpoint t ht⟩ else center
  have hgval (t : ℂ) (ht : t ∈ U) : (g t).val = affinePoint (f t) t := by
    simp [g, ht]
  have hgc (t : ℂ) (ht : t ∈ U) : finiteY (g t).val = t := by
    rw [hgval t ht, finiteY_affinePoint]
  have hgx (t : ℂ) (ht : t ∈ U) : finiteX (g t).val = f t := by
    rw [hgval t ht, finiteX_affinePoint]
  have hgd (t : ℂ) (ht : t ∈ U) : finiteX (g t).val ∈ V := by
    rw [hgx t ht]
    exact hmap ht
  have hgs : MapsTo g U (finitePatch g₂ g₃) := by
    intro t ht
    change (g t).val ∈ ProjectivePlaneTopology.coordinatePatch 0
    rw [hgval t ht]
    exact affinePoint_mem_patch (f t) t
  have hfcont : ContinuousOn f U := fun t ht => (hf.2 t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g U := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (continuous_affinePoint.comp_continuousOn (hfcont.prodMk continuousOn_id)).congr
      (fun t ht => hgval t ht)
  have hcg (p : Cubic g₂ g₃) (hp : p ∈ finitePatch g₂ g₃)
      (hy : finiteY p.val ∈ U) (hx : finiteX p.val ∈ V) :
      g (finiteY p.val) = p := by
    apply Subtype.ext
    rw [hgval _ hy]
    have hcurve : finiteY p.val ^ 2 = q g₂ g₃ (finiteX p.val) :=
      (affine_equation g₂ g₃ p.val hp).mp p.property
    have hxf := (hgraph _ hy _ hx).mp hcurve
    rw [← hxf]
    exact affinePoint_coordinates hp
  let e := chartOfParametrization
    (fun p : Cubic g₂ g₃ => finiteY p.val) (fun p => finiteX p.val)
    (finitePatch g₂ g₃) U V g (finitePatch_isOpen g₂ g₃) hU hV
    (continuousOn_finiteY_cubic g₂ g₃) (continuousOn_finiteX_cubic g₂ g₃)
    hgcont hgc hgd hgs hcg
  have he : IsFiniteChart g₂ g₃ false e := by
    refine ⟨fun p hp => hp.1, fun p hp => rfl, ?_, ?_⟩
    · exact holo_congr hf hgx
    · exact holo_congr ⟨hU, fun z hz => differentiableAt_id⟩ hgc
  exact ⟨U, V, f, e, hU, hU0, hV, haV, hf, hfa, hmap, hgraph,
    he, rfl, rfl, hgval⟩



theorem finite_charts : Specs.D12Complex.Ch22.CubicFiniteCharts.finite_charts_type := by
  intro ω₁ ω₂ h₁ h₂ p hp
  have hcurve : finiteY p.val ^ 2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (finiteX p.val) :=
    (affine_equation _ _ p.val hp).mp p.property
  by_cases hy : finiteY p.val = 0
  · have hq : q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (finiteX p.val) = 0 := by
      simpa [hy] using hcurve.symm
    have hd := cubic_derivative_ne_zero (HalfPeriodValues.discriminant ω₁ ω₂ h₁ h₂) hq
    obtain ⟨U, V, f, e, hU, hU0, hV, hxV, hf, hfa, hmap, hgraph, he, ht, hs, hi⟩ :=
      y_chart _ _ (finiteX p.val) hq hd
    refine ⟨e, ?_, by simpa only [hy, ↓reduceIte] using he⟩
    rw [hs]
    exact ⟨hp, by simpa only [hy] using hU0, hxV⟩
  · obtain ⟨U, V, f, e, hU, hxU, hV, hyV, hf, hfa, hmap, hgraph, he, ht, hs, hi⟩ :=
      x_chart _ _ (finiteX p.val) (finiteY p.val) hcurve hy
    refine ⟨e, ?_, by simpa only [hy, ↓reduceIte] using he⟩
    rw [hs]
    exact ⟨hp, hxU, hyV⟩

end D12Complex.CubicFiniteCharts

namespace D12Complex.CubicFiniteCharts.Definitions
abbrev homogeneousEquation : Specs.D12Complex.Ch22.CubicFiniteCharts.homogeneousEquation_type :=
  D12Complex.CubicFiniteCharts.homogeneousEquation
abbrev OnCubic : Specs.D12Complex.Ch22.CubicFiniteCharts.OnCubic_type :=
  D12Complex.CubicFiniteCharts.OnCubic
abbrev Cubic : Specs.D12Complex.Ch22.CubicFiniteCharts.Cubic_type :=
  D12Complex.CubicFiniteCharts.Cubic
abbrev q : Specs.D12Complex.Ch22.CubicFiniteCharts.q_type :=
  D12Complex.CubicFiniteCharts.q
abbrev finiteX : Specs.D12Complex.Ch22.CubicFiniteCharts.finiteX_type :=
  D12Complex.CubicFiniteCharts.finiteX
abbrev finiteY : Specs.D12Complex.Ch22.CubicFiniteCharts.finiteY_type :=
  D12Complex.CubicFiniteCharts.finiteY
abbrev affinePoint : Specs.D12Complex.Ch22.CubicFiniteCharts.affinePoint_type :=
  D12Complex.CubicFiniteCharts.affinePoint
abbrev finitePatch : Specs.D12Complex.Ch22.CubicFiniteCharts.finitePatch_type :=
  D12Complex.CubicFiniteCharts.finitePatch
abbrev coordinate : Specs.D12Complex.Ch22.CubicFiniteCharts.coordinate_type :=
  D12Complex.CubicFiniteCharts.coordinate
abbrev IsFiniteChart : Specs.D12Complex.Ch22.CubicFiniteCharts.IsFiniteChart_type :=
  D12Complex.CubicFiniteCharts.IsFiniteChart
end D12Complex.CubicFiniteCharts.Definitions
