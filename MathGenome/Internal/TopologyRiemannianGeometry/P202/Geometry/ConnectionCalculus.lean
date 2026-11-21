import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PullbackConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurveCovariantDerivative

/-! Local connection calculus, pullbacks and C¹ covariant differentiation.
This assembles paper.tex 3017--3054 on the canonical shared bundle objects. -/
set_option autoImplicit false
namespace P202.Geometry.ConnectionCalculus
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData
open Set Filter
open scoped Topology
universe u v w

abbrev Connection := @P202.ConnectionData.Connection
abbrev frameMember := @P202.ConnectionData.frameMember
noncomputable abbrev frameCoefficient := @P202.ConnectionData.frameCoefficient
noncomputable abbrev frameMatrix := @P202.ConnectionData.frameMatrix
noncomputable abbrev frameTransition := @P202.ConnectionData.frameTransition
noncomputable abbrev frameTransitionDerivative := @P202.ConnectionData.frameTransitionDerivative

section Sections
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

@[simp] theorem mulSection_apply (f : GlobalSmooth S) (s : Section B) (p : M) :
    (mulSection f s).val p = f.val p • s.val p := rfl

@[simp] theorem section_add_apply (s t : Section B) (p : M) :
    (s + t).val p = s.val p + t.val p := rfl

@[simp] theorem section_zero_apply (p : M) : (0 : Section B).val p = 0 := rfl

@[simp] theorem section_smul_apply (c : ℝ) (s : Section B) (p : M) :
    (c • s).val p = c • s.val p := rfl

@[ext] theorem section_ext {s t : Section B} (h : ∀ p, s.val p = t.val p) : s = t :=
  Subtype.ext (funext h)

@[simp] theorem mulSection_one (s : Section B) : mulSection 1 s = s := by
  apply section_ext
  intro p
  exact one_smul ℝ (s.val p)

@[simp] theorem mulSection_zero (s : Section B) : mulSection 0 s = 0 := by
  apply section_ext
  intro p
  exact zero_smul ℝ (s.val p)

@[simp] theorem mulSection_mul (f g : GlobalSmooth S) (s : Section B) :
    mulSection (f * g) s = mulSection f (mulSection g s) := by
  apply section_ext
  intro p
  exact mul_smul (f.val p) (g.val p) (s.val p)

end Sections

section Actions
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- This is equality with the intrinsic germ action, not a coordinate surrogate. -/
@[simp] theorem act_apply (X : Field S) (f : GlobalSmooth S) (p : M) :
    (act S X f).val p = (X.val p).val (SmoothManifolds.globalToGerm S p f) := rfl

/-- The scalar derivative depends only on the germ of the scalar function. -/
theorem act_congr (X : Field S) (f g : GlobalSmooth S) (p : M)
    (h : f.val =ᶠ[𝓝 p] g.val) : (act S X f).val p = (act S X g).val p := by
  have hg : SmoothManifolds.globalToGerm S p f = SmoothManifolds.globalToGerm S p g :=
    Subtype.ext (Germ.coe_eq.mpr h)
  simp only [act_apply, hg]

@[simp] theorem act_one (X : Field S) : act S X 1 = 0 := (act S X).map_one_eq_zero

/-- Smooth cutoffs are constructed, rather than required as connection data. -/
theorem exists_cutoff_near (p : M) (U : Set M) (hU : IsOpen U) (hp : p ∈ U) :
    ∃ f : GlobalSmooth S, f.val =ᶠ[𝓝 p] (fun _ => 1) ∧
      SmoothManifolds.ModelData.sectionSupport f.val ⊆ U := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨χ, hχsmooth, _hχrange, ⟨V, hVo, hVp, hχone⟩, hχsupp⟩ :=
    SmoothManifolds.exists_smooth_cutoff S {p} U isClosed_singleton hU
      (singleton_subset_iff.mpr hp)
  refine ⟨⟨χ, (SmoothManifolds.mem_globalSmoothAlgebra_iff S χ).mpr hχsmooth⟩, ?_, hχsupp⟩
  filter_upwards [hVo.mem_nhds (hVp (mem_singleton p))] with q hq
  exact hχone hq

end Actions

section Connections
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B)

/-- Germ-locality in the section variable follows from Leibniz and a cutoff. -/
theorem locality_section (X : Field S) (s t : Section B) (p : M)
    (h : ∀ᶠ q in 𝓝 p, s.val q = t.val q) :
    (C.cov X s).val p = (C.cov X t).val p := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp h
  obtain ⟨f, hfone, hfsupp⟩ := exists_cutoff_near (S := S) p U hUo hpU
  have hfp : f.val p = 1 := hfone.eq_of_nhds
  have hact : (act S X f).val p = 0 := by
    have he := act_congr X f 1 p hfone
    simpa [act_one] using he
  have hfst : mulSection f s = mulSection f t := by
    apply section_ext
    intro q
    by_cases hq : q ∈ U
    · rw [mulSection_apply, mulSection_apply, hU q hq]
    · have hfq : f.val q = 0 := Function.notMem_support.mp
        (fun hz => hq (hfsupp (subset_closure hz)))
      simp only [mulSection_apply, hfq, zero_smul]
  have he := congrArg (fun z : Section B => z.val p) (congrArg (C.cov X) hfst)
  rw [C.leibniz, C.leibniz] at he
  simpa only [section_add_apply, mulSection_apply, hfp, hact, zero_smul,
    one_smul, zero_add] using he

/-- Germ-locality in the vector-field variable follows from C∞-linearity. -/
theorem locality_field (X Y : Field S) (s : Section B) (p : M)
    (h : ∀ᶠ q in 𝓝 p, X.val q = Y.val q) :
    (C.cov X s).val p = (C.cov Y s).val p := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp h
  obtain ⟨f, hfone, hfsupp⟩ := exists_cutoff_near (S := S) p U hUo hpU
  have hfp : f.val p = 1 := hfone.eq_of_nhds
  have hXY : mulSection f X = mulSection f Y := by
    apply section_ext
    intro q
    by_cases hq : q ∈ U
    · rw [mulSection_apply, mulSection_apply, hU q hq]
    · have hfq : f.val q = 0 := Function.notMem_support.mp
        (fun hz => hq (hfsupp (subset_closure hz)))
      simp only [mulSection_apply, hfq, zero_smul]
  have he := congrArg (fun z : Field S => (C.cov z s).val p) hXY
  simp only [C.linear_field, mulSection_apply, hfp, one_smul] at he
  exact he

/-- Applying Leibniz to a finite frame expansion; the empty frame is allowed. -/
theorem finite_expansion (X : Field S) (k : ℕ)
    (f : Fin k → GlobalSmooth S) (e : Fin k → Section B) :
    C.cov X (∑ j, mulSection (f j) (e j)) =
      ∑ j, (mulSection (act S X (f j)) (e j) + mulSection (f j) (C.cov X (e j))) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => C.leibniz X (f j) (e j))

section Frame
variable (b : LocalFrame B Set.univ isOpen_univ)

@[simp] theorem frameMember_apply (j : Fin r) (p : M) :
    (frameMember b j).val p = b.section_ j ⟨p, Set.mem_univ p⟩ := rfl

@[simp] theorem frameCoefficient_apply (s : Section B) (j : Fin r) (p : M) :
    (frameCoefficient b s j).val p =
      (b.basis ⟨p, Set.mem_univ p⟩).equivFun (s.val p) j := rfl

/-- Exact frame expansion in the smooth section space, including rank zero. -/
theorem frame_expansion (s : Section B) :
    s = ∑ j, mulSection (frameCoefficient b s j) (frameMember b j) := by
  apply section_ext
  intro p
  simp only [Submodule.coe_sum, Finset.sum_apply, mulSection_apply,
    frameCoefficient_apply, frameMember_apply]
  exact SmoothManifolds.Frames.section_expansion B Set.univ isOpen_univ b
    (fun q => s.val q.val) ⟨p, Set.mem_univ p⟩

/-- Evaluation of the connection in a global frame. The arbitrary-open-domain version is local_frame_formula below. -/
theorem global_frame_formula (X : Field S) (s : Section B) (p : M) (i : Fin r) :
    (frameCoefficient b (C.cov X s) i).val p =
      (act S X (frameCoefficient b s i)).val p +
        ∑ j, frameMatrix C b X p i j * (frameCoefficient b s j).val p := by
  have h := congrArg (fun t : Section B =>
    (b.basis ⟨p, Set.mem_univ p⟩).equivFun (t.val p) i)
      (finite_expansion B C X r (frameCoefficient b s) (frameMember b))
  rw [← frame_expansion B b s] at h
  simp only [Submodule.coe_sum, Finset.sum_apply, section_add_apply, mulSection_apply,
    map_sum, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [frameCoefficient_apply]
  rw [h]
  simp only [Finset.sum_add_distrib]
  congr 1
  · simp only [frameMember_apply, ← b.basis_eq, Module.Basis.equivFun_self]
    simp
  · apply Finset.sum_congr rfl
    intro j _
    change (frameCoefficient b s j).val p *
      (frameCoefficient b (C.cov X (frameMember b j)) i).val p = _
    exact mul_comm _ _

end Frame

section Transition
variable (b c : LocalFrame B Set.univ isOpen_univ)

/-- Coordinates transform by the genuine frame transition. -/
theorem coefficient_change (s : Section B) (p : M) (i : Fin r) :
    (frameCoefficient b s i).val p =
      ∑ j, frameTransition b c p i j * (frameCoefficient c s j).val p := by
  have h := congrArg (fun t : Section B =>
    (b.basis ⟨p, Set.mem_univ p⟩).equivFun (t.val p) i)
      (frame_expansion B c s)
  rw [frameCoefficient_apply]
  rw [h]
  simp only [Submodule.coe_sum, Finset.sum_apply, mulSection_apply, map_sum,
    map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (frameCoefficient c s j).val p *
    (frameCoefficient b (frameMember c j) i).val p = _
  exact mul_comm _ _

theorem transition_inverse (p : M) :
    frameTransition b c p * frameTransition c b p = 1 ∧
      frameTransition c b p * frameTransition b c p = 1 := by
  have h (b c : LocalFrame B Set.univ isOpen_univ) :
      frameTransition b c p * frameTransition c b p = 1 := by
    ext i j
    have he := coefficient_change B b c (frameMember b j) p i
    change _ = (∑ k, frameTransition b c p i k * frameTransition c b p k j) at he
    rw [Matrix.mul_apply, ← he]
    simp only [frameCoefficient_apply, frameMember_apply, ← b.basis_eq,
      Module.Basis.equivFun_self]
    simp [Matrix.one_apply, eq_comm]
  exact ⟨h b c, h c b⟩

/-- Before left multiplication by the inverse transition, the product rule
reads A Γ' = Γ A + dA, with all entries constructed from this connection. -/
theorem frame_transformation_product (X : Field S) (p : M) :
    frameTransition b c p * frameMatrix C c X p =
      frameMatrix C b X p * frameTransition b c p +
        frameTransitionDerivative X b c p := by
  ext i j
  have he := coefficient_change B b c (C.cov X (frameMember c j)) p i
  have hf := global_frame_formula B C b X (frameMember c j) p i
  change _ = ∑ k, frameTransition b c p i k * frameMatrix C c X p k j at he
  rw [Matrix.mul_apply, ← he, hf]
  change _ = (∑ k, frameMatrix C b X p i k * frameTransition b c p k j) + _
  exact add_comm _ _

/-- The usual row-frame gauge law, for global frames; it makes no metric
assumption and uses the proved inverse relation between the two transitions. -/
theorem global_frame_transformation (X : Field S) (p : M) :
    frameMatrix C c X p =
      frameTransition c b p * frameMatrix C b X p * frameTransition b c p +
        frameTransition c b p * frameTransitionDerivative X b c p := by
  have h := congrArg (fun Z => frameTransition c b p * Z)
    (frame_transformation_product B C b c X p)
  simpa only [← Matrix.mul_assoc, (transition_inverse B b c p).2,
    Matrix.one_mul, Matrix.mul_add] using h

end Transition

end Connections

noncomputable abbrev Section := @P202.ConnectionData.Section

noncomputable abbrev mulSection := @P202.ConnectionData.mulSection

noncomputable abbrev LocalSection := @P202.ConnectionData.LocalSection

noncomputable abbrev covOn := @P202.ConnectionData.covOn

noncomputable abbrev pointDerivative := @P202.ConnectionData.pointDerivative

noncomputable abbrev connectionForm := @P202.ConnectionData.connectionForm

noncomputable abbrev connectionMatrix := @P202.ConnectionData.connectionMatrix

noncomputable abbrev localTransition := @P202.ConnectionData.localTransition

noncomputable abbrev localTransitionDerivative := @P202.ConnectionData.localTransitionDerivative

noncomputable abbrev frameSection := @P202.ConnectionData.frameSection

noncomputable abbrev restrictFrame := @P202.ConnectionData.restrictFrame

noncomputable abbrev restrictLocalSection := @P202.ConnectionData.restrictLocalSection

noncomputable abbrev restrictGlobalSection := @P202.ConnectionData.restrictGlobalSection

noncomputable abbrev Field := @P202.ConnectionData.Field

noncomputable abbrev act := @P202.ConnectionData.act

noncomputable abbrev scalarDerivative := @P202.ConnectionData.scalarDerivative

noncomputable abbrev pullbackBundle := @P202.PullbackData.bundle

noncomputable abbrev coefficientsAlong := @P202.CurveConnectionData.coefficientsAlong

noncomputable abbrev frameFieldAlong := @P202.CurveConnectionData.frameFieldAlong

noncomputable abbrev frameDerivative := @P202.CurveConnectionData.frameDerivative

noncomputable abbrev C1FieldOn := @P202.CurveConnectionData.C1FieldOn

noncomputable abbrev HasCovariantDerivativeWithinAt := @P202.CurveConnectionData.HasCovariantDerivativeWithinAt

noncomputable abbrev covariantDerivativeWithin := @P202.CurveConnectionData.covariantDerivativeWithin

noncomputable abbrev HasCovariantDerivativeAt := @P202.CurveConnectionData.HasCovariantDerivativeAt

noncomputable abbrev covariantDerivative := @P202.CurveConnectionData.covariantDerivative

noncomputable abbrev HasVelocityWithinAt := @P202.CurveConnectionData.HasVelocityWithinAt

theorem pointwise_field : P202Specs.Geometry.ConnectionCalculus.pointwise_fieldType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.pointwise_field

theorem covOn_smooth : P202Specs.Geometry.ConnectionCalculus.covOn_smoothType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.covOn_smooth

theorem covOn_global : P202Specs.Geometry.ConnectionCalculus.covOn_globalType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.covOn_global

theorem covOn_restriction : P202Specs.Geometry.ConnectionCalculus.covOn_restrictionType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.covOn_restriction

theorem pointDerivative_global : P202Specs.Geometry.ConnectionCalculus.pointDerivative_globalType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.pointDerivative_global

theorem covOn_pointDerivative : P202Specs.Geometry.ConnectionCalculus.covOn_pointDerivativeType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.covOn_pointDerivative

theorem connectionForm_smooth : P202Specs.Geometry.ConnectionCalculus.connectionForm_smoothType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.connectionForm_smooth

theorem connectionForm_characterization : P202Specs.Geometry.ConnectionCalculus.connectionForm_characterizationType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.connectionForm_characterization

theorem connectionForm_restriction : P202Specs.Geometry.ConnectionCalculus.connectionForm_restrictionType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.connectionForm_restriction

theorem local_frame_formula : P202Specs.Geometry.ConnectionCalculus.local_frame_formulaType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.local_frame_formula

theorem local_frame_formula_coefficients : P202Specs.Geometry.ConnectionCalculus.local_frame_formula_coefficientsType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.local_frame_formula_coefficients

theorem local_transition_inverse : P202Specs.Geometry.ConnectionCalculus.local_transition_inverseType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.local_transition_inverse

theorem localTransition_smooth : P202Specs.Geometry.ConnectionCalculus.localTransition_smoothType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.localTransition_smooth

theorem local_frame_transformation : P202Specs.Geometry.ConnectionCalculus.local_frame_transformationType.{u,v,w} :=
  @P202.Geometry.ConnectionForms.local_frame_transformation

theorem pullback_exists_unique : P202Specs.Geometry.ConnectionCalculus.pullback_exists_uniqueType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.pullback_exists_unique

theorem canonical_pullback_exists_unique : P202Specs.Geometry.ConnectionCalculus.canonical_pullback_exists_uniqueType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.canonical_pullback_exists_unique

theorem pullback_unique : P202Specs.Geometry.ConnectionCalculus.pullback_uniqueType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.pullback_unique

theorem pullback_frame_exists : P202Specs.Geometry.ConnectionCalculus.pullback_frame_existsType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.pullback_frame_exists

theorem pullback_frame_change : P202Specs.Geometry.ConnectionCalculus.pullback_frame_changeType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.pullback_frame_change

theorem pullback_local_formulas_agree : P202Specs.Geometry.ConnectionCalculus.pullback_local_formulas_agreeType.{u,v,w} :=
  @P202.Geometry.PullbackConnections.pullback_local_formulas_agree

theorem frameDerivative_independent : P202Specs.Geometry.ConnectionCalculus.frameDerivative_independentType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.frameDerivative_independent

theorem covariantDerivative_unique : P202Specs.Geometry.ConnectionCalculus.covariantDerivative_uniqueType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivative_unique

theorem exists_coefficients_deriv : P202Specs.Geometry.ConnectionCalculus.exists_coefficients_derivType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.exists_coefficients_deriv

theorem local_formula : P202Specs.Geometry.ConnectionCalculus.local_formulaType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.local_formula

theorem exists_covariantDerivative : P202Specs.Geometry.ConnectionCalculus.exists_covariantDerivativeType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.exists_covariantDerivative

theorem covariantDerivativeWithin_spec : P202Specs.Geometry.ConnectionCalculus.covariantDerivativeWithin_specType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_spec

theorem covariantDerivativeWithin_eq : P202Specs.Geometry.ConnectionCalculus.covariantDerivativeWithin_eqType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_eq

theorem segment_derivative : P202Specs.Geometry.ConnectionCalculus.segment_derivativeType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.segment_derivative

theorem derivative_add : P202Specs.Geometry.ConnectionCalculus.derivative_addType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_add

theorem derivative_smul : P202Specs.Geometry.ConnectionCalculus.derivative_smulType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_smul

theorem derivative_reparam : P202Specs.Geometry.ConnectionCalculus.derivative_reparamType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_reparam

theorem covariantDerivativeWithin_reparam : P202Specs.Geometry.ConnectionCalculus.covariantDerivativeWithin_reparamType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_reparam

theorem ordinary_reparam : P202Specs.Geometry.ConnectionCalculus.ordinary_reparamType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.ordinary_reparam

theorem derivative_section : P202Specs.Geometry.ConnectionCalculus.derivative_sectionType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_section

theorem derivative_section_field : P202Specs.Geometry.ConnectionCalculus.derivative_section_fieldType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_section_field

theorem derivative_frame_expansion : P202Specs.Geometry.ConnectionCalculus.derivative_frame_expansionType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.derivative_frame_expansion

theorem covariantDerivativeWithin_add : P202Specs.Geometry.ConnectionCalculus.covariantDerivativeWithin_addType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_add

theorem covariantDerivativeWithin_smul : P202Specs.Geometry.ConnectionCalculus.covariantDerivativeWithin_smulType.{u,v,w} :=
  @P202.Geometry.CurveCovariantDerivative.covariantDerivativeWithin_smul


section FiberFormulas
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E) (C : Connection B)

/-- Equality in E_p, rather than only equality of frame coefficients. -/
theorem local_frame_synthesis {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (s : LocalSection B U hU) (p : U) (v : TangentSpace S p.val) :
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v =
      (b.basis p).equivFun.symm (fun i =>
        scalarDerivative S (SmoothManifolds.FrameData.totalize
          (fun q : U => SmoothManifolds.FrameData.coefficients b s.val q i)) p.val v +
        (connectionMatrix C b p v).mulVec
          (SmoothManifolds.FrameData.coefficients b s.val p) i) := by
  apply (b.basis p).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact ConnectionForms.local_frame_formula B C b s p v i

/-- The actual derivative field of e(γ(t))v(t) is e(v' + Γ(γ')v). -/
theorem curve_frame_formula {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {f : ℝ → Euclidean r} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {f' : Euclidean r} (hf : HasDerivWithinAt f f' J t) :
    covariantDerivativeWithin C c (frameFieldAlong b c f) J t =
      (b.basis ⟨c t, hp⟩).equivFun.symm
        (f' + (connectionMatrix C b ⟨c t, hp⟩ V).mulVec (f t)) :=
  CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ
    (CurveCovariantDerivative.derivative_frame_expansion C b ht hp hV hf)

/-- The C¹ construction extends the connection's differentiation of sections. -/
theorem curve_derivative_section (s : Section B) {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V) :
    covariantDerivativeWithin C c (fun z => s.val (c z)) J t =
      pointDerivative C s.val (c t) V :=
  CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ
    (CurveCovariantDerivative.derivative_section C s ht hV)

/-- No sign or nonvanishing hypothesis is needed on the parameter derivative. -/
theorem ordinary_derivative_reparam
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ} {s k : ℝ}
    {D : E (c (φ s))} (hD : HasCovariantDerivativeAt C c f (φ s) D)
    (hφ : HasDerivAt φ k s) :
    covariantDerivative C (c ∘ φ) (fun z => f (φ z)) s =
      k • covariantDerivative C c f (φ s) :=
  CurveCovariantDerivative.covariantDerivativeWithin_reparam C
    (Set.mem_univ s) (uniqueDiffWithinAt_univ) (Set.mem_univ (φ s))
    (uniqueDiffWithinAt_univ) hD hφ.hasDerivWithinAt (Set.mapsTo_univ _ _)

end FiberFormulas

theorem ordinary_velocity_iff : P202Specs.Geometry.ConnectionCalculus.ordinary_velocity_iffType.{u} :=
  @CurveCovariantDerivative.ordinary_velocity_iff

end P202.Geometry.ConnectionCalculus
