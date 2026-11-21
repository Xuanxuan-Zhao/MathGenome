import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionForms

/-! General connections, localization, intrinsic section derivatives and smooth
connection one-forms. This implements the ConnectionForms part of paper.tex
3017--3045; pullback and curve constructions are assigned to separate goals. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.ConnectionForms
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.MapData
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

noncomputable abbrev Section := @P202.ConnectionData.Section

noncomputable abbrev sectionModule := @P202.ConnectionData.sectionModule

noncomputable abbrev mulSection := @P202.ConnectionData.mulSection

noncomputable abbrev Field := @P202.ConnectionData.Field

noncomputable abbrev originalField := @P202.ConnectionData.originalField

noncomputable abbrev act := @P202.ConnectionData.act

noncomputable abbrev scalarDerivative := @P202.ConnectionData.scalarDerivative

noncomputable abbrev LocalSection := @P202.ConnectionData.LocalSection

noncomputable abbrev localCov := @P202.ConnectionData.localCov

noncomputable abbrev covOn := @P202.ConnectionData.covOn

noncomputable abbrev pointDerivative := @P202.ConnectionData.pointDerivative

noncomputable abbrev connectionForm := @P202.ConnectionData.connectionForm

noncomputable abbrev connectionMatrix := @P202.ConnectionData.connectionMatrix

noncomputable abbrev localTransition := @P202.ConnectionData.localTransition

noncomputable abbrev localTransitionDerivative := @P202.ConnectionData.localTransitionDerivative

noncomputable abbrev frameSection := @P202.ConnectionData.frameSection

noncomputable abbrev restrictGlobalSection := @P202.ConnectionData.restrictGlobalSection

noncomputable abbrev restrictLocalSection := @P202.ConnectionData.restrictLocalSection

noncomputable abbrev restrictFrame := @P202.ConnectionData.restrictFrame

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

@[simp] theorem section_neg_apply (s : Section B) (p : M) :
    (-s).val p = -s.val p := rfl

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

/-- The local differential agrees with the action on every global representative. -/
theorem scalarDerivative_representative (f : M → ℝ) (g : GlobalSmooth S)
    (p : M) (h : g.val =ᶠ[𝓝 p] f) (v : TangentSpace S p) :
    scalarDerivative S f p v = v.val (SmoothManifolds.globalToGerm S p g) := by
  classical
  have hg := (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp g.property p
  have hg' : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val g.val p :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp hg
  have hf := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr (hg'.congr h)
  have he : scalarGerm S f p = SmoothManifolds.globalToGerm S p g := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hf]
    exact Germ.coe_eq.mpr h.symm
  unfold scalarDerivative P202.ConnectionData.scalarDerivative
  rw [he]
  rfl

theorem scalarDerivative_global (f : GlobalSmooth S) (X : Field S) (p : M) :
    scalarDerivative S f.val p (X.val p) = (act S X f).val p := by
  rw [scalarDerivative_representative f.val f p Filter.EventuallyEq.rfl, act_apply]

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

section LocalExtension
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Any smooth local section agrees near a point with a global smooth section. -/
theorem exists_section_representative (U : Set M) (hU : IsOpen U)
    (s : (q : M) → E q)
    (hs : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U)
    (p : M) (hp : p ∈ U) :
    ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q := by
  obtain ⟨f, hf, hfsupp⟩ := exists_cutoff_near (S := S) p U hU hp
  refine ⟨⟨fun q => f.val q • s q,
    SmoothManifolds.SectionExtension.weighted_section_smooth B
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp f.property) hs hfsupp⟩, ?_⟩
  filter_upwards [hf] with q hq
  exact hq ▸ one_smul ℝ (s q)

theorem germRepresentative_eq {s : (q : M) → E q} {p : M}
    (h : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) :
    ∀ᶠ q in 𝓝 p, (germRepresentative (B := B) s p).val q = s q := by
  classical
  simpa only [germRepresentative, dite_eq_left h] using Classical.choose_spec h

/-- Smooth coefficients in an arbitrary local frame admit global germ representatives. -/
theorem local_coefficients_representative {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (s : (q : U) → E q.val)
    (hs : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q.val, s q⟩ : Bundle.TotalSpace (Euclidean r) E))) (p : U) :
    ∃ f : Fin r → GlobalSmooth S, ∀ j,
      (f j).val =ᶠ[𝓝 p.val]
        (SmoothManifolds.FrameData.totalize
          (fun q : U => SmoothManifolds.FrameData.coefficients b s q j)) := by
  classical
  have hcoeff := (SmoothManifolds.Frames.smooth_section_iff_coefficients B U hU b s).mp hs
  have he (j : Fin r) : ∃ f : GlobalSmooth S, f.val =ᶠ[𝓝 p.val]
      (SmoothManifolds.FrameData.totalize
        (fun q : U => SmoothManifolds.FrameData.coefficients b s q j)) := by
    have hj := SmoothManifolds.FrameData.VectorSmoothAt.totalize hU (hcoeff j p)
    obtain ⟨f, hf, heq⟩ := SmoothManifolds.exists_global_representative S p.val _
      ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hj)
    exact ⟨⟨f, (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr hf⟩, heq⟩
  choose f hf using he
  exact ⟨f, hf⟩

/-- Local frame sections have simultaneous global germ representatives. -/
theorem local_frame_representative {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (p : U) :
    ∃ e : Fin r → Section B, ∀ j, ∀ᶠ q in 𝓝 p.val,
      (e j).val q = SmoothManifolds.SectionExtension.totalSection (b.section_ j) q := by
  classical
  have he (j : Fin r) := exists_section_representative B U hU
    (SmoothManifolds.SectionExtension.totalSection (b.section_ j))
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ (b.smooth j)) p.val p.property
  choose e he using he
  exact ⟨e, he⟩

/-- The finite local expansion can be realized by global sections and scalars.
In particular coefficients vanish at p when the original section does. -/
theorem section_zero_decomposition (s : Section B) (p : M) (hsp : s.val p = 0) :
    ∃ (f : Fin r → GlobalSmooth S) (e : Fin r → Section B),
      (∀ᶠ q in 𝓝 p, s.val q = (∑ j, mulSection (f j) (e j)).val q) ∧
      ∀ j, (f j).val p = 0 := by
  classical
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B p
  let pU : U := ⟨p, hp⟩
  have hs := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    S.smoothStructure.val B.totalManifold.smoothStructure.val _ U hU).mp
      (fun q _ => s.property q)
  obtain ⟨f, hf⟩ := local_coefficients_representative B b (fun q => s.val q.val) hs pU
  obtain ⟨e, he⟩ := local_frame_representative B b pU
  refine ⟨f, e, ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hp, Filter.eventually_all.mpr hf,
      Filter.eventually_all.mpr he] with q hq hfq heq
    rw [SmoothManifolds.Frames.section_expansion B U hU b (fun z => s.val z.val) ⟨q, hq⟩]
    simp only [Submodule.coe_sum, Finset.sum_apply, mulSection_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfq j, heq j]
    simp only [SmoothManifolds.FrameData.totalize_of_mem _ q hq,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  · intro j
    have hj := (hf j).eq_of_nhds
    simpa [SmoothManifolds.FrameData.totalize_of_mem _ p hp,
      SmoothManifolds.FrameData.coefficients, pU, hsp] using hj

/-- Evaluation of smooth sections onto every fiber is surjective. -/
theorem section_evaluation_surjective (p : M) (v : E p) :
    ∃ s : Section B, s.val p = v := by
  classical
  obtain ⟨U, hU, hp, ⟨b⟩⟩ := SmoothManifolds.ConstantRankBundles.exists_localFrame B p
  let pU : U := ⟨p, hp⟩
  obtain ⟨e, he⟩ := local_frame_representative B b pU
  let c : Fin r → ℝ := (b.basis pU).equivFun v
  refine ⟨∑ j, c j • e j, ?_⟩
  simp only [Submodule.coe_sum, Finset.sum_apply, section_smul_apply]
  have hev (j : Fin r) : (e j).val p = b.basis pU j := by
    have hj := (he j).self_of_nhds
    simpa [SmoothManifolds.SectionExtension.totalSection_of_mem _ p hp, b.basis_eq] using hj
  simp_rw [hev]
  exact (b.basis pU).sum_equivFun v

end LocalExtension

section Covectors
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Smoothness tested on global smooth fields is genuine cotangent-bundle
smoothness, since every local tangent-frame member has a global germ extension. -/
theorem covector_smoothOn_of_evaluations (U : Set M)
    (ω : (p : M) → TangentSpace S p →ₗ[ℝ] ℝ)
    (hω : ∀ X : Field S, ∀ p ∈ U,
      SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
        (fun q => ω q (X.val q)) p) :
    ManifoldSmoothOn S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, ω q⟩ : Bundle.TotalSpace (Euclidean n)
        (fun p => Module.Dual ℝ (TangentSpace S p)))) U := by
  classical
  intro p hp
  let T := tangentBundle S
  obtain ⟨i, hi⟩ := T.covers p
  let V := T.baseSet i
  have hV : IsOpen V := by
    change IsOpen (T.baseSet i)
    rw [← T.trivialization_baseSet i]
    exact (T.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame T i
  obtain ⟨e, he⟩ := local_frame_representative T b ⟨p, hi⟩
  apply SmoothManifolds.SectionExtension.smoothAt_of_coordinates (cotangentBundle S) i
    (by rw [(cotangentDual S).baseSet i]; exact hi)
  apply SmoothManifolds.FrameData.VectorSmoothAt.pi
  intro j
  apply (hω (e j) p hp).congr
  filter_upwards [hV.mem_nhds hi, he j] with q hq heq
  rw [(cotangentDual S).coordinates i q hq (ω q) j]
  rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  congr 1
  change ((Pi.basisFun ℝ (Fin n)).map (T.fiberCoordinates i q hq).symm) j = _
  simp only [Module.Basis.map_apply, Pi.basisFun_apply,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  rfl

end Covectors

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

/-- C∞-linearity and a finite local tangent-frame expansion imply tensoriality. -/
theorem cov_field_eq_zero (X : Field S) (s : Section B) (p : M)
    (hX : X.val p = 0) : (C.cov X s).val p = 0 := by
  obtain ⟨f, e, heq, hf⟩ := section_zero_decomposition (tangentBundle S) X p hX
  rw [locality_field B C X (∑ j, mulSection (f j) (e j)) s p heq]
  simp only [map_sum, LinearMap.sum_apply, C.linear_field, Submodule.coe_sum,
    Finset.sum_apply, mulSection_apply, hf, zero_smul, Finset.sum_const_zero]

/-- At p the field argument depends only on its actual tangent value. -/
theorem pointwise_field (X Y : Field S) (s : Section B) (p : M)
    (hXY : X.val p = Y.val p) : (C.cov X s).val p = (C.cov Y s).val p := by
  have hz := cov_field_eq_zero B C (X + (-1 : ℝ) • Y) s p (by
    simp only [section_add_apply, section_smul_apply, neg_one_smul, hXY, add_neg_cancel])
  simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    section_add_apply, section_smul_apply, neg_one_smul, section_neg_apply, add_neg_eq_zero] using hz

/-- The restricted operator agrees with any global representatives. -/
theorem localCov_eq (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (p : M) (Y : Field S) (t : Section B)
    (hX : ∀ᶠ q in 𝓝 p, Y.val q = X q)
    (hs : ∀ᶠ q in 𝓝 p, t.val q = s q) :
    localCov C X s p = (C.cov Y t).val p := by
  unfold localCov P202.ConnectionData.localCov
  rw [locality_field B C _ Y _ p
    (by
      filter_upwards [germRepresentative_eq (tangentBundle S) ⟨Y, hX⟩, hX] with q hq hq'
      exact hq.trans hq'.symm)]
  exact locality_section B C Y _ t p
    (by
      filter_upwards [germRepresentative_eq B ⟨t, hs⟩, hs] with q hq hq'
      exact hq.trans hq'.symm)

theorem localCov_global (X : Field S) (s : Section B) (p : M) :
    localCov C X.val s.val p = (C.cov X s).val p :=
  localCov_eq B C _ _ p X s (Eventually.of_forall (fun _ => rfl)) (Eventually.of_forall (fun _ => rfl))

/-- Germ locality of the restricted connection in both arguments. -/
theorem localCov_congr (X Y : (q : M) → TangentSpace S q) (s t : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hXY : ∀ᶠ q in 𝓝 p, X q = Y q) (hst : ∀ᶠ q in 𝓝 p, s q = t q) :
    localCov C X s p = localCov C Y t p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨u, hu⟩ := hs
  have hZY : ∀ᶠ q in 𝓝 p, Z.val q = Y q := by
    filter_upwards [hZ, hXY] with q hq hq'
    exact hq.trans hq'
  have hut : ∀ᶠ q in 𝓝 p, u.val q = t q := by
    filter_upwards [hu, hst] with q hq hq'
    exact hq.trans hq'
  rw [localCov_eq B C _ _ p Z u hZ hu, localCov_eq B C _ _ p Z u hZY hut]

theorem localCov_add_field (X Y : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hY : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = Y q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q) :
    localCov C (fun q => X q + Y q) s p = localCov C X s p + localCov C Y s p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨W, hW⟩ := hY
  obtain ⟨u, hu⟩ := hs
  have hZW : ∀ᶠ q in 𝓝 p, (Z + W).val q = X q + Y q := by
    filter_upwards [hZ, hW] with q hq hq'
    simp only [section_add_apply, hq, hq']
  rw [localCov_eq B C _ _ p (Z + W) u hZW hu,
    localCov_eq B C _ _ p Z u hZ hu, localCov_eq B C _ _ p W u hW hu]
  simp only [map_add, LinearMap.add_apply, section_add_apply]

theorem localCov_add_section (X : (q : M) → TangentSpace S q) (s t : (q : M) → E q)
    (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (ht : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = t q) :
    localCov C X (fun q => s q + t q) p = localCov C X s p + localCov C X t p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := ht
  have huv : ∀ᶠ q in 𝓝 p, (u + v).val q = s q + t q := by
    filter_upwards [hu, hv] with q hq hq'
    simp only [section_add_apply, hq, hq']
  rw [localCov_eq B C _ _ p Z (u + v) hZ huv,
    localCov_eq B C _ _ p Z u hZ hu, localCov_eq B C _ _ p Z v hZ hv]
  simp only [map_add, section_add_apply]

theorem localCov_smul_section (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (c : ℝ) (p : M) (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q) :
    localCov C X (fun q => c • s q) p = c • localCov C X s p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨u, hu⟩ := hs
  have hcu : ∀ᶠ q in 𝓝 p, (c • u).val q = c • s q := by
    filter_upwards [hu] with q hq
    simp only [section_smul_apply, hq]
  rw [localCov_eq B C _ _ p Z (c • u) hZ hcu,
    localCov_eq B C _ _ p Z u hZ hu]
  simp only [map_smul, section_smul_apply]

/-- C∞-linearity survives restriction to arbitrary smooth germs. -/
theorem localCov_mul_field (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (f : M → ℝ) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hf : ∃ g : GlobalSmooth S, g.val =ᶠ[𝓝 p] f) :
    localCov C (fun q => f q • X q) s p = f p • localCov C X s p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨u, hu⟩ := hs
  obtain ⟨g, hg⟩ := hf
  have hgZ : ∀ᶠ q in 𝓝 p, (mulSection g Z).val q = f q • X q := by
    filter_upwards [hg, hZ] with q hq hq'
    simp only [mulSection_apply, hq, hq']
  rw [localCov_eq B C _ _ p (mulSection g Z) u hgZ hu,
    localCov_eq B C _ _ p Z u hZ hu, C.linear_field, mulSection_apply, hg.eq_of_nhds]

/-- The full scalar Leibniz rule survives restriction. -/
theorem localCov_leibniz (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (f : M → ℝ) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hf : ∃ g : GlobalSmooth S, g.val =ᶠ[𝓝 p] f) :
    localCov C X (fun q => f q • s q) p =
      scalarDerivative S f p (X p) • s p + f p • localCov C X s p := by
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨u, hu⟩ := hs
  obtain ⟨g, hg⟩ := hf
  have hgu : ∀ᶠ q in 𝓝 p, (mulSection g u).val q = f q • s q := by
    filter_upwards [hg, hu] with q hq hq'
    simp only [mulSection_apply, hq, hq']
  rw [localCov_eq B C _ _ p Z (mulSection g u) hZ hgu,
    localCov_eq B C _ _ p Z u hZ hu, C.leibniz, section_add_apply,
    mulSection_apply, mulSection_apply, hg.eq_of_nhds, hu.self_of_nhds,
    scalarDerivative_representative f g p hg, ← hZ.self_of_nhds, act_apply]

/-- Every smooth section germ has a unique linear derivative on T_p M. -/
theorem exists_pointDerivative (s : (q : M) → E q) (p : M)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) :
    ∃! D : TangentSpace S p →ₗ[ℝ] E p,
      ∀ X : Field S, D (X.val p) = localCov C X.val s p := by
  classical
  obtain ⟨t, ht⟩ := hs
  choose lift hlift using section_evaluation_surjective (tangentBundle S) p
  let D : TangentSpace S p →ₗ[ℝ] E p := {
    toFun := fun v => (C.cov (lift v) t).val p
    map_add' := by
      intro v w
      have h := pointwise_field B C (lift (v + w)) (lift v + lift w) t p (by
        simp only [hlift, section_add_apply])
      simpa only [map_add, LinearMap.add_apply, section_add_apply] using h
    map_smul' := by
      intro c v
      have h := pointwise_field B C (lift (c • v)) (c • lift v) t p (by
        simp only [hlift, section_smul_apply])
      simpa only [map_smul, LinearMap.smul_apply, section_smul_apply, RingHom.id_apply] using h }
  have hD (X : Field S) : D (X.val p) = localCov C X.val s p := by
    rw [localCov_eq B C _ _ p X t (Eventually.of_forall (fun _ => rfl)) ht]
    exact pointwise_field B C _ X t p (hlift _)
  refine ⟨D, hD, ?_⟩
  intro D' hD'
  ext v
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, hD' X, hD X]

theorem pointDerivative_apply (s : (q : M) → E q) (p : M)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) (X : Field S) :
    pointDerivative C s p (X.val p) = localCov C X.val s p := by
  classical
  have he := (exists_pointDerivative B C s p hs).exists
  simpa only [pointDerivative, P202.ConnectionData.pointDerivative, dite_eq_left he] using Classical.choose_spec he X

/-- The intrinsic derivative agrees with the original connection operator. -/
theorem pointDerivative_global (s : Section B) (p : M) (X : Field S) :
    pointDerivative C s.val p (X.val p) = (C.cov X s).val p := by
  rw [pointDerivative_apply B C _ p ⟨s, Eventually.of_forall (fun _ => rfl)⟩,
    localCov_global B C]

/-- Germ dependence of the section variable, now as an actual tangent-linear map. -/
theorem pointDerivative_congr (s t : (q : M) → E q) (p : M)
    (hs : ∃ u : Section B, ∀ᶠ q in 𝓝 p, u.val q = s q)
    (hst : ∀ᶠ q in 𝓝 p, s q = t q) : pointDerivative C s p = pointDerivative C t p := by
  obtain ⟨u, hu⟩ := hs
  have hut : ∀ᶠ q in 𝓝 p, u.val q = t q := by
    filter_upwards [hu, hst] with q hq hq'
    exact hq.trans hq'
  ext v
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, pointDerivative_apply B C _ p ⟨u, hu⟩,
    pointDerivative_apply B C _ p ⟨u, hut⟩,
    localCov_eq B C _ _ p X u (Eventually.of_forall (fun _ => rfl)) hu,
    localCov_eq B C _ _ p X u (Eventually.of_forall (fun _ => rfl)) hut]

/-- Evaluation on a local field uses its value alone, with no choice of extension. -/
theorem pointDerivative_local (X : (q : M) → TangentSpace S q)
    (s : (q : M) → E q) (p : M)
    (hX : ∃ Y : Field S, ∀ᶠ q in 𝓝 p, Y.val q = X q)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) :
    pointDerivative C s p (X p) = localCov C X s p := by
  obtain ⟨Y, hY⟩ := hX
  obtain ⟨t, ht⟩ := hs
  rw [← hY.self_of_nhds, pointDerivative_apply B C _ p ⟨t, ht⟩,
    localCov_eq B C _ _ p Y t (Eventually.of_forall (fun _ => rfl)) ht,
    localCov_eq B C _ _ p Y t hY ht]

theorem localCov_pointwise_field (X Y : (q : M) → TangentSpace S q)
    (s : (q : M) → E q) (p : M)
    (hX : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = X q)
    (hY : ∃ Z : Field S, ∀ᶠ q in 𝓝 p, Z.val q = Y q)
    (hs : ∃ t : Section B, ∀ᶠ q in 𝓝 p, t.val q = s q) (hXY : X p = Y p) :
    localCov C X s p = localCov C Y s p := by
  rw [← pointDerivative_local B C X s p hX hs,
    ← pointDerivative_local B C Y s p hY hs, hXY]

/-- Real linearity of ∇s at a point in its smooth-section argument. -/
theorem pointDerivative_add_section (s t : Section B) (p : M) (v : TangentSpace S p) :
    pointDerivative C (s + t).val p v =
      pointDerivative C s.val p v + pointDerivative C t.val p v := by
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  simp only [← hX, pointDerivative_global B C, map_add, section_add_apply]

theorem pointDerivative_smul_section (s : Section B) (c : ℝ) (p : M) (v : TangentSpace S p) :
    pointDerivative C (c • s).val p v = c • pointDerivative C s.val p v := by
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  simp only [← hX, pointDerivative_global B C, map_smul, section_smul_apply]

theorem pointDerivative_leibniz (s : Section B) (f : GlobalSmooth S)
    (p : M) (v : TangentSpace S p) :
    pointDerivative C (mulSection f s).val p v =
      scalarDerivative S f.val p v • s.val p + f.val p • pointDerivative C s.val p v := by
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, pointDerivative_global B C, C.leibniz, section_add_apply,
    mulSection_apply, mulSection_apply, pointDerivative_global B C, scalarDerivative_global]

/-- Smoothness of the restriction follows locally from smooth global outputs. -/
theorem localCov_smooth (U : Set M) (hU : IsOpen U)
    (X : (q : M) → TangentSpace S q) (s : (q : M) → E q)
    (hX : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      (tangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, X q⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) U)
    (hs : SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U) :
    SmoothManifolds.MapData.ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q, localCov C X s q⟩ : Bundle.TotalSpace (Euclidean r) E)) U := by
  intro p hp
  obtain ⟨Y, hY⟩ := exists_section_representative (tangentBundle S) U hU X hX p hp
  obtain ⟨t, ht⟩ := exists_section_representative B U hU s hs p hp
  apply SmoothManifolds.SectionExtension.section_smoothAt_congr B ((C.cov Y t).property p)
  filter_upwards [hY.eventually_nhds, ht.eventually_nhds] with q hYq htq
  exact (localCov_eq B C X s q Y t hYq htq).symm

/-- In particular the restriction is an actual smooth local section. -/
theorem covOn_smooth (U : Set M) (hU : IsOpen U)
    (X : LocalSection (tangentBundle S) U hU) (s : LocalSection B U hU) :
    SmoothManifolds.MapData.ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      B.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, covOn C U hU X s p⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
  exact (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ _ U hU).mp
    (localCov_smooth B C U hU _ _
      (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ X.property)
      (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ s.property))

/-- Applying Leibniz to a finite frame expansion; the empty frame is allowed. -/
theorem finite_expansion (X : Field S) (k : ℕ)
    (f : Fin k → GlobalSmooth S) (e : Fin k → Section B) :
    C.cov X (∑ j, mulSection (f j) (e j)) =
      ∑ j, (mulSection (act S X (f j)) (e j) + mulSection (f j) (C.cov X (e j))) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => C.leibniz X (f j) (e j))

/-- Agreement with the original connection after restriction of global inputs. -/
theorem covOn_global (U : Set M) (hU : IsOpen U) (X : Field S) (s : Section B) (p : U) :
    covOn C U hU (restrictGlobalSection X U hU) (restrictGlobalSection s U hU) p =
      (C.cov X s).val p.val := by
  apply localCov_eq B C _ _ p.val X s
  · filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rfl
  · filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rfl

/-- The constructed restriction commutes with all further open restrictions. -/
theorem covOn_restriction {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (hUV : U ⊆ V) (X : LocalSection (tangentBundle S) V hV)
    (s : LocalSection B V hV) (p : U) :
    covOn C U hU (restrictLocalSection X hUV) (restrictLocalSection s hUV) p =
      covOn C V hV X s ⟨p.val, hUV p.property⟩ := by
  apply localCov_congr B C _ _ _ _ p.val
  · exact exists_section_representative (tangentBundle S) U hU _
      (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _
        (restrictLocalSection X hUV).property) p.val p.property
  · exact exists_section_representative B U hU _
      (SmoothManifolds.SectionExtension.totalSection_smooth B hU _
        (restrictLocalSection s hUV).property) p.val p.property
  · filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ q (hUV hq)]
    rfl
  · filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ q (hUV hq)]
    rfl

/-- The restriction is the evaluation of the intrinsic derivative on local fields. -/
theorem covOn_pointDerivative {U : Set M} {hU : IsOpen U}
    (X : LocalSection (tangentBundle S) U hU) (s : LocalSection B U hU) (p : U) :
    covOn C U hU X s p =
      pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val (X.val p) := by
  let t := SmoothManifolds.SectionExtension.totalSection s.val
  have hs := exists_section_representative B U hU t
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ s.property) p.val p.property
  have hX := exists_section_representative (tangentBundle S) U hU
    (SmoothManifolds.SectionExtension.totalSection X.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ X.property)
    p.val p.property
  rw [← SmoothManifolds.SectionExtension.totalSection_of_mem X.val p.val p.property,
    pointDerivative_local B C _ t p.val hX hs]
  rfl

/-- Connection forms restrict naturally; hence the gauge law applies on all
frame overlaps using restrictFrame. The tangent fibers themselves stay fixed. -/
theorem connectionForm_restriction {U V : Set M} {hU : IsOpen U} {hV : IsOpen V}
    (hUV : U ⊆ V) (b : LocalFrame B V hV) (p : U) (i j : Fin r) :
    connectionForm C (restrictFrame (hU := hU) b hUV) p i j =
      connectionForm C b ⟨p.val, hUV p.property⟩ i j := by
  let t := SmoothManifolds.SectionExtension.totalSection ((restrictFrame (hU := hU) b hUV).section_ j)
  let s := SmoothManifolds.SectionExtension.totalSection (b.section_ j)
  have ht := exists_section_representative B U hU t
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _
      ((restrictFrame (hU := hU) b hUV).smooth j)) p.val p.property
  have hts : ∀ᶠ q in 𝓝 p.val, t q = s q := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    simp only [t, s, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ q (hUV hq)]
    rfl
  have hd := pointDerivative_congr B C t s p.val ht hts
  ext v
  change (b.basis ⟨p.val, hUV p.property⟩).equivFun (pointDerivative C t p.val v) i =
    (b.basis ⟨p.val, hUV p.property⟩).equivFun (pointDerivative C s p.val v) i
  rw [hd]

/-- Each entry of Γ is smooth as a section of the actual cotangent bundle. -/
theorem connectionForm_smooth {U : Set M} (hU : IsOpen U)
    (b : LocalFrame B U hU) (i j : Fin r) :
    ManifoldSmoothOn S.smoothStructure.val (cotangentBundle S).totalManifold.smoothStructure.val
      (fun q => (⟨q, SmoothManifolds.SectionExtension.totalSection
        (E := fun p => Module.Dual ℝ (TangentSpace S p))
        (fun p : U => connectionForm C b p i j) q⟩ :
        Bundle.TotalSpace (Euclidean n) (fun p => Module.Dual ℝ (TangentSpace S p)))) U := by
  classical
  apply covector_smoothOn_of_evaluations U
  intro X p hp
  let e := SmoothManifolds.SectionExtension.totalSection (b.section_ j)
  have hs := localCov_smooth B C U hU X.val e
    (fun q _ => X.property q)
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ (b.smooth j))
  have hr := (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞)
    _ _ _ U hU).mp hs
  have hc := (SmoothManifolds.Frames.smooth_section_iff_coefficients B U hU b
    (fun q => localCov C X.val e q.val)).mp hr i
  apply (SmoothManifolds.FrameData.VectorSmoothAt.totalize hU (hc ⟨p, hp⟩)).congr
  filter_upwards [hU.mem_nhds hp] with q hq
  simp only [SmoothManifolds.FrameData.totalize_of_mem _ q hq,
    SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq,
    SmoothManifolds.FrameData.coefficients]
  change (b.basis ⟨q, hq⟩).equivFun (localCov C X.val e q) i =
    (b.basis ⟨q, hq⟩).equivFun (pointDerivative C e q (X.val q)) i
  rw [pointDerivative_apply B C e q
    (exists_section_representative B U hU e
      (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ (b.smooth j)) q hq)]

/-- Γ is characterized by ∇e = eΓ, including for arbitrary local fields. -/
theorem connectionForm_characterization {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (X : LocalSection (tangentBundle S) U hU)
    (p : U) (i j : Fin r) :
    connectionForm C b p i j (X.val p) =
      (b.basis p).equivFun (covOn C U hU X ⟨b.section_ j, b.smooth j⟩ p) i := by
  let e := SmoothManifolds.SectionExtension.totalSection (b.section_ j)
  have he := exists_section_representative B U hU e
    (SmoothManifolds.SectionExtension.totalSection_smooth B hU _ (b.smooth j)) p.val p.property
  have hX := exists_section_representative (tangentBundle S) U hU
    (SmoothManifolds.SectionExtension.totalSection X.val)
    (SmoothManifolds.SectionExtension.totalSection_smooth (tangentBundle S) hU _ X.property)
    p.val p.property
  change (b.basis p).equivFun (pointDerivative C e p.val (X.val p)) i = _
  rw [← SmoothManifolds.SectionExtension.totalSection_of_mem X.val p.val p.property,
    pointDerivative_local B C _ e p.val hX he]
  rfl

/-- Leibniz for the pointwise linear derivative of a finite global expansion. -/
theorem pointDerivative_finite_expansion (k : ℕ) (f : Fin k → GlobalSmooth S)
    (e : Fin k → Section B) (p : M) (v : TangentSpace S p) :
    pointDerivative C (∑ j, mulSection (f j) (e j)).val p v =
      ∑ j, (scalarDerivative S (f j).val p v • (e j).val p +
        (f j).val p • pointDerivative C (e j).val p v) := by
  obtain ⟨X, hX⟩ := section_evaluation_surjective (tangentBundle S) p v
  rw [← hX, pointDerivative_global B C, finite_expansion B C]
  simp only [Submodule.coe_sum, Finset.sum_apply, section_add_apply, mulSection_apply]
  simp_rw [pointDerivative_global B C, scalarDerivative_global]

/-- The full local formula in an arbitrary smooth row frame, at every tangent
vector, with the actual germ differential of the local coefficient column. -/
theorem local_frame_formula {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (s : LocalSection B U hU) (p : U)
    (v : TangentSpace S p.val) (i : Fin r) :
    (b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val v) i =
    scalarDerivative S (SmoothManifolds.FrameData.totalize
      (fun q : U => SmoothManifolds.FrameData.coefficients b s.val q i)) p.val v +
      ∑ j, connectionForm C b p i j v *
        SmoothManifolds.FrameData.coefficients b s.val p j := by
  classical
  obtain ⟨f, hf⟩ := local_coefficients_representative B b s.val s.property p
  obtain ⟨e, he⟩ := local_frame_representative B b p
  let t : Section B := ∑ j, mulSection (f j) (e j)
  have ht : ∀ᶠ q in 𝓝 p.val,
      t.val q = SmoothManifolds.SectionExtension.totalSection s.val q := by
    filter_upwards [hU.mem_nhds p.property, Filter.eventually_all.mpr hf,
      Filter.eventually_all.mpr he] with q hq hfq heq
    simp only [t, Submodule.coe_sum, Finset.sum_apply, mulSection_apply]
    simp_rw [hfq, heq]
    simp only [SmoothManifolds.FrameData.totalize_of_mem _ q hq,
      SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact (SmoothManifolds.Frames.section_expansion B U hU b s.val ⟨q, hq⟩).symm
  rw [← pointDerivative_congr B C t.val _ p.val
    ⟨t, Eventually.of_forall (fun _ => rfl)⟩ ht]
  have h := congrArg (fun z : E p.val => (b.basis p).equivFun z i)
    (pointDerivative_finite_expansion B C r f e p.val v)
  change _ = _ at h
  rw [h]
  simp only [map_sum, map_add, map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  have hfe (j : Fin r) : (f j).val p.val =
      SmoothManifolds.FrameData.coefficients b s.val p j := by
    simpa only [SmoothManifolds.FrameData.totalize_of_mem _ p.val p.property] using
      (hf j).eq_of_nhds
  have hee (j : Fin r) : (e j).val p.val = b.basis p j := by
    simpa only [SmoothManifolds.SectionExtension.totalSection_of_mem _ p.val p.property,
      b.basis_eq] using (he j).self_of_nhds
  have hde (j : Fin r) : pointDerivative C (e j).val p.val =
      pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val :=
    pointDerivative_congr B C _ _ p.val ⟨e j, Eventually.of_forall (fun _ => rfl)⟩ (he j)
  congr 1
  · simp_rw [hee, Module.Basis.equivFun_self]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact (scalarDerivative_representative (f i).val (f i) p.val Filter.EventuallyEq.rfl v).trans
      (scalarDerivative_representative _ (f i) p.val (hf i) v).symm
  · apply Finset.sum_congr rfl
    intro j _
    rw [hfe, hde]
    exact mul_comm _ _

/-- Explicit e(dv + Γv) for every smooth local coefficient column v. -/
theorem local_frame_formula_coefficients {U : Set M} {hU : IsOpen U}
    (b : LocalFrame B U hU) (f : U → Euclidean r)
    (hf : SmoothManifolds.FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU) f)
    (p : U) (v : TangentSpace S p.val) (i : Fin r) :
    (b.basis p).equivFun
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection
        (frameSection b f hf).val) p.val v) i =
      scalarDerivative S (SmoothManifolds.FrameData.totalize (fun q : U => f q i)) p.val v +
        ∑ j, connectionForm C b p i j v * f p j := by
  have h := local_frame_formula B C b (frameSection b f hf) p v i
  simpa only [frameSection, P202.ConnectionData.frameSection, SmoothManifolds.FrameData.coefficients,
    LinearEquiv.apply_symm_apply] using h

section LocalTransition
variable {U : Set M} {hU : IsOpen U} (b c : LocalFrame B U hU)

/-- Coordinate change in the actual fiber, with no smoothness restriction on z. -/
theorem local_coefficient_change (p : U) (z : E p.val) (i : Fin r) :
    (b.basis p).equivFun z i =
      ∑ j, localTransition b c p i j * (c.basis p).equivFun z j := by
  have h := congrArg (fun z => (b.basis p).equivFun z i)
    ((c.basis p).sum_equivFun z).symm
  rw [h]
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [c.basis_eq]
  exact mul_comm _ _

theorem local_transition_inverse (p : U) :
    localTransition b c p * localTransition c b p = 1 ∧
      localTransition c b p * localTransition b c p = 1 := by
  have h (b c : LocalFrame B U hU) : localTransition b c p * localTransition c b p = 1 := by
    ext i j
    have he := local_coefficient_change B b c p (b.section_ j p) i
    change _ = (∑ k, localTransition b c p i k * localTransition c b p k j) at he
    rw [Matrix.mul_apply, ← he]
    simp only [← b.basis_eq, Module.Basis.equivFun_self]
    simp [Matrix.one_apply, eq_comm]
  exact ⟨h b c, h c b⟩

/-- The transition entries themselves are smooth functions on the open domain. -/
theorem localTransition_smooth (i j : Fin r) :
    SmoothManifolds.FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p => localTransition b c p i j) :=
  (SmoothManifolds.Frames.smooth_section_iff_coefficients B U hU b
    (c.section_ j)).mp (c.smooth j) i

/-- The Leibniz product formula A Γ' = Γ A + dA, on every open frame domain. -/
theorem local_frame_transformation_product (p : U) (v : TangentSpace S p.val) :
    localTransition b c p * connectionMatrix C c p v =
      connectionMatrix C b p v * localTransition b c p + localTransitionDerivative b c p v := by
  ext i j
  have he := local_coefficient_change B b c p
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (c.section_ j)) p.val v) i
  have hf := local_frame_formula B C b ⟨c.section_ j, c.smooth j⟩ p v i
  change _ = ∑ k, localTransition b c p i k * connectionMatrix C c p v k j at he
  rw [Matrix.mul_apply, ← he, hf]
  change _ + (∑ k, connectionMatrix C b p v i k * localTransition b c p k j) =
    (∑ k, connectionMatrix C b p v i k * localTransition b c p k j) + _
  exact add_comm _ _

/-- The full gauge law, using the proved genuine inverse transition. -/
theorem local_frame_transformation (p : U) (v : TangentSpace S p.val) :
    connectionMatrix C c p v =
      localTransition c b p * connectionMatrix C b p v * localTransition b c p +
        localTransition c b p * localTransitionDerivative b c p v := by
  have h := congrArg (fun Z => localTransition c b p * Z)
    (local_frame_transformation_product B C b c p v)
  simpa only [← Matrix.mul_assoc, (local_transition_inverse B b c p).2,
    Matrix.one_mul, Matrix.mul_add] using h

end LocalTransition

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

/-- Evaluation of the connection in a global frame. The arbitrary-open-domain and tangent-linear versions are established above. -/
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
end P202.Geometry.ConnectionForms
