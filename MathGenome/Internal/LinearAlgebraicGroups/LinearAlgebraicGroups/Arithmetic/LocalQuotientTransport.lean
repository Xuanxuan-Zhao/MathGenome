import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

namespace LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport

universe u v w

theorem subgroup_transport : Specs.SubgroupTransport.{u, v} := by
  intro G G' _ _ _ _ e H
  have hmem (g : G) : e g ∈ imageSubgroup e H ↔ g ∈ H := by
    change (∃ x ∈ H, e x = e g) ↔ g ∈ H
    exact ⟨fun ⟨x, hx, he⟩ => e.injective he ▸ hx, fun hg => ⟨g, hg, rfl⟩⟩
  have himage : (imageSubgroup e H : Set G') = e.toHomeomorph '' (H : Set G) := rfl
  exact ⟨hmem, himage ▸ e.toHomeomorph.isClosed_image.symm,
    (e.toHomeomorph.subtype fun g => (hmem g).symm).discreteTopology_iff⟩

theorem quotient_action : Specs.QuotientAction.{u} := by
  intro G _ _ _ H
  have hopen : IsOpenQuotientMap (coset H) := MulAction.isOpenQuotientMap_quotientMk
  refine ⟨hopen, ?_, ?_⟩
  · intro x y
    constructor
    · intro h
      have hrel : QuotientGroup.rightRel H x y := Quotient.exact' h
      obtain ⟨b, hb⟩ := hrel
      exact ⟨b, b.property, hb.symm⟩
    · rintro ⟨b, hb, hx⟩
      exact Quotient.sound' (show QuotientGroup.rightRel H x y from ⟨⟨b, hb⟩, hx.symm⟩)
  · rw [← (hopen.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    exact continuous_quotient_mk'.comp continuous_mul

theorem quotient_transport : Specs.QuotientTransport.{u, v} := by
  intro G G' _ _ _ _ _ _ e H
  have hrel (x y : G) :
      QuotientGroup.rightRel H x y ↔
        QuotientGroup.rightRel (imageSubgroup e H) (e x) (e y) := by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
      ← map_inv, ← map_mul, (subgroup_transport e H).1]
  have hrel' (x y : G') :
      QuotientGroup.rightRel (imageSubgroup e H) x y →
        QuotientGroup.rightRel H (e.symm x) (e.symm y) := by
    intro h
    apply (hrel _ _).2
    simpa using h
  let q : RightCosets H ≃ₜ RightCosets (imageSubgroup e H) :=
    { toFun := Quotient.map' e (fun x y => (hrel x y).1)
      invFun := Quotient.map' e.symm hrel'
      left_inv := by
        intro z
        induction z using Quotient.inductionOn' with
        | _ g =>
          change coset H (e.symm (e g)) = coset H g
          rw [e.symm_apply_apply]
      right_inv := by
        intro z
        induction z using Quotient.inductionOn' with
        | _ g =>
          change coset (imageSubgroup e H) (e (e.symm g)) = coset (imageSubgroup e H) g
          rw [e.apply_symm_apply]
      continuous_toFun := continuous_quot_map _ e.continuous
      continuous_invFun := continuous_quot_map _ e.symm.continuous }
  refine ⟨q, fun _ => rfl, ?_⟩
  intro z a
  induction z using Quotient.inductionOn' with
  | _ g =>
    change coset (imageSubgroup e H) (e (g * a)) = coset (imageSubgroup e H) (e g * e a)
    rw [map_mul]

theorem measure_transport : Specs.MeasureTransport.{u, v} := by
  intro G G' _ _ _ _ _ _ e H H' q hq μ hμ hfinite h₀
  refine ⟨inferInstance, (Measure.map_ne_zero_iff q.measurable.aemeasurable).2 h₀, ?_, ?_⟩
  · intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    have hmeas (b : G') : Measurable (rightTranslate (H := H') b) :=
      ((quotient_action H').2.2.comp (continuous_id.prodMk continuous_const)).measurable
    refine ⟨hmeas (e a), ?_⟩
    have hcomm :
        (rightTranslate (e a) ∘ q : RightCosets H → RightCosets H') =
          q ∘ rightTranslate a := funext fun x => (hq x a).symm
    rw [Measure.map_map (hmeas (e a)) q.measurable, hcomm,
      ← Measure.map_map q.measurable (hμ a).measurable, (hμ a).map_eq]
  · exact fun s => q.toMeasurableEquiv.map_apply s

/-- Equal underlying functions induce equal pullbacks, regardless of the chosen proofs
of measure preservation. -/
private theorem pullback_congr {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f g : X → Y}
    (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g μ ν) (h : f = g)
    (z : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving f hf z = Lp.compMeasurePreserving g hg z := by
  subst g
  rfl

theorem representation_law : Specs.RepresentationLaw.{u} := by
  intro G _ _ H μ hμ
  refine ⟨?_, ?_⟩
  · intro f
    have hone : rightTranslate (H := H) (1 : G) = id := by
      funext x
      induction x using Quotient.inductionOn' with
      | _ g =>
        change coset H (g * 1) = coset H g
        rw [mul_one]
    change Lp.compMeasurePreserving _ (hμ 1) f = f
    exact (pullback_congr (hμ 1) (.id μ) hone f).trans (Lp.compMeasurePreserving_id_apply f)
  · intro a b f
    have hmul : rightTranslate (H := H) (a * b) = rightTranslate b ∘ rightTranslate a := by
      funext x
      induction x using Quotient.inductionOn' with
      | _ g =>
        change coset H (g * (a * b)) = coset H (g * a * b)
        rw [mul_assoc]
    change Lp.compMeasurePreserving _ (hμ (a * b)) f =
      Lp.compMeasurePreserving _ (hμ a) (Lp.compMeasurePreserving _ (hμ b) f)
    exact (pullback_congr (hμ (a * b)) ((hμ b).comp (hμ a)) hmul f).trans
      (Lp.compMeasurePreserving_comp_apply f (hμ b) (hμ a))

theorem representation_transport : Specs.RepresentationTransport.{u, v, w} := by
  intro G G' _ _ _ _ e H H' q hq μ hμ hν
  have hp : MeasurePreserving q μ (μ.map q) := ⟨q.measurable, rfl⟩
  have hqinv : MeasurePreserving q.symm (μ.map q) μ :=
    ⟨q.symm.measurable, q.toMeasurableEquiv.map_symm_map⟩
  have inverse_comp (f : L2 (μ.map q)) :
      Lp.compMeasurePreserving q.symm hqinv (Lp.compMeasurePreserving q hp f) = f := by
    rw [← Lp.compMeasurePreserving_comp_apply f hp hqinv]
    exact (pullback_congr (hp.comp hqinv) (.id _) (funext q.apply_symm_apply) f).trans
      (Lp.compMeasurePreserving_id_apply f)
  have comp_inverse (f : L2 μ) :
      Lp.compMeasurePreserving q hp (Lp.compMeasurePreserving q.symm hqinv f) = f := by
    rw [← Lp.compMeasurePreserving_comp_apply f hqinv hp]
    exact (pullback_congr (hqinv.comp hp) (.id _) (funext q.symm_apply_apply) f).trans
      (Lp.compMeasurePreserving_id_apply f)
  let U : L2 μ ≃ₗᵢ[ℂ] L2 (μ.map q) :=
    LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℂ q.symm hqinv)
      (Lp.compMeasurePreservingₗ ℂ q hp)
      (by
        ext1 f
        exact inverse_comp f)
      (by
        ext1 f
        exact comp_inverse f)
  have hU (f : L2 μ) : (U f : RightCosets H' → ℂ) =ᵐ[μ.map q] (f ∘ q.symm) :=
    Lp.coeFn_compMeasurePreserving f hqinv
  have hintertwine (a : G) (f : L2 μ) :
      U (rightOperator hμ a f) = rightOperator hν (e a) (U f) := by
    change Lp.compMeasurePreserving _ hqinv (Lp.compMeasurePreserving _ (hμ a) f) =
      Lp.compMeasurePreserving _ (hν (e a)) (Lp.compMeasurePreserving _ hqinv f)
    rw [← Lp.compMeasurePreserving_comp_apply f (hμ a) hqinv,
      ← Lp.compMeasurePreserving_comp_apply f hqinv (hν (e a))]
    apply pullback_congr
    funext x
    apply q.injective
    simpa only [Function.comp_apply, q.apply_symm_apply] using hq (q.symm x) a
  have hcoefficient (a : G) (f g : L2 μ) :
      ⟪rightOperator hν (e a) (U f), U g⟫_ℂ = ⟪rightOperator hμ a f, g⟫_ℂ := by
    rw [← hintertwine]
    exact U.inner_map_map _ _
  refine ⟨U, hU, fun f => Lp.coeFn_compMeasurePreserving f hp, hintertwine, hcoefficient,
    ?_, ?_, ?_, ?_⟩
  ·
    intro ι l a f g z
    rw [funext fun i => hcoefficient (a i) f g]
  ·
    intro c f
    constructor
    · intro h
      have h' := (q.toMeasurableEquiv.measurableEmbedding.ae_map_iff
        (p := fun y => f (q.symm y) = c)).1 ((hU f).symm.trans h)
      change ∀ᵐ x ∂μ, f x = c
      simpa only [Homeomorph.toMeasurableEquiv_coe, q.symm_apply_apply] using h'
    · intro h
      exact (hU f).trans (hqinv.quasiMeasurePreserving.ae_eq_comp h)
  · intro f
    have horbit :
        ((fun b : G' => rightOperator hν b (U f)) ∘ e.toHomeomorph) =
          U.toHomeomorph ∘ (fun a : G => rightOperator hμ a f) :=
      funext fun a => (hintertwine a f).symm
    calc
      Continuous (fun b : G' => rightOperator hν b (U f)) ↔
          Continuous ((fun b : G' => rightOperator hν b (U f)) ∘ e.toHomeomorph) :=
        e.toHomeomorph.comp_continuous_iff'.symm
      _ ↔ Continuous (fun a : G => rightOperator hμ a f) := by
        rw [horbit, U.toHomeomorph.comp_continuous_iff]
  · intro ι l a B
    dsimp only
    rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto,
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
    have hlimit (f g : L2 μ) :
        Tendsto (fun i => ⟪U g, rightOperator hν (e (a i)) (U f)⟫_ℂ) l
          (𝓝 ⟪U g, U (B (U.symm (U f)))⟫_ℂ) ↔
        Tendsto (fun i => ⟪g, rightOperator hμ (a i) f⟫_ℂ) l (𝓝 ⟪g, B f⟫_ℂ) := by
      simp only [U.symm_apply_apply, ← hintertwine, U.inner_map_map]
    refine ⟨fun h f g => (hlimit f g).1 (h (U f) (U g)), fun h f' g' => ?_⟩
    obtain ⟨f, rfl⟩ := U.surjective f'
    obtain ⟨g, rfl⟩ := U.surjective g'
    exact (hlimit f g).2 (h f g)

theorem normal_closure_transport : Specs.NormalClosureTransport.{u, v} := by
  intro G G' _ _ _ _ _ _ e s
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe]
  have himage := e.toHomeomorph.image_closure (Subgroup.normalClosure s : Set G)
  change e '' closure (Subgroup.normalClosure s : Set G) = _
  rw [show e '' closure (Subgroup.normalClosure s : Set G) =
      closure (e '' (Subgroup.normalClosure s : Set G)) from himage]
  change closure (↑((Subgroup.normalClosure s).map e.toMulEquiv.toMonoidHom) : Set G') =
    (closedNormalClosure (e '' s) : Set G')
  rw [Subgroup.map_normalClosure _ _ e.surjective, Subgroup.topologicalClosure_coe]
  rfl

theorem group_convergence : Specs.GroupConvergence.{u, v, w} := by
  intro G G' _ _ _ _ e ι l g x
  exact e.toHomeomorph.isInducing.tendsto_nhds_iff.symm

theorem rescaling_convergence : Specs.RescalingConvergence.{u, v, w} := by
  intro G G' _ _ _ _ e ι l a n y h r
  have hfun :
      (fun i => (e a ^ n i)⁻¹ * (e (y i))⁻¹ * e (h i) * e (y i) * e a ^ n i) =
        e ∘ (fun i => (a ^ n i)⁻¹ * (y i)⁻¹ * h i * y i * a ^ n i) := by
    funext i
    simp only [Function.comp_apply, map_mul, map_inv, map_pow]
  rw [hfun]
  exact group_convergence e l _ r

theorem quotient_convergence : Specs.QuotientConvergence.{u, v, w} := by
  intro G G' _ _ _ _ e H H' q hq ι l g x
  refine ⟨q.isInducing.tendsto_nhds_iff.symm, fun a => ?_⟩
  have hcomm (i : ι) : rightTranslate (e (a i)) (q (g i)) =
      (q ∘ fun j => rightTranslate (a j) (g j)) i := (hq (g i) (a i)).symm
  rw [funext hcomm]
  exact q.isInducing.tendsto_nhds_iff.symm

end LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
