import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Mathlib.Analysis.Calculus.MeanValue

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
/-! Conditional derivation of M11.01 on the shared smooth exterior sections.
The public helpers take the entire ordered upstream contract; the original
closed targets are reserved for closure by the owner with real upstream proofs.
The independent Specs keep the original unconditional mathematical statements. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
noncomputable section

namespace SmoothManifolds.DeRhamResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData
  DeRhamData Set Filter
open scoped Topology
universe u

private theorem regular_zero {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) :
    IsRegularField C ⊤ k (0 : Field S k) := by
  intro c hc p
  refine ⟨univ, isOpen_univ, mem_univ _, fun _ => 0, contDiffOn_const, ?_⟩
  intro q hq
  funext I
  simp [coefficients]

private theorem regular_add {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (α β : Field S k)
    (hα : IsRegularField C ⊤ k α) (hβ : IsRegularField C ⊤ k β) :
    IsRegularField C ⊤ k (α+β) := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, eF⟩ := hα c hc p
  obtain ⟨V, hV, hpV, G, hG, eG⟩ := hβ c hc p
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, fun z => F z + G z,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), ?_⟩
  intro q hq
  change F (c q.val).val + G (c q.val).val = _
  rw [eF q hq.1, eG q hq.2]
  funext I
  simp [coefficients]

private theorem regular_smul {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) (r : ℝ) (α : Field S k)
    (hα : IsRegularField C ⊤ k α) : IsRegularField C ⊤ k (r • α) := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, eF⟩ := hα c hc p
  refine ⟨U, hU, hpU, fun z => r • F z, hF.const_smul r, ?_⟩
  intro q hq
  change r • F (c q.val).val = _
  rw [eF q hq]
  funext I
  simp [coefficients]

private def regularForms {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ) :
    Submodule ℝ (Field S k) where
  carrier := {ω | IsRegularField C ⊤ k ω}
  zero_mem' := regular_zero C k
  add_mem' := regular_add C k _ _
  smul_mem' := regular_smul C k

private theorem complex_exists_proof
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (hfamily : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (hcoordinates : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.complex_existsType.{u} := by
  intro n a M _ S C B
  obtain ⟨D, hD, _⟩ := hfamily C B
  exact ⟨{
    forms := regularForms C
    mem_forms := fun k ω => (hcoeff C k (B k) ω).symm
    D := D
    axioms := hD
    coordinates := hcoordinates C B D hD }⟩

private theorem square_zero_proof :
    Specs.SmoothManifolds.DeRham.Algebra.square_zeroType.{u} := by
  intro n a M _ S C B K k ω
  apply Subtype.ext
  exact K.axioms.square k ω.val ((K.mem_forms _ _).mp ω.property)

private theorem exact_closed_proof :
    Specs.SmoothManifolds.DeRham.Algebra.exact_closedType.{u} := by
  intro n a M _ S C B K k
  cases k with
  | zero => exact bot_le
  | succ k =>
    rintro ω ⟨α, rfl⟩
    exact square_zero_proof K k α

private theorem class_zero_iff_exact_proof :
    Specs.SmoothManifolds.DeRham.Algebra.class_zero_iff_exactType.{u} := by
  intro n a M _ S C B K k ω
  exact Submodule.Quotient.mk_eq_zero (K.boundaries k)

private theorem above_dimension_proof :
    Specs.SmoothManifolds.DeRham.Algebra.above_dimensionType.{u} := by
  intro n a M _ S C B K k hk
  have hz (ω : Field S k) : ω = 0 := by
    funext p
    exact ExteriorAlgebraResults.fields_above_dimension C k hk ω p
  letI : Subsingleton (K.forms k) := ⟨fun α β =>
    Subtype.ext ((hz α.val).trans (hz β.val).symm)⟩
  change Subsingleton (↥(K.closed k) ⧸ K.boundaries k)
  infer_instance

private theorem negative_degrees_proof :
    Specs.SmoothManifolds.DeRham.Algebra.negative_degreesType.{u} := by
  intro n a M _ S C B K j
  constructor <;> exact inferInstanceAs (Subsingleton (ULift.{u} (Fin 0) → ℝ))

private theorem empty_cohomology_proof :
    Specs.SmoothManifolds.DeRham.Algebra.empty_cohomologyType.{u} := by
  intro n a M _ _ S C B K k
  change Subsingleton (↥(K.closed k) ⧸ K.boundaries k)
  infer_instance

section Wedge
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

private def formWedge {k l : ℕ} (α : K.forms k) (β : K.forms l) : K.forms (k+l) :=
  ⟨fieldWedge α.val β.val, (K.mem_forms _ _).mpr
    (ExteriorAlgebraResults.wedge_smooth C k l (B k) (B l) (B (k+l)) α.val β.val
      ((K.mem_forms _ _).mp α.property) ((K.mem_forms _ _).mp β.property))⟩

private theorem wedge_closed {k l : ℕ} (α : K.closed k) (β : K.closed l) :
    K.d (k+l) (formWedge K α.val β.val) = 0 := by
  have hα : K.D k α.val.val = 0 := congrArg Subtype.val α.property
  have hβ : K.D l β.val.val = 0 := congrArg Subtype.val β.property
  apply Subtype.ext
  funext p
  apply Subtype.ext
  change (K.D (k+l) (fieldWedge α.val.val β.val.val) p :
    ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = 0
  have h := K.axioms.leibniz k l α.val.val β.val.val
    ((K.mem_forms _ _).mp α.val.property) ((K.mem_forms _ _).mp β.val.property) p
  simpa only [hα, hβ, Pi.zero_apply, map_zero, LinearMap.zero_apply,
    ZeroMemClass.coe_zero, smul_zero, add_zero] using h

private def closedWedge {k l : ℕ} (α : K.closed k) (β : K.closed l) : K.closed (k+l) :=
  ⟨formWedge K α.val β.val, wedge_closed K α β⟩

end Wedge

section Pullback
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {C : CotangentBundle S} {A : CotangentBundle T}
  {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
  (K : Calculus C B) (J : Calculus A E)
  (f : M → N) (hf : MapData.IsSmoothMap S T f)
  (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
  (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))

private def smoothPull (k : ℕ) : J.forms k →ₗ[ℝ] K.forms k where
  toFun α := ⟨FormPullbackData.pullbackField S T f L α.val,
    (K.mem_forms k _).mpr (FormPullbackResults.pullback_smooth S T C A f hf L hL k
      (B k) (E k) α.val ((J.mem_forms k _).mp α.property))⟩
  map_add' α β := by
    apply Subtype.ext
    funext p
    exact map_add (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (f p)) k (L p)) (α.val (f p)) (β.val (f p))
  map_smul' r α := by
    apply Subtype.ext
    funext p
    exact map_smul (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (f p)) k (L p)) r (α.val (f p))

private theorem smoothPull_chain
    (hnat : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (k : ℕ) (α : J.forms k) :
    smoothPull K J f hf L hL (k+1) (J.d k α) =
      K.d k (smoothPull K J f hf L hL k α) := by
  apply Subtype.ext
  exact hnat S T C A B E K.D J.D K.axioms J.axioms f hf L hL k α.val
    ((J.mem_forms k _).mp α.property)

private def closedPull
    (hnat : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (k : ℕ) : J.closed k →ₗ[ℝ] K.closed k where
  toFun α := ⟨smoothPull K J f hf L hL k α.val, by
    change K.d k (smoothPull K J f hf L hL k α.val) = 0
    rw [← smoothPull_chain K J f hf L hL hnat]
    have hα : J.d k α.val = 0 := α.property
    rw [hα, map_zero]⟩
  map_add' α β := Subtype.ext (map_add _ _ _)
  map_smul' r α := Subtype.ext (map_smul _ _ _)

private theorem closedPull_boundaries
    (hnat : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (k : ℕ) : J.boundaries k ≤
      (K.boundaries k).comap (closedPull K J f hf L hL hnat k) := by
  intro α hα
  cases k with
  | zero =>
    have hz : α.val = 0 := hα
    change smoothPull K J f hf L hL 0 α.val = 0
    rw [hz, map_zero]
  | succ k =>
    obtain ⟨β, hβ⟩ := hα
    refine ⟨smoothPull K J f hf L hL k β, ?_⟩
    change K.d k (smoothPull K J f hf L hL k β) =
      smoothPull K J f hf L hL (k+1) α.val
    rw [← smoothPull_chain K J f hf L hL hnat, hβ]
    rfl

end Pullback

private theorem pullback_exists_proof
    (hnat : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_existsType.{u} := by
  intro n m a b M N _ _ S T C A B E K J f hf L hL
  let F (k : ℕ) := (J.boundaries k).mapQ (K.boundaries k)
    (closedPull K J f hf L hL hnat k)
    (closedPull_boundaries K J f hf L hL hnat k)
  refine ⟨F, ?_⟩
  intro k α
  exact ⟨closedPull K J f hf L hL hnat k α, rfl, rfl⟩

private theorem pullback_id_proof :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_idType.{u} := by
  intro n a M _ S C B K L hL F hF k x
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  obtain ⟨β, hβ, hFβ⟩ := hF k α
  change F k (K.classOf k α) = K.classOf k α
  rw [hFβ]
  apply congrArg (K.classOf k)
  apply Subtype.ext
  apply Subtype.ext
  exact hβ.trans (FormPullbackResults.pullback_id S L hL k α.val.val)

private theorem closed_ext {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) {k : ℕ} (α β : K.closed k) (h : α.val.val = β.val.val) : α = β :=
  Subtype.ext (Subtype.ext h)

private theorem pullback_comp_proof :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_compType.{u} := by
  intro n m r a b c M N P _ _ _ S T U C A V B E W K J I f g hf hg
    L R H hL hR hH F G Q hF hG hQ k x
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  obtain ⟨β, hβ, hGβ⟩ := hG k α
  obtain ⟨γ, hγ, hFγ⟩ := hF k β
  obtain ⟨δ, hδ, hQδ⟩ := hQ k α
  change Q k (I.classOf k α) = F k (G k (I.classOf k α))
  have heq : δ = γ := closed_ext K δ γ
    (hδ.trans ((FormPullbackResults.pullback_comp S T U f g hf hg
      L R H hL hR hH k α.val.val).trans
        ((congrArg (FormPullbackData.pullbackField S T f L) hβ.symm).trans hγ.symm)))
  exact hQδ.trans ((congrArg (K.classOf k) heq).trans
    (hFγ.symm.trans (congrArg (fun z => F k z) hGβ.symm)))

private theorem class_surjective {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (k : ℕ) : Function.Surjective (K.classOf k) :=
  (K.boundaries k).mkQ_surjective

section ProductNaturality
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {C : CotangentBundle S} {A : CotangentBundle T}
  {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
  (K : Calculus C B) (J : Calculus A E)
  (P : K.GradedProduct) (Q : J.GradedProduct) (f : M → N)
  (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
  (F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k)

private theorem pullback_one
    (hPone : K.ProductOneRepresentative P) (hQone : J.ProductOneRepresentative Q)
    (hF : IsCohomologyPullback C B K J f L F) : F 0 Q.one = P.one := by
  obtain ⟨ε, hε, hQ⟩ := hQone
  obtain ⟨ε', hε', hP⟩ := hPone
  obtain ⟨β, hβ, hFβ⟩ := hF 0 ε
  have heq : β = ε' := closed_ext K β ε'
    (hβ.trans ((congrArg (FormPullbackData.pullbackField S T f L) hε).trans
      ((FormPullbackResults.pullback_zero S T f L (fun _ => 1)).trans hε'.symm)))
  exact (congrArg (fun z => F 0 z) hQ).trans
    (hFβ.trans ((congrArg (K.classOf 0) heq).trans hP.symm))

set_option maxHeartbeats 8000000 in
private theorem pullback_mul
    (hPrep : K.ProductRepresentatives P) (hQrep : J.ProductRepresentatives Q)
    (hF : IsCohomologyPullback C B K J f L F)
    (k l : ℕ) (x : J.Cohomology k) (y : J.Cohomology l) :
    F (k+l) (Q.mul k l x y) = P.mul k l (F k x) (F l y) := by
  obtain ⟨α, rfl⟩ := class_surjective J k x
  obtain ⟨β, rfl⟩ := class_surjective J l y
  have hγex := hQrep k l α β
  let γ : J.closed (k+l) := hγex.choose
  have hγ := hγex.choose_spec.1
  have hQ := hγex.choose_spec.2
  have hαex := hF k α
  let α' : K.closed k := hαex.choose
  have hα' := hαex.choose_spec.1
  have hFα := hαex.choose_spec.2
  have hβex := hF l β
  let β' : K.closed l := hβex.choose
  have hβ' := hβex.choose_spec.1
  have hFβ := hβex.choose_spec.2
  have hγpex := hF (k+l) γ
  let γ' : K.closed (k+l) := hγpex.choose
  have hγ' := hγpex.choose_spec.1
  have hFγ := hγpex.choose_spec.2
  have hδex := hPrep k l α' β'
  let δ : K.closed (k+l) := hδex.choose
  have hδ := hδex.choose_spec.1
  have hP := hδex.choose_spec.2
  have heq : γ' = δ := by
    apply closed_ext K
    rw [hγ', hγ, FormPullbackResults.pullback_wedge S T f L k l α.val.val β.val.val, ← hα', ← hβ', ← hδ]
  change F (k+l) (Q.mul k l (J.classOf k α) (J.classOf l β)) = _
  exact (congrArg (fun z => F (k+l) z) hQ).trans
    (hFγ.trans ((congrArg (K.classOf (k+l)) heq).trans
      (hP.symm.trans (congrArg₂ (P.mul k l) hFα.symm hFβ.symm))))

end ProductNaturality

private theorem pullback_product_proof :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_productType.{u} := by
  intro n m a b M N _ _ S T C A B E K J P Q f L F hP hQ hF
  exact ⟨pullback_one K J P Q f L F hP.2.2.2.2.2.1 hQ.2.2.2.2.2.1 hF,
    pullback_mul K J P Q f L F hP.2.2.2.2.1 hQ.2.2.2.2.1 hF⟩


section H0
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
 {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

private theorem coefficients_zero (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
 (ω : Field S 0) (p : c.source) (I : Index n 0) :
 coefficients C 0 c hc ω p I = exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val)) (ω p.val) := by
  unfold coefficients
  rw [exteriorPower.basis_repr_apply]
  let v : Fin 0 → Module.Dual ℝ (TangentSpace S p.val) := fun i => Fin.elim0 i
  have hx : ω p.val =
      exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val)) (ω p.val) •
        exteriorPower.ιMulti ℝ 0 v := by
    apply (exteriorPower.zeroEquiv ℝ _).injective
    simp
  rw [hx]
  simp


private theorem scalarField_const_smooth (r : ℝ) :
    IsForm (B 0) (FormPullbackData.scalarField S (fun _ => r)) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C 0 (B 0) _).mpr
  intro c hc I p
  have heq : (fun q : c.source => coefficients C 0 c hc
      (FormPullbackData.scalarField S (fun _ => r)) q I) = fun _ => r := by
    funext q
    rw [coefficients_zero]
    exact (exteriorPower.zeroEquiv ℝ _).apply_symm_apply r
  rw [heq]
  exact FrameData.VectorSmoothAt.const _ _ _


private theorem scalarField_lc_smooth (f : M → ℝ) (hf : IsLocallyConstant f) :
    IsForm (B 0) (FormPullbackData.scalarField S f) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C 0 (B 0) _).mpr
  intro c hc I p
  have heq : (fun q : c.source => coefficients C 0 c hc
      (FormPullbackData.scalarField S f) q I) = fun q => f q.val := by
    funext q
    rw [coefficients_zero]
    exact (exteriorPower.zeroEquiv ℝ _).apply_symm_apply _
  rw [heq]
  apply FrameData.VectorSmoothAt.congr
    (FrameData.VectorSmoothAt.const _ (f p.val) p)
  have he : f =ᶠ[𝓝 p.val] (fun _ => f p.val) := hf.eventually_eq p.val
  filter_upwards [he.comp_tendsto continuous_subtype_val.continuousAt] with q hq
  exact hq.symm


private def zeroCoefficient (ω : Field S 0) (p : M) : ℝ :=
  exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω p)

private theorem zeroCoefficient_smooth (ω : Field S 0) (hω : IsForm (B 0) ω) :
    PartitionData.ScalarSmooth S.smoothStructure.val (zeroCoefficient ω) := by
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  let I : Index n 0 := ⟨∅, by simp⟩
  have hs := (ExteriorAlgebraResults.smooth_iff_coefficients C 0 (B 0) ω).mp hω c hc I ⟨p, hp⟩
  have ht := FrameData.VectorSmoothAt.totalize c.open_source hs
  apply (scalarContDiffAt_iff _ _ _ _).mpr
  apply FrameData.VectorSmoothAt.congr ht
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  rw [FrameData.totalize_of_mem (fun q : c.source => coefficients C 0 c hc ω q I) q hq]
  exact coefficients_zero c hc ω ⟨q, hq⟩ I


private theorem scalar_lc_smooth (f : M → ℝ) (hf : IsLocallyConstant f) :
    PartitionData.ScalarSmooth S.smoothStructure.val f := by
  intro p
  apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ (f p) p)
  exact Filter.EventuallyEq.symm (hf.eventually_eq p)

private theorem dFunction_lc_zero (f : M → ℝ) (hf : IsLocallyConstant f)
    (hs : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) :
    dFunction S f hs p = 0 := by
  ext v
  change v.val (functionGerm S f hs p) = 0
  have heq : functionGerm S f hs p = algebraMap ℝ (SmoothGerm S p) (f p) := by
    apply Subtype.ext
    exact Germ.coe_eq.mpr ((IsLocallyConstant.iff_eventually_eq f).mp hf p)
  rw [heq]
  exact derivation_kills_constants _ v (f p)

private def closedOfLocallyConstant (K : Calculus C B) (f : LocallyConstant M ℝ) : K.closed 0 :=
  ⟨⟨FormPullbackData.scalarField S f,
    (K.mem_forms _ _).mpr (scalarField_lc_smooth f f.isLocallyConstant)⟩, by
      apply Subtype.ext
      funext p
      change K.D 0 (FormPullbackData.scalarField S f) p = 0
      rw [K.axioms.function_rule f (scalar_lc_smooth f f.isLocallyConstant),
        dFunction_lc_zero f f.isLocallyConstant]
      exact map_zero _⟩


private theorem scalar_locally_constant_of_dFunction_zero
    (C : CotangentBundle S) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f)
    (hdf : ∀ p, dFunction S f hf p = 0) : IsLocallyConstant f := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨F, ⟨U, hU, hpU, hF⟩, hFf⟩ :=
    exists_germChartExtension S p c hc hp (functionGerm S f hf p)
  have heq : (fun y => F (c y).val) =ᶠ[𝓝 p] f := Filter.Germ.coe_eq.mp hFf
  obtain ⟨V, hVe, hV, hpV⟩ := mem_nhds_iff.mp heq
  let W : Set (ModelSpace n a) := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.isOpen_inter_preimage_symm hV
  have hpW : c p ∈ W := ⟨c.map_source hp, by simpa only [mem_preimage, c.left_inv hp] using hpV⟩
  obtain ⟨W0, hW0, eW0⟩ := (isOpen_induced_iff (f := (Subtype.val : ModelSpace n a → Euclidean n))).mp hW
  have hpW0 : (c p).val ∈ W0 := by
    have : c p ∈ Subtype.val ⁻¹' W0 := by rw [eW0]; exact hpW
    exact this
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (hU.inter hW0) (c p).val ⟨hpU, hpW0⟩
  let Q : Set (Euclidean n) := Metric.ball (c p).val r ∩ modelSet n a
  have hQ : Convex ℝ Q := (convex_ball _ _).inter (convex_modelSet n a)
  have hD (z : Euclidean n) (hz : z ∈ Q) : fderiv ℝ F z = 0 := by
    have hzU : z ∈ U := (hrsub hz.1).1
    let z' : ModelSpace n a := ⟨z, hz.2⟩
    have hzW : z' ∈ W := by
      rw [← eW0]
      exact (hrsub hz.1).2
    have hzT : z' ∈ c.target := hzW.1
    have hzV : c.symm z' ∈ V := hzW.2
    have hcp : c (c.symm z') = z' := c.right_inv hzT
    have hcg : TangentData.GermChartExtension S (c.symm z') c
        (functionGerm S f hf (c.symm z')) F := by
      refine ⟨⟨U, hU, ?_, hF⟩, Filter.Germ.coe_eq.mpr ?_⟩
      · simpa only [hcp] using hzU
      · filter_upwards [hV.mem_nhds hzV] with y hy
        exact hVe hy
    have hcoord := (Covectors.differential_coordinates S C f hf c hc
      (c.symm z') (c.map_target hzT) F hcg).1
    apply ContinuousLinearMap.coe_injective
    have hhmap : (fderiv ℝ F z).toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin n)).ext
      intro j
      have hh := hcoord j
      rw [hdf] at hh
      simpa only [LinearMap.zero_apply, hcp, Pi.basisFun_apply,
        ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_zero, Pi.zero_apply] using hh.symm
    exact hhmap
  have hFD (z : Euclidean n) (hz : z ∈ Q) :
      HasFDerivWithinAt F (0 : Euclidean n →L[ℝ] ℝ) Q z := by
    have hzU := (hrsub hz.1).1
    have hdiff : DifferentiableAt ℝ F z :=
      (hF.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    simpa only [hD z hz] using hdiff.hasFDerivAt.hasFDerivWithinAt (s := Q)
  have hpQ : (c p).val ∈ Q := ⟨Metric.mem_ball_self hr, (c p).property⟩
  have hconst (z : Euclidean n) (hz : z ∈ Q) : F z = F (c p).val := by
    have hh := hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le hFD
      (C := 0) (by intro z hz; simp) hpQ hz
    have hh' : ‖F z - F (c p).val‖ = 0 := le_antisymm (by simpa using hh) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hh')
  have hball : ∀ᶠ y in 𝓝 p, (c y).val ∈ Metric.ball (c p).val r :=
    ((continuous_subtype_val.continuousAt.comp (c.continuousAt hp)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  filter_upwards [heq, hball] with y hy hyball
  rw [← hy]
  rw [hconst (c y).val ⟨hyball, (c y).property⟩]
  exact heq.self_of_nhds


private theorem closed_zeroCoefficient_lc (K : Calculus C B) (ω : K.closed 0) :
    IsLocallyConstant (zeroCoefficient ω.val.val) := by
  let f := zeroCoefficient ω.val.val
  have hs : PartitionData.ScalarSmooth S.smoothStructure.val f :=
    zeroCoefficient_smooth ω.val.val ((K.mem_forms _ _).mp ω.val.property)
  apply scalar_locally_constant_of_dFunction_zero C f hs
  intro p
  have heq : FormPullbackData.scalarField S f = ω.val.val := by
    funext q
    exact (exteriorPower.zeroEquiv ℝ _).symm_apply_apply _
  have hD : K.D 0 ω.val.val = 0 := congrArg Subtype.val ω.property
  have h := K.axioms.function_rule f hs p
  rw [heq, hD] at h
  have h' := congrArg (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) h
  simpa only [Pi.zero_apply, map_zero, LinearEquiv.apply_symm_apply] using h'.symm

private def closedZeroCoefficients (K : Calculus C B) : K.closed 0 →ₗ[ℝ] LocallyConstant M ℝ where
  toFun ω := ⟨zeroCoefficient ω.val.val, closed_zeroCoefficient_lc K ω⟩
  map_add' ω η := by
    apply LocallyConstant.ext
    intro p
    exact map_add (exteriorPower.zeroEquiv ℝ _) _ _
  map_smul' r ω := by
    apply LocallyConstant.ext
    intro p
    exact map_smul (exteriorPower.zeroEquiv ℝ _) r _

private def closedZeroEquiv (K : Calculus C B) : K.closed 0 ≃ₗ[ℝ] LocallyConstant M ℝ :=
  LinearEquiv.ofBijective (closedZeroCoefficients K) ⟨by
    intro ω η h
    apply Subtype.ext
    apply Subtype.ext
    funext p
    apply (exteriorPower.zeroEquiv ℝ _).injective
    exact congrArg (fun f : LocallyConstant M ℝ => f p) h,
    by
      intro f
      refine ⟨closedOfLocallyConstant K f, ?_⟩
      apply LocallyConstant.ext
      intro p
      exact (exteriorPower.zeroEquiv ℝ _).apply_symm_apply _⟩

private def classZeroEquiv (K : Calculus C B) : K.closed 0 ≃ₗ[ℝ] K.Cohomology 0 :=
  LinearEquiv.ofBijective (K.classOf 0) ⟨by
    intro ω η h
    have hz : (ω - η).val = 0 := (Submodule.Quotient.eq (K.boundaries 0)).mp h
    apply Subtype.ext
    exact sub_eq_zero.mp hz,
    (K.boundaries 0).mkQ_surjective⟩

private theorem h0_locally_constant_equiv (K : Calculus C B) :
    ∃ e : K.Cohomology 0 ≃ₗ[ℝ] LocallyConstant M ℝ,
      ∀ (ω : K.closed 0) (p : M), e (K.classOf 0 ω) p =
        exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω.val.val p) := by
  let e := (classZeroEquiv K).symm.trans (closedZeroEquiv K)
  refine ⟨e, ?_⟩
  intro ω p
  change closedZeroEquiv K ((classZeroEquiv K).symm (classZeroEquiv K ω)) p = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem h0_locally_constant_proof :
    Specs.SmoothManifolds.DeRham.Algebra.h0_locally_constantType.{u} := by
  intro n a M _ S C B K
  exact h0_locally_constant_equiv K


end H0

section ProductBuild
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

private theorem closed_ext' {k : ℕ} (α β : K.closed k)
    (h : α.val.val = β.val.val) : α = β := Subtype.ext (Subtype.ext h)

private def closedWedgeBilinear (k l : ℕ) : K.closed k →ₗ[ℝ] K.closed l →ₗ[ℝ] K.closed (k+l) where
  toFun α := {
    toFun := closedWedge K α
    map_add' := by
      intro β γ
      apply closed_ext' K
      funext p
      exact map_add (wedge (V := TangentSpace S p) (k := k) (l := l) (α.val.val p)) _ _
    map_smul' := by
      intro r β
      apply closed_ext' K
      funext p
      exact map_smul (wedge (V := TangentSpace S p) (k := k) (l := l) (α.val.val p)) r _ }
  map_add' := by
    intro α β
    apply LinearMap.ext
    intro γ
    apply closed_ext' K
    funext p
    exact congrArg (fun f => f (γ.val.val p)) (map_add (wedge (V := TangentSpace S p) (k := k) (l := l)) (α.val.val p) (β.val.val p))
  map_smul' := by
    intro r α
    apply LinearMap.ext
    intro β
    apply closed_ext' K
    funext p
    exact congrArg (fun f => f (β.val.val p)) (map_smul (wedge (V := TangentSpace S p) (k := k) (l := l)) r (α.val.val p))

private theorem form_cast_coe {k l : ℕ} (h : k = l) (α : K.forms k) (p : M) :
    ((cast (congrArg (fun j => ↥(K.forms j)) h) α).val p :
      ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = α.val p := by
  subst l
  rfl

private theorem closed_cast_coe {k l : ℕ} (h : k = l) (α : K.closed k) (p : M) :
    ((cast (congrArg (fun j => ↥(K.closed j)) h) α).val.val p :
      ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = α.val.val p := by
  subst l
  rfl

private theorem cast_form_exact {k l : ℕ} (h : k = l) (α : K.forms k)
    (hα : α ∈ K.exact k) :
    cast (congrArg (fun j => ↥(K.forms j)) h) α ∈ K.exact l := by
  subst l
  exact hα

private theorem cast_closed_boundary {k l : ℕ} (h : k = l) (α : K.closed k)
    (hα : α ∈ K.boundaries k) :
    cast (congrArg (fun j => ↥(K.closed j)) h) α ∈ K.boundaries l := by
  subst l
  exact hα

private theorem closedWedge_boundary_left {k l : ℕ} (α : K.closed k) (β : K.closed l)
    (hα : α ∈ K.boundaries k) : closedWedge K α β ∈ K.boundaries (k+l) := by
  cases k with
  | zero =>
    have hz : α.val = 0 := hα
    have he : closedWedge K α β = 0 := by
      apply closed_ext' K
      funext p
      change wedge (V := TangentSpace S p) (k := 0) (l := l) (α.val.val p) (β.val.val p) = 0
      have hz' := congrArg (fun z : K.forms 0 => z.val p) hz
      rw [hz']
      simp
    rw [he]
    exact Submodule.zero_mem _
  | succ k =>
    obtain ⟨ξ, hξ⟩ := hα
    let η := formWedge K ξ β.val
    let θ : K.forms (k+1+l) := cast
      (congrArg (fun j => ↥(K.forms j)) (by omega : k+l+1 = k+1+l)) (K.d (k+l) η)
    have hθ : θ = (closedWedge K α β).val := by
      apply Subtype.ext
      funext p
      apply Subtype.ext
      rw [form_cast_coe K (by omega : k+l+1 = k+1+l)]
      have hβ : K.D l β.val.val = 0 := congrArg Subtype.val β.property
      have hξ' : K.D k ξ.val = α.val.val := congrArg Subtype.val hξ
      change (K.D (k+l) (fieldWedge ξ.val β.val.val) p :
          ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
        (wedge (V := TangentSpace S p) (k := k+1) (l := l)
          (α.val.val p) (β.val.val p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p)))
      have h := K.axioms.leibniz k l ξ.val β.val.val
        ((K.mem_forms _ _).mp ξ.property) ((K.mem_forms _ _).mp β.val.property) p
      simpa only [hξ', hβ, Pi.zero_apply, map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero] using h
    have hb : θ ∈ K.exact (k+1+l) :=
      cast_form_exact K (by omega) (K.d (k+l) η) ⟨η, rfl⟩
    change (closedWedge K α β).val ∈ K.exact (k+1+l)
    rw [← hθ]
    exact hb

private theorem closedWedge_boundary_right {k l : ℕ} (α : K.closed k) (β : K.closed l)
    (hβ : β ∈ K.boundaries l) : closedWedge K α β ∈ K.boundaries (k+l) := by
  let θ : K.closed (k+l) := cast
    (congrArg (fun j => ↥(K.closed j)) (Nat.add_comm l k)) (closedWedge K β α)
  have he : closedWedge K α β = (-1 : ℝ)^(k*l) • θ := by
    apply closed_ext' K
    funext p
    apply Subtype.ext
    change (wedge (V := TangentSpace S p) (α.val.val p) (β.val.val p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      (-1 : ℝ)^(k*l) • (θ.val.val p :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p)))
    rw [closed_cast_coe K (Nat.add_comm l k)]
    exact ExteriorAlgebraResults.wedge_comm (TangentSpace S p) k l _ _
  rw [he]
  exact Submodule.smul_mem _ _ (cast_closed_boundary K (Nat.add_comm l k) _
    (closedWedge_boundary_left K β α hβ))

private def wedgeRightQ (k l : ℕ) (α : K.closed k) :
    K.Cohomology l →ₗ[ℝ] K.Cohomology (k+l) :=
  (K.boundaries l).liftQ ((K.classOf (k+l)).comp (closedWedgeBilinear K k l α)) (by
    intro β hβ
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (closedWedge_boundary_right K α β hβ))

private def wedgeLeftMap (k l : ℕ) :
    K.closed k →ₗ[ℝ] K.Cohomology l →ₗ[ℝ] K.Cohomology (k+l) where
  toFun := wedgeRightQ K k l
  map_add' := by
    intro α β
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro γ
    change K.classOf (k+l) (closedWedge K (α+β) γ) =
      K.classOf (k+l) (closedWedge K α γ) + K.classOf (k+l) (closedWedge K β γ)
    rw [← map_add]
    apply congrArg (K.classOf (k+l))
    exact congrArg (fun z => z γ) (map_add (closedWedgeBilinear K k l) α β)
  map_smul' := by
    intro r α
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro β
    change K.classOf (k+l) (closedWedge K (r • α) β) =
      r • K.classOf (k+l) (closedWedge K α β)
    rw [← map_smul]
    apply congrArg (K.classOf (k+l))
    exact congrArg (fun z => z β) (map_smul (closedWedgeBilinear K k l) r α)

private def cohomWedge (k l : ℕ) :
    K.Cohomology k →ₗ[ℝ] K.Cohomology l →ₗ[ℝ] K.Cohomology (k+l) :=
  (K.boundaries k).liftQ (wedgeLeftMap K k l) (by
    intro α hα
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro β
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (closedWedge_boundary_left K α β hα))

private theorem cohomWedge_representatives (k l : ℕ) (α : K.closed k) (β : K.closed l) :
    cohomWedge K k l (K.classOf k α) (K.classOf l β) =
      K.classOf (k+l) (closedWedge K α β) := rfl

private theorem cast_class {k l : ℕ} (h : k = l) (α : K.closed k) :
    cast (congrArg (fun j => K.Cohomology j) h) (K.classOf k α) =
      K.classOf l (cast (congrArg (fun j => ↥(K.closed j)) h) α) := by
  subst l
  rfl

private theorem cohomWedge_assoc (k l m : ℕ)
    (x : K.Cohomology k) (y : K.Cohomology l) (z : K.Cohomology m) :
    cast (congrArg (fun j => K.Cohomology j) (Nat.add_assoc k l m))
      (cohomWedge K (k+l) m (cohomWedge K k l x y) z) =
        cohomWedge K k (l+m) x (cohomWedge K l m y z) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  refine Submodule.Quotient.induction_on _ y ?_
  intro β
  refine Submodule.Quotient.induction_on _ z ?_
  intro γ
  change cast _ (K.classOf ((k+l)+m) (closedWedge K (closedWedge K α β) γ)) =
    K.classOf (k+(l+m)) (closedWedge K α (closedWedge K β γ))
  rw [cast_class K (Nat.add_assoc k l m)]
  apply congrArg (K.classOf _)
  apply closed_ext' K
  funext p
  apply Subtype.ext
  rw [closed_cast_coe K (Nat.add_assoc k l m)]
  exact ExteriorAlgebraResults.wedge_assoc (TangentSpace S p) k l m _ _ _

private theorem cohomWedge_comm (k l : ℕ) (x : K.Cohomology k) (y : K.Cohomology l) :
    cohomWedge K k l x y = (-1 : ℝ)^(k*l) •
      cast (congrArg (fun j => K.Cohomology j) (Nat.add_comm l k)) (cohomWedge K l k y x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro α
  refine Submodule.Quotient.induction_on _ y ?_
  intro β
  change K.classOf (k+l) (closedWedge K α β) =
    (-1 : ℝ)^(k*l) • cast _ (K.classOf (l+k) (closedWedge K β α))
  rw [cast_class K (Nat.add_comm l k), ← map_smul]
  apply congrArg (K.classOf _)
  apply closed_ext' K
  funext p
  apply Subtype.ext
  change (wedge (V := TangentSpace S p) (α.val.val p) (β.val.val p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      (-1 : ℝ)^(k*l) • _
  rw [closed_cast_coe K (Nat.add_comm l k)]
  exact ExteriorAlgebraResults.wedge_comm (TangentSpace S p) k l _ _

private theorem scalar_one_coe (p : M) :
    (FormPullbackData.scalarField S (fun _ => 1) p :
      ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = 1 := by
  have he : FormPullbackData.scalarField S (fun _ => 1) p =
      exteriorPower.ιMulti ℝ 0 (Fin.elim0) := by
    apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
    simp [FormPullbackData.scalarField]
  rw [he]
  exact ExteriorAlgebra.ιMulti_zero_apply _

private theorem product_from_unit (ε : K.closed 0)
    (hε : ε.val.val = FormPullbackData.scalarField S (fun _ => 1)) :
    ∃ P : K.GradedProduct, K.IsGradedProduct P := by
  let P : K.GradedProduct := {
    mul := fun k l x y => cohomWedge K k l x y
    one := K.classOf 0 ε }
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k l x y z
    exact congrArg (fun f => f z) (map_add (cohomWedge K k l) x y)
  · intro k l x y z
    exact map_add (cohomWedge K k l x) y z
  · intro k l r x y
    exact congrArg (fun f => f y) (map_smul (cohomWedge K k l) r x)
  · intro k l r x y
    exact map_smul (cohomWedge K k l x) r y
  · intro k l α β
    exact ⟨closedWedge K α β, rfl, rfl⟩
  · exact ⟨ε, hε, rfl⟩
  · exact cohomWedge_assoc K
  · exact cohomWedge_comm K
  · intro k x
    refine Submodule.Quotient.induction_on _ x ?_
    intro α
    change cast _ (K.classOf (0+k) (closedWedge K ε α)) = K.classOf k α
    rw [cast_class K (Nat.zero_add k)]
    apply congrArg (K.classOf k)
    apply closed_ext' K
    funext p
    apply Subtype.ext
    rw [closed_cast_coe K (Nat.zero_add k)]
    change (wedge (V := TangentSpace S p) (ε.val.val p) (α.val.val p) :
      ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = _
    change (ε.val.val p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) *
      (α.val.val p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = _
    rw [hε, scalar_one_coe, one_mul]
  · intro k x
    refine Submodule.Quotient.induction_on _ x ?_
    intro α
    change K.classOf k (closedWedge K α ε) = K.classOf k α
    apply congrArg (K.classOf k)
    apply closed_ext' K
    funext p
    apply Subtype.ext
    change (α.val.val p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) *
      (ε.val.val p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = _
    rw [hε, scalar_one_coe, mul_one]

end ProductBuild

private theorem product_exists_proof :
    Specs.SmoothManifolds.DeRham.Algebra.product_existsType.{u} := by
  intro n a M _ S C B K
  exact product_from_unit K
    (closedOfLocallyConstant K (LocallyConstant.const M (1 : ℝ))) rfl

private def componentPull {M : Type u} [TopologicalSpace M] [LocallyConnectedSpace M] :
    (ConnectedComponents M → ℝ) →ₗ[ℝ] LocallyConstant M ℝ where
  toFun f := ⟨fun p => f (ConnectedComponents.mk p), by
    exact (IsLocallyConstant.of_discrete f).comp_continuous
      ConnectedComponents.continuous_coe⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem componentPull_bijective {M : Type u} [TopologicalSpace M]
    [LocallyConnectedSpace M] : Function.Bijective (componentPull (M := M)) := by
  constructor
  · intro f g h
    funext c
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg (fun h : LocallyConstant M ℝ => h p) h
  · intro f
    let g : ConnectedComponents M → ℝ := Quotient.lift (f : M → ℝ) (by
      intro x y h
      exact f.isLocallyConstant.apply_eq_of_isPreconnected
        isPreconnected_connectedComponent mem_connectedComponent
        (h ▸ mem_connectedComponent))
    exact ⟨g, LocallyConstant.ext (fun _ => rfl)⟩

private theorem h0_components_proof
    (hzero : Specs.SmoothManifolds.DeRham.Algebra.h0_locally_constantType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.h0_componentsType.{u} := by
  intro n a M _ S C B K
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  obtain ⟨e, _⟩ := hzero K
  exact ⟨e.trans (LinearEquiv.ofBijective componentPull componentPull_bijective).symm⟩

private def constantEquiv {M : Type u} [TopologicalSpace M] [ConnectedSpace M] :
    LocallyConstant M ℝ ≃ₗ[ℝ] ℝ where
  toFun f := f (Classical.arbitrary M)
  invFun r := LocallyConstant.const M r
  left_inv f := LocallyConstant.ext (fun p =>
    f.isLocallyConstant.apply_eq_of_preconnectedSpace _ p)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem h0_connected_proof
    (hzero : Specs.SmoothManifolds.DeRham.Algebra.h0_locally_constantType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.h0_connectedType.{u} := by
  intro n a M _ _ S C B K
  obtain ⟨e, _⟩ := hzero K
  exact ⟨e.trans constantEquiv⟩

theorem complex_exists_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.complex_existsType.{u} :=
  complex_exists_proof h41 h42 h33

theorem square_zero_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.square_zeroType.{u} :=
  square_zero_proof

theorem exact_closed_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.exact_closedType.{u} :=
  exact_closed_proof

theorem class_zero_iff_exact_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.class_zero_iff_exactType.{u} :=
  class_zero_iff_exact_proof

theorem above_dimension_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.above_dimensionType.{u} :=
  above_dimension_proof

theorem negative_degrees_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.negative_degreesType.{u} :=
  negative_degrees_proof

theorem empty_cohomology_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.empty_cohomologyType.{u} :=
  empty_cohomology_proof

theorem pullback_exists_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_existsType.{u} :=
  pullback_exists_proof h43

theorem pullback_id_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_idType.{u} :=
  pullback_id_proof

theorem pullback_comp_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_compType.{u} :=
  pullback_comp_proof

theorem pullback_product_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.pullback_productType.{u} :=
  pullback_product_proof

theorem h0_locally_constant_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.h0_locally_constantType.{u} :=
  h0_locally_constant_proof

theorem h0_components_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.h0_componentsType.{u} :=
  h0_components_proof h0_locally_constant_proof

theorem h0_connected_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.h0_connectedType.{u} :=
  h0_connected_proof h0_locally_constant_proof

theorem product_exists_conditional
    (h0 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_coefficient_leibnizType)
    (h1 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_leibnizType.{u})
    (h2 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coefficient_alternating_bridgeType)
    (h3 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.intrinsic_derivative_squareType.{u})
    (h4 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType)
    (h5 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType)
    (h6 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType)
    (h7 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType)
    (h8 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_localityType.{u})
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_supportType.{u})
    (h10 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_uniqueType.{u})
    (h11 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.axioms_zero_germType.{u})
    (h12 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_continuousType.{u})
    (h13 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u})
    (h14 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_section_continuousType.{u})
    (h15 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u})
    (h16 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_restrictionType.{u})
    (h17 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u})
    (h18 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u})
    (h19 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.continuous_field_section_iffType.{u})
    (h20 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_derivative_pullbackType.{u})
    (h21 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u})
    (h22 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u})
    (h23 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_addType.{u})
    (h24 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u})
    (h25 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u})
    (h26 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_regularType.{u})
    (h27 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smoothType.{u})
    (h28 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_smulType.{u})
    (h29 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u})
    (h30 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u})
    (h31 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType)
    (h32 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u})
    (h33 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u})
    (h34 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType)
    (h35 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extDerivWithin_pullbackType)
    (h36 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType)
    (h37 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u})
    (h38 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_regularType.{u})
    (h39 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u})
    (h40 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u})
    (h41 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u})
    (h42 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u})
    (h43 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_naturalityType.{u})
    (h44 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_regularType.{u})
    (h45 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u})
    (h46 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType)
    (h47 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u})
    (h48 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u})
    (h49 : Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u}) :
    Specs.SmoothManifolds.DeRham.Algebra.product_existsType.{u} :=
  product_exists_proof

end SmoothManifolds.DeRhamResults

universe v8_closure_24eda128901457f8_u0
theorem _root_.«SmoothManifolds».«DeRhamResults».«above_dimension» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«above_dimensionType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«above_dimension_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«class_zero_iff_exact» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«class_zero_iff_exactType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«class_zero_iff_exact_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«complex_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«complex_existsType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«complex_exists_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«empty_cohomology» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«empty_cohomologyType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«empty_cohomology_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«exact_closed» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«exact_closedType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«exact_closed_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«h0_components» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«h0_componentsType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«h0_components_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«h0_connected» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«h0_connectedType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«h0_connected_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«h0_locally_constant» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«h0_locally_constantType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«h0_locally_constant_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«negative_degrees» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«negative_degreesType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«negative_degrees_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«product_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«product_existsType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«product_exists_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«pullback_comp» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«pullback_compType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«pullback_comp_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«pullback_exists» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«pullback_existsType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«pullback_exists_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«pullback_id» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«pullback_idType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«pullback_id_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«pullback_product» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«pullback_productType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«pullback_product_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
theorem _root_.«SmoothManifolds».«DeRhamResults».«square_zero» : _root_.«Specs».«SmoothManifolds».«DeRham».«Algebra».«square_zeroType».{v8_closure_24eda128901457f8_u0} :=
  @_root_.«SmoothManifolds».«DeRhamResults».«square_zero_conditional».{v8_closure_24eda128901457f8_u0} (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«coordinate_derivative_leibniz») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«CoefficientCalculus».«intrinsic_derivative_leibniz».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«coefficient_alternating_bridge») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«Euclidean».«intrinsic_derivative_square».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_continuous») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_derivative_square») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_dimension_zero») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«ambient_naturality») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«axioms_zero_germ».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_derivative_section_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«c1_restriction».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_embedding_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«closed_face_inclusion_proper».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«continuous_field_section_iff».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_derivative_pullback».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_formula_extension».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«coordinate_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_add».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_locality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smooth».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_smul».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«derivative_unique».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«function_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«global_coordinates».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«model_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extDerivWithin_pullback») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«orthant_extension_independence») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«proper_pullback_compact_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«pullback_support».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«regular_continuous».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_coefficients».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_family_exists».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_naturality».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«smooth_regular».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«tautological_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«uniqueDiffOn_orthant») (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_derivative».{v8_closure_24eda128901457f8_u0}) (@_root_.«SmoothManifolds».«ExteriorDerivativeResults».«zero_dim_family_exists».{v8_closure_24eda128901457f8_u0})
