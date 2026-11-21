import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.HomotopyInvariance
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.SmoothingHomotopies

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyOperator
/-! Conditional derivation of the cohomological conclusions of M11.02.
Only the full, frozen homotopy-operator proposition is a conditional premise.
Original closed targets are reserved for the owner's dependency closure. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SmoothManifolds.HomotopyResults
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData HomotopyData
  InteriorHomotopyData Set Filter
open scoped Topology
universe u
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations

/-- When coordinates induce the topology, an extension of a germ can be
shrunk to agree everywhere on a relative coordinate neighborhood. -/
private theorem extension_of_inducing {X : Type u} [TopologicalSpace X] {n m : ℕ}
    {ι : X → Euclidean n} {f : X → Euclidean m} {x : X}
    (hι : Topology.IsInducing ι)
    (h : LocalCoordinateExtension (⊤ : ℕ∞) ι f x) :
    HasLocalContDiffExtensionAt (⊤ : ℕ∞) ι f x := by
  obtain ⟨U, hU, hxU, g, hg, he⟩ := h
  rw [hι.nhds_eq_comap] at he
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (Filter.eventually_comap.mp he)
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, g, hg.mono inter_subset_left, ?_⟩
  intro y hy
  exact hVsub hy.2 y rfl

/-- The chart coordinates together with time induce the topology of every
restricted cylinder chart, including its spatial and temporal faces. -/
private theorem cylinder_coordinates_inducing {n m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (c : ModelChart n a M) (d : ModelChart m b N) (F : M × UnitInterval → N) :
    Topology.IsInducing
      (fun z : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source} =>
        @Fin.snoc n (fun _ => ℝ) (c z.val.1).val z.val.2.val) := by
  let X := {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source}
  let j : X → c.source × UnitInterval := fun z => (⟨z.val.1, z.property.1⟩, z.val.2)
  have hj : Continuous j :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  have hji : Topology.IsInducing j := Topology.IsInducing.of_comp hj
    (continuous_subtype_val.prodMap continuous_id) Topology.IsInducing.subtypeVal
  have hc : Topology.IsInducing (fun p : c.source => (c p.val).val) :=
    Topology.IsInducing.subtypeVal.comp c.isEmbedding_restrict.isInducing
  have hp := hc.prodMap (Topology.IsInducing.subtypeVal (t := Icc (0 : ℝ) 1))
  let sn : Euclidean n × ℝ → Euclidean (n+1) := fun z => Fin.snoc z.1 z.2
  have hs : Continuous sn := Continuous.finSnoc (A := fun _ : Fin (n+1) => ℝ) continuous_fst continuous_snd
  have hr : Continuous (fun z : Euclidean (n+1) => (Fin.init z, z (Fin.last n))) :=
    continuous_id.finInit.prodMk (continuous_apply _)
  have hsn : Topology.IsInducing sn := Topology.IsInducing.of_comp hs hr (by
    convert (Topology.IsInducing.id (X := Euclidean n × ℝ)) using 1
    funext z
    simp [sn])
  exact hsn.comp (hp.comp hji)

/-- Reordering time from first to last and passing from germs to relative
extensions connects the independently specified smoothing and operator APIs. -/
private theorem smooth_cylinder {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {H : HomotopyTime × M → N}
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H) :
    IsSmoothHomotopy S T (fun z => H (z.2, z.1)) := by
  refine ⟨hH.1.comp (continuous_snd.prodMk continuous_fst), ?_⟩
  intro c hc d hd z
  let ι := fun w : {q : M × UnitInterval | q.1 ∈ c.source ∧ H (q.2,q.1) ∈ d.source} =>
    @Fin.snoc n (fun _ => ℝ) (c w.val.1).val w.val.2.val
  have h := LocalCoordinateExtension.precomp
    (hH.2 c hc d hd (z.val.2, z.val.1) z.property.1 z.property.2)
    ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).continuousAt rfl
  have hr : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Euclidean (n+1) => @Fin.cons n (fun _ => ℝ) (y (Fin.last n)) (Fin.init y)) := by
    apply contDiff_pi.mpr
    intro i
    cases i using Fin.cases with
    | zero => simpa using contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (Fin.last n)
    | succ j => simpa [Fin.init] using contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) j.castSucc
  have hi : LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun w => Fin.cons w.val.2.val (c w.val.1).val) z := by
    refine ⟨univ, isOpen_univ, mem_univ _, _, hr.contDiffOn, ?_⟩
    exact Eventually.of_forall (fun w => by simp [ι])
  exact extension_of_inducing
    (cylinder_coordinates_inducing c d (fun q => H (q.2,q.1)))
    (LocalCoordinateExtension.comp h hi)


section Pullbacks
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {A : CotangentBundle T} {E : ∀ k, FormBundle A k}

private theorem pullback_congr (f g : M → N) (he : f = g)
    (hg : IsSmoothMap S T g)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (R : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (g p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (hR : ∀ p, IsDifferential S T g p (R p))
    {k : ℕ} (ω : Field T k) :
    FormPullbackData.pullbackField S T f L ω =
      FormPullbackData.pullbackField S T g R ω := by
  subst g
  have hLR : L = R := by
    funext p
    obtain ⟨Q, hQ, hu⟩ := differential_exists S T f hg p
    exact (hu (L p) (hL p)).trans (hu (R p) (hR p)).symm
  rw [hLR]

private theorem smooth_homotopy_pullbacks
    (hoperator : Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u})
    (K : Calculus C B) (J : Calculus A E) (f₀ f₁ : M → N)
    (hf₀ : IsSmoothMap S T f₀) (hf₁ : IsSmoothMap S T f₁)
    (H : HomotopyTime × M → N)
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    (hH0 : ∀ p, H (timeZero,p) = f₀ p) (hH1 : ∀ p, H (timeOne,p) = f₁ p)
    (L₀ : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f₀ p))
    (L₁ : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f₁ p))
    (hL₀ : ∀ p, IsDifferential S T f₀ p (L₀ p))
    (hL₁ : ∀ p, IsDifferential S T f₁ p (L₁ p))
    (P₀ P₁ : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k)
    (hP₀ : IsCohomologyPullback C B K J f₀ L₀ P₀)
    (hP₁ : IsCohomologyPullback C B K J f₁ L₁ P₁) : ∀ k, P₀ k = P₁ k := by
  obtain ⟨D, op, _, hchain, _⟩ := hoperator S T C B A E K J
    (fun z => H (z.2,z.1)) (smooth_cylinder S T hH)
  have hα₀ {k : ℕ} (ω : Field T k) : alpha D ω initialTime =
      FormPullbackData.pullbackField S T f₀ L₀ ω :=
    pullback_congr _ _ (funext hH0) hf₀ _ _ (D.spatial_correct initialTime) hL₀ ω
  have hα₁ {k : ℕ} (ω : Field T k) : alpha D ω finalTime =
      FormPullbackData.pullbackField S T f₁ L₁ ω :=
    pullback_congr _ _ (funext hH1) hf₁ _ _ (D.spatial_correct finalTime) hL₁ ω
  intro k
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro ω
  obtain ⟨β₀, hβ₀, e₀⟩ := hP₀ k ω
  obtain ⟨β₁, hβ₁, e₁⟩ := hP₁ k ω
  change P₀ k (J.classOf k ω) = P₁ k (J.classOf k ω)
  rw [e₀, e₁]
  cases k with
  | zero =>
    have hd : J.d 0 ω.val = 0 := ω.property
    have hh := hchain.2 ω.val
    simp only [hd, map_zero, Submodule.coe_zero] at hh
    have heq : β₁.val.val = β₀.val.val := by
      apply sub_eq_zero.mp
      exact (congrArg₂ (fun x y : Field S 0 => x-y)
        (hβ₁.trans (hα₁ ω.val.val).symm)
        (hβ₀.trans (hα₀ ω.val.val).symm)).trans hh.symm
    exact congrArg (K.classOf 0) (Subtype.ext (Subtype.ext heq.symm))
  | succ k =>
    have hd : J.d (k+1) ω.val = 0 := ω.property
    have hh := hchain.1 k ω.val
    simp only [hd, map_zero, Submodule.coe_zero, add_zero] at hh
    have he : β₁.val - β₀.val ∈ K.exact (k+1) := by
      refine ⟨op k ω.val, ?_⟩
      apply Subtype.ext
      change (K.d k (op k ω.val)).val = β₁.val.val - β₀.val.val
      exact hh.trans (congrArg₂ (fun x y : Field S (k+1) => x-y)
        ((hα₁ ω.val.val).trans hβ₁.symm)
        ((hα₀ ω.val.val).trans hβ₀.symm))
    have hz := (DeRhamResults.class_zero_iff_exact K (k+1) (β₁-β₀)).mpr he
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm

end Pullbacks

/-- The original theorem, derived conditionally from the entire smooth
homotopy-operator statement with the exact supplied premise. -/
theorem homotopy_invariance_conditional
    (hoperator : Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u}) :
    Specs.SmoothManifolds.DeRham.HomotopyInvariance.homotopy_invarianceType.{u} := by
  intro n m a b M N _ _ S T C B A E K J f₀ f₁ hf₀ hf₁ hH L₀ L₁ hL₀ hL₁ P₀ P₁ hP₀ hP₁
  obtain ⟨H, hH, hH0, hH1⟩ :=
    SmoothingHomotopies.continuous_homotopy_smoothing S T f₀ f₁ hf₀ hf₁ hH
  exact smooth_homotopy_pullbacks hoperator K J f₀ f₁ hf₀ hf₁ H hH hH0 hH1
    L₀ L₁ hL₀ hL₁ P₀ P₁ hP₀ hP₁


section Contractions
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
  (K : Calculus C B)

private theorem constant_smooth (q : M) : IsSmoothMap S S (fun _ : M => q) := by
  intro p
  refine ⟨continuousAt_const, ?_⟩
  intro c hc d hd hp hq
  exact ⟨univ, isOpen_univ, mem_univ _, fun _ => (d q).val,
    contDiffOn_const, Eventually.of_forall (fun _ => rfl)⟩

private theorem constant_differential (q p : M) :
    IsDifferential S S (fun _ : M => q) p
      (0 : TangentSpace S p →ₗ[ℝ] TangentSpace S q) := by
  intro v h k r hr hk
  have hk' : k = algebraMap ℝ (SmoothGerm S p) (r q) := Subtype.ext hk.symm
  rw [hk', derivation_kills_constants]
  rfl

include C in
private theorem constant_pullback_zero (q : M) (k : ℕ) (ω : Field S (k+1)) :
    FormPullbackData.pullbackField S S (fun _ : M => q) (fun _ => 0) ω = 0 := by
  funext p
  apply (CartanData.evaluationEquiv C.tangent.fiberCoordinates p (k+1)).injective
  change evaluate (TangentSpace S p) (k+1)
    (FormPullbackData.pullbackField S S (fun _ : M => q) (fun _ => 0) ω p) =
    evaluate (TangentSpace S p) (k+1) 0
  rw [map_zero]
  apply AlternatingMap.ext
  intro v
  rw [FormPullbackResults.pullback_apply]
  exact (evaluate (TangentSpace S q) (k+1) (ω q)).map_coord_zero 0 rfl

private theorem constant_cohomology_zero (q : M)
    (P : ∀ k, K.Cohomology k →ₗ[ℝ] K.Cohomology k)
    (hP : IsCohomologyPullback C B K K (fun _ : M => q) (fun _ => 0) P)
    (k : ℕ) (x : K.Cohomology (k+1)) : P (k+1) x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro ω
  obtain ⟨β, hβ, he⟩ := hP (k+1) ω
  have hβ0 : β = 0 := Subtype.ext (Subtype.ext
    (hβ.trans (constant_pullback_zero S C q k ω.val.val)))
  change P (k+1) (K.classOf (k+1) ω) = 0
  rw [he, hβ0, map_zero]

end Contractions

/-- Continuous contractions give vanishing in all positive degrees. -/
theorem contractible_vanishing_conditional
    (hoperator : Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u}) :
    Specs.SmoothManifolds.DeRham.HomotopyInvariance.contractible_vanishingType.{u} := by
  intro n a M _ _ _ S C B K k hk
  obtain ⟨q, ⟨H⟩⟩ := id_nullhomotopic M
  have hid : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1
  have hq := constant_smooth S q
  obtain ⟨P, hP⟩ := DeRhamResults.pullback_exists S S C C B B K K
    (fun _ : M => q) hq (fun _ => 0) (constant_differential S q)
  have hId : IsCohomologyPullback C B K K id (fun p => LinearMap.id) (fun _ => LinearMap.id) := by
    intro j ω
    exact ⟨ω, (FormPullbackResults.pullback_id S _ (differential_id S) j ω.val.val).symm, rfl⟩
  have hEq := homotopy_invariance_conditional hoperator S S C B C B K K
    id (fun _ : M => q) hid hq
    ⟨H, H.continuous_toFun, H.map_zero_left, H.map_one_left⟩
    (fun p => LinearMap.id) (fun _ => 0) (differential_id S)
    (constant_differential S q) (fun _ => LinearMap.id) P hId hP
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hz (x : K.Cohomology (j+1)) : x = 0 := by
    calc x = P (j+1) x := congrArg (fun L => L x) (hEq (j+1))
         _ = 0 := constant_cohomology_zero S C B K q P hP j x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Poincaré exactness on star-shaped open Euclidean domains, in any linear
coordinates. Membership in the exact submodule provides a smooth primitive. -/
theorem poincare_lemma_conditional
    (hoperator : Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u}) :
    Specs.SmoothManifolds.DeRham.HomotopyInvariance.poincare_lemmaType.{u} := by
  intro n V _ _ coordinates U hU q hq hstar S C B K k hk ω
  have : ContractibleSpace U := hstar.contractibleSpace ⟨q, hq⟩
  have : Nonempty U := ⟨⟨q, hq⟩⟩
  have := contractible_vanishing_conditional hoperator S C B K k hk
  exact (DeRhamResults.class_zero_iff_exact K k ω).mp (Subsingleton.elim _ _)

end SmoothManifolds.HomotopyResults

universe v8_closure_754cd3a4cf6fbbce_u0
theorem _root_.«SmoothManifolds».«HomotopyResults».«contractible_vanishing» : _root_.«Specs».«SmoothManifolds».«DeRham».«HomotopyInvariance».«contractible_vanishingType».{v8_closure_754cd3a4cf6fbbce_u0} :=
  @_root_.«SmoothManifolds».«HomotopyResults».«contractible_vanishing_conditional».{v8_closure_754cd3a4cf6fbbce_u0} (@_root_.«SmoothManifolds».«HomotopyResults».«homotopy_operator».{v8_closure_754cd3a4cf6fbbce_u0})
theorem _root_.«SmoothManifolds».«HomotopyResults».«homotopy_invariance» : _root_.«Specs».«SmoothManifolds».«DeRham».«HomotopyInvariance».«homotopy_invarianceType».{v8_closure_754cd3a4cf6fbbce_u0} :=
  @_root_.«SmoothManifolds».«HomotopyResults».«homotopy_invariance_conditional».{v8_closure_754cd3a4cf6fbbce_u0} (@_root_.«SmoothManifolds».«HomotopyResults».«homotopy_operator».{v8_closure_754cd3a4cf6fbbce_u0})
theorem _root_.«SmoothManifolds».«HomotopyResults».«poincare_lemma» : _root_.«Specs».«SmoothManifolds».«DeRham».«HomotopyInvariance».«poincare_lemmaType».{v8_closure_754cd3a4cf6fbbce_u0} :=
  @_root_.«SmoothManifolds».«HomotopyResults».«poincare_lemma_conditional».{v8_closure_754cd3a4cf6fbbce_u0} (@_root_.«SmoothManifolds».«HomotopyResults».«homotopy_operator».{v8_closure_754cd3a4cf6fbbce_u0})
