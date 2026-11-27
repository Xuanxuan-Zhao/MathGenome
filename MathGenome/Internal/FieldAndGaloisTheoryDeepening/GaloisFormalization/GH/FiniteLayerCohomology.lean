import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteLayerCohomology
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteCochainDescent

/-! Finite-layer comparison for abelian Galois cohomology. -/

namespace GaloisFormalization.GH.FiniteLayerCohomology

open Specs.GaloisFormalization.GH.FiniteLayerCohomology

universe u v w

noncomputable section

abbrev LayerCoefficients := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.LayerCoefficients
abbrev layerAction := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.layerAction
abbrev includeCoefficients := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.includeCoefficients
abbrev LayerH := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.LayerH
abbrev stageTransition := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.stageTransition
abbrev stageClass := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.stageClass
abbrev inflateCocycle := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.inflateCocycle
abbrev LayerLimit := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.LayerLimit
abbrev limitOf := @Specs.GaloisFormalization.GH.FiniteLayerCohomology.limitOf

theorem inflateCocycle_apply : InflationFormula.{u,v,w} := by
  intro k L _ _ _ _ M _ _ E _ _ _ q c g
  rfl

theorem stageClass_surjective : StageClassesSurjective.{u,v,w} := by
  intro k L _ _ _ _ M _ _ E _ _ q a
  let e := ordinaryCohomologyEquiv.{v,w,0} (KrullLayers.LayerGroup E) (LayerCoefficients M E) q
  obtain ⟨c, hc⟩ := continuousClass_surjective q (e.symm a)
  exact ⟨c, (ordinaryCohomologyEquiv_class.{v,w,0} _ _ q c).symm.trans
    ((congrArg e hc).trans (e.apply_symm_apply a))⟩

set_option backward.isDefEq.respectTransparency false

section Stages

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable {M : Type w} [AddCommGroup M] [DistribMulAction Gal(L/k) M]
variable [TopologicalSpace M] [DiscreteTopology M]
variable {E F D : FiniteGaloisIntermediateField k L} {q : ℕ}

open KrullLayers

private abbrev LayerCochains (M : Type w) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction Gal(L/k) M]
    (E : FiniteGaloisIntermediateField k L) (q : ℕ) :=
  continuousCochains (LayerGroup E) (LayerCoefficients M E) q

private abbrev LayerCocycles (M : Type w) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction Gal(L/k) M]
    (E : FiniteGaloisIntermediateField k L) (q : ℕ) :=
  continuousCocycles (LayerGroup E) (LayerCoefficients M E) q

private def transitionCochain (h : E ≤ F) (q : ℕ) :
    LayerCochains M E q →ₗ[ℤ] LayerCochains M F q :=
  continuousCochainMap (transition h).toMonoidHom (transition h).continuous
    (includeCoefficients M h) q

private def transitionCocycle (h : E ≤ F) (q : ℕ) :
    LayerCocycles M E q →ₗ[ℤ] LayerCocycles M F q :=
  continuousCocycleMap (transition h).toMonoidHom (transition h).continuous
    (includeCoefficients M h) (includeCoefficients_equivariant M h) q

private theorem stageTransition_class (h : E ≤ F) (c : LayerCocycles M E q) :
    stageTransition M E F q h (stageClass M E q c) =
      stageClass M F q (transitionCocycle h q c) := by
  have hmap := (ordinaryCohomologyEquiv_map.{v,w,0,v,w} (transition h).toMonoidHom
    (transition h).continuous (includeCoefficients M h) (includeCoefficients_equivariant M h)
    q (continuousClass (LayerGroup E) (LayerCoefficients M E) q c)).symm
  simp only [Model.continuousCohomologyMap_class, ordinaryCohomologyEquiv_class] at hmap
  exact hmap

private theorem transitionCocycle_refl (c : LayerCocycles M E q) :
    transitionCocycle (le_refl E) q c = c := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  change (c.val.val (fun j => transition (le_refl E) (g j)) : M) = (c.val.val g : M)
  rw [transition_refl]
  rfl

private theorem transitionCocycle_comp (hEF : E ≤ F) (hFD : F ≤ D)
    (c : LayerCocycles M E q) :
    transitionCocycle hFD q (transitionCocycle hEF q c) =
      transitionCocycle (hEF.trans hFD) q c := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply Subtype.ext
  change (c.val.val (fun j => transition hEF (transition hFD (g j))) : M) =
    (c.val.val (fun j => transition (hEF.trans hFD) (g j)) : M)
  have hcomp (x : LayerGroup D) :
      transition hEF (transition hFD x) = transition (hEF.trans hFD) x :=
    (DFunLike.congr_fun (transition_comp hEF hFD) x).symm
  exact congrArg (fun t : Fin q → LayerGroup E => (c.val.val t : M))
    (funext fun j => hcomp (g j))

end Stages

theorem directedTransitions : DirectedTransitions.{u,v,w} := by
  intro k L _ _ _ _ M _ _ q
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  constructor
  · intro E a
    obtain ⟨c, rfl⟩ := stageClass_surjective M E q a
    rw [stageTransition_class, transitionCocycle_refl]
  · intro D F E hEF hFD a
    obtain ⟨c, rfl⟩ := stageClass_surjective M E q a
    rw [stageTransition_class, stageTransition_class, stageTransition_class,
      transitionCocycle_comp]

section Inflation

open KrullLayers

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable {M : Type w} [AddCommGroup M] [DistribMulAction Gal(L/k) M]
variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul Gal(L/k) M]
variable {E F : FiniteGaloisIntermediateField k L} {q : ℕ}

private def inflateCochain (E : FiniteGaloisIntermediateField k L) (q : ℕ) :
    LayerCochains M E q →ₗ[ℤ] continuousCochains Gal(L/k) M q :=
  continuousCochainMap (restrict E).toMonoidHom (restrict E).continuous
    (LayerCoefficients M E).subtype.toAddMonoidHom q

omit [ContinuousSMul Gal(L/k) M] in
private theorem inflateCochain_injective (E : FiniteGaloisIntermediateField k L) (q : ℕ) :
    Function.Injective (inflateCochain (M := M) E q) := by
  intro a b hab
  apply Subtype.ext
  funext t
  choose g hg using fun j => restrict_surjective E (t j)
  have h := congrArg (fun c : continuousCochains Gal(L/k) M q => c.val g) hab
  apply Subtype.ext
  change (a.val (fun j => restrict E (g j)) : M) =
    (b.val (fun j => restrict E (g j)) : M) at h
  rw [show (fun j => restrict E (g j)) = t from funext hg] at h
  exact h

omit [IsGalois k L] [ContinuousSMul Gal(L/k) M] in
private theorem inflateCochain_transition (h : E ≤ F) (c : LayerCochains M E q) :
    inflateCochain (M := M) F q (transitionCochain h q c) = inflateCochain (M := M) E q c := by
  apply Subtype.ext
  funext g
  change (c.val (fun j => transition h (restrict F (g j))) : M) =
    (c.val (fun j => restrict E (g j)) : M)
  exact congrArg (fun t : Fin q → LayerGroup E => (c.val t : M))
    (funext fun j => (DFunLike.congr_fun (restrict_comp h) (g j)).symm)

private theorem inflateCocycle_transition (h : E ≤ F) (c : LayerCocycles M E q) :
    inflateCocycle M F q (transitionCocycle h q c) = inflateCocycle M E q c :=
  Subtype.ext (inflateCochain_transition h c.val)

private theorem inflateCochain_d (E : FiniteGaloisIntermediateField k L) (q : ℕ)
    (c : LayerCochains M E q) :
    inflateCochain (M := M) E (q + 1)
        (continuousDifferential (LayerGroup E) (LayerCoefficients M E) q c) =
      continuousDifferential Gal(L/k) M q (inflateCochain (M := M) E q c) :=
  Model.continuousCochainMap_d (restrict E).toMonoidHom (restrict E).continuous
    (LayerCoefficients M E).subtype.toAddMonoidHom (layerAction_restrict M E) q c

private theorem inflateCochain_incoming (E : FiniteGaloisIntermediateField k L) (q : ℕ)
    (c : LayerCochains M E q.pred) :
    inflateCochain (M := M) E q (continuousIncoming (LayerGroup E) (LayerCoefficients M E) q c) =
      continuousIncoming Gal(L/k) M q (inflateCochain (M := M) E q.pred c) := by
  cases q with
  | zero => exact map_zero (inflateCochain E 0)
  | succ q => exact inflateCochain_d E q c

private theorem descendCochain (E₀ : FiniteGaloisIntermediateField k L)
    (c : continuousCochains Gal(L/k) M q) :
    ∃ E, E₀ ≤ E ∧ ∃ t : LayerCochains M E q, inflateCochain (M := M) E q t = c := by
  obtain ⟨E, hE, fE, hfE⟩ := FiniteCochainDescent.finiteCochainFactorization c.val c.property E₀
  let f (x : Fin q → LayerGroup E) : LayerCoefficients M E :=
    ⟨fE x, fun σ => (fE x).property σ⟩
  refine ⟨E, hE, ⟨f, continuous_of_discreteTopology⟩, Subtype.ext ?_⟩
  exact funext hfE

private theorem descendCocycle (c : continuousCocycles Gal(L/k) M q) :
    ∃ (E : FiniteGaloisIntermediateField k L) (t : LayerCocycles M E q),
      inflateCocycle M E q t = c := by
  obtain ⟨E, _, t, ht⟩ := descendCochain ⊥ c.val
  have hd : continuousDifferential (LayerGroup E) (LayerCoefficients M E) q t = 0 := by
    apply inflateCochain_injective E (q + 1)
    rw [inflateCochain_d, ht, LinearMap.mem_ker.mp c.property, map_zero]
  exact ⟨E, ⟨t, LinearMap.mem_ker.mpr hd⟩, Subtype.ext ht⟩

private theorem class_eq_iff_incoming {G : Type*} {A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
    (a b : continuousCocycles G A q) :
    continuousClass G A q a = continuousClass G A q b ↔
      ∃ t : continuousCochains G A q.pred, continuousIncoming G A q t = a.val - b.val := by
  rw [continuousClass_eq_iff]
  change (∃ t, _ = a - b) ↔ _
  exact ⟨fun ⟨t, ht⟩ => ⟨t, congrArg Subtype.val ht⟩,
    fun ⟨t, ht⟩ => ⟨t, Subtype.ext ht⟩⟩

private theorem equal_after_transition (a : LayerCocycles M E q) (b : LayerCocycles M F q)
    (h : continuousClass Gal(L/k) M q (inflateCocycle M E q a) =
      continuousClass Gal(L/k) M q (inflateCocycle M F q b)) :
    ∃ (D : FiniteGaloisIntermediateField k L) (hE : E ≤ D) (hF : F ≤ D),
      stageTransition M E D q hE (stageClass M E q a) =
        stageTransition M F D q hF (stageClass M F q b) := by
  obtain ⟨t, ht⟩ := (class_eq_iff_incoming _ _).mp h
  obtain ⟨D, hD, tD, htD⟩ := descendCochain (E ⊔ F) t
  let hE : E ≤ D := le_sup_left.trans hD
  let hF : F ≤ D := le_sup_right.trans hD
  let aD := transitionCocycle hE q a
  let bD := transitionCocycle hF q b
  have hd : continuousIncoming (LayerGroup D) (LayerCoefficients M D) q tD =
      aD.val - bD.val := by
    apply inflateCochain_injective D q
    rw [inflateCochain_incoming, htD, map_sub]
    change continuousIncoming Gal(L/k) M q t =
      inflateCochain (M := M) D q (transitionCochain hE q a.val) -
        inflateCochain (M := M) D q (transitionCochain hF q b.val)
    rw [inflateCochain_transition, inflateCochain_transition]
    exact ht
  have hc := (class_eq_iff_incoming aD bD).mpr ⟨tD, hd⟩
  refine ⟨D, hE, hF, ?_⟩
  rw [stageTransition_class, stageTransition_class]
  change stageClass M D q aD = stageClass M D q bD
  have h := congrArg (ordinaryCohomologyEquiv.{v,w,0} (LayerGroup D) (LayerCoefficients M D) q) hc
  simp only [ordinaryCohomologyEquiv_class] at h
  exact h

private def stageInflation (E : FiniteGaloisIntermediateField k L) (q : ℕ) :
    LayerH M E q →ₗ[ℤ] ContinuousH Gal(L/k) M q :=
  let e := ordinaryCohomologyEquiv.{v,w,0} (LayerGroup E) (LayerCoefficients M E) q
  (continuousCohomologyMap (restrict E).toMonoidHom (restrict E).continuous
    (LayerCoefficients M E).subtype.toAddMonoidHom (layerAction_restrict M E) q).comp
      e.symm.toIntLinearEquiv.toLinearMap

private theorem stageInflation_class (c : LayerCocycles M E q) :
    stageInflation (M := M) E q (stageClass M E q c) =
      continuousClass Gal(L/k) M q (inflateCocycle M E q c) := by
  have hc := ordinaryCohomologyEquiv_class.{v,w,0} (LayerGroup E) (LayerCoefficients M E) q c
  change _ = stageClass M E q c at hc
  rw [← hc]
  change continuousCohomologyMap (restrict E).toMonoidHom (restrict E).continuous
    (LayerCoefficients M E).subtype.toAddMonoidHom (layerAction_restrict M E) q
    ((ordinaryCohomologyEquiv.{v,w,0} (LayerGroup E) (LayerCoefficients M E) q).symm
      (ordinaryCohomologyEquiv.{v,w,0} (LayerGroup E) (LayerCoefficients M E) q
        (continuousClass (LayerGroup E) (LayerCoefficients M E) q c))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

private theorem stageInflation_compatible (h : E ≤ F) (a : LayerH M E q) :
    stageInflation (M := M) F q (stageTransition M E F q h a) = stageInflation (M := M) E q a := by
  obtain ⟨c, rfl⟩ := stageClass_surjective M E q a
  rw [stageTransition_class, stageInflation_class, stageInflation_class, inflateCocycle_transition]

end Inflation

/-- The canonical inflation comparison from the colimit of ordinary cohomology
of finite Galois layers is an isomorphism in every degree. -/
theorem finiteLayerComparison : FiniteLayerComparison.{u,v,w} := by
  intro k L _ _ _ _ M _ _ _ _ _ q
  let ι := FiniteGaloisIntermediateField k L
  let : DecidableEq ι := Classical.decEq _
  let A (E : ι) : Type (max v w) := LayerH M E q
  let f (E F : ι) (h : E ≤ F) : A E →ₗ[ℤ] A F := stageTransition M E F q h
  let comparison : LayerLimit (k := k) (L := L) M q →ₗ[ℤ] ContinuousH Gal(L/k) M q :=
    Module.DirectLimit.lift ℤ ι A f (fun E => stageInflation (M := M) E q)
      (fun _ _ h a => stageInflation_compatible h a)
  have comparison_of (E : ι) (a : A E) :
      comparison (limitOf M E q a) = stageInflation (M := M) E q a :=
    Module.DirectLimit.lift_of _ _ a
  have of_transition {E F : ι} (h : E ≤ F) (a : A E) :
      limitOf M F q (stageTransition M E F q h a) = limitOf M E q a :=
    Module.DirectLimit.of_f
  have hinj : Function.Injective comparison := by
    intro x y h
    obtain ⟨E, a, rfl⟩ := Module.DirectLimit.exists_of (R := ℤ) (ι := ι) (G := A) (f := f) x
    obtain ⟨F, b, rfl⟩ := Module.DirectLimit.exists_of (R := ℤ) (ι := ι) (G := A) (f := f) y
    obtain ⟨a, rfl⟩ := stageClass_surjective M E q a
    obtain ⟨b, rfl⟩ := stageClass_surjective M F q b
    change comparison (limitOf M E q (stageClass M E q a)) =
      comparison (limitOf M F q (stageClass M F q b)) at h
    simp only [comparison_of, stageInflation_class] at h
    obtain ⟨D, hE, hF, hEq⟩ := equal_after_transition a b h
    exact (of_transition hE _).symm.trans
      ((congrArg (limitOf M D q) hEq).trans (of_transition hF _))
  have hsurj : Function.Surjective comparison := by
    intro a
    obtain ⟨c, rfl⟩ := continuousClass_surjective q a
    obtain ⟨E, t, ht⟩ := descendCocycle c
    exact ⟨limitOf M E q (stageClass M E q t),
      (comparison_of E _).trans ((stageInflation_class t).trans
        (congrArg (continuousClass Gal(L/k) M q) ht))⟩
  refine ⟨LinearEquiv.ofBijective comparison ⟨hinj, hsurj⟩, fun E c => ?_⟩
  exact (comparison_of E _).trans (stageInflation_class c)

end

end GaloisFormalization.GH.FiniteLayerCohomology
