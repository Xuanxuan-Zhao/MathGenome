import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations
import Mathlib.LinearAlgebra.TensorProduct.Basis
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.ConstantRankBundles
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses

/-! Bundle constructions for M05.04 on the prescribed algebraic fibers. -/
set_option autoImplicit false
namespace SmoothManifolds.BundleOperations
open ModelData AtlasData MapData ProductData BundleData FrameData ConstantRankData
  QuotientData TangentData TangentBundleData DifferentialData MapClassData
  BundleOperationsData Bundle Set Filter
open scoped Topology
universe u v w z t q

/-- A zero-rank bundle has zero fibers and the standard smooth trivialization. -/
theorem zero_of_rank_eq_zero {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (h : r = 0) :
    (∀ p (v : E p), v = 0) ∧ SmoothlyTrivial B := by
  subst r
  exact ⟨(Frames.rankZero B).1, (Frames.rankZero B).2.2⟩

/-- Coordinate restriction identifies an adapted submodule with its first k coordinates. -/
noncomputable def adaptedCoordinates {r k : ℕ} {V : Type w}
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis (Fin r) ℝ V)
    (K : Submodule ℝ V) (hk : k ≤ r)
    (hK : ∀ v : V, v ∈ K ↔ ∀ j : Fin r, k ≤ j.val → b.equivFun v j = 0) :
    K ≃ₗ[ℝ] Euclidean k := by
  classical
  refine {
    toFun := fun v j => b.equivFun v.val (j.castLE hk)
    map_add' := by
      intro v w
      funext j
      exact congrFun (b.equivFun.map_add v.val w.val) (j.castLE hk)
    map_smul' := by
      intro c v
      funext j
      exact congrFun (b.equivFun.map_smul c v.val) (j.castLE hk)
    invFun := fun v => ⟨b.equivFun.symm (fun j => if h : j.val < k then v ⟨j.val,h⟩ else 0), by
      apply (hK _).mpr
      intro j hj
      simp only [LinearEquiv.apply_symm_apply]
      exact dite_eq_right (Nat.not_lt.mpr hj)⟩
    left_inv := by
      intro v
      apply Subtype.ext
      apply b.equivFun.injective
      simp only [LinearEquiv.apply_symm_apply]
      funext j
      by_cases hj : j.val < k
      · simp only [dite_eq_left hj]
        rfl
      · rw [dite_eq_right hj]
        exact ((hK v.val).mp v.property j (Nat.le_of_not_lt hj)).symm
    right_inv := by
      intro v
      funext j
      simp only [LinearEquiv.apply_symm_apply, Fin.val_castLE]
      rw [dite_eq_left j.isLt] }

theorem adaptedCoordinates_symm_basis {r k : ℕ} {V : Type w}
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis (Fin r) ℝ V)
    (K : Submodule ℝ V) (hk : k ≤ r)
    (hK : ∀ v : V, v ∈ K ↔ ∀ j : Fin r, k ≤ j.val → b.equivFun v j = 0)
    (j : Fin k) :
    ((adaptedCoordinates b K hk hK).symm (Pi.single j 1)).val = b (j.castLE hk) := by
  classical
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm _) = b.equivFun (b (j.castLE hk))
  rw [LinearEquiv.apply_symm_apply]
  funext i
  rw [b.equivFun_self]
  by_cases hi : i.val < k
  · rw [dite_eq_left hi]
    have hj : (⟨i.val, hi⟩ : Fin k) = j ↔ j.castLE hk = i := by
      constructor
      · intro h
        apply Fin.ext
        exact (congrArg (fun x : Fin k => x.val) h).symm
      · intro h
        apply Fin.ext
        exact (congrArg (fun x : Fin r => x.val) h).symm
    simp only [Pi.single_apply, hj]
  · rw [dite_eq_right hi]
    have hj : j.castLE hk ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      exact hi (hval ▸ j.isLt)
    rw [ite_eq_right hj]

noncomputable def adaptedSubbundleFrame
    {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} {K : (p : M) → Submodule ℝ (E p)}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (hk : k ≤ r)
    (hK : ∀ (p : U) (v : E p.val),
      v ∈ K p.val ↔ ∀ j : Fin r, k ≤ j.val → (b.basis p).equivFun v j = 0) :
    LocalSubbundleFrame B K k U hU where
  basis p := (Pi.basisFun ℝ (Fin k)).map
    (adaptedCoordinates (b.basis p) (K p.val) hk (hK p)).symm
  smooth j := by
    have heq (p : U) : (((Pi.basisFun ℝ (Fin k)).map
        (adaptedCoordinates (b.basis p) (K p.val) hk (hK p)).symm) j).val =
        b.section_ (j.castLE hk) p := by
      rw [Module.Basis.map_apply, Pi.basisFun_apply,
        adaptedCoordinates_symm_basis, b.basis_eq]
    simpa only [heq] using b.smooth (j.castLE hk)

theorem smoothSubbundle_of_adapted
    {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (K : (p : M) → Submodule ℝ (E p))
    (hK : IsSmoothSubbundle B k K) : SmoothSubbundle B K k := by
  intro p
  obtain ⟨hk, U, hU, hp, b, hb⟩ := hK p
  exact ⟨U, hU, hp, ⟨adaptedSubbundleFrame b hk hb⟩⟩


/-- Full tangent injectivity and rank for embeddings, also at boundary points. -/
theorem embedding_differential_injective
    {m n : ℕ} {a b : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m a P) (S : SmoothManifold n b M) (i : P → M)
    (hi : IsSmoothEmbedding T S i)
    (L : (p : P) → TangentSpace T p →ₗ[ℝ] TangentSpace S (i p))
    (hL : ∀ p, IsDifferential T S i p (L p)) :
    ∀ p, Function.Injective (L p) ∧ Module.finrank ℝ (LinearMap.range (L p)) = m := by
  intro p
  have hinj : Function.Injective (L p) :=
    (MapClasses.smooth_tangent_invariants T S i hi.1 p (L p) (hL p)).2.1.mp (hi.2.2.1 p)
  exact ⟨hinj, (LinearMap.finrank_range_of_inj hinj).trans (tangent_dimension T p).2⟩

theorem pullback_comp :
  ∀ {n m l r : ℕ} {a b c : ModelKind} {M : Type u} {P : Type v} {Q : Type z}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q]
    {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (T : SmoothManifold m b P)
    (U : SmoothManifold l c Q) (f : P → M) (g : Q → P),
    IsSmoothMap T S f → IsSmoothMap U T g →
    ∀ (F : PullbackBundle B T f) (H : PullbackBundle B U (f ∘ g)),
    letI := F.space.topology
    ∀ (G : @PullbackBundle m l r b c P Q _ _ T ι (fun p => E (f p))
        (fun _ => inferInstance) (fun _ => inferInstance) F.space.topology F.space.bundle U g),
    letI := H.space.topology; letI := G.space.topology
    @IsSmoothMap (l+r) (l+r) _ _ _ _ H.space.topology G.space.topology
      H.space.bundle.totalManifold G.space.bundle.totalManifold id ∧
    @IsSmoothMap (l+r) (l+r) _ _ _ _ G.space.topology H.space.topology
      G.space.bundle.totalManifold H.space.bundle.totalManifold id := by
  intro n m l r a b c M P Q _ _ _ S ι E _ _ _ B T U f g _hf _hg F H G
  letI := F.space.topology
  letI := H.space.topology
  letI := G.space.topology
  have hbase : ∀ i, H.space.bundle.baseSet i = G.space.bundle.baseSet i := by
    intro i
    rw [H.baseSet, G.baseSet, F.baseSet]
    rfl
  have hcoord : ∀ i p, p ∈ H.space.bundle.baseSet i → ∀ v : E (f (g p)),
      ((G.space.bundle.trivialization i) ⟨p,v⟩).2 =
        ((H.space.bundle.trivialization i) ⟨p,v⟩).2 := by
    intro i p hp v
    have hpB : f (g p) ∈ B.baseSet i := by
      simpa only [H.baseSet, mem_preimage, Function.comp_apply] using hp
    have hpF : g p ∈ F.space.bundle.baseSet i := by
      simpa only [F.baseSet, mem_preimage] using hpB
    exact (G.coordinates i p hpF v).trans
      ((F.coordinates i (g p) hpB v).trans (H.coordinates i p hpB v).symm)
  constructor
  · exact @BundleData.SmoothVectorBundle.smooth_of_preserves l r c Q _ U ι
      (fun p => E (f (g p))) (fun p => E (f (g p))) _ _ _ _
      H.space.topology G.space.topology H.space.bundle G.space.bundle
      hbase (fun p => LinearEquiv.refl ℝ _) hcoord
  · apply @BundleData.SmoothVectorBundle.smooth_of_preserves l r c Q _ U ι
      (fun p => E (f (g p))) (fun p => E (f (g p))) _ _ _ _
      G.space.topology H.space.topology G.space.bundle H.space.bundle
      (fun i => (hbase i).symm) (fun p => LinearEquiv.refl ℝ _)
    intro i p hp v
    exact (hcoord i p ((hbase i).symm ▸ hp) v).symm

/-- The canonical degree-zero algebraic identification is a smooth line-bundle trivialization. -/
theorem exterior_zero : Specs.SmoothManifolds.Ch05.BundleOperations.exterior_zeroType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B V
  classical
  letI := V.space.topology
  letI : Unique (Fin (r.choose 0)) := by rw [Nat.choose_zero_right]; infer_instance
  let basis (p : M) : Module.Basis (Fin (r.choose 0)) ℝ (⋀[ℝ]^0 (E p)) :=
    (Module.Basis.singleton (Fin (r.choose 0)) ℝ).map (exteriorPower.zeroEquiv ℝ (E p)).symm
  have hgen (p : M) : (exteriorPower.zeroEquiv ℝ (E p)).symm 1 =
      exteriorPower.ιMulti ℝ 0 (Fin.elim0) := by
    apply (exteriorPower.zeroEquiv ℝ (E p)).injective
    simp
  let b : LocalFrame V.space.bundle univ isOpen_univ := {
    section_ := fun _ p => (exteriorPower.zeroEquiv ℝ (E p.val)).symm 1
    basis := fun p => basis p.val
    basis_eq := by intro p j; simp only [basis, Module.Basis.map_apply, Module.Basis.singleton_apply]
    smooth := by
      intro j p
      obtain ⟨i, hi⟩ := B.covers p.val
      have hiV : p.val ∈ V.space.bundle.baseSet i := (V.baseSet i).symm ▸ hi
      apply Frames.smoothAt_of_sectionCoordinates V.space.bundle univ isOpen_univ i _ p hiV
      let c₀ := V.modelEquiv (exteriorPower.ιMulti ℝ 0 (Fin.elim0))
      have hev : ∀ᶠ q : (univ : Set M) in 𝓝 p, q.val ∈ B.baseSet i := by
        have hU : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
        exact (hU.preimage continuous_subtype_val).mem_nhds hi
      have heq : (Frames.sectionCoordinates V.space.bundle univ i
          (fun q => (exteriorPower.zeroEquiv ℝ (E q.val)).symm 1)) =ᶠ[𝓝 p] (fun _ => c₀) := by
        filter_upwards [hev] with q hq
        change ((V.space.bundle.trivialization i)
          ⟨q.val, (exteriorPower.zeroEquiv ℝ (E q.val)).symm 1⟩).2 = c₀
        rw [hgen]
        exact V.coordinates i q.val hq (Fin.elim0)
      exact (FrameData.VectorSmoothAt.const _ c₀ p).congr heq.symm }
  obtain ⟨e, he⟩ := Frames.globalFrame_trivialization V.space.bundle b
  refine ⟨e, ?_⟩
  intro p v j
  rw [he]
  change (basis p).equivFun v j = exteriorPower.zeroEquiv ℝ (E p) v
  simp only [basis, Module.Basis.map_equivFun, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm]
  simp [Module.Basis.singleton, Subsingleton.elim j default]

theorem exterior_above_rank : Specs.SmoothManifolds.Ch05.BundleOperations.exterior_above_rankType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B k V hk
  letI := V.space.topology
  exact zero_of_rank_eq_zero V.space.bundle (Nat.choose_eq_zero_of_lt hk)

/-- Local linear coordinates on prescribed fibers, with smooth transition matrices.
The transition operators are totalized only to avoid imposing data off overlaps. -/
structure CoordinatePresentation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : ℕ) (ι : Type v)
    (E : M → Type w) [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)] where
  domain : ι → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  covers : ∀ p, ∃ i, p ∈ domain i
  coord : ∀ i p, p ∈ domain i → E p ≃ₗ[ℝ] Euclidean r
  transition : ι → ι → M → (Euclidean r →L[ℝ] Euclidean r)
  transition_eq : ∀ i j p (hi : p ∈ domain i) (hj : p ∈ domain j) v,
    transition i j p v = coord j p hj ((coord i p hi).symm v)
  smooth : ∀ i j p, p ∈ domain i → p ∈ domain j →
    VectorSmoothAt S.smoothStructure.val (transition i j) p

namespace CoordinatePresentation
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  (C : CoordinatePresentation S r ι E)

noncomputable def cocycle : OverlapCocycle S r ι where
  baseSet := C.domain
  isOpen_baseSet := C.isOpen_domain
  covers := C.covers
  g i j p := ((C.coord i p.val p.property.1).symm.trans
    (C.coord j p.val p.property.2)).toContinuousLinearEquiv
  self i p hp := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact (C.coord i p hp).apply_symm_apply v
  comp i j k p hi hj hk := by
    apply ContinuousLinearMap.ext
    intro v
    change C.coord k p hk ((C.coord j p hj).symm
      (C.coord j p hj ((C.coord i p hi).symm v))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  smooth i j p := by
    have heq : (fun q : ↥(C.domain i ∩ C.domain j) =>
        ((((C.coord i q.val q.property.1).symm.trans
          (C.coord j q.val q.property.2)).toContinuousLinearEquiv :
            Euclidean r →L[ℝ] Euclidean r))) = fun q => C.transition i j q.val := by
      funext q
      apply ContinuousLinearMap.ext
      intro v
      exact (C.transition_eq i j q.val q.property.1 q.property.2 v).symm
    rw [heq]
    have hs := C.smooth i j p.val p.property.1 p.property.2
    refine ⟨hs.1.comp continuousAt_subtype_val, ?_⟩
    intro c hc hp
    obtain ⟨W, hW, hpW, F, hF, he⟩ := hs.2 c hc hp
    exact ⟨W, hW, hpW, F, hF, he.comp_tendsto continuousAt_subtype_val⟩

/-- Gluing followed by fiberwise transport retains the specified algebraic fibers. -/
theorem exists_bundle :
    ∃ V : BundleSpace S r ι E, letI := V.topology; (∀ i, V.bundle.baseSet i = C.domain i) ∧
      ∀ i p (hp : p ∈ C.domain i) v,
        ((V.bundle.trivialization i) ⟨p, v⟩).2 = C.coord i p hp v := by
  classical
  let D := C.cocycle.totalize
  obtain ⟨G⟩ := exists_gluedBundle D
  letI := G.addCommGroup
  letI := G.module
  letI := G.topology
  let k (p : M) : ι := Classical.choose (C.covers p)
  have hk (p : M) : p ∈ C.domain (k p) := Classical.choose_spec (C.covers p)
  let e (p : M) : E p ≃ₗ[ℝ] G.Fiber p := (C.coord (k p) p (hk p)).trans
    (G.bundle.fiberCoordinates (k p) p ((G.realizes.1 _).symm ▸ hk p)).symm
  let V : BundleSpace S r ι E := {
    topology := QuotientBundles.Transport.topology (r := r) e
    bundle := QuotientBundles.Transport.bundle G.bundle e }
  refine ⟨V, G.realizes.1, ?_⟩
  intro i p hp v
  change ((G.bundle.trivialization i) ⟨p, e p v⟩).2 = _
  rw [G.bundle.coordinates_transition G.realizes (k p) i p (hk p) hp]
  change C.cocycle.totalTransition (k p) i p _ = _
  rw [C.cocycle.totalTransition_eq (k p) i p (hk p) hp]
  change C.coord i p hp ((C.coord (k p) p (hk p)).symm
    (G.bundle.fiberCoordinates (k p) p ((G.realizes.1 _).symm ▸ hk p) (e p v))) = _
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply]

end CoordinatePresentation

/-- Every smooth bundle gives a smooth coordinate presentation on its original cover. -/
noncomputable def bundlePresentation {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) : CoordinatePresentation S r ι E where
  domain := B.baseSet
  isOpen_domain i := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  covers := B.covers
  coord := B.fiberCoordinates
  transition := QuotientBundles.bundleTransitionOperator B
  transition_eq := QuotientBundles.bundleTransitionOperator_apply B
  smooth := QuotientBundles.bundleTransitionOperator_smooth B

/-- Coordinate presentations pull back by smooth maps, including at the boundary. -/
noncomputable def CoordinatePresentation.pullback {n m r : ℕ} {a b : ModelKind}
    {M : Type u} {P : Type z} [TopologicalSpace M] [TopologicalSpace P]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (C : CoordinatePresentation S r ι E) (T : SmoothManifold m b P)
    (f : P → M) (hf : IsSmoothMap T S f) :
    CoordinatePresentation T r ι (fun p => E (f p)) where
  domain i := f ⁻¹' C.domain i
  isOpen_domain i := (C.isOpen_domain i).preimage (continuous_iff_continuousAt.mpr (fun p => (hf p).1))
  covers p := C.covers (f p)
  coord i p hp := C.coord i (f p) hp
  transition i j p := C.transition i j (f p)
  transition_eq i j p hi hj v := C.transition_eq i j (f p) hi hj v
  smooth i j p hi hj := (C.smooth i j (f p) hi hj).comp S.smoothStructure.property.1.1 (hf p)

theorem exists_pullback :
  ∀ {n m r : ℕ} {a b : ModelKind} {M : Type u} {P : Type v}
    [TopologicalSpace M] [TopologicalSpace P]
    {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (T : SmoothManifold m b P) (f : P → M),
    IsSmoothMap T S f → Nonempty (PullbackBundle B T f) := by
  intro n m r a b M P _ _ S ι E _ _ _ B T f hf
  let C := (bundlePresentation B).pullback T f hf
  obtain ⟨V, hbase, hcoord⟩ := C.exists_bundle
  letI := V.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates := hcoord, canonical_smooth := ?_ }⟩
  intro q
  obtain ⟨i, hi⟩ := V.bundle.covers q.proj
  have hiB : f q.proj ∈ B.baseSet i := by
    change q.proj ∈ C.domain i
    rw [← hbase i]
    exact hi
  have hproj := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1
    (TotalSpace.proj : Bundle.TotalSpace (Euclidean r) (fun p => E (f p)) → P) f
    V.bundle.projection_smooth hf
  apply Frames.smoothAt_from_trivialization B V.bundle.totalManifold.smoothStructure.property.1
    i hiB (hproj q) (Frames.trivializationCoordinates_smoothAt V.bundle i q hi) (fun _ => rfl)
  have hev := (V.bundle.projection_smooth q).1.preimage_mem_nhds
    ((C.isOpen_domain i).mem_nhds hiB)
  filter_upwards [hev] with y hy
  exact (hcoord i y.proj hy y.snd).symm

/-- Smooth columns assemble to a smooth finite matrix, also with zero rows or columns. -/
theorem columnOperator_smooth {d r k : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {A : Set (ModelChart d a X)}
    {v : X → Fin k → Euclidean r} {p : X}
    (hv : ∀ j, VectorSmoothAt A (fun x => v x j) p) :
    VectorSmoothAt A (fun x => QuotientBundles.columnOperator (v x)) p := by
  unfold QuotientBundles.columnOperator
  apply FrameData.VectorSmoothAt.sum
  intro j
  exact (hv j).postcomp (contDiff_const.smulRight contDiff_id)

noncomputable def dualCoordinates {r : ℕ} {V : Type w}
    [AddCommGroup V] [Module ℝ V] (e : V ≃ₗ[ℝ] Euclidean r) :
    Module.Dual ℝ V ≃ₗ[ℝ] Euclidean r :=
  e.symm.dualMap.trans (Pi.basisFun ℝ (Fin r)).dualBasis.equivFun

@[simp] theorem dualCoordinates_apply {r : ℕ} {V : Type w}
    [AddCommGroup V] [Module ℝ V] (e : V ≃ₗ[ℝ] Euclidean r)
    (lam : Module.Dual ℝ V) (j : Fin r) :
    dualCoordinates e lam j = lam (e.symm (Pi.single j 1)) := by
  simp [dualCoordinates, Module.Basis.dualBasis_equivFun]

theorem dualCoordinates_symm_apply {r : ℕ} {V : Type w}
    [AddCommGroup V] [Module ℝ V] (e : V ≃ₗ[ℝ] Euclidean r)
    (v : Euclidean r) (x : V) :
    (dualCoordinates e).symm v x = ∑ j, v j * e x j := by
  have he := (Pi.basisFun ℝ (Fin r)).sum_equivFun (e x)
  have hex : x = ∑ j, e x j • e.symm (Pi.single j 1) := by
    simpa using (congrArg e.symm he).symm
  conv_lhs => rw [hex, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  have hv := congrFun ((dualCoordinates e).apply_symm_apply v) j
  rw [dualCoordinates_apply] at hv
  rw [hv]
  exact mul_comm (e x j) (v j)

noncomputable def CoordinatePresentation.dual {n r : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (C : CoordinatePresentation S r ι E) :
    CoordinatePresentation S r ι (fun p => Module.Dual ℝ (E p)) where
  domain := C.domain
  isOpen_domain := C.isOpen_domain
  covers := C.covers
  coord i p hp := dualCoordinates (C.coord i p hp)
  transition i j p := QuotientBundles.columnOperator
    (fun l k => C.transition j i p (Pi.single k 1) l)
  transition_eq i j p hi hj v := by
    funext k
    rw [dualCoordinates_apply, dualCoordinates_symm_apply, QuotientBundles.columnOperator_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [C.transition_eq j i p hj hi]
  smooth i j p hi hj := by
    apply columnOperator_smooth
    intro l
    apply FrameData.VectorSmoothAt.pi
    intro k
    exact ((C.smooth j i p hj hi).clm_apply
      (FrameData.VectorSmoothAt.const _ (Pi.single k 1) p)).postcomp
      (ContinuousLinearMap.proj l).contDiff

theorem exists_dual : Specs.SmoothManifolds.Ch05.BundleOperations.exists_dualType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B
  obtain ⟨V, hbase, hcoord⟩ := (bundlePresentation B).dual.exists_bundle
  letI := V.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates := ?_ }⟩
  intro i p hp lam j
  rw [hcoord i p hp lam]
  exact dualCoordinates_apply (B.fiberCoordinates i p hp) lam j

/-- Concatenate the two standard coordinate blocks. -/
noncomputable def sumCoordinates (r s : ℕ) :
    (Euclidean r × Euclidean s) ≃ₗ[ℝ] Euclidean (r+s) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℝ ℝ).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm)

@[simp] theorem sumCoordinates_left {r s : ℕ} (v : Euclidean r × Euclidean s) (j : Fin r) :
    sumCoordinates r s v (Fin.castAdd s j) = v.1 j := by
  simp [sumCoordinates, LinearEquiv.sumArrowLequivProdArrow]
  rfl

@[simp] theorem sumCoordinates_right {r s : ℕ} (v : Euclidean r × Euclidean s) (j : Fin s) :
    sumCoordinates r s v (Fin.natAdd r j) = v.2 j := by
  simp [sumCoordinates, LinearEquiv.sumArrowLequivProdArrow]
  rfl

noncomputable def CoordinatePresentation.directSum {n r s : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {κ : Type t} {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    (C : CoordinatePresentation S r ι E) (D : CoordinatePresentation S s κ F) :
    CoordinatePresentation S (r+s) (ι × κ) (fun p => E p × F p) where
  domain i := C.domain i.1 ∩ D.domain i.2
  isOpen_domain i := (C.isOpen_domain i.1).inter (D.isOpen_domain i.2)
  covers p := by obtain ⟨i, hi⟩ := C.covers p; obtain ⟨j, hj⟩ := D.covers p; exact ⟨(i,j), hi,hj⟩
  coord i p hp := ((C.coord i.1 p hp.1).prodCongr (D.coord i.2 p hp.2)).trans (sumCoordinates r s)
  transition i j p := QuotientBundles.columnOperator (fun l => sumCoordinates r s
    (C.transition i.1 j.1 p ((sumCoordinates r s).symm (Pi.single l 1)).1,
      D.transition i.2 j.2 p ((sumCoordinates r s).symm (Pi.single l 1)).2))
  transition_eq i j p hi hj v := by
    change p ∈ C.domain i.1 ∧ p ∈ D.domain i.2 at hi
    change p ∈ C.domain j.1 ∧ p ∈ D.domain j.2 at hj
    have heq : (QuotientBundles.columnOperator (fun l => sumCoordinates r s
        (C.transition i.1 j.1 p ((sumCoordinates r s).symm (Pi.single l 1)).1,
          D.transition i.2 j.2 p ((sumCoordinates r s).symm (Pi.single l 1)).2))).toLinearMap =
        ((((C.coord i.1 p hi.1).prodCongr (D.coord i.2 p hi.2)).trans (sumCoordinates r s)).symm.trans
          (((C.coord j.1 p hj.1).prodCongr (D.coord j.2 p hj.2)).trans (sumCoordinates r s))).toLinearMap := by
      apply (Pi.basisFun ℝ (Fin (r+s))).ext
      intro l
      rw [Pi.basisFun_apply]
      change (QuotientBundles.columnOperator _) (Pi.single l 1) = _
      rw [QuotientBundles.columnOperator_single,
        C.transition_eq i.1 j.1 p hi.1 hj.1, D.transition_eq i.2 j.2 p hi.2 hj.2]
      rfl
    exact LinearMap.congr_fun heq v
  smooth i j p hi hj := by
    apply columnOperator_smooth
    intro l
    exact (((C.smooth i.1 j.1 p hi.1 hj.1).clm_apply (FrameData.VectorSmoothAt.const _ _ p)).prod
      ((D.smooth i.2 j.2 p hi.2 hj.2).clm_apply (FrameData.VectorSmoothAt.const _ _ p))).postcomp
      (sumCoordinates r s).toContinuousLinearEquiv.contDiff

theorem exists_directSum :
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F),
    Nonempty (DirectSumBundle B D) := by
  intro n r s a M _ S ι κ E F _ _ _ _ _ _ B D
  obtain ⟨V, hbase, hcoord⟩ := ((bundlePresentation B).directSum (bundlePresentation D)).exists_bundle
  letI := V.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates_left := ?_, coordinates_right := ?_ }⟩
  · intro i p hp v j
    rw [hcoord i p ((hbase i) ▸ hp) v]
    exact sumCoordinates_left _ j
  · intro i p hp v j
    rw [hcoord i p ((hbase i) ▸ hp) v]
    exact sumCoordinates_right _ j

/-- Standard ordered tensor coordinates. -/
noncomputable def tensorModelCoordinates (r s : ℕ) :
    TensorProduct ℝ (Euclidean r) (Euclidean s) ≃ₗ[ℝ] Euclidean (r*s) :=
  (((Pi.basisFun ℝ (Fin r)).tensorProduct (Pi.basisFun ℝ (Fin s))).reindex
    finProdFinEquiv).equivFun

@[simp] theorem tensorModelCoordinates_tmul {r s : ℕ} (v : Euclidean r) (w : Euclidean s)
    (j : Fin r) (k : Fin s) :
    tensorModelCoordinates r s (TensorProduct.tmul ℝ v w) (finProdFinEquiv (j,k)) = v j * w k := by
  simp [tensorModelCoordinates, Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex_apply, mul_comm]

@[simp] theorem tensorModelCoordinates_symm_single {r s : ℕ} (l : Fin (r*s)) :
    (tensorModelCoordinates r s).symm (Pi.single l 1) =
      TensorProduct.tmul ℝ (Pi.single (finProdFinEquiv.symm l).1 1)
        (Pi.single (finProdFinEquiv.symm l).2 1) := by
  classical
  change ((((Pi.basisFun ℝ (Fin r)).tensorProduct (Pi.basisFun ℝ (Fin s))).reindex
    finProdFinEquiv).equivFun.symm (Pi.single l 1)) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply, ite_smul, Module.Basis.reindex_apply,
    Module.Basis.tensorProduct_apply']

noncomputable def tensorCoordinates {r s : ℕ} {V : Type w} {W : Type z}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] Euclidean r) (f : W ≃ₗ[ℝ] Euclidean s) :
    TensorProduct ℝ V W ≃ₗ[ℝ] Euclidean (r*s) :=
  (TensorProduct.congr e f).trans (tensorModelCoordinates r s)

@[simp] theorem tensorCoordinates_tmul {r s : ℕ} {V : Type w} {W : Type z}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] Euclidean r) (f : W ≃ₗ[ℝ] Euclidean s) (v : V) (w : W)
    (j : Fin r) (k : Fin s) :
    tensorCoordinates e f (TensorProduct.tmul ℝ v w) (finProdFinEquiv (j,k)) = e v j * f w k := by
  simp [tensorCoordinates]

@[simp] theorem tensorCoordinates_symm_single {r s : ℕ} {V : Type w} {W : Type z}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] Euclidean r) (f : W ≃ₗ[ℝ] Euclidean s) (l : Fin (r*s)) :
    (tensorCoordinates e f).symm (Pi.single l 1) =
      TensorProduct.tmul ℝ (e.symm (Pi.single (finProdFinEquiv.symm l).1 1))
        (f.symm (Pi.single (finProdFinEquiv.symm l).2 1)) := by
  simp [tensorCoordinates, TensorProduct.congr_symm]

noncomputable def CoordinatePresentation.tensor {n r s : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {κ : Type t} {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    (C : CoordinatePresentation S r ι E) (D : CoordinatePresentation S s κ F) :
    CoordinatePresentation S (r*s) (ι × κ) (fun p => TensorProduct ℝ (E p) (F p)) where
  domain i := C.domain i.1 ∩ D.domain i.2
  isOpen_domain i := (C.isOpen_domain i.1).inter (D.isOpen_domain i.2)
  covers p := by obtain ⟨i, hi⟩ := C.covers p; obtain ⟨j, hj⟩ := D.covers p; exact ⟨(i,j), hi,hj⟩
  coord i p hp := tensorCoordinates (C.coord i.1 p hp.1) (D.coord i.2 p hp.2)
  transition i j p := QuotientBundles.columnOperator (fun l k =>
    C.transition i.1 j.1 p (Pi.single (finProdFinEquiv.symm l).1 1) (finProdFinEquiv.symm k).1 *
      D.transition i.2 j.2 p (Pi.single (finProdFinEquiv.symm l).2 1) (finProdFinEquiv.symm k).2)
  transition_eq i j p hi hj v := by
    change p ∈ C.domain i.1 ∧ p ∈ D.domain i.2 at hi
    change p ∈ C.domain j.1 ∧ p ∈ D.domain j.2 at hj
    have heq : (QuotientBundles.columnOperator (fun l k =>
        C.transition i.1 j.1 p (Pi.single (finProdFinEquiv.symm l).1 1) (finProdFinEquiv.symm k).1 *
          D.transition i.2 j.2 p (Pi.single (finProdFinEquiv.symm l).2 1) (finProdFinEquiv.symm k).2)).toLinearMap =
        ((tensorCoordinates (C.coord i.1 p hi.1) (D.coord i.2 p hi.2)).symm.trans
          (tensorCoordinates (C.coord j.1 p hj.1) (D.coord j.2 p hj.2))).toLinearMap := by
      apply (Pi.basisFun ℝ (Fin (r*s))).ext
      intro l
      rw [Pi.basisFun_apply]
      change (QuotientBundles.columnOperator _) (Pi.single l 1) = _
      rw [QuotientBundles.columnOperator_single]
      funext k
      change _ = tensorCoordinates (C.coord j.1 p hj.1) (D.coord j.2 p hj.2)
        ((tensorCoordinates (C.coord i.1 p hi.1) (D.coord i.2 p hi.2)).symm (Pi.single l 1)) k
      conv_rhs => rw [← finProdFinEquiv.apply_symm_apply k]
      simp only [LinearEquiv.trans_apply, tensorCoordinates_symm_single, tensorCoordinates_tmul]
      rw [C.transition_eq i.1 j.1 p hi.1 hj.1, D.transition_eq i.2 j.2 p hi.2 hj.2]
      exact (tensorCoordinates_tmul _ _ _ _
        (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).symm
    exact LinearMap.congr_fun heq v
  smooth i j p hi hj := by
    apply columnOperator_smooth
    intro l
    apply FrameData.VectorSmoothAt.pi
    intro k
    exact ((((C.smooth i.1 j.1 p hi.1 hj.1).clm_apply
      (FrameData.VectorSmoothAt.const _ _ p)).postcomp (ContinuousLinearMap.proj _).contDiff).prod
      (((D.smooth i.2 j.2 p hi.2 hj.2).clm_apply
      (FrameData.VectorSmoothAt.const _ _ p)).postcomp (ContinuousLinearMap.proj _).contDiff)).postcomp
      (contDiff_fst.mul contDiff_snd)

theorem exists_tensor :
  ∀ {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
    {E : M → Type w} {F : M → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean s) F)]
    (B : SmoothVectorBundle S r ι E) (D : SmoothVectorBundle S s κ F),
    Nonempty (TensorBundle B D) := by
  intro n r s a M _ S ι κ E F _ _ _ _ _ _ B D
  obtain ⟨V, hbase, hcoord⟩ := ((bundlePresentation B).tensor (bundlePresentation D)).exists_bundle
  letI := V.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates := ?_ }⟩
  intro i p hp v w j k
  rw [hcoord i p ((hbase i) ▸ hp)]
  exact tensorCoordinates_tmul _ _ v w j k

/-- Functorial linear equivalence on the actual homogeneous exterior powers. -/
noncomputable def exteriorEquiv {V : Type w} {W : Type z}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (e : V ≃ₗ[ℝ] W) : (⋀[ℝ]^k V) ≃ₗ[ℝ] (⋀[ℝ]^k W) :=
  LinearEquiv.ofLinear (exteriorPower.map k e.toLinearMap)
    (exteriorPower.map k e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simpa using (exteriorPower.map_id (R := ℝ) (M := W) (n := k)))
    (by rw [← exteriorPower.map_comp]; simpa using (exteriorPower.map_id (R := ℝ) (M := V) (n := k)))

@[simp] theorem exteriorEquiv_apply_ιMulti {V : Type w} {W : Type z}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (k : ℕ) (e : V ≃ₗ[ℝ] W) (v : Fin k → V) :
    exteriorEquiv k e (exteriorPower.ιMulti ℝ k v) = exteriorPower.ιMulti ℝ k (fun j => e (v j)) :=
  exteriorPower.map_apply_ιMulti e.toLinearMap v

noncomputable def exteriorModelCoordinates (r k : ℕ) :
    (⋀[ℝ]^k (Euclidean r)) ≃ₗ[ℝ] Euclidean (r.choose k) :=
  LinearEquiv.ofFinrankEq _ _ (by simp [exteriorPower.finrank_eq, Module.finrank_pi])

/-- Coordinates of decomposable wedges are polynomial functions of their arguments. -/
theorem wedgeCoordinates_smooth {d r k s : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {A : Set (ModelChart d a X)}
    (L : (⋀[ℝ]^k (Euclidean r)) →ₗ[ℝ] Euclidean s)
    {v : X → Fin k → Euclidean r} {p : X}
    (hv : ∀ j, VectorSmoothAt A (fun x => v x j) p) :
    VectorSmoothAt A (fun x => L (exteriorPower.ιMulti ℝ k (v x))) p := by
  classical
  let b := (Pi.basisFun ℝ (Fin r)).exteriorPower k
  have heq (x : X) : L (exteriorPower.ιMulti ℝ k (v x)) =
      ∑ s : Set.powersetCard (Fin r) k,
        b.repr (exteriorPower.ιMulti ℝ k (v x)) s • L (b s) := by
    conv_lhs => rw [← b.sum_repr (exteriorPower.ιMulti ℝ k (v x))]
    simp only [map_sum, map_smul]
  simp_rw [heq]
  apply FrameData.VectorSmoothAt.sum
  intro t
  have hc : VectorSmoothAt A
      (fun x => b.repr (exteriorPower.ιMulti ℝ k (v x)) t) p := by
    simp only [b, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    refine (FrameData.VectorSmoothAt.pi hv).postcomp
      (h := fun w : Fin k → Euclidean r =>
        (Matrix.of fun i j => (Pi.basisFun ℝ (Fin r)).coord
          ((Set.powersetCard.ofFinEmbEquiv.symm t) j) (w i)).det) ?_
    simp only [Matrix.det_apply, Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr]
    fun_prop
  exact hc.postcomp (contDiff_id.smul contDiff_const)

/-- Polynomial matrix on exterior coordinates induced by an arbitrary linear operator. -/
noncomputable def exteriorOperator {r k s : ℕ}
    (L : (⋀[ℝ]^k (Euclidean r)) ≃ₗ[ℝ] Euclidean s)
    (A : Euclidean r →L[ℝ] Euclidean r) : Euclidean s →L[ℝ] Euclidean s :=
  LinearMap.toContinuousLinearMap
    (L.toLinearMap.comp ((exteriorPower.map k A.toLinearMap).comp L.symm.toLinearMap))

theorem exteriorOperator_smooth {d r k s : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {A : Set (ModelChart d a X)}
    (L : (⋀[ℝ]^k (Euclidean r)) ≃ₗ[ℝ] Euclidean s)
    {T : X → (Euclidean r →L[ℝ] Euclidean r)} {p : X}
    (hT : VectorSmoothAt A T p) :
    VectorSmoothAt A (fun x => exteriorOperator L (T x)) p := by
  classical
  have hcol (l : Fin s) : VectorSmoothAt A
      (fun x => exteriorOperator L (T x) (Pi.single l 1)) p := by
    let b := (Pi.basisFun ℝ (Fin r)).exteriorPower k
    let z := L.symm (Pi.single l 1)
    have heq (x : X) : exteriorOperator L (T x) (Pi.single l 1) =
        ∑ t : Set.powersetCard (Fin r) k,
          b.repr z t • L (exteriorPower.map k (T x).toLinearMap (b t)) := by
      change L (exteriorPower.map k (T x).toLinearMap z) = _
      conv_lhs => rw [← b.sum_repr z]
      simp only [map_sum, map_smul]
    simp_rw [heq]
    apply FrameData.VectorSmoothAt.sum
    intro t
    have hw : VectorSmoothAt A
        (fun x => L (exteriorPower.map k (T x).toLinearMap (b t))) p := by
      simp only [b, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
        exteriorPower.map_apply_ιMulti]
      apply wedgeCoordinates_smooth L.toLinearMap
      intro j
      exact hT.clm_apply (FrameData.VectorSmoothAt.const _ _ p)
    exact hw.postcomp (h := fun y : Euclidean s => b.repr z t • y) (by fun_prop)
  have heq (x : X) : exteriorOperator L (T x) =
      QuotientBundles.columnOperator (fun l => exteriorOperator L (T x) (Pi.single l 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hh := (Pi.basisFun ℝ (Fin s)).sum_equivFun v
    conv_lhs => rw [← hh]
    rw [QuotientBundles.columnOperator_apply]
    simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  exact (columnOperator_smooth hcol).congr (Filter.Eventually.of_forall fun x => (heq x).symm)

noncomputable def CoordinatePresentation.exterior {n r : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (C : CoordinatePresentation S r ι E) (k : ℕ) :
    CoordinatePresentation S (r.choose k) ι (fun p => ⋀[ℝ]^k (E p)) where
  domain := C.domain
  isOpen_domain := C.isOpen_domain
  covers := C.covers
  coord i p hp := (exteriorEquiv k (C.coord i p hp)).trans (exteriorModelCoordinates r k)
  transition i j p := exteriorOperator (exteriorModelCoordinates r k) (C.transition i j p)
  transition_eq i j p hi hj v := by
    have hT : (C.transition i j p).toLinearMap =
        ((C.coord i p hi).symm.trans (C.coord j p hj)).toLinearMap := by
      apply LinearMap.ext
      intro x
      exact C.transition_eq i j p hi hj x
    change exteriorModelCoordinates r k (exteriorPower.map k (C.transition i j p).toLinearMap
      ((exteriorModelCoordinates r k).symm v)) = _
    rw [hT]
    change _ = exteriorModelCoordinates r k (exteriorPower.map k (C.coord j p hj).toLinearMap
      (exteriorPower.map k (C.coord i p hi).symm.toLinearMap
        ((exteriorModelCoordinates r k).symm v)))
    rw [show ((C.coord i p hi).symm.trans (C.coord j p hj)).toLinearMap =
      (C.coord j p hj).toLinearMap.comp (C.coord i p hi).symm.toLinearMap from rfl,
      exteriorPower.map_comp]
    rfl
  smooth i j p hi hj := exteriorOperator_smooth _ (C.smooth i j p hi hj)


theorem exists_exterior : Specs.SmoothManifolds.Ch05.BundleOperations.exists_exteriorType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B k
  obtain ⟨V, hbase, hcoord⟩ := ((bundlePresentation B).exterior k).exists_bundle
  letI := V.topology
  refine ⟨{ space := V
            modelEquiv := exteriorModelCoordinates r k
            baseSet := hbase
            coordinates := ?_ }⟩
  intro i p hp v
  rw [hcoord i p hp]
  exact congrArg (exteriorModelCoordinates r k)
    (exteriorEquiv_apply_ιMulti k (B.fiberCoordinates i p hp) v)



/-- A local extension in one base chart gives vector-valued smoothness. -/
theorem vectorSmoothAt_of_chart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : M → V) (p : M) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c p).val ∈ U)
    (F : Euclidean n → V) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (he : (fun q => F (c q).val) =ᶠ[𝓝 p] f) :
    VectorSmoothAt S.smoothStructure.val f p := by
  refine ⟨?_, ?_⟩
  · exact ((hF.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
      (f := fun q => (c q).val)
      (continuous_subtype_val.continuousAt.comp (f := fun q => c q) (c.continuousAt hp))).congr he
  · intro d hd hpd
    obtain ⟨W, hW, hpW, G, hG, heG⟩ := chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 d hd c hc) hpd hp
    refine ⟨W ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage hW hU,
      ⟨hpW, ?_⟩, F ∘ G, hF.comp (hG.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
    · change G (d p).val ∈ U
      rw [heG.eq_of_nhds]
      exact hpU
    · exact (heG.fun_comp F).trans he

/-- Tangent transitions on the original maximal base atlas. -/
noncomputable def tangentTransition {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (K : FiberCoordinates S) (c d : TangentIndex S) (p : M) :
    Euclidean n →L[ℝ] Euclidean n := by
  classical
  exact if hc : p ∈ c.val.source then if hd : p ∈ d.val.source then
    (((K.equiv c.val c.property p hc).symm.trans
      (K.equiv d.val d.property p hd)).toContinuousLinearEquiv :
        Euclidean n →L[ℝ] Euclidean n) else 0 else 0

@[simp] theorem tangentTransition_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (K : FiberCoordinates S) (c d : TangentIndex S) (p : M)
    (hc : p ∈ c.val.source) (hd : p ∈ d.val.source) (v : Euclidean n) :
    tangentTransition K c d p v = K.equiv d.val d.property p hd
      ((K.equiv c.val c.property p hc).symm v) := by
  simp only [tangentTransition, dite_eq_left hc, dite_eq_left hd]
  rfl

noncomputable def tangentPresentation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (K : FiberCoordinates S) :
    CoordinatePresentation S n (TangentIndex S) (TangentSpace S) where
  domain c := c.val.source
  isOpen_domain c := c.val.open_source
  covers p := by
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨⟨c,hc⟩,hp⟩
  coord c p hp := K.equiv c.val c.property p hp
  transition := tangentTransition K
  transition_eq := tangentTransition_apply K
  smooth c d p hc hd := by
    obtain ⟨U, hU, hpU, F, hF, he⟩ := TangentBundle.transition_smooth
      S K c.val d.val c.property d.property p hc hd
    apply vectorSmoothAt_of_chart S (tangentTransition K c d) p c.val c.property hc U hU hpU F hF
    have hcp := continuous_subtype_val.continuousAt.comp (c.val.continuousAt hc)
    filter_upwards [c.val.open_source.mem_nhds hc, d.val.open_source.mem_nhds hd,
      hcp.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqc hqd hqU
    apply ContinuousLinearMap.ext
    intro v
    rw [tangentTransition_apply K c d q hqc hqd]
    exact he q hqc hqd hqU v

/-- The sigma tangent bundle and the vector-bundle total space have identical
smooth local fiber coordinates. -/
theorem exists_tangentRealization :
    Specs.SmoothManifolds.Ch05.BundleOperations.exists_tangentRealizationType.{u} := by
  intro n a M _ S TB
  let C := tangentPresentation S TB.fiberCoordinates
  obtain ⟨V, hbase, hcoord⟩ := C.exists_bundle
  letI := V.topology
  letI := TB.topology
  refine ⟨{ space := V, baseSet := hbase, coordinates := hcoord, smooth_to_original := ?_, smooth_from_original := ?_ }⟩
  · intro q
    obtain ⟨c, hc⟩ := V.bundle.covers q.proj
    have hqc : q.proj ∈ c.val.source := by
      change q.proj ∈ C.domain c
      rw [← hbase c]
      exact hc
    apply TangentBundle.lift_smoothAt_of_coeff S TB V.bundle.totalManifold
      (fun q => (⟨q.proj, q.snd⟩ : TangentBundleData.TotalSpace S)) q
      c.val c.property hqc (fun q => ((V.bundle.trivialization c) q).2)
      (V.bundle.projection_smooth q)
      (Frames.trivializationCoordinates_smoothAt V.bundle c q hc)
    have hev := (V.bundle.projection_smooth q).1.preimage_mem_nhds
      (c.val.open_source.mem_nhds hqc)
    filter_upwards [hev] with y hy
    exact ⟨hy, hcoord c y.proj hy y.snd⟩
  · intro q
    obtain ⟨c, hc, hqc⟩ := S.smoothStructure.property.1.1 q.1
    let i : TangentIndex S := ⟨c,hc⟩
    have hi : q.1 ∈ V.bundle.baseSet i := (hbase i).symm ▸ hqc
    have hid := manifoldContDiff_id (⊤ : ℕ∞) TB.manifold.smoothStructure.val
      TB.manifold.smoothStructure.property.1
    apply Frames.smoothAt_from_trivialization V.bundle TB.manifold.smoothStructure.property.1
      i hi (TangentBundle.projection_smooth S TB q)
      (TangentBundle.chartFiber_smoothAt S TB TB.manifold id q c hc hqc (hid q))
      (fun _ => rfl)
    have hev := (TangentBundle.projection_smooth S TB q).1.preimage_mem_nhds
      (c.open_source.mem_nhds hqc)
    filter_upwards [hev] with y hy
    exact (hcoord i y.1 hy y.2).trans
      (TangentBundle.chartFiber_eq S TB c hc y hy).symm

theorem exists_cotangent :
    Specs.SmoothManifolds.Ch05.BundleOperations.exists_cotangentType.{u} := by
  intro n a M _ S
  obtain ⟨TB⟩ := TangentBundle.exists_bundle S
  obtain ⟨R⟩ := exists_tangentRealization S TB
  letI := R.space.topology
  obtain ⟨D⟩ := exists_dual R.space.bundle
  exact ⟨{ tangent := TB, realization := R, dual := D }⟩

/-- Smooth maps to a bundle pullback are detected by the base and ambient map. -/
theorem pullback_smooth_lift {n m r d : ℕ} {a b c : ModelKind}
    {M : Type u} {P : Type v} {X : Type z}
    [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace X]
    {S : SmoothManifold n a M} {ι : Type t} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) {T : SmoothManifold m b P}
    {f : P → M} (F : PullbackBundle B T f) (R : SmoothManifold d c X)
    (g : X → P) (v : ∀ x, E (f (g x)))
    (hg : IsSmoothMap R T g)
    (hv : IsSmoothMap R B.totalManifold (fun x => ⟨f (g x), v x⟩)) :
    letI := F.space.topology
    IsSmoothMap R F.space.bundle.totalManifold (fun x => ⟨g x, v x⟩) := by
  letI := F.space.topology
  intro x
  obtain ⟨i, hi⟩ := F.space.bundle.covers (g x)
  have hiB : f (g x) ∈ B.baseSet i := by
    simpa only [F.baseSet, mem_preimage] using hi
  have hcoord := FrameData.VectorSmoothAt.comp
    (g := fun y : X => (⟨f (g y), v y⟩ : Bundle.TotalSpace (Euclidean r) E))
    B.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt B i
      (⟨f (g x), v x⟩ : Bundle.TotalSpace (Euclidean r) E) hiB) (hv x)
  apply Frames.smoothAt_from_trivialization F.space.bundle R.smoothStructure.property.1
    i hi (hg x) hcoord (fun _ => rfl)
  have hopen : IsOpen (F.space.bundle.baseSet i) :=
    F.space.bundle.trivialization_baseSet i ▸ (F.space.bundle.trivialization i).open_baseSet
  filter_upwards [(hg x).1.preimage_mem_nhds (hopen.mem_nhds hi)] with y hy
  exact F.coordinates i (g y) (by simpa only [F.baseSet, mem_preimage] using hy) (v y)




/-- The normal bundle is the smooth quotient by the embedded tangent image. -/
theorem exists_normal : Specs.SmoothManifolds.Ch05.BundleOperations.exists_normalType.{u} := by
  intro m n a b P M _ _ T S i hi
  classical
  obtain ⟨TB⟩ := TangentBundle.exists_bundle T
  obtain ⟨SB⟩ := TangentBundle.exists_bundle S
  obtain ⟨TR⟩ := exists_tangentRealization T TB
  obtain ⟨SR⟩ := exists_tangentRealization S SB
  letI := TB.topology
  letI := SB.topology
  letI := TR.space.topology
  letI := SR.space.topology
  obtain ⟨PB⟩ := exists_pullback SR.space.bundle T i hi.1
  letI := PB.space.topology
  let L := differential T S i hi.1
  have hL : ∀ p, IsDifferential T S i p (L p) := differential_spec T S i hi.1
  have hambient : IsSmoothMap TR.space.bundle.totalManifold SR.space.bundle.totalManifold
      (fun q => (⟨i q.proj, L q.proj q.snd⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) := by
    have hm := TangentBundle.map_smooth T S TB SB i hi.1 L hL
    have hcomp := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ TB.manifold.smoothStructure.property.1.1
      (fun q : Bundle.TotalSpace (Euclidean m) (TangentSpace T) =>
        (⟨q.proj,q.snd⟩ : TangentBundleData.TotalSpace T))
      (totalMap T S i L) TR.smooth_to_original hm
    exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ SB.manifold.smoothStructure.property.1.1
      (fun q : Bundle.TotalSpace (Euclidean m) (TangentSpace T) =>
        (⟨i q.proj, L q.proj q.snd⟩ : TangentBundleData.TotalSpace S))
      (fun q : TangentBundleData.TotalSpace S =>
        (⟨q.1,q.2⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)))
      hcomp SR.smooth_from_original
  have hsm : IsSmoothMap TR.space.bundle.totalManifold PB.space.bundle.totalManifold
      (fun q => (⟨q.proj, L q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean n) (fun p => TangentSpace S (i p)))) :=
    pullback_smooth_lift SR.space.bundle PB TR.space.bundle.totalManifold
      TotalSpace.proj (fun q => L q.proj q.snd) TR.space.bundle.projection_smooth hambient
  let A : SmoothBundleMorphism TR.space.bundle PB.space.bundle := ⟨L,hsm⟩
  have hdim := embedding_differential_injective T S i hi L hL
  have him := (ConstantRankBundles.kernel_image_subbundles TR.space.bundle PB.space.bundle A m
    (fun p => (hdim p).2)).2.1
  have hframe := smoothSubbundle_of_adapted PB.space.bundle (fun p => LinearMap.range (L p)) him
  obtain ⟨Q⟩ := QuotientBundles.exists_smoothQuotient PB.space.bundle
    (fun p => LinearMap.range (L p)) m hframe
  refine ⟨{
    sourceTangent := TB
    ambientTangent := SB
    sourceRealization := TR
    ambientRealization := SR
    pullback := PB
    differential := L
    isDifferential := hL
    injective := fun p => (hdim p).1
    differential_smooth := hsm
    image_smooth := him
    image_frame := hframe
    quotient := Q }⟩

end SmoothManifolds.BundleOperations
