import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalResidueCorrection
import LinearAlgebraicGroups.Descent.Lang
import LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Topology TopologicalSpace

universe u

namespace LinearAlgebraicGroups.RamifiedExceptionalResidueCorrection

open Specs.RamifiedExceptionalResidueCorrection

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- The points where membership in a set is forced by membership in its
closure are dense open locally for constructible sets. -/
private theorem constructible_dense_open_coborder {s : Set X} (hs : IsConstructible s) :
    Dense (interior (coborder s)) := by
  suffices Dense (interior (coborder s)) ∧ Dense (interior (coborder sᶜ)) from this.1
  refine hs.empty_union_induction (fun U hU _ => ?_) (fun s _ t _ hs ht => ?_)
    (fun s _ hs => ?_)
  · exact ⟨by simpa only [(isLocallyClosed_iff_isOpen_coborder.mp
          hU.isLocallyClosed).interior_eq] using (dense_coborder (s := U)),
      by simpa only [(isLocallyClosed_iff_isOpen_coborder.mp
          hU.isClosed_compl.isLocallyClosed).interior_eq] using (dense_coborder (s := Uᶜ))⟩
  · have hu : coborder s ∩ coborder t ⊆ coborder (s ∪ t) := by
      intro x hx
      simp only [Set.mem_inter_iff, mem_coborder_iff_imp] at hx ⊢
      rw [closure_union]
      exact fun h => h.elim (fun h => Or.inl (hx.1 h)) (fun h => Or.inr (hx.2 h))
    have hi : coborder sᶜ ∩ coborder tᶜ ⊆ coborder ((s ∪ t)ᶜ) := by
      rw [Set.compl_union]
      intro x hx
      simp only [Set.mem_inter_iff, mem_coborder_iff_imp] at hx ⊢
      exact fun h => ⟨hx.1 (closure_mono Set.inter_subset_left h),
        hx.2 (closure_mono Set.inter_subset_right h)⟩
    refine ⟨?_, ?_⟩
    · have h := hs.1.inter_of_isOpen_right ht.1 isOpen_interior
      exact h.mono (by rw [← interior_inter]; exact interior_mono hu)
    · have h := hs.2.inter_of_isOpen_right ht.2 isOpen_interior
      exact h.mono (by rw [← interior_inter]; exact interior_mono hi)
  · simpa only [compl_compl] using hs.symm

private theorem constructible_open_in_closure [NoetherianSpace X] {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) :
    ∃ U : Set X, IsOpen U ∧ (U ∩ s).Nonempty ∧ U ∩ closure s ⊆ s := by
  let Z := closure s
  let t : Set Z := Subtype.val ⁻¹' s
  have ht : IsConstructible t := hs.preimage continuous_subtype_val
    (fun W hW _ => (NoetherianSpace.isCompact _).isRetrocompact
      (hW.preimage continuous_subtype_val))
  have hd : Dense t := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    rw [closure_subtype]
    change z.val ∈ closure (Subtype.val '' (Subtype.val ⁻¹' s : Set Z))
    rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    change z.val ∈ closure (s ∩ closure s)
    rw [Set.inter_eq_left.mpr subset_closure]
    exact z.property
  have hct : coborder t = t := by rw [coborder_eq_union_closure_compl, hd.closure_eq,
    Set.compl_univ, Set.union_empty]
  have hdo := constructible_dense_open_coborder ht
  rw [hct] at hdo
  have : Nonempty Z := hne.mono subset_closure |>.to_subtype
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior t))
  obtain ⟨z, hz⟩ := hdo.nonempty
  have hzU : z.val ∈ U := by
    have : z ∈ Subtype.val ⁻¹' U := hpre.symm ▸ hz
    exact this
  refine ⟨U, hU, ⟨z.val, hzU, interior_subset (s := t) hz⟩, ?_⟩
  intro x hx
  have hxi : (⟨x, hx.2⟩ : Z) ∈ interior t := hpre ▸ hx.1
  exact interior_subset (s := t) hxi

private theorem constructible_meets_closedPoints [NoetherianSpace X] [JacobsonSpace X]
    {s : Set X} (hs : IsConstructible s) (hne : s.Nonempty) :
    (s ∩ closedPoints X).Nonempty := by
  obtain ⟨U, hU, hn, hsub⟩ := constructible_open_in_closure hs hne
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
    (Z := U ∩ closure s)
    (hn.mono (fun _ h => ⟨h.1, subset_closure h.2⟩))
    (hU.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  exact ⟨x, hsub hx, hxc⟩

private theorem closed_of_constructible_subgroup {M : Type*} [Group M]
    [TopologicalSpace M] [NoetherianSpace M]
    (hl : ∀ a : M, Continuous (a * ·)) (hr : ∀ a : M, Continuous (· * a))
    (hi : Continuous (Inv.inv : M → M)) (S : Subgroup M)
    (hs : IsConstructible (S : Set M)) : IsClosed (S : Set M) := by
  obtain ⟨U, hU, ⟨u, hu, huS⟩, hsub⟩ :=
    constructible_open_in_closure hs ⟨1, S.one_mem⟩
  apply closure_subset_iff_isClosed.mp
  intro x hx
  have hmap : Set.MapsTo (fun y => y⁻¹ * u) (S : Set M) S :=
    fun y hy => S.mul_mem (S.inv_mem hy) huS
  have hx' := hmap.closure ((hr u).comp hi) hx
  have hmem : x⁻¹ * u ∈ (x * ·) ⁻¹' U := by
    change x * (x⁻¹ * u) ∈ U
    simpa using hu
  obtain ⟨a, haU, ha⟩ := mem_closure_iff.mp hx' _ (hU.preimage (hl x)) hmem
  have hmap' : Set.MapsTo (· * a) (S : Set M) S := fun y hy => S.mul_mem hy ha
  have hxS : x * a ∈ S := hsub ⟨haU, hmap'.closure (hr a) hx⟩
  simpa using S.mul_mem hxS (S.inv_mem ha)

private theorem connected_of_generators {M : Type*} [Group M] [TopologicalSpace M]
    (hl : ∀ a : M, Continuous (a * ·))
    (hi : Continuous (Inv.inv : M → M)) {t : Set M}
    (ht : ∀ x ∈ t, ∃ C : Set M, IsPreconnected C ∧
      C ⊆ Subgroup.closure t ∧ 1 ∈ C ∧ x ∈ C) :
    _root_.IsConnected (Subgroup.closure t : Set M) := by
  let S := Subgroup.closure t
  let w := { C : Set M // IsPreconnected C ∧ C ⊆ S ∧ 1 ∈ C }
  have cover (x) (hx : x ∈ S) : ∃ C : w, x ∈ (C : Set M) := by
    refine Subgroup.closure_induction (k := t) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨C, hc, hC, h1, hy'⟩ := ht y hy
      exact ⟨⟨C, hc, hC, h1⟩, hy'⟩
    · exact ⟨⟨{1}, isPreconnected_singleton, Set.singleton_subset_iff.mpr S.one_mem,
        Set.mem_singleton _⟩, Set.mem_singleton _⟩
    · intro x y hx hy hx' hy'
      obtain ⟨A, hA⟩ := hx'
      obtain ⟨B, hB⟩ := hy'
      let C := (A : Set M) ∪ (x * ·) '' (B : Set M)
      have hxB : x ∈ (x * ·) '' (B : Set M) := ⟨1, B.2.2.2, mul_one x⟩
      refine ⟨⟨C, A.2.1.union x hA hxB (B.2.1.image _ (hl x).continuousOn), ?_,
        Or.inl A.2.2.2⟩, Or.inr ⟨y, hB, rfl⟩⟩
      rintro z (hz | ⟨v, hv, rfl⟩)
      · exact A.2.2.1 hz
      · exact S.mul_mem hx (B.2.2.1 hv)
    · intro x _ hx
      obtain ⟨A, hA⟩ := hx
      exact ⟨⟨Inv.inv '' (A : Set M), A.2.1.image _ hi.continuousOn,
        fun _ ⟨a, ha, e⟩ => e ▸ S.inv_mem (A.2.2.1 ha),
        ⟨1, A.2.2.2, inv_one⟩⟩, ⟨x, hA, rfl⟩⟩
  have he : (⋃ C : w, (C : Set M)) = (S : Set M) := by
    ext x
    exact ⟨fun hx => let ⟨C, hC⟩ := Set.mem_iUnion.mp hx; C.2.2.1 hC,
      fun hx => Set.mem_iUnion.mpr (cover x hx)⟩
  exact ⟨⟨1, S.one_mem⟩, he ▸ isPreconnected_iUnion
    ⟨1, Set.mem_iInter.mpr fun C => C.2.2.2⟩ (fun C => C.2.1)⟩

end Topology

section GeometricPoints

variable {k : Type u} [Field k]

local notation "K" => AlgebraicClosure k
local notation "R" => CommAlgCat.of K K

open private pointsClosedEquiv point_in_range_of_closed_point from
  LinearAlgebraicGroups.Descent.SmoothLang

private abbrev rationalEquiv (X : SchemeOver k) :
    Points (geometricScheme X) R ≃ GeometricPoints X :=
  baseChangePointsEquiv K X R

private abbrev rationalGroupEquiv (G : Specs.GroupScheme k) :
    Points ((groupBaseChange k K).obj G).X R ≃* GeometricPoints G.X :=
  baseChangePointGroupEquiv K G R

private theorem rational_left_eq_lift {X : SchemeOver k} (p : GeometricPoints X) :
    ((rationalEquiv X).symm p).left =
      pullback.lift p.left (𝟙 (Spec (CommRingCat.of K))) (by
        change p.left ≫ X.hom = 𝟙 (Spec (CommRingCat.of K)) ≫ fieldSpecMap k K
        rw [Category.id_comp]
        exact Over.w p) := by
  let r := (rationalEquiv X).symm p
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact congrArg (fun q : GeometricPoints X => q.left) ((rationalEquiv X).apply_symm_apply p)
  · rw [pullback.lift_snd]
    exact (Over.w r).trans (Spec.map_id _)

private theorem carrier_eq_eval {X : SchemeOver k} (p : GeometricPoints X) :
    geometricCarrier p = ((rationalEquiv X).symm p).left (IsLocalRing.closedPoint K) := by
  rw [rational_left_eq_lift]
  rfl

private theorem carrier_project {X : SchemeOver k} (p : GeometricPoints X) :
    pullback.fst X.hom (fieldSpecMap k K) (geometricCarrier p) =
      p.left (IsLocalRing.closedPoint K) := by
  have h := congrArg (fun q : GeometricPoints X => q.left)
    ((rationalEquiv X).apply_symm_apply p)
  rw [carrier_eq_eval]
  exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ X.left =>
    f (IsLocalRing.closedPoint K)) h

private theorem carrier_map {X Y : SchemeOver k} (f : X ⟶ Y) (p : GeometricPoints X) :
    geometricCarrier (p ≫ f) = ((baseChange k K).map f).left (geometricCarrier p) := by
  have h : (rationalEquiv Y).symm (p ≫ f) =
      (rationalEquiv X).symm p ≫ (baseChange k K).map f := by
    apply (rationalEquiv Y).injective
    simp only [Equiv.apply_symm_apply]
    exact (baseChangePointsSchemeNaturality k K f R _).trans
      (congrArg (· ≫ f) ((rationalEquiv X).apply_symm_apply p)) |>.symm
  rw [carrier_eq_eval, h, carrier_eq_eval]
  rfl

private instance geometricFiniteType (X : SchemeOver k) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (geometricScheme X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom (fieldSpecMap k K)))

private instance geometricQuasiCompact (X : SchemeOver k) [QuasiCompact X.hom] :
    QuasiCompact (geometricScheme X).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X.hom (fieldSpecMap k K)))

private theorem carrier_range {X : SchemeOver k} [LocallyOfFiniteType X.hom] :
    Set.range (geometricCarrier (X := X)) = closedPoints (geometricScheme X).left := by
  let e := (rationalEquiv X).symm.trans (pointsClosedEquiv (geometricScheme X))
  have h : geometricCarrier (X := X) = fun p => (e p).val := by
    funext p
    exact carrier_eq_eval p
  ext x
  rw [h]
  exact ⟨fun ⟨p, hp⟩ => hp ▸ (e p).property,
    fun hx => let ⟨p, hp⟩ := e.surjective ⟨x, hx⟩
              ⟨p, congrArg Subtype.val hp⟩⟩

private theorem carrier_image_iff {X Y : SchemeOver k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : GeometricPoints Y) :
    geometricCarrier p ∈ Set.range ((baseChange k K).map f).left ↔
      p ∈ Set.range (fun q : GeometricPoints X => q ≫ f) := by
  constructor
  · intro hp
    rw [carrier_eq_eval] at hp
    obtain ⟨r, hr⟩ := point_in_range_of_closed_point ((baseChange k K).map f) _ hp
    refine ⟨rationalEquiv X r, ?_⟩
    exact (baseChangePointsSchemeNaturality k K f R r).symm.trans
      ((congrArg (rationalEquiv Y) hr).trans ((rationalEquiv Y).apply_symm_apply p))
  · rintro ⟨q, rfl⟩
    exact ⟨geometricCarrier q, (carrier_map f q).symm⟩

private theorem geometric_isPullback {X Y : SchemeOver k} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom (fieldSpecMap k K)) ((baseChange k K).map f).left
      f.left (pullback.fst Y.hom (fieldSpecMap k K)) := by
  let πX := pullback.fst X.hom (fieldSpecMap k K)
  let πY := pullback.fst Y.hom (fieldSpecMap k K)
  let F := ((baseChange k K).map f).left
  have hX : IsPullback πX (geometricScheme X).hom X.hom (fieldSpecMap k K) :=
    .of_hasPullback _ _
  have hY : IsPullback πY (geometricScheme Y).hom Y.hom (fieldSpecMap k K) :=
    .of_hasPullback _ _
  have hX' : IsPullback (F ≫ (geometricScheme Y).hom) πX
      (fieldSpecMap k K) (f.left ≫ Y.hom) := by
    rw [Over.w ((baseChange k K).map f), Over.w f]
    exact hX.flip
  have hcomm : F ≫ πY = πX ≫ f.left := by simp [F, πX, πY]
  exact (IsPullback.of_right hX' hcomm hY.flip).flip
 
private theorem carrier_range_map {X Y : SchemeOver k} (f : X ⟶ Y) :
    Set.range ((baseChange k K).map f).left =
      pullback.fst Y.hom (fieldSpecMap k K) ⁻¹' Set.range f.left := by
  have hr := Scheme.image_preimage_eq_of_isPullback (geometric_isPullback f) (Set.univ : Set X.left)
  simp only [Set.preimage_univ, Set.image_univ] at hr
  exact hr

private theorem geometric_noetherian {X : SchemeOver k}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    NoetherianSpace (geometricScheme X).left := by
  let Y := geometricScheme X
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  exact @IsNoetherian.noetherianSpace Y.left ⟨⟩

private def rationalStructural (Y : SchemeOver K) :
    Y ⟶ (testSpec K).obj (op R) :=
  Over.homMk Y.hom (by
    change Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)) = Y.hom
    rw [Algebra.algebraMap_self]
    change Y.hom ≫ Spec.map (𝟙 (CommRingCat.of K)) = Y.hom
    rw [Spec.map_id, Category.comp_id])

private theorem rational_comp_structural {Y : SchemeOver K}
    (p : Points Y R) : p ≫ rationalStructural Y = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact (Over.w p).trans (Spec.map_id _)

private theorem continuous_of_geo_morphism {X : SchemeOver k}
    (f : geometricScheme X ⟶ geometricScheme X) (t : GeometricPoints X → GeometricPoints X)
    (ht : ∀ p, (rationalEquiv X).symm (t p) = (rationalEquiv X).symm p ≫ f) :
    @Continuous _ _ (geometricTopology X) (geometricTopology X) t := by
  let := geometricTopology X
  have h : IsInducing (geometricCarrier (X := X)) := ⟨rfl⟩
  apply h.continuous_iff.mpr
  convert f.left.continuous.comp h.continuous using 1
  funext p
  rw [Function.comp_apply, Function.comp_apply, carrier_eq_eval, ht, carrier_eq_eval]
  rfl

private theorem translations_continuous (G : Specs.GroupScheme k) :
    letI := geometricTopology G.X
    (∀ a : GeometricPoints G.X, Continuous (a * ·)) ∧
    (∀ a : GeometricPoints G.X, Continuous (· * a)) ∧
    Continuous (Inv.inv : GeometricPoints G.X → GeometricPoints G.X) := by
  let B := (groupBaseChange k K).obj G
  let e := rationalGroupEquiv G
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · apply continuous_of_geo_morphism
      ((rationalStructural B.X ≫ e.symm a) * 𝟙 B.X)
    intro p
    change e.symm (a * p) = e.symm p ≫ ((rationalStructural B.X ≫ e.symm a) * 𝟙 B.X)
    rw [MonObj.comp_mul, ← Category.assoc, rational_comp_structural, Category.id_comp,
      Category.comp_id, map_mul]
  · apply continuous_of_geo_morphism
      (𝟙 B.X * (rationalStructural B.X ≫ e.symm a))
    intro p
    change e.symm (p * a) = e.symm p ≫ (𝟙 B.X * (rationalStructural B.X ≫ e.symm a))
    rw [MonObj.comp_mul, ← Category.assoc, rational_comp_structural, Category.id_comp,
      Category.comp_id, map_mul]
  · let f : B.X ⟶ B.X := (𝟙 B.X)⁻¹
    apply continuous_of_geo_morphism f
    intro p
    change e.symm p⁻¹ = e.symm p ≫ (𝟙 B.X)⁻¹
    rw [GrpObj.comp_inv, Category.comp_id, map_inv]

end GeometricPoints

section Realization

variable {k : Type u} [Field k]

local notation "K" => AlgebraicClosure k

private theorem constructible_ext_on_closedPoints {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [JacobsonSpace X] {s t : Set X}
    (hs : IsConstructible s) (ht : IsConstructible t)
    (h : s ∩ closedPoints X = t ∩ closedPoints X) : s = t := by
  have aux {a b : Set X} (ha : IsConstructible a) (hb : IsConstructible b)
      (hab : a ∩ closedPoints X ⊆ b ∩ closedPoints X) : a ⊆ b := by
    intro x hx
    by_contra hx'
    obtain ⟨y, hy, hyc⟩ := constructible_meets_closedPoints (ha.sdiff hb)
      ⟨x, hx, hx'⟩
    exact hy.2 (hab ⟨hy.1, hyc⟩).1
  exact (aux hs ht h.le).antisymm (aux ht hs h.symm.le)

private theorem parameter_image_closed (G : Specs.AffineAlgebraicGroup k)
    (S : Subgroup (GeometricPoints G.val.X)) (P : Parameterization G S) :
    ∃ C : Closeds G.val.X.left, let π := pullback.fst G.val.X.hom (fieldSpecMap k K)
      (∀ p : GeometricPoints G.val.X, π (geometricCarrier p) ∈ C ↔ p ∈ S) ∧
      geometricCarrier '' (S : Set _) = (π ⁻¹' (C : Set _)) ∩ closedPoints _ := by
  let X := G.val.X
  let Y := geometricScheme X
  let π := pullback.fst X.hom (fieldSpecMap k K)
  let C : Set X.left := ⋃ i, Set.range (P.map i).left
  let B : Set Y.left := ⋃ i, Set.range ((baseChange k K).map (P.map i)).left
  have : LocallyOfFiniteType X.hom := G.property.2.1
  have : QuasiCompact X.hom := G.property.2.2
  have : NoetherianSpace Y.left := geometric_noetherian (X := X)
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hBC : B = π ⁻¹' C := by
    simp only [B, C, Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => carrier_range_map (P.map i)
  have hB : IsConstructible B := by
    let : Finite P.Index := P.finite
    apply IsConstructible.iUnion
    intro i
    let f : (geometricScheme (P.source i)).left ⟶ Y.left :=
      ((baseChange k K).map (P.map i)).left
    have : LocallyOfFiniteType (P.source i).hom := P.finiteType i
    have : QuasiCompact (P.source i).hom := P.quasiCompact i
    have : NoetherianSpace (geometricScheme (P.source i)).left := geometric_noetherian
    have : LocallyOfFiniteType (f ≫ Y.hom) := by
      change LocallyOfFiniteType (((baseChange k K).map (P.map i)).left ≫
        (geometricScheme X).hom)
      rw [Over.w]
      exact geometricFiniteType (P.source i)
    have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f Y.hom
    have : LocallyOfFinitePresentation f := inferInstance
    have : QuasiCompact f := inferInstance
    simpa only [Set.image_univ] using f.isConstructible_image IsConstructible.univ
  have hpre : geometricCarrier ⁻¹' B = (S : Set _) := by
    rw [← P.image_eq]
    ext p
    change geometricCarrier p ∈ B ↔ _
    simp only [B, Set.mem_iUnion]
    exact exists_congr fun i =>
      @carrier_image_iff k _ (P.source i) X (P.finiteType i) G.property.2.1 (P.map i) p
  let := geometricTopology X
  have hind : IsInducing (geometricCarrier (X := X)) := ⟨rfl⟩
  have : NoetherianSpace (GeometricPoints X) := hind.noetherianSpace
  have hS : IsConstructible (S : Set (GeometricPoints X)) := by
    rw [← hpre]
    exact hB.preimage hind.continuous
      (fun U hU _ => (NoetherianSpace.isCompact _).isRetrocompact (hU.preimage hind.continuous))
  obtain ⟨hl, hr, hi⟩ := translations_continuous G.val
  have hSc := closed_of_constructible_subgroup hl hr hi S hS
  obtain ⟨E, hE, hpreE⟩ := hind.isClosed_iff.mp hSc
  have htrace : geometricCarrier '' (S : Set _) = B ∩ closedPoints Y.left := by
    rw [← hpre, Set.image_preimage_eq_inter_range, carrier_range]
  have hBE : B = E := by
    refine constructible_ext_on_closedPoints hB
      (IsConstructible.of_compl
        (IsRetrocompact.isConstructible hE.isOpen_compl
          ((NoetherianSpace.isCompact _).isRetrocompact hE.isOpen_compl))) ?_
    rw [← htrace, ← hpreE, Set.image_preimage_eq_inter_range, carrier_range]
  have hBclosed : IsClosed B := hBE.symm ▸ hE
  have hK : IsIntegralHom (fieldSpecMap k K) := by
    apply IsIntegralHom.SpecMap_iff.mpr
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : IsIntegralHom π := inferInstanceAs (IsIntegralHom (pullback.fst X.hom (fieldSpecMap k K)))
  have hπ : Surjective π := inferInstanceAs (Surjective (pullback.fst X.hom (fieldSpecMap k K)))
  have hC : IsClosed C := by
    have h := π.isClosedMap B hBclosed
    rwa [hBC, Set.image_preimage_eq _ π.surjective] at h
  exact ⟨⟨C, hC⟩, fun p => by
    change geometricCarrier p ∈ π ⁻¹' C ↔ p ∈ (S : Set _)
    rw [← hBC, ← hpre]; rfl, hBC ▸ htrace⟩

open private exists_geometric_point_at_closed reduced_tensor from LinearAlgebraicGroups.Descent.Lang

private abbrev closedOver (X : SchemeOver k) (C : Closeds X.left) : SchemeOver k :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ X.hom)

private abbrev closedInclusion {X : SchemeOver k} (C : Closeds X.left) :
    closedOver X C ⟶ X :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal C).subschemeι

private theorem closed_reduced (X : SchemeOver k) (C : Closeds X.left) :
    IsReduced (closedOver X C).left := by
  let J := Scheme.IdealSheafData.vanishingIdeal C
  refine @IsReduced.of_openCover _ J.subschemeCover.openCover ?_
  intro U
  change IsReduced (Spec (CommRingCat.of (Γ(X.left, U.1) ⧸ J.ideal U)))
  have hJ : (J.ideal U).IsRadical := by
    change ((Scheme.IdealSheafData.vanishingIdeal C).ideal U).IsRadical
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact (affine_isReduced_iff _).mpr ((Ideal.isRadical_iff_quotient_reduced _).mp hJ)

private theorem closed_range (X : SchemeOver k) (C : Closeds X.left) :
    Set.range (closedInclusion C).left = (C : Set X.left) := by
  exact (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal C)

private theorem range_subset_of_geometric {T X : SchemeOver k} [LocallyOfFiniteType T.hom]
    (f : T ⟶ X) (C : Closeds X.left)
    (hf : ∀ p : GeometricPoints T, (p ≫ f).left (IsLocalRing.closedPoint K) ∈ C) :
    Set.range f.left ⊆ C := by
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  have hpre : IsClosed (f.left ⁻¹' (C : Set X.left)) := C.isClosed.preimage f.left.continuous
  have hcp : closedPoints T.left ⊆ f.left ⁻¹' (C : Set X.left) := by
    intro x hx
    obtain ⟨p, hp⟩ := exists_geometric_point_at_closed x hx
    exact hp ▸ hf p
  have h := hpre.closure_subset_iff.mpr hcp
  rw [closure_closedPoints] at h
  exact Set.range_subset_iff.mpr fun x => h (Set.mem_univ x)

private def liftToClosed {T X : SchemeOver k} [IsReduced T.left]
    (f : T ⟶ X) (C : Closeds X.left) (h : Set.range f.left ⊆ C) :
    T ⟶ closedOver X C := by
  let J := Scheme.IdealSheafData.vanishingIdeal C
  have hker : J.subschemeι.ker ≤ f.left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
      ← Scheme.nilradical_eq_bot (X := T.left), ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono
      (TopologicalSpace.Closeds.closure_le.mpr (by simpa using h))
  exact Over.homMk (IsClosedImmersion.lift J.subschemeι f.left hker) (by
    change IsClosedImmersion.lift J.subschemeι f.left hker ≫ J.subschemeι ≫ X.hom = T.hom
    rw [IsClosedImmersion.lift_fac_assoc, Over.w])

private theorem liftToClosed_fac {T X : SchemeOver k} [IsReduced T.left]
    (f : T ⟶ X) (C : Closeds X.left) (h : Set.range f.left ⊆ C) :
    liftToClosed f C h ≫ closedInclusion C = f := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

private theorem closed_points_image {X : SchemeOver k} (C : Closeds X.left)
    (p : GeometricPoints X) :
    p ∈ Set.range (fun q : GeometricPoints (closedOver X C) => q ≫ closedInclusion C) ↔
      p.left (IsLocalRing.closedPoint K) ∈ C := by
  constructor
  · rintro ⟨q, rfl⟩
    have h : (closedInclusion C).left (q.left (IsLocalRing.closedPoint K)) ∈
        Set.range (closedInclusion C).left := Set.mem_range_self _
    rw [closed_range X C] at h
    exact h
  · intro hp
    have : IsReduced (testSpec k |>.obj (op (CommAlgCat.of k K))).left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
    have h : Set.range p.left ⊆ C := by
      rintro _ ⟨x, rfl⟩
      have e : x = IsLocalRing.closedPoint K := Subsingleton.elim
        (α := PrimeSpectrum K) _ _
      exact e.symm ▸ hp
    exact ⟨liftToClosed p C h, liftToClosed_fac p C h⟩

/-- Operation morphisms on a subobject, with their comparison to the ambient
group operations. -/
private structure GroupRestriction {G : Specs.GroupScheme k} {D : SchemeOver k}
    (j : D ⟶ G.X) where
  unit : 𝟙_ (SchemeOver k) ⟶ D
  prod : D ⊗ D ⟶ D
  inv : D ⟶ D
  unit_fac : unit ≫ j = η[G.X]
  prod_fac : prod ≫ j = (j ⊗ₘ j) ≫ μ[G.X]
  inv_fac : inv ≫ j = j ≫ ι[G.X]

private abbrev GroupRestriction.grpObj {G : Specs.GroupScheme k} {D : SchemeOver k}
    {j : D ⟶ G.X} [Mono j] (A : GroupRestriction j) : GrpObj D := by
  have hmul {T : SchemeOver k} (f g : T ⟶ D) :
      lift f g ≫ A.prod ≫ j = (f ≫ j) * (g ≫ j) := by
    rw [A.prod_fac, lift_map_assoc]
    rfl
  refine {
    one := A.unit
    mul := A.prod
    inv := A.inv
    one_mul := ?_
    mul_one := ?_
    mul_assoc := ?_
    left_inv := ?_
    right_inv := ?_ }
  · rw [← cancel_mono j, Category.assoc, A.prod_fac, whiskerRight_comp_tensorHom_assoc,
      A.unit_fac, ← lift_fst_comp_snd_comp, MonObj.lift_comp_one_left, leftUnitor_hom]
  · rw [← cancel_mono j, Category.assoc, A.prod_fac, whiskerLeft_comp_tensorHom_assoc,
      A.unit_fac, ← lift_fst_comp_snd_comp, MonObj.lift_comp_one_right, rightUnitor_hom]
  · let a : (D ⊗ D) ⊗ D ⟶ D := fst _ _ ≫ fst _ _
    let b : (D ⊗ D) ⊗ D ⟶ D := fst _ _ ≫ snd _ _
    let c : (D ⊗ D) ⊗ D ⟶ D := snd _ _
    have hl : A.prod ▷ D = lift (lift a b ≫ A.prod) c := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [a, b, c]
    have hr : (α_ D D D).hom ≫ D ◁ A.prod = lift a (lift b c ≫ A.prod) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [a]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
        congr 1
        apply CartesianMonoidalCategory.hom_ext <;> simp [b, c]
    rw [← cancel_mono j, Category.assoc, hl, hmul]
    rw [← Category.assoc (α_ D D D).hom, hr]
    simp only [Category.assoc, hmul, mul_assoc]
  · rw [← cancel_mono j, Category.assoc, hmul, Category.id_comp, A.inv_fac, Category.assoc,
      A.unit_fac, ← Hom.inv_def, inv_mul_cancel]
    rfl
  · rw [← cancel_mono j, Category.assoc, hmul, Category.id_comp, A.inv_fac, Category.assoc,
      A.unit_fac, ← Hom.inv_def, mul_inv_cancel]
    rfl

private theorem geometric_connected_of_trace {X D : SchemeOver k}
    [LocallyOfFiniteType X.hom] (j : D ⟶ X) [IsClosedImmersion j.left]
    (T : Set (GeometricPoints X)) (hT : @_root_.IsConnected _ (geometricTopology X) T)
    (h : geometricCarrier '' T =
      Set.range ((baseChange k K).map j).left ∩ closedPoints _) :
    ConnectedSpace (geometricScheme D).left := by
  let := geometricTopology X
  have hc : Continuous (geometricCarrier (X := X)) := continuous_induced_dom
  have : JacobsonSpace (geometricScheme X).left :=
    LocallyOfFiniteType.jacobsonSpace (geometricScheme X).hom
  let f := ((baseChange k K).map j).left
  have hj : IsClosedImmersion f :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (geometric_isPullback j) ‹_›
  have hconn := (hT.image _ hc.continuousOn).closure
  rw [h, closure_inter_closedPoints f.isClosedEmbedding.isClosed_range] at hconn
  rw [connectedSpace_iff_univ]
  have : Nonempty (geometricScheme D).left :=
    Set.range_nonempty_iff_nonempty.mp hconn.nonempty
  refine ⟨Set.univ_nonempty, ?_⟩
  apply f.isClosedEmbedding.isEmbedding.isInducing.isPreconnected_image.mp
  rw [Set.image_univ]
  exact hconn.isPreconnected

/-- A finite constructible reduction image generated by connected algebraic
subgroup images is the geometric image of a smooth connected closed subgroup. -/
theorem closedResidueImage : ClosedResidueImage.{u} := by
  intro k _ _ G S P Q
  let X := G.val.X
  let := geometricTopology X
  obtain ⟨C, hC, htrace⟩ := parameter_image_closed G S P
  let D := closedOver X C
  let j : D ⟶ X := closedInclusion C
  have hj : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)
  have hjm : Mono j := by
    constructor
    intro T f g h
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).mp
    exact congrArg (fun m : T ⟶ X => m.left) h
  have hDred : IsReduced D.left := closed_reduced X C
  have : LocallyOfFiniteType X.hom := G.property.2.1
  have : QuasiCompact X.hom := G.property.2.2
  have : IsAffine X.left := G.property.1
  have hDa : IsAffine D.left := isAffine_of_isAffineHom j.left
  have hDf : LocallyOfFiniteType D.hom :=
    inferInstanceAs (LocallyOfFiniteType (j.left ≫ X.hom))
  have hDq : QuasiCompact D.hom := inferInstanceAs (QuasiCompact (j.left ≫ X.hom))
  have hmred : IsReduced (D ⊗ D).left := reduced_tensor D D
  have : IsReduced ((𝟙_ (SchemeOver k)).left) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hmem (p : GeometricPoints X) :
      p ∈ (S : Set _) ↔ p.left (IsLocalRing.closedPoint (AlgebraicClosure k)) ∈ C := by
    rw [← carrier_project p]
    exact (hC p).symm
  have himage : Set.range (fun p : GeometricPoints D => p ≫ j) = (S : Set _) := by
    ext p
    exact (closed_points_image C p).trans (hmem p).symm
  have hfactor (p : GeometricPoints D) : p ≫ j ∈ S := by
    change p ≫ j ∈ (S : Set _)
    rw [← himage]
    exact ⟨p, rfl⟩
  have : LocallyOfFiniteType (𝟙_ (SchemeOver k)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : LocallyOfFiniteType (D ⊗ D).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst D.hom D.hom ≫ D.hom))
  have he : Set.range (η[X] : 𝟙_ (SchemeOver k) ⟶ X).left ⊆ C := by
    apply range_subset_of_geometric
    intro p
    apply (hmem _).mp
    rw [MonObj.one_eq_one X, MonObj.comp_one]
    exact S.one_mem
  have hn : Set.range (j ≫ ι[X]).left ⊆ C := by
    apply range_subset_of_geometric
    intro p
    apply (hmem _).mp
    rw [← Category.assoc, ← Hom.inv_def]
    exact S.inv_mem (hfactor p)
  have hmult : Set.range ((j ⊗ₘ j) ≫ μ[X]).left ⊆ C := by
    apply range_subset_of_geometric
    intro p
    apply (hmem _).mp
    have hp : p = lift (p ≫ fst _ _) (p ≫ snd _ _) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hp, ← Category.assoc, lift_map]
    exact S.mul_mem (hfactor (p ≫ fst _ _)) (hfactor (p ≫ snd _ _))
  let A : GroupRestriction j :=
    ⟨liftToClosed η[X] C he, liftToClosed ((j ⊗ₘ j) ≫ μ[X]) C hmult,
      liftToClosed (j ≫ ι[X]) C hn, liftToClosed_fac _ _ _, liftToClosed_fac _ _ _,
      liftToClosed_fac _ _ _⟩
  let : GrpObj D := A.grpObj
  let H : Specs.AffineAlgebraicGroup k := ⟨Grp.mk D, hDa, hDf, hDq⟩
  let i : H.val ⟶ G.val := Grp.homMk'' j A.unit_fac A.prod_fac
  have hsm : Smooth D.hom := smoothOfReducedOverPerfectField k H.val hDred
  refine ⟨H, i, hj, hDred, hsm, ?_, himage⟩
  have hSconn : _root_.IsConnected (S : Set (GeometricPoints X)) := by
    obtain ⟨hl, _, hinv⟩ := translations_continuous G.val
    rw [← Q.generates]
    apply connected_of_generators hl hinv
    intro z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
    let m := (Q.map t).hom.hom
    have : IsMonHom m := (Q.map t).hom.isMonHom_hom
    refine ⟨Set.range (fun p : GeometricPoints (Q.source t).val.X => p ≫ m),
      (Q.imageConnected t).isPreconnected, ?_, ?_, ht⟩
    · intro x hx
      exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨t, hx⟩)
    · exact ⟨1, MonObj.one_comp m⟩
  apply geometric_connected_of_trace j (S : Set _) hSconn
  rw [carrier_range_map j, closed_range X C]
  exact htrace

end Realization

section Correction

variable {k : Type u} [Field k] [Fintype k]
variable {G : Specs.AffineAlgebraicGroup k} {S : Subgroup (GeometricPoints G.val.X)}
variable {I : Type u} [Preorder I] [IsDirectedOrder I]

/-- Once the image is realized by a smooth connected subgroup, one directed
enlargement suffices to lift a Lang preimage and correct the entire cocycle. -/
theorem correct_of_realization {H : Specs.AffineAlgebraicGroup k} {m : H.val ⟶ G.val}
    (hH : Realizes G S H m) (D : CoefficientStages G S I)
    (i : I) (c : D.Gal i → D.Coeff i)
    (hc : ∀ σ τ, c (σ * τ) = c σ * D.act i σ (c τ)) :
    CorrectsAtLargerStage D i c := by
  let K := AlgebraicClosure k
  have : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  have : QuasiCompact H.val.X.hom := H.property.2.2
  have : Smooth H.val.X.hom := hH.2.2.1
  have : ConnectedSpace ↥(pullback H.val.X.hom (fieldSpecMap k K)) := hH.2.2.2.1
  let π := pullback.fst H.val.X.hom (fieldSpecMap k K)
  have hπ : Surjective π := inferInstanceAs
    (Surjective (pullback.fst H.val.X.hom (fieldSpecMap k K)))
  have : ConnectedSpace H.val.X.left := π.surjective.connectedSpace π.continuous
  let a := D.reduction i (c (D.generator i))
  have haS : a ∈ (S : Set _) := by
    rw [← D.image_eq]
    exact Set.mem_iUnion.mpr ⟨i, ⟨_, rfl⟩⟩
  obtain ⟨x, hx⟩ : a⁻¹ ∈ Set.range
      (fun p : GeometricPoints H.val.X => p ≫ m.hom.hom) := by
    rw [hH.2.2.2.2]
    exact S.inv_mem haS
  obtain ⟨y, hy⟩ := smoothLangSurjectivity k H.val x
  let z := y ≫ m.hom.hom
  have hz : frobeniusOnPoints _ z * z⁻¹ = a⁻¹ := by
    change frobeniusOnPoints _ (y ≫ m.hom.hom) * (y ≫ m.hom.hom)⁻¹ = a⁻¹
    have hF : frobeniusOnPoints _ (y ≫ m.hom.hom) =
        frobeniusOnPoints _ y ≫ m.hom.hom := Category.assoc _ _ _ |>.symm
    have : IsMonHom m.hom.hom := m.hom.isMonHom_hom
    rw [hF, ← GrpObj.inv_comp, ← MonObj.mul_comp]
    exact (congrArg (· ≫ m.hom.hom) hy).trans hx
  have hzS : z ∈ (S : Set _) := by
    rw [← hH.2.2.2.2]
    exact ⟨y, rfl⟩
  rw [← D.image_eq] at hzS
  obtain ⟨l, v, hv⟩ := Set.mem_iUnion.mp hzS
  obtain ⟨j, hij, hlj⟩ := exists_ge_ge i l
  let b := D.extend hlj v
  have hb : D.reduction j b = z := (D.reduction_extend hlj v).trans hv
  let d : D.Gal j → D.Coeff j := fun σ => D.extend hij (c (D.restrict hij σ))
  have hd (σ τ : D.Gal j) : d (σ * τ) = d σ * D.act j σ (d τ) := by
    simp only [d, map_mul, hc, D.extend_action]
  let e : D.Gal j → D.Coeff j := fun σ => b⁻¹ * d σ * D.act j σ b
  have he (σ τ : D.Gal j) : e (σ * τ) = e σ * D.act j σ (e τ) := by
    simp only [e, hd, map_mul, MulAut.mul_apply, map_inv]
    group
  have hgen : D.reduction j (e (D.generator j)) = 1 := by
    have hf : frobeniusOnPoints _ z = a⁻¹ * z := (mul_inv_eq_iff_eq_mul).mp hz
    simp only [e, d, map_mul, map_inv, D.reduction_generator, hb, D.reduction_extend,
      D.restrict_generator]
    change z⁻¹ * a * frobeniusOnPoints _ z = 1
    rw [hf]
    group
  have he1 : e 1 = 1 := by
    have h := he 1 1
    rw [one_mul, map_one, MulAut.one_apply] at h
    exact (mul_left_cancel ((mul_one (e 1)).trans h)).symm
  have hpow (n : ℕ) : D.reduction j (e (D.generator j ^ n)) = 1 := by
    induction n with
    | zero => rw [pow_zero, he1, map_one]
    | succ n hn =>
      rw [pow_succ', he, map_mul, hgen, D.reduction_generator, hn, one_mul]
      exact MonObj.comp_one _
  let : Finite (D.Gal j) := D.galFinite j
  refine ⟨j, hij, b, fun σ => ?_⟩
  have hm : σ ∈ Subgroup.zpowers (D.generator j) := by rw [D.cyclic]; exact Subgroup.mem_top σ
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hm
  exact hpow n

/-- The first residue correction for a finite parameterized reduction image. -/
theorem residueLangCorrection : ResidueLangCorrection.{u} := by
  intro k _ _ G S P Q I _ _ D i c hc
  obtain ⟨H, m, hm⟩ := closedResidueImage k G S P Q
  exact correct_of_realization hm D i c hc

end Correction

end

end LinearAlgebraicGroups.RamifiedExceptionalResidueCorrection
