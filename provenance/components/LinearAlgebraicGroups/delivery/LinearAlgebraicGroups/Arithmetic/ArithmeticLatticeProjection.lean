import Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.LinearAlgebra.Countable
import Batteries.Tactic.OpenPrivate

open Set Topology TopologicalSpace Filter MeasureTheory
open scoped Pointwise RestrictedProduct ENNReal NNReal Polynomial RatFunc

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

open AdelicGroups
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private subgroup_closedDiscrete_of_isolating_identity from
  LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals

section Topology

variable {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]

private def cosetMap (f : A →* B) {L : Subgroup A} {M : Subgroup B}
    (h : L ≤ M.comap f) : A ⧸ L → B ⧸ M :=
  Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply]
    rw [← map_inv, ← map_mul]
    exact h (QuotientGroup.leftRel_apply.mp hab))

private theorem continuous_cosetMap (f : A →* B) {L : Subgroup A} {M : Subgroup B}
    (h : L ≤ M.comap f) (hf : Continuous f) : Continuous (cosetMap f h) :=
  (QuotientGroup.isQuotientMap_mk L).continuous_iff.mpr (QuotientGroup.continuous_mk.comp hf)

private theorem surjective_cosetMap (f : A →* B) {L : Subgroup A} {M : Subgroup B}
    (h : L ≤ M.comap f) (hf : Function.Surjective f) : Function.Surjective (cosetMap f h) := by
  intro b
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨QuotientGroup.mk a, rfl⟩

private theorem image_openSubgroup_closed (L H : Subgroup A) (hH : IsOpen (H : Set A)) :
    IsClosed ((QuotientGroup.mk : A → A ⧸ L) '' (H : Set A)) := by
  let q : A → A ⧸ L := QuotientGroup.mk
  apply (QuotientGroup.isQuotientMap_mk L).isClosed_preimage.mp
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  let V := (· * a) '' (H : Set A)
  have hV : IsOpen V := isOpenMap_mul_right a _ hH
  have haV : a ∈ V := ⟨1, H.one_mem, one_mul a⟩
  refine mem_of_superset (hV.mem_nhds haV) ?_
  rintro _ ⟨b, hb, rfl⟩ ⟨c, hc, he⟩
  apply ha
  refine ⟨b⁻¹ * c, H.mul_mem (H.inv_mem hb) hc, QuotientGroup.eq.mpr ?_⟩
  have he' := QuotientGroup.eq.mp he
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using he'

/-- An open subgroup has compact representatives for its orbit in a compact coset space. -/
private theorem compact_orbit_representatives (L H : Subgroup A)
    [CompactSpace (A ⧸ L)] {K : Set A} (hK : IsCompact K) (h1 : (1 : A) ∈ interior K)
    (hKH : K ⊆ H) (hH : IsOpen (H : Set A)) :
    ∃ C : Set A, IsCompact C ∧ C ⊆ H ∧
      (QuotientGroup.mk : A → A ⧸ L) '' C = QuotientGroup.mk '' (H : Set A) := by
  classical
  let q : A → A ⧸ L := QuotientGroup.mk
  let V (a : H) := q '' ((a.val * ·) '' interior K)
  have hv (a : H) : IsOpen (V a) :=
    QuotientGroup.isOpenMap_coe _ (isOpenMap_mul_left a.val _ isOpen_interior)
  have hcover : q '' (H : Set A) ⊆ ⋃ a, V a := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, a, ⟨1, h1, mul_one a⟩, rfl⟩
  obtain ⟨s, hs⟩ := (image_openSubgroup_closed L H hH).isCompact.elim_finite_subcover V hv hcover
  let C := ⋃ a ∈ s, (a.val * ·) '' K
  have hC : C ⊆ H := by
    rintro a ha
    obtain ⟨b, hb⟩ := mem_iUnion.mp ha
    obtain ⟨_, c, hc, rfl⟩ := mem_iUnion.mp hb
    exact H.mul_mem b.property (hKH hc)
  refine ⟨C, s.finite_toSet.isCompact_biUnion (fun a _ =>
    hK.image (continuous_const_mul a.val)), hC, subset_antisymm (image_mono hC) ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hs ha)
  obtain ⟨hbs, _, ⟨c, hc, rfl⟩, rfl⟩ := mem_iUnion.mp hb
  exact ⟨b.val * c, mem_iUnion.mpr ⟨b, mem_iUnion.mpr
    ⟨hbs, c, interior_subset hc, rfl⟩⟩, rfl⟩

private theorem compact_of_representatives (L : Subgroup A) {C : Set A}
    (hc : IsCompact C) (h : C * (L : Set A) = univ) : CompactSpace (A ⧸ L) := by
  constructor
  convert hc.image (QuotientGroup.continuous_mk (N := L)) using 1
  refine eq_univ_of_forall ?_ |>.symm
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : x ∈ C * (L : Set A) := h.symm ▸ mem_univ x
  obtain ⟨c, hc, l, hl, rfl⟩ := hx
  exact ⟨c, hc, (QuotientGroup.mk_mul_of_mem c hl).symm⟩

private theorem finite_inter_closed_discrete [T2Space A] {L C : Set A}
    (hc : IsCompact C) (hl : IsClosed L) (hd : IsDiscrete L) : (C ∩ L).Finite :=
  (hc.inter_right hl).finite (hd.mono inter_subset_right)

end Topology

section Adeles

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
  (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)

private instance (w : D.Place) : T2Space (LocalPoints D i w) :=
  (usualLocalTopology D i w).t2Space

private instance (w : D.Place) : LocallyCompactSpace (D.Completion w) := by
  cases w with
  | inl w =>
    change LocallyCompactSpace (D.FiniteCompletion w)
    infer_instance
  | inr w =>
    cases D with
    | number h => exact inferInstanceAs (LocallyCompactSpace w.Completion)
    | function F t => exact w.elim

private instance (w : D.Place) : LocallyCompactSpace (LocalPoints D i w) := by
  letI : LocallyCompactSpace (Matrix (Index.{u} i.size) (Index.{u} i.size) (D.Completion w)) :=
    inferInstanceAs (LocallyCompactSpace (Index.{u} i.size → Index.{u} i.size → D.Completion w))
  letI : LocallyCompactSpace (Matrix.GeneralLinearGroup (Index.{u} i.size) (D.Completion w)) :=
    inferInstanceAs (LocallyCompactSpace (Matrix (Index.{u} i.size) (Index.{u} i.size)
      (D.Completion w))ˣ)
  exact (localMatrixEmbedding D i w).locallyCompactSpace

private theorem rational_matrix_injective : Function.Injective i.onPoints := by
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  exact (asMatrix_isClosedEmbedding i K).injective

private theorem localPoint_injective (w : D.Place) : Function.Injective (localPoint D i w) := by
  intro a b hab
  apply rational_matrix_injective i
  apply Units.ext
  ext s t
  apply (D.embedding w).injective
  have he := congrArg (fun x => (asMatrix i (D.Completion w) x).val s t) hab
  rw [localPoint_matrix, localPoint_matrix] at he
  exact he

private theorem rationalProjection_injective {T : Finset D.Place} (ht : T.Nonempty) :
    Function.Injective (rationalProjection D i T) := by
  obtain ⟨w, hw⟩ := ht
  intro a b h
  exact localPoint_injective D i w (congrFun h ⟨w, hw⟩)

private abbrev FullIndex := Outside D (∅ : Finset D.Place)

private def outsideIndex (T : Finset D.Place) (w : Outside D T) : FullIndex D :=
  ⟨w.1, by simp⟩

private theorem outsideIndex_injective (T : Finset D.Place) :
    Function.Injective (outsideIndex D T) :=
  fun _ _ h => Subtype.ext (congrArg (fun w : FullIndex D => w.val) h)

private def outsideProjection (T : Finset D.Place) :
    Adeles D i ∅ →* Adeles D i T :=
  RestrictedProduct.mapAlongMonoidHom _ _ (outsideIndex D T)
    (outsideIndex_injective D T).tendsto_cofinite (fun _ => MonoidHom.id _) (Eventually.of_forall
      fun _ _ hx => hx)

private theorem outsideProjection_continuous (T : Finset D.Place) :
    Continuous (outsideProjection D i T) :=
  RestrictedProduct.mapAlong_continuous _ _ (outsideIndex D T)
    ((outsideIndex_injective D T).tendsto_cofinite) (fun _ => id)
    (Eventually.of_forall fun _ _ hx => hx) (fun _ => continuous_id)

private def insideProjection (T : Finset D.Place) :
    Adeles D i ∅ →* FinitePoints D i T where
  toFun x w := x ⟨w.1, by simp⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem insideProjection_continuous (T : Finset D.Place) :
    Continuous (insideProjection D i T) := by
  change Continuous (fun x : Adeles D i ∅ => fun w : (↑T : Set D.Place) => x ⟨w.1, by simp⟩)
  exact continuous_pi fun w => RestrictedProduct.continuous_eval
    (R := fun w : FullIndex D => LocalPoints D i w.1)
    (A := fun w => (localSubgroup D i w.1 : Set _)) ⟨w.1, by simp⟩

private def combine (T : Finset D.Place) (a : FinitePoints D i T) (b : Adeles D i T)
    (w : FullIndex D) : LocalPoints D i w.1 := by
  classical
  exact if h : w.1 ∈ T then a ⟨w.1, h⟩ else b ⟨w.1, h⟩

private theorem combine_outside (T : Finset D.Place) (a : FinitePoints D i T)
    (b : Adeles D i T) (w : Outside D T) :
    combine D i T a b (outsideIndex D T w) = b w := by
  unfold combine
  rw [dite_eq_right (show (outsideIndex D T w).val ∉ T from w.property)]
  rfl

private abbrev outsideSet (T : Finset D.Place) (W : Set (Outside D T)) : Set (FullIndex D) :=
  (outsideIndex D T) '' W

private theorem outsideSet_cofinite (T : Finset D.Place) {W : Set (Outside D T)}
    (hW : cofinite ≤ 𝓟 W) : cofinite ≤ 𝓟 (outsideSet D T W) := by
  rw [le_principal_iff, mem_cofinite] at hW ⊢
  refine ((T.finite_toSet.preimage (f := Subtype.val) Subtype.val_injective.injOn).union
    (hW.image (outsideIndex D T))).subset ?_
  intro w hw
  by_cases h : w.1 ∈ T
  · exact Or.inl h
  · exact Or.inr ⟨⟨w.1, h⟩, fun hg => hw ⟨⟨w.1, h⟩, hg, Subtype.ext rfl⟩, Subtype.ext rfl⟩

private def joinAdeles (T : Finset D.Place) :
    FinitePoints D i T × Adeles D i T → Adeles D i ∅ := fun x =>
  ⟨combine D i T x.1 x.2, by
    have hW : {w : Outside D T | x.2 w ∈ localSubgroup D i w.1} ∈
        (cofinite : Filter (Outside D T)) := x.2.eventually
    have h : ∀ᶠ w in (cofinite : Filter (FullIndex D)),
        w ∈ outsideSet D T {w : Outside D T | x.2 w ∈ localSubgroup D i w.1} :=
      le_principal_iff.mp
      (outsideSet_cofinite D T (le_principal_iff.mpr hW))
    exact h.mono (by
      rintro _ ⟨w, hw, rfl⟩
      rw [combine_outside]
      exact hw)⟩

private theorem joinAdeles_continuous (T : Finset D.Place) : Continuous (joinAdeles D i T) := by
  classical
  let R (w : FullIndex D) := LocalPoints D i w.1
  let E (w : FullIndex D) : Set (R w) := localSubgroup D i w.1
  apply (RestrictedProduct.continuous_dom_prod_left (A := fun w : Outside D T =>
    (localSubgroup D i w.1 : Set (LocalPoints D i w.1)))
    (fun w => localSubgroup_open D i w.1)).mpr
  intro W hW
  let f (x : FinitePoints D i T × Πʳ w : Outside D T,
      [LocalPoints D i w.1, localSubgroup D i w.1]_[𝓟 W]) :
      Πʳ w : FullIndex D, [R w, E w]_[𝓟 (outsideSet D T W)] :=
    ⟨combine D i T x.1 (RestrictedProduct.inclusion _ _ hW x.2),
      mem_principal.mpr (by
        rintro _ ⟨w, hw, rfl⟩
        change combine D i T x.1 (RestrictedProduct.inclusion _ _ hW x.2)
          (outsideIndex D T w) ∈ localSubgroup D i w.1
        rw [combine_outside]
        exact mem_principal.mp x.2.eventually hw)⟩
  change Continuous (RestrictedProduct.inclusion R E (outsideSet_cofinite D T hW) ∘ f)
  apply (RestrictedProduct.continuous_inclusion _).comp
  apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
  intro w
  let R' (k : Outside D T) := LocalPoints D i k.1
  let A' (k : Outside D T) : Set (R' k) := localSubgroup D i k.1
  let Y := FinitePoints D i T × Πʳ k : Outside D T, [R' k, A' k]_[𝓟 W]
  change Continuous (fun x : Y => f x w)
  by_cases h : w.1 ∈ T
  · have he (x : Y) : f x w = x.1 ⟨w.1, h⟩ := by
      change combine D i T x.1 _ w = _
      rw [combine, dite_eq_left h]
    simp only [he]
    exact (@continuous_apply _ (fun k : (↑T : Set D.Place) => LocalPoints D i k.1)
      _ ⟨w.1, h⟩).comp continuous_fst
  · have he (x : Y) : f x w = x.2 ⟨w.1, h⟩ := by
      change combine D i T x.1 _ w = _
      rw [combine, dite_eq_right h]
      rfl
    simp only [he]
    exact (RestrictedProduct.continuous_eval (R := R') (A := A') (𝓕 := 𝓟 W)
      ⟨w.1, h⟩).comp continuous_snd

private def splitAdeles (T : Finset D.Place) :
    Adeles D i ∅ ≃ₜ* (FinitePoints D i T × Adeles D i T) where
  toFun x := (insideProjection D i T x, outsideProjection D i T x)
  invFun := joinAdeles D i T
  left_inv x := RestrictedProduct.ext _ _ fun w => by
    by_cases h : w.1 ∈ T <;>
      simp [joinAdeles, combine, h, insideProjection, outsideProjection, outsideIndex,
        RestrictedProduct.mapAlongMonoidHom_apply]
  right_inv x := Prod.ext
    (funext fun w => by simp [insideProjection, joinAdeles, combine])
    (RestrictedProduct.ext _ _ fun w => by
      simp [outsideProjection, outsideIndex, RestrictedProduct.mapAlongMonoidHom_apply,
        joinAdeles, combine, w.property])
  map_mul' x y := Prod.ext (map_mul (insideProjection D i T) x y)
    (map_mul (outsideProjection D i T) x y)
  continuous_toFun := (insideProjection_continuous D i T).prodMk (outsideProjection_continuous D i T)
  continuous_invFun := joinAdeles_continuous D i T

end Adeles

section ProductLattice

variable {P Q : Type*} [Group P] [Group Q] [TopologicalSpace P] [TopologicalSpace Q]
  [T2Space P] [T2Space Q] [IsTopologicalGroup P] [IsTopologicalGroup Q] [LocallyCompactSpace P]

private theorem productLattice (Γ : Subgroup (P × Q)) (U : Subgroup Q)
    [CompactSpace ((P × Q) ⧸ Γ)] (hΓc : IsClosed (Γ : Set (P × Q)))
    (hΓd : IsDiscrete (Γ : Set (P × Q))) (hUc : IsCompact (U : Set Q))
    (hUo : IsOpen (U : Set Q)) :
    let L := (Γ ⊓ (⊤ : Subgroup P).prod U).map (MonoidHom.fst P Q)
    IsClosed (L : Set P) ∧ IsDiscrete (L : Set P) ∧
      ∃ C : Set P, IsCompact C ∧ C * (L : Set P) = univ := by
  classical
  let H := (⊤ : Subgroup P).prod U
  let L := (Γ ⊓ H).map (MonoidHom.fst P Q)
  change IsClosed (L : Set P) ∧ IsDiscrete (L : Set P) ∧
    ∃ C : Set P, IsCompact C ∧ C * (L : Set P) = univ
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : P)
  have hH : IsOpen (H : Set (P × Q)) := by
    simpa [H, Subgroup.coe_prod] using isOpen_univ.prod hUo
  have hbox : IsCompact (K ×ˢ (U : Set Q)) := hKc.prod hUc
  have h1 : (1 : P × Q) ∈ interior (K ×ˢ (U : Set Q)) :=
    mem_interior_iff_mem_nhds.mpr (prod_mem_nhds hKn (hUo.mem_nhds U.one_mem))
  obtain ⟨C, hCc, hCH, hCq⟩ := compact_orbit_representatives Γ H hbox h1
    (fun z hz => ⟨Subgroup.mem_top _, hz.2⟩) hH
  have hKfinite : (K ∩ (L : Set P)).Finite := by
    apply ((finite_inter_closed_discrete hbox hΓc hΓd).image Prod.fst).subset
    rintro x ⟨hx, z, ⟨hzΓ, hzH⟩, rfl⟩
    exact ⟨z, ⟨⟨hx, hzH.2⟩, hzΓ⟩, rfl⟩
  have hF : IsClosed ((K ∩ (L : Set P)) \ {1}) :=
    (hKfinite.subset sdiff_subset).isClosed
  have hi : (1 : P) ∈ interior K \ ((K ∩ (L : Set P)) \ {1}) :=
    ⟨mem_interior_iff_mem_nhds.mpr hKn, by simp⟩
  obtain ⟨hc, hd⟩ := subgroup_closedDiscrete_of_isolating_identity L _
    (isOpen_interior.sdiff hF) hi (fun x hx hxO => by
      by_contra h
      exact hxO.2 ⟨⟨interior_subset hxO.1, hx⟩, h⟩)
  refine ⟨hc, hd, Prod.fst '' C, hCc.image continuous_fst, eq_univ_of_forall ?_⟩
  intro p
  let z : P × Q := (p, 1)
  have hz : QuotientGroup.mk z ∈ (QuotientGroup.mk : P × Q → (P × Q) ⧸ Γ) '' C :=
    hCq.symm ▸ mem_image_of_mem _ (show z ∈ H from ⟨Subgroup.mem_top _, U.one_mem⟩)
  obtain ⟨c, hc, heq⟩ := hz
  have hγ : c⁻¹ * z ∈ Γ := QuotientGroup.eq.mp heq
  exact ⟨c.1, ⟨c, hc, rfl⟩, (c⁻¹ * z).1,
    ⟨c⁻¹ * z, ⟨hγ, H.mul_mem (H.inv_mem (hCH hc)) ⟨Subgroup.mem_top _, U.one_mem⟩⟩, rfl⟩,
    mul_inv_cancel_left _ _⟩

end ProductLattice

section ArithmeticTopology

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
  (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)

private theorem arithmeticSubgroup_mem_iff {T : Finset D.Place} {U : Subgroup (Adeles D i T)}
    {g : RationalPoints G} :
    g ∈ arithmeticSubgroup D i T U ↔ AdelicGroups.diagonal D i T g ∈ U := by
  constructor
  · rintro ⟨x, hx, h⟩
    have he : x = AdelicGroups.diagonal D i T g := RestrictedProduct.ext _ _ h
    exact he ▸ hx
  · intro h
    exact ⟨_, h, fun _ => rfl⟩

private theorem lattice_topology (T : Finset D.Place) (U : Subgroup (Adeles D i T))
    [CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)]
    (hUc : IsCompact (U : Set (Adeles D i T))) (hUo : IsOpen (U : Set (Adeles D i T))) :
    let L := lattice D i T U
    IsClosed (L : Set (FinitePoints D i T)) ∧ IsDiscrete (L : Set (FinitePoints D i T)) ∧
      ∃ C : Set (FinitePoints D i T),
        IsCompact C ∧ C * (L : Set (FinitePoints D i T)) = univ := by
  let e := splitAdeles D i T
  let Γ := (diagonalSubgroup D i).map e.toMonoidHom
  have hΓeq : (Γ : Set (FinitePoints D i T × Adeles D i T)) =
      e '' (diagonalSubgroup D i : Set (Adeles D i ∅)) := rfl
  obtain ⟨hc, hd⟩ := DiscreteDiagonals.groupClosedDiscrete D i
  have hΓc : IsClosed (Γ : Set (FinitePoints D i T × Adeles D i T)) :=
    hΓeq ▸ e.toHomeomorph.isClosedMap _ hc
  have hΓd : IsDiscrete (Γ : Set (FinitePoints D i T × Adeles D i T)) :=
    hΓeq ▸ hd.image e.toHomeomorph.isInducing
  have hle : diagonalSubgroup D i ≤ Γ.comap e.toMonoidHom := fun a ha => ⟨a, ha, rfl⟩
  letI : CompactSpace ((FinitePoints D i T × Adeles D i T) ⧸ Γ) :=
    ⟨(Function.Surjective.range_eq (surjective_cosetMap e.toMonoidHom hle e.surjective)) ▸
      isCompact_range (continuous_cosetMap e.toMonoidHom hle e.continuous)⟩
  have he (g : RationalPoints G) :
      e (AdelicGroups.diagonal D i ∅ g) =
        (rationalProjection D i T g, AdelicGroups.diagonal D i T g) := rfl
  have hL : (Γ ⊓ (⊤ : Subgroup (FinitePoints D i T)).prod U).map
      (MonoidHom.fst (FinitePoints D i T) (Adeles D i T)) = lattice D i T U := by
    ext a
    constructor
    · rintro ⟨_, ⟨⟨x, ⟨g, hg⟩, rfl⟩, hu⟩, rfl⟩
      have hx : x = AdelicGroups.diagonal D i ∅ g := RestrictedProduct.ext _ _ hg
      subst x
      have hu' : AdelicGroups.diagonal D i T g ∈ U := hu.2
      exact ⟨g, (arithmeticSubgroup_mem_iff D i).mpr hu', rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨e (AdelicGroups.diagonal D i ∅ g), ⟨⟨_, ⟨g, fun _ => rfl⟩, rfl⟩, ?_⟩,
        congrArg Prod.fst (he g)⟩
      exact ⟨Subgroup.mem_top _, (arithmeticSubgroup_mem_iff D i).mp hg⟩
  simpa only [hL] using productLattice Γ U hΓc hΓd hUc hUo

private def extendByOne {J T : Finset D.Place} (_h : J ⊆ T)
    (x : FinitePoints D i J) (w : (↑T : Set D.Place)) : LocalPoints D i w.1 := by
  classical
  exact if hw : w.1 ∈ J then x ⟨w.1, hw⟩ else 1

private theorem forgetPlaces_surjective {J T : Finset D.Place} (h : J ⊆ T) :
    Function.Surjective (forgetPlaces D i h) := by
  intro x
  exact ⟨extendByOne D i h x, funext fun w => by simp [forgetPlaces, extendByOne]⟩

private theorem forgetPlaces_continuous {J T : Finset D.Place} (h : J ⊆ T) :
    Continuous (forgetPlaces D i h) := by
  change Continuous (fun x : FinitePoints D i T => fun w : (↑J : Set D.Place) => x ⟨w.val, h w.property⟩)
  exact continuous_pi fun w =>
    @continuous_apply _ (fun a : (↑T : Set D.Place) => LocalPoints D i a.1) _
      ⟨w.val, h w.property⟩

private theorem lattice_projection_injective {J T : Finset D.Place} (hJ : J ⊆ T) (hj : J.Nonempty)
    (U : Subgroup (Adeles D i T)) :
    Set.InjOn (forgetPlaces D i hJ) (lattice D i T U : Set (FinitePoints D i T)) := by
  intro a ha b hb he
  obtain ⟨g, _, rfl⟩ := ha
  obtain ⟨h, _, rfl⟩ := hb
  exact congrArg (rationalProjection D i T) (rationalProjection_injective D i hj he)

private theorem projection_nondiscrete {S T J : Finset D.Place} (hS : S ⊆ T) (hJ : J ⊆ T)
    (hd : Disjoint J S) (hj : J.Nonempty) (U : Subgroup (Adeles D i T))
    (hSnon : ¬ CompactSpace (FinitePoints D i S))
    {C : Set (FinitePoints D i T)} (hCc : IsCompact C)
    (hC : C * (lattice D i T U : Set (FinitePoints D i T)) = univ) :
    ¬ IsDiscrete (((lattice D i T U).map (forgetPlaces D i hJ)) : Set (FinitePoints D i J)) := by
  classical
  let L := lattice D i T U
  let f := forgetPlaces D i hJ
  let M := L.map f
  intro hMd
  have hMc := M.isClosed_of_isDiscrete hMd
  let B := (f '' C)⁻¹ ∩ (M : Set (FinitePoints D i J))
  have hB : B.Finite :=
    finite_inter_closed_discrete (hCc.image (forgetPlaces_continuous D i hJ)).inv hMc hMd
  let A := (L : Set (FinitePoints D i T)) ∩ f ⁻¹' B
  have hA : A.Finite := Set.Finite.of_injOn (f := f) (fun _ hx => hx.2)
    ((lattice_projection_injective D i hJ hj U).mono inter_subset_left) hB
  have heq : forgetPlaces D i hS '' (C * A) = univ := eq_univ_of_forall fun x => by
    let y := extendByOne D i hS x
    have hy : y ∈ C * (L : Set (FinitePoints D i T)) := hC.symm ▸ mem_univ y
    obtain ⟨c, hc, l, hl, hcl⟩ := hy
    have hyJ : f y = 1 := by
      funext w
      have hn : w.val ∉ S := fun hw => Finset.disjoint_left.mp hd w.property hw
      simp [f, y, forgetPlaces, extendByOne, hn]
    have hfl : f l = (f c)⁻¹ := by
      have h := (map_mul f c l).symm.trans ((congrArg f hcl).trans hyJ)
      exact eq_inv_of_mul_eq_one_right h
    have hyS : forgetPlaces D i hS y = x := funext fun w => by
      simp [y, forgetPlaces, extendByOne]
    exact ⟨y, ⟨c, hc, l, ⟨hl, ⟨show f l ∈ (f '' C)⁻¹ from
      by rw [hfl]; exact inv_mem_inv.mpr (mem_image_of_mem f hc), ⟨l, hl, rfl⟩⟩⟩, hcl⟩, hyS⟩
  apply hSnon
  exact ⟨heq ▸ (hCc.mul hA.isCompact).image (forgetPlaces_continuous D i hS)⟩

end ArithmeticTopology

section QuotientMeasure

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [LocallyCompactSpace A]

/-- A compact quotient by a discrete group has a measurable transversal in a compact set. -/
private theorem compact_borel_transversal (L : Subgroup A) (hd : IsDiscrete (L : Set A))
    [CompactSpace (A ⧸ L)] :
    letI : MeasurableSpace A := borel A
    ∃ F K : Set A, MeasurableSet F ∧ IsCompact K ∧ F ⊆ K ∧
      (∀ q : A ⧸ L, ∃! a : A, a ∈ F ∧ QuotientGroup.mk a = q) := by
  classical
  borelize A
  let q : A → A ⧸ L := QuotientGroup.mk
  haveI : DiscreteTopology L := isDiscrete_iff_discreteTopology.mp hd
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set L))
  have h1 : (1 : A) ∈ W := by
    change (1 : L) ∈ Subtype.val ⁻¹' W
    rw [hW]
    exact mem_singleton 1
  obtain ⟨V, hVn, hV⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : A)
  let O := interior (V⁻¹ ∩ K)
  have hO1 : (1 : A) ∈ O := mem_interior_iff_mem_nhds.mpr
    (inter_mem (continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hVn)) hKn)
  have hOinj : Set.InjOn q O := by
    intro a ha b hb he
    have h := QuotientGroup.eq.mp he
    have hin : a⁻¹ * b ∈ W := by
      simpa [div_eq_mul_inv] using hV a⁻¹ (interior_subset ha).1 b⁻¹ (interior_subset hb).1
    have hs : (⟨a⁻¹ * b, h⟩ : L) ∈ ({1} : Set L) := hW ▸ hin
    exact inv_mul_eq_one.mp (congrArg Subtype.val (mem_singleton_iff.mp hs))
  let Oa (a : A) := (a * ·) '' O
  have ho (a : A) : IsOpen (Oa a) := isOpenMap_mul_left a _ isOpen_interior
  have hqin (a : A) : Set.InjOn q (Oa a) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have h : x⁻¹ * y ∈ L := by
      simpa [mul_assoc] using QuotientGroup.eq.mp hxy
    exact congrArg (a * ·) (hOinj hx hy (QuotientGroup.eq.mpr h))
  have hcover : (univ : Set (A ⧸ L)) ⊆ ⋃ a, q '' Oa a := by
    rintro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact mem_iUnion.mpr ⟨a, a, ⟨1, hO1, mul_one a⟩, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a => q '' Oa a)
    (fun a => QuotientGroup.isOpenMap_coe _ (ho a)) hcover
  let e : Fin s.card ≃ (↑s : Set A) := s.equivFin.symm
  let B (n : Fin s.card) := Oa (e n).val
  let C (n : Fin s.card) := q '' B n
  let F := ⋃ n, B n ∩ q ⁻¹' disjointed C n
  let K' := ⋃ a ∈ s, (a * ·) '' K
  have hmeas (n : Fin s.card) : IsOpen (C n) := QuotientGroup.isOpenMap_coe _ (ho _)
  letI : MeasurableSpace (A ⧸ L) := borel (A ⧸ L)
  letI : BorelSpace (A ⧸ L) := ⟨rfl⟩
  have hq : Measurable q := QuotientGroup.continuous_mk.measurable
  refine ⟨F, K', MeasurableSet.iUnion (fun n => (ho _).measurableSet.inter
    (hq (by
      rw [disjointed_eq_inter_compl]
      exact (hmeas n).measurableSet.inter
        (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hmeas j).measurableSet.compl)))),
    s.finite_toSet.isCompact_biUnion (fun a _ => hK.image (continuous_const_mul a)), ?_, ?_⟩
  · intro x hx
    obtain ⟨n, ⟨y, hy, rfl⟩, _⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨(e n).property, y, (interior_subset hy).2, rfl⟩⟩
  · intro z
    have hz : z ∈ ⋃ n, C n := by
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hs (mem_univ z))
      obtain ⟨has, haz⟩ := mem_iUnion.mp ha
      refine mem_iUnion.mpr ⟨e.symm ⟨a, has⟩, ?_⟩
      change z ∈ q '' Oa (e (e.symm ⟨a, has⟩)).val
      rw [e.apply_symm_apply]
      exact haz
    rw [← iUnion_disjointed] at hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    obtain ⟨a, ha, haq⟩ := disjointed_subset C n hn
    refine ⟨a, ⟨mem_iUnion.mpr ⟨n, ha, show q a ∈ disjointed C n by rw [haq]; exact hn⟩, haq⟩, ?_⟩
    rintro b ⟨hb, hbq⟩
    obtain ⟨m, hmB, hm⟩ := mem_iUnion.mp hb
    have he : m = n := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_disjointed C hne) (show z ∈ disjointed C m by rw [← hbq]; exact hm) hn
    subst m
    exact hqin _ hmB ha (hbq.trans haq.symm)

private theorem transversal_fundamental (L : Subgroup A) [MeasurableSpace A]
    {μ : Measure A} {F : Set A} (hF : MeasurableSet F)
    (h : ∀ q : A ⧸ L, ∃! a : A, a ∈ F ∧ QuotientGroup.mk a = q) :
    IsFundamentalDomain L.op F μ := by
  apply IsFundamentalDomain.mk' hF.nullMeasurableSet
  intro a
  obtain ⟨b, ⟨hb, hbq⟩, hu⟩ := h (QuotientGroup.mk a)
  have hab : a⁻¹ * b ∈ L := QuotientGroup.eq.mp hbq.symm
  refine ⟨⟨MulOpposite.op (a⁻¹ * b), hab⟩, ?_, ?_⟩
  · change a * (a⁻¹ * b) ∈ F
    simpa using hb
  · intro c hc
    have hcq : (QuotientGroup.mk (c • a) : A ⧸ L) = QuotientGroup.mk a :=
      QuotientGroup.mk_mul_of_mem a c.property
    have he := hu (c • a) ⟨hc, hcq⟩
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change c.val.unop = a⁻¹ * b
    exact eq_inv_mul_of_mul_eq he

private theorem translated_transversal (L : Subgroup A) {F : Set A}
    (h : ∀ q : A ⧸ L, ∃! a : A, a ∈ F ∧ QuotientGroup.mk a = q) (g : A) :
    ∀ q : A ⧸ L, ∃! a : A, a ∈ (g * ·) '' F ∧ QuotientGroup.mk a = q := by
  intro q
  obtain ⟨b, ⟨hb, hbq⟩, he⟩ := h (g⁻¹ • q)
  refine ⟨g * b, ⟨⟨b, hb, rfl⟩, ?_⟩, ?_⟩
  · change g • (QuotientGroup.mk b : A ⧸ L) = q
    rw [hbq, smul_inv_smul]
  · rintro _ ⟨⟨c, hc, rfl⟩, hcq⟩
    have hqc : (QuotientGroup.mk c : A ⧸ L) = g⁻¹ • q := by
      change g • (QuotientGroup.mk c : A ⧸ L) = q at hcq
      rw [← hcq, inv_smul_smul]
    rw [he c ⟨hc, hqc⟩]

private theorem cocompact_discrete_measure (L : Subgroup A) [Countable L]
    [CompactSpace (A ⧸ L)] (hd : IsDiscrete (L : Set A)) :
    Unimodular A ∧ FiniteInvariantQuotientMeasure L := by
  classical
  unfold Unimodular FiniteInvariantQuotientMeasure
  borelize A (A ⧸ L)
  obtain ⟨F, K, hF, hK, hFK, htrans⟩ := compact_borel_transversal L hd
  obtain ⟨K₀⟩ := PositiveCompacts.nonempty' (α := A)
  let μ := Measure.haarMeasure K₀
  let ν := μ.inv
  haveI : μ.IsHaarMeasure := inferInstance
  haveI : μ.Regular := inferInstance
  have hscale (g : A) : Measure.map (· * g) μ = Measure.modularCharacterFun g • μ := by
    haveI : (Measure.map (· * g) μ).Regular := Measure.Regular.map (Homeomorph.mulRight g)
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
    exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _
  haveI : ν.IsMulRightInvariant := inferInstanceAs (μ.inv.IsMulRightInvariant)
  haveI : ν.IsOpenPosMeasure := inferInstanceAs (μ.inv.IsOpenPosMeasure)
  haveI : IsFiniteMeasureOnCompacts ν := inferInstanceAs (IsFiniteMeasureOnCompacts μ.inv)
  haveI : SMulInvariantMeasure L.op A ν := inferInstance
  have hfund := transversal_fundamental L (μ := ν) hF htrans
  have hF0 : ν F ≠ 0 := hfund.measure_ne_zero (by
    have hp : 0 < ν univ := isOpen_univ.measure_pos _ univ_nonempty
    exact fun h => hp.ne' (by simp [h]))
  have hFtop : ν F ≠ ⊤ := (lt_of_le_of_lt (measure_mono hFK) hK.measure_lt_top).ne
  have htranslate (g : A) : IsFundamentalDomain L.op ((g * ·) '' F) ν :=
    transversal_fundamental L ((Homeomorph.mulLeft g).measurableEmbedding.measurableSet_image.mpr hF)
      (translated_transversal L htrans g)
  have hΔ (g : A) : Measure.modularCharacterFun g = 1 := by
    have h := congrArg (fun m : Measure A => m F⁻¹)
      (hscale g)
    have hpre : (· * g) ⁻¹' F⁻¹ = (((g * ·) '' F) : Set A)⁻¹ := by
      ext a
      change (a * g)⁻¹ ∈ F ↔ a⁻¹ ∈ (g * ·) '' F
      rw [mul_inv_rev]
      exact ⟨fun ha => ⟨_, ha, mul_inv_cancel_left _ _⟩, by
        rintro ⟨b, hb, he⟩
        rw [← he, inv_mul_cancel_left]
        exact hb⟩
    rw [Measure.map_apply (measurable_mul_const g) hF.inv, hpre, ← Measure.inv_apply,
      (htranslate g).measure_eq hfund, Measure.smul_apply, ← Measure.inv_apply] at h
    have he : (1 : ℝ≥0∞) * ν F = (Measure.modularCharacterFun g : ℝ≥0∞) * ν F := by
      simpa only [one_mul, Measure.nnreal_smul_coe_apply] using h
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_left_inj hF0 hFtop).mp he).symm
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [hscale g, hΔ, one_smul]⟩
  haveI : ν.IsMulLeftInvariant := inferInstanceAs (μ.inv.IsMulLeftInvariant)
  refine ⟨⟨μ, inferInstance, inferInstance⟩, ?_⟩
  let q : A → A ⧸ L := QuotientGroup.mk
  have hq : Measurable q := QuotientGroup.continuous_mk.measurable
  let m := Measure.map q (ν.restrict F)
  have hm {B : Set (A ⧸ L)} (hB : MeasurableSet B) : m B = ν (q ⁻¹' B ∩ F) := by
    rw [Measure.map_apply hq hB, Measure.restrict_apply (hq hB)]
  have hinv (B : Set (A ⧸ L)) (l : L.op) :
      (fun x : A => l • x) ⁻¹' (q ⁻¹' B) = q ⁻¹' B := by
    ext a
    change (QuotientGroup.mk (a * l.val.unop) : A ⧸ L) ∈ B ↔ QuotientGroup.mk a ∈ B
    rw [QuotientGroup.mk_mul_of_mem a l.property]
  refine ⟨m, ⟨by simpa [hm MeasurableSet.univ] using lt_top_iff_ne_top.mpr hFtop⟩,
    ⟨fun B hB hne h0 => ?_⟩, ⟨fun g B hB => ?_⟩⟩
  · rw [hm hB.measurableSet] at h0
    have hzero := hfund.measure_zero_of_invariant (q ⁻¹' B) (fun l => by
      rw [← preimage_smul_inv]
      exact hinv B l⁻¹) h0
    exact ((hB.preimage QuotientGroup.continuous_mk).measure_pos ν
      (hne.preimage' (by rw [QuotientGroup.mk_surjective.range_eq]; exact subset_univ _))).ne' hzero
  · rw [hm ((measurable_const_smul g) hB), hm hB]
    have hpre : q ⁻¹' ((g • ·) ⁻¹' B) ∩ F =
        (g * ·) ⁻¹' (q ⁻¹' B ∩ (g * ·) '' F) := by
      ext a
      exact and_congr Iff.rfl (by simp)
    rw [hpre, measure_preimage_mul]
    exact (htranslate g).measure_set_eq hfund (hq hB) (hinv B)

end QuotientMeasure

section MeasureTransport

variable {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]

private theorem quotientMeasure_pushforward (L : Subgroup A) (M : Subgroup B)
    (f : A →* B) (h : L ≤ M.comap f) (hf : Continuous f) (hs : Function.Surjective f)
    (hμ : FiniteInvariantQuotientMeasure L) : FiniteInvariantQuotientMeasure M := by
  unfold FiniteInvariantQuotientMeasure at *
  borelize (A ⧸ L) (B ⧸ M)
  obtain ⟨μ, hfin, hpos, hinv⟩ := hμ
  let q := cosetMap f h
  have hq := continuous_cosetMap f h hf
  have hqs := surjective_cosetMap f h hs
  refine ⟨μ.map q, inferInstance, hq.isOpenPosMeasure_map hqs, ⟨?_⟩⟩
  intro b V hV
  obtain ⟨a, rfl⟩ := hs b
  have hB : Measurable (f a • · : B ⧸ M → B ⧸ M) := (continuous_const_smul (f a)).measurable
  rw [Measure.map_apply hq.measurable (hB hV), Measure.map_apply hq.measurable hV]
  have hpre : q ⁻¹' ((f a • ·) ⁻¹' V) = (a • ·) ⁻¹' (q ⁻¹' V) := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    change (QuotientGroup.mk (f a * f x) : B ⧸ M) ∈ V ↔ QuotientGroup.mk (f (a * x)) ∈ V
    rw [map_mul]
  rw [hpre]
  exact measure_preimage_smul μ a _

private theorem unimodular_of_mulEquiv (e : A ≃ₜ* B) (h : Unimodular A) : Unimodular B := by
  unfold Unimodular at *
  borelize A B
  obtain ⟨μ, hl, hr⟩ := h
  refine ⟨μ.map e, inferInstance, ⟨fun b => ?_⟩⟩
  obtain ⟨a, rfl⟩ := e.surjective b
  have heMeas : Measurable (e : A → B) := e.continuous.measurable
  rw [Measure.map_map (measurable_mul_const (e a)) heMeas]
  have he : (· * e a) ∘ e = e ∘ (· * a) := funext fun x => (map_mul e x a).symm
  rw [he, ← Measure.map_map heMeas (measurable_mul_const a),
    map_mul_right_eq_self]

private theorem unimodular_of_prod [T2Space A] [T2Space B] [LocallyCompactSpace B]
    (h : Unimodular (A × B)) : Unimodular A := by
  unfold Unimodular at *
  borelize (A × B) A
  obtain ⟨μ, hl, hr⟩ := h
  obtain ⟨C, hc, hn⟩ := exists_compact_mem_nhds (1 : B)
  let ν := Measure.map Prod.fst (μ.restrict (Prod.snd ⁻¹' C))
  have hν {s : Set A} (hs : MeasurableSet s) : ν s = μ (s ×ˢ C) := by
    rw [Measure.map_apply continuous_fst.measurable hs,
      Measure.restrict_apply (continuous_fst.measurable hs)]
    rfl
  have hleft : ν.IsMulLeftInvariant := by
    rw [← forall_measure_preimage_mul_iff]
    intro a s hs
    rw [hν hs, hν (measurable_const_mul a hs)]
    have he : (fun x : A × B => (a, 1) * x) ⁻¹' (s ×ˢ C) =
        ((a * ·) ⁻¹' s) ×ˢ C := by ext x; simp
    rw [← he, measure_preimage_mul]
  have hright : ν.IsMulRightInvariant := by
    rw [← forall_measure_preimage_mul_right_iff]
    intro a s hs
    rw [hν hs, hν (measurable_mul_const a hs)]
    have he : (fun x : A × B => x * (a, 1)) ⁻¹' (s ×ˢ C) =
        ((· * a) ⁻¹' s) ×ˢ C := by ext x; simp
    rw [← he, measure_preimage_mul_right]
  refine ⟨ν, ?_, hright⟩
  refine { toIsFiniteMeasureOnCompacts := ⟨fun K hK => ?_⟩
           toIsMulLeftInvariant := hleft
           toIsOpenPosMeasure := ⟨fun O hO hne => ?_⟩ }
  · rw [hν hK.measurableSet]
    exact (hK.prod hc).measure_lt_top
  · rw [hν hO.measurableSet]
    exact (((hO.prod isOpen_interior).measure_pos μ (hne.prod
      ⟨1, mem_interior_iff_mem_nhds.mpr hn⟩)).trans_le (measure_mono
        (Set.prod_mono Subset.rfl interior_subset))).ne'

end MeasureTransport

section Results

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

private theorem globalField_countable (D : GlobalFieldData.{u, v} K) : Countable K := by
  cases D with
  | number h =>
    letI := h
    exact Finsupp.Countable.of_moduleFinite (R := ℚ)
  | function F t =>
    letI : Countable (AddMonoidAlgebra F ℕ) := AddMonoidAlgebra.coeff_injective.countable
    letI : Countable F[X] := Polynomial.toFinsupp_injective.countable
    let f (p : F[X] × F[X]) := algebraMap F[X] F⟮X⟯ p.1 / algebraMap F[X] F⟮X⟯ p.2
    letI : Countable F⟮X⟯ := (show Function.Surjective f from
      fun x => ⟨(x.num, x.denom), RatFunc.num_div_denom x⟩).countable
    letI := t.rationalAlgebra
    exact Finsupp.Countable.of_moduleFinite (R := F⟮X⟯)

private theorem lattice_countable (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (T : Finset D.Place) (U : Subgroup (Adeles D i T)) : Countable (lattice D i T U) := by
  letI := globalField_countable D
  letI : Countable (Matrix (Index.{u} i.size) (Index.{u} i.size) K) :=
    inferInstanceAs (Countable (Index.{u} i.size → Index.{u} i.size → K))
  letI : Countable (RationalPoints G) :=
    (Units.val_injective.comp (rational_matrix_injective i)).countable
  let M := arithmeticSubgroup D i T U
  let f := rationalProjection D i T
  let p (x : M) : lattice D i T U := ⟨f x, ⟨x, x.property, rfl⟩⟩
  have hp : Function.Surjective p := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact hp.countable

theorem latticeConstruction : Specs.ArithmeticLatticeProjection.latticeConstruction.{u, v} := by
  intro K _ G D i T U hA ht hUc hUo
  letI := hA
  let L := lattice D i T U
  obtain ⟨hLc, hLd, C, hC, hrep⟩ := lattice_topology D i T U hUc hUo
  letI := compact_of_representatives L hC hrep
  letI := lattice_countable D i T U
  exact ⟨(rationalProjection_injective D i ht).injOn, hLc, hLd, inferInstance,
    ⟨C, hC, hrep⟩, cocompact_discrete_measure L hLd⟩

theorem projectionProperties : Specs.ArithmeticLatticeProjection.projectionProperties.{u, v} := by
  intro K _ G D i S T J U hS hJ hA hSnon hj hd hUc hUo
  have hT : T.Nonempty := hj.mono hJ
  obtain ⟨_, _, _, hc, ⟨C, hC, hrep⟩, _, hμ⟩ :=
    latticeConstruction D i T U hA hT hUc hUo
  letI := hc
  let L := lattice D i T U
  let f := forgetPlaces D i hJ
  let H := (L.map f).topologicalClosure
  have hle : L ≤ H.comap f := fun a ha => subset_closure ⟨a, ha, rfl⟩
  have hf := forgetPlaces_continuous D i hJ
  have hs := forgetPlaces_surjective D i hJ
  have hc' : CompactSpace (FinitePoints D i J ⧸ H) :=
    ⟨(Function.Surjective.range_eq (surjective_cosetMap f hle hs)) ▸
      isCompact_range (continuous_cosetMap f hle hf)⟩
  exact ⟨projection_nondiscrete D i hS hJ hd hj U hSnon hC hrep, H, rfl, hc',
    quotientMeasure_pushforward L H f hle hf hs hμ⟩

theorem compactOpenOutside : Specs.ArithmeticLatticeProjection.compactOpenOutside.{u, v} := by
  intro K _ G D i T hT
  let R (w : Outside D T) := LocalPoints D i w.1
  let B (w : Outside D T) : Set (R w) := localSubgroup D i w.1
  have hB (w : Outside D T) : IsCompact (B w) := by
    obtain ⟨w, hw⟩ := w
    cases w with
    | inl w => exact (integralCompactOpen D i w).1
    | inr w =>
      letI := hT w hw
      exact isCompact_univ
  letI (w : Outside D T) : CompactSpace (B w) := isCompact_iff_compactSpace.mp (hB w)
  let f := RestrictedProduct.structureMap R B cofinite
  have he : Set.range f = (integralOutside D i T : Set (Adeles D i T)) :=
    RestrictedProduct.range_structureMap R B
  rw [← he]
  have hopen := RestrictedProduct.isOpenEmbedding_structureMap (R := R) (A := B)
    (fun w => localSubgroup_open D i w.1)
  exact ⟨isCompact_range hopen.continuous, hopen.isOpen_range⟩

theorem localUnimodularity : Specs.ArithmeticLatticeProjection.localUnimodularity.{u, v} := by
  classical
  intro K _ G D i hA w
  haveI : Finite D.InfinitePlace := by
    cases D with
    | number h => letI := h; exact inferInstanceAs (Finite (NumberField.InfinitePlace K))
    | function F t => exact inferInstanceAs (Finite PEmpty)
  letI := Fintype.ofFinite D.InfinitePlace
  let T : Finset D.Place := insert w (Finset.univ.image Sum.inr)
  have hw : w ∈ T := Finset.mem_insert_self _ _
  have hT (a : D.InfinitePlace) : Sum.inr a ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  obtain ⟨hc, ho⟩ := compactOpenOutside D i T (fun a ha => (ha (hT a)).elim)
  have h := (latticeConstruction D i T (integralOutside D i T) hA ⟨w, hw⟩ hc ho).2.2.2.2.2.1
  let j : (↑T : Set D.Place) := ⟨w, hw⟩
  let R (a : (↑T : Set D.Place)) := LocalPoints D i a.1
  let e := Homeomorph.piSplitAt j R
  let em : FinitePoints D i T ≃ₜ* (R j × ∀ a : {a : (↑T : Set D.Place) // a ≠ j}, R a.1) :=
    { e.toEquiv with
      map_mul' := fun _ _ => rfl
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  exact unimodular_of_prod (unimodular_of_mulEquiv em h)

end Results
end LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
