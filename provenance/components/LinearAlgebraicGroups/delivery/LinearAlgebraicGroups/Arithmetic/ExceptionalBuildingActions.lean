import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingActions
import Mathlib.Tactic.Group

import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
namespace LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingActions

open Set
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalBuildingActions
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open scoped CategoryTheory.MonObj Classical Pointwise
attribute [local instance] integerAlgebra

noncomputable section

universe u v

section Local
variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

local notation "Ω" => alcoveStabilizer A (A.alcove p)
local notation "B" => A.SimpleWall p

private theorem unit_le_iwahori : C.T₀ ≤ C.I := by
  rw [← (show C.I ⊓ C.N = C.T₀ from C.localIwahori.intersection)]
  exact inf_le_left

private theorem iwahori_le_ordinary : C.I ≤ C.G₀ := le_sup_left

private theorem affine_eq_one_iff (n : C.N) : C.affine n = 1 ↔ (n : G) ∈ C.T₀ := by
  rw [← (show C.affine.ker.map C.N.subtype = C.T₀ from C.kernel)]
  exact ⟨fun h => ⟨n, h, rfl⟩, fun ⟨m, hm, h⟩ => (Subtype.ext h : m = n) ▸ hm⟩

private theorem same_label_div {n m : C.N} (h : C.affine n = C.affine m) :
    (n : G) * (m : G)⁻¹ ∈ C.T₀ :=
  (affine_eq_one_iff (n * m⁻¹)).mp (by simp [h])

private theorem same_label_inv_mul {n m : C.N} (h : C.affine n = C.affine m) :
    (n : G)⁻¹ * (m : G) ∈ C.T₀ :=
  (affine_eq_one_iff (n⁻¹ * m)).mp (by simp [h])

private theorem ordinary_label {q : ℕ} (hB : C.Bruhat q) (n : C.N) :
    (n : G) ∈ C.G₀ ↔ C.affine n ∈ A.affineWeylGroup := by
  constructor
  · intro hn
    have hm : (n : G) ∈ C.G₀ ⊓ C.N := ⟨hn, n.property⟩
    rw [hB.ordinary_normalizer] at hm
    obtain ⟨m, hm, he⟩ := hm
    exact (Subtype.ext he : m = n) ▸ hm
  · intro hn
    exact (le_sup_right : _ ≤ C.G₀) (show (n : G) ∈ _ from ⟨n, hn, rfl⟩)

private theorem lift_mem_ordinary (w : A.affineWeylGroup) : (C.lift w : G) ∈ C.G₀ :=
  (le_sup_right : _ ≤ C.G₀) (show (C.lift w : G) ∈ _ from
    ⟨C.lift w, by change C.affine (C.lift w) ∈ A.affineWeylGroup; rw [C.lift_label]; exact w.property, rfl⟩)

private theorem parahoric_le_ordinary (T : Set B) : parahoric C T ≤ C.G₀ := by
  apply (Subgroup.closure_le _).mpr
  rintro _ (hi | ⟨i, _, rfl⟩)
  · exact iwahori_le_ordinary hi
  · exact lift_mem_ordinary (C.coxeter.coxeter.simple i)

private theorem iwahori_le_parahoric (T : Set B) : C.I ≤ parahoric C T :=
  fun _ h => Subgroup.subset_closure (Or.inl h)

private theorem parahoric_empty : parahoric C ∅ = C.I := by
  rw [parahoric, image_empty, union_empty, Subgroup.closure_eq]

private theorem type_eq_one_iff (Q : C.TypeQuotient) (g : G) :
    typeChange C Q g = 1 ↔ g ∈ C.G₀ := by
  let _ := Q.normal
  change Q.quotient (QuotientGroup.mk (s := C.G₀) g) = 1 ↔ _
  rw [← Q.quotient.map_one, Q.quotient.injective.eq_iff, QuotientGroup.eq_one_iff]

@[simp] private theorem type_lift (Q : C.TypeQuotient) (ω : Ω) :
    typeChange C Q (Q.lift ω : G) = ω := Q.quotient_lift ω

private theorem lengthZero_mem_iff {n : C.N} :
    (n : G) ∈ lengthZeroNormalizer C ↔ ∃ ω : Ω, C.affine n = ω.val.val := by
  constructor
  · rintro ⟨m, ⟨o, ho, he⟩, hm⟩
    have he' : m = n := Subtype.ext hm
    exact ⟨⟨o, ho⟩, by rw [← he']; exact he.symm⟩
  · rintro ⟨ω, he⟩
    exact ⟨n, ⟨ω, ω.property, he.symm⟩, rfl⟩

private theorem lengthZero_lift (Q : C.TypeQuotient) (ω : Ω) :
    (Q.lift ω : G) ∈ lengthZeroNormalizer C :=
  lengthZero_mem_iff.mpr ⟨ω, Q.affine_lift ω⟩

private theorem type_eq_label (Q : C.TypeQuotient) (n : C.N) (ω : Ω)
    (hn : C.affine n = ω.val.val) : typeChange C Q n = ω := by
  have h := same_label_div (hn.trans (Q.affine_lift ω).symm)
  have ht := (type_eq_one_iff Q _).mpr (iwahori_le_ordinary (unit_le_iwahori h))
  rw [map_mul, map_inv, type_lift, mul_inv_eq_one] at ht
  exact ht

private theorem lengthZero_inter {q : ℕ} (hB : C.Bruhat q) :
    C.G₀ ⊓ lengthZeroNormalizer C = C.T₀ := by
  ext g
  constructor
  · rintro ⟨hg, ⟨n, ⟨o, ho, he⟩, rfl⟩⟩
    have hn := (ordinary_label hB n).mp hg
    let w : A.affineWeylGroup := ⟨C.affine n, hn⟩
    have hw : w.val '' A.alcove p = A.alcove p := by
      change C.affine n '' A.alcove p = _
      rw [← he]
      exact ho
    obtain ⟨a, _, huniq⟩ := C.geometry.simply_transitive p C.geometry.regular
    have h : w = 1 := (huniq w hw).trans (huniq 1 (by simp)).symm
    exact (affine_eq_one_iff n).mp (congrArg Subtype.val h)
  · intro hg
    have hi := unit_le_iwahori hg
    have hn : g ∈ C.N := by
      have h : g ∈ C.I ⊓ C.N := C.localIwahori.intersection.symm ▸ hg
      exact h.2
    exact ⟨iwahori_le_ordinary hi,
      lengthZero_mem_iff (C := C) (n := ⟨g, hn⟩) |>.mpr
        ⟨1, (affine_eq_one_iff ⟨g, hn⟩).mpr hg⟩⟩

private theorem lengthZero_normalizes (Q : C.TypeQuotient) :
    lengthZeroNormalizer C ≤ Subgroup.normalizer (C.I : Set G) := by
  rintro _ ⟨n, ⟨o, ho, he⟩, rfl⟩
  let ω : Ω := ⟨o, ho⟩
  have ht := same_label_div (he.symm.trans (Q.affine_lift ω).symm)
  have h₁ : (n : G) * (Q.lift ω : G)⁻¹ ∈ Subgroup.normalizer (C.I : Set G) :=
    Subgroup.le_normalizer (unit_le_iwahori ht)
  have h₂ : (Q.lift ω : G) ∈ Subgroup.normalizer (C.I : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Q.preserves_I ω)
  simpa using (Subgroup.normalizer (C.I : Set G)).mul_mem h₁ h₂

private def normalized (Q : C.TypeQuotient) (g : G) (h : C.G₀) : C.G₀ :=
  ⟨g * (h : G) * (Q.lift (typeChange C Q g) : G)⁻¹, (type_eq_one_iff Q _).mp (by
    rw [map_mul, map_mul, map_inv, type_lift, (type_eq_one_iff Q _).mpr h.property]
    simp)⟩

private theorem chamber_product (Q : C.TypeQuotient) :
    (baseChamberStabilizer C : Set G) = (C.I : Set G) * (lengthZeroNormalizer C : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (lengthZero_normalizes Q)

private theorem mem_chamber_stabilizer_iff (Q : C.TypeQuotient) (g : G) :
    g ∈ baseChamberStabilizer C ↔ (normalized Q g 1 : G) ∈ C.I := by
  change g ∈ (baseChamberStabilizer C : Set G) ↔ _
  rw [chamber_product Q]
  constructor
  · rintro ⟨i, hi, a, ⟨n, ⟨o, ho, he⟩, rfl⟩, rfl⟩
    let ω : Ω := ⟨o, ho⟩
    have h := type_eq_label Q n ω he.symm
    change i * (n : G) * (1 : G) * (Q.lift (typeChange C Q (i * n)) : G)⁻¹ ∈ C.I
    rw [map_mul, (type_eq_one_iff Q _).mpr (iwahori_le_ordinary hi), one_mul, h, mul_one,
      mul_assoc]
    exact C.I.mul_mem hi (unit_le_iwahori (same_label_div (he.symm.trans (Q.affine_lift ω).symm)))
  · intro hg
    exact ⟨normalized Q g 1, hg, Q.lift (typeChange C Q g),
      lengthZero_lift Q _, by simp [normalized]⟩

private def chamberCosets (Q : C.TypeQuotient) : Chamber C ≃ (G ⧸ baseChamberStabilizer C) := by
  let f : G ⧸ C.I → G ⧸ baseChamberStabilizer C := Quotient.map'
    (fun g : G => g) (fun _ _ h => by
      rw [QuotientGroup.leftRel_apply] at h ⊢
      exact (le_sup_left : C.I ≤ baseChamberStabilizer C) h)
  refine Equiv.ofBijective (fun g : Chamber C => f g.val) ⟨?_, ?_⟩
  · rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩ he
    change (QuotientGroup.mk ((g : G)) : G ⧸ baseChamberStabilizer C) =
      QuotientGroup.mk (h : G) at he
    have ho : (g : G)⁻¹ * (h : G) ∈ C.G₀ := C.G₀.mul_mem (C.G₀.inv_mem g.property) h.property
    have hi := (mem_chamber_stabilizer_iff Q _).mp (QuotientGroup.eq.mp he)
    have h1 := C.I.inv_mem (unit_le_iwahori ((affine_eq_one_iff (Q.lift 1)).mp (by simp [Q.affine_lift])))
    change (g : G)⁻¹ * (h : G) * 1 * (Q.lift (typeChange C Q ((g : G)⁻¹ * (h : G))) : G)⁻¹ ∈ C.I at hi
    rw [(type_eq_one_iff Q _).mpr ho, mul_one, C.I.mul_mem_cancel_right h1] at hi
    exact Subtype.ext (QuotientGroup.eq.mpr hi)
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      let a := normalized Q g 1
      refine ⟨⟨QuotientGroup.mk (a : G), a, rfl⟩, QuotientGroup.eq.mpr ?_⟩
      have hl : (Q.lift (typeChange C Q g) : G) ∈ baseChamberStabilizer C :=
        (le_sup_right : lengthZeroNormalizer C ≤ baseChamberStabilizer C) (lengthZero_lift Q _)
      simpa [a, normalized] using hl

/-- Automorphisms carrying the Iwahori and the marked simple lifts carry their parahorics. -/
private theorem map_parahoric (s : MulAut G) (e : Equiv.Perm B)
    (hI : C.I.map s.toMonoidHom = C.I)
    (hl : ∀ i, s (C.lift (C.coxeter.coxeter.simple i)) *
      (C.lift (C.coxeter.coxeter.simple (e i)) : G)⁻¹ ∈ C.I) (T : Set B) :
    (parahoric C T).map s.toMonoidHom = parahoric C (e '' T) := by
  rw [parahoric, MonoidHom.map_closure]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx | ⟨i, hi, rfl⟩, rfl⟩
    · exact iwahori_le_parahoric _ (hI ▸ ⟨x, hx, rfl⟩)
    · have ht := iwahori_le_parahoric (C := C) (e '' T) (hl i)
      have h' := Subgroup.subset_closure (k := (C.I : Set G) ∪
        (fun w => (C.lift w : G)) ∘ C.coxeter.coxeter.simple '' (e '' T))
        (Or.inr ⟨e i, ⟨i, hi, rfl⟩, rfl⟩)
      simpa using (parahoric C (e '' T)).mul_mem ht h'
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y (hy | ⟨_, ⟨i, hi, rfl⟩, rfl⟩)
    · have hs : y ∈ C.I.map s.toMonoidHom := hI.symm ▸ hy
      obtain ⟨x, hx, he⟩ := hs
      exact Subgroup.subset_closure ⟨x, Or.inl hx, he⟩
    · have hs : _ ∈ C.I.map s.toMonoidHom := hI.symm ▸ (hl i)
      obtain ⟨x, hx, hx'⟩ := hs
      have h₁ := Subgroup.subset_closure (k := s.toMonoidHom '' ((C.I : Set G) ∪
        (fun w => (C.lift w : G)) ∘ C.coxeter.coxeter.simple '' T)) ⟨x, Or.inl hx, rfl⟩
      have h₂ := Subgroup.subset_closure (k := s.toMonoidHom '' ((C.I : Set G) ∪
        (fun w => (C.lift w : G)) ∘ C.coxeter.coxeter.simple '' T))
        ⟨_, Or.inr ⟨i, hi, rfl⟩, rfl⟩
      rw [show s.toMonoidHom x = _ from hx'] at h₁
      simpa using (Subgroup.closure _).mul_mem ((Subgroup.closure _).inv_mem h₁) h₂

private theorem reflection_apply (a : J × ℤ) (x : V) :
    A.reflection a x = x - A.wallValue a x • A.coroot a.1 := by
  change (-a.2) • A.coroot a.1 + Module.reflection (A.diagonal a.1) x =
    x - (A.root a.1 x + (a.2 : ℚ)) • A.coroot a.1
  rw [Module.reflection_apply, add_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg, neg_smul]
  abel

private theorem lengthZero_simple_label (Q : C.TypeQuotient) (ω : Ω) (i : B) :
    ω.val.val * (C.coxeter.coxeter.simple i).val * ω.val.val⁻¹ =
      (C.coxeter.coxeter.simple (Q.wallPerm ω i)).val := by
  let e := ω.val.val
  obtain ⟨σ, hσ⟩ := C.geometry.extended_symmetries ω.val.property
  have he : e '' A.alcove p = A.alcove p := ω.property
  have hv (x : V) : A.wallValue (σ i.val) (e x) = A.wallValue i.val x := (hσ i.val).1 x
  have hc : e.linear (A.coroot i.val.1) = A.coroot (σ i.val).1 := (hσ i.val).2
  have hp : p ∈ A.alcove p := fun _ h => h
  obtain ⟨z, hz, hz'⟩ := he.symm ▸ hp
  have hpos : A.positive p (σ i.val) := by
    change 0 < A.wallValue (σ i.val) p
    calc
      0 < A.wallValue i.val z := hz i.val i.property.1
      _ = A.wallValue (σ i.val) (e z) := (hv z).symm
      _ = A.wallValue (σ i.val) p := congrArg (A.wallValue (σ i.val)) hz' 
  have hwall : σ i.val = (Q.wallPerm ω i).val := by
    by_contra hne
    obtain ⟨y, hy, hpanel⟩ := (Q.wallPerm ω i).property.2
    have hy' : y ∈ e '' A.wallHyperplane i.val := (Q.wall_action ω i).symm ▸ hy
    obtain ⟨x, hx, rfl⟩ := hy'
    have hn := hpanel (σ i.val) hpos hne
    change 0 < A.wallValue (σ i.val) (e x) at hn
    rw [hv, show A.wallValue i.val x = 0 from hx] at hn
    exact (lt_irrefl _ hn)
  have hconj : e * A.reflection i.val = A.reflection (σ i.val) * e := by
    ext x
    change e (A.reflection i.val x) = A.reflection (σ i.val) (e x)
    rw [reflection_apply, reflection_apply, hv]
    have hd : x - A.wallValue i.val x • A.coroot i.val.1 =
        (-(A.wallValue i.val x • A.coroot i.val.1)) +ᵥ x := by
      change _ = _ + x
      abel
    rw [hd]
    rw [e.map_vadd, map_neg, map_smul, hc]
    change -(A.wallValue i.val x • A.coroot (σ i.val).1) + e x = _
    abel
  rw [C.coxeter.simple_eq]
  change e * A.reflection i.val * e⁻¹ = A.reflection (Q.wallPerm ω i).val
  rw [hconj, hwall]
  group

private theorem lengthZero_conjugates (Q : C.TypeQuotient) (n : C.N) (ω : Ω)
    (hn : C.affine n = ω.val.val) (T : Set B) :
    (parahoric C T).map (MulAut.conj (n : G)).toMonoidHom =
      parahoric C (Q.wallPerm ω '' T) := by
  apply map_parahoric _ (Q.wallPerm ω) _ _ T
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (lengthZero_normalizes Q (lengthZero_mem_iff.mpr ⟨ω, hn⟩))
  · intro i
    have he : C.affine (n * C.lift (C.coxeter.coxeter.simple i) * n⁻¹) =
        C.affine (C.lift (C.coxeter.coxeter.simple (Q.wallPerm ω i))) := by
      simp only [map_mul, map_inv, hn, C.lift_label, lengthZero_simple_label Q ω i]
    exact unit_le_iwahori (same_label_div he)

private def normalizerComparison {q : ℕ} (hB : C.Bruhat q) (Q : C.TypeQuotient) :
    NormalizerComparison Q where
  kernel := Subgroup.ext (type_eq_one_iff Q)
  label := type_eq_label Q
  normalizes := lengthZero_normalizes Q
  intersection := lengthZero_inter hB
  factorization g := ⟨normalized Q g 1, by simp [normalized]⟩
  ordinary_product := by
    ext g
    exact iff_true_intro ⟨normalized Q g 1, (normalized Q g 1).property,
      Q.lift (typeChange C Q g), lengthZero_lift Q _, by simp [normalized]⟩
  chamber_product := chamber_product Q
  cosets := chamberCosets Q
  cosets_mk _ := rfl
  conjugates := lengthZero_conjugates Q

section Gluing

variable {X : Type v} {ctype : X → Set (A.SimpleWall p)}

theorem place_eq_iff (g h : C.G₀) (t s : X) :
    place (C := C) (cotype := ctype) g t = place (C := C) (cotype := ctype) h s ↔
      t = s ∧ (g : G)⁻¹ * (h : G) ∈ parahoric C (ctype t) :=
  by exact Quotient.eq

private theorem place_eq_unit {g h : C.G₀} (t : X) (hh : (g : G)⁻¹ * (h : G) ∈ C.T₀) :
    place (C := C) (cotype := ctype) g t = place (C := C) (cotype := ctype) h t :=
  (place_eq_iff _ _ _ _).mpr ⟨rfl, iwahori_le_parahoric _ (unit_le_iwahori hh)⟩

private def actionOf {H Y : Type*} [Group H] (f : H → Y → Y)
    (hone : ∀ x, f 1 x = x) (hmul : ∀ a b x, f (a * b) x = f a (f b x)) :
    H →* Equiv.Perm Y where
  toFun a :=
    { toFun := f a
      invFun := f a⁻¹
      left_inv := fun x => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hmul, mul_inv_cancel, hone] }
  map_one' := Equiv.ext hone
  map_mul' a b := Equiv.ext (hmul a b)

private theorem lift_one_mem_unit (Q : C.TypeQuotient) : (Q.lift 1 : G) ∈ C.T₀ :=
  (affine_eq_one_iff (Q.lift 1)).mp (by simp [Q.affine_lift])

variable {Q : C.TypeQuotient} (S : Coordinates C Q X)

private def adjointMap (g : G) : Point (C := C) S.cotype → Point (C := C) S.cotype :=
  Quotient.lift (fun r : C.G₀ × X => place (normalized Q g r.1) (S.perm (typeChange C Q g) r.2))
    (by
      rintro ⟨h, t⟩ ⟨k, s⟩ (⟨rfl, hm⟩ : t = s ∧
        (h : G)⁻¹ * (k : G) ∈ parahoric C (S.cotype t))
      apply (place_eq_iff _ _ _ _).mpr
      refine ⟨rfl, ?_⟩
      let ω := typeChange C Q g
      have hmem : (MulAut.conj (Q.lift ω : G)) ((h : G)⁻¹ * (k : G)) ∈
          parahoric C (Q.wallPerm ω '' S.cotype t) := by
        rw [← lengthZero_conjugates Q (Q.lift ω) ω (Q.affine_lift ω)]
        exact ⟨_, hm, rfl⟩
      rw [S.cotype_perm]
      convert hmem using 1
      change (g * (h : G) * (Q.lift ω : G)⁻¹)⁻¹ * (g * (k : G) * (Q.lift ω : G)⁻¹) =
        (Q.lift ω : G) * ((h : G)⁻¹ * (k : G)) * (Q.lift ω : G)⁻¹
      group)

private theorem adjointMap_place (g : G) (h : C.G₀) (t : X) :
    adjointMap S g (place h t) = place (normalized Q g h) (S.perm (typeChange C Q g) t) := rfl

private theorem adjointMap_ordinary (g h : C.G₀) (t : X) :
    adjointMap S g (place h t) = place (g * h) t := by
  rw [adjointMap_place, (type_eq_one_iff Q _).mpr g.property, map_one]
  apply place_eq_unit
  change ((g : G) * (h : G) * (Q.lift (typeChange C Q g) : G)⁻¹)⁻¹ * ((g : G) * (h : G)) ∈ C.T₀
  rw [(type_eq_one_iff Q _).mpr g.property]
  simpa [mul_assoc] using lift_one_mem_unit Q

private theorem adjointMap_mul (g h : G) (x : Point (C := C) S.cotype) :
    adjointMap S (g * h) x = adjointMap S g (adjointMap S h x) := by
  induction x using Quotient.inductionOn with
  | h r =>
    obtain ⟨k, t⟩ := r
    change adjointMap S (g * h) (place k t) = _
    change adjointMap S (g * h) (place k t) = adjointMap S g (adjointMap S h (place k t))
    rw [adjointMap_place, adjointMap_place, adjointMap_place]
    have hp : S.perm (typeChange C Q (g * h)) t =
        S.perm (typeChange C Q g) (S.perm (typeChange C Q h) t) := by
      rw [map_mul, map_mul, Equiv.Perm.mul_apply]
    rw [hp]
    apply place_eq_unit
    let ωg := typeChange C Q g
    let ωh := typeChange C Q h
    let ωgh := typeChange C Q (g * h)
    have he : C.affine (Q.lift ωgh) = C.affine (Q.lift ωg * Q.lift ωh) := by
      simp only [map_mul, Q.affine_lift, ωgh, ωg, ωh, Subgroup.coe_mul]
    have ht := same_label_div he
    change ((g * h) * (k : G) * (Q.lift ωgh : G)⁻¹)⁻¹ *
      (g * (h * (k : G) * (Q.lift ωh : G)⁻¹) * (Q.lift ωg : G)⁻¹) ∈ C.T₀
    convert ht using 1
    change ((g * h) * (k : G) * (Q.lift ωgh : G)⁻¹)⁻¹ *
      (g * (h * (k : G) * (Q.lift ωh : G)⁻¹) * (Q.lift ωg : G)⁻¹) =
        (Q.lift ωgh : G) * ((Q.lift ωg : G) * (Q.lift ωh : G))⁻¹
    group

private def adjointPerm : G →* Equiv.Perm (Point (C := C) S.cotype) :=
  actionOf (adjointMap S) (by
    intro x
    induction x using Quotient.inductionOn with
    | h r =>
      obtain ⟨g, t⟩ := r
      change adjointMap S ((1 : C.G₀) : G) (place g t) = place g t
      rw [adjointMap_ordinary, one_mul]) (adjointMap_mul S)

private theorem adjointPerm_place (g : G) (h : C.G₀) (t : X) :
    adjointPerm S g (place h t) = place (normalized Q g h) (S.perm (typeChange C Q g) t) := rfl

private theorem adjoint_normalizer {q : ℕ} (hB : C.Bruhat q) (n : C.N)
    (w : A.affineWeylGroup) (h : (C.lift w : G) ∈ C.G₀) (t : X) :
    ∃ (v : A.affineWeylGroup) (hv : (C.lift v : G) ∈ C.G₀),
      v.val = C.affine n * w.val * (typeChange C Q n).val.val⁻¹ ∧
      adjointPerm S n (place ⟨(C.lift w : G), h⟩ t) =
        place ⟨(C.lift v : G), hv⟩ (S.perm (typeChange C Q n) t) := by
  let ω := typeChange C Q n
  let m := n * C.lift w * (Q.lift ω)⁻¹
  have hm : (m : G) ∈ C.G₀ := (normalized Q n ⟨(C.lift w : G), h⟩).property
  let v : A.affineWeylGroup := ⟨C.affine m, (ordinary_label hB m).mp hm⟩
  refine ⟨v, lift_mem_ordinary v, ?_, ?_⟩
  · change C.affine m = _
    simp [m, ω, C.lift_label, Q.affine_lift]
  · rw [adjointPerm_place]
    apply place_eq_unit
    exact same_label_inv_mul (show C.affine m = C.affine (C.lift v) from (C.lift_label v).symm)

private theorem normalized_one_mem_iff (T : Set B) (g : G) (ω : Ω) (hω : ω = typeChange C Q g) :
    (normalized Q g 1 : G) ∈ parahoric C T ↔
      ∃ a : parahoric C T, g = (a : G) * (Q.lift ω : G) := by
  subst ω
  constructor
  · intro h
    exact ⟨⟨normalized Q g 1, h⟩, by simp [normalized]⟩
  · rintro ⟨a, ha⟩
    change g * 1 * (Q.lift (typeChange C Q g) : G)⁻¹ ∈ parahoric C T
    rw [mul_one, ← eq_mul_inv_of_mul_eq ha.symm]
    exact a.property

private theorem adjoint_chamber_image (g : G) :
    adjointPerm S g '' chamberPoints (cotype := S.cotype) 1 =
      chamberPoints (normalized Q g 1) := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, adjointPerm_place S g 1 t⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (S.perm (typeChange C Q g)).surjective t
    exact ⟨place 1 s, ⟨s, rfl⟩, adjointPerm_place S g 1 s⟩

private theorem adjoint_chamber_stabilizer (h : ∃ t, S.cotype t = ∅) (g : G) :
    adjointPerm S g '' chamberPoints (cotype := S.cotype) 1 = chamberPoints 1 ↔
      g ∈ baseChamberStabilizer C := by
  rw [adjoint_chamber_image, mem_chamber_stabilizer_iff Q]
  obtain ⟨t, ht⟩ := h
  constructor
  · intro he
    have hx : place (cotype := S.cotype) 1 t ∈ chamberPoints (normalized Q g 1) := by
      rw [he]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hx
    have hh := (place_eq_iff _ _ _ _).mp hs.symm
    simpa [ht, parahoric_empty] using hh.2
  · intro hg
    have he (s : X) : place (cotype := S.cotype) 1 s = place (normalized Q g 1) s := by
      apply (place_eq_iff _ _ _ _).mpr
      refine ⟨rfl, ?_⟩
      simpa using iwahori_le_parahoric (S.cotype s) hg
    simp only [chamberPoints, show place (cotype := S.cotype) 1 =
      place (normalized Q g 1) from funext he]

private theorem adjoint_open_face_image (g : G) (T : Set B) :
    adjointPerm S g '' openFace (cotype := S.cotype) 1 T =
      openFace (normalized Q g 1) (Q.wallPerm (typeChange C Q g) '' T) := by
  ext x
  simp only [openFace, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨_, by rw [S.cotype_perm, ht], (adjointPerm_place S g 1 t).symm⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, rfl⟩ := (S.perm (typeChange C Q g)).surjective s
    have ht : S.cotype t = T :=
      (Set.image_injective.mpr (Q.wallPerm (typeChange C Q g)).injective) (by
        simpa only [S.cotype_perm] using hs)
    exact ⟨place 1 t, ⟨t, ht, rfl⟩, adjointPerm_place S g 1 t⟩

private theorem adjoint_face_stabilizer (T : Set B) (h : ∃ t, S.cotype t = T) (g : G) :
    adjointPerm S g '' openFace (cotype := S.cotype) 1 T = openFace 1 T ↔
      ∃ (a : parahoric C T) (ω : Ω), g = (a : G) * (Q.lift ω : G) ∧ Q.wallPerm ω '' T = T := by
  rw [adjoint_open_face_image]
  obtain ⟨t, ht⟩ := h
  constructor
  · intro he
    have hx : place (cotype := S.cotype) 1 t ∈
        openFace (normalized Q g 1) (Q.wallPerm (typeChange C Q g) '' T) :=
      he.symm ▸ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, he'⟩ := hx
    rcases (place_eq_iff _ _ _ _).mp he'.symm with ⟨rfl, hn⟩
    change S.cotype t = Q.wallPerm (typeChange C Q g) '' T at hs
    rw [ht] at hn hs
    simp only [Subgroup.coe_one, inv_one, one_mul] at hn
    obtain ⟨a, ha⟩ := (normalized_one_mem_iff T g _ rfl).mp hn
    exact ⟨a, _, ha, hs.symm⟩
  · rintro ⟨a, ω, he, hω⟩
    have hω' : typeChange C Q g = ω := by
      rw [he, map_mul, type_lift, (type_eq_one_iff Q _).mpr (parahoric_le_ordinary T a.property), one_mul]
    have hn := (normalized_one_mem_iff T g ω hω'.symm).mpr ⟨a, he⟩
    rw [hω', hω]
    apply Set.image_congr
    intro s hs
    apply (place_eq_iff _ _ _ _).mpr
    refine ⟨rfl, ?_⟩
    rw [show S.cotype s = T from hs]
    simpa using (parahoric C T).inv_mem hn

private theorem adjoint_point_stabilizer (t : X) (g : G) :
    adjointPerm S g (place 1 t) = place 1 t ↔
      ∃ (a : parahoric C (S.cotype t)) (ω : Ω), g = (a : G) * (Q.lift ω : G) ∧ S.perm ω t = t := by
  rw [adjointPerm_place, eq_comm (a := place _ _), place_eq_iff]
  constructor
  · rintro ⟨ht, hm⟩
    simp only [Subgroup.coe_one, inv_one, one_mul] at hm
    obtain ⟨a, ha⟩ := (normalized_one_mem_iff _ g _ rfl).mp hm
    exact ⟨a, _, ha, ht.symm⟩
  · rintro ⟨a, ω, ha, ht⟩
    have hω : typeChange C Q g = ω := by
      rw [ha, map_mul, type_lift,
        (type_eq_one_iff Q _).mpr (parahoric_le_ordinary _ a.property), one_mul]
    refine ⟨by rw [hω, ht], ?_⟩
    simpa using (normalized_one_mem_iff _ g ω hω.symm).mpr ⟨a, ha⟩

private theorem adjoint_stabilizer_types (t : X) (g : G)
    (h : adjointPerm S g (place 1 t) = place 1 t) :
    Q.wallPerm (typeChange C Q g) '' S.cotype t = S.cotype t := by
  rw [adjointPerm_place] at h
  rw [← S.cotype_perm, (place_eq_iff _ _ _ _).mp h |>.1]

private def adjointAction {q : ℕ} (hB : C.Bruhat q) : AdjointAction S where
  action := adjointPerm S
  on_place g h t := ⟨normalized Q g h, rfl, adjointPerm_place S g h t⟩
  ordinary := adjointMap_ordinary S
  normalizer := adjoint_normalizer S hB
  chamber_stabilizer := adjoint_chamber_stabilizer S
  face_stabilizer := adjoint_face_stabilizer S
  point_stabilizer := adjoint_point_stabilizer S
  stabilizer_types := adjoint_stabilizer_types S
  barycenter_stabilizer t weight hw hperm r hb g := by
    rw [adjoint_point_stabilizer]
    constructor
    · rintro ⟨a, ω, ha, ht⟩
      exact ⟨a, ω, ha, (S.cotype_perm ω t).symm.trans (congrArg S.cotype ht)⟩
    · rintro ⟨a, ω, ha, ht⟩
      refine ⟨a, ω, ha, hw ?_⟩
      funext j
      obtain ⟨i, rfl⟩ := (Q.wallPerm ω).surjective j
      have hm : Q.wallPerm ω i ∈ S.cotype t ↔ i ∈ S.cotype t := by
        nth_rw 1 [← ht]
        constructor
        · rintro ⟨k, hk, he⟩
          exact (Q.wallPerm ω).injective he ▸ hk
        · intro hi
          exact ⟨i, hi, rfl⟩
      rw [hperm, hb i, hb (Q.wallPerm ω i), hm]

end Gluing

section Coefficients

variable {Γ : Type u} [Group Γ] {Q : C.TypeQuotient} {ρ : Γ →* MulAut G}
  (R : CoefficientTransport Q ρ)

private theorem coefficient_type (σ : Γ) (g : G) :
    typeChange C Q (ρ σ g) = R.types σ (typeChange C Q g) :=
  (R.type_transport σ).1 g

private theorem coefficient_parahoric (σ : Γ) (T : Set B) :
    (parahoric C T).map (ρ σ).toMonoidHom = parahoric C (R.walls σ '' T) := by
  apply map_parahoric _ _ (R.comparison σ).1 _ T
  intro i
  obtain ⟨w, hw, ht⟩ := (R.comparison σ).2.2.2.2.2.2.2 (C.coxeter.coxeter.simple i)
  have he : w = C.coxeter.coxeter.simple (R.walls σ i) :=
    Subtype.ext (hw.trans (R.simple_label σ i).symm)
  exact unit_le_iwahori (he ▸ ht)

private theorem coefficient_alcove_label (σ : Γ) (ω : Ω) :
    (R.types σ ω).val.val = R.affine σ * ω.val.val * (R.affine σ)⁻¹ := by
  have hn : ρ σ (Q.lift ω : G) ∈ C.N := by
    have hm : ρ σ (Q.lift ω : G) ∈ C.N.map (ρ σ).toMonoidHom :=
      ⟨Q.lift ω, (Q.lift ω).property, rfl⟩
    rw [(R.comparison σ).2.1] at hm
    exact hm
  let n : C.N := ⟨ρ σ (Q.lift ω : G), hn⟩
  have he : C.affine n = R.affine σ * C.affine (Q.lift ω) * (R.affine σ)⁻¹ :=
    (R.comparison σ).2.2.2.2.2.2.1 (Q.lift ω) n rfl
  have hu : C.affine (n * (Q.lift (R.types σ ω))⁻¹) = 1 :=
    (affine_eq_one_iff _).mpr ((R.type_transport σ).2 ω)
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  rw [← Q.affine_lift, ← hu, he, Q.affine_lift]

private theorem simpleWall_hyperplane_injective :
    Function.Injective (fun i : B => A.wallHyperplane i.val) := by
  intro i k h
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx, hp⟩ := k.property.2
  have hi := hp i.val i.property.1 hne
  change 0 < A.wallValue i.val x at hi
  have hx' : x ∈ A.wallHyperplane i.val := by
    change A.wallHyperplane i.val = A.wallHyperplane k.val at h
    rw [h]
    exact hx
  rw [show A.wallValue i.val x = 0 from hx'] at hi
  exact lt_irrefl _ hi

private theorem coefficient_wall_compat (σ : Γ) (ω : Ω) :
    R.walls σ * Q.wallPerm ω = Q.wallPerm (R.types σ ω) * R.walls σ := by
  apply Equiv.ext
  intro i
  apply simpleWall_hyperplane_injective (A := A) (p := p)
  change A.wallHyperplane (R.walls σ (Q.wallPerm ω i)).val =
    A.wallHyperplane (Q.wallPerm (R.types σ ω) (R.walls σ i)).val
  have ha : R.affine σ * ω.val.val = (R.types σ ω).val.val * R.affine σ := by
    rw [coefficient_alcove_label R]
    group
  rw [← R.wall, ← Q.wall_action, ← Q.wall_action, ← R.wall, Set.image_image, Set.image_image]
  exact congrArg (fun f : V ≃ᵃ[ℚ] V => f '' A.wallHyperplane i.val) ha

variable {X : Type v} {S : Coordinates C Q X}
  (perm : Γ →* Equiv.Perm X)
  (hctype : ∀ σ t, S.cotype (perm σ t) = R.walls σ '' S.cotype t)

private def coefficientRep (σ : Γ) (g : C.G₀) : C.G₀ :=
  ⟨ρ σ (g : G), by
    have hm : ρ σ (g : G) ∈ C.G₀.map (ρ σ).toMonoidHom := ⟨g, g.property, rfl⟩
    rw [(R.comparison σ).2.2.2.1] at hm
    exact hm⟩

private def coefficientMap (σ : Γ) : Point (C := C) S.cotype → Point (C := C) S.cotype :=
  Quotient.lift (fun r : C.G₀ × X => place (coefficientRep R σ r.1) (perm σ r.2)) (by
    rintro ⟨g, t⟩ ⟨h, s⟩ (⟨rfl, hp⟩ : t = s ∧ (g : G)⁻¹ * (h : G) ∈ parahoric C (S.cotype t))
    apply (place_eq_iff _ _ _ _).mpr
    refine ⟨rfl, ?_⟩
    rw [hctype, ← coefficient_parahoric R]
    exact ⟨(g : G)⁻¹ * (h : G), hp, by simp [coefficientRep]⟩)

private theorem coefficientMap_place (σ : Γ) (g : C.G₀) (t : X) :
    coefficientMap R perm hctype σ (place g t) = place (coefficientRep R σ g) (perm σ t) := rfl

private def coefficientPerm : Γ →* Equiv.Perm (Point (C := C) S.cotype) :=
  actionOf (coefficientMap R perm hctype) (by
    intro x
    induction x using Quotient.inductionOn with
    | h r =>
      obtain ⟨g, t⟩ := r
      change coefficientMap R perm hctype 1 (place g t) = place g t
      rw [coefficientMap_place, map_one, Equiv.Perm.one_apply]
      have he : coefficientRep R 1 g = g := Subtype.ext (by simp [coefficientRep])
      rw [he]) (by
    intro σ τ x
    induction x using Quotient.inductionOn with
    | h r =>
      obtain ⟨g, t⟩ := r
      change coefficientMap R perm hctype (σ * τ) (place g t) =
        coefficientMap R perm hctype σ (coefficientMap R perm hctype τ (place g t))
      rw [coefficientMap_place, coefficientMap_place, coefficientMap_place, map_mul, Equiv.Perm.mul_apply]
      have he : coefficientRep R (σ * τ) g = coefficientRep R σ (coefficientRep R τ g) :=
        Subtype.ext (by simp [coefficientRep, MulAut.mul_apply])
      rw [he])

private theorem coefficientPerm_place (σ : Γ) (g : C.G₀) (t : X) :
    coefficientPerm R perm hctype σ (place g t) = place (coefficientRep R σ g) (perm σ t) := rfl

variable (ad : AdjointAction S)
  (hperm : ∀ σ ω, perm σ * S.perm ω = S.perm (R.types σ ω) * perm σ)

include hperm in
private theorem coefficient_compatible (σ : Γ) (g : G) (x : Point (C := C) S.cotype) :
    coefficientPerm R perm hctype σ (ad.action g x) =
      ad.action (ρ σ g) (coefficientPerm R perm hctype σ x) := by
  induction x using Quotient.inductionOn with
  | h r =>
    obtain ⟨k, t⟩ := r
    change coefficientPerm R perm hctype σ (ad.action g (place k t)) =
      ad.action (ρ σ g) (coefficientPerm R perm hctype σ (place k t))
    obtain ⟨b, hb, hact⟩ := ad.on_place g k t
    rw [hact, coefficientPerm_place, coefficientPerm_place]
    obtain ⟨c, hc, hact'⟩ := ad.on_place (ρ σ g) (coefficientRep R σ k) (perm σ t)
    rw [hact']
    have hp := congrArg (fun f : Equiv.Perm X => f t) (hperm σ (typeChange C Q g))
    simp only [Equiv.Perm.mul_apply] at hp
    rw [hp, ← coefficient_type R]
    apply place_eq_unit
    have hc' : (c : G) =
        ρ σ g * ρ σ (k : G) * (Q.lift (typeChange C Q (ρ σ g)) : G)⁻¹ := hc
    change (ρ σ (b : G))⁻¹ * (c : G) ∈ C.T₀
    rw [hc', hb, map_mul, map_mul, map_inv, coefficient_type R]
    have hd : ρ σ (Q.lift (typeChange C Q g) : G) *
        (Q.lift (R.types σ (typeChange C Q g)) : G)⁻¹ ∈ C.T₀ :=
      (R.type_transport σ).2 (typeChange C Q g)
    convert hd using 1
    group

private theorem cocycle_one (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    a 1 = 1 := by
  have h := ha 1 1
  rw [mul_one, map_one, MulAut.one_apply] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

private def twistAction (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    Γ →* Equiv.Perm (Point (C := C) S.cotype) where
  toFun σ := ad.action (a σ) * coefficientPerm R perm hctype σ
  map_one' := by rw [cocycle_one a ha, map_one, map_one, mul_one]
  map_mul' σ τ := by
    ext x
    simp only [ha, map_mul, Equiv.Perm.mul_apply]
    rw [coefficient_compatible R perm hctype ad hperm]

private def twistTypes (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    Γ →* Equiv.Perm B where
  toFun σ := Q.wallPerm (typeChange C Q (a σ)) * R.walls σ
  map_one' := by rw [cocycle_one a ha, map_one, map_one, map_one, mul_one]
  map_mul' σ τ := by
    simp only [ha, map_mul, coefficient_type R]
    calc
      _ = Q.wallPerm (typeChange C Q (a σ)) *
          (Q.wallPerm (R.types σ (typeChange C Q (a τ))) * R.walls σ) * R.walls τ := by
        simp only [mul_assoc]
      _ = _ := by rw [← coefficient_wall_compat R]; simp only [mul_assoc]

private def coefficientAction : CoefficientAction ad R perm where
  type_equivariance := coefficient_type R
  wall_compat := coefficient_wall_compat R
  parahoric_equivariance := coefficient_parahoric R
  action := coefficientPerm R perm hctype
  on_place σ g t := ⟨coefficientRep R σ g, rfl, coefficientPerm_place R perm hctype σ g t⟩
  compatible := coefficient_compatible R perm hctype ad hperm
  twist a ha := by
    refine ⟨twistAction R perm hctype ad hperm a ha, twistTypes R a ha, fun _ _ => rfl,
      fun _ => rfl, ?_⟩
    intro σ g t
    obtain ⟨h, _, hh⟩ := ad.on_place (a σ) (coefficientRep R σ g) (perm σ t)
    refine ⟨h, hh, ?_⟩
    rw [S.cotype_perm, hctype, Set.image_image]
    rfl

end Coefficients

end Local

end

theorem normalizerActions_conditional.{u,v}
    (_coxeterDoubleCosets : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u,u,u})
    (_e6CoweightClass : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u}) :
    NormalizerActions.{u,v} := by
  intro K _ _ _ _ D M G Wf _ _ j V J _ _ A p C q hB Q
  exact ⟨normalizerComparison hB Q⟩

theorem adjointActions_conditional.{u,v}
    (_coxeterDoubleCosets : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u,u,u})
    (_e6CoweightClass : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u}) :
    AdjointActions.{u,v} := by
  intro K _ _ _ _ D M G Wf _ _ j V J _ _ A p C q hB Q X S
  exact ⟨adjointAction S hB⟩

theorem coefficientActions_conditional.{u,v}
    (_coxeterDoubleCosets : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u,u,u})
    (_e6CoweightClass : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u}) :
    CoefficientActions.{u,v} := by
  intro K _ _ _ _ D M G Wf _ _ j V J _ _ A p C q _ Q X S ad Γ _ ρ R perm hc hp
  exact ⟨coefficientAction R perm hc ad hp⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingActions

universe v8_closure_5c0292bcbd75332c_u0 v8_closure_5c0292bcbd75332c_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«adjointActions» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingActions».«AdjointActions».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«adjointActions_conditional».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«coefficientActions» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingActions».«CoefficientActions».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«coefficientActions_conditional».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«normalizerActions» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingActions».«NormalizerActions».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingActions».«normalizerActions_conditional».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0, v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_5c0292bcbd75332c_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_5c0292bcbd75332c_u0})
