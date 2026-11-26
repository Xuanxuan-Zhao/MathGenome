import Specs.LinearAlgebraicGroups.Relative.LeviConjugacy
import Specs.LinearAlgebraicGroups.Relative.RationalCocharacter
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Affine.LieLeftExact
import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Flag.NormalAffineQuotient
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Solvable.TorusSections
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Relative.RationalCocharacter
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Relative.LeviConjugacy

open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup IsSchemeKernel)
open Specs.LeviConjugacy (Transports)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (LimitDecomposition multiplyFactors)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k] {P C N H : GroupScheme k}

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 1024
set_option linter.style.haveILetI false

private abbrev underlying {A B : GroupScheme k} (f : A ⟶ B) : A.X ⟶ B.X :=
  f.hom.hom

private theorem underlying_comp {A B D : GroupScheme k} (f : A ⟶ B) (g : B ⟶ D) :
    underlying (f ≫ g) = underlying f ≫ underlying g := rfl

private theorem underlying_id (A : GroupScheme k) : underlying (𝟙 A) = 𝟙 A.X := rfl

private lemma closed_mono (J : ClosedSubgroup P) : Mono (underlying J.inclusion) := by
  let := J.isClosedImmersion
  exact (Over.forget _).mono_of_mono_map (f := underlying J.inclusion)
    (inferInstanceAs (Mono J.inclusion.hom.hom.left))

/-- Conjugation carrying one section to the other, with the same quotient
coordinate. The equation is tested after every change of test scheme. -/
private def Intertwines (s t : C ⟶ P) {X : SchemeOver k} (g : X ⟶ P.X) : Prop :=
  ∀ (Y : SchemeOver k) (f : Y ⟶ X) (x : Y ⟶ C.X),
    (f ≫ g) * (x ≫ underlying s) = (x ≫ underlying t) * (f ≫ g)

private theorem intertwines_iff (s t : C ⟶ P) {X : SchemeOver k} (g : X ⟶ P.X) :
    Intertwines s t g ↔
      (snd C.X X ≫ g) * (fst C.X X ≫ underlying s) =
        (fst C.X X ≫ underlying t) * (snd C.X X ≫ g) := by
  constructor
  · exact fun h ↦ h _ (snd _ _) (fst _ _)
  · intro h Y f x
    simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc] using
      congrArg (fun a ↦ lift x f ≫ a) h

private theorem intertwines_pullback {s t : C ⟶ P} {X Y : SchemeOver k}
    {g : X ⟶ P.X} (h : Intertwines s t g) (f : Y ⟶ X) :
    Intertwines s t (f ≫ g) := by
  intro Z a x
  simpa only [Category.assoc] using h Z (a ≫ f) x

private theorem intertwines_inv {s t : C ⟶ P} {X : SchemeOver k}
    {g : X ⟶ P.X} (h : Intertwines s t g) : Intertwines t s g⁻¹ := by
  intro Y f x
  rw [GrpObj.comp_inv]
  calc
    (f ≫ g)⁻¹ * (x ≫ underlying t) =
        (f ≫ g)⁻¹ * ((x ≫ underlying t) * (f ≫ g)) * (f ≫ g)⁻¹ := by group
    _ = (x ≫ underlying s) * (f ≫ g)⁻¹ := by rw [← h Y f x]; group

private theorem intertwines_mul {r s t : C ⟶ P} {X : SchemeOver k}
    {g h : X ⟶ P.X} (hg : Intertwines r s g) (hh : Intertwines s t h) :
    Intertwines r t (h * g) := by
  intro Y f x
  simp only [MonObj.comp_mul]
  rw [mul_assoc, hg Y f x, ← mul_assoc (f ≫ h), hh Y f x, mul_assoc]

private theorem intertwines_post {s t : C ⟶ P} {X : SchemeOver k}
    {g : X ⟶ P.X} (h : Intertwines s t g) (j : P ⟶ H) :
    Intertwines (s ≫ j) (t ≫ j) (g ≫ underlying j) := by
  intro Y f x
  simpa only [underlying_comp, MonObj.mul_comp, Category.assoc] using
    congrArg (fun a ↦ a ≫ underlying j) (h Y f x)

private theorem intertwines_pre {s t : C ⟶ P} {X : SchemeOver k}
    {g : X ⟶ P.X} (h : Intertwines s t g) (j : H ⟶ C) :
    Intertwines (j ≫ s) (j ≫ t) g := by
  intro Y f x
  simpa only [underlying_comp, Category.assoc] using h Y f (x ≫ underlying j)

private theorem intertwines_self_centralizes {s : C ⟶ P} {X : SchemeOver k}
    {g : X ⟶ P.X} :
    Intertwines s s g ↔ Centralizes s g := by
  rw [intertwines_iff, Centralizes, conjugateFamily]
  exact mul_inv_eq_iff_eq_mul.symm

private theorem detects_through_section {q : P ⟶ C} {N₀ : ClosedSubgroup P}
    (hN : IsSchemeKernel q N₀) {s t : C ⟶ P} (hs : s ≫ q = 𝟙 _)
    {L L' : ClosedSubgroup P}
    [IsIso (L.inclusion ≫ q)] [IsIso (L'.inclusion ≫ q)]
    (hsdef : s = inv (L.inclusion ≫ q) ≫ L.inclusion)
    (htdef : t = inv (L'.inclusion ≫ q) ≫ L'.inclusion)
    {X : SchemeOver k} (g : X ⟶ N₀.group.X) :
    Transports L L' (g ≫ underlying N₀.inclusion) ↔
      Intertwines s t (g ≫ underlying N₀.inclusion) := by
  let a := g ≫ underlying N₀.inclusion
  let e := asIso (L.inclusion ≫ q)
  let e' := asIso (L'.inclusion ≫ q)
  change s = e.inv ≫ L.inclusion at hsdef
  change t = e'.inv ≫ L'.inclusion at htdef
  have eq (Y : SchemeOver k) (f : Y ⟶ X) : (f ≫ a) ≫ underlying q = 1 := by
    simp only [a, Category.assoc, hN.w, comp_toUnit_assoc, Hom.one_def]
  have eqs (Y : SchemeOver k) (x : Y ⟶ C.X) :
      (x ≫ underlying s) ≫ underlying q = x := by
    simpa only [underlying_comp, underlying_id, Category.assoc, Category.comp_id] using
      congrArg (fun z : C ⟶ C ↦ x ≫ underlying z) hs
  have forward : (∃ f : L.group.X ⊗ X ⟶ L'.group.X,
      f ≫ underlying L'.inclusion = conjugateFamily L.inclusion a) → Intertwines s t a := by
    rintro ⟨z, hz⟩ Y f x
    let l := lift (x ≫ underlying e.inv) f
    have hc : (l ≫ z) ≫ underlying L'.inclusion =
        (f ≫ a) * (x ≫ underlying s) * (f ≫ a)⁻¹ := by
      simpa only [Category.assoc, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
        lift_fst_assoc, lift_snd_assoc, l, hsdef, underlying_comp] using congrArg (fun v ↦ l ≫ v) hz
    have hp : (l ≫ z) ≫ underlying e'.hom = x := by
      change ((l ≫ z) ≫ underlying L'.inclusion) ≫ underlying q = x
      rw [hc, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, eq Y f, eqs, inv_one,
        one_mul, mul_one]
    have hz' : l ≫ z = x ≫ underlying e'.inv := by
      have hh := congrArg (fun v ↦ v ≫ underlying e'.inv) hp
      simpa only [Category.assoc, ← show underlying (e'.hom ≫ e'.inv) =
        underlying e'.hom ≫ underlying e'.inv from rfl, e'.hom_inv_id, underlying_id,
        Category.comp_id] using hh
    rw [hz', Category.assoc, ← show underlying (e'.inv ≫ L'.inclusion) =
      underlying e'.inv ≫ underlying L'.inclusion from rfl, ← htdef] at hc
    exact mul_inv_eq_iff_eq_mul.mp hc.symm
  have backward : Intertwines s t a → ∃ f : L.group.X ⊗ X ⟶ L'.group.X,
      f ≫ underlying L'.inclusion = conjugateFamily L.inclusion a := by
    intro h
    have hls : e.hom ≫ s = L.inclusion := by
      rw [hsdef, e.hom_inv_id_assoc]
    let x := fst L.group.X X ≫ underlying e.hom
    refine ⟨x ≫ underlying e'.inv, ?_⟩
    have he := h _ (snd _ _) x
    have hx : x ≫ underlying s = fst L.group.X X ≫ underlying L.inclusion := by
      simpa only [x, Category.assoc, underlying_comp] using
        congrArg (fun z : L.group ⟶ P ↦ fst L.group.X X ≫ underlying z) hls
    rw [hx] at he
    change x ≫ underlying e'.inv ≫ underlying L'.inclusion = _
    rw [← show underlying (e'.inv ≫ L'.inclusion) =
      underlying e'.inv ≫ underlying L'.inclusion from rfl, ← htdef]
    rw [conjugateFamily, he, mul_inv_cancel_right]
  refine ⟨fun h ↦ forward h.1, fun h ↦ ⟨backward h, ?_⟩⟩
  have hi := intertwines_inv h
  have hls : e'.hom ≫ t = L'.inclusion := by
    rw [htdef, e'.hom_inv_id_assoc]
  let x := fst L'.group.X X ≫ underlying e'.hom
  refine ⟨x ≫ underlying e.inv, ?_⟩
  have he := hi _ (snd _ _) x
  have hx : x ≫ underlying t = fst L'.group.X X ≫ underlying L'.inclusion := by
    simpa only [x, Category.assoc, underlying_comp] using
      congrArg (fun z : L'.group ⟶ P ↦ fst L'.group.X X ≫ underlying z) hls
  rw [hx] at he
  change x ≫ underlying e.inv ≫ underlying L.inclusion = _
  rw [← show underlying (e.inv ≫ L.inclusion) =
    underlying e.inv ≫ underlying L.inclusion from rfl, ← hsdef]
  rw [conjugateFamily, he, mul_inv_cancel_right]

private theorem kernel_sections {q : P ⟶ C} {j : N ⟶ P}
    (h : IsPullback (underlying j) (toUnit _) (underlying q) η[C.X])
    {X : SchemeOver k} (x : X ⟶ P.X) :
    x ≫ underlying q = 1 ↔ ∃ n : X ⟶ N.X, n ≫ underlying j = x := by
  constructor
  · intro hx
    exact ⟨h.lift x (toUnit X) hx, h.lift_fst _ _ _⟩
  · rintro ⟨n, rfl⟩
    simp only [Category.assoc, h.w, comp_toUnit_assoc, Hom.one_def]

/-- A homomorphism killing the kernel of a split quotient factors through that quotient. -/
private theorem projections_factor {q : P ⟶ C} {p : P ⟶ H} {s : C ⟶ P}
    {j : N ⟶ P}
    (hq : IsPullback (underlying j) (toUnit _) (underlying q) η[C.X])
    (hp : underlying j ≫ underlying p = 1) (hs : s ≫ q = 𝟙 _) :
    q ≫ s ≫ p = p := by
  apply Grp.hom_ext
  have hs' : underlying s ≫ underlying q = 𝟙 C.X :=
    congrArg (fun f : C ⟶ C ↦ underlying f) hs
  let x : P.X ⟶ P.X := 𝟙 P.X * (underlying q ≫ underlying s)⁻¹
  have hx : x ≫ underlying q = 1 := by
    simp only [x, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc,
      hs', Category.comp_id, mul_inv_cancel]
  obtain ⟨y, hy⟩ := (kernel_sections hq x).mp hx
  have he : x ≫ underlying p = 1 := by rw [← hy, Category.assoc, hp, MonObj.comp_one]
  change underlying q ≫ underlying s ≫ underlying p = underlying p
  apply Eq.symm
  apply mul_inv_eq_one.mp
  simpa only [x, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc] using he

private def twist (s t : H ⟶ P) : H.X ⊗ P.X ⟶ P.X :=
  (fst H.X P.X ≫ underlying t) * snd H.X P.X * (fst H.X P.X ≫ underlying s)⁻¹

private theorem fixed_twist_iff (s t : H ⟶ P) {X : SchemeOver k} (a : X ⟶ P.X) :
    IsFixedBy (twist s t) a ↔ Intertwines s t a := by
  rw [IsFixedBy, intertwines_iff]
  simp only [twist, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst_assoc, whiskerLeft_snd]
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem baseChange_twist (K : Type u) [Field K] [Algebra k K]
    (s t : H ⟶ P) :
    baseChangeAction K (twist s t) =
      twist ((groupBaseChange k K).map s) ((groupBaseChange k K).map t) := by
  let F := baseChange k K
  change (prodComparisonIso F H.X P.X).inv ≫ F.map (twist s t) = _
  let e := prodComparisonIso F H.X P.X
  have h₁ : e.inv ≫ F.map (fst H.X P.X) = fst _ _ := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (CartesianMonoidalCategory.prodComparison_fst F H.X P.X).symm
  have h₂ : e.inv ≫ F.map (snd H.X P.X) = snd _ _ := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (CartesianMonoidalCategory.prodComparison_snd F H.X P.X).symm
  change e.inv ≫ F.map (twist s t) = _
  simp only [twist, Functor.map_mul, Functor.map_inv', Functor.map_comp, MonObj.comp_mul,
    GrpObj.comp_inv, reassoc_of% h₁, h₂]
  rfl

private theorem intertwines_trivial {q : P ⟶ C} {s : C ⟶ P} {J : GroupScheme k} {j : J ⟶ P}
    (hs : s ≫ q = 𝟙 _) {c : H ⟶ C} {i : P ⟶ N} [Mono (underlying i)]
    (hc : ∀ (X : SchemeOver k) (g : X ⟶ N.X),
      Centralizes (c ≫ s ≫ i) g ↔
        ∃ x : X ⟶ C.X, x ≫ underlying (s ≫ i) = g)
    (hj : underlying j ≫ underlying q = 1)
    {X : SchemeOver k} (g : X ⟶ J.X)
    (h : Intertwines (c ≫ s) (c ≫ s) (g ≫ underlying j)) :
    g ≫ underlying j = 1 := by
  have hcomm := intertwines_post h i
  rw [Category.assoc] at hcomm
  have hcent := (intertwines_self_centralizes.mp hcomm)
  obtain ⟨x, hx⟩ := (hc _ _).mp hcent
  change (x ≫ underlying s) ≫ underlying i = (g ≫ underlying j) ≫ underlying i at hx
  have he := (cancel_mono (underlying i)).mp hx
  have hxq := congrArg (· ≫ underlying q) he
  have hsq : underlying s ≫ underlying q = 𝟙 C.X :=
    congrArg (fun f : C ⟶ C ↦ underlying f) hs
  simp only [Category.assoc, hsq, Category.comp_id, hj, MonObj.comp_one] at hxq
  rw [← he, hxq, MonObj.one_comp]

private theorem intertwines_unique {q : P ⟶ C} {s : C ⟶ P}
    {J : GroupScheme k} {j : J ⟶ P}
    (hs : s ≫ q = 𝟙 _) {c : H ⟶ C} {i : P ⟶ N} [Mono (underlying i)]
    (hc : ∀ (X : SchemeOver k) (g : X ⟶ N.X),
      Centralizes (c ≫ s ≫ i) g ↔
        ∃ x : X ⟶ C.X, x ≫ underlying (s ≫ i) = g)
    (hj : underlying j ≫ underlying q = 1) [Mono (underlying j)]
    {t : H ⟶ P} {X : SchemeOver k} {g g' : X ⟶ J.X}
    (h : Intertwines (c ≫ s) t (g ≫ underlying j))
    (h' : Intertwines (c ≫ s) t (g' ≫ underlying j)) : g = g' := by
  have hh := intertwines_mul h (intertwines_inv h')
  have he : Intertwines (c ≫ s) (c ≫ s) ((g'⁻¹ * g) ≫ underlying j) := by
    simpa only [MonObj.mul_comp, GrpObj.inv_comp] using hh
  have he' := intertwines_trivial hs hc hj _ he
  apply (cancel_mono (underlying j)).mp
  apply Eq.symm
  apply inv_mul_eq_one.mp
  simpa only [MonObj.mul_comp, GrpObj.inv_comp] using he'

open private centralizes_iff fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers
open private isFixedBy_baseChange_iff whiskerLeft_pullback
  from LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem intertwines_of_cocharacter {q : P ⟶ C} {s t : C ⟶ P}
    {J : GroupScheme k} {j : J ⟶ P}
    (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _) {c : H ⟶ C} {i : P ⟶ N}
    [Mono (underlying i)]
    (hc : ∀ (X : SchemeOver k) (g : X ⟶ N.X),
      Centralizes (c ≫ s ≫ i) g ↔
        ∃ x : X ⟶ C.X, x ≫ underlying (s ≫ i) = g)
    (hj : underlying j ≫ underlying q = 1)
    {X : SchemeOver k} (g : X ⟶ J.X)
    (hg : Intertwines (c ≫ s) (c ≫ t) (g ≫ underlying j)) :
    Intertwines s t (g ≫ underlying j) := by
  have hsq : underlying s ≫ underlying q = 𝟙 C.X :=
    congrArg (fun f : C ⟶ C ↦ underlying f) hs
  have htq : underlying t ≫ underlying q = 𝟙 C.X :=
    congrArg (fun f : C ⟶ C ↦ underlying f) ht
  have hC {Y : SchemeOver k} (y : Y ⟶ C.X) (a : Y ⟶ H.X) :
      Commute y (a ≫ underlying c) := by
    have he := (centralizes_iff (c ≫ s ≫ i) _).mp
      ((hc Y (y ≫ underlying (s ≫ i))).mpr ⟨y, rfl⟩) Y (𝟙 Y) a
    change y * (a ≫ underlying c) = (a ≫ underlying c) * y
    have hsmono : IsSplitMono (underlying s) := IsSplitMono.mk' ⟨underlying q, hsq⟩
    apply (cancel_mono (underlying s ≫ underlying i)).mp
    simpa only [Commute, SemiconjBy, underlying_comp, Category.assoc, Category.id_comp,
      MonObj.mul_comp] using he
  intro Y f x
  let u : Y ⟶ P.X := f ≫ g ≫ underlying j
  let z := u⁻¹ * (x ≫ underlying t) * u
  have hz : Centralizes (c ≫ s ≫ i) (z ≫ underlying i) := by
    apply (centralizes_iff _ _).mpr
    intro W b a
    let v := b ≫ u
    let y := b ≫ x ≫ underlying t
    let cs := a ≫ underlying c ≫ underlying s
    let ct := a ≫ underlying c ≫ underlying t
    have h₁ : v * cs = ct * v := by
      simpa only [v, u, cs, ct, Category.assoc, underlying_comp] using hg W (b ≫ f) a
    have h₂ : v⁻¹ * ct = cs * v⁻¹ := by
      simpa only [v, u, cs, ct, Category.assoc, underlying_comp, GrpObj.comp_inv] using
        intertwines_inv hg W (b ≫ f) a
    have h₃ : Commute y ct := by
      have hh := (hC (b ≫ x) a).map (IsMonHom.monoidHom (underlying t) W)
      change Commute ((b ≫ x) ≫ underlying t) ((a ≫ underlying c) ≫ underlying t) at hh
      simpa only [y, ct, Category.assoc] using hh
    have h₄ : Commute (v⁻¹ * y * v) cs := by
      change (v⁻¹ * y * v) * cs = cs * (v⁻¹ * y * v)
      calc
        _ = v⁻¹ * y * (v * cs) := mul_assoc _ _ _
        _ = (v⁻¹ * ct) * y * v := by
          rw [h₁]
          calc
            _ = v⁻¹ * (y * ct) * v := by group
            _ = _ := by rw [h₃.eq]; group
        _ = _ := by rw [h₂]; group
    have hh := h₄.map (IsMonHom.monoidHom (underlying i) W)
    change Commute ((v⁻¹ * y * v) ≫ underlying i) (cs ≫ underlying i) at hh
    change Commute (b ≫ z ≫ underlying i) (a ≫ underlying (c ≫ s ≫ i))
    have hz' : b ≫ z = v⁻¹ * y * v := by
      simp only [z, v, y, MonObj.comp_mul, GrpObj.comp_inv]
    rw [← Category.assoc b z, hz']
    simpa only [cs, Category.assoc, underlying_comp] using hh
  obtain ⟨x', hx'⟩ := (hc Y (z ≫ underlying i)).mp hz
  have he : x' ≫ underlying s = z := by
    apply (cancel_mono (underlying i)).mp
    simpa only [Category.assoc, underlying_comp] using hx'
  have hu : u ≫ underlying q = 1 := by
    simp only [u, Category.assoc, hj, MonObj.comp_one]
  have hx : x' = x := by
    have eq := congrArg (fun m ↦ m ≫ underlying q) he
    simpa only [Category.assoc, hsq, Category.comp_id, z, MonObj.mul_comp, GrpObj.inv_comp,
      hu, htq, inv_one, one_mul, mul_one] using eq
  change u * (x ≫ underlying s) = (x ≫ underlying t) * u
  rw [← hx, he, hx]
  dsimp [z]
  group

/-- Uniqueness on all test schemes gives the compatibility needed for faithfully flat descent. -/
private theorem descend_intertwiner (K : Type u) [Field K] [Algebra k K]
    (s t : H ⟶ P) {J : GroupScheme k} (j : J ⟶ P)
    (hunique : ∀ (X : SchemeOver k) (g g' : X ⟶ J.X),
      Intertwines s t (g ≫ underlying j) →
      Intertwines s t (g' ≫ underlying j) → g = g')
    (g : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj J).X)
    (hg : Intertwines ((groupBaseChange k K).map s) ((groupBaseChange k K).map t)
      (g ≫ underlying ((groupBaseChange k K).map j))) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ J.X, Intertwines s t (a ≫ underlying j) := by
  let b := fieldSpecMap k K
  let F := Over.map b
  let A := Over.mapPullbackAdj b
  let V := F.obj (𝟙_ (SchemeOver K))
  let v : V ⟶ 𝟙_ (SchemeOver k) := toUnit V
  let z : V ⟶ J.X := (A.homEquiv _ J.X).symm g
  have hfix := (fixed_twist_iff _ _ _).mpr hg
  rw [← baseChange_twist] at hfix
  have hz := (isFixedBy_baseChange_iff K _ _ _).mp hfix
  change IsFixedBy (twist s t)
    ((A.homEquiv (𝟙_ (SchemeOver K)) P.X).symm (g ≫ (baseChange k K).map (underlying j))) at hz
  rw [A.homEquiv_naturality_right_symm] at hz
  have hz' : Intertwines s t (z ≫ underlying j) := (fixed_twist_iff _ _ _).mp hz
  have hv : v.left = b := rfl
  letI : Surjective b := fieldSpecMap_surjective K
  letI : Flat b := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [Flat.SpecMap_iff]
    let : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  letI : QuasiCompact b := inferInstanceAs (QuasiCompact (Spec.map _))
  have hvEpi : EffectiveEpi v.left := hv ▸ (inferInstance : EffectiveEpi b)
  have compatible {Y : Scheme.{u}} (f f' : Y ⟶ V.left) (hf : f ≫ v.left = f' ≫ v.left) :
      f ≫ z.left = f' ≫ z.left := by
    let Y' : SchemeOver k := Over.mk (f ≫ V.hom)
    let r : Y' ⟶ V := Over.homMk f rfl
    let r' : Y' ⟶ V := Over.homMk f' (by change f' ≫ v.left = f ≫ v.left; exact hf.symm)
    have eq := hunique Y' (r ≫ z) (r' ≫ z)
      (by simpa only [Category.assoc] using intertwines_pullback hz' r)
      (by simpa only [Category.assoc] using intertwines_pullback hz' r')
    exact congrArg (fun m : Y' ⟶ J.X ↦ m.left) eq
  let a' := EffectiveEpi.desc v.left z.left compatible
  have ha' : v.left ≫ a' = z.left := EffectiveEpi.fac v.left z.left compatible
  have ha'' : a' ≫ J.X.hom = 𝟙 _ := by
    apply (cancel_epi v.left).mp
    rw [← Category.assoc, ha', Category.comp_id]
    exact Over.w z
  let a : 𝟙_ (SchemeOver k) ⟶ J.X := Over.homMk a' ha''
  have ha : v ≫ a = z := Over.OverMorphism.ext ha'
  refine ⟨a, (fixed_twist_iff _ _ _).mp ?_⟩
  have hp := (Over.forget (Spec (CommRingCat.of k))).map_isPullback (whiskerLeft_pullback (H := H.X) v)
  have hvS : Surjective v.left := hv ▸ (inferInstance : Surjective b)
  have hvF : Flat v.left := hv ▸ (inferInstance : Flat b)
  have hvQ : QuasiCompact v.left := hv ▸ (inferInstance : QuasiCompact b)
  haveI : Surjective (H.X ◁ v).left := MorphismProperty.of_isPullback hp.flip hvS
  haveI : Flat (H.X ◁ v).left := MorphismProperty.of_isPullback hp.flip hvF
  haveI : QuasiCompact (H.X ◁ v).left := MorphismProperty.of_isPullback hp.flip hvQ
  haveI : Epi (H.X ◁ v) :=
    (Over.forget _).epi_of_epi_map (f := H.X ◁ v) (inferInstanceAs (Epi (H.X ◁ v).left))
  unfold IsFixedBy
  apply (cancel_epi (H.X ◁ v)).mp
  rw [← Category.assoc, ← whiskerLeft_comp, ← Category.assoc, ha, whiskerLeft_snd_assoc]
  simpa only [IsFixedBy, Category.assoc, reassoc_of% ha] using (fixed_twist_iff _ _ _).mpr hz'

open private baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components

private theorem flat_split_projection {q : P ⟶ C} {s : C ⟶ P} {j : N ⟶ P}
    (hs : s ≫ q = 𝟙 _) (hN : Flat N.X.hom)
    (h : IsPullback (underlying j) (toUnit _) (underlying q) η[C.X])
    (hm : IsIso (multiplyFactors s j)) :
    Flat (underlying q).left := by
  let m := multiplyFactors s j
  letI : IsIso m := hm
  letI : IsIso m.left := (Over.forget _).map_isIso m
  have he : m ≫ underlying q = fst C.X N.X := by
    have hs' : underlying s ≫ underlying q = 𝟙 C.X :=
      congrArg (fun z : C ⟶ C ↦ underlying z) hs
    have hj : underlying j ≫ underlying q = (1 : N.X ⟶ C.X) := h.w
    simp only [m, multiplyFactors, MonObj.mul_comp, Category.assoc, hs', hj, Category.comp_id,
      MonObj.comp_one, mul_one]
  have hf : Flat (fst C.X N.X).left := by
    have pb := (Over.forget (Spec (CommRingCat.of k))).map_isPullback
      (whiskerLeft_pullback (H := C.X) (toUnit N.X))
    have hunit : Flat (toUnit N.X).left := hN
    have H : Flat (C.X ◁ toUnit N.X).left := MorphismProperty.of_isPullback pb.flip hunit
    have eq : (C.X ◁ toUnit N.X) ≫ fst C.X (𝟙_ (SchemeOver k)) = fst C.X N.X :=
      whiskerLeft_fst _ _
    have hunitor : fst C.X (𝟙_ (SchemeOver k)) = (ρ_ C.X).hom := by simp [fst_def]
    letI : IsIso (fst C.X (𝟙_ (SchemeOver k))) := by rw [hunitor]; infer_instance
    letI : IsIso (fst C.X (𝟙_ (SchemeOver k))).left :=
      (Over.forget _).map_isIso (fst C.X (𝟙_ (SchemeOver k)))
    rw [← eq]
    exact Flat.comp _ _
  have hq : (underlying q).left = (inv m ≫ fst C.X N.X).left := by
    rw [← he, IsIso.inv_hom_id_assoc]
  rw [hq]
  exact Flat.comp _ _

/-- Pull back the quotient and its two sections along the given map from a split torus. -/
private theorem exists_intertwining_over_split_torus [PerfectField k]
    (A B T : AffineAlgebraicGroup k) (q : A.val ⟶ B.val)
    (U : ClosedSubgroup A.val) (hU : IsSchemeKernel q U)
    (hq : Flat (underlying q).left)
    (hsU : Smooth U.group.X.hom) (hcU : ConnectedSpace U.group.X.left)
    (hu : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup U))
    (hT : Specs.EquivariantUnipotentSeries.IsSplitTorus T.val)
    (c : T.val ⟶ B.val) (s t : B.val ⟶ A.val) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
      Intertwines (c ≫ s) (c ≫ t) (a ≫ underlying U.inclusion) := by
  let E := pullback q c
  let l : E ⟶ A.val := pullback.fst q c
  let r : E ⟶ T.val := pullback.snd q c
  let hol := Grp.forget (SchemeOver k)
  have pb : IsPullback (underlying l) (underlying r) (underlying q) (underlying c) :=
    (IsPullback.of_hasPullback q c).map hol
  have pb' := pb.map (Over.forget (Spec (CommRingCat.of k)))
  let D : AffineAlgebraicGroup k := ⟨E, affineAlgebraicPullback k A B T q c⟩
  have hfn : U.inclusion ≫ q = (0 : U.group ⟶ B.val) := by
    apply Grp.hom_ext
    exact hU.w
  let i : U.group ⟶ E := pullback.lift U.inclusion 0 (by rw [hfn, zero_comp])
  have hi : i ≫ l = U.inclusion := pullback.lift_fst _ _ _
  have hir : i ≫ r = 0 := pullback.lift_snd _ _ _
  have his : underlying i ≫ underlying l = underlying U.inclusion :=
    congrArg (fun z : U.group ⟶ A.val ↦ underlying z) hi
  have hrs : underlying i ≫ underlying r = toUnit _ ≫ η[T.val.X] :=
    congrArg (fun z : U.group ⟶ T.val ↦ underlying z) hir
  have htunit : η[T.val.X] ≫ underlying c = η[B.val.X] := IsMonHom.one_hom _
  have hp : IsPullback (underlying i) (toUnit _) (underlying r) η[T.val.X] := by
    apply IsPullback.of_right (v₁₃ := underlying q) (h₁₂ := underlying l)
      (h₂₂ := underlying c) _ hrs pb
    rwa [his, htunit]
  let U' : ClosedSubgroup D.val :=
    ⟨U.group, i, MorphismProperty.of_isPullback
      (hp.map (Over.forget (Spec (CommRingCat.of k)))).flip
      (isClosedImmersion_of_comp_eq_id T.val.X.hom η[T.val.X].left (Over.w η[T.val.X]))⟩
  let liftSection (v : B.val ⟶ A.val) (hv : v ≫ q = 𝟙 _) : T.val ⟶ E :=
    pullback.lift (c ≫ v) (𝟙 _) (by rw [Category.assoc, hv, Category.comp_id, Category.id_comp])
  have hsection (v : B.val ⟶ A.val) (hv : v ≫ q = 𝟙 _) : liftSection v hv ≫ r = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hsurj : Surjective (underlying r).left := by
    have h : (underlying (liftSection s hs)).left ≫ (underlying r).left = 𝟙 _ :=
      congrArg (fun z : T.val ⟶ T.val ↦ (underlying z).left) (hsection s hs)
    exact ⟨fun x ↦ ⟨(underlying (liftSection s hs)).left x,
      congrArg (fun f : T.val.X.left ⟶ T.val.X.left ↦ f x) h⟩⟩
  obtain ⟨a, ha⟩ := (TorusSections.splitTorusExtension D T U' r hp
    (MorphismProperty.of_isPullback pb' hq) hsurj hT hsU hcU hu).2
    _ _ (hsection s hs) (hsection t ht)
  have hs' : liftSection s hs ≫ l = c ≫ s := pullback.lift_fst _ _ _
  have ht' : liftSection t ht ≫ l = c ≫ t := pullback.lift_fst _ _ _
  have eq := congrArg (fun f : T.val.X ⟶ E.X ↦ f ≫ underlying l) ha
  change underlying (liftSection t ht) ≫ underlying l =
    (toUnit _ ≫ a ≫ underlying i * underlying (liftSection s hs) *
      (toUnit _ ≫ a ≫ underlying i)⁻¹) ≫ underlying l at eq
  simp only [MonObj.mul_comp, GrpObj.inv_comp, ← underlying_comp, ht', hs',
    Category.assoc, his] at eq
  refine ⟨a, fun Y f x ↦ ?_⟩
  have hx := congrArg (fun v : T.val.X ⟶ A.val.X ↦ x ≫ v) eq
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc] at hx
  have hf : f = toUnit Y := toUnit_unique f (toUnit Y)
  rw [hf]
  change (toUnit Y ≫ (a ≫ underlying U.inclusion)) * (x ≫ underlying (c ≫ s)) =
    (x ≫ underlying (c ≫ t)) * (toUnit Y ≫ (a ≫ underlying U.inclusion))
  exact mul_inv_eq_iff_eq_mul.mp hx.symm

open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient

open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.GeometricRadicals (IsUnipotentRadical baseChangedSubgroup)
open Specs.StandardParabolicLevi (IsContractingRadical)
open Specs.Unipotent (baseChangedAlgebraicGroup)

private theorem multiplicative_group_iso :
    Nonempty (specGroup (groupAlgebra k IntegerCharacters) ≅
      (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 1))).val) := by
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) 1
  let a : Specs.CharacterDescent.StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) IntegerCharacters
  exact ⟨(hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k a)).op ≪≫ e⟩

private theorem cocharacter_factors_through_centralizer {G : GroupScheme k}
    {c : Cocharacter G} (D : LimitDecomposition c) :
    ∃ d : Cocharacter D.centralizer.group, d ≫ D.centralizer.inclusion = c := by
  have hz : Centralizes c (underlying c) := by
    apply (centralizes_iff c _).mpr
    intro Y a b
    exact (show Commute a b from mul_comm _ _).map (IsMonHom.monoidHom (underlying c) Y)
  obtain ⟨x, hx⟩ := (D.centralizer_points _ _).mp hz
  letI := D.centralizer.isClosedImmersion
  letI := isMonHom_of_comp_closed x c D.centralizer.inclusion hx
  exact ⟨Grp.homMk x, Grp.hom_ext _ _ hx⟩

/-- Pulling a section back along the central cocharacter suffices to construct
a conjugator. The scheme centralizer then determines the section on the entire Levi. -/
private theorem conjugate_to_limit_section {G : AffineAlgebraicGroup k} {c : Cocharacter G.val}
    (D : LimitDecomposition c) (hD : IsContractingRadical D)
    (t : D.centralizer.group ⟶ D.parabolic.group) (ht : t ≫ D.limit = 𝟙 _) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ D.contracting.group.X,
      Intertwines D.sectionMap t (a ≫ underlying D.contractingToParabolic) := by
  let U := contractingSubgroup D
  let P := closedSubgroupAlgebraicGroup D.parabolic
  let C := closedSubgroupAlgebraicGroup D.centralizer
  let s := D.sectionMap
  let q := D.limit
  let j := D.contractingToParabolic
  have hker : IsSchemeKernel q U := D.isKernel
  letI : Mono (underlying j) := closed_mono U
  letI : Mono (underlying D.parabolic.inclusion) := closed_mono D.parabolic
  obtain ⟨d, hd⟩ := cocharacter_factors_through_centralizer D
  have he : d ≫ s ≫ D.parabolic.inclusion = c := by
    rw [show s ≫ D.parabolic.inclusion = D.centralizer.inclusion from D.section_in_G, hd]
  have hcent (X : SchemeOver k) (g : X ⟶ G.val.X) :
      Centralizes (d ≫ s ≫ D.parabolic.inclusion) g ↔
        ∃ x : X ⟶ C.val.X, x ≫ underlying (s ≫ D.parabolic.inclusion) = g := by
    rw [he, show s ≫ D.parabolic.inclusion = D.centralizer.inclusion from D.section_in_G]
    exact D.centralizer_points X g
  have hj : underlying j ≫ underlying q = (1 : D.contracting.group.X ⟶ C.val.X) := hker.w
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let P' := baseChangedAlgebraicGroup K P
  let C' := baseChangedAlgebraicGroup K C
  obtain ⟨hclosed, hUK⟩ := hD.2
  let U' := baseChangedSubgroup K U hclosed
  have hU' : IsSchemeKernel (F.map q) U' := baseChangeKernelSquare q j hker
  have hf : Flat (underlying q).left := flat_split_projection D.section_limit
    (by letI := hD.1.1.1; infer_instance) hker D.product_iso
  have hf' : Flat (underlying (F.map q)).left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) (underlying q)).flip hf
  let T := Specs.StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin 1))
  obtain ⟨eT⟩ := multiplicative_group_iso (k := K)
  let m : extendedHopf K (groupAlgebra k IntegerCharacters.{u}) ≅
      groupAlgebra K IntegerCharacters.{u} :=
    CommHopfAlgCat.isoMk
      (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K IntegerCharacters)
  let e : T.val ≅ F.obj (specGroup (groupAlgebra k IntegerCharacters)) :=
    eT.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso m.op ≪≫ extendedGroupIso K _
  have hs' : F.map s ≫ F.map q = 𝟙 (F.obj C.val) := by
    exact ((F.map_comp s q).symm.trans (F.congr_map D.section_limit)).trans (F.map_id _)
  have ht' : F.map t ≫ F.map q = 𝟙 (F.obj C.val) := by
    exact ((F.map_comp t q).symm.trans (F.congr_map ht)).trans (F.map_id _)
  obtain ⟨a, ha⟩ := exists_intertwining_over_split_torus P' C' T
    (F.map q) U' hU' hf' hUK.1.1 hUK.1.2.1 hUK.2.1 ⟨1, ⟨Iso.refl _⟩⟩
    (e.hom ≫ F.map d) (F.map s) (F.map t) hs' ht'
  have ha' := intertwines_pre ha e.inv
  simp only [Iso.inv_hom_id_assoc, Category.assoc, ← F.map_comp] at ha'
  obtain ⟨a₀, ha₀⟩ := descend_intertwiner K (d ≫ s) (d ≫ t) j
    (fun X x y hx hy ↦ intertwines_unique D.section_limit hcent hj hx hy) a ha'
  exact ⟨a₀, intertwines_of_cocharacter D.section_limit ht hcent hj a₀ ha₀⟩

private theorem limit_sections_transporter {G : AffineAlgebraicGroup k}
    {c : Cocharacter G.val} (D : LimitDecomposition c) (hD : IsContractingRadical D)
    (s t : D.centralizer.group ⟶ D.parabolic.group)
    (hs : s ≫ D.limit = 𝟙 _) (ht : t ≫ D.limit = 𝟙 _) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ D.contracting.group.X,
      ∀ (X : SchemeOver k) (g : X ⟶ D.contracting.group.X),
        Intertwines s t (g ≫ underlying D.contractingToParabolic) ↔ g = toUnit X ≫ a := by
  let j := D.contractingToParabolic
  obtain ⟨a, ha⟩ := conjugate_to_limit_section D hD s hs
  obtain ⟨b, hb⟩ := conjugate_to_limit_section D hD t ht
  letI : Mono (underlying j) := closed_mono (contractingSubgroup D)
  letI : Mono (underlying D.parabolic.inclusion) := closed_mono D.parabolic
  obtain ⟨d, hd⟩ := cocharacter_factors_through_centralizer D
  have hc (X : SchemeOver k) (g : X ⟶ G.val.X) :
      Centralizes (d ≫ D.sectionMap ≫ D.parabolic.inclusion) g ↔
        ∃ x : X ⟶ D.centralizer.group.X,
          x ≫ underlying (D.sectionMap ≫ D.parabolic.inclusion) = g := by
    rw [D.section_in_G, hd]
    exact D.centralizer_points X g
  have hj : underlying j ≫ underlying D.limit =
      (1 : D.contracting.group.X ⟶ D.centralizer.group.X) := D.isKernel.w
  refine ⟨b * a⁻¹, fun X g ↦ ⟨?_, ?_⟩⟩
  · intro hg
    have hga : Intertwines D.sectionMap t ((g * (toUnit X ≫ a)) ≫ underlying j) := by
      simpa only [MonObj.mul_comp, Category.assoc] using
        intertwines_mul (intertwines_pullback ha (toUnit X)) hg
    have hbX : Intertwines D.sectionMap t ((toUnit X ≫ b) ≫ underlying j) := by
      simpa only [Category.assoc] using intertwines_pullback hb (toUnit X)
    have he := intertwines_unique D.section_limit hc hj
      (intertwines_pre hga d) (intertwines_pre hbX d)
    simpa only [MonObj.comp_mul, GrpObj.comp_inv] using
      (eq_mul_inv_iff_mul_eq.mpr he : g = (toUnit X ≫ b) * (toUnit X ≫ a)⁻¹)
  · intro hg
    rw [hg, Category.assoc, MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv]
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using
      intertwines_pullback (intertwines_mul (intertwines_inv ha) hb) (toUnit X)

open private normalSubgroup_of_iso from LinearAlgebraicGroups.Flag.NormalAffineQuotient

private def pushSubgroup (S : ClosedSubgroup P) (e : P ≅ C) : ClosedSubgroup C := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  letI : IsIso (underlying e.hom).left := F.map_isIso e.hom
  letI := S.isClosedImmersion
  exact ⟨S.group, S.inclusion ≫ e.hom, IsClosedImmersion.comp _ _⟩

private theorem pushRadical {A B : AffineAlgebraicGroup k}
    (e : A.val ≅ B.val) {S : ClosedSubgroup A.val} (h : IsUnipotentRadical A S) :
    IsUnipotentRadical B (pushSubgroup S e) := by
  have eq (J : ClosedSubgroup B.val) :
      (pushSubgroup J e.symm).inclusion ≫ e.hom = J.inclusion := by
    change (J.inclusion ≫ e.inv) ≫ e.hom = _
    simp
  refine ⟨⟨h.1.1, h.1.2.1, ?_⟩, h.2.1, ?_⟩
  · apply normalSubgroup_of_iso e.symm (Iso.refl S.group) _ h.1.2.2
    change (S.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ S.inclusion
    simp
  · intro J hnormal huni
    have hJ : Specs.GeometricRadicals.IsSmoothConnectedNormal (G := A) (pushSubgroup J e.symm) :=
      ⟨hnormal.1, hnormal.2.1, normalSubgroup_of_iso e (Iso.refl J.group)
        ((eq J).trans (Category.id_comp J.inclusion).symm) hnormal.2.2⟩
    obtain ⟨j, hj⟩ := h.2.2 (pushSubgroup J e.symm) hJ huni
    exact ⟨j, by
      change j ≫ S.inclusion ≫ e.hom = _
      rw [← Category.assoc, hj, eq]⟩

private theorem subgroup_iso {A B : ClosedSubgroup P}
    (h₁ : IsSubgroupOf A B) (h₂ : IsSubgroupOf B A) :
    ∃ e : A.group ≅ B.group, e.hom ≫ B.inclusion = A.inclusion := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  let F := Grp.forget (SchemeOver k)
  letI : Mono A.inclusion := F.mono_of_mono_map (closed_mono A)
  letI : Mono B.inclusion := F.mono_of_mono_map (closed_mono B)
  exact ⟨⟨f, g,
    (cancel_mono A.inclusion).mp (by rw [Category.assoc, hg, hf, Category.id_comp]),
    (cancel_mono B.inclusion).mp (by rw [Category.assoc, hf, hg, Category.id_comp])⟩, hf⟩

private theorem transported_kernel {q : C ⟶ H} {A : ClosedSubgroup P}
    {B : ClosedSubgroup C} (e : P ≅ C) (b : A.group ≅ B.group)
    (h : b.hom ≫ B.inclusion = A.inclusion ≫ e.hom) (hk : IsSchemeKernel q B) :
    IsSchemeKernel (e.hom ≫ q) A := by
  let F := Grp.forget (SchemeOver k)
  apply hk.of_iso' (F.mapIso b) (F.mapIso e) (Iso.refl _) (Iso.refl _)
  · exact congrArg F.map h
  · exact toUnit_unique _ _
  · change underlying e.hom ≫ underlying q = underlying (e.hom ≫ q) ≫ 𝟙 H.X
    rw [Category.comp_id]
    rfl
  · change 𝟙 (𝟙_ (SchemeOver k)) ≫ η[H.X] = η[H.X] ≫ 𝟙 H.X
    rw [Category.id_comp, Category.comp_id]

private theorem projection_iso {p : P ⟶ C} {q : P ⟶ H} {A : ClosedSubgroup P}
    (hp : IsSchemeKernel p A) (hq : IsSchemeKernel q A)
    {s : C ⟶ P} (hs : s ≫ p = 𝟙 _) {t : H ⟶ P} (ht : t ≫ q = 𝟙 _) :
    ∃ e : C ≅ H, p ≫ e.hom = q := by
  have h₁ := projections_factor hp hq.w hs
  have h₂ := projections_factor hq hp.w ht
  refine ⟨⟨s ≫ q, t ≫ p, ?_, ?_⟩, h₁⟩
  · rw [Category.assoc, h₂, hs]
  · rw [Category.assoc, h₁, ht]

private theorem intertwines_base_iso {s t : H ⟶ P} {A : ClosedSubgroup P} {B : ClosedSubgroup C}
    (e : P ≅ C) (b : A.group ≅ B.group)
    (h : b.hom ≫ B.inclusion = A.inclusion ≫ e.hom)
    {X : SchemeOver k} (g : X ⟶ A.group.X) :
    Intertwines s t (g ≫ underlying A.inclusion) ↔
      Intertwines (s ≫ e.hom) (t ≫ e.hom) ((g ≫ underlying b.hom) ≫ underlying B.inclusion) := by
  have he : (g ≫ underlying b.hom) ≫ underlying B.inclusion =
      (g ≫ underlying A.inclusion) ≫ underlying e.hom := by
    rw [Category.assoc, Category.assoc, ← underlying_comp, ← underlying_comp, h]
  rw [he]
  refine ⟨fun hg ↦ intertwines_post hg e.hom, ?_⟩
  intro hg
  have hj : underlying e.hom ≫ underlying e.inv = 𝟙 P.X :=
    (Grp.forget (SchemeOver k)).congr_map e.hom_inv_id
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, hj] using
    intertwines_post hg e.inv

/-- Under the rational cocharacter premises, the unique radical point conjugating two Levi
complements represents their transporter on every test scheme. -/
theorem leviConjugacy_conditional :
    Specs.RationalCocharacter.RationalParabolic.{u} →
    Specs.RationalCocharacter.RationalParabolicThroughTorus.{u} →
    Specs.LeviConjugacy.Statement.{u} := by
  intro rationalParabolic _ k _ G P hP U hU Q q hq L L' hL hL'
  obtain ⟨c, D, hD, _, hrad⟩ := rationalParabolic G P hP
  obtain ⟨e, _⟩ := subgroup_iso hD.1 hD.2
  let A := closedSubgroupAlgebraicGroup P
  let B := closedSubgroupAlgebraicGroup D.parabolic
  let U₀ := contractingSubgroup D
  let U₁ := pushSubgroup U₀ e.symm
  have hU₁ : IsUnipotentRadical A U₁ := pushRadical (A := B) (B := A) e.symm hrad.1
  obtain ⟨d, hd⟩ := subgroup_iso
    (hU₁.2.2 U hU.1 hU.2.1) (hU.2.2 U₁ hU₁.1 hU₁.2.1)
  have hd' : d.hom ≫ U₀.inclusion = U.inclusion ≫ e.hom := by
    rw [← hd]
    change d.hom ≫ U₀.inclusion = (d.hom ≫ U₀.inclusion ≫ e.inv) ≫ e.hom
    simp
  let p := e.hom ≫ D.limit
  have hp : IsSchemeKernel p U := transported_kernel e d hd' D.isKernel
  let s₀ := D.sectionMap ≫ e.inv
  have hs₀ : s₀ ≫ p = 𝟙 _ := by
    simp only [s₀, p, Category.assoc, Iso.inv_hom_id_assoc, D.section_limit]
  let sQ := inv (L.inclusion ≫ q) ≫ L.inclusion
  have hsQ : sQ ≫ q = 𝟙 _ := IsIso.inv_hom_id (L.inclusion ≫ q)
  obtain ⟨f, hf⟩ := projection_iso hp hq hs₀ hsQ
  have hqp : q ≫ f.inv = p := by
    rw [← hf, Category.assoc, f.hom_inv_id, Category.comp_id]
  letI : IsIso (L.inclusion ≫ p) := by
    rw [← hqp, ← Category.assoc]
    infer_instance
  letI : IsIso (L'.inclusion ≫ p) := by
    rw [← hqp, ← Category.assoc]
    infer_instance
  let s := inv (L.inclusion ≫ p) ≫ L.inclusion
  let t := inv (L'.inclusion ≫ p) ≫ L'.inclusion
  have hs : s ≫ p = 𝟙 _ := IsIso.inv_hom_id (L.inclusion ≫ p)
  have ht : t ≫ p = 𝟙 _ := IsIso.inv_hom_id (L'.inclusion ≫ p)
  have hse : (s ≫ e.hom) ≫ D.limit = 𝟙 _ := by rwa [Category.assoc]
  have hte : (t ≫ e.hom) ≫ D.limit = 𝟙 _ := by rwa [Category.assoc]
  obtain ⟨a, ha⟩ := limit_sections_transporter D hrad (s ≫ e.hom) (t ≫ e.hom) hse hte
  refine ⟨a ≫ underlying d.inv, fun X g ↦ ?_⟩
  rw [detects_through_section hp hs (s := s) (t := t) rfl rfl,
    intertwines_base_iso e d hd']
  change Intertwines (s ≫ e.hom) (t ≫ e.hom)
    ((g ≫ underlying d.hom) ≫ underlying D.contractingToParabolic) ↔ _
  rw [ha]
  let E := (Grp.forget (SchemeOver k)).mapIso d
  change g ≫ E.hom = toUnit X ≫ a ↔ g = toUnit X ≫ a ≫ E.inv
  have hAssoc : (toUnit X ≫ a) ≫ E.inv = toUnit X ≫ a ≫ E.inv :=
    Category.assoc _ _ _
  exact (E.eq_comp_inv (f := toUnit X ≫ a) (g := g)).symm.trans
    (iff_of_eq (congrArg (fun m : X ⟶ U.group.X ↦ g = m) hAssoc))

end

end LinearAlgebraicGroups.Relative.LeviConjugacy

universe v8_closure_1008dbef7dd7e3a0_u0
theorem _root_.«LinearAlgebraicGroups».«Relative».«LeviConjugacy».«leviConjugacy» : _root_.«LinearAlgebraicGroups».«Specs».«LeviConjugacy».«Statement».{v8_closure_1008dbef7dd7e3a0_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«LeviConjugacy».«leviConjugacy_conditional».{v8_closure_1008dbef7dd7e3a0_u0} (@_root_.«LinearAlgebraicGroups».«Relative».«RationalCocharacter».«rationalParabolic».{v8_closure_1008dbef7dd7e3a0_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«RationalCocharacter».«rationalParabolicThroughTorus».{v8_closure_1008dbef7dd7e3a0_u0})
