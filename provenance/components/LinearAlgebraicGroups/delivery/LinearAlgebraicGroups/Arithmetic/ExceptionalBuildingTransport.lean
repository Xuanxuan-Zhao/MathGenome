import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingTransport
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.GroupTheory.Subgroup.Centralizer

import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingTransport

open _root_.LinearAlgebraicGroups.Specs
open ExceptionalAffineBruhat ExceptionalAffineRootSystems ExceptionalBuildingTransport
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model integerAlgebra)

attribute [local instance] integerAlgebra
open AffineArrangement (Datum)

noncomputable section

section Walls

variable {V V' J J' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  {A : ApartmentRoots ℚ V J} {A' : ApartmentRoots ℚ V' J'} {p : V} {p' : V'}
  {e : V ≃ᵃ[ℚ] V'} (d : WallComparison A A' p p' e)

theorem affine_apply_add (f : V ≃ᵃ[ℚ] V') (x y : V) :
    f (x + y) = f.linear x + f y := f.map_vadd y x

theorem reflection_apply (A : ApartmentRoots ℚ V J) (a : J × ℤ) (x : V) :
    A.reflection a x = x - A.wallValue a x • A.coroot a.1 := by
  change (AffineEquiv.constVAdd ℚ V _ : V ≃ᵃ[ℚ] V) (A.linearReflection a.1 x) = _
  change (-a.2) • A.coroot a.1 + (x - A.root a.1 x • A.coroot a.1) = _
  simp only [Datum.value, add_smul, neg_smul, Int.cast_smul_eq_zsmul ℚ]
  abel

theorem isSimple_iff (a : J × ℤ) : A'.IsSimple p' (d.walls a) ↔ A.IsSimple p a := by
  constructor
  · rintro ⟨hp, y, hz, hother⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨(d.positive a).1 hp, x, (d.equation a x).symm.trans hz, ?_⟩
    intro b hb hne
    have h := hother (d.walls b) ((d.positive b).2 hb) (fun h => hne (d.walls.injective h))
    simpa only [Datum.positive, d.equation] using h
  · rintro ⟨hp, x, hz, hother⟩
    refine ⟨(d.positive a).2 hp, e x, (d.equation a x).trans hz, ?_⟩
    intro b hb hne
    obtain ⟨b, rfl⟩ := d.walls.surjective b
    have h := hother b ((d.positive b).1 hb) (fun h => hne (congrArg d.walls h))
    simpa only [Datum.positive, d.equation] using h

def simpleWalls : A.SimpleWall p ≃ A'.SimpleWall p' where
  toFun a := ⟨d.walls a.val, (isSimple_iff d _).2 a.property⟩
  invFun b := ⟨d.walls.symm b.val, (isSimple_iff d _).1 (by simpa using b.property)⟩
  left_inv a := Subtype.ext (d.walls.symm_apply_apply a.val)
  right_inv b := Subtype.ext (d.walls.apply_symm_apply b.val)

theorem walls_image (a : J × ℤ) :
    e '' A.wallHyperplane a = A'.wallHyperplane (d.walls a) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [Set.mem_image, e.injective.eq_iff, exists_eq_right, ApartmentRoots.wallHyperplane,
    Set.mem_ofPred_eq, d.equation]

theorem vertex_image (a : A.SimpleWall p) (x : V) (hx : IsAlcoveVertex A p a x) :
    IsAlcoveVertex A' p' (simpleWalls d a) (e x) := by
  constructor
  · intro b hb
    obtain ⟨b, rfl⟩ := d.walls.surjective b
    rw [d.equation]
    exact hx.1 b ((d.positive b).1 hb)
  · intro b
    obtain ⟨b, rfl⟩ := (simpleWalls d).surjective b
    change A'.wallValue (d.walls b.val) (e x) = 0 ↔ simpleWalls d b ≠ simpleWalls d a
    rw [d.equation, hx.2, (simpleWalls d).injective.ne_iff]

theorem reflection_transport (a : J × ℤ) (x : V) :
    A'.reflection (d.walls a) (e x) = e (A.reflection a x) := by
  rw [reflection_apply, reflection_apply, d.equation, sub_eq_add_neg x]
  rw [add_comm x, affine_apply_add, map_neg, map_smul, d.coroot]
  abel

def affineConjugacy (e : V ≃ᵃ[ℚ] V') : (V ≃ᵃ[ℚ] V) ≃* (V' ≃ᵃ[ℚ] V') where
  toFun w := e.symm.trans (w.trans e)
  invFun w := e.trans (w.trans e.symm)
  left_inv w := by ext x; simp
  right_inv w := by ext x; simp
  map_mul' w z := by ext x; simp [AffineEquiv.coe_mul]

theorem conjugacy_reflection (a : J × ℤ) :
    affineConjugacy e (A.reflection a) = A'.reflection (d.walls a) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simpa [affineConjugacy] using (reflection_transport d a x).symm

theorem conjugacy_ordinary (d : WallComparison A A' p p' e) :
    A.affineWeylGroup.map (affineConjugacy e).toMonoidHom = A'.affineWeylGroup := by
  have hs : (affineConjugacy e).toMonoidHom '' Set.range A.reflection =
      Set.range A'.reflection := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨d.walls a, (conjugacy_reflection d a).symm⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := d.walls.surjective b
      exact ⟨_, ⟨a, rfl⟩, conjugacy_reflection d a⟩
  change (Subgroup.closure (Set.range A.reflection)).map (affineConjugacy e).toMonoidHom =
    Subgroup.closure (Set.range A'.reflection)
  rw [MonoidHom.map_closure, hs]

def ordinaryLabels : A.affineWeylGroup ≃* A'.affineWeylGroup :=
  (A.affineWeylGroup.equivMapOfInjective (affineConjugacy e).toMonoidHom (affineConjugacy e).injective).trans
    (MulEquiv.subgroupCongr (conjugacy_ordinary d))

theorem ordinaryLabels_apply (w : A.affineWeylGroup) (x : V) :
    (ordinaryLabels d w).val (e x) = e (w.val x) := by
  change e (w.val (e.symm (e x))) = _
  rw [e.symm_apply_apply]

theorem ordinaryLabels_simple (a : A.SimpleWall p) :
    ordinaryLabels d (A.simpleAffineReflection p a) =
      A'.simpleAffineReflection p' (simpleWalls d a) :=
  Subtype.ext (conjugacy_reflection d a.val)

def linearWallComparison (e₀ : V ≃ₗ[ℚ] V') (b : J ≃ J')
    (hp : p' = e₀ p) (hr : ∀ i x, A'.root (b i) (e₀ x) = A.root i x)
    (hc : ∀ i, e₀ (A.coroot i) = A'.coroot (b i)) :
    WallComparison A A' p p' e₀.toAffineEquiv where
  walls := b.prodCongr (Equiv.refl ℤ)
  equation := fun a x => by
    change A'.root (b a.1) (e₀ x) + (a.2 : ℚ) = A.root a.1 x + (a.2 : ℚ)
    rw [hr]
  coroot := fun a => hc a.1
  positive := fun a => by
    change A'.root (b a.1) p' + (a.2 : ℚ) > 0 ↔ A.root a.1 p + (a.2 : ℚ) > 0
    rw [hp, hr]

end Walls


section Arrangement

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

theorem coroot_ne_zero (i : J) : A.coroot i ≠ 0 := by
  intro h
  have hd := A.diagonal i
  rw [h, map_zero] at hd
  exact (by norm_num : (0 : ℚ) ≠ 2) hd

theorem reflection_fixes_iff (a : J × ℤ) (x : V) :
    A.reflection a x = x ↔ A.wallValue a x = 0 := by
  rw [reflection_apply, sub_eq_self, smul_eq_zero]
  simp only [coroot_ne_zero, or_false]

theorem reflection_ne_one (a : J × ℤ) : A.reflection a ≠ 1 := by
  intro h
  have hz : A.wallValue a 0 = 0 := (reflection_fixes_iff a 0).1 (by rw [h]; rfl)
  have hc : A.wallValue a (A.coroot a.1) = 0 :=
    (reflection_fixes_iff a _).1 (by rw [h]; rfl)
  simp only [Datum.value, map_zero, zero_add] at hz
  simp only [Datum.value, A.diagonal, hz, add_zero] at hc
  norm_num at hc

theorem exists_opposite_direction (hA : AlcoveGeometry A p) (i : J) :
    ∃ j, A.root j = -A.root i := by
  let a : J × ℤ := (i, 0)
  have hmem : A.reflection a ∈ A.affineWeylGroup := Subgroup.subset_closure ⟨a, rfl⟩
  obtain ⟨d, hd⟩ := hA.ordinary_symmetries hmem
  refine ⟨(d a).1, LinearMap.ext fun x => ?_⟩
  have hzero := (hd a).1 0
  have hval := (hd a).1 (A.reflection a x)
  have hlin (y : V) : A.reflection a y = y - A.root i y • A.coroot i := by
    simp [reflection_apply, Datum.value, a]
  have invol : A.reflection a (A.reflection a x) = x := by
    rw [hlin, hlin, map_sub, map_smul, A.diagonal]
    simp only [smul_eq_mul, show ∀ t : ℚ, t - t * 2 = -t from fun t => by ring,
      neg_smul, sub_neg_eq_add, sub_add_cancel]
  rw [invol, hlin] at hval
  rw [hlin, map_zero, zero_smul, sub_zero] at hzero
  simp only [Datum.value, map_zero, a, Int.cast_zero, add_zero, zero_add] at hzero
  simp only [Datum.value, map_sub, map_smul, A.diagonal, smul_eq_mul,
    a, Int.cast_zero, add_zero, hzero, LinearMap.neg_apply] at hval ⊢
  linarith

theorem alcove_sign (hA : AlcoveGeometry A p) {x : V} (hx : x ∈ A.alcove p)
    (a : J × ℤ) : A.positive x a ↔ A.positive p a := by
  refine ⟨?_, hx a⟩
  intro ha
  by_contra hn
  obtain ⟨j, hj⟩ := exists_opposite_direction hA a.1
  let b : J × ℤ := (j, -a.2)
  have hb (z : V) : A.wallValue b z = -A.wallValue a z := by
    simp [Datum.value, b, hj, neg_add_rev, add_comm]
  have hpa : A.wallValue a p ≠ 0 := by
    intro hz
    apply hA.regular a.1
    refine ⟨-a.2, ?_⟩
    change A.root a.1 p + (a.2 : ℚ) = 0 at hz
    push_cast
    linarith
  have hpb : A.positive p b := by
    change 0 < A.wallValue b p
    rw [hb]
    change ¬ 0 < A.wallValue a p at hn
    linarith [lt_of_le_of_ne (le_of_not_gt hn) hpa]
  have hn' := hx b hpb
  change 0 < A.wallValue b x at hn'
  change 0 < A.wallValue a x at ha
  rw [hb] at hn'
  linarith

theorem alcove_at_mem (hA : AlcoveGeometry A p) {x : V} (hx : x ∈ A.alcove p) :
    A.alcove x = A.alcove p := by
  ext y
  change (∀ a, A.positive x a → A.positive y a) ↔ (∀ a, A.positive p a → A.positive y a)
  simp only [alcove_sign hA hx]

theorem symmetries_alcove (hA : AlcoveGeometry A p) {g : V ≃ᵃ[ℚ] V} (hg : g ∈ A.symmetries)
    (he : g '' A.alcove p = A.alcove p) : Nonempty (WallComparison A A p p g) := by
  obtain ⟨d, hd⟩ := hg
  have hgp : g p ∈ A.alcove p :=
    he ▸ Set.mem_image_of_mem g (fun _ h => h)
  refine ⟨⟨d, fun a => (hd a).1, fun a => (hd a).2, fun a => ?_⟩⟩
  rw [← alcove_sign hA hgp (d a)]
  simp only [Datum.positive, (hd a).1]

theorem ordinary_fixes_regular (hA : AlcoveGeometry A p) {g : A.affineWeylGroup}
    {x : V} (hx : A.IsRegular x) (h : g.val x = x) : g = 1 := by
  obtain ⟨d, hd⟩ := hA.ordinary_symmetries g.property
  have H (a : J × ℤ) (z : V) : A.positive (g.val z) (d a) ↔ A.positive z a := by
    simp only [Datum.positive, (hd a).1]
  have hg : g.val '' A.alcove x = A.alcove x := by
    ext y
    obtain ⟨z, rfl⟩ := g.val.surjective y
    rw [Set.mem_image]
    constructor
    · rintro ⟨a, ha, hza⟩
      have he := g.val.injective hza
      subst a
      intro b hbx
      obtain ⟨b, rfl⟩ := d.surjective b
      apply (H b z).2
      apply ha b
      exact (H b x).1 (by simpa only [h] using hbx)
    · intro hz
      refine ⟨z, ?_, rfl⟩
      intro a ha
      apply (H a z).1
      apply hz (d a)
      simpa only [h] using (H a x).2 ha
  obtain ⟨w, hw, hu⟩ := hA.simply_transitive x hx
  have hg' : (g * w).val '' A.alcove p = A.alcove x := by
    change (⇑g.val ∘ ⇑w.val) '' A.alcove p = _
    rw [Set.image_comp, hw, hg]
  exact mul_right_cancel (show g * w = 1 * w by simpa using hu _ hg')

/-- A rational affine map is determined by its conjugation on every marked wall reflection. -/
theorem affine_centralizer_trivial
    (hA : ∀ x, (∀ i, A.root i x = 0) → x = 0) (g : V ≃ᵃ[ℚ] V)
    (hg : ∀ a : J × ℤ, Commute g (A.reflection a)) : g = 1 := by
  have he (a : J × ℤ) (x : V) : g (A.reflection a x) = A.reflection a (g x) :=
    congrArg (fun f : V ≃ᵃ[ℚ] V => f x) (hg a).eq
  have hg₀ : g 0 = 0 := hA _ fun i => by
    have h := he (i, 0) 0
    rw [reflection_apply] at h
    simp only [Datum.value, map_zero, Int.cast_zero, add_zero, zero_smul, sub_zero] at h
    have hf := (reflection_fixes_iff (i, 0) (g 0)).1 h.symm
    simpa [Datum.value] using hf
  have hlin (x : V) : g x = g.linear x := by simpa [hg₀] using affine_apply_add g x 0
  have hc (i : J) : g.linear (A.coroot i) = A.coroot i := by
    have h := he (i, 1) 0
    rw [hg₀] at h
    simp only [reflection_apply, Datum.value, map_zero, zero_add, Int.cast_one, one_smul,
      zero_sub, hlin, map_neg, neg_inj] at h
    exact h
  ext x
  change g x = x
  rw [hlin]
  have H i : A.root i (g.linear x) = A.root i x := by
    have h := he (i, 0) x
    simp only [reflection_apply, Datum.value, Int.cast_zero, add_zero, hlin, map_sub, map_smul,
      hc, sub_right_inj] at h
    exact (smul_left_injective ℚ (coroot_ne_zero (A := A) i)) h.symm
  apply sub_eq_zero.mp
  apply hA
  intro i
  simp [H]


private theorem exists_small_parameter [Finite J] (δ : J → ℚ) (hδ : ∀ i, 0 < δ i) :
    ∃ t : ℚ, 0 < t ∧ ∀ i, t < δ i := by
  classical
  let := Fintype.ofFinite J
  let s := insert (1 : ℚ) (Finset.univ.image δ)
  have hn : s.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  refine ⟨s.min' hn / 2, div_pos ?_ (by norm_num), fun i => ?_⟩
  · have hm := Finset.min'_mem s hn
    simp only [s, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hm
    rcases hm with h | ⟨i, h⟩
    · rw [h]; norm_num
    · rw [← h]; exact hδ i
  · have hl : s.min' hn ≤ δ i := Finset.min'_le s _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    linarith [hδ i]

private theorem nonintegral_perturbation (b c : ℚ)
    (h : b ∉ Set.range (Int.cast : ℤ → ℚ) ∨ c ≠ 0) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t < δ → b + t * c ∉ Set.range (Int.cast : ℤ → ℚ) := by
  have between {x : ℚ} {m : ℤ} (h₁ : (m : ℚ) < x) (h₂ : x < (m : ℚ) + 1) :
      x ∉ Set.range (Int.cast : ℤ → ℚ) := by
    rintro ⟨k, rfl⟩
    have hk₁ : m < k := by exact_mod_cast h₁
    have hk₂ : k < m + 1 := by exact_mod_cast h₂
    omega
  by_cases hb : b ∈ Set.range (Int.cast : ℤ → ℚ)
  · obtain ⟨m, rfl⟩ := hb
    have hc : c ≠ 0 := h.resolve_left (not_not_intro ⟨m, rfl⟩)
    refine ⟨1 / |c|, div_pos zero_lt_one (abs_pos.mpr hc), fun t ht hsmall => ?_⟩
    have htc : t * |c| < 1 := (lt_div_iff₀ (abs_pos.mpr hc)).1 hsmall
    rcases lt_trichotomy c 0 with hneg | hzero | hpos
    · rw [abs_of_neg hneg] at htc
      apply between (m := m - 1) <;> push_cast <;> nlinarith [mul_neg_of_pos_of_neg ht hneg]
    · exact (hc hzero).elim
    · rw [abs_of_pos hpos] at htc
      exact between (by nlinarith [mul_pos ht hpos]) (by linarith)
  · have h₁ := (Int.floor_lt_self_iff (a := b)).2 hb
    have h₂ := Int.lt_floor_add_one b
    let r := min (b - (⌊b⌋ : ℚ)) ((⌊b⌋ : ℚ) + 1 - b)
    have hr : 0 < r := lt_min (sub_pos.mpr h₁) (sub_pos.mpr h₂)
    have hp : 0 < |c| + 1 := by positivity
    refine ⟨r / (|c| + 1), div_pos hr hp, fun t ht hsmall => ?_⟩
    have hs := (lt_div_iff₀ hp).1 hsmall
    have htc : |t * c| < r := by rw [abs_mul, abs_of_pos ht]; nlinarith
    have habs := abs_lt.mp htc
    have hleft : r ≤ b - (⌊b⌋ : ℚ) := min_le_left _ _
    have hright : r ≤ (⌊b⌋ : ℚ) + 1 - b := min_le_right _ _
    have hlo : (⌊b⌋ : ℚ) < b + t * c := by linarith
    have hhi : b + t * c < (⌊b⌋ : ℚ) + 1 := by linarith
    exact between hlo hhi

theorem normalizes_ordinary_wall {g : V ≃ᵃ[ℚ] V}
    (hA : AlcoveGeometry A p)
    (hg : ∀ w ∈ A.affineWeylGroup, g * w * g⁻¹ ∈ A.affineWeylGroup)
    (a : J × ℤ) {x : V} (hx : A.wallValue a x = 0) : ¬ A.IsRegular (g x) := by
  intro hreg
  let w := A.reflection a
  let v : A.affineWeylGroup := ⟨g * w * g⁻¹, hg w (Subgroup.subset_closure ⟨a, rfl⟩)⟩
  have hfix : v.val (g x) = g x := by
    simp only [v, AffineEquiv.coe_mul, Function.comp_apply, AffineEquiv.inv_def,
      AffineEquiv.symm_apply_apply, w, (reflection_fixes_iff a x).2 hx]
  have he := congrArg Subtype.val (ordinary_fixes_regular hA hreg hfix)
  change g * w * g⁻¹ = 1 at he
  apply reflection_ne_one (A := A) a
  simpa [mul_assoc] using congrArg (fun f : V ≃ᵃ[ℚ] V => g⁻¹ * f * g) he

/-- An affine hyperplane in the union of the rational walls lies in one wall. -/
theorem wall_in_singular [Finite J] (g : V ≃ᵃ[ℚ] V) (a : J × ℤ)
    (h : ∀ x, A.wallValue a x = 0 → ¬A.IsRegular (g x)) :
    ∃ b : J × ℤ, ∀ x, A.wallValue a x = 0 → A.wallValue b (g x) = 0 := by
  classical
  by_contra! hn
  let x₀ := (-(a.2 : ℚ) / 2) • A.coroot a.1
  have hx₀ : A.wallValue a x₀ = 0 := by
    simp only [Datum.value, x₀, map_smul, A.diagonal, smul_eq_mul]
    ring
  let Q := LinearMap.ker (A.root a.1)
  let L (i : J) : Q →ₗ[ℚ] ℚ := ((A.root i).comp g.linear.toLinearMap).domRestrict Q
  let I := {i // A.root i (g x₀) ∈ Set.range (Int.cast : ℤ → ℚ)}
  have hL (i : I) : ∃ y, L i.val y ≠ 0 := by
    obtain ⟨m, hm⟩ := i.property
    obtain ⟨x, hx, hn'⟩ := hn (i.val, -m)
    have hh : x - x₀ ∈ Q := by
      change A.root a.1 (x - x₀) = 0
      simp only [Datum.value] at hx hx₀
      rw [map_sub]
      linarith
    refine ⟨⟨x - x₀, hh⟩, fun hz => hn' ?_⟩
    have hgx : g x = g.linear (x - x₀) + g x₀ := by
      rw [← affine_apply_add, sub_add_cancel]
    change A.root i.val (g.linear (x - x₀)) = 0 at hz
    change A.root i.val (g x) + ((-m : ℤ) : ℚ) = 0
    rw [hgx, map_add, hz, zero_add, ← hm]
    simp
  obtain ⟨y, hy⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (fun i : I => L i.val) hL
  have hδ (i : J) := nonintegral_perturbation (A.root i (g x₀)) (L i y)
    (by by_cases hi : i ∈ {i | A.root i (g x₀) ∈ Set.range (Int.cast : ℤ → ℚ)}
        · exact Or.inr (hy ⟨i, hi⟩)
        · exact Or.inl hi)
  choose δ hδ hsmall using hδ
  obtain ⟨t, ht, hlt⟩ := exists_small_parameter δ hδ
  let x := t • (y : V) + x₀
  have hx : A.wallValue a x = 0 := by
    have hy₀ : A.root a.1 (y : V) = 0 := y.property
    simpa only [Datum.value, x, map_add, map_smul, hy₀, smul_zero, zero_add] using hx₀
  apply h x hx
  intro i
  have he : A.root i (g x) = A.root i (g x₀) + t * L i y := by
    change A.root i (g (t • (y : V) + x₀)) = _
    rw [affine_apply_add, map_smul, map_add, map_smul, smul_eq_mul, add_comm]
    rfl
  rw [he]
  exact hsmall i t ht (hlt i)



private theorem wall_value_proportional (g : V ≃ᵃ[ℚ] V) (a b : J × ℤ)
    (h : ∀ x, A.wallValue a x = 0 → A.wallValue b (g x) = 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (∀ x, A.root b.1 (g.linear x) = c * A.root a.1 x) ∧
      (∀ x, A.wallValue b (g x) = c * A.wallValue a x) := by
  let v := A.coroot a.1
  let c := A.root b.1 (g.linear v) / 2
  have hv : A.root a.1 v = 2 := A.diagonal a.1
  have hcalc (x : V) :
      A.wallValue a ((-(A.wallValue a x) / 2) • v + x) = 0 := by
    simp only [Datum.value, map_add, map_smul, hv, smul_eq_mul]
    ring
  have hval (x : V) : A.wallValue b (g x) = c * A.wallValue a x := by
    have hx := h _ (hcalc x)
    rw [affine_apply_add, map_smul] at hx
    simp only [Datum.value, map_add, map_smul, smul_eq_mul] at hx ⊢
    dsimp [c]
    linarith
  have hr (x : V) : A.root b.1 (g.linear x) = c * A.root a.1 x := by
    have hx := hval x
    have h₀ := hval 0
    rw [show g x = g.linear x + g 0 by simpa using affine_apply_add g x 0] at hx
    simp only [Datum.value, map_add, map_zero, zero_add, mul_add] at hx h₀
    linarith
  refine ⟨c, fun hc => ?_, hr, hval⟩
  obtain ⟨y, hy⟩ := g.linear.surjective (A.coroot b.1)
  have hz := hr y
  rw [hy, A.diagonal, hc, zero_mul] at hz
  norm_num at hz

private theorem root_map_integral [Finite J] (hA : AlcoveGeometry A p)
    (hR : A.ReducedDirections) (g : V ≃ᵃ[ℚ] V)
    (hg : ∀ w ∈ A.affineWeylGroup, g * w * g⁻¹ ∈ A.affineWeylGroup) (i : J) :
    ∃ (j : J) (m c : ℤ), c ≠ 0 ∧ A.root j (g 0) = (m : ℚ) ∧
      ∀ x, A.root j (g.linear x) = (c : ℚ) * A.root i x := by
  obtain ⟨b, hb⟩ := wall_in_singular g (i, 0) (fun _ => normalizes_ordinary_wall hA hg (i, 0))
  obtain ⟨b', hb'⟩ := wall_in_singular g (i, 1) (fun _ => normalizes_ordinary_wall hA hg (i, 1))
  obtain ⟨c, hc, hlin, ha⟩ := wall_value_proportional g (i, 0) b hb
  obtain ⟨c', hc', hlin', ha'⟩ := wall_value_proportional g (i, 1) b' hb'
  have hre : A.root b'.1 = (c' / c) • A.root b.1 := by
    ext y
    obtain ⟨x, rfl⟩ := g.linear.surjective y
    simp only [LinearMap.smul_apply, smul_eq_mul, hlin, hlin']
    field_simp
  have hm : A.root b.1 (g 0) = (-(b.2 : ℤ) : ℚ) := by
    have h := ha 0
    simp only [Datum.value, map_zero, Int.cast_zero, add_zero, mul_zero] at h
    linarith
  have hm' : A.root b'.1 (g 0) + (b'.2 : ℚ) = c' := by
    simpa [Datum.value] using ha' 0
  have hci : c ∈ Set.range (Int.cast : ℤ → ℚ) := by
    rcases hR.2 b.1 b'.1 (c' / c) hre with he | he
    · refine ⟨b'.2 - b.2, ?_⟩
      have hcc : c' = c := by
        have h₂ := hlin (A.coroot i)
        have h₃ := hlin' (A.coroot i)
        rw [← he] at h₃
        rw [A.diagonal] at h₂ h₃
        linarith
      rw [← he, hm, hcc] at hm'
      push_cast at hm' ⊢
      linarith
    · refine ⟨-b.2 - b'.2, ?_⟩
      have hcc : c' = -c := by
        have h₂ := hlin (A.coroot i)
        have h₃ := hlin' (A.coroot i)
        rw [he, LinearMap.neg_apply] at h₃
        rw [A.diagonal] at h₂ h₃
        linarith
      rw [he, LinearMap.neg_apply, hm, hcc] at hm'
      push_cast at hm' ⊢
      linarith
  obtain ⟨k, rfl⟩ := hci
  exact ⟨b.1, -b.2, k, by exact_mod_cast hc, hm, hlin⟩

theorem normalizer_root_permutation [Finite J] (hA : AlcoveGeometry A p)
    (hR : A.ReducedDirections) (g : V ≃ᵃ[ℚ] V)
    (hg : ∀ w ∈ A.affineWeylGroup, g * w * g⁻¹ ∈ A.affineWeylGroup)
    (hg' : ∀ w ∈ A.affineWeylGroup, g⁻¹ * w * g ∈ A.affineWeylGroup) :
    ∃ (d : Equiv.Perm J) (n : J → ℤ),
      (∀ i, A.root (d i) (g 0) = (n i : ℚ)) ∧
      ∀ i x, A.root (d i) (g.linear x) = A.root i x := by
  classical
  have h (i : J) : ∃ (j : J) (n : ℤ), A.root j (g 0) = (n : ℚ) ∧
      ∀ x, A.root j (g.linear x) = A.root i x := by
    obtain ⟨j, n, k, hk, hn, hlin⟩ := root_map_integral hA hR g hg i
    obtain ⟨j', _, l, hl, _, hlin'⟩ := root_map_integral hA hR g⁻¹ (by simpa only [inv_inv] using hg') j
    have hcomp (x : V) : A.root j' x = ((l * k : ℤ) : ℚ) * A.root i x := by
      have hh := hlin' (g.linear x)
      change A.root j' (g.linear.symm (g.linear x)) = _ at hh
      rw [LinearEquiv.symm_apply_apply, hlin x] at hh
      push_cast
      nlinarith only [hh]
    have hratio : A.root j' = ((l * k : ℤ) : ℚ) • A.root i := by
      ext x
      exact hcomp x
    have hu : l * k = 1 ∨ l * k = -1 := by
      have hh := hcomp (A.coroot i)
      rw [A.diagonal] at hh
      rcases hR.2 i j' _ hratio with he | he
      · left
        rw [← he, A.diagonal] at hh
        exact_mod_cast (show ((l * k : ℤ) : ℚ) = 1 by linarith)
      · right
        rw [he, LinearMap.neg_apply, A.diagonal] at hh
        exact_mod_cast (show ((l * k : ℤ) : ℚ) = -1 by linarith)
    have hk' : k = 1 ∨ k = -1 := by
      have hnat : l.natAbs * k.natAbs = 1 := by
        rw [← Int.natAbs_mul]
        rcases hu with hu | hu <;> simp [hu]
      have hkabs : k.natAbs = 1 := by
        have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
        have hlpos : 0 < l.natAbs := Int.natAbs_pos.mpr hl
        nlinarith [Nat.mul_le_mul_right k.natAbs (show 1 ≤ l.natAbs by omega)]
      omega
    rcases hk' with rfl | rfl
    · exact ⟨j, n, hn, by simpa using hlin⟩
    · obtain ⟨j', hj'⟩ := exists_opposite_direction hA j
      exact ⟨j', -n, by simp [hj', hn], by simp [hj', hlin]⟩
  choose d n hn hd using h
  have hd' : Function.Injective d := by
    intro i j h
    apply hR.1
    ext x
    rw [← hd i x, ← hd j x, h]
  exact ⟨Equiv.ofBijective d ⟨hd', Finite.injective_iff_surjective.mp hd'⟩, n, hn, hd⟩


end Arrangement


section Euclidean

variable {V V' J J' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  {A : ApartmentRoots ℚ V J} {A' : ApartmentRoots ℚ V' J'}

theorem root_eq_of_wall_eq {e : V ≃ᵃ[ℚ] V'} {a : J × ℤ} {b : J' × ℤ}
    (h : ∀ x, A'.wallValue b (e x) = A.wallValue a x) (x : V) :
    A'.root b.1 (e.linear x) = A.root a.1 x := by
  have hx := h x
  have h₀ := h 0
  have he : e x = e.linear x + e 0 := by simpa using affine_apply_add e x 0
  simp only [Datum.value, map_zero] at h₀
  rw [he] at hx
  simp only [Datum.value, map_add] at hx
  linarith

theorem realFunctional_comp {f : V →ₗ[ℚ] ℚ} {f' : V' →ₗ[ℚ] ℚ} (e : V →ₗ[ℚ] V')
    (h : ∀ x, f' (e x) = f x) :
    (realFunctional f').comp (e.baseChange ℝ) = realFunctional f := by
  have hh : f'.comp e = f := LinearMap.ext h
  simp only [realFunctional, LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hh]

def realRootMap [Fintype J] (A : ApartmentRoots ℚ V J) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] EuclideanSpace ℝ J :=
  (EuclideanSpace.equiv J ℝ).symm.toLinearMap.comp
    (LinearMap.pi fun i => realFunctional (A.root i))

theorem realRootMap_apply [Fintype J] (z : ℝ ⊗[ℚ] V) (i : J) :
    realRootMap A z i = realFunctional (A.root i) z := rfl

theorem realRootMap_injective [Fintype J]
    (hA : ∀ x, (∀ i, A.root i x = 0) → x = 0) :
    Function.Injective (realRootMap A) := by
  classical
  let f : V →ₗ[ℚ] (J → ℚ) := LinearMap.pi A.root
  have hf : Function.Injective f := (LinearMap.ker_eq_bot).1 (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => hA x (congrFun hx))
  have hfb : Function.Injective (f.baseChange ℝ) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  let E := (TensorProduct.piScalarRight ℚ ℝ ℝ J)
  have he : (EuclideanSpace.equiv J ℝ).toLinearMap.comp (realRootMap A) =
      E.toLinearMap.comp (f.baseChange ℝ) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    funext i
    simp [f, E, realRootMap, realFunctional, TensorProduct.piScalarRight]
  have hi : Function.Injective ⇑((EuclideanSpace.equiv J ℝ).toLinearMap.comp (realRootMap A)) := by
    rw [he]
    exact E.injective.comp hfb
  intro x y h
  exact hi (congrArg (EuclideanSpace.equiv J ℝ) h)

def rangeCoordinates [Fintype J] (hA : ∀ x, (∀ i, A.root i x = 0) → x = 0) :
    LinearMap.range (realRootMap A) ≃ₗᵢ[ℝ] EuclideanApartment V := by
  have hd := (LinearEquiv.ofInjective (realRootMap A) (realRootMap_injective hA)).finrank_eq
  rw [Module.finrank_baseChange] at hd
  exact ((stdOrthonormalBasis ℝ (LinearMap.range (realRootMap A))).reindex
    (finCongr hd.symm)).repr

def rootCoordinates [Fintype J] (hA : ∀ x, (∀ i, A.root i x = 0) → x = 0) :
    RealCoordinates V :=
  (LinearEquiv.ofInjective (realRootMap A) (realRootMap_injective hA)).trans
    (rangeCoordinates hA).toLinearEquiv

theorem rootCoordinates_norm [Fintype J] (hA : ∀ x, (∀ i, A.root i x = 0) → x = 0) :
    RootCoordinates A (rootCoordinates hA) := by
  intro z
  rw [show ‖rootCoordinates hA z‖ = ‖realRootMap A z‖ from
    (rangeCoordinates hA).norm_map
      (LinearEquiv.ofInjective (realRootMap A) (realRootMap_injective hA) z)]
  simp only [EuclideanSpace.real_norm_sq_eq, realRootMap_apply]

theorem realAffine_isometry [Fintype J] [Fintype J']
    {r : RealCoordinates V} {r' : RealCoordinates V'} (hr : RootCoordinates A r)
    (hr' : RootCoordinates A' r') {e : V ≃ᵃ[ℚ] V'} (d : J ≃ J')
    (he : ∀ i x, A'.root (d i) (e.linear x) = A.root i x) :
    Isometry (realAffine r r' e) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [realAffine, dist_eq_norm, ← map_sub, add_sub_add_right_eq_sub]
  let z := r.symm (x - y)
  change ‖r' (e.linear.toLinearMap.baseChange ℝ z)‖ = ‖x - y‖
  have hnorm : ‖r' (e.linear.toLinearMap.baseChange ℝ z)‖ ^ 2 = ‖r z‖ ^ 2 := by
    rw [hr', hr, ← Equiv.sum_comp d (fun j => (realFunctional (A'.root j)
      (e.linear.toLinearMap.baseChange ℝ z)) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← LinearMap.comp_apply, realFunctional_comp _ (he i)]
  have hz : r z = x - y := r.apply_symm_apply _
  rw [hz] at hnorm
  nlinarith [norm_nonneg (r' (e.linear.toLinearMap.baseChange ℝ z)), norm_nonneg (x - y)]

theorem realAffine_rational {r : RealCoordinates V} {r' : RealCoordinates V'}
    (e : V ≃ᵃ[ℚ] V') (x : V) :
    realAffine r r' e (rationalPoint r x) = rationalPoint r' (e x) := by
  simp only [realAffine, rationalPoint, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    ← TensorProduct.tmul_add]
  congr 2
  simpa using (affine_apply_add e x 0).symm


theorem direction_permutation [Finite J] (hR : A.ReducedDirections) {g : V ≃ᵃ[ℚ] V}
    (hg : g ∈ A.symmetries) :
    ∃ d : Equiv.Perm J, ∀ i x, A.root (d i) (g.linear x) = A.root i x := by
  obtain ⟨w, hw⟩ := hg
  let d (i : J) := (w (i, 0)).1
  have hd (i : J) (x : V) : A.root (d i) (g.linear x) = A.root i x :=
    root_eq_of_wall_eq (hw (i, 0)).1 x
  have hinj : Function.Injective d := by
    intro i j h
    apply hR.1
    ext x
    rw [← hd i x, ← hd j x, h]
  exact ⟨Equiv.ofBijective d ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hd⟩

theorem realAffine_isometry_of_symmetry [Fintype J] {r : RealCoordinates V} (hr : RootCoordinates A r)
    (hR : A.ReducedDirections) {g : V ≃ᵃ[ℚ] V} (hg : g ∈ A.symmetries) :
    Isometry (realAffine r r g) := by
  obtain ⟨d, hd⟩ := direction_permutation hR hg
  exact realAffine_isometry hr hr d hd

private def rootSquare [Fintype J] (A : ApartmentRoots ℚ V J) (x : V) : ℚ :=
  ∑ i, (A.root i x) ^ 2

private theorem rootSquare_linear [Fintype J] {g : V ≃ᵃ[ℚ] V}
    (d : Equiv.Perm J) (hd : ∀ i x, A.root (d i) (g.linear x) = A.root i x) (x : V) :
    rootSquare A (g.linear x) = rootSquare A x := by
  rw [rootSquare, rootSquare, ← Equiv.sum_comp d (fun j => (A.root j (g.linear x)) ^ 2)]
  simp only [hd]

private theorem reflection_linear (a : J × ℤ) (x : V) :
    (A.reflection a).linear x = x - A.root a.1 x • A.coroot a.1 := rfl

private theorem involution_coroot_unique [Fintype J]
    (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0)
    {r : V →ₗ[ℚ] ℚ} {v w : V} (hv : r v = 2) (hw : r w = 2)
    (h₁ : ∀ x, rootSquare A (x - r x • v) = rootSquare A x)
    (h₂ : ∀ x, rootSquare A (x - r x • w) = rootSquare A x) :
    v = w := by
  let B : ℚ := ∑ i, A.root i v * A.root i w
  have hcalc (x y : V) (k : ℚ) :
      rootSquare A (x - k • y) =
        rootSquare A x - 2 * k * (∑ i, A.root i x * A.root i y) + k ^ 2 * rootSquare A y := by
    unfold rootSquare
    simp only [map_sub, map_smul, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have H₁ := h₁ w
  have H₂ := h₂ v
  rw [hw, hcalc, show (∑ i, A.root i w * A.root i v) = B by simp [B, mul_comm]] at H₁
  rw [hv, hcalc] at H₂
  change rootSquare A v - 2 * 2 * B + 2 ^ 2 * rootSquare A w = _ at H₂
  have H : rootSquare A (v - w) = 0 := by
    rw [← one_smul ℚ w, hcalc]
    change rootSquare A v - 2 * 1 * B + 1 ^ 2 * rootSquare A w = 0
    linarith
  apply sub_eq_zero.mp
  apply hS
  intro i
  have hnon (j : J) (_ : j ∈ (Finset.univ : Finset J)) : 0 ≤ (A.root j (v - w)) ^ 2 := sq_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp H i (Finset.mem_univ i)
  nlinarith [sq_nonneg (A.root i (v - w))]

theorem normalizer_wallComparison [Fintype J]
    {p : V} (hA : AlcoveGeometry A p) (hR : A.ReducedDirections)
    (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0) (g : V ≃ᵃ[ℚ] V)
    (hC : g '' A.alcove p = A.alcove p)
    (hg : ∀ w ∈ A.affineWeylGroup, g * w * g⁻¹ ∈ A.affineWeylGroup)
    (hg' : ∀ w ∈ A.affineWeylGroup, g⁻¹ * w * g ∈ A.affineWeylGroup) :
    Nonempty (WallComparison A A p p g) := by
  obtain ⟨d, n, hn, hd⟩ := normalizer_root_permutation hA hR g hg hg'
  let w : Equiv.Perm (J × ℤ) :=
    { toFun := fun a => (d a.1, a.2 - n a.1)
      invFun := fun b => (d.symm b.1, b.2 + n (d.symm b.1))
      left_inv := fun a => by simp
      right_inv := fun a => by simp }
  have he (a : J × ℤ) (x : V) : A.wallValue (w a) (g x) = A.wallValue a x := by
    change A.root (d a.1) (g x) + ((a.2 - n a.1 : ℤ) : ℚ) = _
    have hl : g x = g.linear x + g 0 := by simpa using affine_apply_add g x 0
    rw [hl, map_add, hd, hn, Int.cast_sub]
    change _ = A.root a.1 x + (a.2 : ℚ)
    ring
  have hgp : g p ∈ A.alcove p := hC ▸ Set.mem_image_of_mem g (fun _ h => h)
  refine ⟨⟨w, he, ?_, fun a => ?_⟩⟩
  · intro a
    let b := w a
    change g.linear (A.coroot a.1) = A.coroot b.1
    have h₁ : g * A.reflection a * g⁻¹ ∈ A.symmetries :=
      hA.ordinary_symmetries (hg _ (Subgroup.subset_closure ⟨a, rfl⟩))
    have h₂ : A.reflection b ∈ A.symmetries :=
      hA.ordinary_symmetries (Subgroup.subset_closure ⟨b, rfl⟩)
    obtain ⟨d₁, hd₁⟩ := direction_permutation hR h₁
    obtain ⟨d₂, hd₂⟩ := direction_permutation hR h₂
    refine involution_coroot_unique hS (by rw [show b.1 = d a.1 from rfl, hd, A.diagonal])
      (A.diagonal b.1) ?_ ?_
    · intro x
      obtain ⟨y, rfl⟩ := g.linear.surjective x
      have h := rootSquare_linear d₁ hd₁ (g.linear y)
      change rootSquare A (g.linear ((A.reflection a).linear (g.linear.symm (g.linear y)))) =
        rootSquare A (g.linear y) at h
      rw [LinearEquiv.symm_apply_apply, reflection_linear, map_sub, map_smul] at h
      simpa only [show b.1 = d a.1 from rfl, hd] using h
    · intro x
      simpa only [reflection_linear] using rootSquare_linear d₂ hd₂ x
  · rw [← alcove_sign hA hgp (w a)]
    simp only [Datum.positive, he]


end Euclidean


section ActualRoots

universe u

open RootData (extendFunctional extendFunctional_one_tmul)

theorem split_roots_separate (D : BasedRootDatum.{u}) (hs : D.datum.rootSpan ℤ = ⊤)
    (x : ℚ ⊗[ℤ] D.Y) (hx : ∀ i, (ApartmentRoots.split D.datum ℚ).root i x = 0) :
    x = 0 := by
  let := D.freeY
  let := D.finiteY
  classical
  let b := Module.Free.chooseBasis ℤ D.Y
  let E := Algebra.TensorProduct.equivPiOfFiniteBasis ℚ b
  have hχ (χ : D.X) : (Module.Dual.baseChange ℚ (D.datum.toLinearMap χ)) x = 0 := by
    have hm : χ ∈ Submodule.span ℤ (Set.range D.datum.root) := by
      change χ ∈ D.datum.rootSpan ℤ
      rw [hs]
      trivial
    let f : D.X →ₗ[ℤ] ℚ :=
      { toFun := fun χ => (Module.Dual.baseChange ℚ (D.datum.toLinearMap χ)) x
        map_add' := fun χ ψ => by simp
        map_smul' := fun n χ => by simp }
    change χ ∈ f.ker
    apply Submodule.span_le.mpr _ hm
    rintro _ ⟨i, rfl⟩
    exact hx i
  apply E.injective
  rw [map_zero]
  funext i
  change E x i = 0
  obtain ⟨χ, h⟩ := D.datum.toLinearMap.toPerfPair.surjective (b.coord i)
  have he : (LinearMap.proj i).comp E.toLinearMap = Module.Dual.baseChange ℚ (b.coord i) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro z y
    simp [E, Algebra.TensorProduct.equivPiOfFiniteBasis, TensorProduct.piScalarRight_apply,
      Module.Basis.equivFun_apply, Module.Basis.coord_apply]
  have h' : Module.Dual.baseChange ℚ (b.coord i) x = 0 := by rw [← h]; exact hχ χ
  exact (LinearMap.congr_fun he x).trans h'

theorem split_roots_reduced (D : BasedRootDatum.{u}) : (ApartmentRoots.split D.datum ℚ).ReducedDirections := by
  let A := ApartmentRoots.split D.datum ℚ
  have hext (f g : D.Y →ₗ[ℤ] ℤ) (h : extendFunctional ℚ f = extendFunctional ℚ g) : f = g := by
    ext y
    have he := LinearMap.congr_fun h ((1 : ℚ) ⊗ₜ[ℤ] y)
    simp only [extendFunctional_one_tmul] at he
    exact_mod_cast he
  refine ⟨fun i j h => D.datum.root.injective
    (D.datum.toLinearMap.toPerfPair.injective (hext _ _ h)), ?_⟩
  intro i j c hc
  have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  have h (y : D.Y) :
      (c.den : ℤ) * D.datum.root' j y = c.num * D.datum.root' i y := by
    have h' := LinearMap.congr_fun hc ((1 : ℚ) ⊗ₜ[ℤ] y)
    change extendFunctional ℚ (D.datum.root' j) _ =
      c * extendFunctional ℚ (D.datum.root' i) _ at h'
    simp only [extendFunctional_one_tmul] at h'
    have hr : (c.num : ℚ) / (c.den : ℚ) = c := Rat.num_div_den c
    rw [← hr, div_mul_eq_mul_div, eq_div_iff hd] at h'
    exact_mod_cast (mul_comm (c.den : ℚ) ((D.datum.root' j y : ℤ) : ℚ) |>.trans h')
  have hrel : (c.den : ℤ) • D.datum.root j = c.num • D.datum.root i := by
    apply D.datum.toLinearMap.toPerfPair.injective
    ext y
    simpa [LinearMap.smul_apply, smul_eq_mul] using h y
  have hdep : ¬ LinearIndependent ℤ ![D.datum.root j, D.datum.root i] := by
    intro hind
    rw [LinearIndependent.pair_iff] at hind
    have hsum : (c.den : ℤ) • D.datum.root j + (-c.num) • D.datum.root i = 0 := by
      rw [hrel, neg_smul, add_neg_cancel]
    exact c.den_nz (by exact_mod_cast (hind _ _ hsum).1)
  rcases D.reduced.eq_or_eq_neg j i hdep with he | he
  · exact Or.inl (D.datum.root.injective he).symm
  · right
    change extendFunctional ℚ (D.datum.root' j) = -extendFunctional ℚ (D.datum.root' i)
    apply TensorProduct.AlgebraTensorModule.ext
    intro z y
    simp [extendFunctional, RootPairing.root', he, zsmul_eq_mul]

private theorem folded_coord_bound (a : FoldedRootDirection) (i : Fin 4) :
    a.val i ∈ Finset.Icc (-2 : ℤ) 2 := by
  have hsign (s : Bool) : unitSign s = 1 ∨ unitSign s = -1 := by cases s <;> simp [unitSign]
  have hsign' (s : Bool) : -2 ≤ 2 * unitSign s ∧ 2 * unitSign s ≤ 2 := by
    rcases hsign s with h | h <;> rw [h] <;> norm_num
  rw [Finset.mem_Icc]
  rcases a.property with ⟨j, k, s, t, hne, h⟩ | ⟨j, s, h⟩ | h
  · by_cases hji : j = i
    · subst j
      simpa [h, Pi.single_apply, Ne.symm hne] using hsign' s
    · by_cases hki : k = i
      · subst k
        simpa [h, Pi.single_apply, hji] using hsign' t
      · simp [h, hji, hki]
  · by_cases hji : j = i
    · subst j
      simpa [h, Pi.single_apply] using hsign' s
    · simp [h, hji]
  · rcases h i with hi | hi <;> rw [hi] <;> norm_num

theorem folded_directions_finite : Finite FoldedRootDirection := by
  let f (a : FoldedRootDirection) (i : Fin 4) : ↥(Finset.Icc (-2 : ℤ) 2) :=
    ⟨a.val i, folded_coord_bound a i⟩
  exact Finite.of_injective f fun a b h => Subtype.ext (funext fun i => congrArg
    (fun v : Fin 4 → ↥(Finset.Icc (-2 : ℤ) 2) => (v i : ℤ)) h)

private def axialRoot (i : Fin 4) : FoldedRootDirection :=
  ⟨Pi.single i 2, Or.inr (Or.inl ⟨i, true, by norm_num [unitSign]⟩)⟩

private theorem axialRoot_not_long (i : Fin 4) : ¬IsLongF4Doubled (axialRoot i).val := by
  rintro ⟨j, k, s, t, hjk, he⟩
  have hzero (b : Bool) : 2 * unitSign b ≠ 0 := by cases b <;> norm_num [unitSign]
  have hj : j = i := by
    by_contra hji
    have h := congrFun he j
    exact hzero s (by simpa [axialRoot, Pi.single_apply, Ne.symm hji, Ne.symm hjk] using h.symm)
  have hk : k = i := by
    by_contra hki
    have h := congrFun he k
    exact hzero t (by simpa [axialRoot, Pi.single_apply, Ne.symm hki, hjk] using h.symm)
  exact hjk (hj.trans hk.symm)

theorem folded_roots_separate {D : BasedRootDatum.{u}} {τ : Pinning.BasedIso D D}
    (A : FoldedApartment τ) (x : ExceptionalValuedTorusNormalizer.invariantApartment D τ)
    (hx : ∀ i, A.roots.root i x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := A.coordinates.surjective x
  suffices hy : y = 0 by rw [hy, map_zero]
  ext i
  have h := hx (axialRoot i)
  rw [A.normalized_root] at h
  have he : normalizedFoldedRoot ℚ (axialRoot i) y = 2 * y i := by
    classical
    simp only [normalizedFoldedRoot, normalizedFoldedNumerator, ite_eq_right (axialRoot_not_long i)]
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · norm_num [axialRoot]
    · intro j _ hji
      simp [axialRoot, hji]
    · simp
  change y i = 0
  rw [he] at h
  linarith


theorem folded_roots_reduced {D : BasedRootDatum.{u}} {τ : Pinning.BasedIso D D}
    (A : FoldedApartment τ) : A.roots.ReducedDirections := by
  classical
  let k (i : FoldedRootDirection) : ℚ := if IsLongF4Doubled i.val then 1 else 2
  let R (i : FoldedRootDirection) (j : Fin 4) : ℚ := (normalizedFoldedNumerator i.val j : ℚ) / 2
  have hk i : k i = 1 ∨ k i = 2 := by unfold k; split <;> simp
  have hR i j : R i j = k i * normalizedFoldedCoroot ℚ i j := by
    dsimp [R, k, normalizedFoldedNumerator, normalizedFoldedCoroot]
    split
    · ring
    · change ((2 * i.val j : ℤ) : ℚ) / 2 = _
      push_cast
      ring
  have he i (x : Fin 4 → ℚ) :
      A.roots.root i (A.coordinates x) = ∑ j, R i j * x j := by
    rw [A.normalized_root]
    simp [normalizedFoldedRoot, R]
  have ht i j : A.roots.root i (A.coordinates (Pi.single j 1)) = R i j := by
    rw [he]
    simp [Pi.single_apply, eq_comm]
  have hnorm i : ∑ j, (R i j) ^ 2 = 2 * k i := by
    have hd := A.roots.diagonal i
    rw [← A.normalized_coroot, he] at hd
    rw [mul_comm, ← hd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_two, hR i j]; ring
  have hinj : Function.Injective R := by
    intro i j h
    have hs := hnorm i
    rw [h, hnorm] at hs
    have hk' : k i = k j := by linarith
    apply Subtype.ext
    funext l
    have hn : R i l = R j l := congrFun h l
    rw [hR, hR, hk'] at hn
    have hp := hk j
    rcases hp with hp | hp <;> rw [hp] at hn <;>
      simp only [normalizedFoldedCoroot] at hn <;>
      exact_mod_cast (show (i.val l : ℚ) = (j.val l : ℚ) by linarith)
  refine ⟨fun i j h => hinj (funext fun l => by rw [← ht i l, ← ht j l, h]), ?_⟩
  intro i j c h
  have hs (l : Fin 4) : R j l = c * R i l := by
    rw [← ht i l, ← ht j l, h]
    rfl
  obtain ⟨m, hm⟩ := A.roots.integral j i
  rw [h, LinearMap.smul_apply, smul_eq_mul, A.roots.diagonal] at hm
  have hq : 2 * k j = c ^ 2 * (2 * k i) := calc
    2 * k j = ∑ l, (R j l) ^ 2 := (hnorm j).symm
    _ = ∑ l, c ^ 2 * (R i l) ^ 2 := Finset.sum_congr rfl fun l _ => by rw [hs, mul_pow]
    _ = _ := by rw [← Finset.mul_sum, hnorm]
  have hbounds : (m : ℚ) ^ 2 ≤ 8 ∧ 2 ≤ (m : ℚ) ^ 2 := by
    rw [← hm]
    rcases hk i with hi | hi <;> rcases hk j with hj | hj <;>
      rw [hi, hj] at hq <;> constructor <;> nlinarith
  have hlo : -3 < m := by
    by_contra! hn
    have hn' : (m : ℚ) ≤ -3 := by exact_mod_cast hn
    nlinarith [sq_nonneg ((m : ℚ) + 3)]
  have hhi : m < 3 := by
    by_contra! hn
    have hn' : (3 : ℚ) ≤ m := by exact_mod_cast hn
    nlinarith [sq_nonneg ((m : ℚ) - 3)]
  have hm' : m = -2 ∨ m = 2 := by
    have hcases : m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with h | h | h | h | h
    · exact Or.inl h
    · norm_num [h] at hbounds
    · norm_num [h] at hbounds
    · norm_num [h] at hbounds
    · exact Or.inr h
  rcases hm' with rfl | rfl
  · right
    have hc : c = -1 := by norm_num at hm; linarith
    rw [h, hc, neg_one_smul]
  · left
    have hc : c = 1 := by norm_num at hm; linarith
    exact (hinj (funext fun l => by simp [hs, hc])).symm


end ActualRoots


section Groups

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  (C : LocalComparison (j := j) (Wf := Wf) A p)

theorem unitTorus_le_iwahori : C.T₀ ≤ C.I := by
  have h : C.I ⊓ C.N = C.T₀ := C.localIwahori.intersection
  rw [← h]
  exact inf_le_left

theorem mem_unitTorus_iff (n : C.N) : (n : G) ∈ C.T₀ ↔ C.affine n = 1 := by
  have h : C.affine.ker.map C.N.subtype = C.T₀ := C.kernel
  rw [← h]
  change (∃ m : C.N, m ∈ C.affine.ker ∧ (m : G) = (n : G)) ↔ _
  simp only [MonoidHom.mem_ker, Subtype.coe_inj, exists_eq_right]

theorem lift_difference (n : C.N) (w : A.affineWeylGroup) (h : C.affine n = w.val) :
    (n : G) * (C.lift w : G)⁻¹ ∈ C.T₀ := by
  exact (mem_unitTorus_iff C (n * (C.lift w)⁻¹)).2 (by simp [h, C.lift_label])

theorem lift_mem_ordinary (w : A.affineWeylGroup) : (C.lift w : G) ∈ C.G₀ :=
  by
    apply (le_sup_right : (A.affineWeylGroup.comap C.affine).map C.N.subtype ≤ C.G₀)
    refine ⟨C.lift w, ?_, rfl⟩
    change C.affine (C.lift w) ∈ A.affineWeylGroup
    rw [C.lift_label]
    exact w.property

theorem ordinary_eq_top (h : C.affine.range = A.affineWeylGroup) : C.G₀ = ⊤ := by
  have he : (A.affineWeylGroup.comap C.affine).map C.N.subtype = C.N := by
    ext n
    constructor
    · rintro ⟨m, _, rfl⟩
      exact m.property
    · intro hn
      refine ⟨⟨n, hn⟩, ?_, rfl⟩
      change C.affine ⟨n, hn⟩ ∈ A.affineWeylGroup
      rw [← h]
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [LocalComparison.G₀, he]
  exact C.localIwahori.generation

private theorem mem_cell_iff (w : A.affineWeylGroup) (x : G) :
    x ∈ C.cell w ↔ ∃ a ∈ C.I, ∃ b ∈ C.I, x = a * (C.lift w : G) * b :=
  DoubleCoset.mem_doubleCoset

private theorem cell_mul_iwahori (w : A.affineWeylGroup) {x i : G}
    (hx : x ∈ C.cell w) (hi : i ∈ C.I) : x * i ∈ C.cell w := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_cell_iff C w x).1 hx
  exact (mem_cell_iff C _ _).2 ⟨a, ha, b * i, C.I.mul_mem hb hi, mul_assoc _ _ _⟩

private theorem lift_one (C : LocalComparison (j := j) (Wf := Wf) A p) :
    (C.lift 1 : G) ∈ C.I :=
  unitTorus_le_iwahori C ((mem_unitTorus_iff C (C.lift 1)).2 (C.lift_label 1))

private theorem lift_simple_sq (i : A.SimpleWall p) :
    (C.lift (C.coxeter.coxeter.simple i) : G) ^ 2 ∈ C.I := by
  apply unitTorus_le_iwahori C
  change ((C.lift (C.coxeter.coxeter.simple i)) ^ 2 : C.N).val ∈ C.T₀
  apply (mem_unitTorus_iff C _).2
  rw [map_pow, C.lift_label, pow_two]
  exact congrArg Subtype.val (C.coxeter.coxeter.simple_mul_simple_self i)

open scoped Pointwise in
theorem mem_parahoric_iff_cell {q : ℕ} (hB : C.Bruhat q)
    (T : Set (A.SimpleWall p)) (x : G) :
    x ∈ parahoric C T ↔ ∃ w ∈ wallSubgroup T, x ∈ C.cell w := by
  classical
  let := C.coxeter.action
  let S := C.coxeter.coxeter.simple
  let P := parahoric C T
  let W := wallSubgroup T
  have hs (i) : S i = A.simpleAffineReflection p i := congrFun C.coxeter.simple_eq i
  have hw : W = Subgroup.closure (S '' T) := by
    unfold W wallSubgroup
    simp only [hs]
  have hI : C.I ≤ P := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have hl {i} (hi : i ∈ T) : (C.lift (S i) : G) ∈ P :=
    Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
  have hprod (w i) : C.cell (w * S i) ⊆ C.cell w * C.cell (S i) ∧
      C.cell w * C.cell (S i) ⊆ C.cell (w * S i) ∪ C.cell w := by
    rw [hB.wall_product w i]
    split
    · exact ⟨fun _ h => h, Set.subset_union_left⟩
    · exact ⟨Set.subset_union_left, fun _ h => h⟩
  have hr {x i : G} (hx : ∃ w ∈ W, x ∈ C.cell w) (hi : i ∈ C.I) :
      ∃ w ∈ W, x * i ∈ C.cell w := by
    obtain ⟨w, hw, h⟩ := hx
    exact ⟨w, hw, cell_mul_iwahori C w h hi⟩
  have hs' {x : G} {i} (hx : ∃ w ∈ W, x ∈ C.cell w) (hi : i ∈ T) :
      ∃ w ∈ W, x * (C.lift (S i) : G) ∈ C.cell w := by
    obtain ⟨w, hW, h⟩ := hx
    have hm : S i ∈ W := by rw [hw]; exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    rcases (hprod w i).2
        (Set.mul_mem_mul h (DoubleCoset.mem_doubleCoset_self C.I C.I (C.lift (S i) : G))) with h' | h'
    · exact ⟨_, W.mul_mem hW hm, h'⟩
    · exact ⟨w, hW, h'⟩
  constructor
  · intro hx
    refine Subgroup.closure_induction_right (p := fun x _ => ∃ w ∈ W, x ∈ C.cell w)
      ?_ ?_ ?_ hx
    · exact ⟨1, W.one_mem, (mem_cell_iff C _ _).2
        ⟨(C.lift 1 : G)⁻¹, C.I.inv_mem (lift_one C), 1, C.I.one_mem, by simp⟩⟩
    · rintro x _ y (hy | ⟨i, hi, rfl⟩) hx
      · exact hr hx hy
      · exact hs' hx hi
    · rintro x _ y (hy | ⟨i, hi, rfl⟩) hx
      · exact hr hx (C.I.inv_mem hy)
      · have he : (C.lift (S i) : G)⁻¹ =
            C.lift (S i) * ((C.lift (S i) : G) ^ 2)⁻¹ := by
          simp [pow_two, mul_inv_rev, ← mul_assoc]
        change ∃ w ∈ W, x * (C.lift (S i) : G)⁻¹ ∈ C.cell w
        rw [he, ← mul_assoc]
        exact hr (hs' hx hi) (C.I.inv_mem (lift_simple_sq C i))
  · rintro ⟨w, hW, hx⟩
    suffices h : ∀ w ∈ W, C.cell w ⊆ P from h w hW hx
    rw [hw]
    intro w hw'
    refine Subgroup.closure_induction_right (p := fun w _ => C.cell w ⊆ P) ?_ ?_ ?_ hw'
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_cell_iff C 1 x).1 hx
      exact P.mul_mem (P.mul_mem (hI ha) (hI (lift_one C))) (hI hb)
    · rintro w _ _ ⟨i, hi, rfl⟩ h x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hprod w i).1 hx
      obtain ⟨c, hc, d, hd, rfl⟩ := (mem_cell_iff C (S i) b).1 hb
      exact P.mul_mem (h ha) (P.mul_mem (P.mul_mem (hI hc) (hl hi)) (hI hd))
    · rintro w _ _ ⟨i, hi, rfl⟩ h x hx
      rw [C.coxeter.coxeter.inv_simple] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (hprod w i).1 hx
      obtain ⟨c, hc, d, hd, rfl⟩ := (mem_cell_iff C (S i) b).1 hb
      exact P.mul_mem (h ha) (P.mul_mem (P.mul_mem (hI hc) (hl hi)) (hI hd))

variable {K' : Type u} [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] {D' : BasedRootDatum.{u}} {M' : Model D'}
  {G' Wf' : Type u} [Group G'] [Group Wf'] {j' : G' →* FieldPoints M' K'}
  {V' : Type u} {J' : Type v} [AddCommGroup V'] [Module ℚ V']
  {A' : ApartmentRoots ℚ V' J'} {p' : V'}
  (C' : LocalComparison (j := j') (Wf := Wf') A' p')

theorem image_mem_cell {φ : G →* G'} {w : A.affineWeylGroup} {w' : A'.affineWeylGroup}
    (hI : C'.I.comap φ = C.I)
    (hL : φ (C.lift w) * (C'.lift w' : G')⁻¹ ∈ C'.T₀)
    {x : G} (hx : x ∈ C.cell w) : φ x ∈ C'.cell w' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_cell_iff C w x).1 hx
  have ha' : φ a ∈ C'.I := by rw [← hI] at ha; exact ha
  have hb' : φ b ∈ C'.I := by rw [← hI] at hb; exact hb
  let t := φ (C.lift w) * (C'.lift w' : G')⁻¹
  refine (mem_cell_iff C' w' _).2 ⟨φ a * t, C'.I.mul_mem ha' (unitTorus_le_iwahori C' hL),
    φ b, hb', ?_⟩
  simp [t, mul_assoc]

theorem parahoric_pullback {q q' : ℕ} (B : C.Bruhat q) (B' : C'.Bruhat q')
    {φ : G →* G'} (d : A.SimpleWall p ≃ A'.SimpleWall p')
    (f : A.affineWeylGroup ≃* A'.affineWeylGroup)
    (hs : ∀ i, f (A.simpleAffineReflection p i) = A'.simpleAffineReflection p' (d i))
    (hI : C'.I.comap φ = C.I) (hG : C'.G₀.comap φ = C.G₀)
    (hl : ∀ w, φ (C.lift w) * (C'.lift (f w) : G')⁻¹ ∈ C'.T₀)
    (T : Set (A.SimpleWall p)) :
    (parahoric C' (d '' T)).comap φ = parahoric C T := by
  have hW : (wallSubgroup T).map f.toMonoidHom = wallSubgroup (d '' T) := by
    rw [wallSubgroup, wallSubgroup, MonoidHom.map_closure, Set.image_image, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => hs i
  have hm w : f w ∈ wallSubgroup (d '' T) ↔ w ∈ wallSubgroup T := by
    rw [← hW]
    constructor
    · rintro ⟨v, hv, he⟩
      exact f.injective he ▸ hv
    · exact fun h => ⟨w, h, rfl⟩
  ext x
  change φ x ∈ parahoric C' (d '' T) ↔ x ∈ parahoric C T
  rw [mem_parahoric_iff_cell C B, mem_parahoric_iff_cell C' B']
  constructor
  · rintro ⟨w', hw', hx⟩
    have hg : x ∈ C.G₀ := by
      rw [← hG]
      change φ x ∈ (C'.G₀ : Set G')
      rw [← B'.cover]
      exact Set.mem_iUnion.mpr ⟨w', hx⟩
    change x ∈ (C.G₀ : Set G) at hg
    rw [← B.cover] at hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    have hf := image_mem_cell C C' hI (hl w) hw
    have he : f w = w' := by
      by_contra hne
      exact Set.disjoint_left.mp (B'.disjoint hne) hf hx
    exact ⟨w, (hm w).1 (he.symm ▸ hw'), hw⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨f w, (hm w).2 hw, image_mem_cell C C' hI (hl w) hx⟩


def markedTransport {q q' : ℕ} (B : C.Bruhat q) (B' : C'.Bruhat q')
    {φ : G →* G'} {e : V ≃ᵃ[ℚ] V'} (d : WallComparison A A' p p' e)
    (hI : C'.I.comap φ = C.I) (hG : C'.G₀.comap φ = C.G₀)
    (hl : ∀ w, φ (C.lift w) * (C'.lift (ordinaryLabels d w) : G')⁻¹ ∈ C'.T₀) :
    MarkedTransport C C' φ e where
  wall := simpleWalls d
  ordinary := ordinaryLabels d
  wall_value i := d.equation i.val
  vertex := vertex_image d
  label := ordinaryLabels_apply d
  simple i := by
    rw [C.coxeter.simple_eq, C'.coxeter.simple_eq]
    exact ordinaryLabels_simple d i
  lift := hl
  iwahori := hI
  group := hG
  face := parahoric_pullback C C' B B' (simpleWalls d) (ordinaryLabels d)
    (ordinaryLabels_simple d) hI hG hl

/-- The unit torus factor gives surjectivity on the type-preserving chambers. -/
theorem central_chamber_onto {φ : G →* G'}
    (h : ∀ y, y ∈ C'.G₀ ↔ ∃ (x : G) (t : C'.T₀), y = φ x * t)
    (h₀ : C.G₀ = ⊤) (y : C'.G₀) :
    ∃ x : C.G₀, (QuotientGroup.mk (φ x : G') : G' ⧸ C'.I) = QuotientGroup.mk (y : G') := by
  obtain ⟨x, t, he⟩ := (h y).1 y.property
  refine ⟨⟨x, by rw [h₀]; exact Subgroup.mem_top x⟩, ?_⟩
  apply QuotientGroup.eq.mpr
  change (φ x)⁻¹ * (y : G') ∈ C'.I
  rw [he, inv_mul_cancel_left]
  exact unitTorus_le_iwahori C' t.property



theorem transport_coset_eq {φ : G →* G'} {e : V ≃ᵃ[ℚ] V'}
    (d : MarkedTransport C C' φ e) (T : Set (A.SimpleWall p)) (g h : G) :
    (QuotientGroup.mk (φ g) : G' ⧸ parahoric C' (d.wall '' T)) = QuotientGroup.mk (φ h) ↔
      (QuotientGroup.mk g : G ⧸ parahoric C T) = QuotientGroup.mk h := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul, ← d.face T]
  rfl

end Groups

section Central

open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D D' : BasedRootDatum.{u}} {M : Model D} {M' : Model D'}
  {G G' Wf Wf' : Type u} [Group G] [Group G'] [Group Wf] [Group Wf']
  {j : G →* FieldPoints M K} {j' : G' →* FieldPoints M' K}
  {V V' : Type u} {J J' : Type v} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup V'] [Module ℚ V'] {A : ApartmentRoots ℚ V J} {A' : ApartmentRoots ℚ V' J'}
  {p : V} {p' : V'}
  {C : LocalComparison (j := j) (Wf := Wf) A p} {C' : LocalComparison (j := j') (Wf := Wf') A' p'}
  {c : MarkedCentralCover M M'} {φ : G →* G'} {e : V ≃ₗ[ℚ] V'}

theorem central_markedTransport {q q' : ℕ} (B : C.Bruhat q) (B' : C'.Bruhat q')
    (h : CentralComparison c φ C C' e) (hp : p' = e p) (h₀ : C.G₀ = ⊤) :
    Nonempty (MarkedTransport C C' φ e.toAffineEquiv) := by
  obtain ⟨_, hI, _, hN, _, _, hA, hG, _, b, _, hr, hc⟩ := h
  let d := linearWallComparison e b hp hr hc
  have hg : C'.G₀.comap φ = C.G₀ := by
    rw [h₀]
    apply top_unique
    intro g _
    exact (hG (φ g)).2 ⟨g, 1, by simp⟩
  refine ⟨markedTransport C C' B B' d hI hg fun w => ?_⟩
  have hn : φ (C.lift w) ∈ C'.N := by
    change (C.lift w : G) ∈ C'.N.comap φ
    rw [hN]
    exact (C.lift w).property
  let n : C'.N := ⟨φ (C.lift w), hn⟩
  apply lift_difference C' n (ordinaryLabels d w)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change C'.affine n (e.toAffineEquiv x) = (ordinaryLabels d w).val (e.toAffineEquiv x)
  rw [ordinaryLabels_apply d w x]
  have hx := hA (C.lift w) n rfl x
  rw [C.lift_label w] at hx
  exact hx.symm

theorem central_apartment_isometry [Fintype J] [Fintype J'] {r : RealCoordinates V}
    {r' : RealCoordinates V'} (hr : RootCoordinates A r) (hr' : RootCoordinates A' r')
    (h : CentralComparison c φ C C' e) :
    Isometry (realAffine r r' e.toAffineEquiv) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, b, _, hb, _⟩ := h
  exact realAffine_isometry hr hr' b hb

end Central

section Scalar

universe u v

variable {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {G G' Wf : Type u} [Group G] [Group G'] [Group Wf]
  {j : G →* FieldPoints M F} {j' : G' →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p} {C' : LocalComparison (j := j') (Wf := Wf) A p}
  {f : F →+* K} {s : G →* G'}

def scalar_markedTransport {q q' : ℕ} (B : C.Bruhat q) (B' : C'.Bruhat q')
    (h : ScalarComparison f s C C') : MarkedTransport C C' s 1 := by
  obtain ⟨_, _, hI, _, _, hG, _, _, _, hL, _, _⟩ := h
  exact
    { wall := Equiv.refl _
      ordinary := MulEquiv.refl _
      wall_value := fun _ _ => rfl
      vertex := fun _ _ hv => hv
      label := fun _ _ => rfl
      simple := fun i => by rw [C.coxeter.simple_eq, C'.coxeter.simple_eq]; rfl
      lift := hL
      iwahori := hI
      group := hG
      face := parahoric_pullback C C' B B' (Equiv.refl _) (MulEquiv.refl _) (fun _ => rfl) hI hG hL }

theorem scalar_apartment_eq (r : RealCoordinates V) (x : EuclideanApartment V) :
    realAffine r r 1 x = x := by
  simp [realAffine, AffineEquiv.one_def]

end Scalar

section Coefficients

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

private theorem simpleWall_hyperplane_injective :
    Function.Injective (fun a : A.SimpleWall p => A.wallHyperplane a.val) := by
  intro a b h
  by_contra! hne
  obtain ⟨_, x, hx, ho⟩ := a.property
  have hne' : b.val ≠ a.val := fun he => hne (Subtype.ext he.symm)
  change A.wallHyperplane a.val = A.wallHyperplane b.val at h
  have hx' : x ∈ A.wallHyperplane b.val := by rw [← h]; exact hx
  exact (ne_of_gt (ho b.val b.property.1 hne')) hx'

theorem lengthZero_wallPerm_injective (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0)
    (Q : C.TypeQuotient) : Function.Injective Q.wallPerm := by
  have hk (ω : alcoveStabilizer A (A.alcove p)) (hω : Q.wallPerm ω = 1) : ω = 1 := by
    let g := ω.val.val
    obtain ⟨d⟩ := symmetries_alcove C.geometry
      (C.geometry.extended_symmetries ω.val.property) ω.property
    have hd (i : A.SimpleWall p) : simpleWalls d i = i := by
      apply simpleWall_hyperplane_injective
      have h := Q.wall_action ω i
      rw [hω] at h
      exact (walls_image d i.val).symm.trans h
    have hgen : ∀ n : A.affineWeylGroup, Commute g n.val := by
      intro n
      refine C.coxeter.coxeter.simple_induction (p := fun w : A.affineWeylGroup => Commute g w.val)
        n ?_ (Commute.one_right _) ?_
      · intro i
        have hh := conjugacy_reflection d i.val
        have hdi := congrArg Subtype.val (hd i)
        change d.walls i.val = i.val at hdi
        rw [hdi] at hh
        rw [C.coxeter.simple_eq]
        change g * A.reflection i.val = A.reflection i.val * g
        have he : g * A.reflection i.val * g⁻¹ = A.reflection i.val := hh
        exact mul_inv_eq_iff_eq_mul.mp he
      · exact fun x y hx hy => hx.mul_right hy
    have hg : g = 1 := affine_centralizer_trivial hS g fun a =>
      hgen ⟨A.reflection a, Subgroup.subset_closure ⟨a, rfl⟩⟩
    exact Subtype.ext (Subtype.ext hg)
  intro a b h
  have hab : Q.wallPerm (a * b⁻¹) = 1 := by simp [h]
  exact mul_inv_eq_one.mp (hk _ hab)

private theorem mem_map_automorphism_iff (H : Subgroup G) (s : MulAut G)
    (hs : H.map s.toMonoidHom = H) (x : G) : s x ∈ H ↔ x ∈ H := by
  constructor
  · intro hx
    rw [← hs] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact s.injective he ▸ hy
  · intro hx
    rw [← hs]
    exact ⟨x, hx, rfl⟩

private def automorphismOnNormalizer (s : MulAut G) (e : V ≃ᵃ[ℚ] V)
    (h : AutomorphismComparison C s e) : C.N ≃* C.N :=
  (C.N.equivMapOfInjective s.toMonoidHom s.injective).trans (MulEquiv.subgroupCongr h.2.1)

private theorem normalizer_conj (s : MulAut G) (e : V ≃ᵃ[ℚ] V)
    (h : AutomorphismComparison C s e) (n : C.N) :
    C.affine (automorphismOnNormalizer s e h n) = e * C.affine n * e⁻¹ :=
  h.2.2.2.2.2.2.1 n _ rfl

theorem coefficient_normalizes_ordinary {q : ℕ} (B : C.Bruhat q)
    {s : MulAut G} {e : V ≃ᵃ[ℚ] V} (h : AutomorphismComparison C s e) :
    (∀ w ∈ A.affineWeylGroup, e * w * e⁻¹ ∈ A.affineWeylGroup) ∧
    (∀ w ∈ A.affineWeylGroup, e⁻¹ * w * e ∈ A.affineWeylGroup) := by
  constructor
  · intro w hw
    obtain ⟨w', he, _⟩ := h.2.2.2.2.2.2.2 ⟨w, hw⟩
    exact he ▸ w'.property
  · intro w hw
    let n := C.lift ⟨w, hw⟩
    let f := automorphismOnNormalizer s e h
    let m := f.symm n
    have hm : s (m : G) = (n : G) := congrArg Subtype.val (f.apply_symm_apply n)
    have hm₀ : (m : G) ∈ C.G₀ :=
      (mem_map_automorphism_iff C.G₀ s h.2.2.2.1 m).1 (hm.symm ▸ lift_mem_ordinary C ⟨w, hw⟩)
    have hm' : C.affine m ∈ A.affineWeylGroup := by
      have hh : (m : G) ∈ C.G₀ ⊓ C.N := ⟨hm₀, m.property⟩
      rw [B.ordinary_normalizer] at hh
      obtain ⟨x, hx, he⟩ := hh
      exact (Subtype.ext he : x = m) ▸ hx
    have hconj := normalizer_conj s e h m
    rw [show f m = n from f.apply_symm_apply n, show C.affine n = w from C.lift_label _] at hconj
    have hz := congrArg (fun z : V ≃ᵃ[ℚ] V => e⁻¹ * z * e) hconj
    have he : e⁻¹ * w * e = C.affine m := by simpa [mul_assoc] using hz
    exact he.symm ▸ hm'

private theorem affine_eq_of_conj
    (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0) (e f : V ≃ᵃ[ℚ] V)
    (he : ∀ w ∈ A.affineWeylGroup, e * w * e⁻¹ = f * w * f⁻¹) : e = f := by
  have h1 : f⁻¹ * e = 1 := affine_centralizer_trivial hS _ fun a => by
    let w := A.reflection a
    have h := he w (Subgroup.subset_closure ⟨a, rfl⟩)
    have h' := congrArg (fun z => f⁻¹ * z * e) h
    show (f⁻¹ * e) * w = w * (f⁻¹ * e)
    simpa [mul_assoc] using h'
  exact (eq_of_inv_mul_eq_one h1).symm

theorem coefficient_affine_mul {Γ : Type u} [Group Γ] (ρ : Γ →* MulAut G)
    (e : Γ → V ≃ᵃ[ℚ] V) (h : ∀ σ, AutomorphismComparison C (ρ σ) (e σ))
    (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0) (σ τ : Γ) :
    e (σ * τ) = e σ * e τ := by
  apply affine_eq_of_conj hS
  intro w hw
  let n := C.lift ⟨w, hw⟩
  let nτ := automorphismOnNormalizer (ρ τ) (e τ) (h τ) n
  let nστ := automorphismOnNormalizer (ρ σ) (e σ) (h σ) nτ
  let n' := automorphismOnNormalizer (ρ (σ * τ)) (e (σ * τ)) (h (σ * τ)) n
  have he : n' = nστ := Subtype.ext (by
    change ρ (σ * τ) (n : G) = ρ σ (ρ τ (n : G))
    rw [map_mul]
    rfl)
  have h' := normalizer_conj (ρ (σ * τ)) (e (σ * τ)) (h (σ * τ)) n
  change C.affine n' = _ at h'
  rw [he, C.lift_label] at h'
  have hσ := normalizer_conj (ρ σ) (e σ) (h σ) nτ
  have hτ := normalizer_conj (ρ τ) (e τ) (h τ) n
  change C.affine nστ = _ at hσ
  change C.affine nτ = _ at hτ
  rw [hτ, C.lift_label] at hσ
  simpa [hσ, mul_assoc] using h'.symm

private def coefficientAffine {Γ : Type u} [Group Γ] (ρ : Γ →* MulAut G)
    (e : Γ → V ≃ᵃ[ℚ] V) (h : ∀ σ, AutomorphismComparison C (ρ σ) (e σ))
    (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0) : Γ →* (V ≃ᵃ[ℚ] V) where
  toFun := e
  map_one' := by
    have he := coefficient_affine_mul ρ e h hS 1 1
    rw [one_mul] at he
    exact mul_left_cancel (show e 1 * e 1 = e 1 * 1 by simpa using he.symm)
  map_mul' := coefficient_affine_mul ρ e h hS

def coefficient_markedTransport {q : ℕ} (B : C.Bruhat q)
    {s : MulAut G} {e : V ≃ᵃ[ℚ] V} (h : AutomorphismComparison C s e)
    (d : WallComparison A A p p e) : MarkedTransport C C s.toMonoidHom e := by
  have hi : C.I.comap s.toMonoidHom = C.I :=
    Subgroup.ext (mem_map_automorphism_iff C.I s h.1)
  have hg : C.G₀.comap s.toMonoidHom = C.G₀ :=
    Subgroup.ext (mem_map_automorphism_iff C.G₀ s h.2.2.2.1)
  refine markedTransport C C B B d hi hg (fun w => ?_)
  obtain ⟨v, hv, hl⟩ := h.2.2.2.2.2.2.2 w
  have he : v = ordinaryLabels d w := Subtype.ext (by
    rw [hv]
    rfl)
  exact he ▸ hl


private theorem normalizer_conjugates_extended {s : MulAut G} {e : V ≃ᵃ[ℚ] V}
    (hE : C.affine.range = A.extendedAffineWeylGroup) (h : AutomorphismComparison C s e) :
    ∀ w, e * w * e⁻¹ ∈ A.extendedAffineWeylGroup ↔ w ∈ A.extendedAffineWeylGroup := by
  intro w
  rw [← hE]
  constructor
  · rintro ⟨n, hn⟩
    let f := automorphismOnNormalizer s e h
    let m := f.symm n
    refine ⟨m, ?_⟩
    have he := normalizer_conj s e h m
    change C.affine (f m) = _ at he
    rw [f.apply_symm_apply n, hn] at he
    have hh := congrArg (fun v : V ≃ᵃ[ℚ] V => e⁻¹ * v * e) he
    simpa [mul_assoc] using hh.symm
  · rintro ⟨n, rfl⟩
    exact ⟨_, normalizer_conj s e h n⟩

private theorem image_conjugacy {e g : V ≃ᵃ[ℚ] V} {U : Set V} (h : e '' U = U)
    (h' : g '' U = U) : (e * g * e⁻¹ : V ≃ᵃ[ℚ] V) '' U = U := by
  have he : (e⁻¹ : V ≃ᵃ[ℚ] V) '' U = U := by
    nth_rw 1 [← h]
    rw [Set.image_image]
    simp [AffineEquiv.inv_def]
  simp only [AffineEquiv.coe_mul, Set.image_comp, he, h', h]

private def quotientConjugacy {s : MulAut G} {e : V ≃ᵃ[ℚ] V}
    (hE : C.affine.range = A.extendedAffineWeylGroup) (h : AutomorphismComparison C s e) :
    MulAut (alcoveStabilizer A (A.alcove p)) where
  toFun ω := ⟨⟨e * ω.val.val * e⁻¹, (normalizer_conjugates_extended hE h _).2 ω.val.property⟩,
    image_conjugacy h.2.2.2.2.2.1 ω.property⟩
  invFun ω :=
    have h' : e⁻¹ * ω.val.val * e ∈ A.extendedAffineWeylGroup := by
      apply (normalizer_conjugates_extended hE h _).1
      simp [mul_assoc, ω.val.property]
    have h'' : (e⁻¹ : V ≃ᵃ[ℚ] V) '' A.alcove p = A.alcove p := by
      nth_rw 1 [← h.2.2.2.2.2.1]
      rw [Set.image_image]
      simp [AffineEquiv.inv_def]
    ⟨⟨e⁻¹ * ω.val.val * e, h'⟩, by
      change (e⁻¹ * ω.val.val * e : V ≃ᵃ[ℚ] V) '' A.alcove p = A.alcove p
      simpa only [inv_inv] using image_conjugacy h'' ω.property⟩
  left_inv ω := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  right_inv ω := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  map_mul' ω ν := Subtype.ext (Subtype.ext (by simp [mul_assoc]))

private def typeLabel (Q : C.TypeQuotient) : G →* alcoveStabilizer A (A.alcove p) :=
  letI := Q.normal
  Q.quotient.toMonoidHom.comp (QuotientGroup.mk' C.G₀)

private theorem typeLabel_lift (Q : C.TypeQuotient) (ω : alcoveStabilizer A (A.alcove p)) :
    typeLabel Q (Q.lift ω : G) = ω := Q.quotient_lift ω

private theorem typeLabel_eq_one (Q : C.TypeQuotient) (g : G) : typeLabel Q g = 1 ↔ g ∈ C.G₀ := by
  let := Q.normal
  change Q.quotient (QuotientGroup.mk g) = 1 ↔ _
  rw [← map_one Q.quotient, Q.quotient.injective.eq_iff, QuotientGroup.eq_one_iff]

private theorem quotient_naturality (Q : C.TypeQuotient)
    {s : MulAut G} {e : V ≃ᵃ[ℚ] V} (hE : C.affine.range = A.extendedAffineWeylGroup)
    (h : AutomorphismComparison C s e) :
    TypeQuotientTransport Q Q s.toMonoidHom (quotientConjugacy hE h).toMonoidHom := by
  let := Q.normal
  let β := quotientConjugacy hE h
  have hL (ω : alcoveStabilizer A (A.alcove p)) :
      s (Q.lift ω) * (Q.lift (β ω) : G)⁻¹ ∈ C.T₀ := by
    let n := automorphismOnNormalizer s e h (Q.lift ω)
    apply (mem_unitTorus_iff C (n * (Q.lift (β ω))⁻¹)).2
    rw [map_mul, map_inv, Q.affine_lift]
    have he := normalizer_conj s e h (Q.lift ω)
    change C.affine n = _ at he
    rw [Q.affine_lift] at he
    rw [he]
    change (e * ω.val.val * e⁻¹) * (e * ω.val.val * e⁻¹)⁻¹ = 1
    exact mul_inv_cancel _
  refine ⟨fun g => ?_, hL⟩
  change typeLabel Q (s g) = β (typeLabel Q g)
  let ω := typeLabel Q g
  have hz : typeLabel Q (s g) = typeLabel Q (s (Q.lift ω)) := by
    have hm : g * (Q.lift ω : G)⁻¹ ∈ C.G₀ := (typeLabel_eq_one Q _).1 (by
      rw [map_mul, map_inv, typeLabel_lift]; exact mul_inv_cancel _)
    have hh := (mem_map_automorphism_iff C.G₀ s h.2.2.2.1 _).2 hm
    have hc := (typeLabel_eq_one Q _).2 hh
    rw [map_mul, map_inv, map_mul, map_inv] at hc
    exact mul_inv_eq_one.mp hc
  rw [hz]
  have hh : typeLabel Q (s (Q.lift ω) * (Q.lift (β ω) : G)⁻¹) = 1 :=
    (typeLabel_eq_one Q _).2 (le_sup_left (α := Subgroup G) (unitTorus_le_iwahori C (hL ω)))
  rw [map_mul, map_inv, typeLabel_lift] at hh
  exact mul_inv_eq_one.mp hh

theorem coefficientTransport [Fintype J] {q : ℕ} (B : C.Bruhat q)
    (hR : A.ReducedDirections) (hS : ∀ x, (∀ i, A.root i x = 0) → x = 0)
    (Q : C.TypeQuotient) (hE : C.affine.range = A.extendedAffineWeylGroup)
    {Γ : Type u} [Group Γ] (ρ : Γ →* MulAut G) (e : Γ → V ≃ᵃ[ℚ] V)
    (h : ∀ σ, AutomorphismComparison C (ρ σ) (e σ)) {r : RealCoordinates V}
    (hr : RootCoordinates A r) : Nonempty (CoefficientTransport C Q ρ e r) := by
  classical
  let E := coefficientAffine ρ e h hS
  have hd σ := normalizer_wallComparison C.geometry hR hS (e σ) (h σ).2.2.2.2.2.1
    (coefficient_normalizes_ordinary B (h σ)).1 (coefficient_normalizes_ordinary B (h σ)).2
  let d (σ : Γ) := (hd σ).some
  let types : Γ →* Equiv.Perm (A.SimpleWall p) :=
    { toFun := fun σ => simpleWalls (d σ)
      map_one' := by
        apply Equiv.ext
        intro i
        apply simpleWall_hyperplane_injective
        change A.wallHyperplane ((d 1).walls i.val) = A.wallHyperplane i.val
        rw [← walls_image (d 1) i.val]
        have he : e 1 = 1 := E.map_one
        rw [he]
        exact Set.image_id _
      map_mul' := fun σ τ => by
        have hm : e (σ * τ) = e σ * e τ := E.map_mul σ τ
        apply Equiv.ext
        intro i
        apply simpleWall_hyperplane_injective
        change A.wallHyperplane ((d (σ * τ)).walls i.val) =
          A.wallHyperplane ((d σ).walls ((d τ).walls i.val))
        rw [← walls_image (d (σ * τ)), ← walls_image (d σ), ← walls_image (d τ), hm, Set.image_image]
        rfl }
  let β : Γ →* MulAut (alcoveStabilizer A (A.alcove p)) :=
    { toFun := fun σ => quotientConjugacy hE (h σ)
      map_one' := by
        apply MulEquiv.ext
        intro ω
        apply Subtype.ext
        apply Subtype.ext
        change e 1 * ω.val.val * (e 1)⁻¹ = ω.val.val
        rw [show e 1 = 1 from E.map_one]
        simp
      map_mul' := fun σ τ => by
        apply MulEquiv.ext
        intro ω
        apply Subtype.ext
        apply Subtype.ext
        change e (σ * τ) * ω.val.val * (e (σ * τ))⁻¹ =
          e σ * (e τ * ω.val.val * (e τ)⁻¹) * (e σ)⁻¹
        rw [show e (σ * τ) = e σ * e τ from E.map_mul σ τ]
        simp [mul_assoc] }
  refine ⟨⟨E, fun _ => rfl, types, fun σ => ?_, fun σ => coefficient_markedTransport B (h σ) (d σ),
    fun _ => rfl, β, fun _ _ => rfl, fun σ => quotient_naturality Q hE (h σ), fun σ ω => ?_⟩⟩
  · exact realAffine_isometry_of_symmetry hr hR ⟨(d σ).walls, fun a => ⟨(d σ).equation a, (d σ).coroot a⟩⟩
  · apply Equiv.ext
    intro i
    obtain ⟨i, rfl⟩ := (types σ).surjective i
    apply simpleWall_hyperplane_injective
    have ha := Q.wall_action (β σ ω) (types σ i)
    have hb := Q.wall_action ω i
    have hh (a : A.SimpleWall p) : e σ '' A.wallHyperplane a.val =
        A.wallHyperplane (types σ a).val := walls_image (d σ) a.val
    have ht : (types σ * Q.wallPerm ω * (types σ)⁻¹) (types σ i) = types σ (Q.wallPerm ω i) := by
      simp
    change A.wallHyperplane (Q.wallPerm (β σ ω) (types σ i)).val =
      A.wallHyperplane ((types σ * Q.wallPerm ω * (types σ)⁻¹) (types σ i)).val
    rw [ht, ← ha, ← hh i, ← hh (Q.wallPerm ω i), ← hb]
    change ((e σ * ω.val.val * (e σ)⁻¹ : V ≃ᵃ[ℚ] V) '' (e σ '' A.wallHyperplane i.val)) =
      e σ '' (ω.val.val '' A.wallHyperplane i.val)
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    simp [AffineEquiv.coe_mul, AffineEquiv.inv_def]


end Coefficients


section Weights

variable {V V' B B' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']

def transportWeights (d : B ≃ B') (t : Weights B) : Weights B' :=
  ⟨t.val ∘ d.symm, ⟨fun i => t.property.1 (d.symm i),
    (finsum_comp_equiv d.symm).trans t.property.2⟩⟩

theorem transportWeights_apply (d : B ≃ B') (t : Weights B) (i : B) :
    (transportWeights d t).val (d i) = t.val i := by simp [transportWeights]

theorem transportWeights_cotype (d : B ≃ B') (t : Weights B) :
    cotype (transportWeights d t) = d '' cotype t := by
  ext i
  obtain ⟨i, rfl⟩ := d.surjective i
  simp [cotype, transportWeights_apply]

theorem transportWeights_trans {B'' : Type*} (d : B ≃ B') (d' : B' ≃ B'') (t : Weights B) :
    transportWeights d' (transportWeights d t) = transportWeights (d.trans d') t := rfl

theorem transportWeights_rational {r : RealCoordinates V} {r' : RealCoordinates V'}
    (d : B ≃ B') (t : Weights B) [Fintype B] [Fintype B']
    (a : B → V) (a' : B' → V') (e : V ≃ᵃ[ℚ] V') (h : ∀ i, a' (d i) = e (a i)) :
    simplexPoint r' a' (transportWeights d t) = realAffine r r' e (simplexPoint r a t) := by
  let L := r'.toLinearMap.comp ((e.linear.toLinearMap.baseChange ℝ).comp r.symm.toLinearMap)
  let b := rationalPoint r' (e 0)
  have hL (x : EuclideanApartment V) : realAffine r r' e x = L x + b :=
    map_add r' _ _
  have ht : ∑ i, t.val i = 1 := by simpa [finsum_eq_sum_of_fintype] using t.property.2
  unfold simplexPoint
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hL, map_sum]
  rw [← Equiv.sum_comp d (fun j => (transportWeights d t).val j • rationalPoint r' (a' j))]
  have he i : rationalPoint r' (a' (d i)) = L (rationalPoint r (a i)) + b := by
    rw [h, ← realAffine_rational (r := r) e, hL]
  simp only [transportWeights_apply, he, smul_add, Finset.sum_add_distrib, map_smul,
    ← Finset.sum_smul, ht, one_smul]

end Weights


section Families

universe u v

open IntegralSemisimpleModel (Integers IntegralGroup integralSpec)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open ExceptionalIwahoriCongruence (changeRingHom)
open ExceptionalValuedTorusNormalizer (invariantApartment)
open AdjointRepresentation (GroupPoints)

private theorem apartmentIsometries {V J : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype J] {A : ApartmentRoots ℚ V J} {p : V} {r : RealCoordinates V}
    (h : AlcoveGeometry A p) (hr : RootCoordinates A r) (hR : A.ReducedDirections) :
    ApartmentIsometries (A := A) r :=
  ⟨fun w => realAffine_isometry_of_symmetry hr hR (h.ordinary_symmetries w.property),
    fun w => realAffine_isometry_of_symmetry hr hR (h.extended_symmetries w.property)⟩

private theorem split_local_apartments
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (X : SplitLevel F c p p' e) (hp : p' = e p)
    [Fintype D.I] [Fintype E.I]
    (hs : ∀ x, (∀ i, (ApartmentRoots.split E.datum ℚ).root i x = 0) → x = 0)
    {r : RealCoordinates (ℚ ⊗[ℤ] D.Y)} {r' : RealCoordinates (ℚ ⊗[ℤ] E.Y)}
    (hr : RootCoordinates (ApartmentRoots.split D.datum ℚ) r)
    (hr' : RootCoordinates (ApartmentRoots.split E.datum ℚ) r') :
    SplitApartmentLevel X r r' := by
  have hR := split_roots_reduced D
  have hR' := split_roots_reduced E
  have hN : X.sc.affine.range = (ApartmentRoots.split D.datum ℚ).affineWeylGroup := by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := X.sc_points
    simpa using h
  have hN' : X.ad.affine.range = (ApartmentRoots.split E.datum ℚ).extendedAffineWeylGroup := by
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := X.ad_points
    simpa using h
  have h₀ := ordinary_eq_top X.sc hN
  obtain ⟨d⟩ := central_markedTransport X.sc_bruhat X.ad_bruhat X.central hp h₀
  exact ⟨apartmentIsometries X.sc.geometry hr hR, apartmentIsometries X.ad.geometry hr' hR',
    ⟨⟨d, central_apartment_isometry hr hr' X.central,
      central_chamber_onto X.sc X.ad X.central.2.2.2.2.2.2.2.1 h₀⟩⟩,
    ⟨lengthZero_wallPerm_injective hs X.typeQuotient, fun Γ _ ρ e' h =>
      coefficientTransport X.ad_bruhat hR' hs X.typeQuotient hN' ρ e' h hr'⟩⟩

private theorem split_apartment_comparisons : SplitApartmentComparisons.{u} := by
  intro F _ _ _ _ D E M M' c p p' e hs hp X
  classical
  let := D.finiteRoots
  let := E.finiteRoots
  let := Fintype.ofFinite D.I
  let := Fintype.ofFinite E.I
  have hS := split_roots_separate E hs
  have hS' : ∀ x, (∀ i, (ApartmentRoots.split D.datum ℚ).root i x = 0) → x = 0 := by
    have h := X.central
    obtain ⟨_, _, _, _, _, _, _, _, _, b, _, hr, _⟩ := h
    intro x hx
    apply e.injective
    rw [map_zero]
    apply hS
    intro j
    obtain ⟨i, rfl⟩ := b.surjective j
    exact (hr i x).trans (hx i)
  let r := rootCoordinates hS'
  let r' := rootCoordinates hS
  have hr := rootCoordinates_norm hS'
  have hr' := rootCoordinates_norm hS
  exact ⟨r, r', split_local_apartments X hp hS hr hr',
    fun _ _ _ _ _ Y => split_local_apartments Y hp hS hr hr'⟩

private theorem folded_apartment_comparisons : FoldedApartmentComparisons.{u} := by
  intro D E M M' c τ τ' A A' e hp
  classical
  let := folded_directions_finite
  let := Fintype.ofFinite FoldedRootDirection
  have hS := folded_roots_separate A
  have hS' := folded_roots_separate A'
  have hR := folded_roots_reduced A
  have hR' := folded_roots_reduced A'
  let r := rootCoordinates hS
  let r' := rootCoordinates hS'
  have hr := rootCoordinates_norm hS
  have hr' := rootCoordinates_norm hS'
  refine ⟨r, r', ?_⟩
  intro K _ _ _ _ G H Wf Wf' _ _ _ _ j j' C C' φ Q q q' B B' hc hN hN'
  have h₀ := ordinary_eq_top C hN
  obtain ⟨d⟩ := central_markedTransport B B' hc hp h₀
  exact ⟨apartmentIsometries C.geometry hr hR, apartmentIsometries C'.geometry hr' hR',
    ⟨⟨d, central_apartment_isometry hr hr' hc,
      central_chamber_onto C C' hc.2.2.2.2.2.2.2.1 h₀⟩⟩,
    ⟨lengthZero_wallPerm_injective hS' Q, fun Γ _ ρ e' h =>
      coefficientTransport B' hR' hS' Q (hN'.trans A'.affine_eq) ρ e' h hr'⟩⟩

private theorem scalar_apartment_comparisons : ScalarApartmentComparisons.{u} := by
  intro F K _ _ _ _ _ _ _ _ D M G H Wf _ _ _ j j' V J _ _ A p C C' f s q q' B B' h
  refine ⟨⟨scalar_markedTransport B B' h, rfl, rfl⟩, fun r => funext (scalar_apartment_eq r), ?_⟩
  intro Q Q' hq
  refine ⟨hq.1, fun ω => ⟨hq.2 ω, ?_⟩⟩
  apply Equiv.ext
  intro i
  apply simpleWall_hyperplane_injective
  exact (Q'.wall_action ω i).symm.trans (Q.wall_action ω i)

private theorem point_comparison_squares : PointComparisonSquares.{u} := by
  constructor
  · intro R S G H f a x
    change integralSpec.map a.op ≫ (x ≫ f.hom.hom) =
      (integralSpec.map a.op ≫ x) ≫ f.hom.hom
    exact (Category.assoc ..).symm
  · intro F k K _ _ _ _ _ G H f a x
    let m := (testSpec F).map (CommAlgCat.ofHom a).op
    change m ≫ (x ≫ f.hom.hom) = (m ≫ x) ≫ f.hom.hom
    exact (Category.assoc ..).symm


end Families

section Conditional

theorem splitApartmentComparisons_conditional.{u}
    (_ : CoxeterDoubleCosets.{u,u,u})
    (_ : ExceptionalAffineBruhat.E6CoweightClass)
    (_ : ExceptionalAffineBruhat.E6ProjectedLattices)
    (_ : LeftCosetIndex.{u})
    (_ : RamifiedAffineBruhatComparison.{u})
    (_ : RankOneDoubleCosetProduct.{u})
    (_ : RankOneWallConjugation.{u})
    (_ : RankOneWallMultiplication.{u})
    (_ : ResidueLayerCounts.{u})
    (_ : ResiduePowerCounts.{u})
    (_ : SplitAffineBruhatComparison.{u}) :
    SplitApartmentComparisons.{u} := split_apartment_comparisons

theorem foldedApartmentComparisons_conditional.{u}
    (_ : CoxeterDoubleCosets.{u,u,u})
    (_ : ExceptionalAffineBruhat.E6CoweightClass)
    (_ : ExceptionalAffineBruhat.E6ProjectedLattices)
    (_ : LeftCosetIndex.{u})
    (_ : RamifiedAffineBruhatComparison.{u})
    (_ : RankOneDoubleCosetProduct.{u})
    (_ : RankOneWallConjugation.{u})
    (_ : RankOneWallMultiplication.{u})
    (_ : ResidueLayerCounts.{u})
    (_ : ResiduePowerCounts.{u})
    (_ : SplitAffineBruhatComparison.{u}) :
    FoldedApartmentComparisons.{u} := folded_apartment_comparisons

theorem scalarApartmentComparisons_conditional.{u}
    (_ : CoxeterDoubleCosets.{u,u,u})
    (_ : ExceptionalAffineBruhat.E6CoweightClass)
    (_ : ExceptionalAffineBruhat.E6ProjectedLattices)
    (_ : LeftCosetIndex.{u})
    (_ : RamifiedAffineBruhatComparison.{u})
    (_ : RankOneDoubleCosetProduct.{u})
    (_ : RankOneWallConjugation.{u})
    (_ : RankOneWallMultiplication.{u})
    (_ : ResidueLayerCounts.{u})
    (_ : ResiduePowerCounts.{u})
    (_ : SplitAffineBruhatComparison.{u}) :
    ScalarApartmentComparisons.{u} := scalar_apartment_comparisons

theorem pointComparisonSquares_conditional.{u}
    (_ : CoxeterDoubleCosets.{u,u,u})
    (_ : ExceptionalAffineBruhat.E6CoweightClass)
    (_ : ExceptionalAffineBruhat.E6ProjectedLattices)
    (_ : LeftCosetIndex.{u})
    (_ : RamifiedAffineBruhatComparison.{u})
    (_ : RankOneDoubleCosetProduct.{u})
    (_ : RankOneWallConjugation.{u})
    (_ : RankOneWallMultiplication.{u})
    (_ : ResidueLayerCounts.{u})
    (_ : ResiduePowerCounts.{u})
    (_ : SplitAffineBruhatComparison.{u}) :
    PointComparisonSquares.{u} := point_comparison_squares

end Conditional

end
end LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingTransport

universe v8_closure_427b4c01d1d5fb5a_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«foldedApartmentComparisons» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingTransport».«FoldedApartmentComparisons».{v8_closure_427b4c01d1d5fb5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«foldedApartmentComparisons_conditional».{v8_closure_427b4c01d1d5fb5a_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«pointComparisonSquares» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingTransport».«PointComparisonSquares».{v8_closure_427b4c01d1d5fb5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«pointComparisonSquares_conditional».{v8_closure_427b4c01d1d5fb5a_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«scalarApartmentComparisons» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingTransport».«ScalarApartmentComparisons».{v8_closure_427b4c01d1d5fb5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«scalarApartmentComparisons_conditional».{v8_closure_427b4c01d1d5fb5a_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«splitApartmentComparisons» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalBuildingTransport».«SplitApartmentComparisons».{v8_closure_427b4c01d1d5fb5a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalBuildingTransport».«splitApartmentComparisons_conditional».{v8_closure_427b4c01d1d5fb5a_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0, v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_427b4c01d1d5fb5a_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_427b4c01d1d5fb5a_u0})
