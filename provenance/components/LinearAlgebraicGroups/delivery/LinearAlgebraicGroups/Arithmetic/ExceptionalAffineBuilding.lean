import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import LinearAlgebraicGroups.Arithmetic.ExceptionalRealAlcove
import LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingActions
import LinearAlgebraicGroups.Arithmetic.ExceptionalBuildingTransport
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import LinearAlgebraicGroups.Geometry.Circumcenter
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

/-! Group-theoretic and metric steps of the affine building construction. -/

open Set
open scoped Pointwise

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

open LinearAlgebraicGroups.Specs.ExceptionalAffineBruhat
open LinearAlgebraicGroups.Specs.ExceptionalAffineBuilding
  (standardWallSubgroup faceSubgroup apartmentChambers)

universe uG uB uW

section Chambers

variable {G : Type uG} [Group G] {B : Type uB} {W : Type uW} [Group W]
  {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (I : Subgroup G) (lift : W → G)

private theorem doubleCoset_eq_subgroup (g : G) (hg : g ∈ I) :
    DoubleCoset.doubleCoset g I I = (I : Set G) := by
  ext x
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, ha, b, hb, hx⟩ => hx ▸ I.mul_mem (I.mul_mem ha hg) hb,
    fun hx => ⟨x * g⁻¹, I.mul_mem hx (I.inv_mem hg), 1, I.one_mem, by simp⟩⟩

omit [Group W] in
private theorem doubleCoset_mul_mem (w : W) {x i : G}
    (hx : x ∈ DoubleCoset.doubleCoset (lift w) I I) (hi : i ∈ I) :
    x * i ∈ DoubleCoset.doubleCoset (lift w) I I := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  exact DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * i, I.mul_mem hb hi, mul_assoc _ _ _⟩

/-- The simple-wall product formulas identify the generated face subgroup with the union
of the double cosets indexed by the corresponding Coxeter subgroup. -/
theorem faceSubgroup_eq_iUnion (J : Set B)
    (hone : lift 1 ∈ I) (hsq : ∀ j, lift (cs.simple j) ^ 2 ∈ I)
    (hup : ∀ w j, ¬cs.IsRightDescent w j →
      DoubleCoset.doubleCoset (lift w) I I * DoubleCoset.doubleCoset (lift (cs.simple j)) I I =
        DoubleCoset.doubleCoset (lift (w * cs.simple j)) I I)
    (hdown : ∀ w j, cs.IsRightDescent w j →
      DoubleCoset.doubleCoset (lift w) I I * DoubleCoset.doubleCoset (lift (cs.simple j)) I I =
        DoubleCoset.doubleCoset (lift (w * cs.simple j)) I I ∪
          DoubleCoset.doubleCoset (lift w) I I) :
    (faceSubgroup cs I lift J : Set G) =
      ⋃ w : standardWallSubgroup cs J, DoubleCoset.doubleCoset (lift w) I I := by
  classical
  let P := faceSubgroup cs I lift J
  let V := standardWallSubgroup cs J
  let D := fun w : W => DoubleCoset.doubleCoset (lift w) I I
  have hI : I ≤ P := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have hs {j : B} (hj : j ∈ J) : lift (cs.simple j) ∈ P :=
    Subgroup.subset_closure (Or.inr ⟨j, hj, rfl⟩)
  have hprod (w : W) (j : B) : D (w * cs.simple j) ⊆ D w * D (cs.simple j) ∧
      D w * D (cs.simple j) ⊆ D (w * cs.simple j) ∪ D w := by
    by_cases hd : cs.IsRightDescent w j
    · rw [show D w * D (cs.simple j) = D (w * cs.simple j) ∪ D w from hdown w j hd]
      exact ⟨subset_union_left, Subset.rfl⟩
    · rw [show D w * D (cs.simple j) = D (w * cs.simple j) from hup w j hd]
      exact ⟨Subset.rfl, subset_union_left⟩
  have hwall {x : G} {j : B} (hx : ∃ w : V, x ∈ D w) (hj : j ∈ J) :
      ∃ w : V, x * lift (cs.simple j) ∈ D w := by
    obtain ⟨w, hw⟩ := hx
    have h := (hprod w j).2
      (Set.mul_mem_mul hw (DoubleCoset.mem_doubleCoset_self I I (lift (cs.simple j))))
    rcases h with h | h
    · exact ⟨⟨w * cs.simple j, V.mul_mem w.property (Subgroup.subset_closure ⟨j, hj, rfl⟩)⟩, h⟩
    · exact ⟨w, h⟩
  have hright {x i : G} (hx : ∃ w : V, x ∈ D w) (hi : i ∈ I) :
      ∃ w : V, x * i ∈ D w := by
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, doubleCoset_mul_mem I lift w hw hi⟩
  ext x
  change x ∈ P ↔ x ∈ ⋃ w : V, D w
  rw [Set.mem_iUnion]
  constructor
  · intro hx
    refine Subgroup.closure_induction_right (p := fun x _ => ∃ w : V, x ∈ D w) ?_ ?_ ?_ hx
    · refine ⟨1, ?_⟩
      change (1 : G) ∈ D 1
      rw [show D 1 = (I : Set G) from doubleCoset_eq_subgroup I _ hone]
      exact I.one_mem
    · rintro x _ y (hy | ⟨j, hj, rfl⟩) hx
      · exact hright hx hy
      · exact hwall hx hj
    · rintro x _ y (hy | ⟨j, hj, rfl⟩) hx
      · exact hright hx (I.inv_mem hy)
      · have heq : (lift (cs.simple j))⁻¹ =
            lift (cs.simple j) * ((lift (cs.simple j)) ^ 2)⁻¹ := by
          simp [pow_two, mul_inv_rev, ← mul_assoc]
        change ∃ w : V, x * (lift (cs.simple j))⁻¹ ∈ D w
        rw [heq, ← mul_assoc]
        exact hright (hwall hx hj) (I.inv_mem (hsq j))
  · rintro ⟨w, hw⟩
    have hall : ∀ v ∈ V, D v ⊆ P := by
      intro v hv
      refine Subgroup.closure_induction_right (p := fun v _ => D v ⊆ P) ?_ ?_ ?_ hv
      · rw [show D 1 = (I : Set G) from doubleCoset_eq_subgroup I _ hone]
        exact hI
      · rintro v _ _ ⟨j, hj, rfl⟩ hv x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := (hprod v j).1 hx
        obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
        exact P.mul_mem (hv ha) (P.mul_mem (P.mul_mem (hI hc) (hs hj)) (hI hd))
      · rintro v _ _ ⟨j, hj, rfl⟩ hv x hx
        rw [cs.inv_simple] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := (hprod v j).1 hx
        obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
        exact P.mul_mem (hv ha) (P.mul_mem (P.mul_mem (hI hc) (hs hj)) (hI hd))
    exact hall w w.property hw

/-- The double-coset cover puts every pair of chambers in a translated apartment. -/
theorem exists_apartment_containing_chambers (hone : lift 1 ∈ I)
    (hcover : ∀ g : G, ∃ w : W, g ∈ DoubleCoset.doubleCoset (lift w) I I)
    (C C' : G ⧸ I) :
    ∃ g, C ∈ apartmentChambers I lift g ∧ C' ∈ apartmentChambers I lift g := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective C
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective C'
  obtain ⟨w, hw⟩ := hcover (a⁻¹ * b)
  obtain ⟨i, hi, j, hj, heq⟩ := DoubleCoset.mem_doubleCoset.mp hw
  refine ⟨a * i, ⟨1, ?_⟩, ⟨w, ?_⟩⟩
  · change (QuotientGroup.mk ((a * i) * lift 1) : G ⧸ I) = QuotientGroup.mk a
    rw [mul_assoc]
    exact QuotientGroup.mk_mul_of_mem a (I.mul_mem hi hone)
  · have hb : b = (a * i * lift w) * j := by
      rw [mul_assoc (a * i) (lift w) j, mul_assoc a i (lift w * j),
        ← mul_assoc i (lift w) j, ← heq, mul_inv_cancel_left]
    change (QuotientGroup.mk (a * i * lift w) : G ⧸ I) = QuotientGroup.mk b
    conv_rhs => rw [hb]
    exact (QuotientGroup.mk_mul_of_mem (a * i * lift w) hj).symm

/-- A positive count of chambers in one double coset proves its finiteness. -/
theorem finite_chambers_in_doubleCoset (q : ℕ) (hq : 0 < q) (w : W)
    (hcount : Nat.card (leftCosets I (lift w)) = q ^ cs.length w) :
    (leftCosets I (lift w)).Finite :=
  Set.finite_coe_iff.mp (Nat.card_pos_iff.mp (hcount ▸ pow_pos hq (cs.length w))).2

/-- Disjoint double cosets detect precisely which Weyl lifts lie in a face subgroup. -/
theorem lift_mem_faceSubgroup_iff (J : Set B) (w : W)
    (hface : (faceSubgroup cs I lift J : Set G) =
      ⋃ v : standardWallSubgroup cs J, DoubleCoset.doubleCoset (lift v) I I)
    (hdisj : Pairwise fun v v' : W =>
      Disjoint (DoubleCoset.doubleCoset (lift v) I I) (DoubleCoset.doubleCoset (lift v') I I)) :
    lift w ∈ faceSubgroup cs I lift J ↔ w ∈ standardWallSubgroup cs J := by
  change lift w ∈ (faceSubgroup cs I lift J : Set G) ↔ _
  rw [hface, Set.mem_iUnion]
  constructor
  · rintro ⟨v, hv⟩
    have heq : w = (v : W) := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (DoubleCoset.mem_doubleCoset_self I I (lift w)) hv
    exact heq ▸ v.property
  · intro hw
    exact ⟨⟨w, hw⟩, DoubleCoset.mem_doubleCoset_self I I (lift w)⟩

/-- Two chambers in a translated apartment determine the same face of cotype `J`
exactly when their indices are in the same left coset of the standard Coxeter subgroup.
The lift compatibility is supplied by the normalizer quotient with kernel contained in `I`. -/
theorem apartment_face_eq_iff (J : Set B) (g : G) (w v : W)
    (hface : (faceSubgroup cs I lift J : Set G) =
      ⋃ u : standardWallSubgroup cs J, DoubleCoset.doubleCoset (lift u) I I)
    (hdisj : Pairwise fun u u' : W =>
      Disjoint (DoubleCoset.doubleCoset (lift u) I I) (DoubleCoset.doubleCoset (lift u') I I))
    (hlift : (lift (w⁻¹ * v))⁻¹ * ((lift w)⁻¹ * lift v) ∈ I) :
    (QuotientGroup.mk (g * lift w) : G ⧸ faceSubgroup cs I lift J) =
      QuotientGroup.mk (g * lift v) ↔
        (QuotientGroup.mk w : W ⧸ standardWallSubgroup cs J) = QuotientGroup.mk v := by
  let P := faceSubgroup cs I lift J
  have hi : (lift (w⁻¹ * v))⁻¹ * ((lift w)⁻¹ * lift v) ∈ P :=
    Subgroup.subset_closure (Or.inl hlift)
  rw [QuotientGroup.eq, QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    ← lift_mem_faceSubgroup_iff cs I lift J (w⁻¹ * v) hface hdisj]
  constructor
  · intro h
    have h' := P.mul_mem h (P.inv_mem hi)
    simpa [mul_inv_rev, mul_assoc] using h'
  · intro h
    simpa using P.mul_mem h hi

/-- Finitely many chambers are incident to a standard face when its Coxeter
subgroup is finite and each chamber count is positive. -/
theorem finite_chambers_in_face (J : Set B) [Finite (standardWallSubgroup cs J)]
    (q : ℕ) (hq : 0 < q)
    (hface : (faceSubgroup cs I lift J : Set G) =
      ⋃ v : standardWallSubgroup cs J, DoubleCoset.doubleCoset (lift v) I I)
    (hcount : ∀ w, Nat.card (leftCosets I (lift w)) = q ^ cs.length w) :
    (QuotientGroup.mk '' (faceSubgroup cs I lift J : Set G) : Set (G ⧸ I)).Finite := by
  rw [hface, Set.image_iUnion]
  exact Set.finite_iUnion fun w => finite_chambers_in_doubleCoset cs I lift q hq w (hcount w)

/-- In a coset complex, the stabilizer under left multiplication of the standard face
of cotype `J` is its face subgroup. -/
theorem stabilizer_standard_face (J : Set B) (g : G) :
    (QuotientGroup.mk g : G ⧸ faceSubgroup cs I lift J) =
      QuotientGroup.mk (1 : G) ↔ g ∈ faceSubgroup cs I lift J := by
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff]

/-- The labels of chambers in one face lie in one left coset of the corresponding
standard Coxeter subgroup. This makes the chamber retraction compatible with faces. -/
theorem retraction_respects_face (J : Set B) {a b : G} {w v : W}
    (hsq : ∀ j, lift (cs.simple j) ^ 2 ∈ I)
    (hprod : ∀ u j,
      DoubleCoset.doubleCoset (lift u) I I * DoubleCoset.doubleCoset (lift (cs.simple j)) I I ⊆
        DoubleCoset.doubleCoset (lift (u * cs.simple j)) I I ∪
          DoubleCoset.doubleCoset (lift u) I I)
    (hdisj : Pairwise fun u u' : W =>
      Disjoint (DoubleCoset.doubleCoset (lift u) I I) (DoubleCoset.doubleCoset (lift u') I I))
    (ha : a ∈ DoubleCoset.doubleCoset (lift w) I I)
    (hb : b ∈ DoubleCoset.doubleCoset (lift v) I I)
    (hf : (QuotientGroup.mk a : G ⧸ faceSubgroup cs I lift J) = QuotientGroup.mk b) :
    (QuotientGroup.mk w : W ⧸ standardWallSubgroup cs J) = QuotientGroup.mk v := by
  let P := faceSubgroup cs I lift J
  let V := standardWallSubgroup cs J
  let D := fun u : W => DoubleCoset.doubleCoset (lift u) I I
  let property (x : G) := ∃ u : W, a * x ∈ D u ∧ w⁻¹ * u ∈ V
  have hI {x i : G} (hx : property x) (hi : i ∈ I) : property (x * i) := by
    obtain ⟨u, hu, hw⟩ := hx
    exact ⟨u, by simpa only [← mul_assoc] using doubleCoset_mul_mem I lift u hu hi, hw⟩
  have hwall {x : G} {j : B} (hx : property x) (hj : j ∈ J) :
      property (x * lift (cs.simple j)) := by
    obtain ⟨u, hu, hw⟩ := hx
    have h := hprod u j
      (Set.mul_mem_mul hu (DoubleCoset.mem_doubleCoset_self I I (lift (cs.simple j))))
    rcases h with h | h
    · refine ⟨u * cs.simple j, by simpa only [← mul_assoc] using h, ?_⟩
      rw [← mul_assoc]
      exact V.mul_mem hw (Subgroup.subset_closure ⟨j, hj, rfl⟩)
    · exact ⟨u, by simpa only [← mul_assoc] using h, hw⟩
  have hx : a⁻¹ * b ∈ P := QuotientGroup.eq.mp hf
  have h : property (a⁻¹ * b) := by
    refine Subgroup.closure_induction_right (p := fun x _ => property x) ?_ ?_ ?_ hx
    · exact ⟨w, by simpa only [mul_one] using ha, by simp⟩
    · rintro x _ y (hy | ⟨j, hj, rfl⟩) h
      · exact hI h hy
      · exact hwall h hj
    · rintro x _ y (hy | ⟨j, hj, rfl⟩) h
      · exact hI h (I.inv_mem hy)
      · have heq : (lift (cs.simple j))⁻¹ =
            lift (cs.simple j) * ((lift (cs.simple j)) ^ 2)⁻¹ := by
          simp [pow_two, mul_inv_rev, ← mul_assoc]
        change property (x * (lift (cs.simple j))⁻¹)
        rw [heq, ← mul_assoc]
        exact hI (hwall h hj) (I.inv_mem (hsq j))
  obtain ⟨u, hu, hw⟩ := h
  rw [mul_inv_cancel_left] at hu
  have huv : u = v := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hu hb
  exact QuotientGroup.eq.mpr (huv ▸ hw)

end Chambers

section RationalAlcove

open LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems
  (AlcoveCoxeterData AlcoveGeometry ApartmentRoots)
open LinearAlgebraicGroups.Arithmetic.AffineArrangement (Datum)

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- The weak inequalities of the marked rational alcove. -/
def InClosedAlcove (A : ApartmentRoots ℚ V J) (p x : V) : Prop :=
  ∀ a, A.positive p a → 0 ≤ A.wallValue a x

private theorem reflection_apply (a : J × ℤ) (x : V) :
    A.reflection a x = x - A.wallValue a x • A.coroot a.1 := by
  change (-a.2) • A.coroot a.1 + Module.reflection (A.diagonal a.1) x =
    x - (A.root a.1 x + (a.2 : ℚ)) • A.coroot a.1
  rw [Module.reflection_apply, add_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg, neg_smul]
  abel

private theorem reflection_reverses_wall (a : J × ℤ) (x : V) :
    A.wallValue a (A.reflection a x) = -A.wallValue a x := by
  change A.root a.1 (A.reflection a x) + (a.2 : ℚ) = -(A.root a.1 x + (a.2 : ℚ))
  rw [reflection_apply, map_sub, map_smul, A.diagonal]
  change A.root a.1 x - (A.root a.1 x + (a.2 : ℚ)) * 2 + (a.2 : ℚ) = _
  ring

/-- Each signed wall has a wall with its opposite affine equation. -/
theorem exists_opposite_wall (hA : AlcoveGeometry A p) (a : J × ℤ) :
    ∃ b, ∀ x, A.wallValue b x = -A.wallValue a x := by
  have hr : A.reflection a ∈ A.affineWeylGroup := Subgroup.subset_closure ⟨a, rfl⟩
  obtain ⟨σ, hσ⟩ := hA.ordinary_symmetries hr
  refine ⟨σ.symm a, fun x => ?_⟩
  have h := (hσ (σ.symm a)).1 x
  rw [Equiv.apply_symm_apply] at h
  exact h.symm.trans (reflection_reverses_wall a x)

private theorem wall_nonpos_of_negative (hA : AlcoveGeometry A p)
    {a : J × ℤ} (ha : A.wallValue a p < 0) {x : V} (hx : InClosedAlcove A p x) :
    A.wallValue a x ≤ 0 := by
  obtain ⟨b, hb⟩ := exists_opposite_wall hA a
  have hp : A.positive p b := by
    change 0 < A.wallValue b p
    rw [hb]
    exact neg_pos.mpr ha
  have h := hx b hp
  rwa [hb, neg_nonneg] at h

private theorem rightDescent_wall_eq_zero (hA : AlcoveGeometry A p)
    (d : AlcoveCoxeterData A p) {w : A.affineWeylGroup} {i : A.SimpleWall p}
    (hi : d.coxeter.IsRightDescent w i) {x : V}
    (hx : InClosedAlcove A p x) (hwx : InClosedAlcove A p (w.val x)) :
    A.wallValue i.val x = 0 := by
  let := d.action
  have h := wall_nonpos_of_negative hA ((d.right_descent w i).mp hi) hwx
  rw [d.equation, AffineEquiv.symm_apply_apply] at h
  exact h.antisymm (hx i.val i.property.1)

private theorem simple_fixes_of_wall_eq_zero (d : AlcoveCoxeterData A p)
    {i : A.SimpleWall p} {x : V} (hx : A.wallValue i.val x = 0) :
    (d.coxeter.simple i).val x = x := by
  rw [d.simple_eq]
  change A.reflection i.val x = x
  rw [reflection_apply, hx, zero_smul, sub_zero]

private theorem wall_eq_zero_of_simple_fixes (d : AlcoveCoxeterData A p)
    {i : A.SimpleWall p} {x : V} (hx : (d.coxeter.simple i).val x = x) :
    A.wallValue i.val x = 0 := by
  rw [d.simple_eq] at hx
  change A.reflection i.val x = x at hx
  rw [reflection_apply, sub_eq_self, smul_eq_zero] at hx
  refine hx.resolve_right fun h => ?_
  have htwo := A.diagonal i.val.1
  rw [h, map_zero] at htwo
  norm_num at htwo

/-- A closed alcove meets each ordinary Weyl orbit in at most one point. The
transporter of two points of the closed alcove is generated by the simple
walls through the source point. -/
theorem closedAlcove_transporter (hA : AlcoveGeometry A p) (d : AlcoveCoxeterData A p)
    {x : V} (hx : InClosedAlcove A p x) (w : A.affineWeylGroup)
    (hwx : InClosedAlcove A p (w.val x)) :
    w.val x = x ∧ w ∈ standardWallSubgroup d.coxeter {i | A.wallValue i.val x = 0} := by
  induction hl : d.coxeter.length w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w = 1
    · subst w
      exact ⟨rfl, Subgroup.one_mem _⟩
    · obtain ⟨i, hi⟩ := d.coxeter.exists_rightDescent_of_ne_one hw
      let s := d.coxeter.simple i
      have hzero := rightDescent_wall_eq_zero hA d hi hx hwx
      have hs : s.val x = x := simple_fixes_of_wall_eq_zero d hzero
      have hws : (w * s).val x = w.val x := by
        change w.val (s.val x) = _
        rw [hs]
      have hshort : d.coxeter.length (w * s) < n := hl ▸ hi
      obtain ⟨heq, hmem⟩ := ih _ hshort (w * s) (hws ▸ hwx) rfl
      refine ⟨hws.symm.trans heq, ?_⟩
      have hsimple : s ∈ standardWallSubgroup d.coxeter {i | A.wallValue i.val x = 0} :=
        Subgroup.subset_closure ⟨i, hzero, rfl⟩
      simpa only [s, mul_assoc, d.coxeter.simple_mul_simple_self, mul_one] using
        (standardWallSubgroup d.coxeter _).mul_mem hmem hsimple

/-- In the rational apartment the point stabilizer is generated precisely by
the simple walls passing through the point. -/
theorem closedAlcove_stabilizer (hA : AlcoveGeometry A p) (d : AlcoveCoxeterData A p)
    {x : V} (hx : InClosedAlcove A p x) (w : A.affineWeylGroup) :
    w.val x = x ↔ w ∈ standardWallSubgroup d.coxeter {i | A.wallValue i.val x = 0} := by
  refine ⟨fun heq => (closedAlcove_transporter hA d hx w (heq.symm ▸ hx)).2, ?_⟩
  intro hw
  refine Subgroup.closure_induction (p := fun w _ => w.val x = x) ?_ rfl ?_ ?_ hw
  · rintro _ ⟨i, hi, rfl⟩
    exact simple_fixes_of_wall_eq_zero d hi
  · intro a b _ _ ha hb
    change a.val (b.val x) = x
    rw [hb, ha]
  · intro a _ ha
    exact (a.val.symm_apply_eq).2 ha.symm

/-- The standard subgroup fixes exactly the prescribed collection of
unomitted vertices in the sense of its common point stabilizer. -/
theorem mem_standardWallSubgroup_iff_fix_vertices (hA : AlcoveGeometry A p)
    (d : AlcoveCoxeterData A p) (vertex : A.SimpleWall p → V)
    (hv : ∀ i, IsAlcoveVertex A p i (vertex i)) (T : Set (A.SimpleWall p)) (w : A.affineWeylGroup) :
    w ∈ standardWallSubgroup d.coxeter T ↔ ∀ i ∉ T, w.val (vertex i) = vertex i := by
  constructor
  · intro hw i hi
    apply (closedAlcove_stabilizer hA d (hv i).1 w).2
    refine Subgroup.closure_mono ?_ hw
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, (hv i).2 j |>.2 (fun h => hi (h ▸ hj)), rfl⟩
  · intro hfix
    induction hl : d.coxeter.length w using Nat.strong_induction_on generalizing w with
    | h n ih =>
      by_cases hw : w = 1
      · exact hw.symm ▸ (standardWallSubgroup d.coxeter T).one_mem
      · obtain ⟨i, hi⟩ := d.coxeter.exists_rightDescent_of_ne_one hw
        have hiT : i ∈ T := by
          by_contra hn
          have hfixi := hfix i hn
          have hzero := rightDescent_wall_eq_zero hA d hi (hv i).1 (hfixi.symm ▸ (hv i).1)
          exact ((hv i).2 i).1 hzero rfl
        let s := d.coxeter.simple i
        have hfix' (j : A.SimpleWall p) (hj : j ∉ T) :
            (w * s).val (vertex j) = vertex j := by
          have hzero := ((hv j).2 i).2 (fun h => hj (h ▸ hiT))
          change w.val (s.val (vertex j)) = _
          rw [simple_fixes_of_wall_eq_zero d hzero, hfix j hj]
        have hshort : d.coxeter.length (w * s) < n := hl ▸ hi
        have hmem := ih _ hshort (w * s) hfix' rfl
        have hs : s ∈ standardWallSubgroup d.coxeter T := Subgroup.subset_closure ⟨i, hiT, rfl⟩
        simpa only [s, mul_assoc, d.coxeter.simple_mul_simple_self, mul_one] using
          (standardWallSubgroup d.coxeter T).mul_mem hmem hs

/-- The standard-subgroup intersection rule, read on the marked vertices. -/
theorem standardWallSubgroup_inf (hA : AlcoveGeometry A p) (d : AlcoveCoxeterData A p)
    (vertex : A.SimpleWall p → V) (hv : ∀ i, IsAlcoveVertex A p i (vertex i))
    (T U : Set (A.SimpleWall p)) :
    standardWallSubgroup d.coxeter T ⊓ standardWallSubgroup d.coxeter U =
      standardWallSubgroup d.coxeter (T ∩ U) := by
  classical
  ext w
  change (w ∈ standardWallSubgroup d.coxeter T ∧ w ∈ standardWallSubgroup d.coxeter U) ↔ _
  simp only [mem_standardWallSubgroup_iff_fix_vertices hA d vertex hv, Set.mem_inter_iff, not_and_or]
  exact ⟨fun ⟨hT, hU⟩ i hi => hi.elim (hT i) (hU i),
    fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩⟩

/-- The linear part of any signed-wall symmetry permutes the finite set of
root functionals. This follows by subtracting the constant terms. -/
theorem root_comp_linear_mem_range {g : V ≃ᵃ[ℚ] V} (hg : g ∈ A.symmetries) (i : J) :
    (A.root i).comp g.linear.toLinearMap ∈ Set.range A.root := by
  obtain ⟨σ, hσ⟩ := hg
  let a := σ.symm (i, 0)
  have h (x : V) : A.wallValue (i, 0) (g x) = A.wallValue a x := by
    simpa only [a, Equiv.apply_symm_apply] using (hσ a).1 x
  refine ⟨a.1, LinearMap.ext fun x => ?_⟩
  have hx := h x
  have h0 := h 0
  change A.root i (g x) + (↑(0 : ℤ) : ℚ) = A.root a.1 x + (a.2 : ℚ) at hx
  change A.root i (g 0) + (↑(0 : ℤ) : ℚ) = A.root a.1 0 + (a.2 : ℚ) at h0
  have hgx : g x = g.linear x + g 0 := by
    simpa only [vadd_eq_add, add_zero] using g.map_vadd (0 : V) x
  rw [hgx, map_add] at hx
  rw [(A.root a.1).map_zero] at h0
  change A.root a.1 x = A.root i (g.linear x)
  linarith only [hx, h0]

/-- When the roots separate vectors, an affine Weyl element fixing a point
is determined by its permutation of the finitely many root functionals. -/
theorem finite_standardWallSubgroup [Finite J] (hA : AlcoveGeometry A p)
    (d : AlcoveCoxeterData A p) (hsep : ∀ x y : V, (∀ i, A.root i x = A.root i y) → x = y)
    (vertex : A.SimpleWall p → V) (hv : ∀ i, IsAlcoveVertex A p i (vertex i))
    (T : Set (A.SimpleWall p)) (hT : T ≠ univ) :
    Finite (standardWallSubgroup d.coxeter T) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
    by_contra! h
    exact hT (Set.eq_univ_iff_forall.mpr h)
  let x := vertex i
  let P := standardWallSubgroup d.coxeter T
  have hfix (w : P) : w.val.val x = x :=
    (mem_standardWallSubgroup_iff_fix_vertices hA d vertex hv T w).mp w.property i hi
  have : Finite (Set.range A.root) := Set.finite_coe_iff.mpr (Set.finite_range _)
  let roots (w : P) (j : J) : Set.range A.root :=
    ⟨(A.root j).comp w.val.val.linear.toLinearMap,
      root_comp_linear_mem_range (hA.ordinary_symmetries w.val.property) j⟩
  refine Finite.of_injective roots (fun w v h => ?_)
  apply Subtype.ext
  apply Subtype.ext
  ext y
  have hlin : w.val.val.linear (y - x) = v.val.val.linear (y - x) :=
    hsep _ _ (fun j => congrArg (fun f : Set.range A.root => f.val (y - x)) (congrFun h j))
  have translate (f : V ≃ᵃ[ℚ] V) (hf : f x = x) :
      f y = f.linear (y - x) + x := by
    have hxy : (y - x) +ᵥ x = y := by simp
    calc
      f y = f ((y - x) +ᵥ x) := congrArg f hxy.symm
      _ = f.linear (y - x) + x := by rw [AffineEquiv.map_vadd, hf, vadd_eq_add]
  rw [translate _ (hfix w), translate _ (hfix v), hlin]

end RationalAlcove

section RealScalarExtension

open LinearAlgebraicGroups.Specs.ExceptionalAffineBuilding
  (EuclideanApartment RealCoordinates rationalPoint realAffine realWallValue)
open LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open scoped TensorProduct

variable {V V' V'' : Type uG}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  [AddCommGroup V''] [Module ℚ V'']

/-- Scalar extension of a rational affine equivalence, bundled in the
specified linear coordinates over the reals. -/
noncomputable def realAffineEquiv (r : RealCoordinates V) (r' : RealCoordinates V')
    (f : V ≃ᵃ[ℚ] V') : EuclideanApartment V ≃ᵃ[ℝ] EuclideanApartment V' :=
  let l := r.symm.trans <| (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℝ ℝ) f.linear).trans r'
  l.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ _ (rationalPoint r' (f 0)))

theorem realAffineEquiv_apply (r : RealCoordinates V) (r' : RealCoordinates V')
    (f : V ≃ᵃ[ℚ] V') (x : EuclideanApartment V) :
    realAffineEquiv r r' f x = realAffine r r' f x := by
  change r' (1 ⊗ₜ[ℚ] f 0) + r' (f.linear.toLinearMap.baseChange ℝ (r.symm x)) = _
  simp only [realAffine, Specs.ExceptionalRealAlcove.realAffine, map_add, add_comm]

@[simp]
theorem realAffine_rationalPoint (r : RealCoordinates V) (r' : RealCoordinates V')
    (f : V ≃ᵃ[ℚ] V') (x : V) :
    realAffine r r' f (rationalPoint r x) = rationalPoint r' (f x) := by
  simp only [realAffine, rationalPoint, Specs.ExceptionalRealAlcove.realAffine,
    Specs.ExceptionalRealAlcove.rationalPoint, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  rw [← TensorProduct.tmul_add]
  have h : f x = f.linear x + f 0 := by
    simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : V) x
  change rationalPoint r' (f.linear x + f 0) = rationalPoint r' (f x)
  exact congrArg (rationalPoint r') h.symm

/-- A real affine map out of the scalar extension is determined by its
values at rational points, since their differences span the tensor product. -/
theorem affineMap_ext_rational (r : RealCoordinates V) {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f g : EuclideanApartment V →ᵃ[ℝ] E} (h : ∀ x, f (rationalPoint r x) = g (rationalPoint r x)) :
    f = g := by
  have h0 : f 0 = g 0 := by simpa only [Specs.ExceptionalRealAlcove.rationalPoint, TensorProduct.tmul_zero, map_zero] using h 0
  have hlin (x : V) : f.linear (rationalPoint r x) = g.linear (rationalPoint r x) := by
    have hf := f.linear_apply_vsub (rationalPoint r x) 0
    have hg := g.linear_apply_vsub (rationalPoint r x) 0
    simp only [vsub_eq_sub, sub_zero] at hf hg
    rw [hf, hg, h, h0]
  refine AffineMap.ext_linear ?_ h0
  have heq : f.linear.comp r.toLinearMap = g.linear.comp r.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
        have ha : (a ⊗ₜ[ℚ] x) = a • ((1 : ℝ) ⊗ₜ[ℚ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ha, map_smul, map_smul]
        exact congrArg (a • ·) (hlin x)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    DFunLike.congr_fun heq (r.symm x)

theorem realAffineEquiv_trans (r : RealCoordinates V) (r' : RealCoordinates V')
    (r'' : RealCoordinates V'') (f : V ≃ᵃ[ℚ] V') (g : V' ≃ᵃ[ℚ] V'') :
    realAffineEquiv r r'' (f.trans g) =
      (realAffineEquiv r r' f).trans (realAffineEquiv r' r'' g) := by
  apply AffineEquiv.toAffineMap_injective
  apply affineMap_ext_rational r
  intro x
  change realAffineEquiv r r'' (f.trans g) (rationalPoint r x) =
    realAffineEquiv r' r'' g (realAffineEquiv r r' f (rationalPoint r x))
  simp only [realAffineEquiv_apply, realAffine_rationalPoint, AffineEquiv.trans_apply]

theorem realAffineEquiv_refl (r : RealCoordinates V) :
    realAffineEquiv r r (AffineEquiv.refl ℚ V) = AffineEquiv.refl ℝ (EuclideanApartment V) := by
  apply AffineEquiv.toAffineMap_injective
  apply affineMap_ext_rational r
  intro x
  change realAffineEquiv r r (AffineEquiv.refl ℚ V) (rationalPoint r x) = rationalPoint r x
  rw [realAffineEquiv_apply, realAffine_rationalPoint]
  rfl

/-- The ordinary Weyl action on the rational apartment extends to the
specified real apartment. -/
@[instance_reducible]
noncomputable def realWeylAction {J : Type*} (A : ApartmentRoots ℚ V J) (r : RealCoordinates V) :
    MulAction A.affineWeylGroup (EuclideanApartment V) where
  smul w x := realAffineEquiv r r w.val x
  one_smul x := by
    change realAffineEquiv r r (AffineEquiv.refl ℚ V) x = x
    rw [realAffineEquiv_refl]
    rfl
  mul_smul w v x := by
    change realAffineEquiv r r (v.val.trans w.val) x =
      realAffineEquiv r r w.val (realAffineEquiv r r v.val x)
    rw [realAffineEquiv_trans]
    rfl

/-- A normalized wall equation in the real coordinates is an affine map. -/
noncomputable def realWallMap {J : Type*} (A : ApartmentRoots ℚ V J) (r : RealCoordinates V)
    (a : J × ℤ) : EuclideanApartment V →ᵃ[ℝ] ℝ :=
  let l := (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap ∘ₗ
    (A.root a.1).baseChange ℝ ∘ₗ r.symm.toLinearMap
  { toFun := realWallValue A r a
    linear := l
    map_vadd' := fun p v => by
      change l (v + p) + (a.2 : ℝ) = l v + (l p + (a.2 : ℝ))
      rw [map_add, add_assoc] }

@[simp]
theorem realWallValue_rationalPoint {J : Type*} (A : ApartmentRoots ℚ V J) (r : RealCoordinates V)
    (a : J × ℤ) (x : V) :
    realWallValue A r a (rationalPoint r x) = (A.wallValue a x : ℝ) := by
  simp only [realWallValue, rationalPoint, Specs.ExceptionalRealAlcove.realWallValue,
    Specs.ExceptionalRealAlcove.rationalPoint, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  change A.root a.1 x • (1 : ℝ) + (a.2 : ℝ) = ((A.root a.1 x + (a.2 : ℚ) : ℚ) : ℝ)
  simp only [Rat.cast_add, Rat.cast_intCast, Rat.smul_def, mul_one]

/-- A rational affine equality between wall equations extends to the
real coordinates, including a change of the marked apartment. -/
theorem realWallValue_comp_of_rational {J J' : Type*}
    (A : ApartmentRoots ℚ V J) (A' : ApartmentRoots ℚ V' J')
    (r : RealCoordinates V) (r' : RealCoordinates V') (a : J × ℤ) (a' : J' × ℤ) (f : V ≃ᵃ[ℚ] V')
    (h : ∀ x, A'.wallValue a' (f x) = A.wallValue a x) (x : EuclideanApartment V) :
    realWallValue A' r' a' (realAffine r r' f x) = realWallValue A r a x := by
  have heq : (realWallMap A' r' a').comp (realAffineEquiv r r' f).toAffineMap = realWallMap A r a :=
    affineMap_ext_rational r (fun y => by
      change realWallValue A' r' a' (realAffineEquiv r r' f (rationalPoint r y)) =
        realWallValue A r a (rationalPoint r y)
      simp only [realAffineEquiv_apply, realAffine_rationalPoint, realWallValue_rationalPoint, h])
  rw [← realAffineEquiv_apply]
  exact AffineMap.congr_fun heq x

end RealScalarExtension

section CosetRealization

open LinearAlgebraicGroups.Specs.ExceptionalAffineBuilding (Weights cotype IsBarycenter)
open scoped BigOperators

variable {G B W : Type*} [Group G] [Group W]
  {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (I G₀ : Subgroup G) (lift : W → G)

theorem faceSubgroup_mono {T U : Set B} (h : T ⊆ U) :
    faceSubgroup cs I lift T ≤ faceSubgroup cs I lift U :=
  Subgroup.closure_mono (Set.union_subset_union subset_rfl (Set.image_mono h))

private def chamberGluing : Setoid (G₀ × Weights B) where
  r x y := x.2 = y.2 ∧ (x.1 : G)⁻¹ * (y.1 : G) ∈ faceSubgroup cs I lift (cotype x.2)
  iseqv := by
    refine ⟨fun x => ⟨rfl, ?_⟩, ?_, ?_⟩
    · simp
    · rintro ⟨g, t⟩ ⟨h, s⟩ ⟨rfl, hmem⟩
      exact ⟨rfl, by simpa only [mul_inv_rev, inv_inv] using
        (faceSubgroup cs I lift (cotype t)).inv_mem hmem⟩
    · rintro ⟨g, t⟩ ⟨h, s⟩ ⟨k, u⟩ ⟨rfl, hgh⟩ ⟨rfl, hhk⟩
      exact ⟨rfl, by simpa only [mul_assoc, mul_inv_cancel_left] using
        (faceSubgroup cs I lift (cotype t)).mul_mem hgh hhk⟩

/-- The points obtained by gluing closed chambers along their actual parahoric cosets. -/
def CosetPoint := Quotient (chamberGluing cs I G₀ lift)

namespace CosetPoint

/-- Place weights in the closed chamber represented by a type-preserving element. -/
def place (g : G₀) (t : Weights B) : CosetPoint cs I G₀ lift :=
  Quotient.mk (chamberGluing cs I G₀ lift) (g, t)

theorem place_surjective (x : CosetPoint cs I G₀ lift) :
    ∃ g t, place cs I G₀ lift g t = x := by
  obtain ⟨⟨g, t⟩, rfl⟩ := Quotient.exists_rep x
  exact ⟨g, t, rfl⟩

theorem place_eq_iff (g h : G₀) (t s : Weights B) :
    place cs I G₀ lift g t = place cs I G₀ lift h s ↔
      t = s ∧ (g : G)⁻¹ * (h : G) ∈ faceSubgroup cs I lift (cotype t) :=
  Quotient.eq

theorem place_eq_of_chamber_eq (g h : G₀) (t : Weights B)
    (heq : (QuotientGroup.mk (g : G) : G ⧸ I) = QuotientGroup.mk (h : G)) :
    place cs I G₀ lift g t = place cs I G₀ lift h t :=
  (place_eq_iff cs I G₀ lift g h t t).2
    ⟨rfl, Subgroup.subset_closure (Or.inl (QuotientGroup.eq.mp heq))⟩

/-- The coset complex inherits left translation by the type-preserving group. -/
def translate : G₀ →* Equiv.Perm (CosetPoint cs I G₀ lift) where
  toFun a :=
    let move (b : G₀) := Quotient.lift
      (fun (x : G₀ × Weights B) => place cs I G₀ lift (b * x.1) x.2)
      (fun x y (h : (chamberGluing cs I G₀ lift).r x y) => (place_eq_iff cs I G₀ lift _ _ _ _).2
        ⟨h.1, by simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
          using h.2⟩)
    { toFun := move a
      invFun := move a⁻¹
      left_inv := fun x => Quotient.inductionOn x fun ⟨g, t⟩ => by
        change place cs I G₀ lift (a⁻¹ * (a * g)) t = place cs I G₀ lift g t
        rw [inv_mul_cancel_left]
      right_inv := fun x => Quotient.inductionOn x fun ⟨g, t⟩ => by
        change place cs I G₀ lift (a * (a⁻¹ * g)) t = place cs I G₀ lift g t
        rw [mul_inv_cancel_left] }
  map_one' := Equiv.ext fun x => Quotient.inductionOn x fun ⟨g, t⟩ => by
    change place cs I G₀ lift (1 * g) t = place cs I G₀ lift g t
    rw [one_mul]
  map_mul' a b := Equiv.ext fun x => Quotient.inductionOn x fun ⟨g, t⟩ => by
    change place cs I G₀ lift ((a * b) * g) t = place cs I G₀ lift (a * (b * g)) t
    rw [mul_assoc]

@[simp]
theorem translate_place (a g : G₀) (t : Weights B) :
    translate cs I G₀ lift a (place cs I G₀ lift g t) =
      place cs I G₀ lift (a * g) t := rfl

theorem translate_fixes_iff (a : G₀) (t : Weights B) :
    translate cs I G₀ lift a (place cs I G₀ lift 1 t) = place cs I G₀ lift 1 t ↔
      (a : G) ∈ faceSubgroup cs I lift (cotype t) := by
  rw [translate_place, mul_one, place_eq_iff]
  simp

end CosetPoint

/-- A nonempty simplex point cannot have all its coordinates zero. -/
theorem cotype_ne_univ (t : Weights B) : cotype t ≠ univ := by
  intro ht
  have hzero (i : B) : t.val i = 0 := Set.eq_univ_iff_forall.mp ht i
  have hsum := t.property.2
  simp only [hzero, finsum_zero] at hsum
  exact zero_ne_one hsum

/-- Each proper cotype has a point with uniform positive weights on its vertices. -/
theorem exists_barycenter [Finite B] (T : Set B) (hT : T ≠ univ) :
    ∃ t : Weights B, cotype t = T ∧ IsBarycenter T t := by
  classical
  let := Fintype.ofFinite B
  obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
    by_contra! h
    exact hT (Set.eq_univ_iff_forall.mpr h)
  have : Nonempty {i // i ∉ T} := ⟨⟨i, hi⟩⟩
  let n := Nat.card {i // i ∉ T}
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  let w (i : B) : ℝ := if i ∈ T then 0 else 1 / (n : ℝ)
  have hpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn
  have hw (i : B) : 0 ≤ w i := by
    by_cases h : i ∈ T
    · simp [w, h]
    · simpa only [w, ite_eq_right h] using hpos.le
  have hsum : ∑ᶠ i, w i = 1 := by
    have hcard : (Finset.univ.filter (· ∉ T)).card = n := by
      change _ = Nat.card {i // i ∉ T}
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have heq : w = fun i => if i ∉ T then 1 / (n : ℝ) else 0 := by
      funext i
      by_cases h : i ∈ T <;> simp [w, h]
    rw [finsum_eq_sum_of_fintype, heq]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  refine ⟨⟨w, hw, hsum⟩, ?_, fun _ => rfl⟩
  ext i
  change (if i ∈ T then 0 else 1 / (n : ℝ)) = 0 ↔ i ∈ T
  by_cases h : i ∈ T
  · simp only [h, ite_true]
  · simp only [h, ite_false, hpos.ne']

namespace CosetPoint

/-- Open faces in the quotient are exactly the left parahoric cosets,
with the cotype recording which coordinates vanish. -/
theorem open_face_cosets [Finite B] (T U : Set B) (hT : T ≠ univ) (_hU : U ≠ univ)
    (g h : G₀) :
    place cs I G₀ lift g '' {t | cotype t = T} = place cs I G₀ lift h '' {t | cotype t = U} ↔
      T = U ∧ (g : G)⁻¹ * (h : G) ∈ faceSubgroup cs I lift T := by
  constructor
  · intro heq
    obtain ⟨t, ht, _⟩ := exists_barycenter T hT
    have hm : place cs I G₀ lift g t ∈ place cs I G₀ lift h '' {t | cotype t = U} :=
      heq ▸ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hm
    obtain ⟨rfl, hmem⟩ := (place_eq_iff cs I G₀ lift g h t s).mp hsx.symm
    exact ⟨ht.symm.trans hs, ht ▸ hmem⟩
  · rintro ⟨rfl, hab⟩
    have heq (t : Weights B) (ht : cotype t = T) :
        place cs I G₀ lift g t = place cs I G₀ lift h t :=
      (place_eq_iff cs I G₀ lift g h t t).2 ⟨rfl, ht.symm ▸ hab⟩
    ext x
    exact ⟨fun ⟨t, ht, hx⟩ => ⟨t, ht, (heq t ht).symm.trans hx⟩,
      fun ⟨t, ht, hx⟩ => ⟨t, ht, (heq t ht).trans hx⟩⟩

/-- Inclusion of closed faces is reverse inclusion of their chamber cosets.
The order-reflecting hypothesis on the face subgroups holds for the actual
parahorics by the marked normalizer and the standard wall reflections. -/
theorem closed_face_incidence [Finite B]
    (hparahoric : ∀ U T, faceSubgroup cs I lift U ≤ faceSubgroup cs I lift T → U ⊆ T)
    (T U : Set B) (hT : T ≠ univ) (_hU : U ≠ univ) (g h : G₀) :
    place cs I G₀ lift g '' {t | T ⊆ cotype t} ⊆ place cs I G₀ lift h '' {t | U ⊆ cotype t} ↔
      {b : G | (h : G)⁻¹ * b ∈ faceSubgroup cs I lift U} ⊆
        {b : G | (g : G)⁻¹ * b ∈ faceSubgroup cs I lift T} := by
  let P := faceSubgroup cs I lift
  constructor
  · intro hfaces
    obtain ⟨t, ht, _⟩ := exists_barycenter T hT
    have ht' : T ⊆ cotype t := ht.symm.le
    obtain ⟨s, hs, heq⟩ := hfaces (show place cs I G₀ lift g t ∈
        place cs I G₀ lift g '' {v | T ⊆ cotype v} from ⟨t, ht', rfl⟩)
    obtain ⟨rfl, hgh⟩ := (place_eq_iff cs I G₀ lift g h t s).1 heq.symm
    intro b hb
    change (h : G)⁻¹ * b ∈ P U at hb
    change (g : G)⁻¹ * b ∈ P T
    have hmem : (g : G)⁻¹ * (h : G) ∈ P T := ht ▸ hgh
    have hUb : (h : G)⁻¹ * b ∈ P T := faceSubgroup_mono cs I lift (ht ▸ hs) hb
    simpa only [mul_assoc, mul_inv_cancel_left] using (P T).mul_mem hmem hUb
  · intro hcosets
    have hgh : (g : G)⁻¹ * (h : G) ∈ P T :=
      hcosets (show (h : G)⁻¹ * (h : G) ∈ P U by simp)
    have hle : P U ≤ P T := by
      intro a ha
      have ha' := hcosets (show (h : G)⁻¹ * ((h : G) * a) ∈ P U by simpa using ha)
      change (g : G)⁻¹ * ((h : G) * a) ∈ P T at ha'
      rw [← mul_assoc] at ha'
      simpa only [inv_mul_cancel_left] using (P T).mul_mem ((P T).inv_mem hgh) ha'
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t, (hparahoric U T hle).trans ht, ?_⟩
    exact ((place_eq_iff cs I G₀ lift g h t t).2
      ⟨rfl, faceSubgroup_mono cs I lift ht hgh⟩).symm

end CosetPoint

end CosetRealization

section MarkedCosets

open LinearAlgebraicGroups.Specs.ExceptionalAffineBuilding
  (Chamber Weights cotype parahoric)
open LinearAlgebraicGroups.Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum)
open LinearAlgebraicGroups.Specs.IntegralSemisimpleModel (Model integerAlgebra)
open scoped CategoryTheory.MonObj
attribute [local instance] integerAlgebra

variable {K : Type uG} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{uG}} {M : Model D} {G Wf : Type uG} [Group G] [Group Wf]
  {j : G →* FieldPoints M K}
  {V : Type uG} {J : Type uB} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  (C : LocalComparison (j := j) (Wf := Wf) A p)

private theorem iwahori_le_ordinary : C.I ≤ C.G₀ := le_sup_left

private theorem unitTorus_le_iwahori : C.T₀ ≤ C.I := by
  have heq : C.I ⊓ C.N = C.T₀ := C.localIwahori.intersection
  rw [← heq]
  exact inf_le_left

private theorem normalizer_mem_unitTorus_iff (n : C.N) :
    (n : G) ∈ C.T₀ ↔ C.affine n = 1 := by
  have heq : C.affine.ker.map C.N.subtype = C.T₀ := C.kernel
  rw [← heq]
  change (∃ x : C.N, x ∈ C.affine.ker ∧ (x : G) = (n : G)) ↔ _
  simp only [MonoidHom.mem_ker, Subtype.coe_inj, exists_eq_right]

private theorem lift_one_mem_iwahori : (C.lift 1 : G) ∈ C.I :=
  unitTorus_le_iwahori C ((normalizer_mem_unitTorus_iff C (C.lift 1)).2 (C.lift_label 1))

private theorem lift_mem_ordinary (w : A.affineWeylGroup) : (C.lift w : G) ∈ C.G₀ := by
  apply (le_sup_right : (A.affineWeylGroup.comap C.affine).map C.N.subtype ≤ C.G₀)
  refine ⟨C.lift w, ?_, rfl⟩
  change C.affine (C.lift w) ∈ A.affineWeylGroup
  rw [C.lift_label]
  exact w.property

/-- A normalizer element with an ordinary label differs from its marked lift by a unit. -/
theorem normalizer_lift_difference (n : C.N) (w : A.affineWeylGroup)
    (hn : C.affine n = w.val) : (C.lift w : G)⁻¹ * (n : G) ∈ C.T₀ := by
  change ((C.lift w)⁻¹ * n : C.N).val ∈ C.T₀
  apply (normalizer_mem_unitTorus_iff C _).2
  rw [map_mul, map_inv, C.lift_label, hn, inv_mul_cancel]

theorem marked_lift_difference (w v : A.affineWeylGroup) :
    (C.lift (w⁻¹ * v) : G)⁻¹ * ((C.lift w : G)⁻¹ * (C.lift v : G)) ∈ C.T₀ := by
  apply normalizer_lift_difference C ((C.lift w)⁻¹ * C.lift v) (w⁻¹ * v)
  rw [map_mul, map_inv, C.lift_label, C.lift_label]
  rfl

private theorem simple_lift_sq_mem_iwahori (i : A.SimpleWall p) :
    (C.lift (C.coxeter.coxeter.simple i) : G) ^ 2 ∈ C.I := by
  apply unitTorus_le_iwahori C
  change ((C.lift (C.coxeter.coxeter.simple i)) ^ 2 : C.N).val ∈ C.T₀
  apply (normalizer_mem_unitTorus_iff C _).2
  rw [map_pow, C.lift_label]
  rw [pow_two]
  exact congrArg Subtype.val (C.coxeter.coxeter.simple_mul_simple_self i)

private theorem wall_product_of_ascent {q : ℕ} (hB : C.Bruhat q)
    (w : A.affineWeylGroup) (i : A.SimpleWall p) (h : ¬ C.coxeter.coxeter.IsRightDescent w i) :
    C.cell w * C.cell (C.coxeter.coxeter.simple i) = C.cell (w * C.coxeter.coxeter.simple i) := by
  let := C.coxeter.action
  classical
  have hpos := (C.coxeter.right_ascent w i).mp (C.coxeter.coxeter.not_isRightDescent_iff.mp h)
  simpa only [ite_eq_left hpos] using hB.wall_product w i

private theorem wall_product_of_descent {q : ℕ} (hB : C.Bruhat q)
    (w : A.affineWeylGroup) (i : A.SimpleWall p) (h : C.coxeter.coxeter.IsRightDescent w i) :
    C.cell w * C.cell (C.coxeter.coxeter.simple i) =
      C.cell (w * C.coxeter.coxeter.simple i) ∪ C.cell w := by
  let := C.coxeter.action
  classical
  have hneg := (C.coxeter.right_descent w i).mp h
  have hnpos : ¬ A.positive p (w • i.val) := not_lt_of_ge hneg.le
  simpa only [ite_eq_right hnpos] using hB.wall_product w i

private theorem parahoric_le_ordinary (T : Set (A.SimpleWall p)) :
    parahoric C T ≤ C.G₀ := by
  refine (Subgroup.closure_le C.G₀).2 ?_
  rintro x (hx | ⟨i, _, rfl⟩)
  · exact iwahori_le_ordinary C hx
  · exact lift_mem_ordinary C _

include C in
/-- A simple wall is determined by its root direction, since its level is
the threshold of that root at the marked base point. -/
theorem finite_simpleWalls [Finite J] : Finite (A.SimpleWall p) := by
  refine Finite.of_injective (fun i : A.SimpleWall p => i.val.1) ?_
  intro i j hij
  change i.val.1 = j.val.1 at hij
  apply Subtype.ext
  refine Prod.ext hij ?_
  rw [C.chart.signs.simple_index i.val i.property,
    C.chart.signs.simple_index j.val j.property, hij]

/-- The marked parahoric is the disjoint union of the cells of its standard subgroup. -/
theorem parahoric_eq_iUnion {q : ℕ} (hB : C.Bruhat q) (T : Set (A.SimpleWall p)) :
    (parahoric C T : Set G) = ⋃ w : standardWallSubgroup C.coxeter.coxeter T, C.cell w :=
  faceSubgroup_eq_iUnion C.coxeter.coxeter C.I (fun w => (C.lift w : G)) T
    (lift_one_mem_iwahori C) (simple_lift_sq_mem_iwahori C)
    (wall_product_of_ascent C hB) (wall_product_of_descent C hB)

/-- The actual parahoric intersection is the parahoric for the
intersection of the standard wall sets. -/
theorem parahoric_inf {q : ℕ} (hB : C.Bruhat q)
    (vertex : A.SimpleWall p → V) (hv : ∀ i, IsAlcoveVertex A p i (vertex i))
    (T U : Set (A.SimpleWall p)) :
    parahoric C T ⊓ parahoric C U = parahoric C (T ∩ U) := by
  apply le_antisymm
  · rintro g ⟨hgT, hgU⟩
    change g ∈ (parahoric C T : Set G) at hgT
    change g ∈ (parahoric C U : Set G) at hgU
    rw [parahoric_eq_iUnion C hB, Set.mem_iUnion] at hgT hgU
    obtain ⟨w, hw⟩ := hgT
    obtain ⟨v, hv'⟩ := hgU
    have heq : w.val = v.val := by
      by_contra hn
      exact Set.disjoint_left.mp (hB.disjoint hn) hw hv'
    have hmem : w.val ∈ standardWallSubgroup C.coxeter.coxeter T ⊓
        standardWallSubgroup C.coxeter.coxeter U := ⟨w.property, heq.symm ▸ v.property⟩
    rw [standardWallSubgroup_inf C.geometry C.coxeter vertex hv] at hmem
    change g ∈ (parahoric C (T ∩ U) : Set G)
    rw [parahoric_eq_iUnion C hB, Set.mem_iUnion]
    exact ⟨⟨w, hmem⟩, hw⟩
  · exact le_inf (faceSubgroup_mono _ _ _ Set.inter_subset_left)
      (faceSubgroup_mono _ _ _ Set.inter_subset_right)

/-- The order of the marked parahorics recovers the wall sets. -/
theorem parahoric_le_iff {q : ℕ} (hB : C.Bruhat q)
    (vertex : A.SimpleWall p → V) (hv : ∀ i, IsAlcoveVertex A p i (vertex i))
    (T U : Set (A.SimpleWall p)) :
    parahoric C T ≤ parahoric C U ↔ T ⊆ U := by
  refine ⟨?_, faceSubgroup_mono _ _ _⟩
  intro h i hi
  by_contra hn
  have hgen : (C.lift (C.coxeter.coxeter.simple i) : G) ∈ parahoric C T :=
    Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
  have hmem := (lift_mem_faceSubgroup_iff C.coxeter.coxeter C.I (fun w => (C.lift w : G))
    U (C.coxeter.coxeter.simple i) (parahoric_eq_iUnion C hB U) hB.disjoint).mp (h hgen)
  have hfix := (mem_standardWallSubgroup_iff_fix_vertices C.geometry C.coxeter vertex hv
    U (C.coxeter.coxeter.simple i)).mp hmem i hn
  exact ((hv i).2 i).mp (wall_eq_zero_of_simple_fixes C.coxeter hfix) rfl

/-- Every chamber incident to a particular face is among finitely many
left cosets when its standard wall group is finite. -/
theorem marked_incident_finite {q : ℕ} (hB : C.Bruhat q) (hq : 0 < q)
    (T : Set (A.SimpleWall p)) [Finite (standardWallSubgroup C.coxeter.coxeter T)]
    (g : G) :
    (QuotientGroup.mk '' {h : G | g⁻¹ * h ∈ parahoric C T} : Set (G ⧸ C.I)).Finite := by
  have hfinite := finite_chambers_in_face C.coxeter.coxeter C.I (fun w => (C.lift w : G))
    T q hq (parahoric_eq_iUnion C hB T) hB.coset_count
  refine (hfinite.image (g • ·)).subset ?_
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨QuotientGroup.mk (g⁻¹ * h), ⟨_, hh, rfl⟩, ?_⟩
  change (QuotientGroup.mk (g * (g⁻¹ * h)) : G ⧸ C.I) = QuotientGroup.mk h
  rw [mul_inv_cancel_left]

/-- The labels of the actual normalizer elements in a face subgroup are exactly
the corresponding standard Coxeter subgroup. -/
theorem parahoric_normalizer_image {q : ℕ} (hB : C.Bruhat q) (T : Set (A.SimpleWall p)) :
    ((parahoric C T).comap C.N.subtype).map C.affine =
      (standardWallSubgroup C.coxeter.coxeter T).map A.affineWeylGroup.subtype := by
  have hlift (w : A.affineWeylGroup) : (C.lift w : G) ∈ parahoric C T ↔
      w ∈ standardWallSubgroup C.coxeter.coxeter T :=
    lift_mem_faceSubgroup_iff C.coxeter.coxeter C.I (fun w => (C.lift w : G)) T w
      (parahoric_eq_iUnion C hB T) hB.disjoint
  ext f
  constructor
  · rintro ⟨n, hn, rfl⟩
    change (n : G) ∈ parahoric C T at hn
    have hn₀ := parahoric_le_ordinary C T hn
    have hm : (n : G) ∈ C.G₀ ⊓ C.N := ⟨hn₀, n.property⟩
    rw [hB.ordinary_normalizer] at hm
    obtain ⟨m, hm, heq⟩ := hm
    have heq' : m = n := Subtype.ext heq
    subst m
    let w : A.affineWeylGroup := ⟨C.affine n, hm⟩
    have hd := unitTorus_le_iwahori C (normalizer_lift_difference C n w rfl)
    have hd' : (C.lift w : G)⁻¹ * (n : G) ∈ parahoric C T :=
      Subgroup.subset_closure (Or.inl hd)
    have hw := (parahoric C T).mul_mem hn ((parahoric C T).inv_mem hd')
    exact ⟨w, (hlift w).mp (by simpa [mul_inv_rev, ← mul_assoc] using hw), rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨C.lift w, (hlift w).mpr hw, C.lift_label w⟩

/-- The marked lifts identify apartment incidence with ordinary Coxeter incidence. -/
theorem marked_apartment_incidence {q : ℕ} (hB : C.Bruhat q) (T : Set (A.SimpleWall p))
    (g : G) (w v : A.affineWeylGroup) :
    (QuotientGroup.mk (g * (C.lift w : G)) : G ⧸ parahoric C T) =
      QuotientGroup.mk (g * (C.lift v : G)) ↔ w⁻¹ * v ∈ standardWallSubgroup C.coxeter.coxeter T :=
  (apartment_face_eq_iff C.coxeter.coxeter C.I (fun u => (C.lift u : G)) T g w v
    (parahoric_eq_iUnion C hB T) hB.disjoint
    (unitTorus_le_iwahori C (marked_lift_difference C w v))).trans QuotientGroup.eq

set_option maxHeartbeats 500000 in
/-- The Bruhat cover puts every pair of actual type-preserving chambers in an apartment. -/
theorem marked_common_apartment {q : ℕ} (hB : C.Bruhat q) (a b : Chamber C.I C.G₀) :
    ∃ g : C.G₀, a.val ∈ apartmentChambers C.I (fun w => (C.lift w : G)) g ∧
      b.val ∈ apartmentChambers C.I (fun w => (C.lift w : G)) g := by
  obtain ⟨a, a', rfl⟩ := a
  obtain ⟨b, b', rfl⟩ := b
  have hd : ((a' : G)⁻¹ * (b' : G)) ∈ C.G₀ :=
    C.G₀.mul_mem (C.G₀.inv_mem a'.property) b'.property
  change ((a' : G)⁻¹ * (b' : G)) ∈ (C.G₀ : Set G) at hd
  rw [← hB.cover, Set.mem_iUnion] at hd
  obtain ⟨w, hw⟩ := hd
  obtain ⟨i, hi, k, hk, heq⟩ := DoubleCoset.mem_doubleCoset.mp hw
  let g : C.G₀ := a' * ⟨i, iwahori_le_ordinary C hi⟩
  refine ⟨g, ⟨1, ?_⟩, ⟨w, ?_⟩⟩
  · change (QuotientGroup.mk (((a' : G) * i) * (C.lift 1 : G)) : G ⧸ C.I) = _
    rw [mul_assoc]
    exact QuotientGroup.mk_mul_of_mem _ (C.I.mul_mem hi (lift_one_mem_iwahori C))
  · have hb : ((g : G) * (C.lift w : G)) * k = (b' : G) := by
      change ((a' : G) * i) * (C.lift w : G) * k = _
      rw [mul_assoc, mul_assoc, ← mul_assoc i, ← heq, mul_inv_cancel_left]
    change (QuotientGroup.mk ((g : G) * (C.lift w : G)) : G ⧸ C.I) =
      QuotientGroup.mk (b' : G)
    rw [← hb]
    exact (QuotientGroup.mk_mul_of_mem _ hk).symm

/-- A marked normalizer lift viewed in the actual type-preserving subgroup. -/
abbrev ordinaryLift (w : A.affineWeylGroup) : C.G₀ :=
  ⟨C.lift w, lift_mem_ordinary C w⟩

private theorem exists_cell_label {q : ℕ} (hB : C.Bruhat q) (a b : C.G₀) :
    ∃ w, (a : G)⁻¹ * (b : G) ∈ C.cell w := by
  have h : (a : G)⁻¹ * (b : G) ∈ (C.G₀ : Set G) := (a⁻¹ * b).property
  rwa [← hB.cover, Set.mem_iUnion] at h

/-- The label from the actual chamber represented by `a` to the chamber
represented by `b`, using the marked disjoint double cosets. -/
noncomputable def relativeLabel {q : ℕ} (hB : C.Bruhat q) (a b : C.G₀) :
    A.affineWeylGroup :=
  (exists_cell_label C hB a b).choose

theorem relativeLabel_mem_cell {q : ℕ} (hB : C.Bruhat q) (a b : C.G₀) :
    (a : G)⁻¹ * (b : G) ∈ C.cell (relativeLabel C hB a b) :=
  (exists_cell_label C hB a b).choose_spec

theorem relativeLabel_eq_of_mem {q : ℕ} (hB : C.Bruhat q) (a b : C.G₀)
    (w : A.affineWeylGroup) (hw : (a : G)⁻¹ * (b : G) ∈ C.cell w) :
    relativeLabel C hB a b = w := by
  by_contra hne
  exact Set.disjoint_left.mp (hB.disjoint hne) (relativeLabel_mem_cell C hB a b) hw

/-- Within an apartment containing the center, the relative label is the
usual Coxeter displacement from the chamber at the center. -/
theorem relativeLabel_of_apartment {q : ℕ} (hB : C.Bruhat q)
    (a h : C.G₀) (v w : A.affineWeylGroup)
    (hc : (QuotientGroup.mk ((h : G) * (C.lift v : G)) : G ⧸ C.I) = QuotientGroup.mk (a : G)) :
    relativeLabel C hB a (h * ordinaryLift C w) = v⁻¹ * w := by
  apply relativeLabel_eq_of_mem
  let d := (C.lift (v⁻¹ * w) : G)⁻¹ * ((C.lift v : G)⁻¹ * (C.lift w : G))
  have hd : d ∈ C.I := unitTorus_le_iwahori C (marked_lift_difference C v w)
  have hl : (a : G)⁻¹ * ((h : G) * (C.lift v : G)) ∈ C.I :=
    QuotientGroup.eq.mp hc.symm
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨_, hl, d, hd, ?_⟩
  change (a : G)⁻¹ * ((h : G) * (C.lift w : G)) =
    ((a : G)⁻¹ * ((h : G) * (C.lift v : G))) * (C.lift (v⁻¹ * w) : G) * d
  simp only [d, mul_assoc, mul_inv_cancel_left]

private theorem relativeLabel_respects_face {q : ℕ} (hB : C.Bruhat q)
    (a b b' : C.G₀) (T : Set (A.SimpleWall p))
    (h : (b : G)⁻¹ * (b' : G) ∈ parahoric C T) :
    (relativeLabel C hB a b)⁻¹ * relativeLabel C hB a b' ∈
      standardWallSubgroup C.coxeter.coxeter T := by
  have hprod (u : A.affineWeylGroup) (i : A.SimpleWall p) :
      C.cell u * C.cell (C.coxeter.coxeter.simple i) ⊆
        C.cell (u * C.coxeter.coxeter.simple i) ∪ C.cell u := by
    by_cases hi : C.coxeter.coxeter.IsRightDescent u i
    · rw [wall_product_of_descent C hB u i hi]
    · rw [wall_product_of_ascent C hB u i hi]
      exact subset_union_left
  apply QuotientGroup.eq.mp
  apply retraction_respects_face C.coxeter.coxeter C.I (fun w => (C.lift w : G)) T
    (simple_lift_sq_mem_iwahori C) hprod hB.disjoint
    (relativeLabel_mem_cell C hB a b) (relativeLabel_mem_cell C hB a b')
  apply QuotientGroup.eq.mpr
  simpa only [mul_inv_rev, mul_assoc, inv_inv, mul_inv_cancel_left] using h

variable {E : Type*} [MulAction A.affineWeylGroup E]
variable (position : Weights (A.SimpleWall p) → E)

local notation "Points" =>
  CosetPoint C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G))
local notation "place" =>
  CosetPoint.place C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G))

/-- The chamber-centered retraction on the glued point set. A standard wall
subgroup fixes the corresponding point of the model apartment. -/
noncomputable def apartmentRetraction {q : ℕ} (hB : C.Bruhat q)
    (hfix : ∀ t w, w ∈ standardWallSubgroup C.coxeter.coxeter (cotype t) → w • position t = position t)
    (g : C.G₀) (u : A.affineWeylGroup) : Points → E :=
  let a := g * ordinaryLift C u
  Quotient.lift (fun (x : C.G₀ × Weights (A.SimpleWall p)) =>
      (u * relativeLabel C hB a x.1) • position x.2) (by
    rintro ⟨b, t⟩ ⟨b', s⟩ ⟨rfl, hb⟩
    calc
      (u * relativeLabel C hB a b) • position t =
          (u * relativeLabel C hB a b) •
            (((relativeLabel C hB a b)⁻¹ * relativeLabel C hB a b') • position t) :=
        congrArg _ (hfix t _ (relativeLabel_respects_face C hB a b b' (cotype t) hb)).symm
      _ = _ := by simp only [smul_smul, mul_assoc, mul_inv_cancel_left])

theorem apartmentRetraction_place {q : ℕ} (hB : C.Bruhat q)
    (hfix : ∀ t w, w ∈ standardWallSubgroup C.coxeter.coxeter (cotype t) → w • position t = position t)
    (g : C.G₀) (u : A.affineWeylGroup) (h : C.G₀) (w : A.affineWeylGroup)
    (t : Weights (A.SimpleWall p))
    (hw : ((g : G) * (C.lift u : G))⁻¹ * (h : G) ∈ C.cell w) :
    apartmentRetraction C position hB hfix g u (place h t) = (u * w) • position t := by
  change (u * relativeLabel C hB (g * ordinaryLift C u) h) • position t = _
  rw [relativeLabel_eq_of_mem C hB _ _ w hw]

variable (covers : ∀ x : E, ∃ (w : A.affineWeylGroup) (t : Weights (A.SimpleWall p)),
  x = w • position t)
variable (gluing : ∀ (w v : A.affineWeylGroup) t s, w • position t = v • position s →
  t = s ∧ w⁻¹ * v ∈ standardWallSubgroup C.coxeter.coxeter (cotype t))

/-- The chart of a translated apartment, using the marked Weyl translates
of the model simplex as representatives. -/
noncomputable def apartmentChart (g : C.G₀) (x : E) : Points :=
  place (g * ordinaryLift C (covers x).choose) (covers x).choose_spec.choose

include gluing in
theorem apartmentChart_place {q : ℕ} (hB : C.Bruhat q)
    (g : C.G₀) (w : A.affineWeylGroup) (t : Weights (A.SimpleWall p)) :
    apartmentChart C position covers g (w • position t) = place (g * ordinaryLift C w) t := by
  let x := w • position t
  let v := (covers x).choose
  let s := (covers x).choose_spec.choose
  have heq : x = v • position s := (covers x).choose_spec.choose_spec
  obtain ⟨hst, hmem⟩ := gluing v w s t heq.symm
  apply (CosetPoint.place_eq_iff _ _ _ _ _ _ _ _).2
  exact ⟨hst, QuotientGroup.eq.mp ((marked_apartment_incidence C hB (cotype s) g v w).2 hmem)⟩

include gluing in
/-- Every pair of points lies in one of the translated model apartments. -/
theorem apartmentChart_pair {q : ℕ} (hB : C.Bruhat q) (x y : Points) :
    ∃ (g : C.G₀) (v w : E), apartmentChart C position covers g v = x ∧
      apartmentChart C position covers g w = y := by
  obtain ⟨a, t, rfl⟩ := CosetPoint.place_surjective _ _ _ _ x
  obtain ⟨b, s, rfl⟩ := CosetPoint.place_surjective _ _ _ _ y
  obtain ⟨g, ⟨v, hv⟩, ⟨w, hw⟩⟩ := marked_common_apartment C hB
    ⟨QuotientGroup.mk (a : G), a, rfl⟩ ⟨QuotientGroup.mk (b : G), b, rfl⟩
  refine ⟨g, v • position t, w • position s, ?_, ?_⟩
  · rw [apartmentChart_place C position covers gluing hB]
    exact CosetPoint.place_eq_of_chamber_eq _ _ _ _ _ _ _ hv
  · rw [apartmentChart_place C position covers gluing hB]
    exact CosetPoint.place_eq_of_chamber_eq _ _ _ _ _ _ _ hw

include gluing in
/-- On any apartment through the center chamber the retraction is precisely
the change of coordinates taking that chamber to its marked image. -/
theorem apartmentRetraction_chart {q : ℕ} (hB : C.Bruhat q)
    (hfix : ∀ t w, w ∈ standardWallSubgroup C.coxeter.coxeter (cotype t) → w • position t = position t)
    (g h : C.G₀) (u v : A.affineWeylGroup)
    (hc : (QuotientGroup.mk ((h : G) * (C.lift v : G)) : G ⧸ C.I) =
      QuotientGroup.mk ((g : G) * (C.lift u : G))) (x : E) :
    apartmentRetraction C position hB hfix g u (apartmentChart C position covers h x) =
      (u * v⁻¹) • x := by
  obtain ⟨w, t, rfl⟩ := covers x
  rw [apartmentChart_place C position covers gluing hB]
  change (u * relativeLabel C hB (g * ordinaryLift C u) (h * ordinaryLift C w)) • position t = _
  rw [relativeLabel_of_apartment C hB (g * ordinaryLift C u) h v w hc, smul_smul, mul_assoc]

end MarkedCosets

section IntrinsicMetric

open LinearAlgebraicGroups.Specs.ExceptionalAffineBuilding (CellChain Weights)
open scoped NNReal

variable {C B E X : Type*} [MetricSpace E]
  {place : C → Weights B → X} {position : Weights B → E}

private theorem cellChain_append {x y z : X} {l m : ℝ}
    (h : CellChain place position x y l) (k : CellChain place position y z m) :
    CellChain place position x z (l + m) := by
  induction h with
  | nil => simpa only [zero_add] using k
  | cons c t s h ih => simpa only [add_assoc] using CellChain.cons c t s (ih k)

private theorem cellChain_reverse {x y : X} {l : ℝ}
    (h : CellChain place position x y l) : CellChain place position y x l := by
  induction h with
  | nil x => exact CellChain.nil x
  | cons c t s h ih =>
    have hk := CellChain.cons (position := position) c s t (CellChain.nil (place c t))
    have ha := cellChain_append ih hk
    rwa [add_zero, dist_comm (position s), add_comm] at ha

/-- A map that contracts each chamber contracts the lengths of chains. -/
theorem cellChain_dist_le {Y : Type*} [MetricSpace Y] (f : X → Y)
    (hf : ∀ c t s, dist (f (place c t)) (f (place c s)) ≤ dist (position t) (position s))
    {x y : X} {l : ℝ} (h : CellChain place position x y l) :
    dist (f x) (f y) ≤ l := by
  induction h with
  | nil => simp
  | cons c t s h ih =>
    exact (dist_triangle _ _ _).trans (add_le_add (hf c t s) ih)

/-- A map preserving the coordinates of every step carries a chamber chain
to a chain with the same length. -/
theorem CellChain.map {D Y : Type*} (place' : D → Weights B → Y)
    (f : X → Y) (mapCell : C → D) (hf : ∀ c t, f (place c t) = place' (mapCell c) t)
    {x y : X} {l : ℝ} (h : CellChain place position x y l) :
    CellChain place' position (f x) (f y) l := by
  induction h with
  | nil x => exact CellChain.nil (f x)
  | cons c t s h ih =>
      rw [hf c s] at ih
      rw [hf c t]
      exact CellChain.cons (mapCell c) t s ih

private theorem cellChain_length_nonneg {x y : X} {l : ℝ}
    (h : CellChain place position x y l) : 0 ≤ l := by
  induction h with
  | nil => exact le_rfl
  | cons c t s h ih => exact add_nonneg dist_nonneg ih

/-- The chain infimum is a metric once chains connect every pair of points
and chamberwise contractions separate distinct points. -/
@[instance_reducible]
noncomputable def cellChainMetric
    (connected : ∀ x y, ∃ l, CellChain place position x y l)
    (separated : ∀ x y, x ≠ y → ∃ r : X → E, r x ≠ r y ∧
      ∀ c t s, dist (r (place c t)) (r (place c s)) ≤ dist (position t) (position s)) :
    MetricSpace X := by
  let lengths := fun x y => {l : ℝ | CellChain place position x y l}
  have hne (x y : X) : (lengths x y).Nonempty := connected x y
  have hbdd (x y : X) : BddBelow (lengths x y) :=
    ⟨0, fun _ h => cellChain_length_nonneg h⟩
  refine {
    dist := fun x y => sInf (lengths x y)
    dist_self := fun x => IsLeast.csInf_eq ⟨CellChain.nil x, fun _ h => cellChain_length_nonneg h⟩
    dist_comm := ?_
    dist_triangle := ?_
    eq_of_dist_eq_zero := ?_ }
  · intro x y
    have heq : lengths x y = lengths y x :=
      Set.ext fun _ => ⟨cellChain_reverse, cellChain_reverse⟩
    rw [heq]
  · intro x y z
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨l, hl, hlt⟩ := exists_lt_of_csInf_lt (hne x y)
      (lt_add_of_pos_right (sInf (lengths x y)) (half_pos hε))
    obtain ⟨m, hm, hmt⟩ := exists_lt_of_csInf_lt (hne y z)
      (lt_add_of_pos_right (sInf (lengths y z)) (half_pos hε))
    have h := csInf_le (hbdd x z) (show l + m ∈ lengths x z from cellChain_append hl hm)
    linarith only [h, hlt, hmt]
  · intro x y h
    by_contra hxy
    obtain ⟨r, hr, hcontract⟩ := separated x y hxy
    have hle : dist (r x) (r y) ≤ sInf (lengths x y) :=
      le_csInf (hne x y) fun _ hl => cellChain_dist_le r hcontract hl
    exact (not_le_of_gt (dist_pos.mpr hr)) (h ▸ hle)

/-- A contraction to an apartment gives the lower distance bound. A chain
following the straight segment gives the matching upper bound. -/
theorem cellChainMetric_chart_isometry
    (connected : ∀ x y, ∃ l, CellChain place position x y l)
    (separated : ∀ x y, x ≠ y → ∃ r : X → E, r x ≠ r y ∧
      ∀ c t s, dist (r (place c t)) (r (place c s)) ≤ dist (position t) (position s))
    (chart : E → X) (r : X → E) (hr : ∀ x, r (chart x) = x)
    (hcontract : ∀ c t s, dist (r (place c t)) (r (place c s)) ≤ dist (position t) (position s))
    (hstraight : ∀ x y, CellChain place position (chart x) (chart y) (dist x y)) :
    letI := cellChainMetric connected separated
    Isometry chart := by
  let := cellChainMetric connected separated
  apply Isometry.of_dist_eq
  intro x y
  change sInf {l | CellChain place position (chart x) (chart y) l} = dist x y
  apply IsLeast.csInf_eq
  refine ⟨hstraight x y, fun l hl => ?_⟩
  simpa only [hr] using cellChain_dist_le r hcontract (l := l) hl

/-- A common bound on a function's variation on the closed chambers also
bounds its variation for the intrinsic chain metric. -/
theorem cellChainMetric_lipschitz
    (connected : ∀ x y, ∃ l, CellChain place position x y l)
    (separated : ∀ x y, x ≠ y → ∃ r : X → E, r x ≠ r y ∧
      ∀ c t s, dist (r (place c t)) (r (place c s)) ≤ dist (position t) (position s))
    {Y : Type*} [MetricSpace Y] (k : ℝ≥0) (f : X → Y)
    (hf : ∀ c t s, dist (f (place c t)) (f (place c s)) ≤ k * dist (position t) (position s)) :
    letI := cellChainMetric connected separated
    LipschitzWith k f := by
  let := cellChainMetric connected separated
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hchain {x y : X} {l : ℝ} (h : CellChain place position x y l) :
      dist (f x) (f y) ≤ k * l := by
    induction h with
    | nil => simp
    | cons c t s h ih =>
      rw [mul_add]
      exact (dist_triangle _ _ _).trans (add_le_add (hf c t s) ih)
  change dist (f x) (f y) ≤ (k : ℝ) * sInf {l | CellChain place position x y l}
  rcases eq_or_lt_of_le k.coe_nonneg with hk | hk
  · rw [← hk, zero_mul]
    obtain ⟨l, hl⟩ := connected x y
    simpa only [← hk, zero_mul] using hchain hl
  · rw [← div_le_iff₀' hk]
    apply le_csInf (connected x y)
    intro l hl
    exact (div_le_iff₀' hk).mpr (hchain hl)

end IntrinsicMetric

section Metric

open LinearAlgebraicGroups.Geometry unitInterval Filter
open scoped NNReal Topology

open private affineSegment from LinearAlgebraicGroups.Geometry.CAT0Comparison

variable {X E : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The apartment midpoint argument, after constructing the intrinsic metric and retractions.
The retraction at a point of the apartment preserves distance to that point. -/
theorem cat0_of_apartment_retractions [Nonempty X] {A : Type*} (chart : A → E → X)
    (hchart : ∀ a, Isometry (chart a))
    (hpair : ∀ x y : X, ∃ (a : A) (u v : E), chart a u = x ∧ chart a v = y)
    (hretract : ∀ (a : A) (m : E), ∃ r : X → E,
      (∀ u, r (chart a u) = u) ∧ LipschitzWith 1 r ∧
      ∀ z, dist (r z) m = dist z (chart a m)) :
    CAT0 X := by
  have hgeo : IsGeodesicSpace X := by
    refine ⟨inferInstance, fun x y => ?_⟩
    obtain ⟨a, u, v, rfl, rfl⟩ := hpair x y
    exact ⟨(affineSegment u v).mapIsometry (hchart a)⟩
  apply (cat0_iff_midpointComparison hgeo).2
  intro z x y p
  obtain ⟨a, u, v, rfl, rfl⟩ := hpair x y
  let half : I := ⟨1 / 2, by norm_num⟩
  let seg := affineSegment u v
  let m := seg.val half
  obtain ⟨r, hfix, hLip, hdist⟩ := hretract a m
  have hcompare (z' : X) :
      dist z' (chart a m) ^ 2 ≤
        (dist z' (chart a u) ^ 2 + dist z' (chart a v) ^ 2) / 2 -
          dist (chart a u) (chart a v) ^ 2 / 4 := by
    have hE : CAT0 E := cat0_of_realInnerProductSpace
    have hm := hE.squaredDistanceComparison.midpointComparison (r z') seg
    change dist (r z') m ^ 2 ≤
      (dist (r z') u ^ 2 + dist (r z') v ^ 2) / 2 - dist u v ^ 2 / 4 at hm
    have hle (w : E) : dist (r z') w ≤ dist z' (chart a w) := by
      simpa [hfix] using hLip.dist_le_mul z' (chart a w)
    have hu : dist (r z') u ^ 2 ≤ dist z' (chart a u) ^ 2 := by gcongr; exact hle u
    have hv : dist (r z') v ^ 2 ≤ dist z' (chart a v) ^ 2 := by gcongr; exact hle v
    rw [hdist, ← (hchart a).dist_eq u v] at hm
    linarith only [hm, hu, hv]
  have heq : p.val half = chart a m := by
    have hh := hcompare (p.val half)
    rw [dist_comm (p.val half) (chart a u), p.dist_source, p.dist_target] at hh
    change dist (p.val half) (chart a m) ^ 2 ≤
      ((1 / 2 * dist (chart a u) (chart a v)) ^ 2 +
        ((1 - 1 / 2) * dist (chart a u) (chart a v)) ^ 2) / 2 -
          dist (chart a u) (chart a v) ^ 2 / 4 at hh
    have hz : dist (p.val half) (chart a m) ^ 2 = 0 := by
      nlinarith only [hh, sq_nonneg (dist (p.val half) (chart a m))]
    exact dist_eq_zero.mp (sq_eq_zero_iff.mp hz)
  change dist z (p.val half) ^ 2 ≤ _
  rw [heq]
  exact hcompare z

/-- Uniformly Lipschitz barycentric coordinates and finite vertex stars imply completeness.
A positive coordinate locates the point in the closed star of its vertex. -/
theorem completeSpace_of_finite_vertex_stars {V C : Type*}
    (cell : C → Set X) (incident : V → Set C) (coord : V → X → ℝ)
    (hcompact : ∀ c, IsCompact (cell c)) (hfinite : ∀ v, (incident v).Finite)
    (K : ℝ≥0) (hL : ∀ v, LipschitzWith K (coord v))
    (hsupport : ∀ v x, 0 < coord v x → x ∈ ⋃ c ∈ incident v, cell c)
    (a : ℝ) (ha : 0 < a) (hlarge : ∀ x, ∃ v, a ≤ coord v x) :
    CompleteSpace X := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨n, hn⟩ := Metric.cauchySeq_iff'.mp hu (a / ((K : ℝ) + 1)) (div_pos ha hK)
  obtain ⟨v, hv⟩ := hlarge (u n)
  have hstar : IsCompact (⋃ c ∈ incident v, cell c) :=
    (hfinite v).isCompact_biUnion (fun c _ => hcompact c)
  refine (hstar.isComplete _ hu (Filter.le_principal_iff.mpr ?_)).imp (fun _ h => h.2)
  change ∀ᶠ j in atTop, u j ∈ ⋃ c ∈ incident v, cell c
  filter_upwards [eventually_ge_atTop n] with j hj
  apply hsupport v
  have hsmall := (lt_div_iff₀ hK).mp (hn j hj)
  have habs := (hL v).dist_le_mul (u j) (u n)
  rw [Real.dist_eq] at habs
  have hdiff := (neg_abs_le (coord v (u j) - coord v (u n))).trans'
    (neg_le_neg habs)
  nlinarith only [hsmall, hdiff, hv, dist_nonneg (x := u j) (y := u n)]

end Metric

section Actions

open LinearAlgebraicGroups.Geometry

/-- A finite isometric action that permutes the open faces fixes an open face
and its barycenter. The face map sends a point to its unique open face. -/
theorem exists_fixed_face_barycenter {Γ X F : Type*} [Group Γ] [Finite Γ]
    [MetricSpace X] [CompleteSpace X] [MulAction Γ X] [IsIsometricSMul Γ X]
    [MulAction Γ F] (hX : CAT0 X) (face : X → F) (barycenter : F → X)
    (hface : ∀ (γ : Γ) x, face (γ • x) = γ • face x)
    (hbary : ∀ (γ : Γ) f, barycenter (γ • f) = γ • barycenter f)
    (hmem : ∀ f, face (barycenter f) = f) :
    ∃ f : F, f ∈ MulAction.fixedPoints Γ F ∧
      barycenter f ∈ MulAction.fixedPoints Γ X ∧ face (barycenter f) = f := by
  obtain ⟨x, hx⟩ := hX.fixedPoints_nonempty_of_finiteGroup (G := Γ)
  have hf : face x ∈ MulAction.fixedPoints Γ F := by
    intro γ
    rw [← hface, hx γ]
  refine ⟨face x, hf, ?_, hmem _⟩
  intro γ
  rw [← hbary, hf γ]

/-- For a face in the standard alcove, its adjoint stabilizer is the product of the
type-preserving stabilizer and its length-zero representatives. -/
theorem mem_stabilizer_iff_mul_representative {H Ω F T : Type*} [Group H] [Group Ω]
    [MulAction H F] [MulAction Ω T] (typeChange : H →* Ω) (representative : Ω → H)
    (hrep : ∀ o, typeChange (representative o) = o)
    (alcoveFaces : Set F) (cotype : F → T)
    (hcotype : ∀ g f, cotype (g • f) = typeChange g • cotype f)
    (hinj : Set.InjOn cotype alcoveFaces)
    (hpres : ∀ o f, f ∈ alcoveFaces → representative o • f ∈ alcoveFaces)
    {f : F} (hf : f ∈ alcoveFaces) (g : H) :
    g • f = f ↔ ∃ (p : H) (o : Ω), p ∈ typeChange.ker ∧ p • f = f ∧
      representative o • f = f ∧ g = p * representative o := by
  constructor
  · intro hg
    let r := representative (typeChange g)
    have hr : r • f = f := by
      apply hinj (hpres _ _ hf) hf
      rw [hcotype, hrep, ← hcotype g f, hg]
    refine ⟨g * r⁻¹, typeChange g, ?_, ?_, hr, ?_⟩
    · change typeChange (g * r⁻¹) = 1
      rw [map_mul, map_inv, hrep, mul_inv_cancel]
    · rw [mul_smul, inv_smul_eq_iff.mpr hr.symm, hg]
    · change g = g * r⁻¹ * r
      rw [mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨p, o, _, hp, ho, rfl⟩
    rw [mul_smul, ho, hp]

end Actions


section Construction

open AlgebraicGeometry CategoryTheory
open scoped Classical NNReal Pointwise TensorProduct CategoryTheory.MonObj ValuativeRel
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer e6Partner)
open Specs.ExceptionalRealAlcove (RealAlcoveData OrderedSubdivision)
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex)
open Specs.ExceptionalIwahoriCongruence (integralRingMap)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment)
open Specs.ExceptionalBuildingTransport (ApartmentIsometries AdjointApartment CentralApartment SplitApartmentLevel)
attribute [local instance] integerAlgebra

noncomputable section

universe u v

set_option linter.style.haveILetI false

private theorem realAffine_one {V : Type u} [AddCommGroup V] [Module ℚ V] (r : RealCoordinates V) :
    realAffine r r (1 : V ≃ᵃ[ℚ] V) = id := by
  funext x
  rw [← realAffineEquiv_apply]
  exact congrArg (fun e : EuclideanApartment V ≃ᵃ[ℝ] EuclideanApartment V => e x)
    (realAffineEquiv_refl r)

section MetricRealization

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf V : Type u} {J : Type v} [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

local notation "types" => A.SimpleWall p

/-- Each point is represented by weights in a chamber of the actual group. -/
abbrev BuildingPoint (C : LocalComparison (j := j) (Wf := Wf) A p) :=
  CosetPoint C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G))

abbrev placePoint (C : LocalComparison (j := j) (Wf := Wf) A p) :=
  CosetPoint.place C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G))

variable (d : RealAlcoveData C.coxeter) (r : RealCoordinates V)

local notation "position" => simplexPoint r d.vertex
local notation "P" => BuildingPoint C

variable (hW : ∀ w : A.affineWeylGroup, Isometry (realAffine r r w.val))

private abbrev apartmentSMul {A : ApartmentRoots ℚ V J} (r : RealCoordinates V)
    (w : A.affineWeylGroup) (x : EuclideanApartment V) : EuclideanApartment V :=
  letI := realWeylAction A r
  w • x

local notation:73 w:73 " •ᵣ " x:74 => apartmentSMul r w x

private theorem apartment_smul (w : A.affineWeylGroup) (x : EuclideanApartment V) :
    w •ᵣ x = realAffine r r w.val x :=
  realAffineEquiv_apply r r w.val x

private theorem alcove_cover (x : EuclideanApartment V) :
    ∃ (w : A.affineWeylGroup) (t : Weights types), x = w •ᵣ position t := by
  obtain ⟨w, t, h⟩ := d.covers r x
  exact ⟨w, t, ((apartment_smul r w _).trans h).symm⟩

private theorem alcove_gluing (w v : A.affineWeylGroup) (t s : Weights types)
    (h : w •ᵣ position t = v •ᵣ position s) :
    t = s ∧ w⁻¹ * v ∈ standardWallSubgroup C.coxeter.coxeter (cotype t) := by
  obtain ⟨ht, hw⟩ := (d.overlap r w v t s).mp (by
    simpa only [apartment_smul] using h)
  exact ⟨ht, ht.symm ▸ hw⟩

private theorem alcove_fix (t : Weights types) (w : A.affineWeylGroup)
    (h : w ∈ standardWallSubgroup C.coxeter.coxeter (cotype t)) : w •ᵣ position t = position t := by
  have he := (d.overlap r 1 w t t).mpr ⟨rfl, by simpa only [inv_one, one_mul] using h⟩
  letI := realWeylAction A r
  have hEq : (1 : A.affineWeylGroup) • position t = w • position t :=
    (apartment_smul r 1 _).trans (he.trans (apartment_smul r w _).symm)
  simpa only [one_smul] using hEq.symm

variable {q : ℕ} (hB : C.Bruhat q)

private abbrev modelChart : C.G₀ → EuclideanApartment V → P :=
  letI := realWeylAction A r
  apartmentChart C position (alcove_cover d r)

private abbrev modelRetraction (g : C.G₀) (u : A.affineWeylGroup) : P → EuclideanApartment V :=
  letI := realWeylAction A r
  apartmentRetraction C position hB (alcove_fix d r) g u

include hB in
private theorem modelChart_place (g : C.G₀) (w : A.affineWeylGroup) (t : Weights types) :
    modelChart d r g (realAffine r r w.val (position t)) = placePoint C (g * ordinaryLift C w) t := by
  letI := realWeylAction A r
  rw [← apartment_smul r]
  exact apartmentChart_place C position (alcove_cover d r) (alcove_gluing d r) hB g w t

include hB in
private theorem modelChart_pair (x y : P) :
    ∃ (g : C.G₀) (v w : EuclideanApartment V), modelChart d r g v = x ∧ modelChart d r g w = y :=
  letI := realWeylAction A r
  apartmentChart_pair C position (alcove_cover d r) (alcove_gluing d r) hB x y

private theorem modelRetraction_chart (g h : C.G₀) (u v : A.affineWeylGroup)
    (hc : (QuotientGroup.mk ((h : G) * (C.lift v : G)) : G ⧸ C.I) =
      QuotientGroup.mk ((g : G) * (C.lift u : G))) (x : EuclideanApartment V) :
    modelRetraction d r hB g u (modelChart d r h x) = realAffine r r (u * v⁻¹).val x := by
  letI := realWeylAction A r
  rw [← apartment_smul r]
  exact apartmentRetraction_chart C position (alcove_cover d r) (alcove_gluing d r)
    hB (alcove_fix d r) g h u v hc x

private theorem modelRetraction_leftInverse (g : C.G₀) (u : A.affineWeylGroup) :
    Function.LeftInverse (modelRetraction d r hB g u) (modelChart d r g) := by
  intro x
  rw [modelRetraction_chart d r hB g g u u rfl, mul_inv_cancel, ← apartment_smul r]
  letI := realWeylAction A r
  exact one_smul _ x

include hW in
private theorem modelRetraction_cell (g : C.G₀) (u : A.affineWeylGroup) (a : C.G₀) (t s : Weights types) :
    dist (modelRetraction d r hB g u (placePoint C a t))
      (modelRetraction d r hB g u (placePoint C a s)) ≤ dist (position t) (position s) := by
  letI := realWeylAction A r
  let w := relativeLabel C hB (g * ordinaryLift C u) a
  have hw := relativeLabel_mem_cell C hB (g * ordinaryLift C u) a
  have h (b : Weights types) :
      modelRetraction d r hB g u (placePoint C a b) = realAffine r r (u * w).val (position b) :=
    (apartmentRetraction_place C position hB (alcove_fix d r) g u a w b hw).trans (apartment_smul r _ _)
  rw [h, h, (hW _).dist_eq]

include hW hB in
private theorem modelChart_chain (g : C.G₀) (x y : EuclideanApartment V)
    {a b l : ℝ} (h : OrderedSubdivision r d.vertex x y a b l) :
    CellChain (placePoint C) position (modelChart d r g (AffineMap.lineMap x y a))
      (modelChart d r g (AffineMap.lineMap x y b)) l := by
  induction h with
  | nil => exact CellChain.nil _
  | cons _ w t s ht hs _ ih =>
    rw [← ht, modelChart_place d r hB]
    rw [← hs, modelChart_place d r hB] at ih
    rw [← hs, (hW w).dist_eq]
    exact CellChain.cons _ t s ih

include hW hB in
private theorem modelChart_straight (g : C.G₀) (x y : EuclideanApartment V) :
    CellChain (placePoint C) position (modelChart d r g x) (modelChart d r g y) (dist x y) := by
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    modelChart_chain d r hW hB g x y (d.subdivision r x y)

include hW hB in
private theorem building_chains (x y : P) : ∃ l, CellChain (placePoint C) position x y l := by
  obtain ⟨g, v, w, rfl, rfl⟩ := modelChart_pair d r hB x y
  exact ⟨_, modelChart_straight d r hW hB g v w⟩

include hW hB in
private theorem building_separated (x y : P) (hne : x ≠ y) :
    ∃ f : P → EuclideanApartment V, f x ≠ f y ∧
      ∀ c t s, dist (f (placePoint C c t)) (f (placePoint C c s)) ≤ dist (position t) (position s) := by
  obtain ⟨g, v, w, rfl, rfl⟩ := modelChart_pair d r hB x y
  refine ⟨modelRetraction d r hB g 1, ?_, modelRetraction_cell d r hW hB g 1⟩
  rw [modelRetraction_leftInverse d r hB, modelRetraction_leftInverse d r hB]
  exact fun h => hne (congrArg _ h)

@[instance_reducible]
private def buildingMetric : MetricSpace P :=
  cellChainMetric (building_chains d r hW hB) (building_separated d r hW hB)

private theorem modelChart_isometry (g : C.G₀) :
    letI := buildingMetric d r hW hB
    Isometry (modelChart d r g) :=
  cellChainMetric_chart_isometry (building_chains d r hW hB) (building_separated d r hW hB)
    (modelChart d r g) (modelRetraction d r hB g 1) (modelRetraction_leftInverse d r hB g 1)
    (modelRetraction_cell d r hW hB g 1) (modelChart_straight d r hW hB g)

private theorem modelRetraction_lipschitz (g : C.G₀) (u : A.affineWeylGroup) :
    letI := buildingMetric d r hW hB
    LipschitzWith 1 (modelRetraction d r hB g u) :=
  cellChainMetric_lipschitz (building_chains d r hW hB) (building_separated d r hW hB)
    1 _ (by simpa only [NNReal.coe_one, one_mul] using modelRetraction_cell d r hW hB g u)

private theorem building_cat0 :
    letI := buildingMetric d r hW hB
    Geometry.CAT0 P := by
  letI := buildingMetric d r hW hB
  letI : Nonempty P := ⟨modelChart d r 1 0⟩
  refine cat0_of_apartment_retractions (modelChart d r) (modelChart_isometry d r hW hB)
    (modelChart_pair d r hB) ?_
  intro g m
  obtain ⟨u, t, rfl⟩ := d.covers r m
  refine ⟨modelRetraction d r hB g u, modelRetraction_leftInverse d r hB g u,
    modelRetraction_lipschitz d r hW hB g u, ?_⟩
  intro z
  obtain ⟨a, s, rfl⟩ := CosetPoint.place_surjective _ _ _ _ z
  obtain ⟨h, ⟨v, hv⟩, ⟨w, hw⟩⟩ := marked_common_apartment C hB
    ⟨QuotientGroup.mk (g * ordinaryLift C u : C.G₀).val, _, rfl⟩
    ⟨QuotientGroup.mk (a : G), _, rfl⟩
  let x := realAffine r r w.val (position s)
  let y := realAffine r r v.val (position t)
  have hx : modelChart d r h x = placePoint C a s :=
    (modelChart_place d r hB h w s).trans (CosetPoint.place_eq_of_chamber_eq _ _ _ _ _ _ _ hw)
  have hy : modelChart d r h y = modelChart d r g (realAffine r r u.val (position t)) := by
    rw [show y = realAffine r r v.val (position t) from rfl, modelChart_place d r hB,
      modelChart_place d r hB]
    exact CosetPoint.place_eq_of_chamber_eq _ _ _ _ _ _ _ hv
  calc
    dist (modelRetraction d r hB g u (placePoint C a s)) (realAffine r r u.val (position t)) =
        dist (modelRetraction d r hB g u (modelChart d r h x))
          (modelRetraction d r hB g u (modelChart d r h y)) := by
      rw [hy, modelRetraction_leftInverse d r hB, hx]
    _ = dist x y := by
      rw [modelRetraction_chart d r hB g h u v hv, modelRetraction_chart d r hB g h u v hv,
        (hW (u * v⁻¹)).dist_eq]
    _ = _ := by rw [← (modelChart_isometry d r hW hB h).dist_eq, hx, hy]

include hB in
private theorem modelChart_base (g : C.G₀) (t : Weights types) :
    modelChart d r g (position t) = placePoint C g t := by
  have hr := congrFun (realAffine_one r) (position t)
  calc
    modelChart d r g (position t) = modelChart d r g (realAffine r r (1 : V ≃ᵃ[ℚ] V) (position t)) :=
      congrArg _ hr.symm
    _ = placePoint C (g * ordinaryLift C 1) t := modelChart_place d r hB g 1 t
    _ = placePoint C g t := by
      apply CosetPoint.place_eq_of_chamber_eq
      exact QuotientGroup.mk_mul_of_mem (g : G) (lift_one_mem_iwahori C)

private theorem compact_modelSimplex :
    IsCompact (Set.range position) := by
  letI : Finite types := d.finiteWalls
  letI := Fintype.ofFinite types
  let f (t : types → ℝ) := ∑ i, t i • rationalPoint r (d.vertex i)
  have hc : Continuous f := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).smul continuous_const
  let simplex : Set (types → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1}
  have hclosed : IsClosed simplex := by
    have h : simplex = (⋂ i : types, {t : types → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i = 1} := by
      ext t
      simp [simplex]
    rw [h]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  have hsub : simplex ⊆ Set.Icc 0 1 := by
    intro t ht
    refine ⟨ht.1, fun i => ?_⟩
    have hi : t i ≤ ∑ j, t j :=
      Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)
    exact hi.trans_eq ht.2
  have h : Set.range position = f '' simplex := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, ⟨t.property.1, by simpa only [finsum_eq_sum_of_fintype] using t.property.2⟩,
        by simp only [f, simplexPoint, Specs.ExceptionalRealAlcove.simplexPoint, finsum_eq_sum_of_fintype]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1, by simpa only [finsum_eq_sum_of_fintype] using ht.2⟩,
        by simp only [f, simplexPoint, Specs.ExceptionalRealAlcove.simplexPoint, finsum_eq_sum_of_fintype]⟩
  rw [h]
  exact (isCompact_Icc.of_isClosed_subset hclosed hsub).image hc

private def vertexCotype (i : types) : Set types := {i}ᶜ

private abbrev Vertex := Σ i : types, G ⧸ parahoric C (vertexCotype i)

private def vertexCoordinate (v : Vertex (C := C)) : P → ℝ :=
  Quotient.lift (fun (z : C.G₀ × Weights types) =>
    if (QuotientGroup.mk (z.1 : G) : G ⧸ parahoric C (vertexCotype v.1)) = v.2
      then z.2.val v.1 else 0) (by
        rintro ⟨g, t⟩ ⟨h, s⟩ ⟨rfl, hm⟩
        by_cases ht : t.val v.1 = 0
        · simp [ht]
        have hsub : cotype t ⊆ vertexCotype v.1 := by
          intro i hi
          have hne : i ≠ v.1 := fun he => ht (he ▸ hi)
          exact hne
        have he : (QuotientGroup.mk (g : G) : G ⧸ parahoric C (vertexCotype v.1)) =
            QuotientGroup.mk (h : G) :=
          QuotientGroup.eq.mpr (faceSubgroup_mono _ _ _ hsub hm)
        simp only [he])

private theorem vertexCoordinate_place (v : Vertex (C := C)) (g : C.G₀) (t : Weights types) :
    vertexCoordinate v (placePoint C g t) =
      if (QuotientGroup.mk (g : G) : G ⧸ parahoric C (vertexCotype v.1)) = v.2
        then t.val v.1 else 0 := rfl

private theorem weight_dist_bound (i : types) :
    ∃ k : ℝ≥0, ∀ t s : Weights types,
      dist (t.val i) (s.val i) ≤ (k : ℝ) * dist (position t) (position s) := by
  let v := Specs.ExceptionalRealAlcove.realWallValue A r i.val (rationalPoint r (d.vertex i))
  have hv : 0 < v := d.opposite_pos r i
  let L := (LinearMap.toContinuousLinearMap (realWallMap A r i.val).linear :
    EuclideanApartment V →L[ℝ] ℝ)
  refine ⟨‖L‖₊ / ⟨v, hv.le⟩, fun t s => ?_⟩
  have hL : L (position t - position s) = v * t.val i - v * s.val i := by
    change (realWallMap A r i.val).linear (position t - position s) = _
    rw [← vsub_eq_sub, AffineMap.linear_apply_vsub]
    change Specs.ExceptionalRealAlcove.realWallValue A r i.val (Specs.ExceptionalRealAlcove.simplexPoint r d.vertex t) -
      Specs.ExceptionalRealAlcove.realWallValue A r i.val (Specs.ExceptionalRealAlcove.simplexPoint r d.vertex s) = _
    rw [d.wall_weight r t i, d.wall_weight r s i]
  have h := L.le_opNorm (position t - position s)
  rw [← dist_eq_norm, hL, ← mul_sub, norm_mul, Real.norm_of_nonneg hv.le, ← dist_eq_norm] at h
  change _ ≤ (‖L‖ / v) * _
  rw [div_mul_eq_mul_div, le_div_iff₀ hv, mul_comm _ v]
  exact h

private def chamberRepresentative (c : Chamber C.I C.G₀) : C.G₀ := c.property.choose

private theorem chamberRepresentative_spec (c : Chamber C.I C.G₀) :
    (QuotientGroup.mk (chamberRepresentative c : G) : G ⧸ C.I) = c.val :=
  c.property.choose_spec

private def incidentChambers (v : Vertex (C := C)) : Set (Chamber C.I C.G₀) :=
  {c | (QuotientGroup.mk (chamberRepresentative c : G) : G ⧸ parahoric C (vertexCotype v.1)) = v.2}

include d hB in
private theorem incidentChambers_finite (hq : 0 < q) (v : Vertex (C := C)) :
    (incidentChambers v).Finite := by
  by_cases hne : (incidentChambers v).Nonempty
  · obtain ⟨c, hc⟩ := hne
    let g := chamberRepresentative c
    letI : Finite (standardWallSubgroup C.coxeter.coxeter (vertexCotype v.1)) :=
      d.finiteFaceSubgroup _ (fun h => by
        have hi : v.1 ∈ vertexCotype v.1 := h ▸ Set.mem_univ _
        exact hi rfl)
    refine ((marked_incident_finite C hB hq (vertexCotype v.1) (g : G)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro b hb
    refine ⟨chamberRepresentative b, ?_, chamberRepresentative_spec b⟩
    exact QuotientGroup.eq.mp (hc.trans hb.symm)
  · exact (Set.not_nonempty_iff_eq_empty.mp hne).symm ▸ Set.finite_empty

include hW hB in
private theorem building_complete (hq : 0 < q) :
    letI := buildingMetric d r hW hB
    CompleteSpace P := by
  letI := buildingMetric d r hW hB
  letI : Finite types := d.finiteWalls
  letI := Fintype.ofFinite types
  let cell (c : Chamber C.I C.G₀) := Set.range (placePoint C (chamberRepresentative c))
  choose k hk using weight_dist_bound d r
  let kmax := Finset.univ.sup k
  let a : ℝ := 1 / (Fintype.card types + 1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  refine completeSpace_of_finite_vertex_stars cell incidentChambers vertexCoordinate ?_
    (incidentChambers_finite d hB hq) kmax ?_ ?_ a ha ?_
  · intro c
    have hc : cell c = modelChart d r (chamberRepresentative c) '' Set.range position := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun t => (modelChart_base d r hB _ t).symm)
    rw [hc]
    exact (compact_modelSimplex d r).image (modelChart_isometry d r hW hB _).continuous
  · intro v
    apply cellChainMetric_lipschitz (building_chains d r hW hB) (building_separated d r hW hB)
    intro g t s
    rw [vertexCoordinate_place, vertexCoordinate_place]
    split_ifs
    · apply (hk v.1 t s).trans
      gcongr
      exact Finset.le_sup (f := k) (Finset.mem_univ v.1)
    · rw [dist_self]; positivity
  · intro v x hx
    obtain ⟨g, t, rfl⟩ := CosetPoint.place_surjective _ _ _ _ x
    let c : Chamber C.I C.G₀ := ⟨QuotientGroup.mk (g : G), g, rfl⟩
    have he : (QuotientGroup.mk (chamberRepresentative c : G) : G ⧸ C.I) = QuotientGroup.mk (g : G) :=
      chamberRepresentative_spec c
    have hg : (QuotientGroup.mk (g : G) : G ⧸ parahoric C (vertexCotype v.1)) = v.2 := by
      rw [vertexCoordinate_place] at hx
      split_ifs at hx with hg
      · exact hg
      · exact (lt_irrefl _ hx).elim
    have hmem : (chamberRepresentative c : G)⁻¹ * (g : G) ∈ parahoric C (vertexCotype v.1) :=
      Subgroup.subset_closure (Or.inl (QuotientGroup.eq.mp he))
    have he' : (QuotientGroup.mk (chamberRepresentative c : G) : G ⧸ parahoric C (vertexCotype v.1)) =
        QuotientGroup.mk (g : G) := QuotientGroup.eq.mpr hmem
    have hc : c ∈ incidentChambers v := he'.trans hg
    exact Set.mem_biUnion hc ⟨t, CosetPoint.place_eq_of_chamber_eq _ _ _ _ _ _ _ he⟩
  · intro x
    obtain ⟨g, t, rfl⟩ := CosetPoint.place_surjective _ _ _ _ x
    have h : ∃ i, a ≤ t.val i := by
      by_contra! h
      have ht := t.property.2
      rw [finsum_eq_sum_of_fintype] at ht
      have hs : (∑ i, t.val i) ≤ ∑ _ : types, a :=
        Finset.sum_le_sum fun i _ => (h i).le
      rw [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
      have hn : (0 : ℝ) < (Fintype.card types : ℝ) + 1 := by positivity
      have hn' : (Fintype.card types : ℝ) * (1 / ((Fintype.card types : ℝ) + 1)) < 1 := by
        rw [mul_one_div, div_lt_iff₀ hn, one_mul]
        exact lt_add_one _
      exact (not_lt_of_ge hs) hn'
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, QuotientGroup.mk (g : G)⟩, by simpa only [vertexCoordinate_place, ite_true] using hi⟩

private theorem barycenter_rationalPoint (T : Set types) (t : Weights types)
    (h : IsBarycenter T t) : ∃ x : V, rationalPoint r x = position t := by
  letI : Finite types := d.finiteWalls
  letI := Fintype.ofFinite types
  let c (i : types) : ℚ := if i ∈ T then 0 else 1 / (Nat.card {i // i ∉ T} : ℚ)
  have hc (i : types) : (c i : ℝ) = t.val i := by
    rw [h i]
    by_cases hi : i ∈ T <;> simp [c, hi]
  refine ⟨∑ i, c i • d.vertex i, ?_⟩
  simp only [Specs.ExceptionalRealAlcove.rationalPoint, Specs.ExceptionalRealAlcove.simplexPoint, finsum_eq_sum_of_fintype, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hc i, ← map_smul, TensorProduct.tmul_smul]
  rfl

/-- A map that acts isometrically on a common apartment for every pair of points
preserves the distance on the whole complex. -/
private theorem isometry_of_charts {X Y E E' S T : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace E] [MetricSpace E']
    (f : X → Y) (source : S → E → X) (target : T → E' → Y)
    (hsource : ∀ s, Isometry (source s)) (htarget : ∀ t, Isometry (target t))
    (pair : ∀ x y : X, ∃ s u v, source s u = x ∧ source s v = y)
    (h : ∀ s, ∃ (t : T) (e : E → E'), Isometry e ∧ ∀ x, f (source s x) = target t (e x)) :
    Isometry f := by
  apply Isometry.of_dist_eq
  intro x y
  obtain ⟨s, u, v, rfl, rfl⟩ := pair x y
  obtain ⟨t, e, he, hf⟩ := h s
  rw [hf, hf, (htarget t).dist_eq, he.dist_eq, (hsource s).dist_eq]

private def isometricPermutations {H X : Type*} [Group H] [MetricSpace X]
    (act : H →* Equiv.Perm X) (h : ∀ g, Isometry (act g)) :
    H →* (X ≃ᵢ X) where
  toFun g := { toEquiv := act g, isometry_toFun := h g }
  map_one' := IsometryEquiv.toEquiv_injective (act.map_one)
  map_mul' g h := IsometryEquiv.toEquiv_injective (act.map_mul g h)

include hB in
private theorem modelChart_translate (g h : C.G₀) (x : EuclideanApartment V) :
    CosetPoint.translate C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G)) g (modelChart d r h x) =
      modelChart d r (g * h) x := by
  obtain ⟨w, t, rfl⟩ := d.covers r x
  rw [modelChart_place d r hB, modelChart_place d r hB, CosetPoint.translate_place, mul_assoc]

/-- The metric realization of one marked ordinary coset complex. -/
private def buildRealization (hq : 0 < q) :
    Realization C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G)) := by
  letI : Finite types := d.finiteWalls
  letI := buildingMetric d r hW hB
  let translate := CosetPoint.translate C.coxeter.coxeter C.I C.G₀ (fun w => (C.lift w : G))
  let act := isometricPermutations translate (fun g =>
    isometry_of_charts (translate g) (modelChart d r) (modelChart d r)
      (modelChart_isometry d r hW hB) (modelChart_isometry d r hW hB) (modelChart_pair d r hB)
      (fun h => ⟨g * h, id, isometry_id, modelChart_translate d r hB g h⟩))
  have hcat := building_cat0 d r hW hB
  refine {
    Point := P
    metric := buildingMetric d r hW hB
    complete := building_complete d r hW hB hq
    cat0 := hcat
    midpoint := Geometry.SquaredDistanceComparison.midpointComparison
      (Geometry.CAT0.squaredDistanceComparison hcat)
    coordinates := r
    finite_types := d.finiteWalls
    vertex := d.vertex
    vertex_marked := d.marked_vertex
    vertex_unique := d.vertex_unique
    independent := d.affineIndependent r
    closed_alcove := Set.ext (fun x => (d.closed_simplex r x).symm)
    open_alcove := ?_
    weyl_isometry := hW
    wall_group := d.wallSubgroup r
    translated_wall_group := d.translatedWallSubgroup r
    finite_wall_group := d.finiteFaceSubgroup
    iwahori_mem := iwahori_le_ordinary C
    lift_mem := lift_mem_ordinary C
    face_mem := parahoric_le_ordinary C
    face_union := parahoric_eq_iUnion C hB
    face_inter := parahoric_inf C hB d.vertex d.marked_vertex
    apartment_incidence := fun T g => marked_apartment_incidence C hB T g
    incident_finite := ?_
    common_apartment := marked_common_apartment C hB
    place := placePoint C
    place_surjective := CosetPoint.place_surjective _ _ _ _
    place_eq := CosetPoint.place_eq_iff _ _ _ _
    open_face_cosets := CosetPoint.open_face_cosets _ _ _ _
    closed_face_incidence := CosetPoint.closed_face_incidence _ _ _ _
      (fun U T => (parahoric_le_iff C hB d.vertex d.marked_vertex U T).mp)
    barycenter := exists_barycenter
    barycenter_rational := barycenter_rationalPoint d r
    chart := modelChart d r
    chart_isometry := modelChart_isometry d r hW hB
    chart_cover := fun x => by obtain ⟨w, t, hx⟩ := d.covers r x; exact ⟨w, t, hx.symm⟩
    chart_place := modelChart_place d r hB
    intrinsic := fun _ _ => rfl
    translate := act
    translate_chart := modelChart_translate d r hB
    retract := ?_ }
  · ext x
    refine Iff.trans ?_ (d.open_simplex r x).symm
    (
      have ht (t : Weights types) : cotype t = ∅ ↔ ∀ i, 0 < t.val i := by
        simp only [Set.eq_empty_iff_forall_notMem, cotype, Specs.ExceptionalRealAlcove.cotype, Set.mem_ofPred_eq]
        exact ⟨fun h i => lt_of_le_of_ne (t.property.1 i) (Ne.symm (h i)),
          fun h i => (h i).ne'⟩
      simp only [Set.mem_image, Set.mem_ofPred_eq, ht])
  · intro T hT g
    letI := d.finiteFaceSubgroup T hT
    exact marked_incident_finite C hB hq T g
  · intro g u
    refine ⟨modelRetraction d r hB g u, modelRetraction_lipschitz d r hW hB g u,
      modelRetraction_leftInverse d r hB g u, ?_,
      fun h v hc x => modelRetraction_chart d r hB g h u v hc x⟩
    intro h w t hw
    letI := realWeylAction A r
    exact (apartmentRetraction_place C position hB (alcove_fix d r) g u h w t hw).trans (apartment_smul r _ _)

private theorem realAffine_trans_apply {V V' V'' : Type u}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
    [AddCommGroup V''] [Module ℚ V'']
    (r : RealCoordinates V) (r' : RealCoordinates V') (r'' : RealCoordinates V'')
    (f : V ≃ᵃ[ℚ] V') (g : V' ≃ᵃ[ℚ] V'') (x : EuclideanApartment V) :
    realAffine r r'' (f.trans g) x = realAffine r' r'' g (realAffine r r' f x) := by
  simpa only [AffineEquiv.trans_apply, realAffineEquiv_apply] using
    congrArg (fun e : EuclideanApartment V ≃ᵃ[ℝ] EuclideanApartment V'' => e x)
      (realAffineEquiv_trans r r' r'' f g)

private theorem realAffine_mul_apply (f g : V ≃ᵃ[ℚ] V) (x : EuclideanApartment V) :
    realAffine r r (f * g) x = realAffine r r f (realAffine r r g x) :=
  realAffine_trans_apply r r r g f x

/-- The marked building over one local level. -/
private def buildLocal (hq : 0 < q) : Building C where
  realization := buildRealization d r hW hB hq
  iwahori_inter_normalizer := C.localIwahori.intersection
  face_normalizer := parahoric_normalizer_image C hB
  lift_difference := marked_lift_difference C
  normalizer_action n hn x := by
    let X := buildRealization d r hW hB hq
    change X.translate ⟨n, hn⟩ (X.chart 1 x) =
      X.chart 1 (realAffine r r (C.affine n) x)
    have hm : (n : G) ∈ C.G₀ ⊓ C.N := ⟨hn, n.property⟩
    rw [hB.ordinary_normalizer] at hm
    obtain ⟨m, hm, he⟩ := hm
    have hnm : m = n := Subtype.ext he
    subst m
    let v : A.affineWeylGroup := ⟨C.affine n, hm⟩
    obtain ⟨w, t, rfl⟩ := d.covers r x
    rw [X.translate_chart, mul_one, ← realAffine_mul_apply r]
    have hvw : C.affine n * w.val = (v * w).val := rfl
    rw [hvw]
    change X.chart ⟨n, hn⟩ (realAffine X.coordinates X.coordinates w.val
      (simplexPoint X.coordinates X.vertex t)) = X.chart 1
        (realAffine X.coordinates X.coordinates (v * w).val (simplexPoint X.coordinates X.vertex t))
    rw [X.chart_place, X.chart_place, one_mul]
    apply (X.place_eq _ _ _ _).2
    refine ⟨rfl, ?_⟩
    have hd := normalizer_lift_difference C (n * C.lift w) (v * w) (by
      rw [map_mul, C.lift_label]
      rfl)
    have hi := unitTorus_le_iwahori C (C.T₀.inv_mem hd)
    apply Subgroup.subset_closure
    refine Or.inl ?_
    change ((n : G) * (C.lift w : G))⁻¹ * (C.lift (v * w) : G) ∈ C.I
    simpa only [Subgroup.coe_mul, mul_inv_rev, inv_inv] using hi
  stabilizer T t ht g := by
    subst T
    exact CosetPoint.translate_fixes_iff _ _ _ _ g t

end MetricRealization

section Weights

variable {B B' : Type*}

private abbrev reindexWeights (d : B ≃ B') (t : Weights B) : Weights B' :=
  ExceptionalBuildingTransport.transportWeights d t

private theorem reindexWeights_apply (d : B ≃ B') (t : Weights B) (i : B) :
    (reindexWeights d t).val (d i) = t.val i :=
  ExceptionalBuildingTransport.transportWeights_apply d t i

private theorem reindexWeights_eq (d : B ≃ B') (t : Weights B) (s : Weights B')
    (hs : ∀ i, s.val (d i) = t.val i) : reindexWeights d t = s := by
  apply Subtype.ext
  funext j
  obtain ⟨i, rfl⟩ := d.surjective j
  exact (reindexWeights_apply d t i).trans (hs i).symm

private theorem reindexWeights_cotype (d : B ≃ B') (t : Weights B) :
    cotype (reindexWeights d t) = d '' cotype t :=
  ExceptionalBuildingTransport.transportWeights_cotype d t

private def weightPermutations (B : Type*) : Equiv.Perm B →* Equiv.Perm (Weights B) where
  toFun d :=
    { toFun := reindexWeights d
      invFun := reindexWeights d.symm
      left_inv := fun t => Subtype.ext (funext fun i => by
        change t.val (d.symm (d i)) = t.val i
        rw [Equiv.symm_apply_apply])
      right_inv := fun t => Subtype.ext (funext fun i => by
        change t.val (d (d.symm i)) = t.val i
        rw [Equiv.apply_symm_apply]) }
  map_one' := Equiv.ext (fun _ => rfl)
  map_mul' _ _ := Equiv.ext (fun _ => rfl)

private theorem reindexWeights_support_barycenter (d : Equiv.Perm B) (T : Set B)
    (hT : d '' T = T) (t : Weights B) (hb : IsBarycenter T t) :
    reindexWeights d t = t := by
  refine reindexWeights_eq d t t (fun i => ?_)
  have hi : d i ∈ T ↔ i ∈ T := by
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := (show d i ∈ d '' T from hT.symm ▸ hi)
      exact d.injective he ▸ hj
    · intro hi
      exact hT ▸ (Set.mem_image_of_mem d hi)
  rw [hb (d i), hb i, hi]

end Weights

section GeometricComparisons

variable {K K' : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']
  {D D' : BasedRootDatum.{u}} {M : Model D} {M' : Model D'}
  {G G' Wf Wf' V V' : Type u} {J J' : Type v} [Group G] [Group G'] [Group Wf] [Group Wf']
  [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  {j : G →* FieldPoints M K} {j' : G' →* FieldPoints M' K'}
  {A : ApartmentRoots ℚ V J} {p : V} {A' : ApartmentRoots ℚ V' J'} {p' : V'}
  {C : LocalComparison (j := j) (Wf := Wf) A p}
  {C' : LocalComparison (j := j') (Wf := Wf') A' p'}

local notation "B" => A.SimpleWall p
local notation "B'" => A'.SimpleWall p'

variable (X : Building C) (Y : Building C')

private theorem place_eq_of_chamber (g h : C.G₀) (t : Weights B)
    (he : (QuotientGroup.mk (g : G) : G ⧸ C.I) = QuotientGroup.mk (h : G)) :
    X.realization.place g t = X.realization.place h t :=
  (X.realization.place_eq _ _ _ _).2 ⟨rfl, Subgroup.subset_closure (Or.inl (QuotientGroup.eq.mp he))⟩

private theorem chamberCoset_of_unit {x : G} (n : C.N) (hn : x * (n : G)⁻¹ ∈ C.T₀) :
    (QuotientGroup.mk x : G ⧸ C.I) = QuotientGroup.mk (n : G) := by
  let d : C.N := ⟨x * (n : G)⁻¹, by
    have hh := hn
    rw [← (show C.I ⊓ C.N = C.T₀ from C.localIwahori.intersection)] at hh
    exact hh.2⟩
  have hd : C.affine d = 1 := (normalizer_mem_unitTorus_iff C d).mp hn
  have hc : C.affine (n⁻¹ * d * n) = 1 := by simp [hd]
  have hi := unitTorus_le_iwahori C ((normalizer_mem_unitTorus_iff C _).mpr hc)
  apply QuotientGroup.eq.mpr
  apply C.I.inv_mem_iff.mp
  have he : (x⁻¹ * (n : G))⁻¹ = (↑(n⁻¹ * d * n) : G) := by
    change (x⁻¹ * (n : G))⁻¹ = (n : G)⁻¹ * (x * (n : G)⁻¹) * n
    group
  rw [he]
  exact hi

private theorem base_chart_place (g : C.G₀) (t : Weights B) :
    X.realization.chart g (simplexPoint X.realization.coordinates X.realization.vertex t) =
      X.realization.place g t := by
  have h := X.realization.chart_place g 1 t
  rw [show (1 : A.affineWeylGroup).val = (1 : V ≃ᵃ[ℚ] V) from rfl, realAffine_one, id_eq] at h
  exact h.trans (place_eq_of_chamber X _ _ _ (QuotientGroup.mk_mul_of_mem (g : G) (lift_one_mem_iwahori C)))

private theorem realization_pair (x y : X.realization.Point) :
    ∃ (g : C.G₀) (v w : EuclideanApartment V), X.realization.chart g v = x ∧ X.realization.chart g w = y := by
  obtain ⟨a, t, rfl⟩ := X.realization.place_surjective x
  obtain ⟨b, s, rfl⟩ := X.realization.place_surjective y
  obtain ⟨g, ⟨v, hv⟩, ⟨w, hw⟩⟩ := X.realization.common_apartment
    ⟨QuotientGroup.mk (a : G), a, rfl⟩ ⟨QuotientGroup.mk (b : G), b, rfl⟩
  refine ⟨g, _, _, (X.realization.chart_place g v t).trans (place_eq_of_chamber X _ _ _ hv),
    (X.realization.chart_place g w s).trans (place_eq_of_chamber X _ _ _ hw)⟩

/-- The marked placement determines the canonical identification with the weighted
parahoric quotient used to define the algebraic actions. -/
private def gluedPointsEquiv : Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B) ≃ X.realization.Point :=
  let f : Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B) → X.realization.Point :=
    Quotient.lift (fun (z : C.G₀ × Weights B) => X.realization.place z.1 z.2) (by
      rintro ⟨g, t⟩ ⟨h, s⟩ hh
      exact (X.realization.place_eq g h t s).mpr hh)
  Equiv.ofBijective f ⟨by
    intro x y h
    induction x using Quotient.inductionOn with
    | _ z =>
      induction y using Quotient.inductionOn with
      | _ z' =>
        exact Quotient.sound ((X.realization.place_eq z.1 z'.1 z.2 z'.2).mp h),
    by
      intro x
      obtain ⟨g, t, h⟩ := X.realization.place_surjective x
      exact ⟨Specs.ExceptionalBuildingActions.place (C := C) (cotype := @cotype B) g t, h⟩⟩

private theorem gluedPointsEquiv_place (g : C.G₀) (t : Weights B) :
    gluedPointsEquiv X (Specs.ExceptionalBuildingActions.place (C := C) (cotype := @cotype B) g t) = X.realization.place g t := rfl

private theorem realAffine_intertwines (e : V ≃ᵃ[ℚ] V') (w : V ≃ᵃ[ℚ] V) (w' : V' ≃ᵃ[ℚ] V')
    (h : ∀ x, w' (e x) = e (w x)) (x : EuclideanApartment V) :
    realAffine X.realization.coordinates Y.realization.coordinates e
      (realAffine X.realization.coordinates X.realization.coordinates w x) =
    realAffine Y.realization.coordinates Y.realization.coordinates w'
      (realAffine X.realization.coordinates Y.realization.coordinates e x) := by
  rw [← realAffine_trans_apply, ← realAffine_trans_apply]
  exact congrArg (fun f => realAffine X.realization.coordinates Y.realization.coordinates f x)
    (AffineEquiv.ext (fun x => (h x).symm))

private theorem markedWall_image {φ : G →* G'} {e : V ≃ᵃ[ℚ] V'} (m : Specs.ExceptionalBuildingTransport.MarkedTransport C C' φ e)
    (i : B) : e '' A.wallHyperplane i.val = A'.wallHyperplane (m.wall i).val := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Set.mem_image]
  change (∃ z, A.wallValue i.val z = 0 ∧ e z = e x) ↔ A'.wallValue (m.wall i).val (e x) = 0
  rw [m.wall_value]
  exact ⟨fun ⟨z, hz, he⟩ => e.injective he ▸ hz, fun h => ⟨x, h, rfl⟩⟩

variable {X Y}

private theorem transport_simplex (e : V ≃ᵃ[ℚ] V') (d : B ≃ B')
    (h : ∀ i, IsAlcoveVertex A' p' (d i) (e (X.realization.vertex i))) (t : Weights B) :
    simplexPoint Y.realization.coordinates Y.realization.vertex (reindexWeights d t) =
      realAffine X.realization.coordinates Y.realization.coordinates e
        (simplexPoint X.realization.coordinates X.realization.vertex t) := by
  letI : Finite B := X.realization.finite_types
  letI : Finite B' := Y.realization.finite_types
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite B'
  exact ExceptionalBuildingTransport.transportWeights_rational d t X.realization.vertex Y.realization.vertex e
    (fun i => (Y.realization.vertex_unique _ _ (h i)).symm)

private def transportRepresentative {φ : G →* G'} {e : V ≃ᵃ[ℚ] V'} (m : Specs.ExceptionalBuildingTransport.MarkedTransport C C' φ e)
    (g : C.G₀) : C'.G₀ :=
  ⟨φ g, show (g : G) ∈ C'.G₀.comap φ from m.group.symm ▸ g.property⟩

private theorem chart_of_markedTransport {φ : G →* G'} {e : V ≃ᵃ[ℚ] V'}
    (m : Specs.ExceptionalBuildingTransport.MarkedTransport C C' φ e) (f : X.realization.Point → Y.realization.Point)
    (hf : ∀ g t, f (X.realization.place g t) = Y.realization.place (transportRepresentative m g)
      (reindexWeights m.wall t)) (g : C.G₀) (x : EuclideanApartment V) :
    f (X.realization.chart g x) = Y.realization.chart (transportRepresentative m g)
      (realAffine X.realization.coordinates Y.realization.coordinates e x) := by
  obtain ⟨w, t, rfl⟩ := X.realization.chart_cover x
  rw [X.realization.chart_place, hf, realAffine_intertwines X Y e w.val (m.ordinary w).val (m.label w)]
  have he := transport_simplex (X := X) (Y := Y) e m.wall
    (fun i => m.vertex i _ (X.realization.vertex_marked i)) t
  rw [← he, Y.realization.chart_place]
  apply place_eq_of_chamber
  have h := chamberCoset_of_unit (C'.lift (m.ordinary w)) (m.lift w)
  have h' := congrArg ((φ (g : G)) • ·) h
  change (QuotientGroup.mk (φ (g : G) * φ (C.lift w)) : G' ⧸ C'.I) =
    QuotientGroup.mk (φ (g : G) * (C'.lift (m.ordinary w) : G')) at h'
  change (QuotientGroup.mk (φ ((g : G) * (C.lift w : G))) : G' ⧸ C'.I) = _
  rw [map_mul]
  exact h'

/-- An actual comparison of marked point groups induces an isometry for
the chain metrics and agrees with its stated affine map on every apartment. -/
private def inducedRealizationMap (X : Building C) (Y : Building C')
    (φ : G →* G') (e : V ≃ₗ[ℚ] V')
    (m : Specs.ExceptionalBuildingTransport.MarkedTransport C C' φ e.toAffineEquiv)
    (he : Isometry (realAffine X.realization.coordinates Y.realization.coordinates e.toAffineEquiv)) :
    RealizationMap X.realization Y.realization φ e := by
  let f₀ : Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B) → Y.realization.Point :=
    Quotient.lift (fun (z : C.G₀ × Weights B) =>
      Y.realization.place (transportRepresentative m z.1) (reindexWeights m.wall z.2)) (by
      rintro ⟨g, t⟩ ⟨h, s⟩ hrel
      obtain ⟨rfl, hm⟩ : t = s ∧ (g : G)⁻¹ * (h : G) ∈ parahoric C (cotype t) := hrel
      apply (Y.realization.place_eq _ _ _ _).mpr
      refine ⟨rfl, ?_⟩
      change (φ g)⁻¹ * φ h ∈ parahoric C' (cotype (reindexWeights m.wall t))
      rw [reindexWeights_cotype, ← map_inv, ← map_mul]
      exact show (g : G)⁻¹ * (h : G) ∈ (parahoric C' (m.wall '' cotype t)).comap φ from
        (m.face (cotype t)).symm ▸ hm)
  let f := f₀ ∘ (gluedPointsEquiv X).symm
  have hplace (g : C.G₀) (t : Weights B) :
      f (X.realization.place g t) = Y.realization.place (transportRepresentative m g)
        (reindexWeights m.wall t) := by
    rw [← gluedPointsEquiv_place X g t]
    exact congrArg f₀ ((gluedPointsEquiv X).symm_apply_apply _)
  have hchart := chart_of_markedTransport m f hplace
  exact {
    maps_group := fun _ hg => m.group.symm ▸ hg
    wall := m.wall
    wall_eq := markedWall_image m
    iwahori := m.iwahori
    parahoric_eq := m.face
    point := f
    isometry := isometry_of_charts f X.realization.chart Y.realization.chart
      X.realization.chart_isometry Y.realization.chart_isometry (realization_pair X)
      (fun g => ⟨transportRepresentative m g, _, he, hchart g⟩)
    chart := hchart
    place := fun g t s hs => (hplace g t).trans (congrArg _ (reindexWeights_eq m.wall t s hs)) }

private theorem realizationMap_onto (X : Building C) (Y : Building C')
    {φ : G →* G'} {e : V ≃ₗ[ℚ] V'}
    (m : RealizationMap X.realization Y.realization φ e)
    (h : ∀ y : C'.G₀, ∃ x : C.G₀,
      (QuotientGroup.mk (φ x) : G' ⧸ C'.I) = QuotientGroup.mk (y : G')) :
    Function.Surjective m.point := by
  intro z
  obtain ⟨y, s, rfl⟩ := Y.realization.place_surjective z
  obtain ⟨x, hx⟩ := h y
  let t := reindexWeights m.wall.symm s
  refine ⟨X.realization.place x t, ?_⟩
  have hs (i : B) : s.val (m.wall i) = t.val i := by
    change s.val (m.wall i) = s.val (m.wall.symm.symm i)
    rfl
  exact (m.place x t s hs).trans (place_eq_of_chamber Y _ _ _ hx)

end GeometricComparisons

section Adjoint

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {G Wf V : Type u} {J : Type v}
  [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

local notation "B" => A.SimpleWall p
local notation "Ω" => alcoveStabilizer A (A.alcove p)

private abbrev adjointCoordinates (Q : C.TypeQuotient) :
    Specs.ExceptionalBuildingActions.Coordinates C Q (Weights B) where
  cotype := cotype
  perm := (weightPermutations B).comp Q.wallPerm
  cotype_perm ω t := reindexWeights_cotype (Q.wallPerm ω) t

variable (X : Building C) {Q : C.TypeQuotient}

local notation "ρ" => X.realization.coordinates
local notation "position" => simplexPoint ρ X.realization.vertex

private abbrev gluedPlace := Specs.ExceptionalBuildingActions.place (C := C) (cotype := @cotype B)

private abbrev realizePermutations {H : Type*} [Group H]
    (act : H →* Equiv.Perm (Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B))) :
    H →* Equiv.Perm X.realization.Point :=
  ((gluedPointsEquiv X).permCongrHom.toMonoidHom).comp act

private theorem realizePermutations_apply {H : Type*} [Group H]
    (act : H →* Equiv.Perm (Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B)))
    (g : H) (x : Specs.ExceptionalBuildingActions.Point (C := C) (@cotype B)) :
    realizePermutations X act g (gluedPointsEquiv X x) = gluedPointsEquiv X (act g x) := by
  simp only [realizePermutations, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]

variable (ad : Specs.ExceptionalBuildingActions.AdjointAction (adjointCoordinates Q))

private theorem adjoint_on_place (g : G) (h : C.G₀) (t : Weights B) :
    ∃ k : C.G₀, (k : G) = g * (h : G) * (Q.lift (typeChange Q g) : G)⁻¹ ∧
      realizePermutations X ad.action g (X.realization.place h t) =
        X.realization.place k (reindexWeights (Q.wallPerm (typeChange Q g)) t) := by
  obtain ⟨k, hk, hm⟩ := ad.on_place g h t
  refine ⟨k, hk, ?_⟩
  rw [← gluedPointsEquiv_place X h t, realizePermutations_apply]
  exact congrArg (gluedPointsEquiv X) hm

private theorem adjoint_ordinary_permutation (g : C.G₀) (x : X.realization.Point) :
    realizePermutations X ad.action (g : G) x = X.realization.translate g x := by
  obtain ⟨h, t, rfl⟩ := X.realization.place_surjective x
  have ha : ad.action g (gluedPlace h t) = gluedPlace (g * h) t := ad.ordinary g h t
  have ht : X.realization.translate g (X.realization.place h t) = X.realization.place (g * h) t := by
    rw [← base_chart_place X h t, X.realization.translate_chart, base_chart_place]
  rw [← gluedPointsEquiv_place X h t, realizePermutations_apply, ha, gluedPointsEquiv_place,
    gluedPointsEquiv_place, ht]

private theorem lengthZero_position (ω : Ω) (t : Weights B) :
    position (reindexWeights (Q.wallPerm ω) t) = realAffine ρ ρ ω.val.val (position t) :=
  transport_simplex (X := X) (Y := X) ω.val.val (Q.wallPerm ω)
    (fun i => Q.vertex_action ω i _ (X.realization.vertex_marked i)) t

private theorem lengthZero_position_fixed (ω : Ω) (t : Weights B) :
    reindexWeights (Q.wallPerm ω) t = t ↔
      realAffine ρ ρ ω.val.val (position t) = position t := by
  rw [← lengthZero_position X ω t]
  refine ⟨congrArg position, fun h => ?_⟩
  have h' : X.realization.place 1 (reindexWeights (Q.wallPerm ω) t) = X.realization.place 1 t := by
    rw [← base_chart_place X 1 t, ← base_chart_place X 1 (reindexWeights (Q.wallPerm ω) t), h]
  exact ((X.realization.place_eq _ _ _ _).mp h').1

private theorem adjoint_normalizer_chart (n : C.N) (x : EuclideanApartment V) :
    realizePermutations X ad.action (n : G) (X.realization.chart 1 x) =
      X.realization.chart 1 (realAffine ρ ρ (C.affine n) x) := by
  obtain ⟨w, t, rfl⟩ := X.realization.chart_cover x
  rw [X.realization.chart_place, one_mul]
  obtain ⟨v, hv, hl, ha⟩ := ad.normalizer n w (X.realization.lift_mem w) t
  have hh : ad.action n (gluedPlace (C := C) ⟨C.lift w, X.realization.lift_mem w⟩ t) =
      gluedPlace (C := C) ⟨C.lift v, hv⟩ (reindexWeights (Q.wallPerm (typeChange Q n)) t) := ha
  rw [← gluedPointsEquiv_place X ⟨C.lift w, X.realization.lift_mem w⟩ t, realizePermutations_apply,
    hh, gluedPointsEquiv_place]
  have he : v.val * (typeChange Q n).val.val = C.affine n * w.val := by
    change v.val = C.affine n * w.val * (typeChange Q n).val.val⁻¹ at hl
    rw [hl]
    group
  rw [← realAffine_mul_apply ρ, ← he, realAffine_mul_apply ρ, ← lengthZero_position X, X.realization.chart_place, one_mul]

private theorem adjoint_isometry (N : Specs.ExceptionalBuildingActions.NormalizerComparison Q)
    (hW : ∀ w : A.extendedAffineWeylGroup, Isometry (realAffine ρ ρ w.val)) (g : G) :
    Isometry (realizePermutations X ad.action g) := by
  apply isometry_of_charts _ X.realization.chart X.realization.chart X.realization.chart_isometry X.realization.chart_isometry (realization_pair X)
  intro h
  let ω := typeChange Q (g * (h : G))
  obtain ⟨k, hk⟩ := N.factorization (g * (h : G))
  refine ⟨k, realAffine ρ ρ ω.val.val, hW ω.val, fun x => ?_⟩
  have hh : X.realization.chart h x = realizePermutations X ad.action (h : G) (X.realization.chart 1 x) := by
    rw [adjoint_ordinary_permutation, X.realization.translate_chart, mul_one]
  have hk' : g * (h : G) = (k : G) * (Q.lift ω : G) := hk
  rw [hh, ← Equiv.Perm.mul_apply, ← map_mul, hk', map_mul, Equiv.Perm.mul_apply,
    adjoint_normalizer_chart, adjoint_ordinary_permutation, Q.affine_lift, X.realization.translate_chart, mul_one]

include X in
private theorem open_chamber_weights :
    ∃ t : Weights B, cotype t = ∅ := by
  obtain ⟨g, t, -⟩ := X.realization.place_surjective (X.realization.chart 1 0)
  have hne : (∅ : Set B) ≠ univ := by
    intro h
    have ht : cotype t = univ := Set.eq_univ_of_univ_subset (h ▸ Set.empty_subset _)
    exact cotype_ne_univ t ht
  obtain ⟨t, ht, -⟩ := X.realization.barycenter ∅ hne
  exact ⟨t, ht⟩

private theorem gluedPointsEquiv_chamber :
    gluedPointsEquiv X '' Specs.ExceptionalBuildingActions.chamberPoints (C := C) (cotype := @cotype B) 1 =
      X.realization.closedFace 1 ∅ := by
  change gluedPointsEquiv X '' Set.range (gluedPlace (C := C) 1) =
    X.realization.place 1 '' {t | (∅ : Set B) ⊆ cotype t}
  rw [← Set.range_comp]
  simp only [Function.comp_def, gluedPointsEquiv_place, Set.empty_subset, Set.ofPred_true, Set.image_univ]

private theorem chamber_stabilizer_iff (g : G) :
    realizePermutations X ad.action g '' X.realization.closedFace 1 ∅ = X.realization.closedFace 1 ∅ ↔
      g ∈ C.I ⊔ lengthZeroNormalizer C := by
  let S := Specs.ExceptionalBuildingActions.chamberPoints (C := C) (cotype := @cotype B) 1
  have h :
    realizePermutations X ad.action g '' (gluedPointsEquiv X '' S) =
      gluedPointsEquiv X '' (ad.action g '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => realizePermutations_apply X ad.action g x)
  rw [← gluedPointsEquiv_chamber X, h,
    (Set.image_injective.mpr (gluedPointsEquiv X).injective).eq_iff]
  exact ad.chamber_stabilizer (open_chamber_weights X) g

private theorem adjoint_barycenter_stabilizer (t : Weights B) (g : G) :
    realizePermutations X ad.action g (X.realization.place 1 t) = X.realization.place 1 t ↔
      ∃ (a : parahoric C (cotype t)) (ω : Ω), g = (a : G) * (Q.lift ω : G) ∧
        realAffine ρ ρ ω.val.val (position t) = position t := by
  rw [← gluedPointsEquiv_place X 1 t, realizePermutations_apply, Equiv.apply_eq_iff_eq]
  exact (ad.point_stabilizer t g).trans
    (exists_congr fun a => exists_congr fun ω => and_congr_right fun _ => lengthZero_position_fixed X ω t)

private def buildAdjointAction (N : Specs.ExceptionalBuildingActions.NormalizerComparison Q)
    (faithful : Function.Injective Q.wallPerm)
    (hW : ∀ w : A.extendedAffineWeylGroup, Isometry (realAffine ρ ρ w.val)) : AdjointAction X Q where
  action := isometricPermutations (realizePermutations X ad.action) (adjoint_isometry X ad N hW)
  type_preserving := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one Q.wallPerm, faithful.eq_iff, ← MonoidHom.mem_ker]
    exact SetLike.ext_iff.mp N.kernel g
  restrict g := IsometryEquiv.ext (adjoint_ordinary_permutation X ad g)
  chart_normalizer := adjoint_normalizer_chart X ad
  place_action g h t := by
    obtain ⟨k, _, hk⟩ := adjoint_on_place X ad g h t
    exact ⟨k, _, hk, reindexWeights_apply _ _⟩
  conjugates_face ω := N.conjugates (Q.lift ω) ω (Q.affine_lift ω)
  chamber_stabilizer := chamber_stabilizer_iff X ad
  chamber_stabilizer_product := N.chamber_product
  chamber_cosets := N.cosets
  chamber_cosets_eq g h hh := by
    have he : g = ⟨QuotientGroup.mk (h : G), h, rfl⟩ := Subtype.ext hh
    rw [he]
    exact N.cosets_mk h
  face_stabilizer T t ht _ g := by
    subst T
    exact adjoint_barycenter_stabilizer X ad t g
  barycenter_types T t ht hb ω := by
    rw [← lengthZero_position_fixed X ω t]
    refine ⟨fun h => ?_, fun h => reindexWeights_support_barycenter (Q.wallPerm ω) T h t hb⟩
    have he := congrArg (@cotype B) h
    rw [reindexWeights_cotype, ht] at he
    exact he
  stabilizer_types T t ht g hg := by
    subst T
    change realizePermutations X ad.action g (X.realization.place 1 t) = X.realization.place 1 t at hg
    rw [← gluedPointsEquiv_place X 1 t, realizePermutations_apply, Equiv.apply_eq_iff_eq] at hg
    exact ad.stabilizer_types t g hg

end Adjoint

section CoefficientActions

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {G Wf V : Type u} {J : Type v}
  [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

local notation "B" => A.SimpleWall p
local notation "Ω" => alcoveStabilizer A (A.alcove p)

variable (X : Building C) {Q : C.TypeQuotient}

private theorem openFace_image_of_weights (f : X.realization.Point → X.realization.Point) (d : Equiv.Perm B)
    (g h : C.G₀) (T : Set B) (hT : d '' T = T)
    (hf : ∀ t, f (X.realization.place g t) = X.realization.place h (reindexWeights d t)) :
    f '' X.realization.openFace g T = X.realization.openFace h T := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [hf]
    exact ⟨_, (reindexWeights_cotype d t).trans ((congrArg (Set.image d) ht).trans hT), rfl⟩
  · rintro ⟨s, hs, rfl⟩
    let t := (weightPermutations B d).symm s
    have hts : reindexWeights d t = s := (weightPermutations B d).apply_symm_apply s
    have hti : d '' cotype t = T := by
      rw [← reindexWeights_cotype, hts]
      exact hs
    have ht : cotype t = T := Set.image_injective.mpr d.injective (hti.trans hT.symm)
    exact ⟨X.realization.place g t, ⟨t, ht, rfl⟩, (hf t).trans (congrArg _ hts)⟩

variable {Γ : Type u} [Group Γ]

private theorem twisted_face [Finite Γ] (twist : Γ →* (X.realization.Point ≃ᵢ X.realization.Point))
    (types : Γ →* Equiv.Perm B)
    (hplace : ∀ σ g, ∃ h, ∀ t,
      twist σ (X.realization.place g t) = X.realization.place h (reindexWeights (types σ) t)) :
    (∃ x, ∀ σ, twist σ x = x) ∧
    ∀ x, (∀ σ, twist σ x = x) →
      ∃ (g : C.G₀) (T : Set B) (t : Weights B),
        x ∈ X.realization.openFace g T ∧ cotype t = T ∧ IsBarycenter T t ∧
        X.realization.translate g (X.realization.place 1 t) = X.realization.place g t ∧
        ∀ σ, twist σ '' X.realization.openFace g T = X.realization.openFace g T ∧
          twist σ (X.realization.place g t) = X.realization.place g t := by
  letI : MulAction Γ X.realization.Point :=
    { smul := fun σ x => twist σ x
      one_smul := fun x => by change twist 1 x = x; rw [map_one]; rfl
      mul_smul := fun σ τ x => by change twist (σ * τ) x = twist σ (twist τ x); rw [map_mul]; rfl }
  letI : IsIsometricSMul Γ X.realization.Point := ⟨fun σ => (twist σ).isometry⟩
  have hc : Geometry.CAT0 X.realization.Point := X.realization.cat0
  refine ⟨hc.fixedPoints_nonempty_of_finiteGroup (G := Γ), ?_⟩
  intro x hx
  obtain ⟨g, t, rfl⟩ := X.realization.place_surjective x
  let T := cotype t
  have hT : T ≠ univ := cotype_ne_univ t
  obtain ⟨b, hb, hbar⟩ := X.realization.barycenter T hT
  refine ⟨g, T, b, ⟨t, rfl, rfl⟩, hb, hbar, ?_, ?_⟩
  · rw [← base_chart_place X 1 b, X.realization.translate_chart, mul_one, base_chart_place X]
  · intro σ
    obtain ⟨h, hh⟩ := hplace σ g
    have heq := (hh t).symm.trans (hx σ)
    obtain ⟨he, hm⟩ := (X.realization.place_eq _ _ _ _).mp heq
    have ht : types σ '' T = T := by
      rw [← reindexWeights_cotype, he]
    have hmem : (h : G)⁻¹ * (g : G) ∈ parahoric C T := by rwa [he] at hm
    have hface : X.realization.openFace h T = X.realization.openFace g T :=
      (X.realization.open_face_cosets T T hT hT h g).mpr ⟨rfl, hmem⟩
    refine ⟨(openFace_image_of_weights X (twist σ) (types σ) g h T ht hh).trans hface, ?_⟩
    rw [hh, reindexWeights_support_barycenter (types σ) T ht b hbar]
    exact (X.realization.place_eq _ _ _ _).mpr ⟨rfl, hb.symm ▸ hmem⟩

variable {ρ : Γ →* MulAut G} {e : Γ → V ≃ᵃ[ℚ] V}
variable (R : Specs.ExceptionalBuildingTransport.CoefficientTransport C Q ρ e X.realization.coordinates)
  (hρ : ∀ σ, AutomorphismComparison C (ρ σ) (e σ))

private def algebraicCoefficientTransport :
    Specs.ExceptionalBuildingActions.CoefficientTransport Q ρ where
  affine := R.affine
  walls := R.types
  types := R.quotient
  comparison σ := (R.affine_eq σ).symm ▸ hρ σ
  wall σ i := by
    rw [R.affine_eq σ, ← R.wall_eq σ]
    exact markedWall_image (R.marked σ) i
  simple_label σ i := by
    rw [← R.wall_eq σ, R.affine_eq σ, ← (R.marked σ).simple i]
    apply AffineEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (e σ).surjective x
    change ((R.marked σ).ordinary (C.coxeter.coxeter.simple i)).val (e σ y) =
      e σ ((C.coxeter.coxeter.simple i).val ((e σ).symm (e σ y)))
    rw [AffineEquiv.symm_apply_apply]
    exact (R.marked σ).label (C.coxeter.coxeter.simple i) y
  type_transport := R.quotient_natural

private abbrev coefficientWeights : Γ →* Equiv.Perm (Weights B) :=
  (weightPermutations B).comp R.types

include hρ in
private theorem coefficients_permute_cotype (σ : Γ) (t : Weights B) :
    cotype (coefficientWeights X R σ t) = (algebraicCoefficientTransport X R hρ).walls σ '' cotype t :=
  reindexWeights_cotype (R.types σ) t

include hρ in
private theorem coefficients_permute_compatibly (σ : Γ) (ω : Ω) :
    coefficientWeights X R σ * (adjointCoordinates Q).perm ω =
      (adjointCoordinates Q).perm ((algebraicCoefficientTransport X R hρ).types σ ω) *
        coefficientWeights X R σ := by
  change weightPermutations B (R.types σ) * weightPermutations B (Q.wallPerm ω) =
    weightPermutations B (Q.wallPerm (R.quotient σ ω)) * weightPermutations B (R.types σ)
  rw [← map_mul, ← map_mul, R.quotient_types]
  congr 1
  group

variable {ad : Specs.ExceptionalBuildingActions.AdjointAction (adjointCoordinates Q)}
variable (coef : Specs.ExceptionalBuildingActions.CoefficientAction ad
  (algebraicCoefficientTransport X R hρ) (coefficientWeights X R))

private theorem coefficient_on_place (σ : Γ) (g : C.G₀) (t : Weights B) :
    realizePermutations X coef.action σ (X.realization.place g t) =
      X.realization.place (transportRepresentative (R.marked σ) g) (reindexWeights (R.types σ) t) := by
  obtain ⟨h, hh, ht⟩ := coef.on_place σ g t
  have he : h = transportRepresentative (R.marked σ) g := Subtype.ext hh
  subst h
  rw [← gluedPointsEquiv_place X g t, realizePermutations_apply]
  exact congrArg (gluedPointsEquiv X) ht

private theorem coefficient_on_chart (σ : Γ) (g : C.G₀) (x : EuclideanApartment V) :
    realizePermutations X coef.action σ (X.realization.chart g x) =
      X.realization.chart (transportRepresentative (R.marked σ) g)
        (realAffine X.realization.coordinates X.realization.coordinates (e σ) x) := by
  apply chart_of_markedTransport (R.marked σ)
  intro h t
  rw [R.wall_eq]
  exact coefficient_on_place X R hρ coef σ h t

private def buildCoefficientAction : CoefficientAction X ρ e where
  action := isometricPermutations (realizePermutations X coef.action) (fun σ =>
    isometry_of_charts _ X.realization.chart X.realization.chart X.realization.chart_isometry
      X.realization.chart_isometry (realization_pair X)
      (fun g => ⟨_, _, R.real_isometry σ, coefficient_on_chart X R hρ coef σ g⟩))
  types := R.types
  wall σ i := by rw [← R.wall_eq]; exact markedWall_image (R.marked σ) i
  real_isometry := R.real_isometry
  chart σ g h hh x := by
    have he : h = transportRepresentative (R.marked σ) g := Subtype.ext hh
    subst h
    exact coefficient_on_chart X R hρ coef σ g x
  place_action σ g h hh t s hs := by
    have he : h = transportRepresentative (R.marked σ) g := Subtype.ext hh
    subst h
    exact (coefficient_on_place X R hρ coef σ g t).trans (congrArg _ (reindexWeights_eq _ t s hs))

variable (N : Specs.ExceptionalBuildingActions.NormalizerComparison Q)
  (ap : Specs.ExceptionalBuildingTransport.AdjointApartment C Q X.realization.coordinates)
  (hW : ∀ w : A.extendedAffineWeylGroup,
    Isometry (realAffine X.realization.coordinates X.realization.coordinates w.val))

local notation "adjoint" => buildAdjointAction X ad N ap.faithful hW
local notation "coefficient" => buildCoefficientAction X R hρ coef

private theorem realized_coefficient_compatible (σ : Γ) (g : G) (x : X.realization.Point) :
    (coefficient).action σ ((adjoint).action g x) =
      (adjoint).action (ρ σ g) ((coefficient).action σ x) := by
  obtain ⟨x', rfl⟩ := (gluedPointsEquiv X).surjective x
  change realizePermutations X coef.action σ
      (realizePermutations X ad.action g (gluedPointsEquiv X x')) =
    realizePermutations X ad.action (ρ σ g)
      (realizePermutations X coef.action σ (gluedPointsEquiv X x'))
  simp only [realizePermutations_apply]
  exact congrArg (gluedPointsEquiv X) (coef.compatible σ g x')

private theorem realized_coefficient_twist [Finite Γ] (a : Γ → G)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    TwistedFixedFace (adjoint) (coefficient) a := by
  obtain ⟨act, types, hf, ht, _⟩ := coef.twist a ha
  have hcomp (σ : Γ) (x : X.realization.Point) :
      realizePermutations X act σ x = (adjoint).action (a σ) ((coefficient).action σ x) := by
    obtain ⟨x', rfl⟩ := (gluedPointsEquiv X).surjective x
    change realizePermutations X act σ (gluedPointsEquiv X x') =
      realizePermutations X ad.action (a σ) (realizePermutations X coef.action σ (gluedPointsEquiv X x'))
    simp only [realizePermutations_apply]
    exact congrArg (gluedPointsEquiv X) (hf σ x')
  let twist := isometricPermutations (realizePermutations X act) (fun σ => by
    apply Isometry.of_dist_eq
    intro x y
    rw [hcomp, hcomp, ((adjoint).action (a σ)).dist_eq, ((coefficient).action σ).dist_eq])
  have hplace (σ : Γ) (g : C.G₀) : ∃ h, ∀ t : Weights B,
      twist σ (X.realization.place g t) = X.realization.place h (reindexWeights (types σ) t) := by
    let g' := transportRepresentative (R.marked σ) g
    obtain ⟨h, hh⟩ := N.factorization (a σ * (g' : G))
    have he : typeChange Q (a σ * (g' : G)) = typeChange Q (a σ) := by
      rw [map_mul]
      have hg : typeChange Q (g' : G) = 1 := by
        change (g' : G) ∈ (Specs.ExceptionalBuildingActions.typeChange C Q).ker
        rw [N.kernel]
        exact g'.property
      rw [hg, mul_one]
    refine ⟨h, fun t => ?_⟩
    change realizePermutations X act σ (X.realization.place g t) = _
    rw [hcomp σ]
    change realizePermutations X ad.action (a σ)
        (realizePermutations X coef.action σ (X.realization.place g t)) = _
    rw [coefficient_on_place]
    obtain ⟨k, hk, hact⟩ := adjoint_on_place X ad (a σ) g' (reindexWeights (R.types σ) t)
    have hkh : k = h := Subtype.ext (by
      rw [hk]
      let ω := typeChange Q (a σ * (g' : G))
      calc
        _ = (a σ * (g' : G)) * (Q.lift ω : G)⁻¹ :=
          congrArg (fun w => (a σ * (g' : G)) * (Q.lift w : G)⁻¹) he.symm
        _ = ((h : G) * (Q.lift ω : G)) * (Q.lift ω : G)⁻¹ :=
          congrArg (fun z : G => z * (Q.lift ω : G)⁻¹) hh
        _ = _ := mul_inv_cancel_right _ _)
    rw [hact, hkh, ht σ]
    rfl
  refine ⟨twist, types, hcomp, ht, ?_, twisted_face X twist types hplace⟩
  intro σ g t
  obtain ⟨h, hh⟩ := hplace σ g
  exact ⟨h, _, hh t, reindexWeights_apply _ _⟩

private theorem buildCoefficientActions {q : ℕ} (hB : C.Bruhat q)
    (N : Specs.ExceptionalBuildingActions.NormalizerComparison Q)
    (ad : Specs.ExceptionalBuildingActions.AdjointAction (adjointCoordinates Q))
    (ap : Specs.ExceptionalBuildingTransport.AdjointApartment C Q X.realization.coordinates)
    (hW : ∀ w : A.extendedAffineWeylGroup,
      Isometry (realAffine X.realization.coordinates X.realization.coordinates w.val)) :
    AdjointCoefficientActions (buildAdjointAction X ad N ap.faithful hW) := by
  intro Γ _ ρ e hρ
  obtain ⟨R⟩ := ap.coefficients Γ ρ e hρ
  let T := algebraicCoefficientTransport X R hρ
  obtain ⟨coef⟩ := ExceptionalBuildingActions.coefficientActions C hB Q (Weights B) (adjointCoordinates Q)
    ad Γ ρ T (coefficientWeights X R) (coefficients_permute_cotype X R hρ)
    (coefficients_permute_compatibly X R hρ)
  exact ⟨buildCoefficientAction X R hρ coef, realized_coefficient_compatible X R hρ coef N ap hW,
    fun [Finite Γ] a ha => realized_coefficient_twist X R hρ coef N ap hW a ha⟩

end CoefficientActions

section ScalarEquivariance

variable {K K' : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {D : BasedRootDatum.{u}} {M : Model D} {G G' Wf V : Type u} {J : Type v}
  [Group G] [Group G'] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {j' : G' →* FieldPoints M K'} {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}
  {C' : LocalComparison (j := j') (Wf := Wf) A p}

local notation "Ω" => alcoveStabilizer A (A.alcove p)

private theorem adjoint_chart_factor (X : Building C) {Q : C.TypeQuotient}
    (ad : AdjointAction X Q) {g : G} {h k : C.G₀} {ω : Ω}
    (hfac : g * (h : G) = (k : G) * (Q.lift ω : G)) (x : EuclideanApartment V) :
    ad.action g (X.realization.chart h x) =
      X.realization.chart k (realAffine X.realization.coordinates X.realization.coordinates ω.val.val x) := by
  have hh : X.realization.chart h x = ad.action (h : G) (X.realization.chart 1 x) := by
    rw [ad.restrict, X.realization.translate_chart, mul_one]
  rw [hh, ← IsometryEquiv.mul_apply, ← map_mul, hfac, map_mul, IsometryEquiv.mul_apply,
    ad.chart_normalizer, Q.affine_lift, ad.restrict, X.realization.translate_chart, mul_one]

private def unitTorusRepresentative (δ : C.T₀) : C.G₀ :=
  ⟨δ, show (δ : G) ∈ C.G₀ from (show C.I ≤ C.G₀ from le_sup_left)
    (unitTorus_le_iwahori C δ.property)⟩

private theorem unitTorus_chart (X : Building C) (δ : C.T₀) (g : C.G₀) (x : EuclideanApartment V) :
    X.realization.chart (g * unitTorusRepresentative δ) x = X.realization.chart g x := by
  have hN : (δ : G) ∈ C.N := by
    have h : (δ : G) ∈ C.I ⊓ C.N := by
      rw [X.iwahori_inter_normalizer]
      exact δ.property
    exact h.2
  let n : C.N := ⟨δ, hN⟩
  have h := X.normalizer_action n (unitTorusRepresentative δ).property x
  rw [(normalizer_mem_unitTorus_iff C n).mp δ.property, realAffine_one] at h
  change X.realization.translate (unitTorusRepresentative δ) (X.realization.chart 1 x) =
      X.realization.chart 1 x at h
  rw [X.realization.translate_chart, mul_one] at h
  calc
    X.realization.chart (g * unitTorusRepresentative δ) x =
      X.realization.translate g (X.realization.chart (unitTorusRepresentative δ) x) :=
        (X.realization.translate_chart g _ x).symm
    _ = _ := by rw [h, X.realization.translate_chart, mul_one]

/-- The actual scalar-point map intertwines the adjoint actions on their
common marked apartments, including the length-zero representatives. -/
private theorem scalar_map_equivariant (X : Building C) (Y : Building C')
    {Q : C.TypeQuotient} {Q' : C'.TypeQuotient}
    (ad : AdjointAction X Q) (ad' : AdjointAction Y Q')
    (N : Specs.ExceptionalBuildingActions.NormalizerComparison Q)
    {s : G →* G'} (f : RealizationMap X.realization Y.realization s (LinearEquiv.refl ℚ V))
    (hc : X.realization.coordinates = Y.realization.coordinates)
    (ht : TypeQuotientTransport Q Q' s (MonoidHom.id _)) (g : G) (x : X.realization.Point) :
    f.point (ad.action g x) = ad'.action (s g) (f.point x) := by
  obtain ⟨h, t, rfl⟩ := X.realization.place_surjective x
  rw [← base_chart_place X h t]
  let x := simplexPoint X.realization.coordinates X.realization.vertex t
  let h' : C'.G₀ := ⟨s h, f.maps_group h.property⟩
  let ω := typeChange Q (g * (h : G))
  obtain ⟨k, hk⟩ := N.factorization (g * (h : G))
  have hk' : g * (h : G) = (k : G) * (Q.lift ω : G) := hk
  let k' : C'.G₀ := ⟨s k, f.maps_group k.property⟩
  let δ : C'.T₀ := ⟨s (Q.lift ω) * (Q'.lift ω : G')⁻¹, ht.2 ω⟩
  have hfac : s g * (h' : G') = (↑(k' * unitTorusRepresentative δ) : G') * (Q'.lift ω : G') := by
    change s g * s (h : G) = s (k : G) * (s (Q.lift ω) * (Q'.lift ω : G')⁻¹) * (Q'.lift ω : G')
    rw [← map_mul, hk', map_mul]
    group
  have hr : realAffine X.realization.coordinates Y.realization.coordinates
      (LinearEquiv.refl ℚ V).toAffineEquiv = id := by
    rw [hc]
    exact realAffine_one _
  change f.point (ad.action g (X.realization.chart h x)) = ad'.action (s g) (f.point (X.realization.chart h x))
  rw [adjoint_chart_factor X ad hk', f.chart, f.chart, hr]
  change Y.realization.chart k' (realAffine X.realization.coordinates X.realization.coordinates ω.val.val x) =
    ad'.action (s g) (Y.realization.chart h' x)
  rw [adjoint_chart_factor Y ad' hfac, unitTorus_chart Y δ k', hc]

end ScalarEquivariance

private theorem residue_card_pos (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 0 < Nat.card (residue K) :=
  (show 0 < Nat.card 𝓀[K] from Nat.card_pos)

section BuildingLevel

variable {K K' : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']
  {D : BasedRootDatum.{u}} {M : Model D} {G G' Wf V : Type u} {J : Type v}
  [Group G] [Group G'] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {j' : G' →* FieldPoints M K'}
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p} {C' : LocalComparison (j := j') (Wf := Wf) A p}

private def adjointLevel (X : Building C) (Q : C.TypeQuotient) {q : ℕ} (hB : C.Bruhat q)
    (ap : AdjointApartment C Q X.realization.coordinates)
    (hW : ApartmentIsometries (A := A) X.realization.coordinates) :
    { ad : AdjointAction X Q // AdjointCoefficientActions ad } :=
  let N := (ExceptionalBuildingActions.normalizerActions C hB Q).some
  let ad := (ExceptionalBuildingActions.adjointActions C hB Q (Weights (A.SimpleWall p))
    (adjointCoordinates Q)).some
  ⟨buildAdjointAction X ad N ap.faithful hW.extended, buildCoefficientActions X hB N ad ap hW.extended⟩

private def scalarBuildingMap (X : Building C) (Y : Building C') {q q' : ℕ}
    (hB : C.Bruhat q) (hB' : C'.Bruhat q') (f : K →+* K') (s : G →* G')
    (h : ScalarComparison f s C C') (hc : X.realization.coordinates = Y.realization.coordinates) :
    RealizationMap X.realization Y.realization s (LinearEquiv.refl ℚ V) :=
  let m := ExceptionalBuildingTransport.scalar_markedTransport hB hB' h
  inducedRealizationMap X Y s (LinearEquiv.refl ℚ V) m (by
    rw [hc]
    change Isometry (realAffine _ _ (1 : V ≃ᵃ[ℚ] V))
    rw [realAffine_one]
    exact isometry_id)

end BuildingLevel

section Split

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}

private def splitBuildingLevel (L : SplitLevel K c p p' e)
    (d : Specs.ExceptionalRealAlcove.RealAlcoveData L.sc.coxeter)
    (d' : Specs.ExceptionalRealAlcove.RealAlcoveData L.ad.coxeter)
    (r : RealCoordinates (ℚ ⊗[ℤ] D.Y)) (r' : RealCoordinates (ℚ ⊗[ℤ] E.Y))
    (h : SplitApartmentLevel L r r') : SplitBuildingLevel L := by
  let X := buildLocal d r h.1.ordinary L.sc_bruhat (residue_card_pos K)
  let Y := buildLocal d' r' h.2.1.ordinary L.ad_bruhat (residue_card_pos K)
  let T := h.2.2.1.some
  let s := integralPointHom c.map (CommAlgCat.of Integers.{u} K)
  let f := inducedRealizationMap X Y s e T.marked T.isometry
  let a := adjointLevel Y L.typeQuotient L.ad_bruhat h.2.2.2 h.2.1
  exact ⟨X, Y, f, realizationMap_onto X Y f T.chambers_onto, a.val, a.property⟩

end Split

/-- The split exceptional affine buildings, with the marked central comparison
and scalar extensions to every finite unramified level. -/
theorem splitAffineBuildings : SplitAffineBuildings.{u} := by
  intro F _ _ _ _ D E M M' c n b b' hn hb hb' hsc had
  obtain ⟨p, p', e, X, he, hp, hlevels⟩ :=
    ExceptionalAffineBruhat.splitAffineBruhatComparison F c n b b' hn hb hb' hsc had
  obtain ⟨r, r', hx, hcoords⟩ :=
    ExceptionalBuildingTransport.splitApartmentComparisons F had hp X
  obtain ⟨⟨u⟩, ⟨v⟩⟩ := ExceptionalRealAlcove.splitRealAlcoves F c n b b' hn hb hb' hsc had e X hp
  let BX := splitBuildingLevel X u v r r' hx
  refine ⟨p, p', e, X, BX, he, hp, ?_⟩
  intro K _ _ _ _ _ _ _ hK
  obtain ⟨Y, hs, hs', ht, hc, ho⟩ := hlevels K hK
  obtain ⟨⟨u'⟩, ⟨v'⟩⟩ := ExceptionalRealAlcove.splitRealAlcoves K c n b b' hn hb hb' hsc had e Y hp
  let BY := splitBuildingLevel Y u' v' r r' (hcoords K Y)
  let s := scalarPoints M (algebraMap F K)
  let s' := scalarPoints M' (algebraMap F K)
  let f := scalarBuildingMap BX.sc BY.sc X.sc_bruhat Y.sc_bruhat (algebraMap F K) s hs rfl
  let f' := scalarBuildingMap BX.ad BY.ad X.ad_bruhat Y.ad_bruhat (algebraMap F K) s' hs' rfl
  refine ⟨Y, BY, hs, hs', ht, ⟨f, f', ?_, ?_⟩, hc, ho⟩
  · exact scalar_map_equivariant BX.ad BY.ad BX.adjoint BY.adjoint
      (ExceptionalBuildingActions.normalizerActions X.ad X.ad_bruhat X.typeQuotient).some f' rfl ht
  · intro x
    obtain ⟨g, t, rfl⟩ := BX.sc.realization.place_surjective x
    rw [← base_chart_place BX.sc g t, BX.central.chart, f'.chart, f.chart, BY.central.chart]
    have hr : realAffine r r (1 : (ℚ ⊗[ℤ] D.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] D.Y)) = id := realAffine_one r
    have hr' : realAffine r' r' (1 : (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)) = id := realAffine_one r'
    let z := simplexPoint BX.sc.realization.coordinates BX.sc.realization.vertex t
    let cF := integralPointHom c.map (CommAlgCat.of Integers.{u} F)
    let cK := integralPointHom c.map (CommAlgCat.of Integers.{u} K)
    have h : s' (cF g) = cK (s g) :=
      ExceptionalBuildingTransport.pointComparisonSquares.1 c.map (integralRingMap (algebraMap F K)) g
    change BY.ad.realization.chart ⟨s' (cF g), _⟩
        (realAffine r' r' 1 (realAffine r r' e.toAffineEquiv z)) =
      BY.ad.realization.chart ⟨cK (s g), _⟩
        (realAffine r r' e.toAffineEquiv (realAffine r r 1 z))
    rw [hr, hr']
    exact congrArg (fun b => BY.ad.realization.chart b (realAffine r r' e.toAffineEquiv z)) (Subtype.ext h)

section Folded

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {R : RamifiedReference F L M} {R' : RamifiedReference F L M'}
  {σ : Gal(L/F)} {σK : Gal(K/k)} {f : L →ₐ[F] K}
  {A : FoldedApartment (R.diagram σ)} {A' : FoldedApartment (R'.diagram σ)}
  {e : invariantApartment D (R.diagram σ) ≃ₗ[ℚ] invariantApartment E (R'.diagram σ)}

set_option maxHeartbeats 1200000 in
private def foldedBuildingLevel (X : FoldedLevel R σ σK f A) (Y : FoldedLevel R' σ σK f A')
    (φ : R.descent.group.val ⟶ R'.descent.group.val)
    (d : Specs.ExceptionalRealAlcove.RealAlcoveData X.comparison.coxeter)
    (d' : Specs.ExceptionalRealAlcove.RealAlcoveData Y.comparison.coxeter)
    (r : RealCoordinates (invariantApartment D (R.diagram σ)))
    (r' : RealCoordinates (invariantApartment E (R'.diagram σ)))
    (h : ApartmentIsometries (A := A.roots) r)
    (h' : ApartmentIsometries (A := A'.roots) r')
    (T : CentralApartment X.comparison Y.comparison
      (pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k)))) e r r')
    (ha : AdjointApartment Y.comparison Y.typeQuotient r') : FoldedBuildingLevel X Y φ e := by
  let Xb : Building X.comparison :=
    buildLocal (C := X.comparison) d r h.ordinary X.bruhat (residue_card_pos k)
  let Yb : Building Y.comparison :=
    buildLocal (C := Y.comparison) d' r' h'.ordinary Y.bruhat (residue_card_pos k)
  let s := pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k)))
  let f := inducedRealizationMap Xb Yb s e T.marked T.isometry
  let a := adjointLevel Yb Y.typeQuotient Y.bruhat ha h'
  exact ⟨Xb, Yb, f, realizationMap_onto Xb Yb f T.chambers_onto, a.val, a.property⟩

end Folded

set_option maxHeartbeats 2200000 in
/-- The marked affine buildings of the ramified quasi-split outer E₆ reference,
using the normalized folded apartment at the base and each unramified level. -/
theorem ramifiedAffineBuildings : RamifiedAffineBuildings.{u} := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ σ hdeg hσ hram D E M M' c b b' hb hb' hsc had R R'
  dsimp only
  intro hR hR' hcom
  obtain ⟨A, A', e, φ, X, X', he, hp, hi, hcen, hlevels⟩ :=
    ExceptionalAffineBruhat.ramifiedAffineBruhatComparison F L σ hdeg hσ hram c b b' hb hb' hsc had R R' hR hR' hcom
  obtain ⟨r, r', hcoords⟩ := ExceptionalBuildingTransport.foldedApartmentComparisons A A' e hp
  let cF : GroupPoints R.descent.group.val (CommAlgCat.of F F) →*
      GroupPoints R'.descent.group.val (CommAlgCat.of F F) :=
    pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F F)))
  obtain ⟨hA, hA', ⟨hc⟩, ha⟩ :=
    hcoords L X.comparison X'.comparison cF X'.typeQuotient _ _ X.bruhat X'.bruhat hcen X.range X'.range
  let u := (ExceptionalRealAlcove.ramifiedRealAlcoves R σ σ (AlgHom.id F L) A X).some
  let v := (ExceptionalRealAlcove.ramifiedRealAlcoves R' σ σ (AlgHom.id F L) A' X').some
  let BX := foldedBuildingLevel X X' φ u v r r' hA hA' hc ha
  refine ⟨A, A', e, φ, X, X', BX, he, hp, hi, hcen, ?_⟩
  intro k _ _ _ _ _ _ _ hk
  obtain ⟨T, Y, Y', hcen', hs, hs', ht, hcf, hcf'⟩ := hlevels k hk
  let ck : GroupPoints R.descent.group.val (CommAlgCat.of F k) →*
      GroupPoints R'.descent.group.val (CommAlgCat.of F k) :=
    pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k)))
  obtain ⟨hB, hB', ⟨hc'⟩, ha'⟩ :=
    hcoords T.field Y.comparison Y'.comparison ck Y'.typeQuotient _ _ Y.bruhat Y'.bruhat hcen' Y.range Y'.range
  let u' := (ExceptionalRealAlcove.ramifiedRealAlcoves R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A Y).some
  let v' := (ExceptionalRealAlcove.ramifiedRealAlcoves R' σ T.diagram (IsScalarTower.toAlgHom F L T.field) A' Y').some
  let BY := foldedBuildingLevel Y Y' φ u' v' r r' hB hB' hc' ha'
  let s := coefficientPoints R.descent.group.val (Algebra.ofId F k)
  let s' := coefficientPoints R'.descent.group.val (Algebra.ofId F k)
  let f := scalarBuildingMap BX.sc BY.sc X.bruhat Y.bruhat (algebraMap L T.field) s hs rfl
  let f' := scalarBuildingMap BX.ad BY.ad X'.bruhat Y'.bruhat (algebraMap L T.field) s' hs' rfl
  refine ⟨T, Y, Y', BY, hcen', hs, hs', ht, ⟨f, f', ?_, ?_⟩, hcf, hcf'⟩
  · exact scalar_map_equivariant BX.ad BY.ad BX.adjoint BY.adjoint
      (ExceptionalBuildingActions.normalizerActions X'.comparison X'.bruhat X'.typeQuotient).some f' rfl ht
  · intro x
    obtain ⟨g, t, rfl⟩ := BX.sc.realization.place_surjective x
    rw [← base_chart_place BX.sc g t, BX.central.chart, f'.chart, f.chart, BY.central.chart]
    have hr := realAffine_one r
    have hr' := realAffine_one r'
    let z := simplexPoint BX.sc.realization.coordinates BX.sc.realization.vertex t
    let a : GroupPoints R.descent.group.val (CommAlgCat.of F F) := g.val
    have h : s' (cF a) = ck (s a) :=
      ExceptionalBuildingTransport.pointComparisonSquares.2 φ (Algebra.ofId F k) a
    change BY.ad.realization.chart ⟨s' (cF a), _⟩
        (realAffine r' r' 1 (realAffine r r' e.toAffineEquiv z)) =
      BY.ad.realization.chart ⟨ck (s a), _⟩
        (realAffine r r' e.toAffineEquiv (realAffine r r 1 z))
    rw [hr, hr']
    exact congrArg (fun b => BY.ad.realization.chart b (realAffine r r' e.toAffineEquiv z)) (Subtype.ext h)

end
end Construction

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
