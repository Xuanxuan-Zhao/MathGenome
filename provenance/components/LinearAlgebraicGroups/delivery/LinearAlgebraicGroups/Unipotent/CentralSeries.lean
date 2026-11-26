import Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import LinearAlgebraicGroups.Unipotent.ExactOperations
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Unipotent

open Specs (AffineAlgebraicGroup GroupScheme IsSchemeKernel)
open Specs.Unipotent

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

abbrev IsSplitUnipotent : IsSplitUnipotentType.{u} := @Specs.Unipotent.IsSplitUnipotent

section Matrices

variable {R : Type u} [CommRing R] {n : ℕ}

private abbrev Mat (n : ℕ) (R : Type u) := Matrix (Index.{u} n) (Index.{u} n) R

private def difference (g : UnitriangularMatrix n R) : Mat n R :=
  g.val.val - 1

private theorem difference_lower (g : UnitriangularMatrix n R) {i j : Index.{u} n}
    (h : j ≤ i) : difference g i j = 0 := by
  rcases lt_or_eq_of_le h with h | rfl
  · simp [difference, g.property.1 h, Matrix.one_apply_ne h.ne']
  · simp [difference, g.property.2]

private theorem difference_upper (g : UnitriangularMatrix n R) (p : StrictUpper.{u} n) :
    difference g p.1.1 p.1.2 = g.val.val p.1.1 p.1.2 := by
  simp [difference, Matrix.one_apply_ne p.2.ne]

private theorem difference_mul (x y : UnitriangularMatrix n R) :
    difference (x * y) =
      difference x + difference y + difference x * difference y := by
  change x.val.val * y.val.val - 1 =
    x.val.val - 1 + (y.val.val - 1) + (x.val.val - 1) * (y.val.val - 1)
  noncomm_ring

private theorem difference_comm (x y : UnitriangularMatrix n R) :
    difference (x * y * x⁻¹ * y⁻¹) =
      (difference x * difference y - difference y * difference x) * (y * x)⁻¹.val.val := by
  have h : (y * x).val.val * (y * x)⁻¹.val.val = 1 := (y * x).val.val_inv
  have he : (x * y * x⁻¹ * y⁻¹).val.val =
      (x * y).val.val * (y * x)⁻¹.val.val := by
    exact congrArg (fun z : UnitriangularMatrix n R => z.val.val)
      (show x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ by rw [mul_inv_rev, mul_assoc (x * y)])
  rw [difference, he, ← h, ← sub_mul]
  change (x.val.val * y.val.val - y.val.val * x.val.val) * _ = _
  congr 1
  unfold difference
  noncomm_ring

private theorem matrix_product_at {a b : Mat n R} {i j : Index.{u} n}
    (ha : ∀ l, l ≤ i → a i l = 0) (hb : ∀ l, j ≤ l → b l j = 0)
    (h : ∀ l, i < l → l < j → a i l * b l j = 0) :
    (a * b) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hi : i < l
  · by_cases hj : l < j
    · exact h l hi hj
    · rw [hb l (le_of_not_gt hj), mul_zero]
  · rw [ha l (le_of_not_gt hi), zero_mul]

private theorem height_product {d e : ℕ} (x y : UnitriangularMatrix n R)
    (hx : InHeight d x) (hy : InHeight e y) (p : StrictUpper.{u} n)
    (hp : entryHeight p < d + e) :
    (difference x * difference y) p.1.1 p.1.2 = 0 := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  apply matrix_product_at (fun _ => difference_lower x) (fun _ => difference_lower y)
  intro l hil hlj
  let a : StrictUpper.{u} n := ⟨(i, l), hil⟩
  let b : StrictUpper.{u} n := ⟨(l, j), hlj⟩
  have hsum : entryHeight (⟨(i, j), hij⟩ : StrictUpper.{u} n) =
      entryHeight a + entryHeight b := by
    have hi : i.down.val ≤ l.down.val := hil.le
    have hj : l.down.val ≤ j.down.val := hlj.le
    dsimp [entryHeight, a, b]
    omega
  rw [hsum] at hp
  by_cases ha : entryHeight a < d
  · rw [difference_upper x a, hx a ha, zero_mul]
  · have hb : entryHeight b < e := by omega
    rw [difference_upper y b, hy b hb, mul_zero]

/-- Vanishing of coordinates at heights below the sum for the matrix commutator. -/
theorem heightCommutators : HeightCommutators.{u} := by
  intro k _ n i j R x y hx hy p hp
  rw [← difference_upper, difference_comm, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hlow : l ≤ p.1.1
  · have hzero (a b : UnitriangularMatrix n R) : (difference a * difference b) p.1.1 l = 0 :=
      matrix_product_at (fun _ => difference_lower a) (fun _ => difference_lower b)
        (fun _ ha hb => False.elim (not_lt_of_ge hlow (ha.trans hb)))
    exact by simp [hzero]
  · by_cases hhigh : p.1.2 < l
    · rw [show (y * x)⁻¹.val.val l p.1.2 = 0 from ((y * x)⁻¹).property.1 hhigh, mul_zero]
    · let q : StrictUpper.{u} n := ⟨(p.1.1, l), lt_of_not_ge hlow⟩
      have hle : l.down.val ≤ p.1.2.down.val := le_of_not_gt hhigh
      have hq : entryHeight q < i + j := by
        dsimp [entryHeight, q] at hp ⊢
        omega
      have ha := height_product x y hx hy q hq
      have hb := height_product y x hy hx q (by omega)
      change ((difference x * difference y) q.1.1 q.1.2 -
        (difference y * difference x) q.1.1 q.1.2) * _ = 0
      rw [ha, hb, sub_self, zero_mul]

private lemma height_pos (p : StrictUpper.{u} n) : 0 < entryHeight p := by
  have hp : p.1.1.down.val < p.1.2.down.val := p.2
  exact Nat.sub_pos_of_lt hp

private lemma rank_lt_of_height_lt {p q : StrictUpper.{u} n} (h : entryHeight p < entryHeight q) :
    coordinateRank p < coordinateRank q := by
  have hp := p.1.1.down.isLt
  have hmul := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hmul
  unfold coordinateRank
  omega

private lemma rank_injective : Function.Injective (@coordinateRank n) := by
  intro p q hpq
  have hh : entryHeight p = entryHeight q := by
    rcases lt_trichotomy (entryHeight p) (entryHeight q) with h | h | h
    · exact False.elim ((rank_lt_of_height_lt h).ne hpq)
    · exact h
    · exact False.elim ((rank_lt_of_height_lt h).ne hpq.symm)
  have hi : p.1.1.down.val = q.1.1.down.val := by
    unfold coordinateRank at hpq
    rw [hh] at hpq
    omega
  have hp : p.1.1.down.val < p.1.2.down.val := p.2
  have hq : q.1.1.down.val < q.1.2.down.val := q.2
  have hj : p.1.2.down.val = q.1.2.down.val := by
    dsimp [entryHeight] at hh
    omega
  exact Subtype.ext (Prod.ext (ULift.ext (Fin.ext hi)) (ULift.ext (Fin.ext hj)))

private lemma before_height {s : ℕ} (x : UnitriangularMatrix n R) (h : InCoordinateFlag s x)
    (p : StrictUpper.{u} n) (hp : coordinateRank p = s) :
    InHeight (entryHeight p) x :=
  fun q hq => h q (hp ▸ rank_lt_of_height_lt hq)

private lemma entry_mul {d : ℕ} (x y : UnitriangularMatrix n R)
    (hx : InHeight d x) (hy : InHeight d y) (p : StrictUpper.{u} n)
    (hp : entryHeight p = d) :
    (x * y).val.val p.1.1 p.1.2 = x.val.val p.1.1 p.1.2 + y.val.val p.1.1 p.1.2 := by
  have hd := height_pos p
  have hz := height_product x y hx hy p (by omega)
  have he := congrArg (fun M : Mat n R => M p.1.1 p.1.2) (difference_mul x y)
  change difference (x * y) p.1.1 p.1.2 =
    difference x p.1.1 p.1.2 + difference y p.1.1 p.1.2 +
      (difference x * difference y) p.1.1 p.1.2 at he
  simpa only [difference_upper, hz, add_zero] using he

private lemma before_comm {k : Type u} [Field k] {n s : ℕ} {R : TestAlgebra k}
    (x y : UnitriangularMatrix n R) (hy : InCoordinateFlag s y) :
    InCoordinateFlag (s + 1) (x * y * x⁻¹ * y⁻¹) := by
  intro p hp
  have hp' : coordinateRank p ≤ s := by omega
  have h₁ : InHeight 1 x := fun q hq => False.elim (by have := height_pos q; omega)
  have h₂ : InHeight (entryHeight p) y :=
    fun q hq => hy q ((rank_lt_of_height_lt hq).trans_le hp')
  exact heightCommutators k n 1 (entryHeight p) R x y h₁ h₂ p (by omega)

private def nextEntry (s : ℕ) (x : UnitriangularMatrix n R) : R := by
  classical
  exact if h : ∃ p : StrictUpper.{u} n, coordinateRank p = s then
    x.val.val h.choose.1.1 h.choose.1.2 else 0

private lemma before_succ (s : ℕ) (x : UnitriangularMatrix n R) :
    InCoordinateFlag (s + 1) x ↔ InCoordinateFlag s x ∧ nextEntry s x = 0 := by
  classical
  unfold nextEntry
  split
  · rename_i h
    have hs := h.choose_spec
    constructor
    · intro hx
      exact ⟨fun p hp => hx p (by omega), hx h.choose (by omega)⟩
    · rintro ⟨hx, hzero⟩ p hp
      by_cases hlt : coordinateRank p < s
      · exact hx p hlt
      · have he : p = h.choose := rank_injective (by omega)
        simpa only [he] using hzero
  · rename_i h
    constructor
    · intro hx
      exact ⟨fun p hp => hx p (by omega), rfl⟩
    · rintro ⟨hx, _⟩ p hp
      exact hx p (lt_of_le_of_ne (by omega) (fun he => h ⟨p, he⟩))

private lemma nextEntry_mul (s : ℕ) (x y : UnitriangularMatrix n R)
    (hx : InCoordinateFlag s x) (hy : InCoordinateFlag s y) :
    nextEntry s (x * y) = nextEntry s x + nextEntry s y := by
  classical
  unfold nextEntry
  split
  · rename_i h
    exact entry_mul x y (before_height x hx h.choose h.choose_spec)
      (before_height y hy h.choose h.choose_spec) h.choose rfl
  · exact (zero_add (0 : R)).symm

private lemma nextEntry_one (s : ℕ) : nextEntry s (1 : UnitriangularMatrix n R) = 0 := by
  classical
  unfold nextEntry
  split
  · rename_i h
    exact Matrix.one_apply_ne h.choose.2.ne
  · rfl

private lemma before_all_eq_one (x : UnitriangularMatrix n R)
    (h : InCoordinateFlag (n * (n + 1)) x) : x = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · let p : StrictUpper.{u} n := ⟨(i, j), hij⟩
    have hj := j.down.isLt
    have hi := i.down.isLt
    have hh : entryHeight p < n := by unfold entryHeight p; omega
    have hm := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hh)
    rw [Nat.succ_mul] at hm
    have hp : coordinateRank p < n * (n + 1) := by
      unfold coordinateRank
      change entryHeight p * (n + 1) + i.down.val < _
      omega
    exact (h p hp).trans (Matrix.one_apply_ne hij.ne).symm
  · exact (x.property.2 i).trans (Matrix.one_apply_eq i).symm
  · exact (x.property.1 hji).trans (Matrix.one_apply_ne hji.ne').symm

private lemma before_height_iff (d : ℕ) (x : UnitriangularMatrix n R) :
    InCoordinateFlag (d * (n + 1)) x ↔ InHeight d x := by
  have hr (p : StrictUpper.{u} n) :
      coordinateRank p < d * (n + 1) ↔ entryHeight p < d := by
    constructor
    · intro h
      by_contra! hd
      have hm := Nat.mul_le_mul_right (n + 1) hd
      unfold coordinateRank at h
      omega
    · intro hd
      have hm := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hd)
      rw [Nat.succ_mul] at hm
      unfold coordinateRank
      have hp := p.1.1.down.isLt
      omega
  exact ⟨fun h p hp => h p ((hr p).mpr hp), fun h p hp => h p ((hr p).mp hp)⟩

end Matrices

section Schemes

variable {k : Type u} [Field k]

open Specs.StandardGroups (additivePoints additivePowerPoints)
open private schemeKernel_sections schemeKernel_exists quotientRepresentsImage
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private unipotent_iff_exists_embedding from LinearAlgebraicGroups.Unipotent.ExactOperations

private abbrev GPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).obj G).obj R

private abbrev onPoints {G H : GroupScheme k} (f : G ⟶ H) (R : TestAlgebra k) :
    GPoints G R →* GPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

private lemma onPoints_comp {G H I : GroupScheme k} (f : G ⟶ H) (g : H ⟶ I)
    (R : TestAlgebra k) (x : GPoints G R) :
    onPoints (f ≫ g) R x = onPoints g R (onPoints f R x) := rfl

private lemma onPoints_natural {A B : GroupScheme k} (f : A ⟶ B)
    {R T : TestAlgebra k} (a : R ⟶ T) (x : GPoints A R) :
    onPoints f T (((groupPointsFunctor k).obj A).map a x) =
      ((groupPointsFunctor k).obj B).map a (onPoints f R x) :=
  congrArg (fun b => b x) (((groupPointsFunctor k).map f).naturality a)

private lemma onPoints_injective {G H : GroupScheme k} (f : G ⟶ H)
    (hf : IsClosedImmersion f.hom.hom.left) (R : TestAlgebra k) :
    Function.Injective (onPoints f R) := by
  let := hf
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  intro x y h
  exact (cancel_mono f.hom.hom).mp h

private lemma group_hom_ext {G H : GroupScheme k} (hG : IsAffine G.X.left)
    {f g : G ⟶ H} (h : ∀ R x, onPoints f R x = onPoints g R x) : f = g := by
  apply (groupHomComparison k G H hG).1
  ext R x
  exact h R x

private lemma scheme_hom_spec {G H : AffineAlgebraicGroup k}
    (α : (groupPointsFunctor k).obj G.val ⟶ (groupPointsFunctor k).obj H.val)
    (R : TestAlgebra k) (x : GPoints G.val R) :
    onPoints ((AffineAlgebraicGroup.groupHomEquiv G H).symm α) R x = α.app R x := by
  have h : (groupPointsFunctor k).map ((AffineAlgebraicGroup.groupHomEquiv G H).symm α) = α :=
    (AffineAlgebraicGroup.groupHomEquiv G H).apply_symm_apply α
  exact congrArg (fun f => f.app R x) h

private lemma closed_of_comp {G H I : GroupScheme k} (f : G ⟶ H) (g : H ⟶ I)
    (hf : IsClosedImmersion (f ≫ g).hom.hom.left)
    (hg : IsClosedImmersion g.hom.hom.left) : IsClosedImmersion f.hom.hom.left := by
  let := hg
  let : IsClosedImmersion (f.hom.hom.left ≫ g.hom.hom.left) := hf
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left g.hom.hom.left

private lemma kernel_of_closed_factor {G Q A : GroupScheme k} (f : G ⟶ A)
    (q : G ⟶ Q) (j : Q ⟶ A) (he : q ≫ j = f)
    (hj : IsClosedImmersion j.hom.hom.left) (N : Specs.ClosedSubgroup G)
    (hN : IsSchemeKernel f N) : IsSchemeKernel q N := by
  let := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hq : q.hom.hom ≫ j.hom.hom = f.hom.hom :=
    congrArg (fun a : G ⟶ A => a.hom.hom) he
  have hj₁ : η[Q.X] ≫ j.hom.hom = η[A.X] := IsMonHom.one_hom _
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors _ _ j.hom.hom _ _ hq hj₁ _ hN.isLimit)

private lemma kernel_points {G H : GroupScheme k} (f : G ⟶ H) (N : Specs.ClosedSubgroup G)
    (h : IsSchemeKernel f N) (R : TestAlgebra k) (x : GPoints G R) :
    onPoints f R x = 1 ↔ ∃ y : GPoints N.group R, onPoints N.inclusion R y = x :=
  (schemeKernel_sections h (T := (testSpec k).obj (op R)) x).symm

private def pointMatrix {n : ℕ} {G U : AffineAlgebraicGroup k}
    (f : G.val ⟶ U.val) (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n)
    (R : TestAlgebra k) : GPoints G.val R →* UnitriangularMatrix n R :=
  (e.hom.app R).hom.comp (onPoints f R)

private lemma pointMatrix_natural {n : ℕ} {G U : AffineAlgebraicGroup k}
    (f : G.val ⟶ U.val) (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n)
    {R T : TestAlgebra k} (a : R ⟶ T) (x : GPoints G.val R) :
    pointMatrix f e T (((groupPointsFunctor k).obj G.val).map a x) =
      (unitriangularPoints k n).map a (pointMatrix f e R x) := by
  change e.hom.app T (onPoints f T (((groupPointsFunctor k).obj G.val).map a x)) = _
  rw [onPoints_natural f]
  exact congrArg (fun b => b (onPoints f R x)) (e.hom.naturality a)

private lemma pointMatrix_injective {n : ℕ} {G U : AffineAlgebraicGroup k}
    (f : G.val ⟶ U.val) (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n)
    (hf : IsClosedImmersion f.hom.hom.left) (R : TestAlgebra k) :
    Function.Injective (pointMatrix f e R) := by
  have he : Function.Injective (e.hom.app R).hom :=
    ((CategoryTheory.forget GrpCat).mapIso (e.app R)).toEquiv.injective
  exact he.comp (onPoints_injective f hf R)

private structure Stage {n : ℕ} {G U : AffineAlgebraicGroup k}
    (f : G.val ⟶ U.val) (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n)
    (s : ℕ) where
  group : AffineAlgebraicGroup k
  inclusion : group.val ⟶ G.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  range_eq : ∀ (R : TestAlgebra k) (x : GPoints G.val R),
    InCoordinateFlag s (pointMatrix f e R x) ↔ ∃ y : GPoints group.val R, onPoints inclusion R y = x

variable {n : ℕ} {G U : AffineAlgebraicGroup k} {f : G.val ⟶ U.val}
    {e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n}

private lemma Stage.before {s : ℕ} (S : Stage f e s) (R : TestAlgebra k)
    (x : GPoints S.group.val R) :
    InCoordinateFlag s (pointMatrix f e R (onPoints S.inclusion R x)) :=
  (S.range_eq R _).mpr ⟨x, rfl⟩

private def firstStage : Stage f e 0 where
  group := G
  inclusion := 𝟙 G.val
  closed := by change IsClosedImmersion (𝟙 G.val.X.left); infer_instance
  range_eq R x := ⟨fun _ => ⟨x, rfl⟩, fun _ _ hp => False.elim (Nat.not_lt_zero _ hp)⟩

private def stageCoordinate {s : ℕ} (S : Stage f e s) :
    (groupPointsFunctor k).obj S.group.val ⟶ additivePoints k where
  app R :=
    let m := (pointMatrix f e R).comp (onPoints S.inclusion R)
    GrpCat.ofHom
      { toFun := fun x => Multiplicative.ofAdd (nextEntry s (m x))
        map_one' := congrArg Multiplicative.ofAdd
          ((congrArg (nextEntry s) m.map_one).trans (nextEntry_one s))
        map_mul' x y := congrArg Multiplicative.ofAdd
          ((congrArg (nextEntry s) (m.map_mul x y)).trans
            (nextEntry_mul _ _ _ (S.before R x) (S.before R y))) }
  naturality R T a := by
    apply GrpCat.ext
    intro x
    have h := pointMatrix_natural (S.inclusion ≫ f) e a x
    change pointMatrix f e T (onPoints S.inclusion T
      (((groupPointsFunctor k).obj S.group.val).map a x)) = _ at h
    change Multiplicative.ofAdd (nextEntry s (pointMatrix f e T (onPoints S.inclusion T
        (((groupPointsFunctor k).obj S.group.val).map a x)))) =
        Multiplicative.ofAdd (a.hom (nextEntry s (pointMatrix f e R (onPoints S.inclusion R x))))
    rw [h]
    classical
    unfold nextEntry
    split
    · rfl
    · exact congrArg Multiplicative.ofAdd (map_zero a.hom).symm

private structure StageLink {s : ℕ} (A : Stage f e s) (B : Stage f e (s + 1)) where
  inclusion : B.group.val ⟶ A.group.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  commutes : inclusion ≫ A.inclusion = B.inclusion
  factor : AffineAlgebraicGroup k
  quotient : A.group.val ⟶ factor.val
  additiveInclusion : factor.val ⟶ (StandardGroups.additiveGroup k).val
  additiveClosed : IsClosedImmersion additiveInclusion.hom.hom.left
  exactness : IsFppfGroupQuotient ⟨_, inclusion, closed⟩ quotient

private structure StageStep {s : ℕ} (S : Stage f e s) where
  next : Stage f e (s + 1)
  link : StageLink S next

private def nextStage {s : ℕ} (S : Stage f e s) : StageStep S := by
  let A := StandardGroups.additiveGroup k
  let c := StandardGroups.additiveGroupPointsIso k
  let α := stageCoordinate S ≫ c.inv
  let a : S.group.val ⟶ A.val := (AffineAlgebraicGroup.groupHomEquiv S.group A).symm α
  have hentry (R : TestAlgebra k) (x : GPoints S.group.val R) :
      onPoints a R x = 1 ↔ nextEntry s (pointMatrix f e R (onPoints S.inclusion R x)) = 0 := by
    rw [scheme_hom_spec α]
    change c.inv.app R (Multiplicative.ofAdd _) = 1 ↔ _
    change (c.inv.app R).hom (Multiplicative.ofAdd _) = 1 ↔ _
    rw [← (c.inv.app R).hom.map_one]
    have hi : Function.Injective (c.inv.app R).hom :=
      ((CategoryTheory.forget GrpCat).mapIso (c.app R).symm).toEquiv.injective
    exact ⟨fun h => congrArg Multiplicative.toAdd (hi h),
      fun h => congrArg (fun z : R => c.inv.app R (Multiplicative.ofAdd z)) h⟩
  choose Q q j N hfac _ hN hs using schemeImageQuotient S.group A a
  obtain ⟨hqj, hflat, hsurj, hfinite, _, hj⟩ := hfac
  let T := closedSubgroupAlgebraicGroup N
  let inc : T.val ⟶ G.val := N.inclusion ≫ S.inclusion
  have hc : IsClosedImmersion inc.hom.hom.left := by
    let := N.isClosedImmersion
    let := S.closed
    change IsClosedImmersion (N.inclusion.hom.hom.left ≫ S.inclusion.hom.hom.left)
    infer_instance
  have hr (R : TestAlgebra k) (x : GPoints G.val R) :
      InCoordinateFlag (s + 1) (pointMatrix f e R x) ↔
        ∃ y : GPoints T.val R, onPoints inc R y = x := by
    rw [before_succ]
    constructor
    · rintro ⟨hbefore, hz⟩
      obtain ⟨y, hy⟩ := (S.range_eq R x).mp hbefore
      have h₀ := (hentry R y).mpr (by rwa [hy])
      obtain ⟨z, hz⟩ := (kernel_points a N hN R y).mp h₀
      exact ⟨z, (onPoints_comp N.inclusion S.inclusion R z).trans
        ((congrArg (onPoints S.inclusion R) hz).trans hy)⟩
    · rintro ⟨y, rfl⟩
      rw [show onPoints inc R y = _ from onPoints_comp N.inclusion S.inclusion R y]
      exact ⟨S.before R _, (hentry R _).mp ((kernel_points a N hN R _).mpr ⟨y, rfl⟩)⟩
  exact ⟨⟨T, inc, hc, hr⟩, ⟨N.inclusion, N.isClosedImmersion, rfl, Q, q, j, hj,
    ⟨kernel_of_closed_factor a q j hqj hj N hN, hflat, hsurj, hfinite, hs⟩⟩⟩

private def stage : (s : ℕ) → Stage f e s
  | 0 => firstStage
  | s + 1 => (nextStage (stage s)).next

private structure StageFamily (f : G.val ⟶ U.val)
    (e : (groupPointsFunctor k).obj U.val ≅ unitriangularPoints k n) where
  term (s : ℕ) : Stage f e s
  top : (term 0).group.val ≅ G.val
  top_hom : top.hom = (term 0).inclusion
  link (s : ℕ) : StageLink (term s) (term (s + 1))

private theorem exists_stages : Nonempty (StageFamily f e) := by
  refine ⟨⟨stage, Iso.refl _, rfl, fun s => ?_⟩⟩
  exact (nextStage (stage s)).link

private def terminalIso (H : AffineAlgebraicGroup k)
    (h : ∀ (R : TestAlgebra k) (x : GPoints H.val R), x = 1) :
    H.val ≅ Grp.trivial (SchemeOver k) where
  hom := default
  inv := default
  hom_inv_id := group_hom_ext H.property.1 (fun R _ => (h R _).trans (h R _).symm)
  inv_hom_id := Subsingleton.elim _ _

/-- The refined series cuts out the upper entries in order of increasing height. -/
theorem embeddedCentralSeries : EmbeddedCentralSeries.{u} := by
  intro k _ n G U e f hf
  obtain ⟨F⟩ := exists_stages (f := f) (e := e)
  let length := n * (n + 1)
  have bottom (R : TestAlgebra k) (y : GPoints (F.term length).group.val R) : y = 1 := by
    apply onPoints_injective (F.term length).inclusion (F.term length).closed R
    apply pointMatrix_injective f e hf R
    rw [(onPoints (F.term length).inclusion R).map_one, (pointMatrix f e R).map_one]
    exact before_all_eq_one _ ((F.term length).before R y)
  let S : ClosedSeries G length :=
    { term := fun s => (F.term s).group
      top := F.top
      bottom := terminalIso (F.term length).group bottom
      step := fun s => (F.link s).inclusion
      closed := fun s => (F.link s).closed }
  have hinc (s : ℕ) : S.inclusion s = (F.term s).inclusion := by
    induction s with
    | zero => exact F.top_hom
    | succ s ih =>
      change (F.link s).inclusion ≫ S.inclusion s = (F.term (s + 1)).inclusion
      rw [ih]
      exact (F.link s).commutes
  refine ⟨S, ?_, ?_, ?_⟩
  · intro s _ R x y
    have hz : InCoordinateFlag (s + 1) (pointMatrix f e R
        (x * onPoints (F.term s).inclusion R y * x⁻¹ *
          (onPoints (F.term s).inclusion R y)⁻¹)) := by
      simp only [(pointMatrix f e R).map_mul, (pointMatrix f e R).map_inv]
      exact before_comm _ _ ((F.term s).before R y)
    obtain ⟨z, hz⟩ := ((F.term (s + 1)).range_eq R _).mp hz
    refine ⟨z, ?_⟩
    change onPoints (S.inclusion (s + 1)) R z =
      x * onPoints (S.inclusion s) R y * x⁻¹ * (onPoints (S.inclusion s) R y)⁻¹
    simpa only [hinc] using hz
  · intro s _
    let t := F.link s
    exact ⟨t.factor, StandardGroups.additiveGroup k, t.quotient, t.additiveInclusion,
      ⟨StandardGroups.additiveGroupPointsIso k⟩, t.additiveClosed, t.exactness⟩
  · intro i R x
    change InCoordinateFlag i (pointMatrix f e R x) ↔
      ∃ y : GPoints (F.term i).group.val R, onPoints (S.inclusion i) R y = x
    simpa only [hinc] using (F.term i).range_eq R x

/-- Every unipotent group admits a finite central series with closed additive factors. -/
theorem unipotentCentralSeries : UnipotentCentralSeries.{u} := by
  intro k _ G hG
  obtain ⟨n, U, ⟨e⟩, f, hf⟩ := (unipotent_iff_exists_embedding G).mp hG
  obtain ⟨S, hcentral, hfactors, _⟩ := embeddedCentralSeries n G U e f hf
  exact ⟨n * (n + 1), S, hcentral, hfactors⟩

theorem unipotentNilpotence : UnipotentNilpotence.{u} := by
  intro k _ G h
  obtain ⟨length, S, hS, _⟩ := unipotentCentralSeries G h
  exact ⟨length, S, hS⟩

private lemma factor_through_closed {A B C : AffineAlgebraicGroup k}
    (f : A.val ⟶ C.val) (i : B.val ⟶ C.val)
    (hi : IsClosedImmersion i.hom.hom.left)
    (h : ∀ (R : TestAlgebra k) (x : GPoints A.val R),
      ∃ y : GPoints B.val R, onPoints i R y = onPoints f R x) :
    ∃ g : A.val ⟶ B.val, g ≫ i = f := by
  choose ψ hψ using h
  let α : (groupPointsFunctor k).obj A.val ⟶ (groupPointsFunctor k).obj B.val :=
    { app R := GrpCat.ofHom
        { toFun := ψ R
          map_one' := onPoints_injective i hi R
            ((hψ R 1).trans ((onPoints f R).map_one.trans (onPoints i R).map_one.symm))
          map_mul' x y := onPoints_injective i hi R
            ((hψ R (x * y)).trans (((onPoints f R).map_mul x y).trans
              ((congrArg₂ (· * ·) (hψ R x).symm (hψ R y).symm).trans
                ((onPoints i R).map_mul (ψ R x) (ψ R y)).symm))) }
      naturality R T a := by
        apply GrpCat.ext
        intro x
        change ψ T (((groupPointsFunctor k).obj A.val).map a x) =
          ((groupPointsFunctor k).obj B.val).map a (ψ R x)
        apply onPoints_injective i hi T
        rw [hψ, onPoints_natural i, hψ, onPoints_natural f] }
  refine ⟨(AffineAlgebraicGroup.groupHomEquiv A B).symm α, group_hom_ext A.property.1 ?_⟩
  intro R x
  rw [onPoints_comp, scheme_hom_spec α]
  exact hψ R x

private lemma closed_surjective_points_iso {A B : AffineAlgebraicGroup k} (i : A.val ⟶ B.val)
    (hi : IsClosedImmersion i.hom.hom.left)
    (hs : ∀ R : TestAlgebra k, Function.Surjective (onPoints i R)) :
    IsIso i := by
  obtain ⟨j, hj⟩ := factor_through_closed (𝟙 B.val) i hi (fun R x => hs R x)
  refine ⟨j, group_hom_ext A.property.1 ?_, hj⟩
  intro R x
  apply onPoints_injective i hi R
  have hc : (i ≫ j) ≫ i = i := by rw [Category.assoc, hj, Category.comp_id]
  exact congrArg (fun a : A.val ⟶ B.val => onPoints a R x) hc

private lemma scheme_kernel_of_iso {A B C : AffineAlgebraicGroup k}
    (f : A.val ⟶ C.val) (i : B.val ⟶ A.val) (hi : IsClosedImmersion i.hom.hom.left)
    (N : Specs.ClosedSubgroup A.val) (hN : IsSchemeKernel f N)
    (e : B.val ≅ N.group) (he : e.hom ≫ N.inclusion = i) :
    IsSchemeKernel f ⟨B.val, i, hi⟩ := by
  let eX : B.val.X ≅ N.group.X := (Grp.forget (SchemeOver k)).mapIso e
  change IsPullback i.hom.hom (toUnit B.val.X) f.hom.hom η[C.val.X]
  have h₁ : eX.hom ≫ N.inclusion.hom.hom = i.hom.hom ≫ 𝟙 A.val.X :=
    (congrArg (fun a : B.val ⟶ A.val => a.hom.hom) he).trans (Category.comp_id _).symm
  have h₂ : eX.hom ≫ toUnit N.group.X = toUnit B.val.X ≫ 𝟙 _ :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  exact hN.of_iso' eX (Iso.refl A.val.X) (Iso.refl _) (Iso.refl C.val.X) h₁ h₂
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

private lemma scheme_kernel_of_points {A B C : AffineAlgebraicGroup k}
    (f : A.val ⟶ C.val) (i : B.val ⟶ A.val) (hi : IsClosedImmersion i.hom.hom.left)
    (h : ∀ (R : TestAlgebra k) (x : GPoints A.val R),
      onPoints f R x = 1 ↔ ∃ y : GPoints B.val R, onPoints i R y = x) :
    IsSchemeKernel f ⟨B.val, i, hi⟩ := by
  let := C.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  let K := closedSubgroupAlgebraicGroup N
  have hr (R : TestAlgebra k) (x : GPoints B.val R) :
      ∃ y : GPoints K.val R, onPoints N.inclusion R y = onPoints i R x :=
    (kernel_points f N hN R _).mp ((h R _).mpr ⟨x, rfl⟩)
  obtain ⟨j, hj⟩ := factor_through_closed (A := B) (B := K) (C := A)
    i N.inclusion N.isClosedImmersion hr
  have hclosed : IsClosedImmersion j.hom.hom.left :=
    closed_of_comp j N.inclusion (hj.symm ▸ hi) N.isClosedImmersion
  have hbij (R : TestAlgebra k) : Function.Surjective (onPoints j R) := by
    intro x
    obtain ⟨y, hy⟩ := (h R _).mp ((kernel_points f N hN R _).mpr ⟨x, rfl⟩)
    refine ⟨y, onPoints_injective N.inclusion N.isClosedImmersion R ?_⟩
    exact (onPoints_comp j N.inclusion R y).symm.trans
      ((congrArg (fun a : B.val ⟶ A.val => onPoints a R y) hj).trans hy)
  have hIso : IsIso j := closed_surjective_points_iso (A := B) (B := K) j hclosed hbij
  let e : B.val ≅ K.val := @asIso _ _ _ _ j hIso
  exact scheme_kernel_of_iso f i hi N hN e hj

private lemma heightCoordinates_surjective {R : Type u} [CommRing R]
    (d : ℕ) (v : HeightEntries.{u} n d → Multiplicative R) :
    ∃ x : UnitriangularMatrix n R, InHeight d x ∧ heightCoordinates x = v := by
  let M : Mat n R := fun i j =>
    if h : i < j then
      if hd : entryHeight (⟨(i, j), h⟩ : StrictUpper.{u} n) = d then
        Multiplicative.toAdd (v ⟨⟨(i, j), h⟩, hd⟩)
      else 0
    else (1 : Mat n R) i j
  have hM : IsUpperUnitriangular M := by
    refine ⟨?_, ?_⟩
    · intro i j h
      change j < i at h
      simp [M, not_lt_of_gt h, Matrix.one_apply_ne h.ne']
    · intro i
      simp [M]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hM.1]
    simp [hM.2]
  let x : UnitriangularMatrix n R :=
    ⟨Matrix.GeneralLinearGroup.mk'' M (hdet ▸ isUnit_one), hM⟩
  refine ⟨x, ?_, ?_⟩
  · intro p hp
    change M p.1.1 p.1.2 = 0
    simp [M, p.2, hp.ne]
  · funext p
    change Multiplicative.ofAdd (M p.1.1.1 p.1.1.2) = v p
    simp [M, p.1.2, p.2]

private lemma height_step_iff {R : Type u} [CommRing R] {d : ℕ} (x : UnitriangularMatrix n R) :
    InHeight (d + 1) x ↔ InHeight d x ∧ heightCoordinates (d := d) x = 1 := by
  constructor
  · intro h
    refine ⟨fun p hp => h p (by omega), ?_⟩
    funext p
    exact h p.1 (by have := p.2; omega)
  · rintro ⟨h, hcoords⟩ p hp
    by_cases hl : entryHeight p < d
    · exact h p hl
    · have he : entryHeight p = d := by omega
      exact congrFun hcoords ⟨p, he⟩

private def heightCoordinateMap {d : ℕ} (S : Stage f e (d * (n + 1))) :
    (groupPointsFunctor k).obj S.group.val ⟶ additivePowerPoints k (HeightEntries n d) where
  app R :=
    let m := (pointMatrix f e R).comp (onPoints S.inclusion R)
    GrpCat.ofHom
      { toFun := fun x => heightCoordinates (m x)
        map_one' := (congrArg heightCoordinates m.map_one).trans (funext fun p =>
          congrArg Multiplicative.ofAdd (Matrix.one_apply_ne (α := R) p.1.2.ne))
        map_mul' x y := by
          have hx : InHeight d (m x) := (before_height_iff d _).mp (S.before R x)
          have hy : InHeight d (m y) := (before_height_iff d _).mp (S.before R y)
          exact (congrArg heightCoordinates (m.map_mul x y)).trans (funext fun p =>
            entry_mul _ _ hx hy p.1 p.2) }
  naturality R T a := by
    apply GrpCat.ext
    intro x
    have hm := pointMatrix_natural (S.inclusion ≫ f) e a x
    change pointMatrix f e T (onPoints S.inclusion T
      (((groupPointsFunctor k).obj S.group.val).map a x)) = _ at hm
    change heightCoordinates (pointMatrix f e T (onPoints S.inclusion T
        (((groupPointsFunctor k).obj S.group.val).map a x))) = _
    rw [hm]
    rfl

/-- The ordinary height quotients are the full vector groups on those diagonals. -/
theorem heightQuotients : HeightQuotients.{u} := by
  intro k _ n U e
  obtain ⟨F⟩ := exists_stages (f := 𝟙 U.val) (e := e)
  let T := F.term
  let H (d : ℕ) : HeightSubgroup U e d :=
    { group := (T (d * (n + 1))).group
      inclusion := (T (d * (n + 1))).inclusion
      closed := (T (d * (n + 1))).closed
      range_eq := by
        intro R g
        constructor
        · intro h
          let x : GPoints U.val R := e.inv.app R g
          have hx : pointMatrix (𝟙 U.val) e R x = g := by
            change e.hom.app R (e.inv.app R g) = g
            exact congrArg (fun a => a g) (e.app R).inv_hom_id
          obtain ⟨y, hy⟩ := ((T (d * (n + 1))).range_eq R x).mp
            ((before_height_iff d _).mpr (hx.symm ▸ h))
          exact ⟨y, (congrArg (e.hom.app R).hom hy).trans hx⟩
        · rintro ⟨x, rfl⟩
          exact (before_height_iff d _).mp ((T (d * (n + 1))).before R x) }
  refine ⟨H, ?_⟩
  intro d
  let B := T ((d + 1) * (n + 1))
  let A := T (d * (n + 1))
  have hle := Nat.mul_le_mul_right (n + 1) (Nat.le_succ d)
  obtain ⟨j, hj⟩ := factor_through_closed B.inclusion A.inclusion A.closed (fun R x =>
    (A.range_eq R _).mp (fun p hp => B.before R x p (lt_of_lt_of_le hp hle)))
  have hc := closed_of_comp j A.inclusion (hj.symm ▸ B.closed) A.closed
  let V := StandardGroups.additivePowerGroup k (HeightEntries n d)
  let c := StandardGroups.additivePowerGroupPointsIso k (HeightEntries n d)
  let α := heightCoordinateMap A ≫ c.inv
  let q : A.group.val ⟶ V.val := (AffineAlgebraicGroup.groupHomEquiv A.group V).symm α
  have hcoord (R : TestAlgebra k) (x : GPoints A.group.val R) :
      (c.hom.app R).hom (onPoints q R x) =
        heightCoordinates (pointMatrix (𝟙 U.val) e R (onPoints A.inclusion R x)) := by
    rw [scheme_hom_spec α]
    let v : (additivePowerPoints k (HeightEntries n d)).obj R :=
      heightCoordinates (pointMatrix (𝟙 U.val) e R (onPoints A.inclusion R x))
    change c.hom.app R (c.inv.app R v) = v
    exact congrArg (fun a => a v) (c.app R).inv_hom_id
  have hinj (R : TestAlgebra k) : Function.Injective (c.hom.app R).hom :=
    ((CategoryTheory.forget GrpCat).mapIso (c.app R)).toEquiv.injective
  have hqker (R : TestAlgebra k) (x : GPoints A.group.val R) :
      onPoints q R x = 1 ↔
        ∃ y : GPoints B.group.val R, onPoints j R y = x := by
    have h₁ : InHeight d (pointMatrix (𝟙 U.val) e R (onPoints A.inclusion R x)) :=
      (before_height_iff d _).mp (A.before R x)
    let x₀ := pointMatrix (𝟙 U.val) e R (onPoints A.inclusion R x)
    have hn := (c.hom.app R).hom.map_one
    have hz : onPoints q R x = 1 ↔ heightCoordinates (d := d) x₀ = 1 :=
      ⟨fun h => (hcoord R x).symm.trans ((congrArg (c.hom.app R).hom h).trans hn),
       fun h => hinj R ((hcoord R x).trans (h.trans hn.symm))⟩
    calc
      _ ↔ heightCoordinates (d := d) x₀ = 1 := hz
      _ ↔ InHeight (d + 1) x₀ :=
        ⟨fun h => (height_step_iff x₀).mpr ⟨h₁, h⟩, fun h => ((height_step_iff x₀).mp h).2⟩
      _ ↔ InCoordinateFlag ((d + 1) * (n + 1)) x₀ := (before_height_iff _ _).symm
      _ ↔ ∃ y : GPoints B.group.val R, onPoints B.inclusion R y = onPoints A.inclusion R x :=
        B.range_eq R _
      _ ↔ _ := by
        constructor
        · rintro ⟨y, hy⟩
          refine ⟨y, onPoints_injective A.inclusion A.closed R ?_⟩
          rw [← onPoints_comp, hj]
          exact hy
        · rintro ⟨y, hy⟩
          exact ⟨y, by rw [← hy, ← onPoints_comp, hj]⟩
  have hk := scheme_kernel_of_points q j hc hqker
  have hsurj (R : TestAlgebra k) : Function.Surjective (onPoints q R) := by
    intro v
    obtain ⟨x, hx, he⟩ := heightCoordinates_surjective d ((c.hom.app R).hom v)
    obtain ⟨y, hy⟩ := ((H d).range_eq R x).mp hx
    refine ⟨y, hinj R ?_⟩
    rw [hcoord]
    change heightCoordinates (e.hom.app R (onPoints A.inclusion R y)) = _
    exact (congrArg (heightCoordinates (d := d)) hy).trans he
  obtain ⟨I, p, i, hfac, _, _⟩ := schemeImageFactorization A.group V q
  have hs (R : TestAlgebra k) : Function.Surjective (onPoints i R) := by
    intro x
    obtain ⟨y, hy⟩ := hsurj R x
    refine ⟨onPoints p R y, ?_⟩
    rwa [← onPoints_comp, hfac.1]
  obtain ⟨hpi, hp, hps, hpf, hpa, hi⟩ := hfac
  let := closed_surjective_points_iso i hi hs
  have hiso : IsIso i.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i)
    infer_instance
  have hq' : Specs.IsImageFactorization q q (𝟙 V.val) := by
    refine ⟨Category.comp_id _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hpi]
      change Flat (p.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    · rw [← hpi]
      change Surjective (p.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    · rw [← hpi]
      change LocallyOfFinitePresentation (p.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    · rw [← hpi]
      change IsAffineHom (p.hom.hom.left ≫ i.hom.hom.left)
      infer_instance
    · change IsClosedImmersion (𝟙 V.val.X.left)
      infer_instance
  refine ⟨j, hc, V, c, q, hj,
    ⟨hk, hq'.2.1, hq'.2.2.1, hq'.2.2.2.1, quotientRepresentsImage hq' hk⟩, ?_⟩
  exact hcoord

end Schemes

end

end LinearAlgebraicGroups.Unipotent
