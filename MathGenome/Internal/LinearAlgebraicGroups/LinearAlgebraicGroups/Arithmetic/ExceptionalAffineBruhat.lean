import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedAlcoveVertices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedCentralCover
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport
import Mathlib.FieldTheory.LinearDisjoint
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open Specs.ExceptionalAffineBruhat
open scoped Pointwise Matrix CategoryTheory.MonObj TensorProduct WithZero

theorem e6ProjectedLattices : E6ProjectedLattices :=
  ExceptionalAffineRootSystems.e6ProjectedLattices

theorem e6CoweightQuotient : E6CoweightClass :=
  ExceptionalAffineRootSystems.e6CoweightQuotient

theorem residuePowerCounts : ResiduePowerCounts := by
  intro R _ _ _ _ m
  let P := IsLocalRing.maximalIdeal R
  have hP : P ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  change Nat.card (R ⧸ P ^ m) = Nat.card (R ⧸ P) ^ m
  simpa only [Submodule.cardQuot_apply] using (cardQuot_pow_of_prime hP (i := m))

theorem residueLayerCounts : ResidueLayerCounts := by
  intro R _ _ _ _ a b hab
  let P := IsLocalRing.maximalIdeal R
  let q := Nat.card (IsLocalRing.ResidueField R)
  change Nat.card (Submodule.map (P ^ b).mkQ (P ^ a)) = q ^ (b - a)
  have hle : P ^ b ≤ P ^ a := Ideal.pow_le_pow_right hab
  have h := Submodule.card_quotient_mul_card_quotient
    (P ^ a : Ideal R) (P ^ b : Ideal R) hle
  rw [residuePowerCounts R a, residuePowerCounts R b] at h
  change Nat.card (Submodule.map (P ^ b).mkQ (P ^ a)) * q ^ a = q ^ b at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q ^ a from pow_pos Nat.card_pos a)
  rw [h, ← pow_add, Nat.sub_add_cancel hab]

theorem leftCosetIndex : LeftCosetIndex := by
  intro G _ I g
  let x := QuotientGroup.mk (s := I) g
  have orbit_eq : leftCosets I g = MulAction.orbit I x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz
      exact ⟨⟨a, ha⟩, (QuotientGroup.mk_mul_of_mem (a * g) hb).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : G) * g, DoubleCoset.mem_doubleCoset.mpr
        ⟨a, a.prop, 1, I.one_mem, (mul_one _).symm⟩, rfl⟩
  have stabilizer_eq : MulAction.stabilizer I x = conjugateIntersection I g := by
    ext a
    change ((a : G) * g : G ⧸ I) = (g : G ⧸ I) ↔ g⁻¹ * a * (g⁻¹)⁻¹ ∈ I
    rw [eq_comm, QuotientGroup.eq, inv_inv, mul_assoc]
  rw [orbit_eq, ← stabilizer_eq]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer I x)

theorem rankOneWallMultiplication : RankOneWallMultiplication := by
  intro K _ p t
  apply Subtype.val_injective
  change (!![1, (t : K); 0, 1] : Matrix (Fin 2) (Fin 2) K) *
      !![0, -(p : K); (↑p⁻¹ : K), 0] =
    !![1, 0; (↑t⁻¹ : K), 1] * !![(↑(t * p⁻¹) : K), 0; 0, (↑(t * p⁻¹)⁻¹ : K)] *
      !![1, -(p : K) ^ 2 / (t : K); 0, 1]
  ext i j
  have hp : (p : K) ≠ 0 := Units.ne_zero p
  have ht : (t : K) ≠ 0 := Units.ne_zero t
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;>
    field_simp
  all_goals ring

theorem rankOneWallConjugation : RankOneWallConjugation := by
  intro K _ p
  have hp : (p : K) ≠ 0 := Units.ne_zero p
  constructor
  · intro t
    apply Subtype.val_injective
    change (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
        !![0, -(p : K); (↑p⁻¹ : K), 0] =
      !![0, -(p : K); (↑p⁻¹ : K), 0] *
        !![1, 0; -(↑p⁻¹ : K) ^ 2 * t, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    field_simp
  · apply Subtype.val_injective
    change (!![0, -(p : K); (↑p⁻¹ : K), 0] : Matrix (Fin 2) (Fin 2) K) *
        !![0, -(p : K); (↑p⁻¹ : K), 0] =
      !![(↑(-1 : Kˣ) : K), 0; 0, (↑(-1 : Kˣ)⁻¹ : K)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, hp]

theorem rankOneDoubleCosetProduct : RankOneDoubleCosetProduct := by
  intro G _ I A Aplus g s hA hFactor
  let D := fun (h : G) => DoubleCoset.doubleCoset h I I
  have coset_eq {r t : G} (h : r ∈ D t) : D r = D t :=
    DoubleCoset.doubleCoset_eq_of_mem h
  have product_membership {z : G} : z ∈ D g * D s ↔ ∃ u ∈ A, z ∈ D (g * u * s) := by
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
      obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
      obtain ⟨u, hu, j, _, hsjs, hbc⟩ := hFactor (b * c) (I.mul_mem hb hc)
      refine ⟨u, hu, DoubleCoset.mem_doubleCoset.mpr
        ⟨a, ha, (s⁻¹ * j * s) * d, I.mul_mem hsjs hd, ?_⟩⟩
      calc
        (a * g * b) * (c * s * d) = (a * g) * (b * c) * s * d := by group
        _ = a * (g * u * s) * ((s⁻¹ * j * s) * d) := by rw [hbc]; group
    · rintro ⟨u, hu, hz⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hz
      have hx : a * g * u ∈ D g :=
        DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, u, hA hu, rfl⟩
      have hy : s * b ∈ D s := DoubleCoset.mem_doubleCoset.mpr ⟨1, I.one_mem, b, hb, by simp⟩
      simpa only [mul_assoc] using (Set.mul_mem_mul hx hy : (a * g * u) * (s * b) ∈ D g * D s)
  have mem_product {z : G} (hz : z ∈ D (g * s)) : z ∈ D g * D s :=
    product_membership.mpr ⟨1, A.one_mem, by simpa only [mul_one] using hz⟩
  refine ⟨?_, ?_⟩
  · intro hPos
    apply Set.Subset.antisymm ?_ (fun _ hz => mem_product hz)
    intro z hz
    obtain ⟨u, hu, hzu⟩ := product_membership.mp hz
    have hmem : g * u * s ∈ D (g * s) :=
      DoubleCoset.mem_doubleCoset.mpr
        ⟨g * u * g⁻¹, hPos u hu, 1, I.one_mem, by group⟩
    rwa [coset_eq hmem] at hzu
  · intro hDeep hExact hExists
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨u, hu, hzu⟩ := product_membership.mp hz
      by_cases h : u ∈ Aplus
      · have hmem : g * u * s ∈ D (g * s) :=
          DoubleCoset.mem_doubleCoset.mpr ⟨1, I.one_mem, s⁻¹ * u * s, hDeep u h, by group⟩
        rw [coset_eq hmem] at hzu
        exact Or.inl hzu
      · rw [coset_eq (hExact u hu h)] at hzu
        exact Or.inr hzu
    · intro z hz
      rcases hz with hz | hz
      · exact mem_product hz
      · obtain ⟨u, hu, hNot⟩ := hExists
        exact product_membership.mpr ⟨u, hu, by
          rw [coset_eq (hExact u hu hNot)]
          exact hz⟩

theorem coxeterDoubleCosets : CoxeterDoubleCosets := by
  classical
  intro G B W _ _ M cs I lift q hq hOne hSquare
  let D := fun w => DoubleCoset.doubleCoset (lift w) I I
  change
    (∀ w, Nat.card (leftCosets I (lift w)) = q ^ cs.length w) →
    (∀ w i, ¬cs.IsRightDescent w i → D w * D (cs.simple i) = D (w * cs.simple i)) →
    (∀ w i, cs.IsRightDescent w i → D w * D (cs.simple i) = D (w * cs.simple i) ∪ D w) →
    (∀ w, lift w ∈ Subgroup.closure ((I : Set G) ∪ Set.range (lift ∘ cs.simple))) →
    (Pairwise fun w v => Disjoint (D w) (D v)) ∧
      ⋃ w, D w = (Subgroup.closure ((I : Set G) ∪ Set.range (lift ∘ cs.simple)) : Set G)
  intro hCount hUp hDown hLifts
  have length_eq {w v : W} (h : D w = D v) : cs.length w = cs.length v := by
    apply Nat.pow_right_injective hq
    change q ^ cs.length w = q ^ cs.length v
    rw [← hCount w, ← hCount v]
    exact congrArg (fun s : Set G => Nat.card (QuotientGroup.mk (s := I) '' s)) h
  have injective : Function.Injective D := by
    suffices ∀ n (w v : W), cs.length w = n → D w = D v → w = v by
      exact fun _ _ h => this _ _ _ rfl h
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w v hn hEq
      by_cases hw : w = 1
      · rw [hw]
        exact (cs.length_eq_zero_iff.mp (by simpa [hw] using (length_eq hEq).symm)).symm
      obtain ⟨i, hwi⟩ := cs.exists_rightDescent_of_ne_one hw
      have hD := congrArg (fun s : Set G => s * D (cs.simple i)) hEq
      change D w * D (cs.simple i) = D v * D (cs.simple i) at hD
      rw [hDown _ _ hwi] at hD
      have hvi : cs.IsRightDescent v i := by
        by_contra hvi
        rw [hUp _ _ hvi] at hD
        have hm : lift w ∈ D (v * cs.simple i) := hD ▸
          (Or.inr (DoubleCoset.mem_doubleCoset_self I I (lift w)) :
            lift w ∈ D (w * cs.simple i) ∪ D w)
        have hlen := length_eq (DoubleCoset.doubleCoset_eq_of_mem hm)
        have hsame := length_eq hEq
        change ¬ cs.length (v * cs.simple i) < cs.length v at hvi
        rcases cs.length_mul_simple v i with hv | hv <;> omega
      rw [hDown _ _ hvi] at hD
      have hm : lift (w * cs.simple i) ∈ D (v * cs.simple i) ∪ D v := hD ▸
        (Or.inl (DoubleCoset.mem_doubleCoset_self I I (lift (w * cs.simple i))) :
          lift (w * cs.simple i) ∈ D (w * cs.simple i) ∪ D w)
      have hm' : lift (w * cs.simple i) ∈ D (v * cs.simple i) := by
        rcases hm with hm | hm
        · exact hm
        have hlen := length_eq (DoubleCoset.doubleCoset_eq_of_mem hm)
        have hsame := length_eq hEq
        change cs.length (w * cs.simple i) < cs.length w at hwi
        omega
      have hshort : cs.length (w * cs.simple i) < n := hn ▸ hwi
      have he := ih _ hshort _ _ rfl (DoubleCoset.doubleCoset_eq_of_mem hm')
      exact mul_right_cancel he
  refine ⟨fun w v h => by
    by_contra hd
    exact h (injective (DoubleCoset.eq_of_not_disjoint hd)), ?_⟩
  let S := (I : Set G) ∪ Set.range (lift ∘ cs.simple)
  let U := ⋃ w, D w
  have memU (w : W) {x : G} (hx : x ∈ D w) : x ∈ U := Set.mem_iUnion.mpr ⟨w, hx⟩
  have rightI {x y : G} (hx : x ∈ U) (hy : y ∈ I) : x * y ∈ U := by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
    exact memU w (DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * y, I.mul_mem hb hy,
      mul_assoc _ _ _⟩)
  have rightSimple {x : G} (hx : x ∈ U) (i : B) : x * lift (cs.simple i) ∈ U := by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    have hmul : x * lift (cs.simple i) ∈ D w * D (cs.simple i) :=
      Set.mul_mem_mul hw (DoubleCoset.mem_doubleCoset_self I I _)
    by_cases hd : cs.IsRightDescent w i
    · rw [hDown _ _ hd] at hmul
      exact hmul.elim (memU (w * cs.simple i)) (memU w)
    · rw [hUp _ _ hd] at hmul
      exact memU (w * cs.simple i) hmul
  have rightGen {x y : G} (hx : x ∈ U) (hy : y ∈ S) : x * y ∈ U := by
    rcases hy with hy | ⟨i, rfl⟩
    · exact rightI hx hy
    · exact rightSimple hx i
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inl ha)) (hLifts w)) (Subgroup.subset_closure (Or.inl hb))
  · intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one =>
      exact memU 1 (DoubleCoset.mem_doubleCoset.mpr
        ⟨(lift 1)⁻¹, I.inv_mem hOne, 1, I.one_mem, by simp⟩)
    | mul_right x hx y hy ih => exact rightGen ih hy
    | mul_inv_cancel x hx y hy ih =>
      rcases hy with hy | ⟨i, rfl⟩
      · exact rightI ih (I.inv_mem hy)
      · have h := rightI (rightSimple ih i) (I.inv_mem (hSquare i))
        simpa only [Function.comp_apply, pow_two, mul_inv_rev, mul_assoc,
          mul_inv_cancel_left] using h

section Assembly

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer threshold)

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

private theorem unitTorus_le_iwahori (C : LocalComparison (j := j) (Wf := Wf) A p) :
    C.T₀ ≤ C.I := by
  change (Specs.ExceptionalIwahoriImageComparison.integralUnitTorus (K := K) M).comap j ≤ _
  rw [← C.localIwahori.intersection]
  exact inf_le_left

/-- Lifts of the same affine label differ by a rational unit torus element. -/
theorem sameLabel_div_mem_unitTorus (C : LocalComparison (j := j) (Wf := Wf) A p)
    {n m : C.N} (h : C.affine n = C.affine m) : (n : G) * (m : G)⁻¹ ∈ C.T₀ := by
  change _ ∈ (Specs.ExceptionalIwahoriImageComparison.integralUnitTorus (K := K) M).comap j
  rw [← C.kernel]
  refine ⟨n * m⁻¹, ?_, rfl⟩
  simp [h]

/-- The ordinary double coset is independent of the choice of lift. -/
theorem sameLabel_doubleCoset (C : LocalComparison (j := j) (Wf := Wf) A p)
    {n m : C.N} (h : C.affine n = C.affine m) :
    DoubleCoset.doubleCoset (n : G) C.I C.I = DoubleCoset.doubleCoset (m : G) C.I C.I := by
  apply DoubleCoset.doubleCoset_eq_of_mem
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨(n : G) * (m : G)⁻¹, unitTorus_le_iwahori C (sameLabel_div_mem_unitTorus C h),
      1, C.I.one_mem, by group⟩

/-- When the affine image is ordinary, the Iwahori and ordinary normalizer
generate the entire marked point group. -/
theorem ordinaryRange_generates (C : LocalComparison (j := j) (Wf := Wf) A p)
    (h : C.affine.range = A.affineWeylGroup) : C.G₀ = ⊤ := by
  have he : (A.affineWeylGroup.comap C.affine).map C.N.subtype = C.N := by
    apply le_antisymm (Subgroup.map_subtype_le _)
    intro g hg
    let n : C.N := ⟨g, hg⟩
    refine ⟨n, ?_, rfl⟩
    change C.affine n ∈ A.affineWeylGroup
    rw [← h]
    exact ⟨n, rfl⟩
  rw [LocalComparison.G₀, he]
  exact C.localIwahori.generation

private theorem ordinaryLifts_generate (C : LocalComparison (j := j) (Wf := Wf) A p) :
    C.G₀ = Subgroup.closure ((C.I : Set G) ∪ Set.range
      (fun i : A.SimpleWall p => (C.lift (C.coxeter.coxeter.simple i) : G))) := by
  let H := Subgroup.closure ((C.I : Set G) ∪ Set.range
    (fun i : A.SimpleWall p => (C.lift (C.coxeter.coxeter.simple i) : G)))
  change C.G₀ = H
  refine le_antisymm (sup_le (fun _ hg => Subgroup.subset_closure (Or.inl hg)) ?_) ?_
  · intro g hg
    obtain ⟨n, hn, rfl⟩ := hg
    let w : A.affineWeylGroup := ⟨C.affine n, hn⟩
    obtain ⟨l, hl⟩ := C.coxeter.coxeter.wordProd_surjective w
    let v (l : List (A.SimpleWall p)) : C.N :=
      (l.map (C.lift ∘ C.coxeter.coxeter.simple)).prod
    have hv (l) : (v l : G) ∈ H := by
      induction l with
      | nil => exact H.one_mem
      | cons i l ih =>
        exact H.mul_mem (Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)) ih
    have hlabel (l) : C.affine (v l) = (C.coxeter.coxeter.wordProd l).val := by
      induction l with
      | nil => simp [v]
      | cons i l ih =>
        simp [v, C.coxeter.coxeter.wordProd_cons, ih, C.lift_label]
    have he : C.affine n = C.affine (v l) := by rw [hlabel, hl]
    have hmem := unitTorus_le_iwahori C (sameLabel_div_mem_unitTorus C he)
    change (n : G) ∈ H
    simpa only [inv_mul_cancel_right] using H.mul_mem (Subgroup.subset_closure (Or.inl hmem)) (hv l)
  · apply (Subgroup.closure_le C.G₀).2
    rintro g (hg | ⟨i, rfl⟩)
    · exact le_sup_left (b := (A.affineWeylGroup.comap C.affine).map C.N.subtype) hg
    · apply le_sup_right (a := C.I)
      refine ⟨C.lift (C.coxeter.coxeter.simple i), ?_, rfl⟩
      change C.affine (C.lift _) ∈ A.affineWeylGroup
      rw [C.lift_label]
      exact Subtype.prop _

open scoped Classical in
/-- Wall multiplication and the congruence indices give the actual double
cosets and detect precisely the ordinary labels in the normalizer. -/
theorem bruhatFromWallProducts (C : LocalComparison (j := j) (Wf := Wf) A p) (q : ℕ)
    (hq : 2 ≤ q) (rankOne : C.RankOneLifts)
    (ordinary : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype)
    (base : ∀ g, g ∈ C.I ↔ C.chart.atPoint p g)
    (translated : ∀ (w : A.affineWeylGroup) (g : G),
      g ∈ C.I.map (MulAut.conj ((C.lift w : C.N) : G)).toMonoidHom ↔
        C.chart.atPoint (w.val p) g)
    (product : ∀ (w : A.affineWeylGroup) (i : A.SimpleWall p),
      letI := C.coxeter.action
      let s := C.coxeter.coxeter.simple i
      C.cell w * C.cell s =
        if A.positive p (w • i.val) then C.cell (w * s) else C.cell (w * s) ∪ C.cell w)
    (index : ∀ w : A.affineWeylGroup,
      (conjugateIntersection C.I ((C.lift w : C.N) : G)).index =
        q ^ ∑ᶠ a, (threshold (A.root a (w.val p)) - threshold (A.root a p)).toNat) :
    C.Bruhat q := by
  classical
  let cs := C.coxeter.coxeter
  let L : A.affineWeylGroup → G := fun w => C.lift w
  let _ := C.coxeter.action
  have hOne : L 1 ∈ C.I := by
    have h := sameLabel_div_mem_unitTorus C (m := 1) (C.lift_label 1 |>.trans C.affine.map_one.symm)
    exact unitTorus_le_iwahori C (by simpa using h)
  have hSquare (i : A.SimpleWall p) : L (cs.simple i) ^ 2 ∈ C.I := by
    have h : C.affine (C.lift (cs.simple i) ^ 2) = C.affine 1 := by
      rw [map_pow, C.lift_label, ← Subgroup.coe_pow, cs.simple_sq, map_one]
      rfl
    exact unitTorus_le_iwahori C (by simpa using sameLabel_div_mem_unitTorus C h)
  have hUp (w) (i) (h : ¬cs.IsRightDescent w i) :
      C.cell w * C.cell (cs.simple i) = C.cell (w * cs.simple i) := by
    let a : J × ℤ := w • i.val
    have hz : A.wallValue a p ≠ 0 := by
      intro he
      apply C.geometry.regular a.1
      refine ⟨-a.2, ?_⟩
      rw [Int.cast_neg, eq_comm, eq_neg_iff_add_eq_zero]
      exact he
    have hpos : A.positive p (w • i.val) :=
      lt_of_le_of_ne (le_of_not_gt fun hh => h ((C.coxeter.right_descent w i).2 hh)) (Ne.symm hz)
    simpa only [ite_eq_left hpos] using product w i
  have hDown (w) (i) (h : cs.IsRightDescent w i) :
      C.cell w * C.cell (cs.simple i) = C.cell (w * cs.simple i) ∪ C.cell w := by
    have hneg : ¬ A.positive p (w • i.val) := not_lt_of_gt ((C.coxeter.right_descent w i).1 h)
    simpa only [ite_eq_right hneg] using product w i
  have hCount (w : A.affineWeylGroup) :
      Nat.card (leftCosets C.I (L w)) = q ^ cs.length w := by
    rw [leftCosetIndex, index, C.coxeter.length_thresholds]
  have hgen (w) : L w ∈ Subgroup.closure ((C.I : Set G) ∪ Set.range (L ∘ cs.simple)) := by
    change L w ∈ Subgroup.closure ((C.I : Set G) ∪ Set.range
      (fun i => (C.lift (cs.simple i) : G)))
    rw [← ordinaryLifts_generate C]
    apply le_sup_right (a := C.I)
    refine ⟨C.lift w, ?_, rfl⟩
    change C.affine (C.lift w) ∈ A.affineWeylGroup
    rw [C.lift_label]
    exact w.property
  obtain ⟨hd, hc⟩ := coxeterDoubleCosets cs C.I L q hq hOne hSquare hCount hUp hDown hgen
  change ⋃ w, C.cell w = (Subgroup.closure ((C.I : Set G) ∪ Set.range
    (fun i : A.SimpleWall p => (C.lift (C.coxeter.coxeter.simple i) : G))) : Set G) at hc
  rw [← ordinaryLifts_generate C] at hc
  exact ⟨rankOne, ordinary, base, translated, hd, hc, product, index, hCount⟩


/-- The extended alcove stabilizer identifies the quotient of the marked
point group by its ordinary subgroup. Its elements lift to the marked
normalizer with their given affine labels. -/
theorem typeQuotientOfAffineRange (C : LocalComparison (j := j) (Wf := Wf) A p)
    (normal : C.G₀.Normal)
    (ordinary : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype)
    (extended : C.affine.range = A.extendedAffineWeylGroup) :
    letI := normal
    ∃ (e : G ⧸ C.G₀ ≃* alcoveStabilizer A (A.alcove p))
      (lift : alcoveStabilizer A (A.alcove p) → C.N),
      (∀ ω, C.affine (lift ω) = ω.val.val) ∧
      ∀ ω, e (QuotientGroup.mk (lift ω : G)) = ω := by
  classical
  let _ := normal
  let q := QuotientGroup.mk' C.G₀
  let r := q.comp C.N.subtype
  let Ω := alcoveStabilizer A (A.alcove p)
  have hOrdinary (n : C.N) : r n = 1 ↔ C.affine n ∈ A.affineWeylGroup := by
    change (QuotientGroup.mk (s := C.G₀) (n : G)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    have hmem : (n : G) ∈ C.G₀ ↔ (n : G) ∈ C.G₀ ⊓ C.N :=
      ⟨fun h => ⟨h, n.property⟩, fun h => h.1⟩
    rw [hmem, ordinary]
    constructor
    · rintro ⟨m, hm, he⟩
      have h : m = n := Subtype.ext he
      exact h ▸ hm
    · intro h
      exact ⟨n, h, rfl⟩
  have hDiff (n m : C.N) : r n = r m ↔
      C.affine n * (C.affine m)⁻¹ ∈ A.affineWeylGroup := by
    rw [← C.affine.map_inv, ← C.affine.map_mul, ← hOrdinary, r.map_mul, r.map_inv, mul_inv_eq_one]
  have hSurj : Function.Surjective r := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    have hle : C.I ⊔ C.N ≤ r.range.comap q := sup_le (fun a ha => by
      change q a ∈ r.range
      have h : q a = 1 := (QuotientGroup.eq_one_iff _).mpr ((le_sup_left : C.I ≤ C.G₀) ha)
      rw [h]
      exact Subgroup.one_mem _) (fun a ha => ⟨⟨a, ha⟩, rfl⟩)
    have hgen : C.I ⊔ C.N = ⊤ := C.localIwahori.generation
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  have hLift (ω : Ω) : ω.val.val ∈ C.affine.range := by
    rw [extended]
    exact ω.val.property
  choose lift hlift using hLift
  let f : Ω →* G ⧸ C.G₀ :=
    { toFun := fun ω => r (lift ω)
      map_one' := by
        apply (hOrdinary _).2
        rw [hlift]
        exact Subgroup.one_mem _
      map_mul' ω τ := by
        rw [← map_mul]
        apply (hDiff _ _).2
        rw [hlift, map_mul, hlift, hlift]
        change ((ω.val.val * τ.val.val) * (ω.val.val * τ.val.val)⁻¹) ∈ _
        rw [mul_inv_cancel]
        exact Subgroup.one_mem _ }
  have extOfOrdinary : A.affineWeylGroup ≤ A.extendedAffineWeylGroup := by
    intro x hx
    let w : A.affineWeylGroup := ⟨x, hx⟩
    rw [← extended]
    exact ⟨C.lift w, C.lift_label w⟩
  have injective : Function.Injective f := by
    intro ω τ h
    have hmem := (hDiff (lift ω) (lift τ)).mp h
    rw [hlift, hlift] at hmem
    let w : A.affineWeylGroup := ⟨(ω * τ⁻¹).val.val, hmem⟩
    have hstab : w.val '' A.alcove p = A.alcove p := (ω * τ⁻¹).property
    obtain ⟨v, _, unique⟩ := C.geometry.simply_transitive p C.geometry.regular
    have hw : w = 1 := (unique w hstab).trans (unique 1 (by simp)).symm
    have heq := congrArg (fun w : A.affineWeylGroup => w.val) hw
    change ω.val.val * τ.val.val⁻¹ = 1 at heq
    exact Subtype.ext (Subtype.ext (mul_inv_eq_one.mp heq))
  have surjective : Function.Surjective f := by
    intro g
    obtain ⟨n, rfl⟩ := hSurj g
    let a : A.extendedAffineWeylGroup := ⟨C.affine n, extended ▸ ⟨n, rfl⟩⟩
    obtain ⟨reg, himg⟩ := C.geometry.extended_action a
    obtain ⟨w, hw, _⟩ := C.geometry.simply_transitive (a.val p) reg
    let w' : A.extendedAffineWeylGroup := ⟨w.val, extOfOrdinary w.property⟩
    have eqImage : w'.val '' A.alcove p = a.val '' A.alcove p := hw.trans himg.symm
    have hω : (w'⁻¹ * a).val '' A.alcove p = A.alcove p := by
      change ((w'.val⁻¹ * a.val) : V ≃ᵃ[ℚ] V) '' A.alcove p = _
      rw [AffineEquiv.coe_mul, Set.image_comp, ← eqImage, Set.image_image]
      simp [AffineEquiv.inv_def]
    let ω : Ω := ⟨w'⁻¹ * a, hω⟩
    refine ⟨ω, Eq.symm ((hDiff n (lift ω)).2 ?_)⟩
    rw [hlift ω]
    change a.val * (w'.val⁻¹ * a.val)⁻¹ ∈ A.affineWeylGroup
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using w.property
  let e := MulEquiv.ofBijective f ⟨injective, surjective⟩
  exact ⟨e.symm, lift, hlift, fun ω => e.symm_apply_apply ω⟩

end Assembly


section CentralApartment

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots simpleRootValues)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)


variable {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

/-- A central cover identifies the rational cocharacter apartments, retaining
the marked roots, coroots and alcoves in the two lattice forms. -/
theorem centralCoverApartment (c : MarkedCentralCover M M')
    {n : ℕ} (b : Fin n ≃ D.base.support)
    (hd : Module.finrank ℤ D.Y = n) (he : Module.finrank ℤ E.Y = n) :
    let A := ApartmentRoots.split D.datum ℚ
    let A' := ApartmentRoots.split E.datum ℚ
    ∃ e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y),
      e.toLinearMap = c.pushCocharacter.baseChange ℚ ∧
      (∀ a x, A'.root (c.rootEquiv a) (e x) = A.root a x) ∧
      (∀ a, e (A.coroot a) = A'.coroot (c.rootEquiv a)) ∧
      ∀ p, e '' A.alcove p = A'.alcove (e p) := by
  intro A A'
  let _ := D.finiteRoots
  let _ := D.reduced
  let _ := D.freeX
  let _ := D.freeY
  let _ := D.finiteX
  let _ := D.finiteY
  let _ := E.freeY
  let _ := E.finiteY
  obtain ⟨d, hD⟩ := ExceptionalAffineRootSystems.cocharacterApartmentCoordinates (K := ℚ) D.datum D.base b hd
  let L := c.pushCocharacter.baseChange ℚ
  have hr (a : D.I) : (A'.root (c.rootEquiv a)).comp L = A.root a := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r y
    change (A'.root (c.rootEquiv a)) (r ⊗ₜ[ℤ] c.pushCocharacter y) =
      (A.root a) (r ⊗ₜ[ℤ] y)
    rw [TensorProduct.tmul_eq_smul_one_tmul r y,
      TensorProduct.tmul_eq_smul_one_tmul r (c.pushCocharacter y), map_smul, map_smul]
    change r • RootData.extendFunctional ℚ (E.datum.root' (c.rootEquiv a))
        (1 ⊗ₜ[ℤ] c.pushCocharacter y) =
      r • RootData.extendFunctional ℚ (D.datum.root' a) (1 ⊗ₜ[ℤ] y)
    rw [RootData.extendFunctional_one_tmul, RootData.extendFunctional_one_tmul]
    have h := c.pairing (E.datum.root (c.rootEquiv a)) y
    rw [c.roots a] at h
    exact congrArg (fun z : ℤ => r • (z : ℚ)) h.symm
  have hval (a : D.I) (x : ℚ ⊗[ℤ] D.Y) : A'.root (c.rootEquiv a) (L x) = A.root a x :=
    congrArg (fun f : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] ℚ => f x) (hr a)
  have inj : Function.Injective L := by
    intro x y h
    apply d.injective
    change d.toLinearMap x = d.toLinearMap y
    rw [hD]
    funext i
    change A.root (b i) x = A.root (b i) y
    rw [← hval, ← hval, h]
  have hdim : Module.finrank ℚ (ℚ ⊗[ℤ] D.Y) = Module.finrank ℚ (ℚ ⊗[ℤ] E.Y) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hd, he]
  let e := LinearEquiv.ofBijective L ⟨inj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp inj⟩
  refine ⟨e, rfl, hval, ?_, ?_⟩
  · intro a
    change (1 : ℚ) ⊗ₜ[ℤ] c.pushCocharacter (D.datum.coroot a) =
      (1 : ℚ) ⊗ₜ[ℤ] E.datum.coroot (c.rootEquiv a)
    rw [c.coroots]
  · intro p
    have hw (a : D.I) (m : ℤ) (x : ℚ ⊗[ℤ] D.Y) :
        A'.wallValue (c.rootEquiv a, m) (e x) = A.wallValue (a, m) x := by
      change A'.root (c.rootEquiv a) (L x) + (m : ℚ) = A.root a x + (m : ℚ)
      rw [hval]
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨z, hz, hz'⟩ ⟨a', m⟩ hp
      have hzx : z = x := e.injective hz'
      subst z
      obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a'
      change 0 < A'.wallValue (c.rootEquiv a, m) (e x)
      rw [hw]
      exact hz _ (by
        change 0 < A'.wallValue (c.rootEquiv a, m) (e p) at hp
        rwa [hw] at hp)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rintro ⟨a, m⟩ ha
      change 0 < A.wallValue (a, m) x
      rw [← hw]
      apply hx (c.rootEquiv a, m)
      change 0 < A'.wallValue (c.rootEquiv a, m) (e p)
      rwa [hw]

end CentralApartment

section IwahoriChart

open AlgebraicGeometry CategoryTheory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers IntegralPoints integerAlgebra TorusValues)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold PinnedWallSigns)
open Specs.ExceptionalIwahoriCongruence (cellValue integralRing iwahoriSubgroup)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalIwahoriImageComparison (markedBorelReduction)
open ValuativeRel
open private normalizedValuation_le_one normalizedValuation_lt_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

open private iwahoriValuationChart positivePower_le_one positivePower_lt_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

attribute [local instance] integerAlgebra

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem rootChartCoordinates_injective
    (C : LocalRootChart (j := j) A p)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos) :
    Function.Injective (fun z : C.chart.torus × (∀ a, C.parameter a) =>
      C.chart.coordinates z.1 z.2) := by
  intro x y h
  refine Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) h)) (funext fun a => ?_)
  have nonzero (z : Integers.{u}ˣ) : algebraMap Integers.{u} K (z : Integers.{u}) ≠ 0 :=
    (Units.map (algebraMap Integers.{u} K).toMonoidHom z).ne_zero
  rcases covers a with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hneg := congrArg (fun z => z.1 l) h
    exact (C.chart.negMap l).injective (mul_left_cancel₀ (nonzero _) hneg)
  · have hpos := congrArg (fun z => z.2.2 l) h
    exact (C.chart.posMap l).injective (mul_left_cancel₀ (nonzero _) hpos)

private theorem valuation_unit_iff (x : K) :
    normalizedValuation K x = 1 ↔ valuation K x = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K x) = 1 ↔ valuation K x = 1
  rw [← map_one e]
  exact e.strictMono.injective.eq_iff

private theorem integerUnit_value (z : Integers.{u}ˣ) :
  normalizedValuation K (algebraMap Integers.{u} K z) = 1 := by
  let v := normalizedValuation K
  have hle (a : Integers.{u}) : v (algebraMap Integers.{u} K a) ≤ 1 :=
    (v.mem_valuationSubring_iff _).mp (intCast_mem v.valuationSubring.toSubring a.down)
  refine le_antisymm (hle _) ?_
  have hprod : v (algebraMap Integers.{u} K (z : Integers.{u})) *
      v (algebraMap Integers.{u} K ((z⁻¹ : Integers.{u}ˣ) : Integers.{u})) = 1 := by
    rw [← map_mul, ← map_mul, show (z : Integers.{u}) * ((z⁻¹ : Integers.{u}ˣ) : Integers.{u}) = 1 from z.val_inv]
    simp
  simpa only [hprod, mul_one] using
    mul_le_mul_of_nonneg_left (hle ((z⁻¹ : Integers.{u}ˣ) : Integers.{u})) (show (0 : ℤᵐ⁰) ≤ v (algebraMap Integers.{u} K z) from bot_le)

/-- The initial thresholds in the rational root chart are obtained directly
from the reduction of the marked model into the positive Borel. -/
theorem iwahori_basePoint_chart
    (P : LocalIwahori j Wf) (C : LocalRootChart (j := j) A p)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos)
    (negDepth : ∀ l, threshold (A.root (C.chart.neg l) p) = 1)
    (posDepth : ∀ l, threshold (A.root (C.chart.pos l) p) = 0)
    (e : J → ℤ) (he : ∀ a, 0 < e a)
    (hvn : ∀ l x, normalizedValuation K (C.chart.negMap l x) =
      C.value (C.chart.neg l) x ^ e (C.chart.neg l))
    (hvp : ∀ l x, normalizedValuation K (C.chart.posMap l x) =
      C.value (C.chart.pos l) x ^ e (C.chart.pos l)) (g : G) :
    g ∈ P.iwahori ↔ C.atPoint p g := by
  let F := P.residueFibre
  let O := (valuation K).valuationSubring
  let k := IsLocalRing.ResidueField O
  let H := j.range
  let g' : H := ⟨j g, ⟨g, rfl⟩⟩
  obtain ⟨B, hB, hchart⟩ := ExceptionalIwahoriCongruence.markedFibreBorel M.toIntegralMarking k
    F.line F.realization F.groupIso F.torusIso F.coordinate F.torus_comm
    (fun i x => F.root_eval i (CommAlgCat.of k k) x)
    C.negative C.positive C.positive_enumerates
  have hB' : (P.residueBorel : Set (FieldPoints M k)) = ↑B := P.borel_eq.trans hB.symm
  have hRaw := iwahoriValuationChart M.toIntegralMarking H (valuation K)
    C.negative C.positive C.negative_enumerates C.positive_enumerates P.residueBorel
    (hB'.trans hchart) g'
  change g ∈ P.iwahori ↔ _ at hRaw
  have hinj := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates).1 (integralRing K)
  have hcoord := rootChartCoordinates_injective C covers
  have hneg (t : C.chart.torus) (x : ∀ a, C.parameter a) (l : Fin C.negative.length) :
      valuation K ((C.chart.coordinates t x).1 l) < 1 ↔
        C.value (C.chart.neg l) (x (C.chart.neg l)) ≤
          WithZero.exp (-threshold (A.root (C.chart.neg l) p)) := by
    rw [← normalizedValuation_lt_one, negDepth]
    change normalizedValuation K (algebraMap Integers.{u} K (C.chart.negUnit l) *
      C.chart.negMap l (x (C.chart.neg l))) < 1 ↔ _
    rw [map_mul, integerUnit_value, one_mul, hvn]
    exact positivePower_lt_one (he _)
  have hpos (t : C.chart.torus) (x : ∀ a, C.parameter a) (l : Fin C.positive.length) :
      valuation K ((C.chart.coordinates t x).2.2 l) ≤ 1 ↔
        C.value (C.chart.pos l) (x (C.chart.pos l)) ≤
          WithZero.exp (-threshold (A.root (C.chart.pos l) p)) := by
    rw [← normalizedValuation_le_one, posDepth, neg_zero, WithZero.exp_zero]
    change normalizedValuation K (algebraMap Integers.{u} K (C.chart.posUnit l) *
      C.chart.posMap l (x (C.chart.pos l))) ≤ 1 ↔ _
    rw [map_mul, integerUnit_value, one_mul, hvp]
    exact positivePower_le_one (he _)
  rw [hRaw]
  constructor
  · rintro ⟨z, ⟨hz, ht, hn, hp⟩, _⟩
    obtain ⟨t, x, rfl⟩ := (C.rational _).mp (hz.symm ▸ g'.property)
    refine ⟨(t, x), ⟨hz, fun χ => (valuation_unit_iff _).mpr (ht χ), ?_⟩, ?_⟩
    · intro a
      rcases covers a with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact (hneg t x l).mp (hn l)
      · exact (hpos t x l).mp (hp l)
    · intro w hw
      exact hcoord (hinj (hw.1.trans hz.symm))
  · rintro ⟨⟨t, x⟩, ⟨hz, ht, hx⟩, _⟩
    refine ⟨C.chart.coordinates t x,
      ⟨hz, fun χ => (valuation_unit_iff _).mp (ht χ),
        fun l => (hneg t x l).mpr (hx _), fun l => (hpos t x l).mpr (hx _)⟩, ?_⟩
    intro w hw
    exact hinj (hw.1.trans hz.symm)


private theorem stepThreshold_eq_threshold (d : ℕ) (e k r : ℤ) (he : 0 < e) :
    Specs.ExceptionalIwahoriCongruence.stepThreshold ((d : ℤ) * e) (k * r) =
      threshold ((k : ℚ) * (r : ℚ) / ((d : ℚ) * (e : ℚ))) := by
  let m : ℤ := (d : ℤ) * e
  have hm : 0 ≤ m := mul_nonneg (Int.natCast_nonneg _) he.le
  unfold Specs.ExceptionalIwahoriCongruence.stepThreshold threshold
  congr 1
  change -(k * r) / m = ⌊-((k : ℚ) * (r : ℚ) / ((d : ℚ) * (e : ℚ)))⌋
  rw [← neg_div, ← Int.cast_mul, ← Int.cast_neg, ← Int.cast_natCast d, ← Int.cast_mul]
  change -(k * r) / m = ⌊((-(k * r) : ℤ) : ℚ) / (m : ℚ)⌋
  have h := Rat.floor_intCast_div_natCast (-(k * r)) m.toNat
  rw [← Int.cast_natCast (R := ℚ) m.toNat, Int.toNat_of_nonneg hm] at h
  exact h.symm

open Specs.ExceptionalIwahoriCongruence (markedScaledReduction integralRingMap changeRing residueHom residueRing)
open Specs.IntegralSemisimpleModel (cocharacter torusPoint)
open private mem_markedTorus_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

/-- Scaling an ordered rational chart in the integral model imposes its
normalized root inequalities, also when the absolute slots use integral units. -/
theorem scaledReduction_atPoint (C : LocalRootChart (j := j) A p)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos)
    {L : Type u} [Field L] (f : K →+* L) (v : Valuation L ℤᵐ⁰)
    (unit : ∀ z, v (f z) = 1 ↔ normalizedValuation K z = 1)
    (e : J → ℤ) (he : ∀ a, 0 < e a)
    (hvn : ∀ l z, v (f (C.chart.negMap l z)) =
      C.value (C.chart.neg l) z ^ e (C.chart.neg l))
    (hvp : ∀ l z, v (f (C.chart.posMap l z)) =
      C.value (C.chart.pos l) z ^ e (C.chart.pos l))
    (y : D.Y) (ξ π : Lˣ) (d : ℕ) (hd : 0 < d) (hpow : (ξ : L) ^ d = π)
    (r : ℤ) (hπ : v (π : L) = WithZero.exp (-r))
    (k : J → ℤ)
    (hn : ∀ l : Fin C.negative.length,
      D.datum.toLinearMap (D.datum.root C.negative[l]) y = k (C.chart.neg l))
    (hp : ∀ l : Fin C.positive.length,
      D.datum.toLinearMap (D.datum.root C.positive[l]) y = k (C.chart.pos l))
    (x : V) (hx : ∀ a, A.root a x = (k a : ℚ) * (r : ℚ) / ((d : ℚ) * (e a : ℚ)))
    (g : G) :
    (⟨j g, ⟨g, rfl⟩⟩ : j.range) ∈ markedScaledReduction M.toIntegralMarking j.range f v y ξ
      ↔ C.atPoint x g := by
  let H := j.range
  let g' : H := ⟨j g, ⟨g, rfl⟩⟩
  have raw := ExceptionalIwahoriCongruence.valuedScaledChart M.toIntegralMarking f v
    C.negative C.positive C.negative_enumerates C.positive_enumerates y ξ (j g)
  let O := integralRing v.valuationSubring
  let t := torusPoint D (integralRing L) (cocharacter D y (integralRing L) ξ) ≫ M.torus.hom.hom
  have hmem : g' ∈ markedScaledReduction M.toIntegralMarking H f v y ξ ↔
      ∃ q : IntegralPoints M.group O,
        changeRing (integralRingMap v.valuationSubring.subtype) q =
          MulAut.conj t (changeRing (integralRingMap f) (j g)) ∧
        ∃ c : TorusValues D (residueRing O),
          changeRing (residueHom O) q = cellValue M.toIntegralMarking _ C.negative C.positive (0, c, 0) := by
    apply exists_congr
    intro q
    exact and_comm.trans (and_congr_right' (mem_markedTorus_iff M.toIntegralMarking _
      C.negative C.positive _))
  have pred := hmem.trans raw
  have hinj := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking
    C.negative C.positive C.negative_enumerates C.positive_enumerates).1 (integralRing K)
  have hcoord := rootChartCoordinates_injective C covers
  have hunit (z : Integers.{u}ˣ) : v (f (algebraMap Integers.{u} K z)) = 1 :=
    (unit _).2 (integerUnit_value z)
  have hn' (t : C.chart.torus) (z : ∀ a, C.parameter a) (l : Fin C.negative.length) :
      v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root C.negative[l]) y) : L) *
        f ((C.chart.coordinates t z).1 l)) < 1 ↔
      C.value (C.chart.neg l) (z (C.chart.neg l)) ≤
        WithZero.exp (-threshold (A.root (C.chart.neg l) x)) := by
    rw [hn, hx, ← stepThreshold_eq_threshold d _ _ _ (he _)]
    change v ((↑(ξ ^ k (C.chart.neg l)) : L) *
      f (algebraMap Integers.{u} K (C.chart.negUnit l) * C.chart.negMap l (z (C.chart.neg l)))) < 1 ↔ _
    simp only [map_mul, hunit, one_mul]
    simpa only [RingHom.coe_comp, Function.comp_apply, map_mul] using
      (ExceptionalIwahoriCongruence.scaledParameterThreshold (f.comp (C.chart.negMap l)) _
        v _ (he _) (hvn l) ξ π d hd hpow r _ hπ (z (C.chart.neg l)))
  have hp' (t : C.chart.torus) (z : ∀ a, C.parameter a) (l : Fin C.positive.length) :
      v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root C.positive[l]) y) : L) *
        f ((C.chart.coordinates t z).2.2 l)) < 1 ↔
      C.value (C.chart.pos l) (z (C.chart.pos l)) ≤
        WithZero.exp (-threshold (A.root (C.chart.pos l) x)) := by
    rw [hp, hx, ← stepThreshold_eq_threshold d _ _ _ (he _)]
    change v ((↑(ξ ^ k (C.chart.pos l)) : L) *
      f (algebraMap Integers.{u} K (C.chart.posUnit l) * C.chart.posMap l (z (C.chart.pos l)))) < 1 ↔ _
    simp only [map_mul, hunit, one_mul]
    simpa only [RingHom.coe_comp, Function.comp_apply, map_mul] using
      (ExceptionalIwahoriCongruence.scaledParameterThreshold (f.comp (C.chart.posMap l)) _
        v _ (he _) (hvp l) ξ π d hd hpow r _ hπ (z (C.chart.pos l)))
  change g' ∈ _ ↔ _
  rw [pred]
  constructor
  · rintro ⟨coords, ⟨hz, ht, hneg, hpos⟩, _⟩
    have h : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive coords ∈ j.range := by
      rw [hz]
      exact ⟨g, rfl⟩
    obtain ⟨t, z, rfl⟩ := (C.rational coords).mp h
    refine ⟨(t, z), ⟨hz, fun χ => (unit _).mp (ht χ), ?_⟩, ?_⟩
    · intro a
      rcases covers a with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact (hn' t z l).mp (hneg l)
      · exact (hp' t z l).mp (hpos l)
    · exact fun z' hz' => hcoord (hinj (hz'.1.trans hz.symm))
  · rintro ⟨⟨t, z⟩, ⟨hz, ht, hroot⟩, _⟩
    exact ⟨C.chart.coordinates t z, ⟨hz, fun χ => (unit _).mpr (ht χ),
      fun l => (hn' t z l).mpr (hroot _), fun l => (hp' t z l).mpr (hroot _)⟩,
      fun z' hz' => hinj (hz'.1.trans hz.symm)⟩

end IwahoriChart


section Split

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers IntegralAlgebra IntegralPoints integerAlgebra
  integralSpec integralPointFunctor)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots PinnedWallSigns AlcoveGeometry threshold)
open Specs.ExceptionalIwahoriCongruence (CellValues integralRing cellValue markedPointTopology
  RationalRootChart changeRingHom iwahoriSubgroup)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalIwahoriImageComparison (markedGroundPoint MarkedLocalNormalizer
  integralUnitTorus)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer)
open Specs.OrderedRootProducts (Enumerates)
open private simpleWeylWords from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private rationalCocharacterAction cocharacterLinearAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private corootLattice_le_coweightLattice from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

attribute [local instance] integerAlgebra

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}

private theorem indexSlots_bijective (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) :
    Function.Bijective
      (Sum.elim (fun l : Fin negative.length => negative[l])
        (fun l : Fin positive.length => positive[l])) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro (l | l) (m | m) h
    · exact congrArg Sum.inl (Fin.ext (hn.1.eq_of_getElem_eq l.isLt m.isLt h))
    · change negative[l] = positive[m] at h
      exact False.elim (((hn.2 (negative[l])).mp (List.getElem_mem l.isLt))
        (h.symm ▸ (hp.2 (positive[m])).mp (List.getElem_mem m.isLt)))
    · change positive[l] = negative[m] at h
      exact False.elim (((hn.2 (negative[m])).mp (List.getElem_mem m.isLt))
        (h ▸ (hp.2 (positive[l])).mp (List.getElem_mem l.isLt)))
    · exact congrArg Sum.inr (Fin.ext (hp.1.eq_of_getElem_eq l.isLt m.isLt h))
  · intro i
    by_cases hi : D.base.IsPos i
    · obtain ⟨l, hl, he⟩ := List.mem_iff_getElem.mp ((hp.2 i).mpr hi)
      exact ⟨Sum.inr ⟨l, hl⟩, he⟩
    · obtain ⟨l, hl, he⟩ := List.mem_iff_getElem.mp ((hn.2 i).mpr hi)
      exact ⟨Sum.inl ⟨l, hl⟩, he⟩

private noncomputable def splitRootChart
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i})
    (p : ℚ ⊗[ℤ] D.Y)
    (hs : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos) :
    LocalRootChart (M := M) (j := identityPoints M K) (ApartmentRoots.split D.datum ℚ) p where
  direction := id
  negative := negative
  positive := positive
  negative_enumerates := hn
  positive_enumerates := hp
  parameter := fun _ => K
  parameterField := fun _ => inferInstance
  value := fun _ => normalizedValuation K
  chart :=
    { torus := Set.univ
      neg := fun l => negative[l]
      pos := fun l => positive[l]
      negMap := fun _ => RingHom.id K
      posMap := fun _ => RingHom.id K
      negUnit := fun _ => 1
      posUnit := fun _ => 1 }
  neg_slots := fun _ => rfl
  pos_slots := fun _ => rfl
  rational := by
    intro z
    let e := Equiv.ofBijective _ (indexSlots_bijective negative positive hn hp)
    let x := Sum.elim z.1 z.2.2 ∘ e.symm
    refine ⟨fun _ => ⟨⟨z.2.1, Set.mem_univ _⟩, x, ?_⟩,
      fun _ => ⟨cellValue M.toIntegralMarking (integralRing K) negative positive z, rfl⟩⟩
    refine Prod.ext (funext fun l => ?_) (Prod.ext rfl (funext fun l => ?_))
    · change algebraMap Integers.{u} K 1 * x (e (Sum.inl l)) = z.1 l
      simp [x]
    · change algebraMap Integers.{u} K 1 * x (e (Sum.inr l)) = z.2.2 l
      simp [x]
  signs := by
    simpa only [id_eq, exists_eq_left] using hs

private theorem splitWeylReflection (D : BasedRootDatum.{u}) (i : D.I) :
    rationalCocharacterAction D (RootPairing.Equiv.reflection D.datum i) =
      (ApartmentRoots.split D.datum ℚ).linearReflection i := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro q y
  change (q ⊗ₜ[ℤ] ((RootPairing.Equiv.reflection D.datum i).coweightEquiv.symm y)) =
    (ApartmentRoots.split D.datum ℚ).linearReflection i (q ⊗ₜ[ℤ] y)
  rw [RootPairing.Equiv.reflection_coweightEquiv]
  change q ⊗ₜ[ℤ] (Module.reflection _).symm y =
    Module.reflection _ (q ⊗ₜ[ℤ] y)
  rw [Module.reflection_symm, Module.reflection_apply, Module.reflection_apply]
  rw [TensorProduct.tmul_sub]
  congr 1
  change q ⊗ₜ[ℤ] (D.datum.root' i y • D.datum.coroot i) =
    RootData.extendFunctional ℚ (D.datum.root' i) (q ⊗ₜ[ℤ] y) •
      ((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i)
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
  simp only [RootData.extendFunctional, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul]
  change _ = (((D.datum.root' i y) • q) * 1) ⊗ₜ[ℤ] _
  rw [mul_one]

private theorem splitWeylLinear_range (D : BasedRootDatum.{u}) :
    ((rationalCocharacterAction D).comp D.datum.weylGroup.subtype).range =
      (ApartmentRoots.split D.datum ℚ).linearWeylGroup := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [RootPairing.weylGroup, MonoidHom.map_closure, ← Set.range_comp]
  have he : rationalCocharacterAction D ∘ RootPairing.Equiv.reflection D.datum =
      (ApartmentRoots.split D.datum ℚ).linearReflection :=
    funext (splitWeylReflection D)
  rw [he]
  rfl

private theorem normalizerAction_range
    {G W : Type u} [Group G] [Group W] {j : G →* FieldPoints M K}
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (N : MarkedLocalNormalizer K j W) (L : W →* (V ≃ₗ[ℚ] V)) (z : N.torus → V)
    (a : N.normalizer →* (V ≃ᵃ[ℚ] V))
    (ha : ∀ n x, a n x = L (N.label n) x + z (N.torusPart n)) :
    ∀ f : V ≃ᵃ[ℚ] V, f ∈ a.range ↔ f 0 ∈ Set.range z ∧ f.linear ∈ L.range := by
  have hzero (n : N.normalizer) : a n 0 = z (N.torusPart n) := by rw [ha, map_zero, zero_add]
  have eval (g : V ≃ᵃ[ℚ] V) (x : V) : g x = g.linear x + g 0 := by
    simpa using g.map_vadd (0 : V) x
  have hlinear (n : N.normalizer) : (a n).linear = L (N.label n) := by
    ext x
    exact add_right_cancel ((eval (a n) x).symm.trans ((ha n x).trans
      (congrArg (L (N.label n) x + ·) (hzero n).symm)))
  intro f
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨N.torusPart n, (hzero n).symm⟩, ⟨N.label n, (hlinear n).symm⟩⟩
  · rintro ⟨⟨t, ht⟩, ⟨w, hw⟩⟩
    let nt : N.normalizer := ⟨t, N.torus_le t.property⟩
    let n := nt * N.lift w
    have hnt : N.label nt = 1 := (N.labelKernel nt).mpr t.property
    have hw' : N.label n = w := by simp [n, hnt, N.lift_label]
    have ht' : N.torusPart n = t := by
      apply Subtype.ext
      change ((n * (N.lift (N.label n))⁻¹ : N.normalizer) : G) = (t : G)
      rw [hw']
      exact congrArg Subtype.val (mul_inv_cancel_right nt (N.lift w))
    refine ⟨n, AffineEquiv.ext fun x => ?_⟩
    rw [ha, hw', ht', eval f, ← hw]
    exact congrArg (L w x + ·) ht

private theorem splitCompactOpen (P : LocalIwahori (j := identityPoints M K) D.datum.weylGroup)
    (B : IntegralAlgebra.{u}) [ft : Algebra.FiniteType Integers.{u} B]
    (e : integralSpec.obj (.op B) ≅ M.group.X) :
    letI : TopologicalSpace (FieldPoints M K) := TopologicalSpace.induced
      (identityPoints M K) (markedPointTopology B e K)
    IsCompact (P.iwahori : Set (FieldPoints M K)) ∧ IsOpen (P.iwahori : Set (FieldPoints M K)) := by
  have htop : TopologicalSpace.induced (identityPoints M K) (markedPointTopology B e K) =
      markedPointTopology B e K := @induced_id _ (markedPointTopology B e K)
  have heq : integerAlgebra B = B.algebra := by
    apply Algebra.algebra_ext
    rintro ⟨z⟩
    exact (map_intCast (integerAlgebra B).algebraMap z).trans
      (map_intCast B.algebra.algebraMap z).symm
  let _ : @Algebra.FiniteType Integers.{u} B _ _ B.algebra := heq ▸ ft
  have h := ExceptionalIwahoriCongruence.compactOpenLocalModel M.toIntegralMarking B e K P.residueBorel
  exact (congrArg (fun t => @IsCompact _ t (P.iwahori : Set (FieldPoints M K)) ∧
    @IsOpen _ t (P.iwahori : Set (FieldPoints M K))) htop).mpr ⟨h.1, h.2.1⟩

/-- The marked split normalizer and its actual affine image, with the
positive Borel reduction and chart on the cocharacter apartment. -/
private theorem splitLocalComparisonWithSimpleWords
    (C : MarkedFibre M K) {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (p : ℚ ⊗[ℤ] D.Y) (adjoint : Bool)
    (hs : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos)
    (geom : AlcoveGeometry (ApartmentRoots.split D.datum ℚ) p)
    (hsc : adjoint = false → D.datum.corootSpan ℤ = ⊤)
    (had : adjoint = true → D.datum.rootSpan ℤ = ⊤) :
    ∃ P : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p, SplitPointComparison C adjoint P ∧
        (∀ g, g ∈ P.I ↔ P.chart.atPoint p g) ∧
        ∀ w, ∀ a ∈ P.localIwahori.normalizer.word w, a ∈ D.base.support := by
  classical
  let A := ApartmentRoots.split D.datum ℚ
  let _ := D.finiteRoots
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := D.reduced
  obtain ⟨word, hword, hprod⟩ := simpleWeylWords D
  obtain ⟨P, F, hN, hf, hPword, hv, _⟩ :=
    ExceptionalLocalRootCoordinates.splitLocalIwahori C b word hword hprod
  let N := P.normalizer
  obtain ⟨a, hker, ha, _⟩ := ExceptionalLocalRootCoordinates.markedNormalizerApartment
    F b (identityPoints M K) N (MonoidHom.id _) Function.injective_id hf (1 : ℚˣ)
  have hform : ∀ n x, a n x =
      (rationalCocharacterAction D).comp D.datum.weylGroup.subtype (N.label n) x +
        ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) := ha
  have htors : Set.range (fun t : N.torus => (1 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      Set.range (fun y : D.Y => (1 : ℚ) ⊗ₜ[ℤ] y) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(N.translation t).toAdd, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨t, ht⟩ := hv (Multiplicative.ofAdd y)
      exact ⟨t, congrArg (fun v : Multiplicative D.Y => (1 : ℚ) ⊗ₜ[ℤ] v.toAdd) ht⟩
  have htrans : Set.range (fun t : N.torus => (1 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      (if adjoint then (A.coweightLattice : Set _) else (A.corootLattice : Set _)) := by
    rw [htors]
    obtain ⟨hc, hp⟩ :=
      ExceptionalAffineRootSystems.splitIntegralCocharacterImages (K := ℚ) D.datum D.base
    cases adjoint
    · have hl := hc
      rw [show Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ from hsc rfl,
        Submodule.top_coe, Set.image_univ] at hl
      exact hl.symm
    · exact (hp (had rfl)).symm
  have hrange : a.range = if adjoint then A.extendedAffineWeylGroup else A.affineWeylGroup := by
    ext f
    rw [normalizerAction_range N ((rationalCocharacterAction D).comp D.datum.weylGroup.subtype)
      (fun t => (1 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) a hform, splitWeylLinear_range, htrans]
    obtain ⟨_, h₁, h₂⟩ := ExceptionalAffineRootSystems.affineGroupNormalForms A
    cases adjoint
    · exact (h₁ f).symm
    · exact (h₂ f).symm
  have hall : A.affineWeylGroup ≤ a.range := by
    rw [hrange]
    cases adjoint
    · exact le_rfl
    · obtain ⟨_, h₁, h₂⟩ := ExceptionalAffineRootSystems.affineGroupNormalForms A
      intro f hf
      obtain ⟨ht, hl⟩ := (h₁ f).1 hf
      exact (h₂ f).2 ⟨corootLattice_le_coweightLattice A ht, hl⟩
  choose lift hlift using fun w : A.affineWeylGroup => hall w.property
  obtain ⟨negative, positive, hn, hp⟩ := rootOrderings_exist D
  let Q : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup) A p :=
    { point_injective := Function.injective_id
      localIwahori := P
      compact_open := splitCompactOpen P
      chart := splitRootChart negative positive hn hp p hs
      geometry := geom
      coxeter := geom.coxeter.some
      affine := a
      kernel := hker
      lift := lift
      lift_label := hlift }
  refine ⟨Q, ⟨hN, ⟨Function.injective_id, F, hf, ?_⟩, rfl, fun _ => rfl, fun _ => rfl,
    fun i => ⟨RingEquiv.refl K, fun _ => rfl, ?_, ?_⟩, ha, htrans, hrange⟩, ?_, ?_⟩
  · intro w
    change ((N.word w).map _).prod = w
    rw [hPword]
    exact hprod w
  · intro l he x
    cases he
    rfl
  · intro l he x
    cases he
    rfl
  · have covers (i : D.I) : i ∈ Set.range Q.chart.chart.neg ∪ Set.range Q.chart.chart.pos := by
      obtain ⟨l, hl⟩ := (indexSlots_bijective negative positive hn hp).surjective i
      cases l with
      | inl l => exact Or.inl ⟨l, hl⟩
      | inr l => exact Or.inr ⟨l, hl⟩
    have hneg (l : Fin negative.length) : threshold (A.root negative[l] p) = 1 :=
      hs.threshold_negative _ ((hn.2 _).mp (List.getElem_mem l.isLt))
    have hpos (l : Fin positive.length) : threshold (A.root positive[l] p) = 0 :=
      hs.threshold_positive _ ((hp.2 _).mp (List.getElem_mem l.isLt))
    exact iwahori_basePoint_chart P Q.chart covers hneg hpos (fun _ => 1) (fun _ => Int.one_pos)
      (fun _ z => (zpow_one (normalizedValuation K z)).symm)
      (fun _ z => (zpow_one (normalizedValuation K z)).symm)

  · intro w a ha
    change a ∈ N.word w at ha
    rw [hPword] at ha
    exact hword w a ha

theorem splitLocalComparison
    (C : MarkedFibre M K) {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (p : ℚ ⊗[ℤ] D.Y) (adjoint : Bool)
    (hs : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos)
    (geom : AlcoveGeometry (ApartmentRoots.split D.datum ℚ) p)
    (hsc : adjoint = false → D.datum.corootSpan ℤ = ⊤)
    (had : adjoint = true → D.datum.rootSpan ℤ = ⊤) :
    ∃ P : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p, SplitPointComparison C adjoint P ∧
        ∀ g, g ∈ P.I ↔ P.chart.atPoint p g := by
  obtain ⟨P, hP, hbase, _⟩ := splitLocalComparisonWithSimpleWords C b p adjoint hs geom hsc had
  exact ⟨P, hP, hbase⟩

/-- For a split exceptional marking in either isogeny form the initial
alcove, absolute point chart, and marked normalizer comparison exist
over the given nonarchimedean local field. -/
theorem splitExceptionalLocalData (M : Model D)
    (n : ℕ) (b : Fin n ≃ D.base.support) (adjoint : Bool)
    (numbering : ExceptionalNumbering D n b)
    (hsc : adjoint = false → D.datum.corootSpan ℤ = ⊤)
    (had : adjoint = true → D.datum.rootSpan ℤ = ⊤) :
    ∃ (p : ℚ ⊗[ℤ] D.Y) (C : MarkedFibre M K)
      (Q : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
        (ApartmentRoots.split D.datum ℚ) p),
      SplitPointComparison C adjoint Q ∧ ∀ g, g ∈ Q.I ↔ Q.chart.atPoint p g := by
  classical
  let _ := D.finiteRoots
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := D.reduced
  obtain ⟨p, _, _, _, hsigns, geom⟩ :=
    ExceptionalAffineRootSystems.splitPinnedAlcoveGeometry (K := ℚ) D.datum D.base b numbering.1
  obtain ⟨C⟩ := ExceptionalMarkedRootDescent.markedFibreExists M K
  let B := Module.Free.chooseBasis ℤ D.Y
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
  obtain ⟨Q, hQ⟩ := splitLocalComparison C B p adjoint hsigns geom hsc had
  exact ⟨p, C, Q, hQ⟩

end Split

section SplitWalls

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers IntegralPoints integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint markedWeylWord markedWall wallMatrix
  weylWordPerm)
open Specs.IntegralRootRelations (upper)
open private weylWord_index from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private simpleWeylWords from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private rationalCocharacterAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

attribute [local instance] integerAlgebra

private theorem simpleWeylTransport (D : BasedRootDatum.{u}) (i : D.I) :
    ∃ a : D.base.support, ∃ w : D.datum.weylGroup, w.val.indexEquiv a.val = i := by
  let _ := D.finiteRoots
  let _ := D.reduced
  let pred (i : D.I) := ∃ a : D.base.support, ∃ w : D.datum.weylGroup, w.val.indexEquiv a.val = i
  have hs (i j : D.I) (hi : pred i) : pred (D.datum.reflectionPerm j i) := by
    obtain ⟨a, w, h⟩ := hi
    exact ⟨a, RootPairing.weylGroup.ofIdx D.datum j * w, by
      change D.datum.reflectionPerm j (w.val.indexEquiv a.val) = _
      rw [h]⟩
  exact D.base.induction_reflect i (fun i hi => hs i i hi)
    (fun i hi => ⟨⟨i, hi⟩, 1, rfl⟩) (fun i j hi _ => hs i j hi)

private theorem conjugateWeylReflection (D : BasedRootDatum.{u})
    (w : D.datum.weylGroup) (a : D.I) :
    w * RootPairing.weylGroup.ofIdx D.datum a * w⁻¹ =
      RootPairing.weylGroup.ofIdx D.datum (w.val.indexEquiv a) := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.datum
  change RootPairing.Equiv.weightHom D.datum
    (w.val * RootPairing.Equiv.reflection D.datum a * w.val⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  apply LinearEquiv.ext
  intro x
  change w.val.weightEquiv (D.datum.reflection a (w.val.weightEquiv.symm x)) =
    D.datum.reflection (w.val.indexEquiv a) x
  rw [RootPairing.Equiv.weightEquiv_reflection, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- Each integral affine wall of the marked split model has the lift in the
corresponding transported rank-one subgroup. The parameter's value and the
action of the actual lift are computed in the same cocharacter apartment. -/
theorem splitAffineWallLift
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D} (F₀ : MarkedFibre M K)
    {p : ℚ ⊗[ℤ] D.Y} {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    {adjoint : Bool} (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p) (hc : SplitPointComparison F₀ adjoint C)
    (i : D.I) (j : ℤ) :
    let R := integralRing K
    ∃ (a : D.base.support) (word : List D.I) (t : Kˣ) (ε : Integers.{u}ˣ)
      (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* FieldPoints M K) (n : C.N),
      (∀ q ∈ word, q ∈ D.base.support) ∧
      weylWordPerm word a.val = i ∧
      (∀ U, ρ U = markedWeylWord M.toIntegralMarking R word *
        (show IntegralPoints M.group R from (M.rankOne a.val).app R U) * (markedWeylWord M.toIntegralMarking R word)⁻¹) ∧
      (∀ x : K, ρ (upper x) =
        markedRootPoint M.toIntegralMarking R i (algebraMap Integers.{u} K (ε : Integers.{u}) * x)) ∧
      normalizedValuation K (t : K) = WithZero.exp (-j) ∧
      (n : FieldPoints M K) = ρ (wallMatrix t) ∧
      C.affine n = (ApartmentRoots.split D.datum ℚ).wallReflection i j := by
  classical
  let R := integralRing K
  let A := ApartmentRoots.split D.datum ℚ
  let N := C.localIwahori.normalizer
  obtain ⟨_, ⟨hinj, F, hpoints, _⟩, _, _, _, _, haffine, _, _⟩ := hc
  obtain ⟨a, w, hwi⟩ := simpleWeylTransport D i
  obtain ⟨words, hwords, hprod⟩ := simpleWeylWords D
  let l := words w
  let m := markedWeylWord M.toIntegralMarking R l
  have hword (q : D.I) (hq : q ∈ l) : q ∈ D.base.support := hwords w q hq
  have hlabel : ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod) = w := hprod w
  have hi : weylWordPerm l a.val = i := by rw [weylWord_index, hlabel, hwi]
  obtain ⟨z, hz⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization K).1 (WithZero.exp (-j))
  have ht : normalizedValuation K z = WithZero.exp (-j) := hz
  have hne : z ≠ 0 := by
    intro h
    exact WithZero.exp_ne_zero (by simpa only [h, map_zero] using ht.symm)
  let t := Units.mk0 z hne
  let ρ : Matrix.SpecialLinearGroup (Fin 2) K →* FieldPoints M K :=
    (MulAut.conj m).toMonoidHom.comp ((M.rankOne a.val).app R).hom
  have hρ (U : Matrix.SpecialLinearGroup (Fin 2) K) : ρ U =
      m * (show IntegralPoints M.group R from (M.rankOne a.val).app R U) * m⁻¹ := rfl
  obtain ⟨ε, hε⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M l a.val
  have hUpper (x : K) : ρ (upper x) = markedRootPoint M.toIntegralMarking R i
      (algebraMap Integers.{u} K (ε : Integers.{u}) * x) := by
    rw [hρ, M.rankOneUpper]
    exact (hε R x).trans (by rw [hi])
  have hl : (RootPairing.weylGroup.ofIdx D.datum i) =
      w * (RootPairing.weylGroup.ofIdx D.datum a.val) * w⁻¹ := by
    rw [conjugateWeylReflection, hwi]
  let o : List (D.base.support × Kˣ) := [(a, t)]
  have hp (z : C.N) : ∃ m, F.point m = identityPoints M K z ∧
      F.label m = (MonoidHom.id _) (N.label z) := hpoints z
  obtain ⟨n, hn, hnl⟩ := ExceptionalLocalRootCoordinates.markedWallNormalizer F
    (identityPoints M K) N (MonoidHom.id _) hinj hp l hword o
    (RootPairing.weylGroup.ofIdx D.datum i)
    (by simpa [o, hlabel] using hl)
    (ρ (wallMatrix t)) (by
      simp only [o, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact hρ _)
  have hdis := (ExceptionalLocalRootCoordinates.markedWallDisplacements F b
    (identityPoints M K) N (MonoidHom.id _) hinj hp l hword).1 a t n
    (by simpa only [MonoidHom.id_apply, hlabel, hnl] using hl)
    (by rw [hn, hρ]; rfl)
  have hcoroot : w.val.coweightEquiv.symm (D.datum.coroot a.val) = D.datum.coroot i := by
    apply w.val.coweightEquiv.injective
    rw [LinearEquiv.apply_symm_apply, ← hwi]
    have h := RootPairing.Hom.coroot_coweightMap_apply D.datum D.datum
      (w.val.indexEquiv a.val) w.val.toHom
    change w.val.coweightEquiv (D.datum.coroot (w.val.indexEquiv a.val)) =
      D.datum.coroot (w.val.indexEquiv.symm (w.val.indexEquiv a.val)) at h
    rw [w.val.indexEquiv.symm_apply_apply] at h
    exact h.symm
  have hp' : normalizedValuation K (t : K) = WithZero.exp (-j) := ht
  have hz' : (N.translation (N.torusPart n)).toAdd = (-j) • D.datum.coroot i := by
    simpa only [hlabel, hp', WithZero.log_exp, map_zsmul, hcoroot] using hdis
  refine ⟨a, l, t, ε, ρ, n, hword, hi, hρ, hUpper, ht, hn, ?_⟩
  apply AffineEquiv.ext
  intro x
  rw [haffine, hnl, hz']
  have hf := (ExceptionalAffineRootSystems.affineGroupNormalForms A).1 i j x
  change rationalCocharacterAction D (RootPairing.Equiv.reflection D.datum i) x +
    ((1 : ℚ) ⊗ₜ[ℤ] ((-j) • D.datum.coroot i)) = A.wallReflection i j x
  rw [splitWeylReflection, hf, TensorProduct.tmul_smul]
  change x - A.root i x • A.coroot i + (-j) • A.coroot i =
    x - (A.root i x + (j : ℚ)) • A.coroot i
  rw [add_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg, neg_smul, ← sub_eq_add_neg, sub_sub]

end SplitWalls

section Compositum

open ValuativeRel
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex)
open ExceptionalLocalRootCoordinates (ramifiedQuadratic)
open private normalizedValuation_algebraMap_exp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [vL : ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [ValuativeRel k] [ValuativeExtension F k] [FiniteDimensional F L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The valuation pulled back along an embedding over the local base is the
unique extended valuation on the finite source extension. -/
private theorem valuativeEmbedding (f : L →ₐ[F] k) (x y : L) :
    valuation k (f x) ≤ valuation k (f y) ↔ valuation L x ≤ valuation L y := by
  let w := (valuation k).comap f.toRingHom
  let s := ValuativeRel.ofValuation w
  have hs : @ValuativeExtension F L _ _ _ s _ := by
    constructor
    intro a b
    change valuation k (f (algebraMap F L a)) ≤ valuation k (f (algebraMap F L b)) ↔ a ≤ᵥ b
    rw [f.commutes, f.commutes, ← (valuation k).vle_iff_le, ValuativeExtension.vle_iff_vle]
  have hext : @ValuativeExtension F L _ _ _ vL _ := inferInstance
  obtain ⟨r, _, _, _, _, _, uniq⟩ := finiteExtension_localField (K := F) (L := L)
  have h : s = vL := (uniq s hs).trans (uniq vL hext).symm
  change @ValuativeRel.vle L _ s x y ↔ _
  rw [h]
  let _ := vL
  exact (valuation L).vle_iff_le

private theorem noRamifiedEmbedding [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (restrict : ∀ x : F, normalizedValuation L (algebraMap F L x) = normalizedValuation F x ^ 2)
    (hk : IsUnramifiedLocalExtension F k)
    (π : F) (hπ : normalizedValuation F π = WithZero.exp (-1))
    (ϖ : L) (hϖ : normalizedValuation L ϖ = WithZero.exp (-1))
    (f : L →ₐ[F] k) : False := by
  have hle (x y : L) : normalizedValuation k (f x) ≤ normalizedValuation k (f y) ↔
      normalizedValuation L x ≤ normalizedValuation L y := by
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
    let d := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
    change e (valuation k (f x)) ≤ e (valuation k (f y)) ↔
      d (valuation L x) ≤ d (valuation L y)
    exact e.strictMono.le_iff_le.trans ((valuativeEmbedding f x y).trans d.strictMono.le_iff_le.symm)
  have hsmall : normalizedValuation k (f ϖ) < 1 := by
    have h := (not_congr (hle 1 ϖ)).mpr (show ¬ normalizedValuation L 1 ≤ normalizedValuation L ϖ by
      rw [map_one, hϖ]
      exact not_le.mpr (WithZero.exp_lt_one_iff.mpr (by decide)))
    simpa only [not_le, map_one] using h
  have hlarge : WithZero.exp (-1 : ℤ) < normalizedValuation k (f ϖ) := by
    have h := (not_congr (hle ϖ (algebraMap F L π))).mpr (show ¬ _ by
      rw [restrict, hπ, hϖ, pow_two, ← WithZero.exp_add]
      exact not_le.mpr (WithZero.exp_lt_exp.mpr (by decide)))
    simpa only [not_le, f.commutes, hk π, hπ] using h
  have hs := (WithZero.lt_mul_exp_iff_le (x := normalizedValuation k (f ϖ))
    (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).mp (by
      rw [← WithZero.exp_add, show (-1 : ℤ) + 1 = 0 by decide, WithZero.exp_zero]
      exact hsmall)
  exact (not_le_of_gt hlarge) hs

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [ValuativeRel k] [ValuativeExtension F k] in
private theorem quadraticTensor_isField [FiniteDimensional F k] [IsGalois F L]
    (hd : Module.finrank F L = 2) (hno : IsEmpty (L →ₐ[F] k)) :
    IsField (L ⊗[F] k) := by
  apply IntermediateField.LinearDisjoint.isField_of_forall
  intro E _ _ f g
  let A := f.fieldRange
  let B := g.fieldRange
  let e : L ≃ₐ[F] A := AlgEquiv.ofInjectiveField f
  let d : k ≃ₐ[F] B := AlgEquiv.ofInjectiveField g
  let : FiniteDimensional F A := e.toLinearEquiv.finiteDimensional
  let : FiniteDimensional F B := d.toLinearEquiv.finiteDimensional
  let : IsGalois F A := IsGalois.of_algEquiv e
  change A.LinearDisjoint B
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  let : IsSimpleOrder (IntermediateField F A) := IntermediateField.isSimpleOrder_of_finrank_prime F A
    (by rw [← e.toLinearEquiv.finrank_eq, hd]; decide)
  let C := (A ⊓ B).restrict (inf_le_left : A ⊓ B ≤ A)
  rcases IsSimpleOrder.eq_bot_or_eq_top C with hc | hc
  · have h := congrArg (IntermediateField.lift (F := A)) hc
    simpa only [C, IntermediateField.lift_restrict, IntermediateField.lift_bot] using h
  · have h := congrArg (IntermediateField.lift (F := A)) hc
    have hab : A ⊓ B = A := by
      simpa only [C, IntermediateField.lift_restrict, IntermediateField.lift_top] using h
    exact (hno.false (d.symm.toAlgHom.comp
      ((IntermediateField.inclusion (show A ≤ B from inf_eq_left.mp hab)).comp e.toAlgHom))).elim

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option maxHeartbeats 650000 in
/-- A ramified quadratic diagram field and an unramified coefficient field
are linearly disjoint. The diagram and coefficient actions extend on the
two tensor factors, and base change from the diagram field is unramified. -/
theorem diagramCompositum_exists [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [FiniteDimensional F k] [IsGalois F L]
    (σ : Gal(L/F)) (hσ : σ ≠ 1) (hd : Module.finrank F L = 2)
    (hr : 1 < ramificationIndex F L) (hk : IsUnramifiedLocalExtension F k) :
    Nonempty (DiagramCompositum F L k σ) := by
  classical
  obtain ⟨_, hram, _⟩ := ramifiedQuadratic F L hd hr
  obtain ⟨π, hπ⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization F).1 (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization L).1 (WithZero.exp (-1))
  have hπ' : normalizedValuation F π = WithZero.exp (-1) := hπ
  have hϖ' : normalizedValuation L ϖ = WithZero.exp (-1) := hϖ
  let T := L ⊗[F] k
  let : Field T := (quadraticTensor_isField hd
    ⟨fun f => noRamifiedEmbedding hram hk π hπ' ϖ hϖ' f⟩).toField
  let swap := Algebra.TensorProduct.commRight F k L
  have hT : Module.finrank k T = 2 := by
    rw [← swap.toLinearEquiv.finrank_eq, Module.finrank_baseChange]
    exact hd
  let : FiniteDimensional k T := Module.finite_of_finrank_pos (by rw [hT]; decide)
  let automorphism (g : Gal(L/F)) : Gal(T/k) :=
    swap.symm.trans ((Algebra.TensorProduct.congr (S := k) (.refl : k ≃ₐ[k] k) g).trans swap)
  let ζ := automorphism σ
  have hζleft (x : L) : ζ (algebraMap L T x) = algebraMap L T (σ x) := by
    change swap ((Algebra.TensorProduct.congr (.refl : k ≃ₐ[k] k) σ)
      (swap.symm (x ⊗ₜ[F] (1 : k)))) = σ x ⊗ₜ[F] (1 : k)
    simp [swap]
  have hζ : ζ ≠ 1 := by
    intro h
    apply hσ
    ext x
    apply (algebraMap L T).injective
    rw [← hζleft, h]
    rfl
  have hcard : Nat.card Gal(T/k) = 2 := by
    have hle : Nat.card Gal(T/k) ≤ 2 := by
      rw [Nat.card_eq_fintype_card, ← hT]
      exact AlgEquiv.card_le
    have hlt : ¬ Nat.card Gal(T/k) ≤ 1 := fun h =>
      hζ ((Finite.card_le_one_iff_subsingleton.mp h).allEq ζ 1)
    omega
  let : IsGalois k T := IsGalois.of_card_aut_eq_finrank k T (hcard.trans hT.symm)
  let coeff : Gal(k/F) →* Gal(T/L) :=
    { toFun := fun g => Algebra.TensorProduct.congr (.refl : L ≃ₐ[L] L) g
      map_one' := by
        apply AlgEquiv.coe_toAlgHom_injective
        ext x
        simp
      map_mul' g h := by
        apply AlgEquiv.coe_toAlgHom_injective
        ext x
        simp }
  have hcoeff (g : Gal(k/F)) (x : k) :
      coeff g (algebraMap k T x) = algebraMap k T (g x) := by
    change Algebra.TensorProduct.congr (.refl : L ≃ₐ[L] L) g
      ((1 : L) ⊗ₜ[F] x) = (1 : L) ⊗ₜ[F] g x
    simp
  obtain ⟨r, top, hkr, hlocal, _, _, _⟩ := finiteExtension_localField (K := k) (L := T)
  let := r
  let := top
  let : ValuativeExtension k T := hkr
  let : IsNonarchimedeanLocalField T := hlocal
  let : ValuativeExtension F T :=
    ⟨fun a b => by
      rw [IsScalarTower.algebraMap_apply F k T a, IsScalarTower.algebraMap_apply F k T b,
        ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩
  let : ValuativeExtension L T :=
    ⟨fun a b => ((valuation T).vle_iff_le).trans
      ((valuativeEmbedding (IsScalarTower.toAlgHom F L T) a b).trans (valuation L).vle_iff_le.symm)⟩
  obtain ⟨e, he, hLT⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization L).2.2 T
  have hLT' (x : L) : normalizedValuation T (algebraMap L T x) = normalizedValuation L x ^ e := hLT x
  have hπne : π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hR :
      WithZero.exp (ramificationIndex k T * (-1)) = WithZero.exp ((-1 : ℤ) * (2 * (e : ℤ))) := by
    calc
      _ = normalizedValuation T (algebraMap k T (algebraMap F k π)) := by
        rw [normalizedValuation_algebraMap_exp (F := k) (L := T) ((map_ne_zero (algebraMap F k)).2 hπne),
          hk π, hπ', WithZero.log_exp]
      _ = normalizedValuation T (algebraMap L T (algebraMap F L π)) := by
        rw [← IsScalarTower.algebraMap_apply F k T, ← IsScalarTower.algebraMap_apply F L T]
      _ = _ := by
        rw [hLT', hram, hπ', ← pow_mul]
        rw [← zpow_natCast, ← WithZero.exp_zsmul, zsmul_eq_mul]
        congr 1
        push_cast
        ring
  have heq : ramificationIndex k T = 2 * (e : ℤ) := by
    have h := WithZero.exp_injective hR
    omega
  have hramT : 1 < ramificationIndex k T := by omega
  obtain ⟨heT, _, _⟩ := ramifiedQuadratic k T hT hramT
  have he1 : e = 1 := by omega
  refine ⟨{ field := T
            tensor := AlgEquiv.refl
            left_eq := fun _ => rfl
            right_eq := fun _ => rfl
            degree := hT
            diagram := ζ
            diagram_ne := hζ
            diagram_extends := hζleft
            coefficient := coeff
            coefficient_extends := hcoeff
            unramified := fun x => by rw [hLT', he1, pow_one] }⟩

end Compositum



/-- A root layer of the same positive relative index as the chamber
intersection supplies representatives for the latter's cosets. -/
theorem factorizationOfRelativeIndex {G : Type*} [Group G] (I U J : Subgroup G)
    (hUI : U ≤ I) (hindex : J.relIndex U = J.relIndex I) (hpos : 0 < J.relIndex I) :
    ∀ g ∈ I, ∃ u ∈ U, ∃ j ∈ J, g = u * j := by
  let i := Subgroup.quotientSubgroupOfEmbeddingOfLE J hUI
  let _ : Finite (I ⧸ J.subgroupOf I) := Nat.finite_of_card_ne_zero hpos.ne'
  have hsurj := ((Nat.bijective_iff_injective_and_card i).2 ⟨i.injective, hindex⟩).2
  intro g hg
  obtain ⟨x, h⟩ := hsurj (QuotientGroup.mk (⟨g, hg⟩ : I))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  change Subgroup.quotientSubgroupOfEmbeddingOfLE J hUI (QuotientGroup.mk u) =
    QuotientGroup.mk (⟨g, hg⟩ : I) at h
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq] at h
  refine ⟨u, u.property, (u : G)⁻¹ * g, h, ?_⟩
  simp

section ConjugateLabels

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- The conjugate Iwahori depends only on the affine label of the lift. -/
theorem sameLabel_conjugateIwahori (C : LocalComparison (j := j) (Wf := Wf) A p)
    {n m : C.N} (h : C.affine n = C.affine m) :
    C.I.map (MulAut.conj (n : G)).toMonoidHom = C.I.map (MulAut.conj (m : G)).toMonoidHom := by
  have hnm : (m : G)⁻¹ * (n : G) ∈ C.I := by
    have h' : C.affine m⁻¹ = C.affine n⁻¹ := by simp only [map_inv, h]
    exact unitTorus_le_iwahori C (by simpa only [Subgroup.coe_inv, inv_inv] using
      (sameLabel_div_mem_unitTorus C h'))
  let a := (m : G)⁻¹ * (n : G)
  have ha : a ∈ C.I := hnm
  have hna : (n : G) = (m : G) * a := by simp [a]
  have him : C.I.map (MulAut.conj a).toMonoidHom = C.I := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact C.I.mul_mem (C.I.mul_mem ha hx) (C.I.inv_mem ha)
    · intro hg
      refine ⟨a⁻¹ * g * a, C.I.mul_mem (C.I.mul_mem (C.I.inv_mem ha) hg) ha, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hcomp : (MulAut.conj (m : G) * MulAut.conj a).toMonoidHom =
      (MulAut.conj (m : G)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := rfl
  rw [hna, map_mul, hcomp, ← Subgroup.map_map, him]

end ConjugateLabels

section FoldedApartment

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection AlcoveGeometry
  PinnedWallSigns e6Cartan exceptionalCartan e6Partner diagramCocharacters diagramAverage
  foldedDepthDenominator foldedApartment unfoldApartment simpleRootValues)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment)

open private transported_reflectionClosed transported_reducedDirections transported_corootLattice
  transported_coweightLattice small_alcove_signs
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

private theorem e6_standardCartan : exceptionalCartan 6 = e6Cartan := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

set_option backward.isDefEq.respectTransparency false in
/-- The dual F₄ affine arrangement on the actual invariant cocharacter
space, including the common projected translation lattice. -/
private theorem foldedExceptionalApartmentAt (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (τ : BasedIso D D) (numbering : ExceptionalNumbering D 6 b)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i))
    (x : ℚ ⊗[ℤ] D.Y) (c : ℚ) (hc : 0 < c)
    (hx : ∀ i, simpleRootValues D.datum D.base b ℚ x i = c)
    (hsmall : ∀ i, (0 < (ApartmentRoots.split D.datum ℚ).root i x ↔ D.base.IsPos i) ∧
      0 < |(ApartmentRoots.split D.datum ℚ).root i x| ∧
      |(ApartmentRoots.split D.datum ℚ).root i x| < 1 / 2) :
    ∃ A : FoldedApartment τ,
      A.basepoint.val = x ∧
      PinnedWallSigns A.roots A.basepoint (fun a => ∃ i, A.direction i = a ∧ D.base.IsPos i) ∧
      AlcoveGeometry A.roots A.basepoint ∧ A.roots.ReflectionClosed ∧ A.roots.ReducedDirections ∧
      ∀ a : A.roots.SimpleWall A.basepoint, ∃! y, IsAlcoveVertex A.roots A.basepoint a y := by
  classical
  let _ := D.finiteRoots
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := D.reduced
  have hC (i j : Fin 6) : e6Cartan i j = D.datum.pairing (b i) (b j) :=
    (congrFun (congrFun e6_standardCartan.symm i) j).trans (numbering.2 i j).symm
  obtain ⟨f, d, B, hf, hd, horb, hlong, horth, hroot, hcoroot, href, hval, hvec, hproj⟩ :=
    ExceptionalAffineRootSystems.e6FoldedDatumInCocharacters (K := ℚ)
      D.datum D.base b τ.val numbering.1 hτ hC
  let V := invariantApartment D τ
  let A : ApartmentRoots ℚ V FoldedRootDirection := B.transport f
  let E := ApartmentRoots.split D.datum ℚ
  have eval (i : D.I) (x : V) : A.root (d i) x = (foldedDepthDenominator (d i) : ℚ) * E.root i x.val := by
    obtain ⟨z, rfl⟩ := f.surjective x
    change B.root (d i) (f.symm (f z)) = _
    rw [f.symm_apply_apply]
    exact hval i z
  have hcor : f '' (B.corootLattice : Set _) = (A.corootLattice : Set V) :=
    transported_corootLattice B f
  have hcow : f '' (B.coweightLattice : Set _) = (A.coweightLattice : Set V) :=
    transported_coweightLattice B f
  have lattice : (invariantApartment D τ).subtype '' (A.corootLattice : Set V) =
      diagramAverage (diagramCocharacters τ.val) '' (E.corootLattice : Set _) := by
    calc
      _ = (fun x : V => x.val) '' (f '' (B.corootLattice : Set _)) :=
        congrArg (Set.image (fun x : V => x.val)) hcor.symm
      _ = (fun x => (f x).val) '' (B.corootLattice : Set _) :=
        Set.image_image (fun x : V => x.val) f _
      _ = _ := hproj
  have lattice' : (invariantApartment D τ).subtype '' (A.corootLattice : Set V) =
      diagramAverage (diagramCocharacters τ.val) '' (E.coweightLattice : Set _) := by
    rw [lattice]
    exact ExceptionalAffineRootSystems.e6ProjectedCocharacters (K := ℚ)
      D.datum D.base b τ.val numbering.1 hτ hC
  have latticeEq : A.corootLattice = A.coweightLattice := by
    apply SetLike.coe_injective
    rw [← hcor, ← hcow,
      ExceptionalAffineRootSystems.foldedTranslationLattice B hroot hcoroot]
  have groupEq : A.affineWeylGroup = A.extendedAffineWeylGroup := by
    ext g
    obtain ⟨_, h₁, h₂⟩ := ExceptionalAffineRootSystems.affineGroupNormalForms A
    rw [h₁, h₂, latticeEq]
  obtain ⟨φ, hφ⟩ :=
    ExceptionalAffineRootSystems.cocharacterApartmentCoordinates (K := ℚ) D.datum D.base b numbering.1
  let p : V := f (unfoldApartment (fun _ => c))
  have hp : p.val = x := by
    apply φ.injective
    change φ.toLinearMap (f (unfoldApartment (fun _ => c))).val = φ.toLinearMap x
    rw [hφ, hf, (ExceptionalAffineRootSystems.foldedApartmentCoordinates (K := ℚ)).2.1 _ rfl rfl]
    exact (funext hx).symm
  let pos (a : FoldedRootDirection) := ∃ i, d i = a ∧ D.base.IsPos i
  have hsign (a : FoldedRootDirection) :
      (0 < A.root a p ↔ pos a) ∧ 0 < |A.root a p| ∧ |A.root a p| < 1 := by
    obtain ⟨i, rfl⟩ := hd a
    have hn (j : D.I) : 0 < (foldedDepthDenominator (d j) : ℚ) := by
      unfold foldedDepthDenominator
      split <;> decide
    have hm : (foldedDepthDenominator (d i) : ℚ) ≤ 2 := by
      unfold foldedDepthDenominator
      split <;> decide
    have hsign' (j : D.I) : 0 < A.root (d j) p ↔ D.base.IsPos j := by
      rw [eval, hp, mul_pos_iff_of_pos_left (hn j)]
      exact (hsmall j).1
    refine ⟨⟨fun h => ⟨i, rfl, (hsign' i).1 h⟩, fun ⟨j, hj, h⟩ => hj ▸ (hsign' j).2 h⟩, ?_⟩
    rw [eval, hp, abs_mul, abs_of_pos (hn i)]
    have ⟨ha, hb⟩ := (hsmall i).2
    exact ⟨mul_pos (hn i) ha, (mul_le_mul_of_nonneg_right hm ha.le).trans_lt (by linarith)⟩
  obtain ⟨hreg, hs⟩ := small_alcove_signs A p pos hsign
  let _ : Finite FoldedRootDirection := Finite.of_surjective d hd
  have hreflection := transported_reflectionClosed B f href
  have hreduced :=
    transported_reducedDirections B f (ExceptionalAffineRootSystems.foldedReducedDirections B hroot)
  have hgeom := ExceptionalAffineRootSystems.affineApartmentGeometry A hreflection hreduced p hreg
  have hΩ : Subsingleton (Specs.ExceptionalAffineRootSystems.alcoveStabilizer A (A.alcove p)) := by
    apply subsingleton_of_forall_eq 1
    intro g
    let w : A.affineWeylGroup := ⟨g.val.val, groupEq.symm ▸ g.val.property⟩
    have hw : w = 1 := (hgeom.simply_transitive p hreg).unique (y₁ := w) (y₂ := 1) g.property (by simp)
    exact Subtype.ext (Subtype.ext (congrArg (fun w : A.affineWeylGroup => w.val) hw))
  let Q : FoldedApartment τ :=
    { roots := A
      basepoint := p
      direction := d
      surjective := hd
      orbits := horb
      long := hlong
      orthogonal := horth
      root_value := eval
      coroot_value := hvec
      coordinates := f
      normalized_root := fun a y => by
        change B.root a (f.symm (f y)) = _
        rw [f.symm_apply_apply, hroot]
      normalized_coroot := fun a => by
        change f _ = f (B.coroot a)
        rw [hcoroot]
      coroot_projection := lattice
      coweight_projection := lattice'
      affine_eq := groupEq
      omega_trivial := hΩ }
  have hvertices : ∀ a : Q.roots.SimpleWall Q.basepoint,
      ∃! y, IsAlcoveVertex Q.roots Q.basepoint a y :=
    ExceptionalFoldedAlcoveVertices.foldedAlcoveVertices Q.roots Q.coordinates
      Q.normalized_root hreduced c hc (fun a => (hsign a).2.2)
  exact ⟨Q, hp, hs, hgeom, hreflection, hreduced, hvertices⟩

theorem foldedExceptionalApartment (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (τ : BasedIso D D) (numbering : ExceptionalNumbering D 6 b)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) :
    ∃ A : FoldedApartment τ,
      PinnedWallSigns A.roots A.basepoint (fun a => ∃ i, A.direction i = a ∧ D.base.IsPos i) ∧
      AlcoveGeometry A.roots A.basepoint := by
  let _ := D.finiteRoots
  let _ := D.reduced
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  obtain ⟨x, c, hc, hx, hsmall⟩ :=
    ExceptionalAffineRootSystems.pinnedAlcovePoint (K := ℚ) D.datum D.base b numbering.1
  obtain ⟨A, _, hs, hg, _, _, _⟩ :=
    foldedExceptionalApartmentAt D b τ numbering hτ x c hc hx hsmall
  exact ⟨A, hs, hg⟩

end FoldedApartment

section SplitCentral

private theorem factorsOfNormalImage {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (I : Subgroup G) (J U : Subgroup H)
    (normal : φ.range.Normal) (hJ : J = I.map φ ⊔ U) (hpre : J.comap φ = I) :
    ∀ h, h ∈ J ↔ ∃ (g : I) (t : U), h = φ g * t := by
  let _ := normal
  let A := φ.range.subgroupOf J
  let B := U.subgroupOf J
  have hA : A.map J.subtype = I.map φ := by
    change (φ.range.comap J.subtype).map J.subtype = _
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    ext x
    constructor
    · rintro ⟨h, ⟨g, rfl⟩⟩
      exact ⟨g, hpre ▸ (show g ∈ J.comap φ from h), rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(show g ∈ J.comap φ from hpre.symm ▸ hg), ⟨g, rfl⟩⟩
  have hU : U ≤ J := hJ.symm ▸ le_sup_right
  have hB : B.map J.subtype = U := Subgroup.map_subgroupOf_eq_of_le hU
  have htop : A ⊔ B = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : H) ∈ (A ⊔ B).map J.subtype := by
      rw [Subgroup.map_sup, hA, hB, ← hJ]
      exact x.property
    obtain ⟨y, hy, he⟩ := hx
    exact (show y = x from Subtype.ext he) ▸ hy
  intro h
  constructor
  · intro hh
    let x : J := ⟨h, hh⟩
    have hx : x ∈ A ⊔ B := htop.symm ▸ Subgroup.mem_top x
    obtain ⟨a, ha, b, hb, he⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨g, hga⟩ : (a : H) ∈ φ.range := ha
    have hg : g ∈ I := by
      rw [← hpre]
      change φ g ∈ J
      rw [hga]
      exact a.property
    have hab : (a : H) * (b : H) = h := congrArg Subtype.val he
    exact ⟨⟨g, hg⟩, ⟨b, hb⟩, hab.symm.trans (congrArg (· * (b : H)) hga.symm)⟩
  · rintro ⟨g, t, rfl⟩
    exact J.mul_mem (hpre.symm ▸ g.property) (hU t.property)

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra TorusValues torusPoint fibre)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom pointHom)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open private markedGroundEquiv markedGroundEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The central map of split marked point groups reflects the Iwahori
and normalizer. Every adjoint Iwahori point is the image of a simply
connected Iwahori point times an adjoint unit torus point. -/
theorem splitCentralIwahori
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (F : MarkedFibre M K) (F' : MarkedFibre M' K)
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (C' : LocalComparison (j := identityPoints M' K) (Wf := E.datum.weylGroup)
      (ApartmentRoots.split E.datum ℚ) p')
    (hC : SplitPointComparison F false C) (hC' : SplitPointComparison F' true C') :
    let φ := integralPointHom c.map (integralRing K)
    C'.I.comap φ = C.I ∧
    (∀ h, h ∈ C'.I ↔ ∃ (g : C.I) (t : C'.T₀), h = φ g * t) ∧
    C'.N.comap φ = C.N ∧ C'.T₀.comap φ = C.T₀ ∧
    C'.localIwahori.normalizer.torus.comap φ = C.localIwahori.normalizer.torus ∧
    φ.range.Normal := by
  intro φ
  let P := C.localIwahori
  let P' := C'.localIwahori
  obtain ⟨hi₀, hp₀⟩ := ExceptionalIwahoriImageComparison.splitIwahoriCoverComparison c F F'
    P.residueFibre P'.residueFibre P.residueBorel P'.residueBorel P.borel_eq P'.borel_eq
  have hi : C'.I = C.I.map φ ⊔ C'.T₀ := by
    simpa only [LocalComparison.I, LocalComparison.T₀, Specs.ExceptionalLocalRootCoordinates.LocalIwahori.iwahori,
      identityPoints, Subgroup.comap_id] using hi₀
  have hpreI : C'.I.comap φ = C.I := by
    simpa only [LocalComparison.I, Specs.ExceptionalLocalRootCoordinates.LocalIwahori.iwahori,
      identityPoints, Subgroup.comap_id] using hp₀
  let f := F.groupIso.inv ≫ (fibre K).map c.map ≫ F'.groupIso.hom
  let q := pointHom f (𝟙_ (SchemeOver K))
  let j := markedGroundEquiv F
  let j' := markedGroundEquiv F'
  obtain ⟨hφ, _, hn, hnormal⟩ := ExceptionalIwahoriImageComparison.splitCentralPointComparison c F F'
  have hcomm (g) : j' (q g) = φ (j g) := by
    rw [markedGroundEquiv_apply, markedGroundEquiv_apply]
    exact hφ g
  have hnormal' : φ.range.Normal := by
    have heq : q.range.map j'.toMonoidHom = φ.range := by
      rw [← MonoidHom.range_comp, show j'.toMonoidHom.comp q = φ.comp j.toMonoidHom from
        MonoidHom.ext hcomm, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr j.surjective,
        Subgroup.map_top]
    exact heq ▸ hnormal.map j'.toMonoidHom j'.surjective
  have hpreN : C'.N.comap φ = C.N := by
    ext a
    obtain ⟨g, rfl⟩ := j.surjective a
    change φ (j g) ∈ C'.N ↔ j g ∈ C.N
    rw [← hcomm, markedGroundEquiv_apply, markedGroundEquiv_apply, hC'.1, hC.1]
    exact hn g
  have hpreT₀ : C'.T₀.comap φ = C.T₀ := by
    have h := P.intersection
    have h' := P'.intersection
    change C.I ⊓ C.N = C.T₀ at h
    change C'.I ⊓ C'.N = C'.T₀ at h'
    rw [← h', Subgroup.comap_inf, hpreI, hpreN, h]
  refine ⟨hpreI, factorsOfNormalImage φ C.I C'.I C'.T₀ hnormal' hi hpreI, hpreN, hpreT₀, ?_, hnormal'⟩
  ext g
  change φ g ∈ P'.normalizer.torus ↔ g ∈ P.normalizer.torus
  rw [P'.normalizer.torusPoints, P.normalizer.torusPoints]
  constructor
  · exact ExceptionalIwahoriImageComparison.splitTorusPointPreimage c F F' g
  · rintro ⟨t, ht⟩
    refine ⟨t.comp c.pullCharacter.toAddMonoidHom.toMultiplicative, ?_⟩
    change g = _ at ht
    change φ g = _
    rw [ht]
    exact c.marking.2.2 (CommAlgCat.of Integers.{u} K) t

end SplitCentral

section NormalizerCharts

open AlgebraicGeometry CategoryTheory
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalAffineBruhat
open Specs.IntegralSemisimpleModel (Model Integers IntegralPoints integerAlgebra TorusValues
  cocharacter torusPoint integralSpec)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRing changeRingHom
  residueRing residueHom markedTorus markedScaledReduction)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (markedWeylWord)
open Specs.ExceptionalValuedTorusNormalizer (conjugateTorus)
open scoped CategoryTheory.MonObj TensorProduct WithZero
open ValuativeRel WithZero

open private rationalCocharacters_clearDenominators 
  normalizedValuation_le_iff integralCocharacter_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private normalizerOfMarkedFibre splitMarkedNormalizerWord
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private affineTorusPointEquiv torusPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

private theorem markedWeylWord_conjugatesTorus {D : BasedRootDatum.{u}} (M : Model D)
    {K : Type u} [Field K] (l : List D.I) (hl : ∀ i ∈ l, i ∈ D.base.support)
    (t : TorusValues D (integralRing K)) :
    let R := integralRing K
    let w := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    MulAut.conj (markedWeylWord M.toIntegralMarking R l) (torusPoint D R t ≫ M.torus.hom.hom) =
      (torusPoint D R (t.comp w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) ≫
        M.torus.hom.hom : IntegralPoints M.group R) := by
  obtain ⟨B⟩ := ExceptionalMarkedRootDescent.markedFibreExists M K
  let F := normalizerOfMarkedFibre B
  let _ := F.torusComm
  obtain ⟨a, ha, hq⟩ := splitMarkedNormalizerWord F l hl
  obtain ⟨j, hj, hconj⟩ := ExceptionalValuedTorusNormalizer.fibreNormalizerTorusAction F
  have h := congrArg (fun n : F.label.ker => F.point n.val) (hconj a t)
  change F.point (a * (j t).val * a⁻¹) = F.point
    (j (t.comp (F.label a).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative)).val at h
  rw [map_mul, map_mul, map_inv, ha, hj, hj, hq] at h
  exact h

private theorem markedWeylWord_normalizesTorus {D : BasedRootDatum.{u}} (M : Model D)
    {K : Type u} [Field K] (l : List D.I) (hl : ∀ i ∈ l, i ∈ D.base.support) :
    markedWeylWord M.toIntegralMarking (integralRing K) l ∈
      Subgroup.normalizer (markedTorus M.toIntegralMarking (integralRing K) : Set _) := by
  let R := integralRing K
  let w := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  let k := w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  let k' := w.val.weightEquiv.toLinearMap.toAddMonoidHom.toMultiplicative
  let m := markedWeylWord M.toIntegralMarking R l
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  apply Set.Subset.antisymm
  · rintro g ⟨h, ⟨t, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).surjective t
    refine ⟨torusPoint D R (x.comp k), ?_⟩
    exact (markedWeylWord_conjugatesTorus M l hl x).symm
  · rintro g ⟨t, rfl⟩
    obtain ⟨x, rfl⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).surjective t
    refine ⟨torusPoint D R (x.comp k') ≫ M.torus.hom.hom, ⟨_, rfl⟩, ?_⟩
    rw [markedWeylWord_conjugatesTorus M l hl]
    apply congrArg (fun t : TorusValues D R => (torusPoint D R t ≫ M.torus.hom.hom :
      IntegralPoints M.group R))
    apply MonoidHom.ext
    intro χ
    change x (Multiplicative.ofAdd (w.val.weightEquiv (w.val.weightEquiv.symm (Multiplicative.toAdd χ)))) = x χ
    rw [LinearEquiv.apply_symm_apply]
    rfl

private theorem normalizedValuation_map_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]
    [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    (a b : K) :
    normalizedValuation L (algebraMap K L a) ≤ normalizedValuation L (algebraMap K L b) ↔
      normalizedValuation K a ≤ normalizedValuation K b := by
  exact (normalizedValuation_le_iff _ _).trans
    ((ValuativeExtension.vle_iff_vle a b).trans (normalizedValuation_le_iff _ _).symm)

private theorem normalizedValuation_map_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]
    [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    (z : K) :
    normalizedValuation L (algebraMap K L z) = 1 ↔ normalizedValuation K z = 1 := by
  simpa only [map_one] using show
      normalizedValuation L (algebraMap K L z) = normalizedValuation L (algebraMap K L 1) ↔
        normalizedValuation K z = normalizedValuation K 1 by
    rw [le_antisymm_iff, le_antisymm_iff, normalizedValuation_map_le, normalizedValuation_map_le]

section Scaling

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- The chart inequalities at an apartment point are the torus-reduction
condition after clearing the denominators of its rescaled cocharacter. -/
private theorem pointChart_fromIntegralScaling (C : LocalRootChart (j := j) A p)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos)
    (x : V) (z : ℚ ⊗[ℤ] D.Y) (m : J → ℤ)
    (root_eq : ∀ i, (ApartmentRoots.split D.datum ℚ).root i z =
      (m (C.direction i) : ℚ) * A.root (C.direction i) x)
    {L : Type u} [Field L] (f : K →+* L) (v : Valuation L ℤᵐ⁰)
    (unit : ∀ a, v (f a) = 1 ↔ normalizedValuation K a = 1)
    (d : ℕ) (hd : 0 < d) (y : D.Y) (hy : (1 : ℚ) ⊗ₜ[ℤ] y = (d : ℚ) • z)
    (ξ π : Lˣ) (hpow : (ξ : L) ^ d = π) (r : ℤ) (hr : 0 < r)
    (hπ : v (π : L) = exp (-r)) (hm : ∀ a, 0 < m a)
    (hn : ∀ l a, v (f (C.chart.negMap l a)) =
      C.value (C.chart.neg l) a ^ (r * m (C.chart.neg l)))
    (hp : ∀ l a, v (f (C.chart.posMap l a)) =
      C.value (C.chart.pos l) a ^ (r * m (C.chart.pos l))) (g : G) :
    (⟨j g, ⟨g, rfl⟩⟩ : j.range) ∈ markedScaledReduction M.toIntegralMarking j.range f v y ξ
      ↔ C.atPoint x g := by
  classical
  have hsurj (a : J) : ∃ i, C.direction i = a := by
    rcases covers a with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · exact ⟨C.negative[l], (C.neg_slots l).symm⟩
    · exact ⟨C.positive[l], (C.pos_slots l).symm⟩
  choose i hi using hsurj
  let k (a : J) := D.datum.toLinearMap (D.datum.root (i a)) y
  have hpair (a : D.I) : (D.datum.toLinearMap (D.datum.root a) y : ℚ) =
        (d : ℚ) * ((m (C.direction a) : ℚ) * A.root (C.direction a) x) := by
    rw [← RootData.extendFunctional_one_tmul ℚ (D.datum.root' a) y]
    change ((ApartmentRoots.split D.datum ℚ).root a) ((1 : ℚ) ⊗ₜ[ℤ] y) = _
    rw [hy, map_smul, root_eq, smul_eq_mul]
  have hk (a : J) : (k a : ℚ) = (d : ℚ) * ((m a : ℚ) * A.root a x) := by
    dsimp only [k]
    rw [hpair, hi]
  have hn' (l : Fin C.negative.length) :
      D.datum.toLinearMap (D.datum.root C.negative[l]) y = k (C.chart.neg l) := by
    apply Int.cast_injective (α := ℚ)
    rw [hpair, hk, C.neg_slots]
  have hp' (l : Fin C.positive.length) :
      D.datum.toLinearMap (D.datum.root C.positive[l]) y = k (C.chart.pos l) := by
    apply Int.cast_injective (α := ℚ)
    rw [hpair, hk, C.pos_slots]
  refine scaledReduction_atPoint C covers f v unit (fun a => r * m a)
    (fun a => mul_pos hr (hm a)) hn hp y ξ π d hd hpow r hπ k hn' hp' x ?_ g
  intro a
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm' : (m a : ℚ) ≠ 0 := by exact_mod_cast (hm a).ne'
  rw [hk, Int.cast_mul]
  field_simp

/-- Conjugation transports the positive-depth chart to the image point
under the marked normalizer action. The embedding doubles the invariant
cocharacters over a ramified quadratic splitting field. -/
theorem normalizerTranslatedChart
    (C : LocalComparison (j := j) (Wf := Wf) A p)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (labels : Wf →* D.datum.weylGroup)
    (simpleWords : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (wordLabel : ∀ w, (((C.localIwahori.normalizer.word w).map
      (RootPairing.weylGroup.ofIdx D.datum)).prod) = labels w)
    (embed : V → ℚ ⊗[ℤ] D.Y) (m : J → ℤ) (hm : ∀ a, 0 < m a)
    (roots : ∀ x i, (ApartmentRoots.split D.datum ℚ).root i (embed x) =
      (m (C.chart.direction i) : ℚ) * A.root (C.chart.direction i) x)
    (action : ∀ (n : C.N) (x : V),
      let N := C.localIwahori.normalizer
      embed (C.affine n x) =
        (labels (N.label n)).val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y (embed x) +
          ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd))
    (covers : ∀ a, a ∈ Set.range C.chart.chart.neg ∪ Set.range C.chart.chart.pos)
    (hvn : ∀ l x, normalizedValuation K (C.chart.chart.negMap l x) =
      C.chart.value (C.chart.chart.neg l) x ^ m (C.chart.chart.neg l))
    (hvp : ∀ l x, normalizedValuation K (C.chart.chart.posMap l x) =
      C.chart.value (C.chart.chart.pos l) x ^ m (C.chart.chart.pos l))
    (base : ∀ g, g ∈ C.I ↔ C.chart.atPoint p g)
    (n : C.N) (g : G) :
    g ∈ C.I.map (MulAut.conj (n : G)).toMonoidHom ↔ C.chart.atPoint (C.affine n p) g := by
  classical
  let N := C.localIwahori.normalizer
  let a := N.label n
  let l := N.word a
  let w := (labels a).val
  let v := w.coweightEquiv.symm
  let h := N.torusPart n
  let z := (N.translation h).toAdd
  obtain ⟨t, ht⟩ := (N.torusPoints h).mp h.property
  obtain ⟨d, hd, x, y, hx, hy⟩ :=
    rationalCocharacters_clearDenominators b (embed p) (embed (C.affine n p))
  have hy' : y = v x + (d : ℤ) • z := by
    apply integralCocharacter_injective D b
    change (1 : ℚ) ⊗ₜ[ℤ] y = (1 : ℚ) ⊗ₜ[ℤ] (v x + (d : ℤ) • z)
    have hz : (d : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] z) = (1 : ℚ) ⊗ₜ[ℤ] ((d : ℤ) • z) := by
      rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      congr 1
    rw [hy, action, smul_add, ← map_smul, ← hx, TensorProduct.tmul_add, hz]
    rfl
  obtain ⟨π₀, hπ₀⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization K).1 (exp (-1))
  change normalizedValuation K π₀ = exp (-1) at hπ₀
  have hπne : π₀ ≠ 0 := by
    intro he
    rw [he, map_zero] at hπ₀
    exact exp_ne_zero hπ₀.symm
  let π := Units.mk0 π₀ hπne
  have hπ : log (normalizedValuation K (π : K)) = -1 := by
    change log (normalizedValuation K π₀) = -1
    rw [hπ₀, log_exp]
  obtain ⟨L, fL, aL, vL, tL, hfin, hext, hloc, ξ, c, hc, hξpow, hξlog, hlog⟩ :=
    ExceptionalValuedTorusNormalizer.uniformizerRootExtension d hd π hπ
  let _ := fL
  let _ := aL
  let _ := vL
  let _ := tL
  let _ := hfin
  let _ := hext
  let _ := hloc
  let r : ℤ := (d : ℤ) * c
  have hr : 0 < r := mul_pos (Int.natCast_pos.mpr hd) hc
  let f := algebraMap K L
  let π' := Units.map f.toMonoidHom π
  have hπ' : normalizedValuation L (π' : L) = exp (-r) := by
    have hp := hlog π
    change log (normalizedValuation L (π' : L)) = r * log (normalizedValuation K (π : K)) at hp
    rw [hπ, mul_neg_one] at hp
    exact (exp_log (by simp : normalizedValuation L (π' : L) ≠ 0)).symm.trans (congrArg exp hp)
  have hpow : (ξ : L) ^ d = (π' : L) :=
    congrArg (fun t : Lˣ => (t : L)) hξpow
  have hval_z (u : K) : normalizedValuation L (f u) = normalizedValuation K u ^ r :=
    ExceptionalIwahoriCongruence.valuationExtensionPowers f _ _ π (show normalizedValuation K (π : K) = exp (-1) from hπ₀)
      (fun _ => (normalizedValuation_map_eq_one _).2) r hr hπ' u
  have hn (l₀) (u) : normalizedValuation L (f (C.chart.chart.negMap l₀ u)) =
      C.chart.value (C.chart.chart.neg l₀) u ^ (r * m (C.chart.chart.neg l₀)) := by
    rw [hval_z, hvn, ← zpow_mul, mul_comm r]
  have hp (l₀) (u) : normalizedValuation L (f (C.chart.chart.posMap l₀ u)) =
      C.chart.value (C.chart.chart.pos l₀) u ^ (r * m (C.chart.chart.pos l₀)) := by
    rw [hval_z, hvp, ← zpow_mul, mul_comm r]
  let O := integralRing (normalizedValuation L).valuationSubring
  let k := residueRing O
  let MO := markedWeylWord M.toIntegralMarking O l
  let kχ := w.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  let TL := integralRing L
  let tL' : TorusValues D TL := (Units.map f.toMonoidHom).comp t
  let cx := cocharacter D x TL ξ
  let cy := cocharacter D y TL ξ
  let wx := cx.comp kχ
  let H := j.range
  let nH : H := ⟨j n, ⟨n, rfl⟩⟩
  let X := markedScaledReduction M.toIntegralMarking H f (normalizedValuation L) x ξ
  let Y := markedScaledReduction M.toIntegralMarking H f (normalizedValuation L) y ξ
  have action_cov : X.map (MulAut.conj nH).toMonoidHom = Y := by
    refine ExceptionalIwahoriCongruence.markedNormalizerCovariance M.toIntegralMarking H f
      (normalizedValuation L) x y ξ nH MO tL' wx ?_ ?_ ?_ ?_
    · rw [show changeRingHom M.group (residueHom O) MO =
          markedWeylWord M.toIntegralMarking k l from
        markedWeylWord_map M.toIntegralMarking (residueHom O) l]
      exact markedWeylWord_normalizesTorus M l (simpleWords a)
    · have hj : j (n : G) = j h * j (N.lift a) := by
        rw [← map_mul]
        congr 1
        exact (inv_mul_cancel_right _ _).symm
      change changeRing (integralRingMap f) (j (n : G)) = _
      rw [hj, N.lift_point, ht]
      change changeRingHom M.group (integralRingMap f) (_ * _) = _
      rw [map_mul, show changeRingHom M.group (integralRingMap f)
        (markedWeylWord M.toIntegralMarking (integralRing K) l) =
          markedWeylWord M.toIntegralMarking TL l from
        markedWeylWord_map M.toIntegralMarking (integralRingMap f) l,
        show changeRingHom M.group (integralRingMap (normalizedValuation L).valuationSubring.subtype) MO =
          markedWeylWord M.toIntegralMarking TL l from
        markedWeylWord_map M.toIntegralMarking
          (integralRingMap (normalizedValuation L).valuationSubring.subtype) l]
      congr 1
      change integralSpec.map (integralRingMap f).op ≫
        (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) = _
      rw [← Category.assoc]
      exact congrArg (· ≫ M.torus.hom.hom)
        (torusPoint_natural (integralRingMap f) t)
    · rw [show changeRingHom M.group (integralRingMap (normalizedValuation L).valuationSubring.subtype) MO =
          markedWeylWord M.toIntegralMarking TL l from
        markedWeylWord_map M.toIntegralMarking
          (integralRingMap (normalizedValuation L).valuationSubring.subtype) l]
      have hw : (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod = labels a := wordLabel a
      simpa only [hw, wx, kχ, w] using markedWeylWord_conjugatesTorus M l (simpleWords a) cx
    · obtain ⟨ν, _, hν, _⟩ := ExceptionalValuedTorusNormalizer.splitTorusTranslation L D b
      obtain ⟨hcochar, hweyl⟩ := ExceptionalValuedTorusNormalizer.splitTranslationAction D ν hν
      have htz : (ν tL').toAdd = r • z := by
        apply D.datum.toLinearMap.flip.toPerfPair.injective
        ext χ
        change D.datum.toLinearMap χ (ν tL').toAdd = D.datum.toLinearMap χ (r • z)
        rw [hν, map_smul, N.characterLog h t ht, zsmul_eq_mul]
        exact hlog (t (Multiplicative.ofAdd χ))
      have hxν : (ν cx).toAdd = -c • x := by rw [hcochar, hξlog]
      have hyν : (ν cy).toAdd = -c • y := by rw [hcochar, hξlog]
      have hwν : (ν wx).toAdd = v (ν cx).toAdd := hweyl w cx
      have hsum : (ν cy).toAdd + (ν tL').toAdd = (ν wx).toAdd := by
        rw [hyν, htz, hwν, hxν, hy', map_smul, smul_add, ← mul_smul]
        rw [Int.neg_mul, add_assoc, mul_comm c, ← show r = (d : ℤ) * c from rfl, (neg_smul r z), neg_add_cancel, add_zero]
      intro χ
      let vL' := normalizedValuation L
      change vL' (cy χ : L) * vL' (tL' χ : L) = vL' (wx χ : L)
      have hval (u : TorusValues D TL) : vL' (u χ : L) ≠ 0 := by
        exact (map_ne_zero vL').mpr (Units.ne_zero _)
      have he := congrArg (D.datum.toLinearMap (Multiplicative.toAdd χ)) hsum
      rw [map_add, hν, hν, hν] at he
      change log (vL' (cy χ : L)) + log (vL' (tL' χ : L)) = log (vL' (wx χ : L)) at he
      rw [← log_mul (hval cy) (hval tL')] at he
      simpa only [exp_log (mul_ne_zero (hval cy) (hval tL')), exp_log (hval wx)] using
        congrArg exp he
  have hxg (g' : G) : (⟨j g', ⟨g', rfl⟩⟩ : H) ∈ X ↔ C.chart.atPoint p g' :=
    pointChart_fromIntegralScaling C.chart covers p (embed p) m (roots p) f
      (normalizedValuation L) normalizedValuation_map_eq_one d hd x hx ξ π' hpow r hr hπ' hm hn hp g'
  have hyg : (⟨j g, ⟨g, rfl⟩⟩ : H) ∈ Y ↔ C.chart.atPoint (C.affine n p) g :=
    pointChart_fromIntegralScaling C.chart covers (C.affine n p) (embed (C.affine n p)) m
      (roots (C.affine n p)) f (normalizedValuation L) normalizedValuation_map_eq_one
      d hd y hy ξ π' hpow r hr hπ' hm hn hp g
  rw [← hyg, ← action_cov, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  have he : nH⁻¹ * (⟨j g, ⟨g, rfl⟩⟩ : H) * nH = ⟨j ((n : G)⁻¹ * g * n), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    change (j (n : G))⁻¹ * j g * j (n : G) = j (((n : G)⁻¹ * g) * n)
    exact (by simp only [map_mul, map_inv])
  rw [he, hxg, base]

end Scaling
end NormalizerCharts

section RootChartCongruence

open AlgebraicGeometry CategoryTheory
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalAffineBruhat
open Specs.IntegralSemisimpleModel (Model Integers IntegralPoints integerAlgebra TorusValues torusPoint)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalIwahoriCongruence (cellValue CellValues integralLayer integralRing
  congruenceRing congruenceHom changeRing changeRingHom mapCellValues)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open scoped CategoryTheory.MonObj WithZero ValuativeRel
open ValuativeRel WithZero

open private normalizedValuation_le_one normalizedValuation_lt_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private cellValue_torus finite_monoidHom_of_fg quotient_eq_of_ramification changeRing_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private affineTorusPointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

attribute [local instance] integerAlgebra

private theorem exists_localUniformizer (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ∃ π : 𝒪[K], normalizedValuation K (π : K) = exp (-1) := by
  obtain ⟨x, hx⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization K).1 (exp (-1))
  change normalizedValuation K x = exp (-1) at hx
  exact ⟨⟨x, (normalizedValuation_le_one K x).1 (hx ▸ le_of_lt (exp_lt_one_iff.mpr (by decide)))⟩, hx⟩

private theorem integral_divides_iff {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {x y : 𝒪[K]} (hx : (x : K) ≠ 0) :
    x ∣ y ↔ normalizedValuation K (y : K) ≤ normalizedValuation K (x : K) := by
  let v := normalizedValuation K
  constructor
  · rintro ⟨z, rfl⟩
    change v ((x : K) * (z : K)) ≤ v x
    rw [map_mul]
    exact mul_le_of_le_one_right zero_le ((normalizedValuation_le_one K (z : K)).2 z.property)
  · intro hv
    have hz : v ((y : K) / (x : K)) ≤ 1 := by
      rw [v.map_div, div_le_iff₀ ((map_ne_zero v).2 hx).bot_lt, one_mul]
      exact hv
    refine ⟨⟨_, (normalizedValuation_le_one K _).1 hz⟩, Subtype.ext ?_⟩
    change (y : K) = (x : K) * ((y : K) / (x : K))
    rw [mul_comm, div_mul_cancel₀ _ hx]

private theorem localUniformizer_span {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {π : 𝒪[K]} (hπ : normalizedValuation K (π : K) = exp (-1)) :
    IsLocalRing.maximalIdeal 𝒪[K] = Ideal.span {π} := by
  ext x
  change x ∈ IsLocalRing.maximalIdeal (valuation K).valuationSubring ↔ _
  rw [(valuation K).mem_maximalIdeal_iff, ← normalizedValuation_lt_one K,
    Ideal.mem_span_singleton, integral_divides_iff, hπ]
  · simpa only [← exp_add, neg_add_cancel, exp_zero] using
      (lt_mul_exp_iff_le (x := normalizedValuation K (x : K)) (y := exp (-1 : ℤ)) exp_ne_zero)
  · intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm

private theorem localUniformizer_pow {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {π : 𝒪[K]} (hπ : normalizedValuation K (π : K) = exp (-1)) (n : ℕ) :
    normalizedValuation K ((π ^ n : 𝒪[K]) : K) = exp (-(n : ℤ)) := by
  change normalizedValuation K ((π : K) ^ n) = _
  rw [map_pow, hπ, ← zpow_natCast, ← exp_zsmul]
  congr 1
  simp

private theorem integerLayer_iff {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]) (n : ℕ) :
    x ∈ (IsLocalRing.maximalIdeal 𝒪[K]) ^ n ↔
      normalizedValuation K (x : K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := exists_localUniformizer K
  have hne : ((π ^ n : 𝒪[K]) : K) ≠ 0 := by
    intro hz
    have h := localUniformizer_pow hπ n
    rw [hz, map_zero] at h
    exact exp_ne_zero h.symm
  rw [localUniformizer_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    integral_divides_iff hne, localUniformizer_pow hπ]

private noncomputable def integerRingMapOfValuation {K L : Type*} [Field K] [Field L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    (f : K →+* L) (e : ℕ)
    (hv : ∀ x, normalizedValuation L (f x) = normalizedValuation K x ^ e) :
    𝒪[K] →+* 𝒪[L] :=
  (f.comp (valuation K).valuationSubring.subtype).codRestrict _ (fun x =>
    (normalizedValuation_le_one L _).1 (by
      change normalizedValuation L (f (x : K)) ≤ 1
      rw [hv]
      exact pow_le_one₀ zero_le ((normalizedValuation_le_one K (x : K)).2 x.property)))

private theorem integerRingMap_maximalIdeal {K L : Type*} [Field K] [Field L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    (f : K →+* L) (e : ℕ)
    (hv : ∀ x, normalizedValuation L (f x) = normalizedValuation K x ^ e) :
    Ideal.map (integerRingMapOfValuation f e hv) (IsLocalRing.maximalIdeal 𝒪[K]) =
      (IsLocalRing.maximalIdeal 𝒪[L]) ^ e := by
  obtain ⟨π, hπ⟩ := exists_localUniformizer K
  obtain ⟨ϖ, hϖ⟩ := exists_localUniformizer L
  rw [localUniformizer_span hπ, localUniformizer_span hϖ, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]
  let q := integerRingMapOfValuation f e hv π
  have hq : normalizedValuation L (q : L) = exp (-(e : ℤ)) := by
    change normalizedValuation L (f (π : K)) = _
    rw [hv, hπ, ← zpow_natCast, ← exp_zsmul]
    congr 1
    simp
  have hq' : (q : L) ≠ 0 := by
    intro h
    rw [h, map_zero] at hq
    exact exp_ne_zero hq.symm
  have hϖ' : ((ϖ ^ e : 𝒪[L]) : L) ≠ 0 := by
    intro h
    have hk := localUniformizer_pow hϖ e
    rw [h, map_zero] at hk
    exact exp_ne_zero hk.symm
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, integral_divides_iff hϖ',
      localUniformizer_pow hϖ, hq]
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, integral_divides_iff hq',
      localUniformizer_pow hϖ, hq]

section Congruence

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G : Type u} [Group G] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem cellValue_identity (negative positive : List D.I) :
    cellValue M.toIntegralMarking (integralRing K) negative positive (0, 1, 0) = 1 := by
  rw [cellValue_torus]
  change (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) _ 1 ≫
    M.torus.hom.hom : FieldPoints M K) = 1
  rw [map_one, MonObj.one_comp]

set_option maxHeartbeats 1100000 in
/-- The index of the two marked threshold charts. Precision is measured in
the ring of integers of each parameter field, even when two absolute
coordinates represent one root parameter. -/
theorem rootChartIntersectionIndex [Fintype J]
    (C : LocalRootChart (j := j) A p) (j_injective : Function.Injective j)
    [∀ a, ValuativeRel (C.parameter a)] [∀ a, TopologicalSpace (C.parameter a)]
    [∀ a, IsNonarchimedeanLocalField (C.parameter a)]
    (vP : ∀ a x, C.value a x = normalizedValuation (C.parameter a) x)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos)
    (e : J → ℕ) (he : ∀ a, 0 < e a)
    (hvn : ∀ l x, normalizedValuation K (C.chart.negMap l x) =
      normalizedValuation (C.parameter (C.chart.neg l)) x ^ e (C.chart.neg l))
    (hvp : ∀ l x, normalizedValuation K (C.chart.posMap l x) =
      normalizedValuation (C.parameter (C.chart.pos l)) x ^ e (C.chart.pos l))
    (q : ℕ) (hq : 0 < q) (hres : ∀ a, Nat.card (residue (C.parameter a)) = q)
    (I I' : Subgroup G) (x : V)
    (hbase : ∀ a, 0 ≤ threshold (A.root a p))
    (base : ∀ g, g ∈ I ↔ C.atPoint p g)
    (other : ∀ g, g ∈ I' ↔ C.atPoint x g) :
    (I ⊓ I').relIndex I =
      q ^ ∑ a, (threshold (A.root a x) - threshold (A.root a p)).toNat := by
  classical
  let R := integralRing 𝒪[K]
  let S := integralRing K
  let P (a : J) := 𝒪[C.parameter a]
  let i : R ⟶ S := valuationRingInclusion K
  let lift := changeRingHom M.group i
  let neg (l) := integerRingMapOfValuation (C.chart.negMap l) _ (hvn l)
  let pos (l) := integerRingMapOfValuation (C.chart.posMap l) _ (hvp l)
  let intUnit (ε : Integers.{u}ˣ) : 𝒪[K]ˣ := Units.map (algebraMap Integers.{u} 𝒪[K]).toMonoidHom ε
  let liftT (t : TorusValues D R) : TorusValues D S := (Units.map i.hom.toRingHom).comp t
  let T := {t : TorusValues D R | liftT t ∈ C.chart.torus}
  have hT₀ : (1 : TorusValues D R) ∈ T := by
    have hr : cellValue M.toIntegralMarking S C.negative C.positive (0, 1, 0) ∈ j.range := by
      rw [cellValue_identity]
      exact j.range.one_mem
    obtain ⟨t, _, ht⟩ := (C.rational _).mp hr
    have ht' : t.val = 1 := congrArg (fun z => z.2.1) ht
    change liftT 1 ∈ C.chart.torus
    have h1 : liftT 1 = 1 := by ext a; simp [liftT]
    rw [h1, ← ht']
    exact t.property
  let coords (z : T × (∀ a, P a)) : CellValues D R C.negative C.positive :=
    (fun l => ↑(intUnit (C.chart.negUnit l)) * neg l (z.2 (C.chart.neg l)), z.1.val,
      fun l => ↑(intUnit (C.chart.posUnit l)) * pos l (z.2 (C.chart.pos l)))
  let chart (z : T × (∀ a, P a)) := cellValue M.toIntegralMarking R C.negative C.positive (coords z)
  let hc := ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates
  have hlift (z : T × (∀ a, P a)) :
      lift (chart z) = cellValue M.toIntegralMarking S C.negative C.positive
        (C.chart.coordinates ⟨liftT z.1.val, z.1.property⟩ (fun a => (z.2 a : C.parameter a))) := by
    change changeRing i (cellValue M.toIntegralMarking R C.negative C.positive (coords z)) = _
    refine (hc.2 i (coords z)).trans (congrArg (cellValue M.toIntegralMarking S _ _) ?_)
    apply Prod.ext
    · funext l
      change (algebraMap 𝒪[K] K) (_ * _) = _
      rw [map_mul]
      rfl
    · apply Prod.ext rfl
      funext l
      change (algebraMap 𝒪[K] K) (_ * _) = _
      rw [map_mul]
      rfl
  have hOne : ∃ t, chart (t, 0) = 1 := by
    refine ⟨⟨1, hT₀⟩, ?_⟩
    have hcoords : coords (⟨1, hT₀⟩, 0) = (0, 1, 0) := by
      apply Prod.ext
      · funext l
        change (intUnit (C.chart.negUnit l)).val * neg l 0 = 0
        rw [map_zero, mul_zero]
      · apply Prod.ext
        · rfl
        · funext l
          change (intUnit (C.chart.posUnit l)).val * pos l 0 = 0
          rw [map_zero, mul_zero]
    change cellValue M.toIntegralMarking R C.negative C.positive _ = _
    rw [hcoords, cellValue_torus]
    change (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R 1 ≫
      M.torus.hom.hom : IntegralPoints M.group R) = 1
    rw [map_one, MonObj.one_comp]
  let a (i : J) := (threshold (A.root i p)).toNat
  let b (i : J) := max (a i) (threshold (A.root i x)).toNat
  have hab : a ≤ b := fun i => le_max_left _ _
  have hdepth (t : ℤ) (i : J) (z : P i) :
      C.value i (z : C.parameter i) ≤ exp (-t) ↔ z ∈ IsLocalRing.maximalIdeal (P i) ^ t.toNat := by
    rw [integerLayer_iff, vP]
    by_cases ht : 0 ≤ t
    · rw [Int.toNat_of_nonneg ht]
    · have hle := (normalizedValuation_le_one (C.parameter i) (z : C.parameter i)).2 z.property
      rw [Int.toNat_of_nonpos (le_of_not_ge ht), Int.natCast_zero, neg_zero, exp_zero]
      exact ⟨fun _ => hle, fun h => h.trans (one_le_exp_iff.mpr (by omega))⟩
  have hchartK (z : T × (∀ a, P a)) (g : G) (hg : lift (chart z) = j g) (y : V) :
      C.atPoint y g ↔ ∀ i, z.2 i ∈ IsLocalRing.maximalIdeal (P i) ^ (threshold (A.root i y)).toNat := by
    let t : C.chart.torus := ⟨liftT z.1.val, z.1.property⟩
    let u (a : J) : C.parameter a := z.2 a
    have hcoord := rootChartCoordinates_injective C covers
    have hz : cellValue M.toIntegralMarking S C.negative C.positive (C.chart.coordinates t u) = j g :=
      (hlift z).symm.trans hg
    have htu (χ) : normalizedValuation K (t.val χ : K) = 1 := by
      let s := (valuation K).valuationSubring.unitGroupMulEquiv.symm (z.1.val χ)
      exact (valuation_unit_iff _).2 ((Valuation.mem_unitGroup_iff (v := valuation K) (x := s.val)).1 s.property)
    let hcS := hc.1 S
    have eq_coords (w : C.chart.torus × (∀ a, C.parameter a))
        (hw : cellValue M.toIntegralMarking S C.negative C.positive
          (C.chart.coordinates w.1 w.2) = j g) : w = (t, u) :=
      @hcoord w (t, u) (@hcS (C.chart.coordinates w.1 w.2) (C.chart.coordinates t u)
        (hw.trans hz.symm))
    constructor
    · rintro ⟨w, ⟨hw, ht, hd⟩, _⟩
      have hpairs := eq_coords w hw
      have hfields : w.2 = u := congrArg Prod.snd hpairs
      rw [hfields] at hd
      exact fun i => (hdepth _ _ _).1 (hd i)
    · intro h
      exact ⟨(t, u), ⟨hz, htu, fun i => (hdepth _ _ _).2 (h i)⟩,
        fun w hw => eq_coords w hw.1⟩
  have integral_coords (g : G) (hg : C.atPoint p g) :
      ∃ z : T × (∀ a, P a), lift (chart z) = j g := by
    obtain ⟨⟨t, u⟩, ⟨hval, htu, hu⟩, _⟩ := hg
    let tO : TorusValues D R := (valuation K).valuationSubring.unitGroupMulEquiv.toMonoidHom.comp
      (t.val.codRestrict _ (fun χ => (Valuation.mem_unitGroup_iff (v := valuation K) (x := _)).2
        ((valuation_unit_iff _).1 (htu χ))))
    have hO : liftT tO = t.val := by ext χ; rfl
    let xO (a₀ : J) : P a₀ := ⟨u a₀, (normalizedValuation_le_one (C.parameter a₀) _).1
      ((vP a₀ _ ▸ hu a₀).trans (exp_le_one_iff.mpr (neg_nonpos.mpr (hbase a₀))))⟩
    have htO : tO ∈ T := by
      change liftT tO ∈ C.chart.torus
      rw [hO]
      exact t.property
    refine ⟨(⟨tO, htO⟩, xO), (hlift _).trans ?_⟩
    have he : (⟨liftT tO, htO⟩ : C.chart.torus) = t := Subtype.ext hO
    rw [he]
    exact hval
  let I₀ := (I.map j).comap lift
  let H₀ := ((I ⊓ I').map j).comap lift
  have hHI : H₀ ≤ I₀ := Subgroup.comap_mono (Subgroup.map_mono inf_le_left)
  have hi : Function.Injective lift :=
    changeRing_injective M.toIntegralMarking i Subtype.val_injective
  have base₀ (g) : g ∈ I₀ ↔ ∃ (t : T) (u : ∀ l, integralLayer (P l) (a l)),
      chart (t, fun l => u l) = g := by
    constructor
    · rintro ⟨y, hy, he⟩
      obtain ⟨⟨t, u⟩, hu⟩ := integral_coords y ((base _).1 hy)
      have hd := (hchartK (t, u) y hu p).1 ((base _).1 hy)
      exact ⟨t, fun l => ⟨u l, hd l⟩, hi (hu.trans he)⟩
    · rintro ⟨t, u, rfl⟩
      have hrange := (C.rational (C.chart.coordinates ⟨liftT t.val, t.property⟩
        (fun l => ((u l : P l) : C.parameter l)))).2 ⟨_, _, rfl⟩
      have hr : lift (chart (t, fun l => u l)) ∈ j.range :=
        (hlift (t, fun l => u l)).symm ▸ hrange
      obtain ⟨g, hg⟩ := hr
      exact ⟨g, (base _).2 ((hchartK _ _ hg.symm p).2 (fun l => (u l).property)), hg⟩
  have both₀ (g) : g ∈ H₀ ↔ ∃ (t : T) (u : ∀ l, integralLayer (P l) (b l)),
      chart (t, fun l => u l) = g := by
    constructor
    · rintro ⟨y, ⟨hy, hy'⟩, he⟩
      obtain ⟨⟨t, u⟩, hu⟩ := integral_coords y ((base _).1 hy)
      have ha := (hchartK (t, u) y hu p).1 ((base _).1 hy)
      have hb := (hchartK (t, u) y hu x).1 ((other _).1 hy')
      refine ⟨t, fun l => ⟨u l, ?_⟩, hi (hu.trans he)⟩
      rcases le_total (a l) (threshold (A.root l x)).toNat with h | h
      · simpa only [b, max_eq_right h] using hb l
      · simpa only [b, max_eq_left h] using ha l
    · rintro ⟨t, u, rfl⟩
      have hrange := (C.rational (C.chart.coordinates ⟨liftT t.val, t.property⟩
        (fun l => ((u l : P l) : C.parameter l)))).2 ⟨_, _, rfl⟩
      have hr : lift (chart (t, fun l => u l)) ∈ j.range :=
        (hlift (t, fun l => u l)).symm ▸ hrange
      obtain ⟨g, hg⟩ := hr
      exact ⟨g, ⟨(base _).2 ((hchartK _ _ hg.symm p).2
        (fun l => Ideal.pow_le_pow_right (le_max_left _ _) (u l).property)),
        (other _).2 ((hchartK _ _ hg.symm x).2
        (fun l => Ideal.pow_le_pow_right (le_max_right _ _) (u l).property))⟩, hg⟩
  let n := 1 + ∑ l, b l * e l
  let m (l : J) := (n + e l - 1) / e l
  have hbm : b ≤ m := by
    intro l
    have hh := Finset.single_le_sum (f := fun l => b l * e l)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    apply (Nat.le_div_iff_mul_le (he l)).2
    dsimp [m, n]
    omega
  let Q := congruenceRing R n
  let red := changeRingHom M.group (congruenceHom R n)
  let truncateT (t : T) : TorusValues D Q := (Units.map (congruenceHom R n).hom.toRingHom).comp t.val
  let tr (t : T) : Set.range truncateT := ⟨truncateT t, t, rfl⟩
  have hTr : Function.Surjective tr := fun ⟨_, ⟨t, ht⟩⟩ => ⟨t, Subtype.ext ht⟩
  let _ : Finite Q := Nat.finite_of_card_ne_zero (by
    change Nat.card (𝒪[K] ⧸ (IsLocalRing.maximalIdeal 𝒪[K]) ^ n) ≠ 0
    rw [residuePowerCounts]
    exact pow_ne_zero _ (Nat.ne_of_gt Nat.card_pos))
  let _ : Group.FG (Multiplicative D.X) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
  let _ : Finite (TorusValues D Q) := finite_monoidHom_of_fg
  let _ : Nonempty (Set.range truncateT) := ⟨tr ⟨1, hT₀⟩⟩
  have hEq (z w : T × (∀ a, P a)) :
      red (chart z) = red (chart w) ↔ tr z.1 = tr w.1 ∧
        ∀ l, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (z.2 l) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (w.2 l) := by
    change changeRing (congruenceHom R n) (cellValue M.toIntegralMarking R C.negative C.positive (coords z)) =
      changeRing (congruenceHom R n) (cellValue M.toIntegralMarking R C.negative C.positive (coords w)) ↔ _
    rw [hc.2, hc.2, (hc.1 Q).eq_iff]
    have factor (l : J) (f : P l →+* R) (u : Rˣ)
        (hf : Ideal.map f (IsLocalRing.maximalIdeal (P l)) = IsLocalRing.maximalIdeal R ^ e l) :
        (congruenceHom R n).hom (u.val * f (z.2 l)) = (congruenceHom R n).hom (u.val * f (w.2 l)) ↔
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (z.2 l) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (w.2 l) := by
      let f₀ := (congruenceHom R n).hom.toRingHom
      change f₀ (u.val * f (z.2 l)) = f₀ (u.val * f (w.2 l)) ↔
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (z.2 l) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P l) ^ m l) (w.2 l)
      rw [map_mul, map_mul, (u.isUnit.map f₀).mul_right_inj]
      exact quotient_eq_of_ramification f n (m l)
        (ExceptionalIwahoriCongruence.ramifiedTruncation f (e l) n (he l) hf) (z.2 l) (w.2 l)
    have hn (l) := factor (C.chart.neg l) (neg l) (intUnit (C.chart.negUnit l))
      (integerRingMap_maximalIdeal _ _ (hvn l))
    have hp (l) := factor (C.chart.pos l) (pos l) (intUnit (C.chart.posUnit l))
      (integerRingMap_maximalIdeal _ _ (hvp l))
    constructor
    · intro h
      refine ⟨Subtype.ext (congrArg (fun t => t.2.1) h), ?_⟩
      intro l
      rcases covers l with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact (hn s).1 (congrArg (fun t => t.1 s) h)
      · exact (hp s).1 (congrArg (fun t => t.2.2 s) h)
    · rintro ⟨ht, hr⟩
      exact Prod.ext (funext fun l => (hn l).2 (hr (C.chart.neg l)))
        (Prod.ext (congrArg Subtype.val ht) (funext fun l => (hp l).2 (hr (C.chart.pos l))))
  -- The congruence theorem puts the root labels and the coordinate rings in
  -- one universe. Reindex by a lifted finite set to include the folded labels.
  let B := ULift.{u} (Fin (Fintype.card J))
  let k : B ≃ J := Equiv.ulift.trans (Fintype.equivFin J).symm
  let π := Equiv.piCongrLeft (fun l => (P l : Type u)) k
  let chart' (z : T × (∀ l : B, P (k l))) := chart (z.1, π z.2)
  have layers (d : J → ℕ) (g : _) :
      (∃ (t : T) (z : ∀ l : J, integralLayer (P l) (d l)), chart (t, fun l => z l) = g) ↔
      ∃ (t : T) (z : ∀ l : B, integralLayer (P (k l)) (d (k l))), chart' (t, fun l => z l) = g := by
    constructor
    · rintro ⟨t, z, hz⟩
      refine ⟨t, fun l => z (k l), ?_⟩
      change chart (t, π (π.symm (fun l => z l))) = g
      rw [Equiv.apply_symm_apply]
      exact hz
    · rintro ⟨t, z, hz⟩
      refine ⟨t, Equiv.piCongrLeft (fun l => integralLayer (P l) (d l)) k z, ?_⟩
      refine (congrArg (fun v => chart (t, v)) ?_).trans hz
      funext l
      obtain ⟨l, rfl⟩ := k.surjective l
      simp only [π, Equiv.piCongrLeft_apply_apply]
  obtain ⟨t, ht⟩ := hOne
  have ht' : chart' (t, 0) = 1 := by
    refine (congrArg (fun v => chart (t, v)) ?_).trans ht
    funext l
    obtain ⟨l, rfl⟩ := k.surjective l
    simp only [π, Equiv.piCongrLeft_apply_apply, Pi.zero_apply]
  have hEq' (z w : T × (∀ l : B, P (k l))) :
      red (chart' z) = red (chart' w) ↔ tr z.1 = tr w.1 ∧
        ∀ l, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P (k l)) ^ m (k l)) (z.2 l) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (P (k l)) ^ m (k l)) (w.2 l) := by
    simp only [chart']
    rw [hEq]
    refine and_congr_right' ?_
    constructor
    · intro h l
      simpa only [π, Equiv.piCongrLeft_apply_apply] using h (k l)
    · intro h l
      obtain ⟨l, rfl⟩ := k.surjective l
      simpa only [π, Equiv.piCongrLeft_apply_apply] using h l
  have hcnt := (ExceptionalIwahoriCongruence.indexByIndependentCongruence red I₀ H₀ hHI
    (fun l => (P (k l) : Type u)) (a ∘ k) (b ∘ k) (m ∘ k) (fun l => hab (k l))
    (fun l => hbm (k l)) q hq (fun l => hres (k l)) chart' tr hTr ⟨t, ht'⟩
    (fun g => (base₀ g).trans (layers a g)) (fun g => (both₀ g).trans (layers b g)) hEq').2
  have hIr : I₀.map lift = I.map j := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    rintro g ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := integral_coords y ((base _).1 hy)
    exact ⟨chart z, hz⟩
  change ((I ⊓ I').map j |>.comap lift).relIndex I₀ = _ at hcnt
  rw [Subgroup.relIndex_comap, hIr, Subgroup.relIndex_map_map_of_injective _ _ j_injective] at hcnt
  rw [hcnt]
  congr 1
  change ∑ l : B, (b (k l) - a (k l)) = _
  rw [k.sum_comp (fun l => b l - a l)]
  apply Finset.sum_congr rfl
  intro l _
  dsimp [a, b]
  have h := hbase l
  omega

end Congruence
end RootChartCongruence

section RankOneProducts

open AlgebraicGeometry CategoryTheory
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalAffineBruhat
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalIwahoriCongruence (cellValue integralRing)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (wallMatrix rankOneMatrixWord)
open Specs.IntegralRootRelations (upper lower diagonal)
open scoped CategoryTheory.MonObj Matrix WithZero Pointwise ValuativeRel
open ValuativeRel WithZero

open private normalizedValuation_le_one normalizedValuation_lt_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

attribute [local instance] integerAlgebra

private theorem threshold_le_iff (r : ℚ) (l : ℤ) :
    threshold r ≤ l ↔ 0 < r + (l : ℚ) := by
  rw [threshold, ← Int.lt_iff_add_one_le, Int.floor_lt, neg_lt_iff_pos_add, add_comm]

private theorem upperHom_mul {K : Type*} [Field K] (x y : K) :
    upper (x + y) = upper x * upper y := by
  apply Subtype.val_injective
  change (!![1, x + y; 0, 1] : Matrix (Fin 2) (Fin 2) K) =
    !![1, x; 0, 1] * !![1, y; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem wallMatrix_eq_wallLift {P : Type*} [Field P] (t : Pˣ) : wallMatrix t = wallLift t := by
  apply Subtype.val_injective
  change (rankOneMatrixWord (-t)).val = _
  rw [(ExceptionalMarkedRootDescent.wallMatrixRelations (-t) (-t)).1]
  simp only [Units.val_neg, inv_neg, neg_neg]
  rfl

section WallProducts

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

private theorem simpleWall_threshold (a : A.SimpleWall p) :
    threshold (A.root a.val.1 p) = a.val.2 := by
  rcases a.property with ⟨hpos, x, hx, hother⟩
  change 0 < A.root a.val.1 p + (a.val.2 : ℚ) at hpos
  have hle := (threshold_le_iff _ _).2 hpos
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  let b : J × ℤ := (a.val.1, a.val.2 - 1)
  have hpos' : A.positive p b := (threshold_le_iff _ _).1 (Int.le_sub_one_of_lt hlt)
  have hne : b ≠ a.val := fun h => by
    have hl := congrArg Prod.snd h
    change a.val.2 - 1 = a.val.2 at hl
    omega
  have h := hother b hpos' hne
  change A.root a.val.1 x + (a.val.2 : ℚ) = 0 at hx
  change 0 < A.root a.val.1 x + ((a.val.2 - 1 : ℤ) : ℚ) at h
  push_cast at h
  linarith

private theorem simpleWall_value_reflect (C : LocalComparison (j := j) (Wf := Wf) A p)
    (a : A.SimpleWall p) (x : V) :
    A.wallValue a.val ((C.coxeter.coxeter.simple a).val x) = - A.wallValue a.val x := by
  rw [C.coxeter.simple_eq]
  change A.wallValue a.val (A.wallReflection a.val.1 a.val.2 x) = _
  rw [(ExceptionalAffineRootSystems.affineGroupNormalForms A).1 a.val.1 a.val.2 x]
  change A.root a.val.1 (x - (A.root a.val.1 x + (a.val.2 : ℚ)) • A.coroot a.val.1) +
    (a.val.2 : ℚ) = -(A.root a.val.1 x + a.val.2)
  rw [map_sub, map_smul, A.diagonal, smul_eq_mul]
  ring

private theorem simpleWall_reflectedThreshold (C : LocalComparison (j := j) (Wf := Wf) A p)
    (a : A.SimpleWall p) :
    threshold (A.root a.val.1 ((C.coxeter.coxeter.simple a).val p)) = a.val.2 + 1 := by
  have hmin := simpleWall_threshold a
  have hp0 : 0 < A.wallValue a.val p := a.property.1
  have hp1 : A.wallValue a.val p < 1 := by
    have hn : ¬ 0 < A.wallValue (a.val.1, a.val.2 - 1) p := by
      intro h
      have hle := (threshold_le_iff _ _).2 h
      rw [hmin] at hle
      omega
    have hne : A.root a.val.1 p + (a.val.2 : ℚ) ≠ 1 := by
      intro h
      apply C.geometry.regular a.val.1
      refine ⟨1 - a.val.2, ?_⟩
      push_cast
      change A.root a.val.1 p + (a.val.2 : ℚ) = 1 at h
      linarith
    change ¬ 0 < A.root a.val.1 p + ((a.val.2 - 1 : ℤ) : ℚ) at hn
    change A.root a.val.1 p + (a.val.2 : ℚ) < 1
    push_cast at hn
    exact lt_of_le_of_ne (by linarith [le_of_not_gt hn]) hne
  apply le_antisymm
  · apply (threshold_le_iff _ _).2
    have he := simpleWall_value_reflect C a p
    change A.root a.val.1 ((C.coxeter.coxeter.simple a).val p) + (a.val.2 : ℚ) = _ at he
    push_cast
    linarith
  · apply Int.add_one_le_iff.mpr
    apply not_le.mp
    rw [threshold_le_iff]
    change ¬ 0 < A.wallValue a.val ((C.coxeter.coxeter.simple a).val p)
    rw [simpleWall_value_reflect C a p]
    linarith

open scoped Classical in
private theorem chartUpper_iff (C : LocalRootChart (j := j) A p)
    (covers : ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos)
    (a : J) (r : Matrix.SpecialLinearGroup (Fin 2) (C.parameter a) →* G)
    (c : (C.parameter a)ˣ) (u : C.chart.torus) (hu : u.val = 1) (hc : C.value a c = 1)
    (hUpper : ∀ z : C.parameter a, j (r (upper z)) =
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (C.chart.coordinates u (Function.update (fun _ => 0) a ((c : C.parameter a) * z))))
    (x : V) (z : C.parameter a) :
    C.atPoint x (r (upper z)) ↔ C.value a z ≤ exp (-threshold (A.root a x)) := by
  let t := Function.update (fun i => (0 : C.parameter i)) a ((c : C.parameter a) * z)
  have hinj := rootChartCoordinates_injective C covers
  have hchart := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates).1 (integralRing K)
  have hval : C.value a (t a) = C.value a z := by
    simp only [t, Function.update_self, map_mul, hc, one_mul]
  constructor
  · rintro ⟨w, hw, _⟩
    have he : w = (u, t) := hinj (hchart (hw.1.trans (hUpper z)))
    rw [he] at hw
    simpa only [hval] using hw.2.2 a
  · intro hz
    refine ⟨(u, t), ⟨(hUpper z).symm, fun χ => by simp [hu], ?_⟩, ?_⟩
    · intro i
      by_cases h : i = a
      · subst i
        rwa [hval]
      · simpa only [t, Function.update_of_ne h, map_zero] using (zero_le : 0 ≤ exp (-threshold (A.root i x)))
    · intro w hw
      exact hinj (hchart (hw.1.trans (hUpper z)))

open scoped Classical in
/-- Compute the simple multiplication in the given point group. The
filtration and the simple intersection index refer to the very Iwahori
and normalizer used in the double cosets. -/
theorem wallProductFromRankOne
    (C : LocalComparison (j := j) (Wf := Wf) A p)
    (a : A.SimpleWall p) (q : ℕ) (hq : 0 < q)
    [ValuativeRel (C.chart.parameter a.val.1)] [TopologicalSpace (C.chart.parameter a.val.1)]
    [IsNonarchimedeanLocalField (C.chart.parameter a.val.1)]
    (vP : ∀ z, C.chart.value a.val.1 z = normalizedValuation (C.chart.parameter a.val.1) z)
    (hres : Nat.card (residue (C.chart.parameter a.val.1)) = q)
    (covers : ∀ i, i ∈ Set.range C.chart.chart.neg ∪ Set.range C.chart.chart.pos)
    (translated : ∀ (n : C.N) (g : G),
      g ∈ C.I.map (MulAut.conj (n : G)).toMonoidHom ↔ C.chart.atPoint (C.affine n p) g)
    (r : Matrix.SpecialLinearGroup (Fin 2) (C.chart.parameter a.val.1) →* G)
    (t c : (C.chart.parameter a.val.1)ˣ) (u : C.chart.chart.torus)
    (hu : u.val = 1) (hc : C.chart.value a.val.1 c = 1)
    (upper_at : ∀ z : C.chart.parameter a.val.1, j (r (upper z)) =
      cellValue M.toIntegralMarking (integralRing K) C.chart.negative C.chart.positive
        (C.chart.chart.coordinates u (Function.update (fun _ => 0) a.val.1 ((c : C.chart.parameter a.val.1) * z))))
    (depth : C.chart.value a.val.1 t = exp (-a.val.2))
    (wall : (C.lift (C.coxeter.coxeter.simple a) : G) = r (wallMatrix t))
    (diag_mem : ∀ z : (C.chart.parameter a.val.1)ˣ, C.chart.value a.val.1 z = 1 → r (diagonal z) ∈ C.I)
    (idx : (conjugateIntersection C.I (C.lift (C.coxeter.coxeter.simple a) : G)).index = q)
    (w : A.affineWeylGroup) :
    letI := C.coxeter.action
    let s := C.coxeter.coxeter.simple a
    C.cell w * C.cell s =
      if A.positive p (w • a.val) then C.cell (w * s) else C.cell (w * s) ∪ C.cell w := by
  classical
  let _ := C.coxeter.action
  let i := a.val.1
  let l := a.val.2
  let s := C.coxeter.coxeter.simple a
  let n := C.lift w
  let m := C.lift s
  let P := C.chart.parameter i
  let O := 𝒪[P]
  let v := C.chart.value i
  let ℘ := IsLocalRing.maximalIdeal O
  let h : Multiplicative O →* G := MonoidHom.mk'
    (fun z => r (upper ((t : P) * (z.toAdd : P)))) (by
      intro z z'
      change r (upper ((t : P) * ((z.toAdd : P) + (z'.toAdd : P)))) = _
      rw [mul_add, upperHom_mul, map_mul])
  let U := h.range
  let I' := C.I.map (MulAut.conj (m : G)).toMonoidHom
  let Uplus := U ⊓ I'
  have hv (z : Multiplicative O) : v ((t : P) * (z.toAdd : P)) = exp (-l) * v (z.toAdd : P) := by
    rw [map_mul, depth]
  have hchart (b : C.N) (z : P) :
      r (upper z) ∈ C.I.map (MulAut.conj (b : G)).toMonoidHom ↔
        v z ≤ exp (-threshold (A.root i (C.affine b p))) :=
    (translated b _).trans (chartUpper_iff C.chart covers i r c u hu hc upper_at (C.affine b p) z)
  have hbase (z : P) : r (upper z) ∈ C.I ↔ v z ≤ exp (-l) := by
    have h := hchart 1 z
    have h1 : C.affine (1 : C.N) p = p := by rw [map_one]; rfl
    have h2 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext y
      change (1 : G) * y * (1 : G)⁻¹ = y
      simp only [one_mul, inv_one, mul_one]
    rw [h1, simpleWall_threshold a, Subgroup.coe_one, h2, Subgroup.map_id] at h
    exact h
  have hm (z : P) : r (upper z) ∈ I' ↔ v z ≤ exp (-(l + 1)) := by
    have h := hchart m z
    rwa [C.lift_label, simpleWall_reflectedThreshold C a] at h
  have hU : U ≤ C.I := by
    rintro _ ⟨z, rfl⟩
    apply (hbase _).2
    rw [hv]
    apply mul_le_of_le_one_right zero_le
    rw [vP]
    exact (normalizedValuation_le_one P _).2 z.toAdd.property
  have hcrit (z : Multiplicative O) : h z ∈ I' ↔ v (z.toAdd : P) < 1 := by
    change r (upper ((t : P) * (z.toAdd : P))) ∈ I' ↔ _
    rw [hm, hv, show -(l + 1) = -l + (-1) by omega, exp_add]
    exact ((mul_le_mul_iff_right₀ (exp_pos (a := -l))).trans
      (by
        have hh := lt_mul_exp_iff_le (x := v (z.toAdd : P)) (y := exp (-1 : ℤ)) exp_ne_zero
        simpa only [← exp_add, show (-1 : ℤ) + 1 = 0 by decide, exp_zero] using hh.symm))
  have hindex : I'.relIndex U = q := by
    let f : Multiplicative O →* Multiplicative (residue P) :=
      (Ideal.Quotient.mk ℘).toAddMonoidHom.toMultiplicative
    have hf : Function.Surjective f := fun y =>
      (Ideal.Quotient.mk_surjective (I := ℘) y.toAdd)
    have hfK : I'.comap h = f.ker := by
      ext z
      change h z ∈ I' ↔ Ideal.Quotient.mk ℘ z.toAdd = 0
      rw [hcrit, vP, Ideal.Quotient.eq_zero_iff_mem]
      exact (normalizedValuation_lt_one P _).trans (valuation P).mem_maximalIdeal_iff.symm
    calc
      I'.relIndex U = (I'.comap h).relIndex ⊤ := by rw [Subgroup.relIndex_comap, Subgroup.map_top]
      _ = q := by
        rw [Subgroup.relIndex_top_right, hfK, ← hres]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hJ (b : G) : b ∈ I' ↔ (m : G)⁻¹ * b * m ∈ C.I := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  let L := C.I ⊓ I'
  have hIidx : L.relIndex C.I = q := by
    change (L.subgroupOf C.I).index = q
    have he : L.subgroupOf C.I = conjugateIntersection C.I (m : G) := by
      ext z
      change ((z : G) ∈ C.I ∧ (z : G) ∈ I') ↔ (m : G)⁻¹ * (z : G) * ((m : G)⁻¹)⁻¹ ∈ C.I
      rw [inv_inv, ← hJ]
      exact ⟨And.right, fun h => ⟨z.property, h⟩⟩
    rw [he]
    exact idx
  have hLUidx : L.relIndex U = q := by
    have he : L.subgroupOf U = I'.subgroupOf U := by
      ext z
      exact ⟨And.right, fun h => ⟨hU z.property, h⟩⟩
    change (L.subgroupOf U).index = _
    rw [he]
    exact hindex
  have hFactor (x : G) (hx : x ∈ C.I) :
      ∃ u ∈ U, ∃ z ∈ C.I, (m : G)⁻¹ * z * m ∈ C.I ∧ x = u * z := by
    obtain ⟨u, hu, z, hz, he⟩ := factorizationOfRelativeIndex C.I U L hU
      (hLUidx.trans hIidx.symm) (hIidx ▸ hq) x hx
    exact ⟨u, hu, z, hz.1, (hJ _).1 hz.2, he⟩
  let d := fun g : G => DoubleCoset.doubleCoset g C.I C.I
  have hLabels : d ((n : G) * m) = C.cell (w * s) := by
    apply sameLabel_doubleCoset C (n := n * m) (m := C.lift (w * s))
    rw [map_mul, C.lift_label, C.lift_label, C.lift_label]
    rfl
  have hProd := rankOneDoubleCosetProduct C.I U Uplus (n : G) (m : G) hU hFactor
  have hWall : (m : G) = r (wallLift t) := wall.trans (congrArg r (wallMatrix_eq_wallLift t))
  have hconj (b : C.N) (x : G) :
      ((b : G) * x * (b : G)⁻¹ ∈ C.I) ↔
        x ∈ C.I.map (MulAut.conj ((b⁻¹ : C.N) : G)).toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp
  change d (n : G) * d (m : G) =
    if A.positive p (w • a.val) then C.cell (w * s) else C.cell (w * s) ∪ d (n : G)
  by_cases hpos : A.positive p (w • a.val)
  · rw [ite_eq_left hpos, ← hLabels]
    apply hProd.1
    rintro x ⟨z, rfl⟩
    rw [hconj]
    apply (hchart n⁻¹ _).2
    have hp : 0 < A.wallValue a.val (C.affine (n⁻¹) p) := by
      rw [map_inv, C.lift_label, AffineEquiv.inv_def, ← C.coxeter.equation w a.val p]
      exact hpos
    have hle := (threshold_le_iff _ _).2 hp
    change threshold (A.root i (C.affine n⁻¹ p)) ≤ l at hle
    exact ((hbase _).1 (hU ⟨z, rfl⟩)).trans (exp_le_exp.mpr (neg_le_neg hle))
  · rw [ite_eq_right hpos, ← hLabels]
    apply hProd.2
    · exact fun x hx => (hJ _).1 hx.2
    · rintro x ⟨z, rfl⟩ hnot
      have hz : v (z.toAdd : P) = 1 := by
        apply le_antisymm
        · rw [vP]
          exact (normalizedValuation_le_one P _).2 z.toAdd.property
        · exact le_of_not_gt fun hlt => hnot ⟨⟨z, rfl⟩, (hcrit z).2 hlt⟩
      have hvz : v ((t : P) * (z.toAdd : P)) = exp (-l) := by
        rw [hv, hz, mul_one]
      have hne : (t : P) * (z.toAdd : P) ≠ 0 := by
        intro he
        rw [he, map_zero] at hvz
        exact exp_ne_zero hvz.symm
      let t' := Units.mk0 ((t : P) * (z.toAdd : P)) hne
      let x' : P := - (t : P)^2 / (t' : P)
      have ht' : v (t' : P) = exp (-l) := hvz
      have hvx' : v x' = exp (-l) := by
        change v (-(t : P)^2 / (t' : P)) = _
        rw [map_div₀, Valuation.map_neg, map_pow, depth, ht', sq, mul_div_cancel_right₀ _ exp_ne_zero]
      have hd : v (↑(t' * t⁻¹) : P) = 1 := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, depth, ht',
          mul_inv_cancel₀ exp_ne_zero]
      have hmul : h z * (m : G) = r (lower (↑(t'⁻¹) : P)) *
          r (diagonal (t' * t⁻¹)) * r (upper x') := by
        change r (upper (t' : P)) * (m : G) = _
        rw [hWall, ← map_mul, rankOneWallMultiplication, map_mul, map_mul]
      have hlower : r (lower (↑(t'⁻¹) : P)) = (m : G)⁻¹ * r (upper x') * m := by
        have hh := (rankOneWallConjugation t).1 x'
        have he : -(↑t⁻¹ : P)^2 * x' = (↑t'⁻¹ : P) := by
          simp only [x', Units.val_inv_eq_inv_val]
          field_simp
        rw [he] at hh
        have h' := congrArg r hh
        simp only [map_mul, ← hWall] at h'
        calc
          _ = (m : G)⁻¹ * ((m : G) * r (lower (↑(t'⁻¹) : P))) := by simp
          _ = _ := by rw [← h', mul_assoc]
      have hleft : (n : G) * r (lower (↑(t'⁻¹) : P)) * (n : G)⁻¹ ∈ C.I := by
        rw [hlower, show (n : G) * ((m : G)⁻¹ * r (upper x') * m) * (n : G)⁻¹ =
          ((n * m⁻¹ : C.N) : G) * r (upper x') * (((n * m⁻¹ : C.N) : G)⁻¹) by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group, hconj]
        apply (hchart (n * m⁻¹)⁻¹ _).2
        have hn : A.wallValue (w • a.val) p < 0 := by
          by_contra! h
          have h0 := le_antisymm (le_of_not_gt hpos) h
          apply C.geometry.regular (w • a.val).1
          refine ⟨-(w • a.val).2, ?_⟩
          rw [Int.cast_neg]
          change A.root (w • a.val).1 p + ((w • a.val).2 : ℚ) = 0 at h0
          linarith
        have hpa : 0 < A.wallValue a.val (C.affine ((n * m⁻¹)⁻¹) p) := by
          rw [mul_inv_rev, inv_inv, map_mul, map_inv, C.lift_label, C.lift_label,
            AffineEquiv.coe_mul, Function.comp_apply, simpleWall_value_reflect C a,
            AffineEquiv.inv_def, ← C.coxeter.equation w a.val p]
          exact neg_pos.mpr hn
        rw [hvx']
        exact exp_le_exp.mpr (neg_le_neg ((threshold_le_iff _ _).2 hpa))
      refine DoubleCoset.mem_doubleCoset.mpr ⟨_, hleft, _,
        C.I.mul_mem (diag_mem _ hd) ((hbase _).2 hvx'.le), ?_⟩
      symm
      calc
        ((n : G) * r (lower (↑(t'⁻¹) : P)) * (n : G)⁻¹) * n *
            (r (diagonal (t' * t⁻¹)) * r (upper x')) =
          (n : G) * (r (lower (↑(t'⁻¹) : P)) * r (diagonal (t' * t⁻¹)) * r (upper x')) := by group
        _ = (n : G) * h z * (m : G) := by rw [← hmul, mul_assoc]
    · let z : Multiplicative O := Multiplicative.ofAdd 1
      refine ⟨h z, ⟨z, rfl⟩, fun hz => ?_⟩
      have hh := (hcrit z).1 hz.2
      change v 1 < 1 at hh
      rw [map_one] at hh
      exact (lt_irrefl _ hh)

end WallProducts
end RankOneProducts


section SplitAssembly

open Specs.ExceptionalAffineBruhat
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots threshold)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.IntegralRootRelations (upper diagonal)
open ValuativeRel WithZero
open scoped BigOperators
open Specs.IntegralSemisimpleModel (integerAlgebra)
attribute [local instance] integerAlgebra
open scoped Pointwise WithZero CategoryTheory.MonObj

section LocalAssembly

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

private theorem alcoveSimpleLabels_injective (C : LocalComparison (j := j) (Wf := Wf) A p) :
    Function.Injective C.coxeter.coxeter.simple := by
  let _ := C.coxeter.action
  let S := C.coxeter.walls
  intro a b he
  apply Subtype.ext
  rw [← C.coxeter.simple_wall a, ← C.coxeter.simple_wall b]
  by_contra hab
  have h := S.simple_preserves b (S.simple_positive a) hab
  rw [← he, S.simple_opposite a, S.opposite_positive] at h
  exact h (S.simple_positive a)

private noncomputable def withSimpleLifts (C : LocalComparison (j := j) (Wf := Wf) A p)
    (n : A.SimpleWall p → C.N) (hn : ∀ a, C.affine (n a) = (C.coxeter.coxeter.simple a).val) :
    LocalComparison (j := j) (Wf := Wf) A p := by
  classical
  let L (w : A.affineWeylGroup) :=
    if h : ∃ a, C.coxeter.coxeter.simple a = w then n h.choose else C.lift w
  refine { C with lift := L, lift_label := ?_ }
  intro w
  dsimp only [L]
  split
  · rename_i h
    exact (hn h.choose).trans (congrArg Subtype.val h.choose_spec)
  · exact C.lift_label w

private theorem withSimpleLifts_apply (C : LocalComparison (j := j) (Wf := Wf) A p)
    (n : A.SimpleWall p → C.N) (hn : ∀ a, C.affine (n a) = (C.coxeter.coxeter.simple a).val)
    (a : A.SimpleWall p) : (withSimpleLifts C n hn).lift (C.coxeter.coxeter.simple a) = n a := by
  classical
  let h : ∃ b, C.coxeter.coxeter.simple b = C.coxeter.coxeter.simple a := ⟨a, rfl⟩
  change (if h : ∃ b, C.coxeter.coxeter.simple b = C.coxeter.coxeter.simple a then
    n h.choose else C.lift (C.coxeter.coxeter.simple a)) = n a
  rw [dite_eq_left h, alcoveSimpleLabels_injective C h.choose_spec]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem rootChart_covers (C : LocalRootChart (j := j) A p)
    (surj : Function.Surjective C.direction) :
    ∀ a, a ∈ Set.range C.chart.neg ∪ Set.range C.chart.pos := by
  intro a
  obtain ⟨i, rfl⟩ := surj a
  by_cases hi : D.base.IsPos i
  · obtain ⟨l, hl, he⟩ := List.mem_iff_getElem.mp ((C.positive_enumerates.2 i).mpr hi)
    exact Or.inr ⟨⟨l, hl⟩, (C.pos_slots _).trans (congrArg C.direction he)⟩
  · obtain ⟨l, hl, he⟩ := List.mem_iff_getElem.mp ((C.negative_enumerates.2 i).mpr hi)
    exact Or.inl ⟨⟨l, hl⟩, (C.neg_slots _).trans (congrArg C.direction he)⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem rootChart_baseThreshold_nonneg (C : LocalRootChart (j := j) A p) (a : J) :
    0 ≤ threshold (A.root a p) := by
  by_cases h : ∃ i, C.direction i = a ∧ D.base.IsPos i
  · rw [C.signs.threshold_positive a h]
  · rw [C.signs.threshold_negative a h]
    exact zero_le_one

private theorem conjugateIntersection_relIndex (I : Subgroup G) (g : G) :
    (I ⊓ I.map (MulAut.conj g).toMonoidHom).relIndex I = (conjugateIntersection I g).index := by
  apply congrArg Subgroup.index
  ext x
  change ((x : G) ∈ I ∧ (x : G) ∈ I.map (MulAut.conj g).toMonoidHom) ↔
    g⁻¹ * (x : G) * g⁻¹⁻¹ ∈ I
  rw [inv_inv]
  refine ⟨?_, fun h => ⟨x.property, _, h, ?_⟩⟩
  · rintro ⟨_, y, hy, he⟩
    change g * y * g⁻¹ = (x : G) at he
    have h : g⁻¹ * (x : G) * g = y := by
      rw [← he]
      group
    rwa [h]
  · change g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
    group

open scoped Classical in
/-- At a single wall, only the upper equation and the unit diagonal are
needed after the two conjugate charts and their relative index are known. -/
private theorem bruhatFromValuedCharts [Fintype J]
    (C : LocalComparison (j := j) (Wf := Wf) A p) (q : ℕ) (hq : 2 ≤ q)
    [∀ a, ValuativeRel (C.chart.parameter a)] [∀ a, TopologicalSpace (C.chart.parameter a)]
    [∀ a, IsNonarchimedeanLocalField (C.chart.parameter a)]
    (vP : ∀ a x, C.chart.value a x = normalizedValuation (C.chart.parameter a) x)
    (covers : ∀ a, a ∈ Set.range C.chart.chart.neg ∪ Set.range C.chart.chart.pos)
    (e : J → ℕ) (he : ∀ a, 0 < e a)
    (hvn : ∀ l x, normalizedValuation K (C.chart.chart.negMap l x) =
      normalizedValuation (C.chart.parameter (C.chart.chart.neg l)) x ^ e (C.chart.chart.neg l))
    (hvp : ∀ l x, normalizedValuation K (C.chart.chart.posMap l x) =
      normalizedValuation (C.chart.parameter (C.chart.chart.pos l)) x ^ e (C.chart.chart.pos l))
    (hres : ∀ a, Nat.card (residue (C.chart.parameter a)) = q)
    (base : ∀ g, g ∈ C.I ↔ C.chart.atPoint p g)
    (translated : ∀ (n : C.N) (g : G),
      g ∈ C.I.map (MulAut.conj (n : G)).toMonoidHom ↔
        C.chart.atPoint (C.affine n p) g)
    (rank : C.RankOneLifts)
    (walls : ∀ a : A.SimpleWall p,
      let P := C.chart.parameter a.val.1
      ∃ (r : Matrix.SpecialLinearGroup (Fin 2) P →* G) (t c : Pˣ) (u : C.chart.chart.torus),
        u.val = 1 ∧ C.chart.value a.val.1 c = 1 ∧
        (∀ z : P, j (r (upper z)) =
          Specs.ExceptionalIwahoriCongruence.cellValue M.toIntegralMarking
            (Specs.ExceptionalIwahoriCongruence.integralRing K) C.chart.negative C.chart.positive
            (C.chart.chart.coordinates u (Function.update (fun _ => 0) a.val.1 ((c : P) * z)))) ∧
        C.chart.value a.val.1 t = exp (-a.val.2) ∧
        (C.lift (C.coxeter.coxeter.simple a) : G) =
          r (Specs.ExceptionalMarkedRootDescent.wallMatrix t) ∧
        (∀ z : Pˣ, C.chart.value a.val.1 z = 1 → r (diagonal z) ∈ C.I))
    (ordinary : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype) :
    C.Bruhat q := by
  classical
  have hpos : 0 < q := by omega
  have hindex (w : A.affineWeylGroup) :
      (conjugateIntersection C.I (C.lift w : G)).index =
        q ^ ∑ᶠ a, (threshold (A.root a (w.val p)) - threshold (A.root a p)).toNat := by
    have h := rootChartIntersectionIndex C.chart C.point_injective vP covers e he hvn hvp q hpos hres
      C.I (C.I.map (MulAut.conj (C.lift w : G)).toMonoidHom) (w.val p)
      (rootChart_baseThreshold_nonneg C.chart) base
      (fun g => by simpa only [C.lift_label] using translated (C.lift w) g)
    rw [← conjugateIntersection_relIndex, finsum_eq_sum_of_fintype]
    exact h
  refine bruhatFromWallProducts C q hq rank ordinary base
    (fun w g => by simpa only [C.lift_label] using translated (C.lift w) g) ?_ hindex
  intro w a
  obtain ⟨r, t, c, u, hu, hc, hupper, ht, hlift, hdiag⟩ := walls a
  have hsimple : (conjugateIntersection C.I (C.lift (C.coxeter.coxeter.simple a) : G)).index = q := by
    rw [hindex, ← C.coxeter.length_thresholds, C.coxeter.coxeter.length_simple, pow_one]
  exact wallProductFromRankOne C a q hpos (vP a.val.1) (hres a.val.1)
    covers translated r t c u hu hc hupper ht hlift hdiag hsimple w

end LocalAssembly

section SplitBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers IntegralMarking IntegralAlgebra IntegralPoints
  integerAlgebra integralSpec integralPointFunctor splitTorus TorusValues torusPoint cocharacter)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots AlcoveGeometry PinnedWallSigns threshold)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint markedWeylWord
  markedCellPoint orderedRootPoint wallMatrix weylWordPerm)
open Specs.ExceptionalIwahoriCongruence (cellValue integralRing markedRootFactors)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open Specs.IntegralRootRelations (upper diagonal)
open Specs.OrderedRootProducts (Enumerates)
open private cellValue_eq_mul rootWord_eq_prod from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private markedRootPoint_single from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedTorusPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private torusPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private weylWord_index from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

open scoped TensorProduct Matrix
attribute [local instance] integerAlgebra
universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem cellValue_ofAbsoluteParameters (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (negative positive : List D.I) (x : D.I → R) (t : TorusValues D R) :
    cellValue M R negative positive (fun l => x negative[l], t, fun l => x positive[l]) =
      markedCellPoint M R negative positive x (torusPoint D R t) := by
  rw [cellValue_eq_mul, rootWord_eq_prod, rootWord_eq_prod]
  have h (l : List D.I) :
      markedRootFactors M R l (fun j => x l[j]) = l.map (fun a => markedRootPoint M R a (x a)) := by
    conv_rhs => rw [← List.ofFn_getElem (xs := l), List.map_ofFn]
    rfl
  rw [h, h, markedCellPoint, orderedRootPoint, orderedRootPoint]

open scoped Classical in
private theorem splitCell_single {p : ℚ ⊗[ℤ] D.Y} {negative positive : List D.I}
    (hn : Enumerates negative {i | ¬D.base.IsPos i}) (hp : Enumerates positive {i | D.base.IsPos i})
    (hs : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos) (a : D.I) (z : K) :
    let C := splitRootChart (M := M) (K := K) negative positive hn hp p hs
    cellValue M.toIntegralMarking (integralRing K) negative positive
      (C.chart.coordinates ⟨1, Set.mem_univ _⟩ (Function.update (fun _ => 0) a z)) =
        markedRootPoint M.toIntegralMarking (integralRing K) a z := by
  classical
  intro C
  let R := integralRing K
  let y : D.I → R := fun i => if i = a then z else 0
  have hcoords :
      C.chart.coordinates ⟨1, Set.mem_univ _⟩ (Function.update (fun _ => 0) a z) =
        (fun l : Fin negative.length => y negative[l], (1 : TorusValues D R),
          fun l : Fin positive.length => y positive[l]) := by
    apply Prod.ext
    · funext l
      change algebraMap Integers.{u} K 1 * Function.update (fun _ : D.I => (0 : K)) a z negative[l] = _
      simp [y, Function.update_apply]
      rfl
    · refine Prod.ext rfl (funext fun l => ?_)
      change algebraMap Integers.{u} K 1 * Function.update (fun _ : D.I => (0 : K)) a z positive[l] = _
      simp [y, Function.update_apply]
      rfl
  have htorus : (torusPoint D R 1 ≫ M.torus.hom.hom : IntegralPoints M.group R) = 1 := by
    rw [← markedTorusPointHom_apply]
    exact map_one _
  rw [hcoords, cellValue_ofAbsoluteParameters, markedCellPoint, htorus, one_mul,
    markedRootPoint_single _ _ _ hn.1, markedRootPoint_single _ _ _ hp.1]
  by_cases ha : D.base.IsPos a
  · rw [ite_eq_right (fun h => (hn.2 a).mp h ha), ite_eq_left ((hp.2 a).mpr ha), one_mul]
  · rw [ite_eq_left ((hn.2 a).mpr ha), ite_eq_right (fun h => ha ((hp.2 a).mp h)), mul_one]

private theorem torusPoint_mem_unitTorus (M : Model D) (t : TorusValues D (integralRing K))
    (ht : ∀ χ, normalizedValuation K (t χ : K) = 1) :
    (torusPoint D (integralRing K) t ≫ M.torus.hom.hom : FieldPoints M K) ∈ integralUnitTorus M := by
  let v := valuation K
  let tO : TorusValues D (integralRing 𝒪[K]) := v.valuationSubring.unitGroupMulEquiv.toMonoidHom.comp
    (t.codRestrict _ (fun χ => (Valuation.mem_unitGroup_iff (v := v) (x := t χ)).2
      ((valuation_unit_iff _).1 (ht χ))))
  refine ⟨torusPoint D (integralRing 𝒪[K]) tO, ?_⟩
  change (integralSpec.map (valuationRingInclusion K).op ≫
    torusPoint D (integralRing 𝒪[K]) tO) ≫ M.torus.hom.hom = _
  exact congrArg (fun b : IntegralPoints (splitTorus D) (integralRing K) => b ≫ M.torus.hom.hom)
    (torusPoint_natural (D := D) (valuationRingInclusion K) tO)

private theorem transportedDiagonal_mem_unitTorus (M : Model D) (l : List D.I)
    (hl : ∀ i ∈ l, i ∈ D.base.support) (a : D.I) (z : Kˣ)
    (hz : normalizedValuation K (z : K) = 1) :
    let R := integralRing K
    let m := markedWeylWord M.toIntegralMarking R l
    m * (show IntegralPoints M.group R from (M.rankOne a).app R (diagonal z)) * m⁻¹ ∈
      integralUnitTorus M := by
  intro R m
  rw [M.rankOneDiagonal]
  change MulAut.conj m _ ∈ _
  rw [markedWeylWord_conjugatesTorus M l hl]
  apply torusPoint_mem_unitTorus
  intro χ
  let w := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  let a' := w.val.weightEquiv.symm χ.toAdd
  change normalizedValuation K (↑(z ^ D.datum.toLinearMap a' (D.datum.coroot a)) : K) = 1
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hz, one_zpow]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The actual marked split root coordinates give the affine double cosets
once the ordinary normalizer subgroup is identified. -/
theorem splitBruhatOfPinnedAlcove (F₀ : MarkedFibre M K)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (p : ℚ ⊗[ℤ] D.Y) (adjoint : Bool)
    (hs : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos)
    (geom : AlcoveGeometry (ApartmentRoots.split D.datum ℚ) p)
    (hsc : adjoint = false → D.datum.corootSpan ℤ = ⊤)
    (had : adjoint = true → D.datum.rootSpan ℤ = ⊤)
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬D.base.IsPos i}) (hp : Enumerates positive {i | D.base.IsPos i}) :
    let A := ApartmentRoots.split D.datum ℚ
    ∃ C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup) A p,
      SplitPointComparison F₀ adjoint C ∧
      C.chart.negative = negative ∧ C.chart.positive = positive ∧
      (∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support) ∧
      (∀ (n : C.N) (g : FieldPoints M K),
        g ∈ C.I.map (MulAut.conj (n : FieldPoints M K)).toMonoidHom ↔
          C.chart.atPoint (C.affine n p) g) ∧
      (C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype →
        C.Bruhat (Nat.card (residue K))) := by
  classical
  intro A
  let _ := D.finiteRoots
  let _ := Fintype.ofFinite D.I
  let R := integralRing K
  obtain ⟨C₀, h₀, _, hword⟩ :=
    splitLocalComparisonWithSimpleWords F₀ b p adjoint hs geom hsc had
  let C₁ : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup) A p :=
    { C₀ with chart := splitRootChart negative positive hn hp p hs }
  have h₁ : SplitPointComparison F₀ adjoint C₁ := by
    refine ⟨h₀.1, h₀.2.1, rfl, fun _ => rfl, fun _ => rfl,
      fun i => ⟨RingEquiv.refl K, fun _ => rfl, ?_, ?_⟩, h₀.2.2.2.2.2.2⟩
    all_goals
      intro l he x
      cases he
      rfl
  choose i word t ε r n hwords hperm hr hu ht hn' haff using
    fun a : A.SimpleWall p => splitAffineWallLift F₀ b C₁ h₁ a.val.1 a.val.2
  have hlabel (a : A.SimpleWall p) : C₁.affine (n a) = (C₁.coxeter.coxeter.simple a).val := by
    rw [C₁.coxeter.simple_eq]
    exact haff a
  let C := withSimpleLifts C₁ n hlabel
  have hC : SplitPointComparison F₀ adjoint C := h₁
  let q := Nat.card (residue K)
  let _ : Fintype (residue K) := Fintype.ofFinite (𝓀[K])
  have hq : 2 ≤ q := by
    dsimp only [q]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  let _ : ∀ a, ValuativeRel (C.chart.parameter a) := fun _ => ‹ValuativeRel K›
  let _ : ∀ a, TopologicalSpace (C.chart.parameter a) := fun _ => ‹TopologicalSpace K›
  let _ : ∀ a, IsNonarchimedeanLocalField (C.chart.parameter a) := fun _ =>
    ‹IsNonarchimedeanLocalField K›
  have hcover := rootChart_covers C.chart Function.surjective_id
  have hneg (l : Fin C.chart.negative.length) : threshold (A.root (C.chart.chart.neg l) p) = 1 :=
    hs.threshold_negative _ ((hn.2 _).mp (List.getElem_mem l.isLt))
  have hpos (l : Fin C.chart.positive.length) : threshold (A.root (C.chart.chart.pos l) p) = 0 :=
    hs.threshold_positive _ ((hp.2 _).mp (List.getElem_mem l.isLt))
  have hbase := iwahori_basePoint_chart C.localIwahori C.chart hcover hneg hpos
    (fun _ => 1) (fun _ => Int.one_pos) (fun _ z => (zpow_one (normalizedValuation K z)).symm)
    (fun _ z => (zpow_one (normalizedValuation K z)).symm)
  have htrans := normalizerTranslatedChart C b (MonoidHom.id _) hword hC.2.1.2.choose_spec.2
    id (fun _ => 1) (fun _ => Int.one_pos) (fun _ _ => (one_mul _).symm) hC.2.2.2.2.2.2.1 hcover
    (fun _ z => (zpow_one (normalizedValuation K z)).symm)
    (fun _ z => (zpow_one (normalizedValuation K z)).symm) hbase
  let c (a : A.SimpleWall p) := Units.map (algebraMap Integers.{u} K).toMonoidHom (ε a)
  let u : C.chart.chart.torus := ⟨1, Set.mem_univ _⟩
  have hc (a : A.SimpleWall p) : C.chart.value a.val.1 (c a : K) = 1 := integerUnit_value (K := K) (ε a)
  have hupper (a : A.SimpleWall p) (z : K) :
      identityPoints M K (r a (upper z)) =
        cellValue M.toIntegralMarking R C.chart.negative C.chart.positive
          (C.chart.chart.coordinates u (Function.update (fun _ => 0) a.val.1 ((c a : K) * z))) := by
    exact (hu a z).trans (splitCell_single (M := M) hn hp hs a.val.1 ((c a : K) * z)).symm
  have hlift (a : A.SimpleWall p) :
      (C.lift (C.coxeter.coxeter.simple a) : FieldPoints M K) = r a (wallMatrix (t a)) :=
    (congrArg Subtype.val (withSimpleLifts_apply C₁ n hlabel a)).trans (hn' a)
  have hrank : C.RankOneLifts := by
    intro a
    refine ⟨word a, [(i a, RingHom.id K)], r a, t a, c a, u, hwords a, ?_, ?_, ?_, ?_,
      rfl, hc a, hupper a, ht a, hlift a⟩
    · simp only [List.length_singleton]
      rw [ite_eq_right]
      rintro ⟨x, y, ne, hx, hy⟩
      exact ne (hx.trans hy.symm)
    · simp
    · intro j
      change j = a.val.1 ↔ j ∈ [_]
      rw [List.mem_singleton]
      change j = a.val.1 ↔ j = ((word a).map (RootPairing.weylGroup.ofIdx D.datum)).prod.val.indexEquiv (i a)
      rw [← weylWord_index, hperm a]
    · intro U
      have hm : Matrix.SpecialLinearGroup.map (RingHom.id K) U = U := by
        apply Subtype.ext
        ext x y
        rfl
      let m := markedWeylWord M.toIntegralMarking R (word a)
      change r a U = m *
        ((show FieldPoints M K from
          (M.rankOne (i a).val).app R (Matrix.SpecialLinearGroup.map (RingHom.id K) U)) * 1) * m⁻¹
      rw [mul_one, hm]
      exact hr a U
  refine ⟨C, hC, rfl, rfl, hword, htrans, fun ho => ?_⟩
  exact bruhatFromValuedCharts C q hq (fun _ _ => rfl) hcover (fun _ => 1)
    (fun _ => Nat.one_pos) (fun _ z => (pow_one (normalizedValuation K z)).symm)
    (fun _ z => (pow_one (normalizedValuation K z)).symm) (fun _ => rfl) hbase htrans hrank
    (fun a => ⟨r a, t a, c a, u, rfl, hc a, hupper a, ht a, hlift a, fun z hz => by
      apply unitTorus_le_iwahori C
      change r a (diagonal z) ∈ integralUnitTorus M
      rw [hr a]
      exact transportedDiagonal_mem_unitTorus M (word a) (hwords a) (i a) z hz⟩) ho

end SplitBruhat

end SplitAssembly

section OrdinarySubgroup

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open ValuativeRel
attribute [local instance] integerAlgebra

universe u v w

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {G H Wf Wf' : Type u} [Group G] [Group H] [Group Wf] [Group Wf']
  {j : G →* FieldPoints M K} {j' : H →* FieldPoints M' K}
  {V V' : Type u} {J : Type v} {J' : Type w}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
  {A : ApartmentRoots ℚ V J} {A' : ApartmentRoots ℚ V' J'} {p : V} {p' : V'}

theorem ordinaryRange_normalizer (C : LocalComparison (j := j) (Wf := Wf) A p)
    (h : C.affine.range = A.affineWeylGroup) :
    C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype := by
  have he : A.affineWeylGroup.comap C.affine = ⊤ := by
    apply top_unique
    intro n _
    change C.affine n ∈ A.affineWeylGroup
    rw [← h]
    exact ⟨n, rfl⟩
  rw [ordinaryRange_generates C h, he, Subgroup.map_top, Subgroup.range_subtype]
  simp

/-- Conjugate an affine transformation under a change of coordinates. -/
private def transportAffine (e : V ≃ᵃ[ℚ] V') : (V ≃ᵃ[ℚ] V) ≃* (V' ≃ᵃ[ℚ] V') where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' f g := by ext x; simp [AffineEquiv.coe_mul]

private theorem transportAffineOrdinary (e : V ≃ₗ[ℚ] V') (d : J ≃ J')
    (hroot : ∀ a x, A'.root (d a) (e x) = A.root a x)
    (hcoroot : ∀ a, e (A.coroot a) = A'.coroot (d a)) :
    A.affineWeylGroup.map (transportAffine e.toAffineEquiv).toMonoidHom = A'.affineWeylGroup := by
  have he (a : J) (m : ℤ) :
      transportAffine e.toAffineEquiv (A.wallReflection a m) = A'.wallReflection (d a) m := by
    ext x
    obtain ⟨x, rfl⟩ := e.surjective x
    change e (A.wallReflection a m (e.symm (e x))) = A'.wallReflection (d a) m (e x)
    rw [e.symm_apply_apply, (ExceptionalAffineRootSystems.affineGroupNormalForms A).1,
      (ExceptionalAffineRootSystems.affineGroupNormalForms A').1, map_sub, map_smul, hroot, hcoroot]
  change (Subgroup.closure (Set.range A.reflection)).map (transportAffine e.toAffineEquiv).toMonoidHom =
    Subgroup.closure (Set.range A'.reflection)
  rw [MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext f
  constructor
  · rintro ⟨_, ⟨⟨a, m⟩, rfl⟩, rfl⟩
    exact ⟨(d a, m), (he a m).symm⟩
  · rintro ⟨⟨a, m⟩, rfl⟩
    obtain ⟨a, rfl⟩ := d.surjective a
    exact ⟨_, ⟨(a, m), rfl⟩, he a m⟩

/-- The central image with the target unit torus is the subgroup whose
normalizer labels are ordinary. The proof uses just the marked central
preimages and covariance on the rational apartments. -/
theorem ordinarySubgroup_ofCentralComparison
    (C : LocalComparison (j := j) (Wf := Wf) A p)
    (C' : LocalComparison (j := j') (Wf := Wf') A' p')
    (φ : G →* H) (hφ : φ.range.Normal)
    (hI : C'.I = C.I.map φ ⊔ C'.T₀)
    (hN : C'.N.comap φ = C.N)
    (hrange : C.affine.range = A.affineWeylGroup)
    (e : V ≃ₗ[ℚ] V') (d : J ≃ J')
    (hroot : ∀ a x, A'.root (d a) (e x) = A.root a x)
    (hcoroot : ∀ a, e (A.coroot a) = A'.coroot (d a))
    (haffine : ∀ (n : C.N) (n' : C'.N), (n' : H) = φ n →
      ∀ x, e (C.affine n x) = C'.affine n' (e x)) :
    C'.G₀.Normal ∧
    C'.G₀ ⊓ C'.N = (A'.affineWeylGroup.comap C'.affine).map C'.N.subtype ∧
    (∀ h, h ∈ C'.G₀ ↔ ∃ (g : G) (t : C'.T₀), h = φ g * t) := by
  let U := C'.T₀
  let P := φ.range
  let _ : P.Normal := hφ
  let O := (A'.affineWeylGroup.comap C'.affine).map C'.N.subtype
  have hN' (g : G) : φ g ∈ C'.N ↔ g ∈ C.N :=
    SetLike.ext_iff.mp hN g
  let i : C.N →* C'.N := (φ.comp C.N.subtype).codRestrict _ (fun n => (hN' n).mpr n.property)
  let b := transportAffine e.toAffineEquiv
  have hav (n : C.N) : b (C.affine n) = C'.affine (i n) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e (C.affine n (e.symm (e x))) = _
    rw [e.symm_apply_apply]
    exact haffine n (i n) rfl x
  have hRange : (C'.affine.comp i).range = A'.affineWeylGroup := by
    rw [show C'.affine.comp i = b.toMonoidHom.comp C.affine from MonoidHom.ext (fun n => (hav n).symm),
      MonoidHom.range_comp, hrange, transportAffineOrdinary e d hroot hcoroot]
  have hker : C'.affine.ker.map C'.N.subtype = U := C'.kernel
  have hU : U ≤ C'.N := by
    rw [← hker]
    exact Subgroup.map_subtype_le _
  have hConj (n : C'.N) (t : H) (ht : t ∈ U) : (n : H) * t * (n : H)⁻¹ ∈ U := by
    have htk : t ∈ C'.affine.ker.map C'.N.subtype := hker.symm ▸ ht
    obtain ⟨v, hv, rfl⟩ := htk
    rw [← hker]
    exact ⟨n * v * n⁻¹, (inferInstance : C'.affine.ker.Normal).conj_mem v hv n, rfl⟩
  have hJ : O = C.N.map φ ⊔ U := by
    apply le_antisymm
    · rintro h ⟨n, hn, rfl⟩
      change C'.affine n ∈ A'.affineWeylGroup at hn
      rw [← hRange] at hn
      obtain ⟨m, hm⟩ := hn
      change (n : H) ∈ C.N.map φ ⊔ U
      have hh := sameLabel_div_mem_unitTorus C' (n := n) (m := i m) hm.symm
      have hm' : (i m : H) ∈ C.N.map φ := ⟨m, m.property, rfl⟩
      simpa only [inv_mul_cancel_right] using
        (C.N.map φ ⊔ U).mul_mem ((le_sup_right : U ≤ C.N.map φ ⊔ U) hh)
          ((le_sup_left : C.N.map φ ≤ C.N.map φ ⊔ U) hm')
    · apply sup_le
      · rintro h ⟨n, hn, rfl⟩
        refine ⟨i ⟨n, hn⟩, ?_, rfl⟩
        change C'.affine (i ⟨n, hn⟩) ∈ A'.affineWeylGroup
        rw [← hRange]
        exact ⟨⟨n, hn⟩, rfl⟩
      · intro h hh
        let n : C'.N := ⟨h, hU hh⟩
        refine ⟨n, ?_, rfl⟩
        have hh' : h ∈ C'.affine.ker.map C'.N.subtype := hker.symm ▸ hh
        obtain ⟨m, hm, he⟩ := hh'
        change C'.affine n ∈ A'.affineWeylGroup
        have eq : m = n := Subtype.ext he
        rw [← eq, MonoidHom.mem_ker.mp hm]
        exact Subgroup.one_mem _
  have hH : C'.G₀ = P ⊔ U := by
    change C'.I ⊔ O = P ⊔ U
    rw [hI, hJ]
    change (C.I.map φ ⊔ U) ⊔ (C.N.map φ ⊔ U) = P ⊔ U
    calc
      _ = (C.I.map φ ⊔ C.N.map φ) ⊔ (U ⊔ U) := by ac_rfl
      _ = _ := by rw [sup_idem, ← Subgroup.map_sup, show C.I ⊔ C.N = ⊤ from C.localIwahori.generation, Subgroup.map_top]
  have hNormal : (P ⊔ U).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    have hN' : C'.N ≤ Subgroup.normalizer ((P ⊔ U : Subgroup H) : Set H) := by
      have hNU : C'.N ≤ Subgroup.normalizer (U : Set H) :=
        Subgroup.le_normalizer_iff.mpr (fun n hn t ht => hConj ⟨n, hn⟩ t ht)
      have hNP : C'.N ≤ Subgroup.normalizer (P : Set H) := Subgroup.le_normalizer_of_normal
      exact (le_inf hNP hNU).trans (Subgroup.inf_normalizer_le_normalizer_sup P U)
    have hI' : C'.I ≤ Subgroup.normalizer ((P ⊔ U : Subgroup H) : Set H) :=
      (show C'.I ≤ P ⊔ U from hH ▸ (le_sup_left : C'.I ≤ C'.G₀)).trans Subgroup.le_normalizer
    apply top_unique
    rw [← C'.localIwahori.generation]
    exact sup_le hI' hN'
  have hInt : C'.G₀ ⊓ C'.N = O := by
    rw [hH, hJ]
    apply le_antisymm
    · rintro g ⟨hg, hn⟩
      obtain ⟨_, ⟨x, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      have hx : φ x ∈ C'.N := by
        simpa only [mul_inv_cancel_right] using C'.N.mul_mem hn (C'.N.inv_mem (hU ht))
      exact (C.N.map φ ⊔ U).mul_mem ((le_sup_left : C.N.map φ ≤ C.N.map φ ⊔ U)
        ⟨x, (hN' x).mp hx, rfl⟩) ((le_sup_right : U ≤ C.N.map φ ⊔ U) ht)
    · refine le_inf (sup_le (fun g hg => ?_) le_sup_right) (sup_le (fun g hg => ?_) hU)
      · obtain ⟨x, hx, rfl⟩ := hg
        exact (le_sup_left : P ≤ P ⊔ U) ⟨x, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := hg
        exact (hN' x).mpr hx
  refine ⟨hH ▸ hNormal, hInt, fun h => ?_⟩
  rw [hH, Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, t, ht, rfl⟩
    exact ⟨g, ⟨t, ht⟩, rfl⟩
  · rintro ⟨g, t, rfl⟩
    exact ⟨φ g, ⟨g, rfl⟩, t, t.property, rfl⟩

end OrdinarySubgroup

section CanonicalNormalizer

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra integralPointFunctor
  TorusValues torusPoint)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer MarkedCentralCover integralPointHom)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open private splitMarkedNormalizerWord fibreNormalizerPoint_injective cover_simple from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private simpleWeylWords from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private rationalCocharacterAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

attribute [local instance] integerAlgebra
open scoped TensorProduct WithZero
universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {G W : Type u} [Group G] [Group W] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

private theorem normalizerTorusWord (N : MarkedLocalNormalizer K j W) (n : N.normalizer) :
    ∃ t : TorusValues D (integralRing K), j (N.torusPart n) = torusPoint D _ t ≫ M.torus.hom.hom ∧
      j n = (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) (N.word (N.label n)) := by
  obtain ⟨t, ht⟩ := (N.torusPoints _).mp (N.torusPart n).property
  refine ⟨t, ht, ?_⟩
  rw [← ht, ← N.lift_point, ← map_mul]
  apply congrArg j
  change (n : G) = ((n * (N.lift (N.label n))⁻¹ : N.normalizer) : G) * (N.lift (N.label n) : G)
  simp

/-- A simple integral Weyl word in a torus-normalizer factorization reads
the actual finite label. Its torus factor reads the translation by taking
the valuation of each character. -/
theorem labelAndTranslationOfWord (C : LocalComparison (j := j) (Wf := W) A p)
    (q : W →* D.datum.weylGroup) (hC : C.FiniteLabels q)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (n : C.N) (l : List D.I) (hl : ∀ i ∈ l, i ∈ D.base.support)
    (t : TorusValues D (integralRing K))
    (ht : j n = (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M K) *
      markedWeylWord M.toIntegralMarking (integralRing K) l) :
    let N := C.localIwahori.normalizer
    q (N.label n) = (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod ∧
    ∀ χ, D.datum.toLinearMap χ (N.translation (N.torusPart n)).toAdd =
      WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd χ) : K)) := by
  intro N
  obtain ⟨hq, B, hB, _⟩ := hC
  let _ := B.torusComm
  obtain ⟨m, hm, hmLabel⟩ := splitMarkedNormalizerWord B l hl
  obtain ⟨x, hx, hxLabel⟩ := hB n
  obtain ⟨T, hT, _⟩ := ExceptionalValuedTorusNormalizer.fibreNormalizerTorusAction B
  have he : x = (T t).val * m := by
    apply fibreNormalizerPoint_injective B
    rw [map_mul, hT, hm, hx, ht]
  have hLabel : q (N.label n) = (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod := by
    rw [← hxLabel, he, map_mul, MonoidHom.mem_ker.mp (T t).property, one_mul, hmLabel]
  obtain ⟨_, _, _, hLog⟩ := ExceptionalLocalRootCoordinates.markedNormalizerApartment
    B b j N q hq hB (1 : ℚˣ)
  refine ⟨hLabel, hLog n m (hmLabel.trans hLabel.symm) ?_ t ?_⟩
  · refine ⟨markedWeylWord M.toIntegralMarking _ l, ?_⟩
    rw [hm]
    exact markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) l
  · rw [hm, ht, mul_inv_cancel_right]

private theorem linearActions_ofRootComparison (c : MarkedCentralCover M M')
    (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (d : D.datum.weylGroup ≃* E.datum.weylGroup)
    (hd : ∀ i, d (RootPairing.weylGroup.ofIdx D.datum i) =
      RootPairing.weylGroup.ofIdx E.datum (c.rootEquiv i))
    (hr : ∀ i x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv i) (e x) =
      (ApartmentRoots.split D.datum ℚ).root i x)
    (hc : ∀ i, e ((ApartmentRoots.split D.datum ℚ).coroot i) =
      (ApartmentRoots.split E.datum ℚ).coroot (c.rootEquiv i)) :
    ∀ w x, e ((rationalCocharacterAction D) w.val x) =
      (rationalCocharacterAction E) (d w).val (e x) := by
  let h (w : D.datum.weylGroup) : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] D.Y) :=
    rationalCocharacterAction D w.val
  let h' (w : E.datum.weylGroup) : (ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y) :=
    rationalCocharacterAction E w.val
  have hw : ∀ w : D.datum.weylGroup, ∃ l : List D.I,
      (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod = w := by
    obtain ⟨l, _, hl⟩ := simpleWeylWords D
    exact fun w => ⟨l w, hl w⟩
  intro w
  obtain ⟨l, rfl⟩ := hw w
  induction l with
  | nil =>
      intro x
      change e (h 1 x) = h' (d 1) (e x)
      simp [h, h']
  | cons i l ih =>
      intro x
      let y := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
      change e (h ((RootPairing.weylGroup.ofIdx D.datum i) * y) x) =
        h' (d ((RootPairing.weylGroup.ofIdx D.datum i) * y)) (e x)
      have hmul (a b : D.datum.weylGroup) (z) : h (a * b) z = h a (h b z) := by
        change (rationalCocharacterAction D) (a.val * b.val) z = _
        rw [map_mul]
        rfl
      have hmul' (a b : E.datum.weylGroup) (z) : h' (a * b) z = h' a (h' b z) := by
        change (rationalCocharacterAction E) (a.val * b.val) z = _
        rw [map_mul]
        rfl
      rw [hmul, map_mul, hmul', hd, ← ih x]
      change e ((rationalCocharacterAction D) (RootPairing.Equiv.reflection D.datum i) (h y x)) =
        (rationalCocharacterAction E) (RootPairing.Equiv.reflection E.datum (c.rootEquiv i)) (e (h y x))
      rw [splitWeylReflection, splitWeylReflection]
      simp only [AffineArrangement.Datum.linearReflection, Module.reflection_apply]
      change e (h y x - (ApartmentRoots.split D.datum ℚ).root i (h y x) • _ ) =
        e (h y x) - (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv i) (e (h y x)) • _
      rw [map_sub, map_smul, hr, hc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The central map compares the actual split normalizer actions on the
rational cocharacter spaces, regardless of the chosen integral words. -/
theorem splitCentralAffine
    (c : MarkedCentralCover M M') (hE : E.datum.rootSpan ℤ = ⊤)
    {F : MarkedFibre M K} {F' : MarkedFibre M' K}
    {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (C' : LocalComparison (j := identityPoints M' K) (Wf := E.datum.weylGroup)
      (ApartmentRoots.split E.datum ℚ) p')
    (hC : SplitPointComparison F false C) (hC' : SplitPointComparison F' true C')
    {index : Type u} [Fintype index] (b' : Module.Basis index ℤ E.Y)
    (hw : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (he : e.toLinearMap = c.pushCocharacter.baseChange ℚ)
    (hr : ∀ i x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv i) (e x) =
      (ApartmentRoots.split D.datum ℚ).root i x)
    (hc : ∀ i, e ((ApartmentRoots.split D.datum ℚ).coroot i) =
      (ApartmentRoots.split E.datum ℚ).coroot (c.rootEquiv i))
    (n : C.N) (n' : C'.N) (hn' : (n' : FieldPoints M' K) = integralPointHom c.map (integralRing K) n) :
    ∀ x, e (C.affine n x) = C'.affine n' (e x) := by
  let N := C.localIwahori.normalizer
  let N' := C'.localIwahori.normalizer
  let R := integralRing K
  let φ := integralPointHom c.map R
  obtain ⟨d, hd, _, _⟩ := ExceptionalIwahoriImageComparison.centralCoverWeylComparison c hE
  obtain ⟨t, ht, hn⟩ := normalizerTorusWord N n
  let l := N.word (N.label n)
  have hl (i : D.I) (hi : i ∈ l) : i ∈ D.base.support := hw _ i hi
  have hl' (i : E.I) (hi : i ∈ l.map c.rootEquiv) : i ∈ E.base.support := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    exact (cover_simple c a).mp (hl a ha)
  have hφword := (ExceptionalIwahoriImageComparison.markedRankOneMapCompatibility c.map c.rootEquiv
    c.pullCharacter.toAddMonoidHom.toMultiplicative c.marking (fun a => c.reflections a a)).2 R l
  let t' : TorusValues E R := t.comp c.pullCharacter.toAddMonoidHom.toMultiplicative
  have hn'' : identityPoints M' K n' = (torusPoint E R t' ≫ M'.torus.hom.hom : FieldPoints M' K) *
        markedWeylWord M'.toIntegralMarking R (l.map c.rootEquiv) := by
    change (n' : FieldPoints M' K) = _
    rw [hn', show (n : FieldPoints M K) = _ from hn, map_mul, hφword, c.marking.2.2 R t]
  obtain ⟨hlabel, hlog⟩ := labelAndTranslationOfWord C' (MonoidHom.id _) hC'.2.1 b' n'
    (l.map c.rootEquiv) hl' t' hn''
  have hlab : N'.label n' = d (N.label n) := by
    rw [show N'.label n' = _ from hlabel]
    have h := hC.2.1.2.choose_spec.2 (N.label n)
    change (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod = N.label n at h
    rw [← h]
    simp only [map_list_prod, List.map_map, Function.comp_def, hd]
  have hcochar := ExceptionalIwahoriImageComparison.markedTranslationCompatibility D E
    c.pullCharacter c.pushCocharacter c.pairing t _ _ (N.characterLog _ t ht) hlog
  have htensor :
      e ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) =
        (1 : ℚ) ⊗ₜ[ℤ] (N'.translation (N'.torusPart n')).toAdd := by
    change e.toLinearMap _ = _
    rw [he]
    exact hcochar.2 1
  intro x
  rw [hC.2.2.2.2.2.2.1, hC'.2.2.2.2.2.2.1, map_add, htensor, hlab]
  exact congrArg (fun y => y + ((1 : ℚ) ⊗ₜ[ℤ] (N'.translation (N'.torusPart n')).toAdd))
    (linearActions_ofRootComparison c e d hd hr hc (N.label n) x)

end CanonicalNormalizer

section SplitLevelAssembly

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots PinnedWallSigns AlcoveGeometry threshold)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.OrderedRootProducts (Enumerates)
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open scoped TensorProduct
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

variable {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

private theorem splitPinnedSigns_ofCentralCover (c : MarkedCentralCover M M')
    (p : ℚ ⊗[ℤ] D.Y) (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (hr : ∀ a x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv a) (e x) =
      (ApartmentRoots.split D.datum ℚ).root a x)
    (hS : PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos) :
    PinnedWallSigns (ApartmentRoots.split E.datum ℚ) (e p) E.base.IsPos := by
  let A := ApartmentRoots.split D.datum ℚ
  let A' := ApartmentRoots.split E.datum ℚ
  have hp (a : D.I) : E.base.IsPos (c.rootEquiv a) ↔ D.base.IsPos a := (c.marking.1 a).symm
  constructor
  · intro a n
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    change 0 < A'.root (c.rootEquiv a) (e p) + (n : ℚ) ↔ _
    rw [hr, hp]
    exact hS.positive_iff a n
  · intro a
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    rw [hr, hp]
    exact hS.threshold_positive a
  · intro a
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    rw [hr, hp]
    exact hS.threshold_negative a
  · intro a ha
    exact (simpleWall_threshold (⟨a, ha⟩ : A'.SimpleWall (e p))).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The simply connected and adjoint split forms have compatible affine
Bruhat decompositions over each local coefficient field, on apartments
identified by their marked central map. -/
theorem splitBruhatAtLocalField
    (c : MarkedCentralCover M M') (n : ℕ) (b : Fin n ≃ D.base.support)
    (hD : D.datum.corootSpan ℤ = ⊤) (hE : E.datum.rootSpan ℤ = ⊤)
    (rD : Module.finrank ℤ D.Y = n) (rE : Module.finrank ℤ E.Y = n) :
    let A := ApartmentRoots.split D.datum ℚ
    let A' := ApartmentRoots.split E.datum ℚ
    ∃ (p : ℚ ⊗[ℤ] D.Y) (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
      (negative positive : List D.I) (negative' positive' : List E.I),
      e.toLinearMap = c.pushCocharacter.baseChange ℚ ∧
      ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
        ∃ (B : MarkedFibre M K) (B' : MarkedFibre M' K)
          (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup) A p)
          (C' : LocalComparison (j := identityPoints M' K) (Wf := E.datum.weylGroup) A' (e p)),
        SplitPointComparison B false C ∧ SplitPointComparison B' true C' ∧
        C.Bruhat (Nat.card (residue K)) ∧ C'.Bruhat (Nat.card (residue K)) ∧
        CentralComparison c (integralPointHom c.map (integralRing K)) C C' e ∧
        C'.G₀.Normal ∧
        (∀ (n : C.N) g, g ∈ C.I.map (MulAut.conj (n : FieldPoints M K)).toMonoidHom ↔
          C.chart.atPoint (C.affine n p) g) ∧
        (∀ (n : C'.N) g, g ∈ C'.I.map (MulAut.conj (n : FieldPoints M' K)).toMonoidHom ↔
          C'.chart.atPoint (C'.affine n (e p)) g) ∧
        (∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support) ∧
        (∀ w, ∀ a ∈ C'.localIwahori.normalizer.word w, a ∈ E.base.support) ∧
        C.chart.negative = negative ∧ C.chart.positive = positive ∧
        C'.chart.negative = negative' ∧ C'.chart.positive = positive' := by
  classical
  intro A A'
  let _ := D.finiteRoots
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := D.reduced
  let _ := E.finiteRoots
  let _ := E.freeY
  let _ := E.finiteY
  let _ := E.reduced
  obtain ⟨p, _, _, _, hS, hGeom⟩ :=
    ExceptionalAffineRootSystems.splitPinnedAlcoveGeometry (K := ℚ) D.datum D.base b rD
  obtain ⟨e, he, hr, hc, halcove⟩ := centralCoverApartment c b rD rE
  have hS' := splitPinnedSigns_ofCentralCover c p e hr hS
  have hreg' : A'.IsRegular (e p) := by
    intro a
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective a
    rw [hr]
    exact hGeom.regular a
  have hGeom' : AlcoveGeometry A' (e p) :=
    ExceptionalAffineRootSystems.affineApartmentGeometry A'
      (fun i j => ⟨E.datum.reflectionPerm i j,
        ExceptionalAffineRootSystems.splitReflectionClosed (K := ℚ) E.datum i j⟩)
      (ExceptionalAffineRootSystems.splitReducedDirections E.datum) (e p) hreg'
  obtain ⟨negative, positive, hn, hp⟩ := rootOrderings_exist D
  obtain ⟨negative', positive', hn', hp'⟩ := rootOrderings_exist E
  let B := Module.Free.chooseBasis ℤ D.Y
  let B' := Module.Free.chooseBasis ℤ E.Y
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ E.Y)
  refine ⟨p, e, negative, positive, negative', positive', he, ?_⟩
  intro K _ _ _ _
  obtain ⟨F⟩ := ExceptionalMarkedRootDescent.markedFibreExists M K
  obtain ⟨F'⟩ := ExceptionalMarkedRootDescent.markedFibreExists M' K
  obtain ⟨C, hC, hneg, hpos, hw, hTr, hBr⟩ := splitBruhatOfPinnedAlcove F B p false hS hGeom
    (fun _ => hD) (fun h => Bool.noConfusion h) negative positive hn hp
  obtain ⟨C', hC', hneg', hpos', hw', hTr', hBr'⟩ := splitBruhatOfPinnedAlcove F' B' (e p) true hS' hGeom'
    (fun h => Bool.noConfusion h) (fun _ => hE) negative' positive' hn' hp'
  let φ := integralPointHom c.map (integralRing K)
  obtain ⟨hpreI, hI, hpreN, hpreT₀, hpreT, hNormal⟩ := splitCentralIwahori c F F' C C' hC hC'
  have hI' : C'.I = C.I.map φ ⊔ C'.T₀ := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, t, rfl⟩ := (hI z).mp hz
      exact (C.I.map φ ⊔ C'.T₀).mul_mem ((le_sup_left : C.I.map φ ≤ C.I.map φ ⊔ C'.T₀)
        ⟨x, x.property, rfl⟩) ((le_sup_right : C'.T₀ ≤ C.I.map φ ⊔ C'.T₀) t.property)
    · apply sup_le
      · rintro z ⟨x, hx, rfl⟩
        exact (hI (φ x)).mpr ⟨⟨x, hx⟩, 1, (mul_one _).symm⟩
      · intro z hz
        exact (hI z).mpr ⟨1, ⟨z, hz⟩, by rw [Subgroup.coe_one, map_one, one_mul]⟩
  have haff := splitCentralAffine c hE C C' hC hC' B' hw e he hr hc
  have hrange : C.affine.range = A.affineWeylGroup := hC.2.2.2.2.2.2.2.2
  obtain ⟨hnormal, hordinary, hprod⟩ := ordinarySubgroup_ofCentralComparison C C' φ
    hNormal hI' hpreN hrange e c.rootEquiv hr hc haff
  exact ⟨F, F', C, C', hC, hC', hBr (ordinaryRange_normalizer C hrange), hBr' hordinary,
    ⟨fun _ => rfl, hpreI, hI, hpreN, hpreT₀, hpreT, haff, hprod, halcove p,
      ⟨c.rootEquiv, fun i => by simp only [hC.2.2.1, hC'.2.2.1, id_eq], hr, hc⟩⟩,
    hnormal, hTr, hTr', hw, hw', hneg, hpos, hneg', hpos'⟩

end SplitLevelAssembly

section AlcoveTypes

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots AlcoveGeometry alcoveStabilizer threshold)
open ValuativeRel
attribute [local instance] integerAlgebra

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G W : Type u} [Group G] [Group W] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- An alcove-preserving affine symmetry permutes its positively oriented
simple walls and carries the vertex of an omitted wall to that of the
permuted wall. -/
theorem alcoveStabilizerTypes (hGeom : AlcoveGeometry A p)
    (hReflection : A.ReflectionClosed) (hReduced : A.ReducedDirections) :
    let Ω := alcoveStabilizer A (A.alcove p)
    ∃ perm : Ω →* Equiv.Perm (A.SimpleWall p),
      (∀ (ω : Ω) (a : A.SimpleWall p),
        ω.val.val '' A.wallHyperplane a.val = A.wallHyperplane (perm ω a).val) ∧
      ∀ (ω : Ω) (a : A.SimpleWall p) (x : V), IsAlcoveVertex A p a x →
        IsAlcoveVertex A p (perm ω a) (ω.val.val x) := by
  intro Ω
  obtain ⟨act, hact⟩ := AffineArrangement.signedAction A hReflection hReduced
  let _ := act
  let emb : Ω →* A.symmetries :=
    ((A.extendedAffineWeylGroup.subtype).comp Ω.subtype).codRestrict _ (fun ω =>
      hGeom.extended_symmetries ω.val.property)
  let _ : MulAction Ω (J × ℤ) := MulAction.compHom (J × ℤ) emb
  have he (ω : Ω) (a : J × ℤ) (x : V) : A.wallValue (ω • a) (ω.val.val x) = A.wallValue a x :=
    (hact (emb ω) a).1.1 x
  have hpos_mono (ω : Ω) (a : J × ℤ) (ha : A.positive p a) : A.positive p (ω • a) := by
    have hp : p ∈ A.alcove p := fun _ h => h
    have h : (ω⁻¹ : Ω).val.val p ∈ A.alcove p :=
      Set.mem_image_of_mem _ hp |> fun hx => (ω⁻¹ : Ω).property ▸ hx
    change 0 < A.wallValue (ω • a) p
    have hh := he ω a ((ω⁻¹ : Ω).val.val p)
    change A.wallValue (ω • a) (ω.val.val (ω.val.val.symm p)) = _ at hh
    rw [AffineEquiv.apply_symm_apply] at hh
    rw [hh]
    exact h a ha
  have hpos (ω : Ω) (a : J × ℤ) : A.positive p (ω • a) ↔ A.positive p a :=
    ⟨fun ha => by simpa only [inv_smul_smul] using hpos_mono ω⁻¹ (ω • a) ha, hpos_mono ω a⟩
  have hsimple (ω : Ω) (a : A.SimpleWall p) : A.IsSimple p (ω • a.val) := by
    obtain ⟨ha, x, hx, hothers⟩ := a.property
    refine ⟨(hpos _ _).mpr ha, ω.val.val x, (he _ _ _).trans hx, ?_⟩
    intro b hb hne
    let c := ω⁻¹ • b
    have hbc : ω • c = b := smul_inv_smul ω b
    have hc : A.positive p c := (hpos ω⁻¹ b).mpr hb
    have hca : c ≠ a.val := fun h => hne (hbc.symm.trans (congrArg (ω • ·) h))
    change 0 < A.wallValue b (ω.val.val x)
    rw [← hbc, he]
    exact hothers c hc hca
  let A₀ : MulAction Ω (A.SimpleWall p) :=
    { smul := fun ω a => ⟨ω • a.val, hsimple ω a⟩
      one_smul := fun a => Subtype.ext (one_smul Ω a.val)
      mul_smul := fun ω τ a => Subtype.ext (mul_smul ω τ a.val) }
  let _ := A₀
  let perm : Ω →* Equiv.Perm (A.SimpleWall p) := MulAction.toPermHom Ω _
  have hperm (ω : Ω) (a : A.SimpleWall p) : (perm ω a).val = ω • a.val := rfl
  refine ⟨perm, ?_, ?_⟩
  · intro ω a
    ext y
    obtain ⟨x, rfl⟩ := ω.val.val.surjective y
    rw [Set.mem_image]
    change (∃ z, A.wallValue a.val z = 0 ∧ ω.val.val z = ω.val.val x) ↔
      A.wallValue (perm ω a).val (ω.val.val x) = 0
    rw [hperm, he]
    exact ⟨fun ⟨z, hz, hzx⟩ => (ω.val.val.injective hzx) ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  · intro ω a x hx
    refine ⟨?_, ?_⟩
    · intro b hb
      let c := ω⁻¹ • b
      have hbc : ω • c = b := smul_inv_smul ω b
      rw [← hbc, he]
      exact hx.1 c ((hpos ω⁻¹ b).mpr hb)
    · intro b
      obtain ⟨c, rfl⟩ := (perm ω).surjective b
      rw [hperm, he, hx.2 c]
      exact (perm ω).injective.ne_iff.symm

/-- Two rational points in one alcove impose the same integer thresholds
on every root parameter in the marked chart. -/
private theorem chartAtPoint_of_sameAlcove (C : LocalRootChart (j := j) A p)
    (hReflection : A.ReflectionClosed) (hReduced : A.ReducedDirections)
    (hp : A.IsRegular p) (x : V) (hx : x ∈ A.alcove p) (g : G) :
    C.atPoint x g ↔ C.atPoint p g := by
  have reg (a : J × ℤ) : A.wallValue a p ≠ 0 := fun h => hp a.1 ⟨-a.2, by
    rw [Int.cast_neg]
    exact (eq_neg_of_add_eq_zero_left h).symm⟩
  have sign := (AffineArrangement.alcove_iff A hReflection hReduced reg).mp hx
  have ht (a : J) : threshold (A.root a x) = threshold (A.root a p) := by
    apply le_antisymm
    · refine (threshold_le_iff _ _).2 ((sign (a, threshold (A.root a p))).1.mpr ?_)
      exact (threshold_le_iff _ _).1 le_rfl
    · refine (threshold_le_iff _ _).2 ((sign (a, threshold (A.root a x))).1.mp ?_)
      exact (threshold_le_iff _ _).1 le_rfl
  unfold LocalRootChart.atPoint
  simp only [ht]

/-- Lift the alcove type quotient to the actual normalizer. Its lifts
preserve the Iwahori by the scaled chart comparison. -/
theorem typeQuotientOfTranslatedChart
    (C : LocalComparison (j := j) (Wf := W) A p)
    (normal : C.G₀.Normal)
    (ordinary : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype)
    (extended : C.affine.range = A.extendedAffineWeylGroup)
    (hReflection : A.ReflectionClosed) (hReduced : A.ReducedDirections)
    (vertex : ∀ a : A.SimpleWall p, ∃! x, IsAlcoveVertex A p a x)
    (base : ∀ g, g ∈ C.I ↔ C.chart.atPoint p g)
    (translated : ∀ (n : C.N) (g : G),
      g ∈ C.I.map (MulAut.conj (n : G)).toMonoidHom ↔
        C.chart.atPoint (C.affine n p) g) :
    Nonempty C.TypeQuotient := by
  obtain ⟨e, lift, ha, hq⟩ := typeQuotientOfAffineRange C normal ordinary extended
  obtain ⟨perm, hw, hv⟩ := alcoveStabilizerTypes C.geometry hReflection hReduced
  refine ⟨⟨normal, e, lift, ha, hq, ?_, perm, hw, vertex, hv⟩⟩
  intro ω
  ext g
  refine (translated _ g).trans ?_
  rw [ha]
  have hp : ω.val.val p ∈ A.alcove p := by
    have hx := Set.mem_image_of_mem ω.val.val (show p ∈ A.alcove p from fun _ h => h)
    exact (Set.ext_iff.mp ω.property (ω.val.val p)).mp hx
  exact (chartAtPoint_of_sameAlcove C.chart hReflection hReduced C.geometry.regular _ hp g).trans
    (base g).symm

end AlcoveTypes

section ScalarDescent

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Specs.IntegralSemisimpleModel (IntegralScheme Model Integers integerAlgebra integralSpec
  TorusValues torusPoint IntegralPoints)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRing changeRingHom
  cellValue cellValuePoint mapCellValues)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open Specs.Pinning (BasedRootDatum)
open private cellValuePoint_bijective torusPoint_bijective torusPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private splitMarkedNormalizerWord fibreNormalizerPoint_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

open scoped TensorProduct
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K]
  {D : BasedRootDatum.{u}} {M : Model D}

set_option backward.isDefEq.respectTransparency false in
/-- A point of the integral test functor factors through a given
monomorphism if its scalar extension does. -/
private theorem factor_of_scalar (f : F →+* K)
    {X Y : IntegralScheme.{u}} (i : X ⟶ Y) [Mono i.left]
    (g : integralSpec.obj (.op (integralRing F)) ⟶ Y)
    (b : integralSpec.obj (.op (integralRing K)) ⟶ X)
    (hb : b ≫ i = changeRing (integralRingMap f) g) :
    ∃ a, a ≫ i = g := by
  let p := integralSpec.map (integralRingMap f).op
  let _ : Algebra F K := f.toAlgebra
  have hf : f.FaithfullyFlat :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := F) (S := K)).mpr inferInstance
  have he : p.left = Spec.map (CommRingCat.ofHom f) := rfl
  have h₁ : Flat p.left := he ▸
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hf).1
  have h₂ : Surjective p.left := he ▸
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hf).2
  have h₃ : QuasiCompact p.left := he ▸ inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  let _ : EffectiveEpi p.left := inferInstance
  have hb' : b.left ≫ i.left = p.left ≫ g.left := congrArg Over.Hom.left hb
  have hdesc {W : Scheme.{u}} (a a' : W ⟶ _) (h : a ≫ p.left = a' ≫ p.left) :
      a ≫ b.left = a' ≫ b.left := by
    apply (cancel_mono i.left).mp
    calc
      (a ≫ b.left) ≫ i.left = (a ≫ p.left) ≫ g.left := by rw [Category.assoc, hb', Category.assoc]
      _ = (a' ≫ p.left) ≫ g.left := congrArg (· ≫ g.left) h
      _ = (a' ≫ b.left) ≫ i.left := by
        rw [Category.assoc a' b.left i.left, hb', Category.assoc a' p.left g.left]
  let a := EffectiveEpi.desc p.left b.left hdesc
  have ha : a ≫ i.left = g.left := by
    rw [← cancel_epi p.left, ← Category.assoc, EffectiveEpi.fac]
    exact hb'
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← Over.w i, ← Category.assoc, ha, Over.w g]

private theorem markedWord_mem_splitNormalizer [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {p : ℚ ⊗[ℤ] D.Y}
    {B : MarkedFibre M K} {ad : Bool}
    (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p) (hC : SplitPointComparison B ad C)
    (l : List D.I) (hl : ∀ a ∈ l, a ∈ D.base.support) :
    markedWeylWord M.toIntegralMarking (integralRing K) l ∈ C.N := by
  let N := C.localIwahori.normalizer
  let q := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  obtain ⟨_, F, hF, _⟩ := hC.2.1
  let _ := F.torusComm
  obtain ⟨x, hx, hxq⟩ := splitMarkedNormalizerWord F l hl
  obtain ⟨y, hy, hyq⟩ := hF (N.lift q)
  have hk : F.label (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxq, hyq, N.lift_label, MonoidHom.id_apply, mul_inv_cancel]
  obtain ⟨T, hT, _⟩ := ExceptionalValuedTorusNormalizer.fibreNormalizerTorusAction F
  let t := T.symm ⟨x * y⁻¹, hk⟩
  have he : F.point (x * y⁻¹) = torusPoint D (integralRing K) t ≫ M.torus.hom.hom := by
    rw [← hT t, T.apply_symm_apply]
  have hmem : F.point (x * y⁻¹) ∈ N.torus := (N.torusPoints _).mpr ⟨t, he⟩
  have hproduct := C.N.mul_mem (N.torus_le hmem) (N.lift q).property
  change F.point (x * y⁻¹) * (N.lift q : FieldPoints M K) ∈ C.N at hproduct
  have hy' : F.point y = (N.lift q : FieldPoints M K) := hy
  rw [map_mul, map_inv, hx, hy', inv_mul_cancel_right] at hproduct
  exact hproduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- The full split torus and its marked normalizer pull back under scalar
extension of the integral model. The normalization of the valuation is unnecessary
for these two subgroup identities. -/
theorem splitTorusNormalizerScalar
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {p : ℚ ⊗[ℤ] D.Y} {B : MarkedFibre M F} {B' : MarkedFibre M K} {ad : Bool}
    (C : LocalComparison (j := identityPoints M F) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (C' : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (hC : SplitPointComparison B ad C) (hC' : SplitPointComparison B' ad C')
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ C'.localIwahori.normalizer.word w, a ∈ D.base.support)
    (f : F →+* K) :
    let s := scalarPoints M f
    C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus ∧
      C'.N.comap s = C.N := by
  intro s
  let N := C.localIwahori.normalizer
  let N' := C'.localIwahori.normalizer
  let a := integralRingMap f
  let _ : IsClosedImmersion M.torus.hom.hom.left := M.torusClosed
  have hT (g : FieldPoints M F) : s g ∈ N'.torus ↔ g ∈ N.torus := by
    rw [N'.torusPoints, N.torusPoints]
    constructor
    · rintro ⟨t, ht⟩
      have hb := factor_of_scalar f M.torus.hom.hom g (torusPoint D _ t) ht.symm
      obtain ⟨b, hb⟩ := hb
      obtain ⟨z, rfl⟩ := (torusPoint_bijective D (integralRing F)).surjective b
      exact ⟨z, hb.symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨(Units.map f.toMonoidHom).comp t, ?_⟩
      change changeRing a g = _
      rw [show g = _ from ht]
      unfold changeRing
      rw [← Category.assoc]
      exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural a t)
  refine ⟨SetLike.ext hT, ?_⟩
  ext g
  change s g ∈ C'.N ↔ g ∈ C.N
  constructor
  · intro hg
    let n : C'.N := ⟨s g, hg⟩
    let l := N'.word (N'.label n)
    let v := markedWeylWord M.toIntegralMarking (integralRing F) l
    have hv : v ∈ C.N := markedWord_mem_splitNormalizer C hC l (hword' _)
    have ht : s (g * v⁻¹) ∈ N'.torus := by
      have h := (N'.torusPart n).property
      change (s g * (N'.lift (N'.label n) : FieldPoints M K)⁻¹) ∈ N'.torus at h
      rw [show (N'.lift (N'.label n) : FieldPoints M K) = _ from N'.lift_point _] at h
      rw [map_mul, map_inv, show s v = _ from markedWeylWord_map _ a l]
      exact h
    simpa only [inv_mul_cancel_right] using C.N.mul_mem (N.torus_le ((hT _).mp ht)) hv
  · intro hg
    let n : C.N := ⟨g, hg⟩
    let l := N.word (N.label n)
    have hv := markedWord_mem_splitNormalizer C' hC' l (hword _)
    have hd : s (N.torusPart n) ∈ N'.torus := (hT _).mpr (N.torusPart n).property
    have hprod := C'.N.mul_mem (N'.torus_le hd) hv
    change s ((g * (N.lift (N.label n) : FieldPoints M F)⁻¹)) *
      markedWeylWord M.toIntegralMarking (integralRing K) l ∈ C'.N at hprod
    rw [show markedWeylWord M.toIntegralMarking (integralRing K) l =
      s (N.lift (N.label n)) from (congrArg s (N.lift_point _)).trans
        (markedWeylWord_map _ a l) |>.symm, ← map_mul, inv_mul_cancel_right] at hprod
    exact hprod

section SplitScalarLabels

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

set_option backward.isDefEq.respectTransparency false in
/-- An embedding preserving normalized valuations preserves both the
finite marked normalizer label and the affine translation. -/
theorem splitNormalizerLabelsScalar
    {p : ℚ ⊗[ℤ] D.Y} {B : MarkedFibre M F} {B' : MarkedFibre M K} {ad : Bool}
    (C : LocalComparison (j := identityPoints M F) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (C' : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (hC : SplitPointComparison B ad C) (hC' : SplitPointComparison B' ad C')
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    {index : Type u} [Fintype index] (b : Module.Basis index ℤ D.Y)
    (f : F →+* K) (hv : ∀ x, normalizedValuation K (f x) = normalizedValuation F x)
    (n : C.N) (n' : C'.N) (hn' : (n' : FieldPoints M K) = scalarPoints M f n) :
    C'.affine n' = C.affine n ∧
      C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n := by
  let N := C.localIwahori.normalizer
  let N' := C'.localIwahori.normalizer
  let l := N.word (N.label n)
  let s := scalarPoints M f
  let a := integralRingMap f
  obtain ⟨t, ht, hn⟩ := normalizerTorusWord N n
  let t' := (Units.map f.toMonoidHom).comp t
  have hmap : s (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M F) =
      (torusPoint D _ t' ≫ M.torus.hom.hom : FieldPoints M K) := by
    change integralSpec.map a.op ≫ torusPoint D _ t ≫ M.torus.hom.hom = _
    rw [← Category.assoc]
    exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural a t)
  have hn'' : identityPoints M K n' = (torusPoint D _ t' ≫ M.torus.hom.hom : FieldPoints M K) *
      markedWeylWord M.toIntegralMarking (integralRing K) l := by
    change (n' : FieldPoints M K) = _
    rw [hn', show (n : FieldPoints M F) = _ from hn, map_mul, hmap]
    exact congrArg (_ * ·) (markedWeylWord_map _ a l)
  obtain ⟨hLabel, hLog⟩ := labelAndTranslationOfWord C' (MonoidHom.id _) hC'.2.1 b n'
    l (hword _) t' hn''
  have hLab : N'.label n' = N.label n :=
    hLabel.trans (hC.2.1.2.choose_spec.2 (N.label n))
  have htors : (N'.translation (N'.torusPart n')).toAdd = (N.translation (N.torusPart n)).toAdd := by
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ (N'.translation (N'.torusPart n')).toAdd =
      D.datum.toLinearMap χ (N.translation (N.torusPart n)).toAdd
    rw [hLog χ, N.characterLog _ t ht χ]
    exact congrArg WithZero.log (hv _)
  refine ⟨AffineEquiv.ext fun x => ?_, hLab⟩
  rw [hC'.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, htors, hLab]

end SplitScalarLabels

section ScalarIwahori

open Specs.IntegralSemisimpleModel (cellMap)
open Specs.ExceptionalIwahoriCongruence (CellValues)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori)
open Specs.ExceptionalIwahoriImageComparison (markedBorelReduction)
open Specs.OrderedRootProducts (Enumerates)
open private iwahoriValuationChart from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private normalizedValuation_le_one normalizedValuation_lt_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem splitIwahori_absoluteChart
    {W : Type u} [Group W] (P : LocalIwahori (j := identityPoints M K) W)
    (negative positive : List D.I)
    (hn : Enumerates negative {a | ¬D.base.IsPos a}) (hp : Enumerates positive {a | D.base.IsPos a})
    (g : FieldPoints M K) :
    g ∈ P.iwahori ↔ ∃ z : CellValues D (integralRing K) negative positive,
      cellValue M.toIntegralMarking (integralRing K) negative positive z = g ∧
      (∀ χ, normalizedValuation K (z.2.1 χ : K) = 1) ∧
      (∀ l, normalizedValuation K (z.1 l) < 1) ∧
      ∀ l, normalizedValuation K (z.2.2 l) ≤ 1 := by
  let B := P.residueFibre
  let H := (identityPoints M K).range
  let g' : H := ⟨g, ⟨g, rfl⟩⟩
  let k := residue K
  obtain ⟨C, hC, hchart⟩ := ExceptionalIwahoriCongruence.markedFibreBorel M.toIntegralMarking k
    B.line B.realization B.groupIso B.torusIso B.coordinate B.torus_comm
    (fun i x => B.root_eval i (CommAlgCat.of k k) x) negative positive hp
  have hB : (P.residueBorel : Set (FieldPoints M k)) = ↑C := P.borel_eq.trans hC.symm
  have hRaw := iwahoriValuationChart M.toIntegralMarking H (valuation K)
    negative positive hn hp P.residueBorel (hB.trans hchart) g'
  change g ∈ P.iwahori ↔ _ at hRaw
  have hinj := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking negative positive hn hp).1
    (integralRing K)
  simp only [valuation_unit_iff, normalizedValuation_le_one, normalizedValuation_lt_one]
  refine hRaw.trans ⟨ExistsUnique.exists, ?_⟩
  rintro ⟨z, hz⟩
  exact ⟨z, hz, fun w hw => hinj (hw.1.trans hz.1.symm)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Positive Borel reduction in the marked split model pulls back along
a field embedding preserving the normalized valuation. -/
theorem splitIwahoriScalar
    {W W' : Type u} [Group W] [Group W']
    (P : LocalIwahori (j := identityPoints M F) W)
    (P' : LocalIwahori (j := identityPoints M K) W')
    (f : F →+* K) (hv : ∀ x, normalizedValuation K (f x) = normalizedValuation F x)
    (negative positive : List D.I) (hn : Enumerates negative {a | ¬D.base.IsPos a})
    (hp : Enumerates positive {a | D.base.IsPos a}) :
    P'.iwahori.comap (scalarPoints M f) = P.iwahori := by
  let i := integralRingMap f
  let s := scalarPoints M f
  let c := cellMap M.line M.torus M.root negative positive
  let h := ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking negative positive hn hp
  have hco (z : CellValues D (integralRing F) negative positive) :
      ((∀ χ, normalizedValuation K ((mapCellValues i z).2.1 χ : K) = 1) ∧
        (∀ l, normalizedValuation K ((mapCellValues i z).1 l) < 1) ∧
        ∀ l, normalizedValuation K ((mapCellValues i z).2.2 l) ≤ 1) ↔
      (∀ χ, normalizedValuation F (z.2.1 χ : F) = 1) ∧
        (∀ l, normalizedValuation F (z.1 l) < 1) ∧
        ∀ l, normalizedValuation F (z.2.2 l) ≤ 1 := by
    change ((∀ χ, normalizedValuation K (f (z.2.1 χ : F)) = 1) ∧
      (∀ l, normalizedValuation K (f (z.1 l)) < 1) ∧
      ∀ l, normalizedValuation K (f (z.2.2 l)) ≤ 1) ↔ _
    simp only [hv]
  have : IsOpenImmersion c.left := M.openCell negative positive hn hp
  ext g
  change s g ∈ P'.iwahori ↔ g ∈ P.iwahori
  rw [splitIwahori_absoluteChart P' negative positive hn hp, splitIwahori_absoluteChart P negative positive hn hp]
  constructor
  · rintro ⟨z', hz', hv'⟩
    have hc : cellValuePoint M.line (integralRing K) negative positive z' ≫ c =
      changeRing i g := hz'
    obtain ⟨b, hb⟩ := factor_of_scalar f c g _ hc
    obtain ⟨z, rfl⟩ := (cellValuePoint_bijective M.line (integralRing F) negative positive).surjective b
    have hb' : cellValue M.toIntegralMarking (integralRing F) negative positive z = g := hb
    have he : mapCellValues i z = z' := h.1 _ ((h.2 i z).symm.trans (hb' ▸ hz'.symm))
    exact ⟨z, hb', (hco z).mp (he.symm ▸ hv')⟩
  · rintro ⟨z, rfl, hv₀⟩
    exact ⟨mapCellValues i z, (h.2 i z).symm, (hco z).mpr hv₀⟩

end ScalarIwahori

end ScalarDescent

section FoldedWords

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalMarkedRootDescent (SimpleRootOrbit)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation orbitWeylReflection fixedWeylGroup)
open private reflection_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

universe u

private noncomputable def simpleOrbitBlock (D : BasedRootDatum.{u}) (τ : BasedIso D D)
    (i : D.base.support) : SimpleRootOrbit D := by
  classical
  exact (i, if simplePermutation D τ i = i then none else some (simplePermutation D τ i))

private theorem simpleOrbitBlock_word (D : BasedRootDatum.{u}) (τ : BasedIso D D)
    (i : D.base.support) :
    (((simpleOrbitBlock D τ i).roots).map (RootPairing.weylGroup.ofIdx D.datum)).prod =
      orbitWeylReflection D τ i := by
  classical
  by_cases hi : simplePermutation D τ i = i
  · simp [simpleOrbitBlock, orbitWeylReflection, hi, SimpleRootOrbit.roots]
  · simp [simpleOrbitBlock, orbitWeylReflection, hi, SimpleRootOrbit.roots]

private theorem simpleOrbitReflection_inv (D : BasedRootDatum.{u}) (τ : BasedIso D D)
    (horthogonal : ∀ i : D.base.support, simplePermutation D τ i ≠ i →
      D.datum.pairing (simplePermutation D τ i).val i.val = 0)
    (i : D.base.support) : (orbitWeylReflection D τ i)⁻¹ = orbitWeylReflection D τ i := by
  let q := simplePermutation D τ
  let s := RootPairing.weylGroup.ofIdx D.datum
  have hinv (j : D.I) : (s j)⁻¹ = s j :=
    Subtype.ext (RootPairing.Equiv.reflection_inv D.datum j)
  by_cases hi : q i = i
  · rw [orbitWeylReflection, ite_eq_left hi, hinv]
  · have hfix : D.datum.reflectionPerm i.val (q i).val = (q i).val := by
      apply D.datum.root.injective
      rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_root, horthogonal i hi, zero_smul, sub_zero]
    have hcomm : Commute (s i.val) (s (q i).val) := by
      apply Subtype.ext
      have h := reflection_natural D (s i.val).val (q i).val
      change (s i.val).val * (s (q i).val).val =
        RootPairing.Equiv.reflection D.datum (D.datum.reflectionPerm i.val (q i).val) * (s i.val).val at h
      rwa [hfix] at h
    rw [orbitWeylReflection, ite_eq_right hi, mul_inv_rev, hinv, hinv, hcomm.eq]

/-- Each fixed finite Weyl label has a word in singleton and orthogonal
paired simple orbits of the diagram involution. -/
theorem foldedFixedWeylWords (D : BasedRootDatum.{u}) (τ : BasedIso D D)
    (hinv : Function.Involutive τ.val.indexEquiv)
    (horthogonal : ∀ i : D.base.support, simplePermutation D τ i ≠ i →
      D.datum.pairing (simplePermutation D τ i).val i.val = 0) :
    ∃ word : fixedWeylGroup D τ → List (SimpleRootOrbit D),
      (∀ w, ∀ o ∈ word w, ∃ i, o = simpleOrbitBlock D τ i) ∧
      ∀ w, (((word w).flatMap SimpleRootOrbit.roots).map (RootPairing.weylGroup.ofIdx D.datum)).prod =
        w.val := by
  classical
  let r := orbitWeylReflection D τ
  have hmem (w : fixedWeylGroup D τ) : w.val ∈ Subgroup.closure (Set.range r) := by
    have hw := w.property
    change w.val.val ∈ Subgroup.centralizer {τ.val} at hw
    apply ((ExceptionalValuedTorusNormalizer.fixedWeylGeneration D τ hinv horthogonal).1 w.val).2
    exact ((Subgroup.mem_centralizer_singleton_iff.mp hw).symm)
  have hwords (w : D.datum.weylGroup) (hw : w ∈ Subgroup.closure (Set.range r)) :
      ∃ l : List D.base.support, (l.map r).prod = w := by
    induction hw using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact ⟨[i], by simp⟩
    | one => exact ⟨[], rfl⟩
    | mul a b _ _ ha hb =>
      obtain ⟨la, rfl⟩ := ha
      obtain ⟨lb, rfl⟩ := hb
      exact ⟨la ++ lb, by rw [List.map_append, List.prod_append]⟩
    | inv a _ ha =>
      obtain ⟨l, rfl⟩ := ha
      refine ⟨l.reverse, ?_⟩
      rw [List.map_reverse, List.prod_inv_reverse, List.map_map]
      simp only [Function.comp_def, r, simpleOrbitReflection_inv D τ horthogonal]
  choose l hl using fun w => hwords w.val (hmem w)
  let word (w : fixedWeylGroup D τ) := (l w).map (simpleOrbitBlock D τ)
  have hprod (p : List D.base.support) :
      (((p.map (simpleOrbitBlock D τ)).flatMap SimpleRootOrbit.roots).map
        (RootPairing.weylGroup.ofIdx D.datum)).prod = (p.map r).prod := by
    induction p with
    | nil => rfl
    | cons i p ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, List.prod_append, List.prod_cons]
      rw [simpleOrbitBlock_word D τ i, ih]
  exact ⟨word, fun w o ho => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
    exact ⟨i, rfl⟩, fun w => (hprod (l w)).trans (hl w)⟩

end FoldedWords

section OrdinaryScalarPullback

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open ValuativeRel
attribute [local instance] integerAlgebra

universe u v

variable {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {G H W : Type u} [Group G] [Group H] [Group W]
  {j : G →* FieldPoints M F} {j' : H →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  (C : LocalComparison (j := j) (Wf := W) A p)
  (C' : LocalComparison (j := j') (Wf := W) A p)

private theorem normalizer_mem_ordinary
    (ho : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype)
    (n : C.N) :
    (n : G) ∈ C.G₀ ↔ C.affine n ∈ A.affineWeylGroup := by
  have hmem : (n : G) ∈ C.G₀ ↔ (n : G) ∈ C.G₀ ⊓ C.N :=
    ⟨fun h => ⟨h, n.property⟩, fun h => h.1⟩
  rw [hmem, ho]
  constructor
  · rintro ⟨m, hm, he⟩
    exact (show m = n from Subtype.ext he) ▸ hm
  · intro h
    exact ⟨n, h, rfl⟩

private theorem ordinary_sup_normalizer : C.G₀ ⊔ C.N = ⊤ := by
  have hgen : C.I ⊔ C.N = ⊤ := C.localIwahori.generation
  exact top_unique (hgen ▸ sup_le_sup (show C.I ≤ C.G₀ from le_sup_left) le_rfl)

/-- A map preserving the normalizer and its affine labels detects the
ordinary subgroup once the ordinary normalizer intersections are known. -/
theorem ordinarySubgroup_pullback (s : G →* H)
    (hI : C.I ≤ C'.I.comap s) (hN : C.N ≤ C'.N.comap s)
    (hAff : ∀ (n : C.N) (n' : C'.N), (n' : H) = s n → C'.affine n' = C.affine n)
    (norm : C.G₀.Normal)
    (hOrd : C.G₀ ⊓ C.N = (A.affineWeylGroup.comap C.affine).map C.N.subtype)
    (hOrd' : C'.G₀ ⊓ C'.N = (A.affineWeylGroup.comap C'.affine).map C'.N.subtype) :
    C'.G₀.comap s = C.G₀ := by
  let _ := norm
  have hN₀ (n : C.N) : s (n : G) ∈ C'.G₀ ↔ (n : G) ∈ C.G₀ := by
    let n' : C'.N := ⟨s n, hN n.property⟩
    change (n' : H) ∈ C'.G₀ ↔ _
    rw [normalizer_mem_ordinary C' hOrd', normalizer_mem_ordinary C hOrd, hAff n n' rfl]
  have hforward : C.G₀ ≤ C'.G₀.comap s := by
    refine sup_le (hI.trans (Subgroup.comap_mono (show C'.I ≤ C'.G₀ from le_sup_left))) ?_
    rintro _ ⟨n, hn, rfl⟩
    change s (n : G) ∈ C'.G₀
    exact (hN₀ n).mpr ((normalizer_mem_ordinary C hOrd n).mpr hn)
  refine le_antisymm ?_ hforward
  intro g hg
  have hU : g ∈ C.G₀ ⊔ C.N := ordinary_sup_normalizer C ▸ Subgroup.mem_top g
  obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hU
  have hsh : s h ∈ C'.G₀ := hforward hh
  have hsn : s n ∈ C'.G₀ := by
    change s (h * n) ∈ C'.G₀ at hg
    rw [map_mul] at hg
    simpa only [inv_mul_cancel_left] using C'.G₀.mul_mem (C'.G₀.inv_mem hsh) hg
  exact C.G₀.mul_mem hh ((hN₀ ⟨n, hn⟩).mp hsn)

/-- Comparison on length-zero lifts determines the map on the whole
type quotient, since the Iwahori and normalizer generate. -/
theorem typeQuotientTransport_of_lifts
    (Q : C.TypeQuotient) (Q' : C'.TypeQuotient) (s : G →* H)
    (sG₀ : C.G₀ ≤ C'.G₀.comap s)
    (α : alcoveStabilizer A (A.alcove p) →* alcoveStabilizer A (A.alcove p))
    (lifts : ∀ ω, s (Q.lift ω) * (Q'.lift (α ω) : H)⁻¹ ∈ C'.T₀) :
    TypeQuotientTransport Q Q' s α := by
  let _ := Q.normal
  let _ := Q'.normal
  let f := Q.quotient.toMonoidHom.comp (QuotientGroup.mk' C.G₀)
  let f' := Q'.quotient.toMonoidHom.comp (QuotientGroup.mk' C'.G₀)
  let a := (f'.comp s).eqLocus (α.comp f)
  have hf (g : G) (hg : g ∈ C.G₀) : f g = 1 := by
    change Q.quotient (QuotientGroup.mk g) = 1
    rw [(QuotientGroup.eq_one_iff g).mpr hg, map_one]
  have hf' (h : H) (hh : h ∈ C'.G₀) : f' h = 1 := by
    change Q'.quotient (QuotientGroup.mk h) = 1
    rw [(QuotientGroup.eq_one_iff h).mpr hh, map_one]
  have h₀ : C.G₀ ≤ a := by
    intro g hg
    change f' (s g) = α (f g)
    rw [hf g hg, hf' _ (sG₀ hg), map_one]
  have hN : C.N ≤ a := by
    intro g _
    let ω := f g
    have hω : f (Q.lift ω) = ω := Q.quotient_lift ω
    have hk : g * (Q.lift ω : G)⁻¹ ∈ C.G₀ := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply Q.quotient.injective
      change f (g * (Q.lift ω : G)⁻¹) = Q.quotient 1
      rw [map_mul, map_inv, map_one, hω]
      exact mul_inv_cancel _
    have hk' : s (Q.lift ω) * (Q'.lift (α ω) : H)⁻¹ ∈ C'.G₀ :=
      (show C'.I ≤ C'.G₀ from le_sup_left) (unitTorus_le_iwahori C' (lifts ω))
    have hg := hf' _ (sG₀ hk)
    rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at hg
    have hl := hf' _ hk'
    rw [map_mul, map_inv, mul_inv_eq_one] at hl
    change f' (s g) = α (f g)
    exact hg.trans (hl.trans (Q'.quotient_lift (α ω)))
  have htop : a = ⊤ := top_unique (ordinary_sup_normalizer C ▸ sup_le h₀ hN)
  exact ⟨fun g => (htop.symm ▸ Subgroup.mem_top g : g ∈ a), lifts⟩

end OrdinaryScalarPullback

section TransportedFoldedRoots

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineRootSystems (FoldedRootDirection orbitFirst orbitSecond e6Partner
  e6Cartan basedOrbitReflection)
open Specs.ExceptionalMarkedRootDescent (SimpleRootOrbit TransportedOrbit transportedLabels weylWordPerm)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation orbitWeylReflection)
open private weylWord_index from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

universe u

private theorem weylWordPerm_append {D : BasedRootDatum.{u}} (l m : List D.I) :
    weylWordPerm (l ++ m) = weylWordPerm l * weylWordPerm m := by
  induction l with
  | nil => simp [weylWordPerm]
  | cons i l ih =>
    change D.datum.reflectionPerm i * weylWordPerm (l ++ m) =
      D.datum.reflectionPerm i * weylWordPerm l * weylWordPerm m
    rw [ih, mul_assoc]

set_option maxHeartbeats 600000 in
/-- Each normalized relative direction has a transported simple orbit
whose ordered absolute labels are precisely its one or two roots. -/
theorem e6TransportedRootBlocks (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (τ : BasedIso D D) (A : FoldedApartment τ) (numbering : ExceptionalNumbering D 6 b)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i))
    (hinv : Function.Involutive τ.val.indexEquiv) :
    ∃ block : FoldedRootDirection → TransportedOrbit D,
      (∀ a, ∃ i, (block a).1 = simpleOrbitBlock D τ i) ∧
      (∀ a o, o ∈ (block a).2 → ∃ i, o = simpleOrbitBlock D τ i) ∧
      (∀ a, (transportedLabels (block a)).Nodup) ∧
      ∀ a i, i ∈ transportedLabels (block a) ↔ A.direction i = a := by
  classical
  let _ := D.finiteRoots
  let _ := D.reduced
  let σ := τ.val.indexEquiv
  let t := simplePermutation D τ
  let S := simpleOrbitBlock D τ
  let s := RootPairing.weylGroup.ofIdx D.datum
  have hCt (i j : Fin 6) : e6Cartan i j = D.datum.pairing (b i) (b j) :=
    (congrFun (congrFun e6_standardCartan.symm i) j).trans (numbering.2 i j).symm
  have hOrth (i : D.base.support) (h : t i ≠ i) :
      D.datum.pairing (t i).val i.val = 0 := by
    have he : σ i.val ≠ i.val := fun h' => h (Subtype.ext h')
    have he' : σ (σ i.val) ≠ σ i.val := σ.injective.ne he
    have hz := A.orthogonal (σ i.val) he'
    rw [hinv i.val] at hz
    exact hz
  obtain ⟨_, hOrbit⟩ :=
    ExceptionalAffineRootSystems.e6BasedOrbitTransport D.datum D.base b τ.val hτ hCt
  have hp (j : Fin 4) : e6Partner (orbitFirst j) = orbitSecond j := by
    fin_cases j <;> decide
  have hMate (j : Fin 4) : t (b (orbitFirst j)) = b (orbitSecond j) :=
    Subtype.ext ((hτ _).trans (congrArg (fun j : Fin 6 => (b j).val) (hp j)))
  let orbit (j : Fin 4) := S (b (orbitFirst j))
  have hroots (j : Fin 4) : (orbit j).roots =
      if orbitFirst j = orbitSecond j then [(b (orbitFirst j)).val]
      else [(b (orbitFirst j)).val, (b (orbitSecond j)).val] := by
    change (b (orbitFirst j)).val ::
      (if t (b (orbitFirst j)) = b (orbitFirst j) then none else some (t (b (orbitFirst j)))).toList.map
        Subtype.val = _
    by_cases h : orbitFirst j = orbitSecond j
    · have he : t (b (orbitFirst j)) = b (orbitFirst j) := (hMate j).trans (congrArg b h.symm)
      rw [ite_eq_left h, ite_eq_left he]
      rfl
    · have he : t (b (orbitFirst j)) ≠ b (orbitFirst j) := fun e =>
        h (b.injective ((hMate j).symm.trans e)).symm
      rw [ite_eq_right h, ite_eq_right he, hMate j]
      rfl
  have hPerm (j : Fin 4) (x : D.I) :
      weylWordPerm (orbit j).roots x = basedOrbitReflection D.datum D.base b j x := by
    rw [hroots, basedOrbitReflection]
    split <;> simp [weylWordPerm]
  let mkWord (w : List (Fin 4)) := (w.map orbit).flatMap SimpleRootOrbit.roots
  have hWord (w : List (Fin 4)) (x : D.I) :
      weylWordPerm (mkWord w) x = w.foldr (basedOrbitReflection D.datum D.base b) x := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      change weylWordPerm ((orbit i).roots ++ mkWord w) x =
        basedOrbitReflection D.datum D.base b i (w.foldr (basedOrbitReflection D.datum D.base b) x)
      rw [weylWordPerm_append]
      change weylWordPerm (orbit i).roots (weylWordPerm (mkWord w) x) = _
      rw [hPerm, ih]
  have hComm (w : List (Fin 4)) (x : D.I) :
      weylWordPerm (mkWord w) (σ x) = σ (weylWordPerm (mkWord w) x) := by
    let T := Subgroup.closure (Set.range (orbitWeylReflection D τ))
    have ht : (List.map s (mkWord w)).prod ∈ T := by
      induction w with
      | nil => exact T.one_mem
      | cons i w ih =>
        change (List.map s ((orbit i).roots ++ mkWord w)).prod ∈ T
        rw [List.map_append, List.prod_append, simpleOrbitBlock_word]
        exact T.mul_mem (Subgroup.subset_closure ⟨b (orbitFirst i), rfl⟩) ih
    have hc := ((ExceptionalValuedTorusNormalizer.fixedWeylGeneration D τ hinv hOrth).1 _).mp ht
    have h := congrArg (fun f : D.datum.Aut => f.indexEquiv x) hc.eq.symm
    rw [weylWord_index]
    exact h
  have hex (a : FoldedRootDirection) :
      ∃ o : TransportedOrbit D,
        (∃ i, o.1 = S i) ∧
        (∀ op ∈ o.2, ∃ i, op = S i) ∧
        (transportedLabels o).Nodup ∧
        ∀ i, i ∈ transportedLabels o ↔ A.direction i = a := by
    obtain ⟨x, rfl⟩ := A.surjective a
    obtain ⟨j, w, hor, hfix⟩ := hOrbit x
    let o : TransportedOrbit D := (orbit j, w.map orbit)
    let e := weylWordPerm (mkWord w)
    let u := e (b (orbitFirst j)).val
    let v := e (b (orbitSecond j)).val
    have hchoices : x = u ∨ x = v := by
      have h₁ : w.foldr (basedOrbitReflection D.datum D.base b) (b (orbitFirst j)).val = u :=
        (hWord w _).symm
      have h₂ : w.foldr (basedOrbitReflection D.datum D.base b) (b (orbitSecond j)).val = v :=
        (hWord w _).symm
      rw [h₁, h₂] at hor
      exact hor
    have hv : v = σ u := by
      change e (b (orbitSecond j)).val = σ (e (b (orbitFirst j)).val)
      rw [← hComm, hτ, hp]
    have hdir : A.direction x = A.direction u := hchoices.elim
      (congrArg A.direction) (fun h => h ▸ (A.orbits u v).mpr (Or.inr hv) |>.symm)
    refine ⟨o, ⟨b (orbitFirst j), rfl⟩, ?_, ?_⟩
    · intro q hq
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
      exact ⟨b (orbitFirst k), rfl⟩
    · by_cases h : orbitFirst j = orbitSecond j
      · have hl : transportedLabels o = [u] := by
          change (orbit j).roots.map e = _
          rw [hroots, ite_eq_left h]
          rfl
        have hu : σ u = u := hv.symm.trans (congrArg (fun j : Fin 6 => e (b j).val) h.symm)
        rw [hl]
        refine ⟨List.nodup_singleton _, fun i => ?_⟩
        rw [List.mem_singleton, hdir, eq_comm (a := A.direction i), A.orbits, hu, or_self]
      · have hl : transportedLabels o = [u, v] := by
          change (orbit j).roots.map e = _
          rw [hroots, ite_eq_right h]
          rfl
        have huv : u ≠ v := fun e' => h (b.injective (Subtype.ext (e.injective e')))
        rw [hl]
        refine ⟨by simp [huv], fun i => ?_⟩
        rw [List.mem_cons, List.mem_singleton, hv, hdir, eq_comm (a := A.direction i), A.orbits]
  choose block h using hex
  exact ⟨block, fun a => (h a).1, fun a => (h a).2.1, fun a => (h a).2.2.1,
    fun a => (h a).2.2.2⟩

end TransportedFoldedRoots

section CoefficientActions

open CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra integralSpec IntegralPoints)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRing)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {D : BasedRootDatum.{u}} {M : Model D}

omit [Algebra F K] in
private theorem scalarPoints_comp (M : Model D) {L : Type u} [Field L]
    (f : F →+* K) (g : K →+* L) (x : FieldPoints M F) :
    scalarPoints M g (scalarPoints M f x) = scalarPoints M (g.comp f) x := by
  change changeRing (integralRingMap g) (changeRing (integralRingMap f) x) = _
  unfold changeRing
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

private theorem scalarPoints_id (M : Model D) (x : FieldPoints M K) :
    scalarPoints M (RingHom.id K) x = x := by
  change changeRing (integralRingMap (RingHom.id K)) x = x
  have h : integralRingMap (RingHom.id K) = 𝟙 _ := rfl
  rw [h]
  simp [changeRing]

/-- The coefficient field automorphisms act on the actual marked split
points via the integral point functor. -/
noncomputable def markedCoefficientAction (M : Model D) : Gal(K/F) →* MulAut (FieldPoints M K) where
  toFun σ :=
    { toFun := scalarPoints M σ.toRingHom
      invFun := scalarPoints M σ.symm.toRingHom
      left_inv := fun x => by
        have hi : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id K :=
          RingHom.ext σ.symm_apply_apply
        rw [scalarPoints_comp, hi]
        exact scalarPoints_id M x
      right_inv := fun x => by
        have hi : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id K :=
          RingHom.ext σ.apply_symm_apply
        rw [scalarPoints_comp, hi]
        exact scalarPoints_id M x
      map_mul' := fun x y => (scalarPoints M σ.toRingHom).map_mul x y }
  map_one' := by
    apply MulEquiv.ext
    intro x
    exact scalarPoints_id M x
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    exact (scalarPoints_comp M τ.toRingHom σ.toRingHom x).symm

variable [FiniteDimensional F K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]

/-- At an unramified level the coefficient action fixes the normalized value
of every element, including in positive residue characteristic. -/
theorem normalizedValuation_unramifiedAut (h : IsUnramifiedLocalExtension F K)
    (σ : Gal(K/F)) (x : K) : normalizedValuation K (σ x) = normalizedValuation K x := by
  obtain ⟨y, hy⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization F).1 (normalizedValuation K x)
  change normalizedValuation F y = _ at hy
  let z := algebraMap F K y
  have hz : normalizedValuation K z = normalizedValuation K x := (h y).trans hy
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hz' : valuation K z = valuation K x := i.injective hz
  have hσz : σ z = z := σ.commutes y
  have h₁ := (valuativeEmbedding σ.toAlgHom x z).mpr hz'.ge
  have h₂ := (valuativeEmbedding σ.toAlgHom z x).mpr hz'.le
  change valuation K (σ x) ≤ valuation K (σ z) at h₁
  change valuation K (σ z) ≤ valuation K (σ x) at h₂
  rw [hσz, hz'] at h₁ h₂
  exact congrArg i (le_antisymm h₁ h₂)

end CoefficientActions

section FoldedRootOrders

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineRootSystems (FoldedRootDirection e6Cartan e6Partner e6Diagram)
open Specs.ExceptionalMarkedRootDescent (SimpleRootOrbit TransportedOrbit transportedLabels)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation)
open Specs.OrderedRootProducts (Enumerates)
open private e6Diagram_apply e6Cartan_symmetric
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

universe u

set_option maxHeartbeats 600000 in
/-- The E₆ diagram acts by an actual root involution preserving positive
roots, and the Cartan pairing is symmetric on the whole root set. -/
theorem e6LocalRootSymmetries (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (τ : BasedIso D D) (numbering : ExceptionalNumbering D 6 b)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) :
    Function.Involutive τ.val.indexEquiv ∧
    (∀ i, D.base.IsPos (τ.val.indexEquiv i) ↔ D.base.IsPos i) ∧
    ∀ i j, D.datum.pairing i j = D.datum.pairing j i := by
  classical
  let _ := D.finiteRoots
  let _ := D.reduced
  have hCt (i j : Fin 6) : e6Cartan i j = D.datum.pairing (b i) (b j) :=
    (congrFun (congrFun e6_standardCartan.symm i) j).trans (numbering.2 i j).symm
  obtain ⟨_, ρ, hρ, _⟩ := ExceptionalAffineRootSystems.e6DiagramCoordinates (K := ℚ)
    D.datum D.base b τ.val hτ hCt
  let a := τ.val.indexEquiv
  have hi : Function.Involutive e6Partner := by intro i; fin_cases i <;> decide
  have hInv : Function.Involutive a := by
    intro i
    apply ρ.injective
    apply Subtype.ext
    change (ρ (a (a i))).val = (ρ i).val
    rw [(hρ (a i)).2.2, (hρ i).2.2]
    funext j
    rw [e6Diagram_apply, e6Diagram_apply, hi j]
  have hs (i : D.I) (hi : i ∈ D.base.support) : a i ∈ D.base.support := by
    change a i ∈ (↑D.base.support : Set D.I)
    rw [← τ.property]
    exact Set.mem_image_of_mem a hi
  have hroot (i : D.I) : τ.val.weightEquiv (D.datum.root i) = D.datum.root (a i) :=
    congrFun τ.val.toHom.root_weightMap i
  have hpos (i : D.I) (hi : D.base.IsPos i) : D.base.IsPos (a i) := by
    refine hi.induction_on_add (p := fun j => D.base.IsPos (a j))
      (fun j hj => D.base.isPos_of_mem_support (hs j hj)) ?_
    intro i j k hk hi hj
    apply hi.add (D.base.isPos_of_mem_support (hs j hj))
    rw [← hroot, hk, map_add, hroot, hroot]
  refine ⟨hInv, fun i => ⟨fun h => hInv i ▸ hpos (a i) h, hpos i⟩, ?_⟩
  let r (i : D.I) := (ρ i).val
  have hp (i j : D.I) : D.datum.pairing i j =
      ∑ l : Fin 6, ∑ m : Fin 6, r i l * (r j m * e6Cartan l m) := by
    change D.datum.toLinearMap (D.datum.root i) (D.datum.coroot j) = _
    rw [(hρ i).1, (hρ j).2.1]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    rw [hCt]
    change r j m * (r i l * D.datum.pairing (b l) (b m)) =
      r i l * (r j m * D.datum.pairing (b l) (b m))
    ring
  intro i j
  rw [hp, hp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [e6Cartan_symmetric.apply l m]
  ring

/-- Order the folded root blocks so that their absolute labels enumerate
the marked negative and positive roots. Each block is confined to one
relative direction. -/
theorem foldedRootOrders
    {D : BasedRootDatum.{u}} {τ : BasedIso D D} (A : FoldedApartment τ)
    (block : FoldedRootDirection → TransportedOrbit D)
    (hn : ∀ a, (transportedLabels (block a)).Nodup)
    (hlabel : ∀ a i, i ∈ transportedLabels (block a) ↔ A.direction i = a)
    (hpos : ∀ i, D.base.IsPos (τ.val.indexEquiv i) ↔ D.base.IsPos i) :
    ∃ (negative positive : List (TransportedOrbit D)),
      (∀ o ∈ negative ++ positive, ∃ a, block a = o) ∧
      Enumerates (negative.flatMap transportedLabels) {i | ¬ D.base.IsPos i} ∧
      Enumerates (positive.flatMap transportedLabels) {i | D.base.IsPos i} := by
  classical
  let _ := D.finiteRoots
  let _ : Finite FoldedRootDirection := Finite.of_surjective A.direction A.surjective
  let _ : Fintype FoldedRootDirection := Fintype.ofFinite _
  let P (a : FoldedRootDirection) := ∃ i, A.direction i = a ∧ D.base.IsPos i
  have hP (i : D.I) : P (A.direction i) ↔ D.base.IsPos i := by
    refine ⟨fun ⟨j, hji, hj⟩ => ?_, fun h => ⟨i, rfl, h⟩⟩
    obtain h | h := (A.orbits i j).mp hji.symm
    · exact h ▸ hj
    · exact (hpos i).mp (h ▸ hj)
  have order (T : FoldedRootDirection → Prop) :
      ∃ O : List (TransportedOrbit D), (∀ o ∈ O, ∃ a, block a = o) ∧
        Enumerates (O.flatMap transportedLabels) {i | T (A.direction i)} := by
    let L := (Finset.univ.filter T).toList
    let O := L.map block
    have hmem (a : FoldedRootDirection) : a ∈ L ↔ T a := by simp [L]
    have hnd : L.Nodup := Finset.nodup_toList _
    refine ⟨O, fun _ ho => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ho
      exact ⟨a, rfl⟩, ?_, ?_⟩
    · rw [show O.flatMap transportedLabels = L.flatMap (transportedLabels ∘ block) from by simp [O, List.flatMap_map, Function.comp_def]]
      refine List.nodup_flatMap.mpr ⟨fun a _ => hn a, hnd.imp ?_⟩
      intro a b h
      apply List.disjoint_left.mpr
      intro i hi hj
      exact h (((hlabel a i).mp hi).symm.trans ((hlabel b i).mp hj))
    · intro i
      change i ∈ O.flatMap transportedLabels ↔ T (A.direction i)
      simp only [O, List.flatMap_map, List.mem_flatMap, hmem, hlabel]
      exact ⟨fun ⟨a, hT, he⟩ => he.symm ▸ hT, fun h => ⟨_, h, rfl⟩⟩
  obtain ⟨negative, hnegative, hN⟩ := order fun a => ¬P a
  obtain ⟨positive, hpositive, hQ⟩ := order P
  exact ⟨negative, positive, fun o h => (List.mem_append.mp h).elim (hnegative o) (hpositive o),
    ⟨hN.1, fun i => (hN.2 i).trans (not_congr (hP i))⟩,
    ⟨hQ.1, fun i => (hQ.2 i).trans (hP i)⟩⟩

end FoldedRootOrders
section FoldedAffineRange

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer)
open Specs.ExceptionalValuedTorusNormalizer (fixedWeylGroup invariantApartment simplePermutation
  orbitWeylReflection orbitProjection simpleCorootBasis fundamentalCoweightBasis)
open scoped TensorProduct CategoryTheory.MonObj

open private reflection_natural rationalCocharacterAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private folded_reflection_action
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

attribute [local instance] integerAlgebra

universe u

variable {D : BasedRootDatum.{u}} {τ : BasedIso D D}

/-- The translation image computed in the permuted integral basis is the
coroot lattice of the normalized folded arrangement in the fixed apartment. -/
theorem foldedNormalizerTranslations
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {M : Model D} {G W : Type u} [Group G] [Group W] {j : G →* FieldPoints M K}
    (N : MarkedLocalNormalizer K j W) (A : FoldedApartment τ)
    [Fintype D.base.support] (b : Module.Basis D.base.support ℤ D.Y)
    (hb : (∃ h, b = simpleCorootBasis D h) ∨ (∃ h, b = fundamentalCoweightBasis D h))
    (hinv : Function.Involutive τ.val.indexEquiv)
    (hproj : Set.range (fun t : N.torus => fun i : D.base.support =>
      ((b.repr (N.translation t).toAdd i : ℤ) : ℚ) / 2) =
      Set.range (orbitProjection (simplePermutation D τ))) :
    Set.range (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      (invariantApartment D τ).subtype '' (A.roots.corootLattice : Set _) := by
  classical
  let _ := D.finiteRoots
  let _ := D.reduced
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let V := ℚ ⊗[ℤ] D.Y
  let d : V ≃ₗ[ℚ] V := diagramCocharacters τ.val
  let lift (y : D.Y) := (1 : ℚ) ⊗ₜ[ℤ] y
  let p := simplePermutation D τ
  let q := (b.baseChange ℚ).equivFun
  have hp (i : D.base.support) : p (p i) = i := Subtype.ext (hinv i.val)
  have hB (i : D.base.support) : τ.val.coweightEquiv.symm (b i) = b (p i) :=
    ((ExceptionalValuedTorusNormalizer.basedPermutation D τ b hb) i).1
  have hrepr (y : D.Y) (i : D.base.support) :
      b.repr (τ.val.coweightEquiv.symm y) i = b.repr y (p i) := by
    have h : (b.coord i).comp τ.val.coweightEquiv.symm.toLinearMap = b.coord (p i) := by
      apply b.ext
      intro k
      rw [LinearMap.comp_apply]
      change b.coord i (τ.val.coweightEquiv.symm (b k)) = _
      rw [hB]
      by_cases hki : k = p i
      · subst k
        simp [hp]
      · have hik : p k ≠ i := fun he => hki (p.injective (he.trans (hp i).symm))
        simp [Module.Basis.coord_apply, Ne.symm hik, Ne.symm hki]
    exact LinearMap.congr_fun h y
  have hq (c : ℚ) (y : D.Y) (i : D.base.support) :
      q (c ⊗ₜ[ℤ] y) i = c * (b.repr y i : ℚ) := by
    change (b.baseChange ℚ).repr (c ⊗ₜ[ℤ] y) i = _
    rw [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_comm]
  have havg (y : D.Y) :
      q (diagramAverage d (lift y)) = orbitProjection p (b.equivFun y) := by
    funext i
    change q ((2 : ℚ)⁻¹ • (lift y + d (lift y))) i = _
    have hdy : d (lift y) = lift (τ.val.coweightEquiv.symm y) := by
      change τ.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y ((1 : ℚ) ⊗ₜ[ℤ] y) =
        (1 : ℚ) ⊗ₜ[ℤ] τ.val.coweightEquiv.symm y
      rw [LinearEquiv.baseChange_tmul]
    rw [hdy, map_smul, map_add, Pi.smul_apply, Pi.add_apply, hq, hq, one_mul, one_mul, hrepr]
    change (2 : ℚ)⁻¹ * ((b.repr y i : ℚ) + (b.repr y (p i) : ℚ)) = _
    simp [orbitProjection, div_eq_mul_inv, mul_comm]
  have hL : (invariantApartment D τ).subtype '' (A.roots.corootLattice : Set _) =
      diagramAverage d '' Set.range lift := by
    obtain ⟨hcor, hcow⟩ := ExceptionalAffineRootSystems.splitIntegralCocharacterImages
      (K := ℚ) D.datum D.base
    rcases hb with ⟨h, _⟩ | ⟨h, _⟩
    · rw [A.coroot_projection, hcor, show Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ from h,
        Submodule.top_coe, Set.image_univ]
    · rw [A.coweight_projection, hcow h]
  apply (Set.image_injective.mpr q.injective)
  rw [hL, Set.image_image, ← Set.range_comp, ← Set.range_comp]
  have h₁ : Set.range (q ∘ (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd)) =
      Set.range (orbitProjection p) := by
    have he : q ∘ (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
        (fun t : N.torus => fun i : D.base.support => ((b.repr (N.translation t).toAdd i : ℤ) : ℚ) / 2) := by
      funext t i
      rw [Function.comp_apply, hq]
      ring
    exact (congrArg Set.range he).trans hproj
  rw [h₁]
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := b.equivFun.surjective x
    exact ⟨y, (havg y).trans (congrArg (orbitProjection p) hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨b.equivFun y, (havg y).symm⟩

/-- The linear part of the relative affine action has exactly the Weyl
group generated by the normalized folded root reflections. -/
theorem foldedWeylLinearRange (A : FoldedApartment τ) (hi : Function.Involutive τ.val.indexEquiv)
    (w : fixedWeylGroup D τ →* ((invariantApartment D τ) ≃ₗ[ℚ] (invariantApartment D τ)))
    (hw : ∀ a (x : invariantApartment D τ), (w a x).val =
      a.val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val) :
    w.range = A.roots.linearWeylGroup := by
  classical
  let W := fixedWeylGroup D τ
  let s := RootPairing.weylGroup.ofIdx D.datum
  let r (i : D.I) := if τ.val.indexEquiv i = i then s i else s i * s (τ.val.indexEquiv i)
  let L := rationalCocharacterAction D
  let B := A.roots.linearWeylGroup
  have hs (i : D.I) :
      τ.val * (s i).val = (s (τ.val.indexEquiv i)).val * τ.val := reflection_natural D τ.val i
  have hcom (i : D.I) (h : τ.val.indexEquiv i ≠ i) : Commute (s i) (s (τ.val.indexEquiv i)) := by
    have hz := A.orthogonal i h
    have hfix : D.datum.reflectionPerm (τ.val.indexEquiv i) i = i := by
      apply D.datum.root.injective
      rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_root, hz, zero_smul, sub_zero]
    apply Commute.symm
    apply Subtype.ext
    have he := reflection_natural D (s (τ.val.indexEquiv i)).val i
    change (s (τ.val.indexEquiv i)).val * (s i).val =
      (s (D.datum.reflectionPerm (τ.val.indexEquiv i) i)).val * (s (τ.val.indexEquiv i)).val at he
    rwa [hfix] at he
  have hrs (i : D.I) : r i ∈ W := by
    change (r i).val ∈ Subgroup.centralizer {τ.val}
    apply (Subgroup.mem_centralizer_singleton_iff).mpr
    apply Commute.symm
    change τ.val * (r i).val = (r i).val * τ.val
    by_cases h : τ.val.indexEquiv i = i
    · simpa only [r, ite_eq_left h, h] using hs i
    · simp only [r, ite_eq_right h, Subgroup.coe_mul]
      rw [← mul_assoc, hs i, mul_assoc, hs (τ.val.indexEquiv i), hi, ← mul_assoc]
      rw [show (s (τ.val.indexEquiv i)).val * (s i).val =
        (s i).val * (s (τ.val.indexEquiv i)).val from congrArg Subtype.val (hcom i h).eq.symm]
  let label (i : D.I) : W := ⟨r i, hrs i⟩
  have hpartner (i : D.I) : A.direction (τ.val.indexEquiv i) = A.direction i :=
    ((A.orbits i _).2 (Or.inr rfl)).symm
  have hR := folded_reflection_action D.datum τ.val A.direction A.roots hpartner A.long A.orthogonal
    A.root_value A.coroot_value
  have hLabel (i : D.I) : w (label i) = A.roots.linearReflection (A.direction i) := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [hw]
    change L (r i).val x.val = _
    by_cases h : τ.val.indexEquiv i = i
    · rw [show r i = s i from ite_eq_left h, show L (s i).val =
        (ApartmentRoots.split D.datum ℚ).linearReflection i from splitWeylReflection D i]
      exact ((hR i x).1 h).symm
    · rw [show r i = s i * s (τ.val.indexEquiv i) from ite_eq_right h,
        Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply,
        show L (s i).val = (ApartmentRoots.split D.datum ℚ).linearReflection i from splitWeylReflection D i,
        show L (s (τ.val.indexEquiv i)).val = (ApartmentRoots.split D.datum ℚ).linearReflection
          (τ.val.indexEquiv i) from splitWeylReflection D _]
      exact ((hR i x).2 h).symm
  have hord (i : D.base.support) (h : simplePermutation D τ i ≠ i) :
      D.datum.pairing (simplePermutation D τ i).val i.val = 0 := by
    change D.datum.pairing (τ.val.indexEquiv i.val) i.val = 0
    have he : τ.val.indexEquiv i.val ≠ i.val := fun h' => h (Subtype.ext h')
    have hp := A.orthogonal (τ.val.indexEquiv i.val) (fun h' => he (h'.symm.trans (hi i.val)))
    rwa [hi] at hp
  have he (i : D.base.support) : r i.val = orbitWeylReflection D τ i := by
    have h : τ.val.indexEquiv i.val = i.val ↔ simplePermutation D τ i = i :=
      ⟨fun h => Subtype.ext h, congrArg (fun j : D.base.support => j.val)⟩
    simp only [r, orbitWeylReflection, h]
    rfl
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let C := (B.comap w).map W.subtype
    have hle : Subgroup.closure (Set.range (orbitWeylReflection D τ)) ≤ C := by
      apply (Subgroup.closure_le C).mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨label i.val, ?_, he i⟩
      change w (label i.val) ∈ B
      rw [hLabel]
      exact Subgroup.subset_closure (Set.mem_range_self _)
    have hGen := (ExceptionalValuedTorusNormalizer.fixedWeylGeneration D τ hi hord).1 v.val
    have hv' : Commute τ.val v.val.val :=
      ((Subgroup.mem_centralizer_singleton_iff).mp v.property).symm
    obtain ⟨z, hz, heq⟩ := hle (hGen.mpr hv')
    have hh : z = v := Subtype.ext heq
    exact hh ▸ hz
  · apply (Subgroup.closure_le w.range).mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨i, rfl⟩ := A.surjective a
    exact ⟨label i, hLabel i⟩

/-- The actual folded affine image is ordinary in both lattice forms. -/
theorem foldedNormalizerActionRange
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {M : Model D} {G : Type u} [Group G] {j : G →* FieldPoints M K}
    (A : FoldedApartment τ) (hi : Function.Involutive τ.val.indexEquiv)
    (N : MarkedLocalNormalizer K j (fixedWeylGroup D τ))
    (a : N.normalizer →* ((invariantApartment D τ) ≃ᵃ[ℚ] (invariantApartment D τ)))
    (ha : ∀ (n : N.normalizer) (x : invariantApartment D τ),
      (a n x).val = (N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
        ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd))
    (ht : Set.range (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      (invariantApartment D τ).subtype '' (A.roots.corootLattice : Set _)) :
    a.range = A.roots.affineWeylGroup := by
  classical
  let V := invariantApartment D τ
  let v (t : N.torus) := (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd
  have hv (t : N.torus) : v t ∈ V := by
    have h : v t ∈ V.subtype '' (A.roots.corootLattice : Set V) := ht ▸ Set.mem_range_self t
    obtain ⟨x, _, hx⟩ := h
    exact hx ▸ x.property
  let z (t : N.torus) : V := ⟨v t, hv t⟩
  have hz : Set.range z = (A.roots.corootLattice : Set V) := by
    apply (Set.image_injective.mpr V.subtype_injective)
    rw [← Set.range_comp]
    exact ht
  let _ := D.freeY
  let _ := D.finiteY
  let b := Module.Free.chooseBasis ℤ D.Y
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
  have ho (i : D.base.support) (h : simplePermutation D τ i ≠ i) :
      D.datum.pairing (simplePermutation D τ i).val i.val = 0 := by
    change D.datum.pairing (τ.val.indexEquiv i.val) i.val = 0
    have he : τ.val.indexEquiv i.val ≠ i.val := fun h' => h (Subtype.ext h')
    have hp := A.orthogonal (τ.val.indexEquiv i.val) (fun h' => he (h'.symm.trans (hi i.val)))
    rwa [hi] at hp
  obtain ⟨w, _, hw⟩ := ExceptionalValuedTorusNormalizer.foldedWeylLinearAction D τ b hi ho
  have he (n : N.normalizer) (x : V) : a n x = w (N.label n) x + z (N.torusPart n) :=
    Subtype.ext ((ha n x).trans (congrArg (· + v (N.torusPart n)) (hw (N.label n) x).symm))
  ext g
  rw [normalizerAction_range N w z a he, hz, foldedWeylLinearRange A hi w hw]
  exact ((ExceptionalAffineRootSystems.affineGroupNormalForms A.roots).2.1 g).symm

end FoldedAffineRange

section FoldedBaseField

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra Integers IntegralPoints)
open Specs.ExceptionalAffineRootSystems (PinnedWallSigns AlcoveGeometry e6Partner)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori ramificationIndex)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalIwahoriImageComparison (pinnedGroundPoint integralUnitTorus)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit TransportedOrbit transportedLabels pinnedDiagram)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv fixedWeylGroup invariantApartment
  simplePermutation simpleCorootBasis fundamentalCoweightBasis FibreNormalizer)
open Specs.OrderedRootProducts (Enumerates)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.PinnedPairDescent (DescendedPair)
open Specs.SchemeDerivedGroup (FactorsThrough)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open scoped TensorProduct
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension k K]
  {D : BasedRootDatum.{u}} {M : Model D}

open Specs.ExceptionalFoldedRootChart (OrbitOrdering)
open Specs.ExceptionalAffineRootSystems (FoldedRootDirection)
open Specs.Pinning (BasedIso)

/-- The simple-orbit words and the ordered blocks are integral choices
that can be used at every coefficient level of the pinned reference. -/
private structure FoldedOrdering {τ : BasedIso D D} (A : FoldedApartment τ) where
  order : OrbitOrdering A.direction
  nodup (a : FoldedRootDirection) : (transportedLabels (order.block a)).Nodup
  simple (a : FoldedRootDirection) : ∃ i, (order.block a).1 = simpleOrbitBlock D τ i
  word (a : FoldedRootDirection) (v : SimpleRootOrbit D) (hv : v ∈ (order.block a).2) :
    ∃ i, v = simpleOrbitBlock D τ i

private theorem foldedOrdering (b : Fin 6 ≃ D.base.support)
    {τ : BasedIso D D} (A : FoldedApartment τ) (hNum : ExceptionalNumbering D 6 b)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) :
    Nonempty (FoldedOrdering A) := by
  obtain ⟨hi, hp, _⟩ := e6LocalRootSymmetries D b τ hNum hτ
  obtain ⟨block, hs, hw, hn, hf⟩ := e6TransportedRootBlocks D b τ A hNum hτ hi
  obtain ⟨negative, positive, ho, hnegative, hpositive⟩ := foldedRootOrders A block hn hf hp
  exact ⟨⟨⟨block, negative, positive, hf, ho, hnegative, hpositive⟩, hn, hs, hw⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem foldedSimpleOrbitMatches (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    (hQ : SplitSequence C.realization.pinned C.realization.attached l Q)
    {ω : Gal(K/k) →* Aut C.realization.attached.toBased} (d : DescendedPair (l := l) K ω)
    (σ : Gal(K/k)) :
    let τ := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
    ∀ (A : FoldedApartment τ), Function.Involutive τ.val.indexEquiv →
    (∀ i j, D.datum.pairing i j = D.datum.pairing j i) →
    ∀ (i : D.base.support), (simpleOrbitBlock D τ i).Matches C (pinnedDiagram d.data σ) := by
  classical
  intro τ A hInv hSym
  let p := simplePermutation D τ
  have hOrth (i : D.base.support) (hi : p i ≠ i) : D.datum.pairing (p i).val i.val = 0 := by
    rw [hSym]
    exact A.orthogonal i.val (fun h => hi (Subtype.ext h))
  have hMatch (i : D.base.support) : (simpleOrbitBlock D τ i).Matches C (pinnedDiagram d.data σ) := by
    apply (ExceptionalLocalRootCoordinates.pinnedSimpleOrbitCriterion C hQ d.data σ
      (simpleOrbitBlock D τ i)).mpr
    change (match (if p i = i then none else some (p i)) with
      | none => p i = i
      | some q => D.datum.pairing i q = 0 ∧ p i = q ∧ p q = i)
    by_cases has : p i = i
    · rw [ite_eq_left has]
      exact has
    · rw [ite_eq_right has]
      exact ⟨(hSym _ _).trans (hOrth i has), rfl, Subtype.ext (hInv (i : D.I))⟩
  exact hMatch

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
/-- The rational normalizer, in the positive Borel reduction of the
given pinned pair and with the preselected integral root ordering. -/
private theorem foldedIwahoriOfE6Pinning (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    (hQ : SplitSequence C.realization.pinned C.realization.attached l Q)
    {ω : Gal(K/k) →* Aut C.realization.attached.toBased} (d : DescendedPair (l := l) K ω)
    (σ : Gal(K/k)) (deg : Module.finrank k K = 2) (hne : σ ≠ 1)
    (hram : 1 < ramificationIndex k K)
    (b : Fin 6 ≃ D.base.support) (hNum : ExceptionalNumbering D 6 b)
    (hIsogeny : D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤) :
    let τ := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
    let W := fixedWeylGroup D τ
    let G := (𝟙_ (SchemeOver k) ⟶ d.group.val.X)
    let R := integralRing K
    (∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) →
    ∀ (A : FoldedApartment τ) (o : FoldedOrdering A),
    (∀ r, (o.order.block r).1.Matches C (pinnedDiagram d.data σ) ∧
        ∀ q ∈ (o.order.block r).2, q.Matches C (pinnedDiagram d.data σ)) →
    ∃ (bb : Module.Basis D.base.support ℤ D.Y)
      (j : G →* IntegralPoints M.group R) (P : LocalIwahori j W)
      (B : FibreNormalizer M K)
      (a : P.normalizer.normalizer →* ((invariantApartment D τ) ≃ᵃ[ℚ] (invariantApartment D τ))),
      Function.Injective j ∧ (∀ g, j g = pinnedGroundPoint C d.data g) ∧
      (∀ g, g ∈ P.normalizer.normalizer ↔ Normalizes d.torus.inclusion g) ∧
      (∀ g, g ∈ P.normalizer.torus ↔ FactorsThrough d.torus g) ∧
      (∀ n : P.normalizer.normalizer, ∃ m, B.point m = j n ∧ B.label m = (P.normalizer.label n).val) ∧
      (∀ w, ∀ i ∈ P.normalizer.word w, i ∈ D.base.support) ∧
      (∀ w, ((P.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val) ∧
      a.ker.map P.normalizer.normalizer.subtype = (integralUnitTorus (K := K) M).comap j ∧
      (∀ n x, (a n x).val =
        (P.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
          ((1 / 2 : ℚ) ⊗ₜ[ℤ] (P.normalizer.translation (P.normalizer.torusPart n)).toAdd)) ∧
      Set.range (fun t : P.normalizer.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (P.normalizer.translation t).toAdd) =
        (invariantApartment D τ).subtype '' (A.roots.corootLattice : Set _) ∧
      a.range = A.roots.affineWeylGroup := by
  classical
  intro τ W G R hτ A o hBlockMatch
  let _ := D.finiteRoots
  let _ : Fintype D.base.support := Fintype.ofFinite _
  obtain ⟨hInv, _, hSym⟩ := e6LocalRootSymmetries D b τ hNum hτ
  let p := simplePermutation D τ
  have hOrth (i : D.base.support) (hi : p i ≠ i) : D.datum.pairing (p i).val i.val = 0 := by
    rw [hSym]
    exact A.orthogonal i.val (fun h => hi (Subtype.ext h))
  have hMatch := foldedSimpleOrbitMatches C hQ d σ A hInv hSym
  have hmatches (v : TransportedOrbit D) (hv : v ∈ o.order.negative ++ o.order.positive) :
      v.1.Matches C (pinnedDiagram d.data σ) ∧
        ∀ q ∈ v.2, q.Matches C (pinnedDiagram d.data σ) := by
    obtain ⟨r, rfl⟩ := o.order.ordered v hv
    exact hBlockMatch r
  obtain ⟨word, hword, hprod⟩ := foldedFixedWeylWords D τ hInv hOrth
  have hwordMatch (w : W) (o : SimpleRootOrbit D) (ho : o ∈ word w) :
      o.Matches C (pinnedDiagram d.data σ) := by
    obtain ⟨i, rfl⟩ := hword w o ho
    exact hMatch i
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis D.base.support ℤ D.Y,
      (∃ h, bb = simpleCorootBasis D h) ∨ (∃ h, bb = fundamentalCoweightBasis D h) :=
    hIsogeny.elim (fun h => ⟨simpleCorootBasis D h, Or.inl ⟨h, rfl⟩⟩)
      (fun h => ⟨fundamentalCoweightBasis D h, Or.inr ⟨h, rfl⟩⟩)
  obtain ⟨j, P, B, S, hj, hJ, hS, hN, hN', hT, hF, hW, _, hProj⟩ :=
    ExceptionalLocalRootCoordinates.foldedLocalIwahori C hQ d σ deg hne hram hSym hOrth
      bb hbb o.order.negative o.order.positive hmatches o.order.negative_enumerates
      o.order.positive_enumerates word hwordMatch hprod
  obtain ⟨a, hKer, hAct⟩ :=
    ExceptionalLocalRootCoordinates.foldedNormalizerApartment B τ bb hbb hInv hOrth j P.normalizer hF hProj
  have hTranslation := foldedNormalizerTranslations P.normalizer A bb hbb hInv hProj
  have hRange := foldedNormalizerActionRange A hInv P.normalizer a hAct hTranslation
  refine ⟨bb, j, P, B, a, hj, hJ, hN', hT, hF, ?_, ?_, hKer, hAct, hTranslation, hRange⟩
  · intro w i hi
    rw [hW w] at hi
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp hi
    change i ∈ o.1.val :: o.2.toList.map Subtype.val at ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact o.1.property
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ho
      exact q.property
  · intro w
    rw [hW w]
    exact hprod w

end FoldedBaseField

section SplitTransport

open CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.OrderedRootProducts (Enumerates)
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open scoped TensorProduct
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {p : ℚ ⊗[ℤ] D.Y} {B : MarkedFibre M F} {B' : MarkedFibre M K} {ad : Bool}
  (C : LocalComparison (j := identityPoints M F) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p)
  (C' : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p)

set_option backward.isDefEq.respectTransparency false in
/-- The marked split subgroup and lift comparisons on valued scalar extension. -/
theorem splitSubgroupsScalar
    (hC : SplitPointComparison B ad C) (hC' : SplitPointComparison B' ad C')
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ C'.localIwahori.normalizer.word w, a ∈ D.base.support)
    (br : C.Bruhat (Nat.card (residue F))) (br' : C'.Bruhat (Nat.card (residue K)))
    (normal : C.G₀.Normal) (f : F →+* K)
    (hv : ∀ x, normalizedValuation K (f x) = normalizedValuation F x) :
    let s := scalarPoints M f
    C'.I.comap s = C.I ∧ C'.N.comap s = C.N ∧ C'.T₀.comap s = C.T₀ ∧ C'.G₀.comap s = C.G₀ ∧
    C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus ∧
    C.affine.range = C'.affine.range ∧
    (∀ (n : C.N) (n' : C'.N), (n' : FieldPoints M K) = s n →
      C'.affine n' = C.affine n ∧
      C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n) ∧
    (∀ w, s (C.lift w) * (C'.lift w : FieldPoints M K)⁻¹ ∈ C'.T₀) := by
  intro s
  let _ := D.finiteRoots
  let _ := D.freeY
  let _ := D.finiteY
  let b := Module.Free.chooseBasis ℤ D.Y
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
  obtain ⟨negative, positive, hn, hp⟩ := rootOrderings_exist D
  have hI := splitIwahoriScalar C.localIwahori C'.localIwahori f hv negative positive hn hp
  obtain ⟨hT, hN⟩ := splitTorusNormalizerScalar C C' hC hC' hword hword' f
  have hT₀ : C'.T₀.comap s = C.T₀ := by
    have he : C.I ⊓ C.N = C.T₀ := C.localIwahori.intersection
    have he' : C'.I ⊓ C'.N = C'.T₀ := C'.localIwahori.intersection
    rw [← he', Subgroup.comap_inf, hI, hN, he]
  have hAff := splitNormalizerLabelsScalar C C' hC hC' hword b f hv
  have hG := ordinarySubgroup_pullback C C' s (le_of_eq hI.symm) (le_of_eq hN.symm)
    (fun n n' he => (hAff n n' he).1) normal br.ordinary_normalizer br'.ordinary_normalizer
  refine ⟨hI, hN, hT₀, hG, hT, ?_, hAff, ?_⟩
  · exact hC.2.2.2.2.2.2.2.2.trans hC'.2.2.2.2.2.2.2.2.symm
  · intro w
    let n := C.lift w
    let n' : C'.N := ⟨s n, (SetLike.ext_iff.mp hN _).mpr n.property⟩
    exact sameLabel_div_mem_unitTorus C' (n := n') (m := C'.lift w)
      ((hAff n n' rfl).1.trans ((C.lift_label w).trans (C'.lift_label w).symm))

end SplitTransport
section SplitCoefficientComparison

open CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open ValuativeRel
open scoped TensorProduct
attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

private theorem map_eq_of_comap_eq {G : Type*} [Group G] (a : MulAut G) (H : Subgroup G)
    (h : H.comap a.toMonoidHom = H) : H.map a.toMonoidHom = H := by
  nth_rw 1 [← h]
  exact Subgroup.map_comap_eq_self_of_surjective a.surjective H

/-- Coefficient automorphisms of a finite unramified level preserve the
marked local data and act trivially on the affine labels. -/
theorem splitCoefficientComparison
    {p : ℚ ⊗[ℤ] D.Y} {B : MarkedFibre M K} {ad : Bool}
    (C : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (hC : SplitPointComparison B ad C)
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (br : C.Bruhat (Nat.card (residue K))) (normal : C.G₀.Normal)
    (h : IsUnramifiedLocalExtension F K) (σ : Gal(K/F)) :
    let a := markedCoefficientAction M σ
    AutomorphismComparison C a 1 ∧ C.G₀.comap a.toMonoidHom = C.G₀ := by
  intro a
  let A := ApartmentRoots.split D.datum ℚ
  have he : a.toMonoidHom = scalarPoints M σ.toRingHom := MonoidHom.ext fun _ => rfl
  obtain ⟨hI, hN, hT₀, hG₀, hT, _, hlabel, hlift⟩ := splitSubgroupsScalar C C hC hC hword hword br br normal
    σ.toRingHom (normalizedValuation_unramifiedAut h σ)
  refine ⟨⟨map_eq_of_comap_eq a C.I (he.symm ▸ hI), map_eq_of_comap_eq a C.N (he.symm ▸ hN),
    map_eq_of_comap_eq a C.T₀ (he.symm ▸ hT₀), map_eq_of_comap_eq a C.G₀ (he.symm ▸ hG₀),
    map_eq_of_comap_eq a C.localIwahori.normalizer.torus (he.symm ▸ hT), by simp, ?_, ?_⟩, he.symm ▸ hG₀⟩
  · intro n n' hn'
    simpa only [one_mul, inv_one, mul_one] using (hlabel n n' hn').1
  · intro w
    exact ⟨w, by simp, hlift w⟩

/-- The pure coefficient actions of a finite unramified extension
intertwine the marked split comparisons and their type quotients. -/
theorem splitLevelCoefficientActions
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)} (X : SplitLevel K c p p' e)
    (hword : ∀ w, ∀ a ∈ X.sc.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ X.ad.localIwahori.normalizer.word w, a ∈ E.base.support)
    (h : IsUnramifiedLocalExtension F K) :
    X.Coefficients (F := F) := by
  have hOrd : X.sc.affine.range = (ApartmentRoots.split D.datum ℚ).affineWeylGroup :=
    X.sc_points.2.2.2.2.2.2.2.2
  have hnormal : X.sc.G₀.Normal := by
    rw [ordinaryRange_generates X.sc hOrd]
    infer_instance
  refine ⟨markedCoefficientAction M, markedCoefficientAction M', fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro σ
  obtain ⟨hsc, _⟩ := splitCoefficientComparison X.sc X.sc_points hword X.sc_bruhat hnormal h σ
  obtain ⟨had, hG₀⟩ := splitCoefficientComparison X.ad X.ad_points hword' X.ad_bruhat
    X.typeQuotient.normal h σ
  refine ⟨hsc, had, typeQuotientTransport_of_lifts X.ad X.ad X.typeQuotient X.typeQuotient _
    (le_of_eq hG₀.symm) (MonoidHom.id _) ?_⟩
  intro ω
  let a := markedCoefficientAction M' σ
  let n := X.typeQuotient.lift ω
  have hmem : a n ∈ X.ad.N.map a.toMonoidHom := ⟨n, n.property, rfl⟩
  have hmem' : a n ∈ X.ad.N := by
    exact (SetLike.ext_iff.mp had.2.1 (a n)).mp hmem
  let n' : X.ad.N := ⟨a n, hmem'⟩
  have he := (had.2.2.2.2.2.2.1 n n' rfl)
  have he' : X.ad.affine n' = X.ad.affine n := by simpa using he
  exact sameLabel_div_mem_unitTorus X.ad (n := n') (m := n) he'

end SplitCoefficientComparison
section SplitScalarCharts

open CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model IntegralAlgebra Integers TorusValues integerAlgebra)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap cellValue CellValues mapCellValues)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open private changeRing_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open ValuativeRel
open scoped TensorProduct
attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K] [ValuativeRel F] [ValuativeRel K]
  [TopologicalSpace F] [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}

private theorem cellValues_eq_of_cast {R : IntegralAlgebra.{u}} {l l' r r' : List D.I}
    (hl : l = l') (hr : r = r') (z : CellValues D R l r) (z' : CellValues D R l' r')
    (hn : ∀ i : Fin l.length, z.1 i = z'.1 (Fin.cast (congrArg List.length hl) i))
    (ht : z.2.1 = z'.2.1)
    (hp : ∀ i : Fin r.length, z.2.2 i = z'.2.2 (Fin.cast (congrArg List.length hr) i)) :
    z = (hl.symm ▸ hr.symm ▸ z') := by
  subst l' r'
  exact Prod.ext (funext hn) (Prod.ext ht (funext hp))

private theorem getElem_of_equal_rootLists (l l' : List D.I) (h : l = l') (i : Fin l.length) :
    l'[Fin.cast (congrArg List.length h) i] = l[i] := by
  subst l'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- The split scalar comparison includes the ordered marked chart when
the two fields use the same root orders. -/
theorem splitScalarComparison
    {p : ℚ ⊗[ℤ] D.Y} {B : MarkedFibre M F} {B' : MarkedFibre M K} {ad : Bool}
    (C : LocalComparison (j := identityPoints M F) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (C' : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
      (ApartmentRoots.split D.datum ℚ) p)
    (hC : SplitPointComparison B ad C) (hC' : SplitPointComparison B' ad C')
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ C'.localIwahori.normalizer.word w, a ∈ D.base.support)
    (br : C.Bruhat (Nat.card (residue F))) (br' : C'.Bruhat (Nat.card (residue K)))
    (normal : C.G₀.Normal) (f : F →+* K)
    (hv : ∀ x, normalizedValuation K (f x) = normalizedValuation F x)
    (hn : C.chart.negative = C'.chart.negative) (hp : C.chart.positive = C'.chart.positive) :
    ScalarComparison f (scalarPoints M f) C C' := by
  classical
  obtain ⟨hI, hN, hT₀, hG₀, hT, hr, ha, hLift⟩ :=
    splitSubgroupsScalar C C' hC hC' hword hword' br br' normal f hv
  refine ⟨changeRing_injective M.toIntegralMarking (integralRingMap f) f.injective, fun _ => rfl,
    hI, hN, hT₀, hG₀, hT, hr, ha, hLift, hC.2.2.1.trans hC'.2.2.1.symm, hn, hp, ?_⟩
  choose e ve en ep using hC.2.2.2.2.2.1
  choose e' ve' en' ep' using hC'.2.2.2.2.2.1
  let φ (i : D.I) := (e' i).symm.toRingHom.comp (f.comp (e i).toRingHom)
  have hφ (i : D.I) (z : C.chart.parameter i) : e' i (φ i z) = f (e i z) :=
    (e' i).apply_symm_apply _
  let tvalue (t : C.chart.chart.torus) : TorusValues D (integralRing K) :=
    (Units.map f.toMonoidHom).comp t.val
  have htorus (t : C.chart.chart.torus) : ∃ u : C'.chart.chart.torus, u.val = tvalue t := by
    let z : CellValues D (integralRing K) C'.chart.negative C'.chart.positive := (0, tvalue t, 0)
    let g := cellValue M.toIntegralMarking (integralRing K) C'.chart.negative C'.chart.positive z
    obtain ⟨u, y, he⟩ := (C'.chart.rational z).mp ⟨g, rfl⟩
    exact ⟨u, congrArg (fun z => z.2.1) he⟩
  choose tmap htmap using htorus
  refine ⟨φ, tmap, fun i x => ?_, fun t x => ?_⟩
  · rw [ve', hφ, hv, ve]
  · apply cellValues_eq_of_cast hn hp _ _ _ ?_ _
    · intro i
      let j := Fin.cast (congrArg List.length hn) i
      have hj : C.chart.chart.neg i = C'.chart.chart.neg j := by
        rw [C.chart.neg_slots, C'.chart.neg_slots, hC.2.2.1, hC'.2.2.1,
          getElem_of_equal_rootLists C.chart.negative C'.chart.negative hn i]
      change f (algebraMap Integers.{u} F (C.chart.chart.negUnit i : Integers.{u}) *
        C.chart.chart.negMap i (x (C.chart.chart.neg i))) =
        algebraMap Integers.{u} K (C'.chart.chart.negUnit j : Integers.{u}) *
          C'.chart.chart.negMap j (φ (C'.chart.chart.neg j) (x (C'.chart.chart.neg j)))
      rw [hC.2.2.2.1 i, hC'.2.2.2.1 j]
      simp only [Units.val_one, map_one, one_mul]
      rw [en _ i rfl _, en' _ j rfl _, hφ, hj]
    · exact (htmap t).symm
    · intro i
      let j := Fin.cast (congrArg List.length hp) i
      have hj : C.chart.chart.pos i = C'.chart.chart.pos j := by
        rw [C.chart.pos_slots, C'.chart.pos_slots, hC.2.2.1, hC'.2.2.1,
          getElem_of_equal_rootLists C.chart.positive C'.chart.positive hp i]
      change f (algebraMap Integers.{u} F (C.chart.chart.posUnit i : Integers.{u}) *
        C.chart.chart.posMap i (x (C.chart.chart.pos i))) =
        algebraMap Integers.{u} K (C'.chart.chart.posUnit j : Integers.{u}) *
          C'.chart.chart.posMap j (φ (C'.chart.chart.pos j) (x (C'.chart.chart.pos j)))
      rw [hC.2.2.2.2.1 i, hC'.2.2.2.2.1 j]
      simp only [Units.val_one, map_one, one_mul]
      rw [ep _ i rfl _, ep' _ j rfl _, hφ, hj]

end SplitScalarCharts


section ExceptionalAlcoveVertices

open Specs.ExceptionalAffineRootSystems

section ExceptionalRootBounds

open private threeTimesCartanInverse
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

variable {n : ℕ} {C B : Matrix (Fin n) (Fin n) ℤ}

private theorem rootCoordinate_norm (hSym : C.IsSymm) (hDiag : ∀ i, C i i = 2)
    {r : Fin n → ℤ} (hr : IsRootCoordinate C r) : r ⬝ᵥ (C *ᵥ r) = 2 := by
  induction hr with
  | simple i =>
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
    exact hDiag i
  | @reflect r _ i ih =>
    let z : Fin n → ℤ := Pi.single i 1
    let c : ℤ := (C *ᵥ r) i
    have hcol : r ⬝ᵥ (C.col i) = c := by
      simp only [c, Matrix.mulVec, dotProduct, Matrix.col]
      apply Finset.sum_congr rfl
      intro j _
      change r j * C j i = C i j * r j
      rw [hSym.apply i j, mul_comm]
    change (r - c • z) ⬝ᵥ (C *ᵥ (r - c • z)) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, z,
      Matrix.mulVec_single_one, single_dotProduct, one_mul, ih, hcol]
    change 2 - c • c - c • (c - c • C i i) = 2
    rw [hDiag]
    change 2 - c * c - c * (c - c * 2) = 2
    ring

private theorem rootCoordinate_neg (hDiag : ∀ i, C i i = 2)
    {r : Fin n → ℤ} (hr : IsRootCoordinate C r) : IsRootCoordinate C (-r) := by
  induction hr with
  | simple i =>
    have h := (IsRootCoordinate.simple (C := C) i).reflect i
    suffices simpleReflection C i (Pi.single i 1) = -(Pi.single i 1) by rwa [← this]
    simp only [simpleReflection, Matrix.mulVec_single_one]
    change Pi.single i 1 - C i i • (Pi.single i 1) = -(Pi.single i 1)
    rw [hDiag]
    abel
  | @reflect r _ i ih =>
    convert ih.reflect i using 1
    simp only [simpleReflection, Matrix.mulVec_neg, Pi.neg_apply, neg_smul]
    abel

private theorem dominantRootCoordinates {d : ℤ} (hd : 0 < d)
    (hInverse : B * C = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hB : ∀ i j, 0 ≤ B i j) (hBdiag : ∀ i, d < B i i)
    (k : Fin n) (θ : Fin n → ℤ) (hdiag : ∀ i, B i i = 2 * d → i = k)
    (hθ : ∀ i, B i k = d * θ i) (r : Fin n → ℤ)
    (hnorm : r ⬝ᵥ (C *ᵥ r) = 2) (hdominant : ∀ i, 0 ≤ (C *ᵥ r) i) : r = θ := by
  classical
  let f := C *ᵥ r
  have hfactor : B *ᵥ f = d • r := by
    change B *ᵥ (C *ᵥ r) = d • r
    rw [Matrix.mulVec_mulVec, hInverse, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hnorm' : f ⬝ᵥ (B *ᵥ f) = 2 * d := by
    rw [hfactor, dotProduct_smul, dotProduct_comm f r, hnorm, smul_eq_mul, mul_comm]
  have hsum : ∑ i, f i ≤ 1 := by
    have hbound (i : Fin n) : (d + 1) * f i ≤ f i * (B *ᵥ f) i := by
      have hbf : (d + 1) * f i ≤ (B *ᵥ f) i := by
        calc
          _ ≤ B i i * f i := mul_le_mul_of_nonneg_right (by have := hBdiag i; omega) (hdominant i)
          _ ≤ _ := Finset.single_le_sum (fun j _ => mul_nonneg (hB i j) (hdominant j))
            (Finset.mem_univ i)
      by_cases hzero : f i = 0
      · simp [hzero]
      · have hone : 1 ≤ f i := by have := hdominant i; change 0 ≤ f i at this; omega
        calc
          _ ≤ f i * ((d + 1) * f i) := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hone (mul_nonneg (by omega) (hdominant i))
          _ ≤ _ := mul_le_mul_of_nonneg_left hbf (hdominant i)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
    rw [← Finset.mul_sum] at h
    change (d + 1) * (∑ i, f i) ≤ f ⬝ᵥ (B *ᵥ f) at h
    rw [hnorm'] at h
    by_contra! h'
    have : (d + 1) * 2 ≤ (d + 1) * ∑ i, f i :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  obtain ⟨i, hi⟩ : ∃ i, 0 < f i := by
    by_contra! hh
    have hf : f = 0 := funext fun i => le_antisymm (hh i) (hdominant i)
    have h := hnorm
    change r ⬝ᵥ f = 2 at h
    rw [hf, dotProduct_zero] at h
    omega
  have hi' : f i = 1 :=
    le_antisymm ((Finset.single_le_sum (fun j _ => hdominant j) (Finset.mem_univ i)).trans hsum)
      (by omega)
  have hrest : ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
    rw [hi'] at he
    exact le_antisymm (by omega) (Finset.sum_nonneg fun j _ => hdominant j)
  have hf : f = Pi.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j; simpa using hi'
    · rw [Pi.single_eq_of_ne hji]
      exact le_antisymm ((Finset.single_le_sum (fun j _ => hdominant j)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).trans_eq hrest) (hdominant j)
  rw [hf, Matrix.mulVec_single_one, single_dotProduct, one_mul] at hnorm'
  have hik : i = k := hdiag i hnorm'
  rw [hf, hik, Matrix.mulVec_single_one] at hfactor
  funext j
  have h := congrFun hfactor j
  change B j k = d * r j at h
  rw [hθ] at h
  exact (mul_left_cancel₀ hd.ne' h).symm

private theorem highestRootCoordinates {d : ℤ} (hd : 0 < d)
    (hSym : C.IsSymm) (hDiag : ∀ i, C i i = 2)
    (hInverse : B * C = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hB : ∀ i j, 0 ≤ B i j) (hBdiag : ∀ i, d < B i i)
    (k : Fin n) (θ : Fin n → ℤ) (hdiag : ∀ i, B i i = 2 * d → i = k)
    (hθ : ∀ i, B i k = d * θ i) (hfinite : {r | IsRootCoordinate C r}.Finite) :
    IsRootCoordinate C (-θ) ∧
      ∀ r, IsRootCoordinate C r → ∀ i, -θ i ≤ r i ∧ r i ≤ θ i := by
  classical
  have hhighest {r : Fin n → ℤ} (hr : IsRootCoordinate C r) :
      IsRootCoordinate C θ ∧ r ≤ θ := by
    let candidates := hfinite.toFinset.filter (fun x => r ≤ x)
    have hmem (x : Fin n → ℤ) : x ∈ candidates ↔ IsRootCoordinate C x ∧ r ≤ x := by
      simp [candidates]
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image candidates (fun x => ∑ i, x i)
      ⟨r, (hmem r).mpr ⟨hr, le_rfl⟩⟩
    obtain ⟨hsroot, hrs⟩ := (hmem s).mp hs
    have hdom (i : Fin n) : 0 ≤ (C *ᵥ s) i := by
      by_contra! hh
      let z := simpleReflection C i s
      have hz (j : Fin n) : s j ≤ z j := by
        change s j ≤ s j - (C *ᵥ s) i * (Pi.single i 1 : Fin n → ℤ) j
        rw [Pi.single_apply]
        split
        · simp only [mul_one, le_sub_self_iff]
          exact hh.le
        · simp
      have hsz := hmax z ((hmem z).mpr ⟨hsroot.reflect i, hrs.trans hz⟩)
      have hp : ∑ j, z j = (∑ j, s j) - (C *ᵥ s) i := by
        unfold z
        simp only [simpleReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [Pi.single_apply]
      omega
    have he := dominantRootCoordinates hd hInverse hB hBdiag k θ hdiag hθ s
      (rootCoordinate_norm hSym hDiag hsroot) hdom
    exact he ▸ ⟨hsroot, hrs⟩
  refine ⟨rootCoordinate_neg hDiag (hhighest (.simple k)).1, ?_⟩
  intro r hr i
  exact ⟨by have h := (hhighest (rootCoordinate_neg hDiag hr)).2 i
            change -r i ≤ θ i at h
            omega,
    (hhighest hr).2 i⟩

private def e6HighestCoefficients : Fin 6 → ℤ :=
  ![1, 2, 2, 3, 2, 1]

/-- The integral matrix obtained by multiplying the inverse Cartan matrix by 2. -/
private def e7ScaledCartanInverse : Matrix (Fin 7) (Fin 7) ℤ :=
  !![4, 4, 6, 8, 6, 4, 2;
    4, 7, 8, 12, 9, 6, 3;
    6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6;
    6, 9, 12, 18, 15, 10, 5;
    4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3]

private def e7HighestCoefficients : Fin 7 → ℤ :=
  ![2, 2, 3, 4, 3, 2, 1]

/-- The integral matrix obtained by multiplying the inverse Cartan matrix by 1. -/
private def e8ScaledCartanInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
    5, 8, 10, 15, 12, 9, 6, 3;
    7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6;
    8, 12, 16, 24, 20, 15, 10, 5;
    6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3;
    2, 3, 4, 6, 5, 4, 3, 2]

private def e8HighestCoefficients : Fin 8 → ℤ :=
  ![2, 3, 4, 6, 5, 4, 3, 2]

/-- Bounds on the simple-root coefficients, including the actual opposite
of the highest root in the reflection orbit. -/
private theorem exceptionalHighestCoordinates (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hfinite : {r | IsRootCoordinate (exceptionalCartan n) r}.Finite) :
    ∃ θ : Fin n → ℤ, (∀ i, 0 < θ i) ∧ IsRootCoordinate (exceptionalCartan n) (-θ) ∧
      ∀ r, IsRootCoordinate (exceptionalCartan n) r → ∀ i, -θ i ≤ r i ∧ r i ≤ θ i := by
  rcases hn with rfl | rfl | rfl
  · refine ⟨e6HighestCoefficients, by decide, highestRootCoordinates (d := 3)
      (B := threeTimesCartanInverse) (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide) (by decide) 1 _ (by decide) (by decide) hfinite⟩
  · refine ⟨e7HighestCoefficients, by decide, highestRootCoordinates (d := 2)
      (B := e7ScaledCartanInverse) (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide) (by decide) 0 _ (by decide) (by decide) hfinite⟩
  · refine ⟨e8HighestCoefficients, by decide, highestRootCoordinates (d := 1)
      (B := e8ScaledCartanInverse) (by decide) (by decide) (by decide) (by decide)
      (by intro i; fin_cases i <;> decide) (by decide) 7 _ (by decide) (by decide) hfinite⟩

end ExceptionalRootBounds

open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems

section AlcoveVertices

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V} {n : ℕ}

/-- The positive affine equations of a simplex are nonnegative sums of its
barycentric coordinates. Only its facet equations can have one summand. -/
private theorem simplexAlcoveVertices (hn : 0 < n)
    (coordinates : V ≃ₗ[ℚ] (Fin n → ℚ)) (facet : Option (Fin n) → J × ℤ)
    (hfacet : Function.Injective facet) (hpos : ∀ i, A.positive p (facet i))
    (w : Option (Fin n) → ℚ) (hw : ∀ i, 0 < w i)
    (hcoordinate : ∀ x i, w (some i) * A.wallValue (facet (some i)) x = coordinates x i)
    (hsum : ∀ x, ∑ i, w i * A.wallValue (facet i) x = 1)
    (hcombination : ∀ a, A.positive p a →
      ∃ c : Option (Fin n) → ℚ, (∀ i, 0 ≤ c i) ∧ (∃ i, 0 < c i) ∧
        (∀ i, (∀ j ≠ i, c j = 0) → a = facet i) ∧
        ∀ x, A.wallValue a x = ∑ i, c i * (w i * A.wallValue (facet i) x)) :
    ∀ a : A.SimpleWall p, ∃! x, IsAlcoveVertex A p a x := by
  classical
  have realizable (v : Option (Fin n) → ℚ) (hv : ∑ j, v j = 1) :
      ∃ x, ∀ j, w j * A.wallValue (facet j) x = v j := by
    obtain ⟨x, hx⟩ := coordinates.surjective (fun i => v (some i))
    have hsome (i : Fin n) : w (some i) * A.wallValue (facet (some i)) x = v (some i) :=
      (hcoordinate x i).trans (congrFun hx i)
    have he := (hsum x).trans hv.symm
    rw [Fintype.sum_option, Fintype.sum_option] at he
    simp_rw [hsome] at he
    exact ⟨x, fun j => j.rec (add_right_cancel he) hsome⟩
  have simple (i : Option (Fin n)) : A.IsSimple p (facet i) := by
    let z : Option (Fin n) → ℚ := fun j => if j = i then 0 else 1
    obtain ⟨j, hj⟩ : ∃ j : Option (Fin n), j ≠ i := by
      cases i with
      | none => exact ⟨some ⟨0, hn⟩, by simp⟩
      | some i => exact ⟨none, by simp⟩
    have hz : 0 < ∑ j, z j := by
      refine Finset.sum_pos' (fun k _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
      · dsimp [z]; split <;> norm_num
      · simp [z, hj]
    let v : Option (Fin n) → ℚ := fun j => z j / ∑ k, z k
    have hv : ∑ j, v j = 1 := by
      change (∑ j, z j / ∑ k, z k) = 1
      rw [← Finset.sum_div, div_self hz.ne']
    obtain ⟨x, hx⟩ := realizable v hv
    refine ⟨hpos i, x, by
      have he := hx i
      have hz' : v i = 0 := by simp [v, z]
      rw [hz'] at he
      exact (mul_eq_zero.mp he).resolve_left (hw i).ne', ?_⟩
    intro a ha hne
    obtain ⟨c, hc, _, hs, he⟩ := hcombination a ha
    have ht : ∃ j, j ≠ i ∧ 0 < c j := by
      by_contra! hn'
      exact hne (hs i fun j hj => le_antisymm (hn' j hj) (hc j))
    obtain ⟨j, hji, hj⟩ := ht
    change 0 < A.wallValue a x
    rw [he]
    simp_rw [hx]
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hc k) ?_)
      ⟨j, Finset.mem_univ _, mul_pos hj (by simpa [v, z, hji] using inv_pos.mpr hz)⟩
    apply div_nonneg _ hz.le
    dsimp [z]
    split <;> norm_num
  have covers (a : A.SimpleWall p) : ∃ i, facet i = a.val := by
    obtain ⟨ha, x, hx, hbound⟩ := a.property
    by_contra! hne
    obtain ⟨c, hc, ⟨i, hi⟩, _, he⟩ := hcombination a.val ha
    apply (ne_of_gt _) hx
    change 0 < A.wallValue a.val x
    rw [he]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hc j) (mul_pos (hw j) (hbound _ (hpos j) (hne j))).le)
      ⟨i, Finset.mem_univ _, mul_pos hi (mul_pos (hw i) (hbound _ (hpos i) (hne i)))⟩
  intro a
  obtain ⟨i, hi⟩ := covers a
  let v : Option (Fin n) → ℚ := fun j => if j = i then 1 else 0
  have hv : ∑ j, v j = 1 := by simp [v]
  obtain ⟨x, hx⟩ := realizable v hv
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨c, hc, _, _, he⟩ := hcombination b hb
    rw [he]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (hx j ▸ by
      dsimp [v]; split <;> norm_num))
  · intro b
    obtain ⟨j, hj⟩ := covers b
    rw [← hj, ← mul_eq_zero_iff_left (hw j).ne', hx]
    have hij : j = i ↔ b = a :=
      ⟨fun h => Subtype.ext (hj.symm.trans ((congrArg facet h).trans hi)),
        fun h => hfacet (hj.trans ((congrArg Subtype.val h).trans hi.symm))⟩
    by_cases h : j = i <;> simp [v, h, ← hij]
  · intro y hy
    have he (j : Option (Fin n)) (hj : j ≠ i) : A.wallValue (facet j) y = 0 :=
      (hy.2 ⟨facet j, simple j⟩).mpr (fun h => hj (hfacet ((congrArg Subtype.val h).trans hi.symm)))
    have hz (j : Option (Fin n)) (hj : j ≠ i) : w j * A.wallValue (facet j) y = 0 := by
      rw [he j hj, mul_zero]
    have hyone : w i * A.wallValue (facet i) y = 1 :=
      (Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)).symm.trans (hsum y)
    apply coordinates.injective
    funext j
    rw [← hcoordinate, ← hcoordinate, hx]
    by_cases h : some j = i
    · rw [h, hyone]; simp [v]
    · rw [hz _ h]; simp [v, h]

/-- Simple-root coordinates and a highest root determine the vertices of
the alcove with the pinned positive affine walls. -/
private theorem alcoveVertices_of_rootCoordinates (hn : 0 < n)
    (coordinates : V ≃ₗ[ℚ] (Fin n → ℚ)) (simple : Fin n ↪ J)
    (highestOpposite : J) (θ : Fin n → ℚ) (hθ : ∀ i, 0 < θ i)
    (hReduced : A.ReducedDirections)
    (hSimple : ∀ x i, A.root (simple i) x = coordinates x i)
    (hHighest : ∀ x, A.root highestOpposite x = - ∑ i, θ i * coordinates x i)
    (hposSimple : ∀ i, A.positive p (simple i, 0))
    (hposHighest : A.positive p (highestOpposite, 1))
    (hLevel : ∀ a m, A.positive p (a, m) → 0 ≤ m)
    (r : J → Fin n → ℚ) (hRoot : ∀ a x, A.root a x = ∑ i, r a i * coordinates x i)
    (hLower : ∀ a i, -θ i ≤ r a i)
    (hPositive : ∀ a, A.positive p (a, 0) → ∀ i, 0 ≤ r a i) :
    ∀ a : A.SimpleWall p, ∃! x, IsAlcoveVertex A p a x := by
  classical
  let scale : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ) :=
    LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfNeZero ℚ ℚ (θ i) (hθ i).ne')
  let f : Option (Fin n) → J × ℤ := fun i => i.rec (highestOpposite, 1) (fun j => (simple j, 0))
  have hfac : Function.Injective f := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => have h : (1 : ℤ) = 0 := congrArg Prod.snd he; omega
    | some i =>
      cases j with
      | none => have h : (0 : ℤ) = 1 := congrArg Prod.snd he; omega
      | some j => exact congrArg some (simple.injective (congrArg Prod.fst he))
  have hsome (x : V) (i : Fin n) : A.wallValue (f (some i)) x = coordinates x i := by
    change A.root (simple i) x + (0 : ℤ) = _
    simpa using hSimple x i
  have hnone (x : V) : A.wallValue (f none) x = 1 - ∑ i, θ i * coordinates x i := by
    change A.root highestOpposite x + (1 : ℤ) = _
    rw [hHighest]
    push_cast
    ring
  have make (x : V) (i : Fin n) : (coordinates.trans scale) x i = θ i * coordinates x i := rfl
  -- In the general simplex lemma all facet functions may be rescaled by
  -- positive constants without changing the conditions on vertices.
  let w : Option (Fin n) → ℚ := fun i => i.rec 1 θ
  have hw (i : Option (Fin n)) : 0 < w i := i.rec zero_lt_one hθ
  apply simplexAlcoveVertices hn (coordinates.trans scale) f hfac
    (fun i => i.rec hposHighest hposSimple) w hw
  · intro x i
    rw [hsome]
    exact (make x i).symm
  · intro x
    rw [Fintype.sum_option, hnone]
    simp only [w, one_mul, hsome]
    ring
  · rintro ⟨a, m⟩ ha
    let c : Option (Fin n) → ℚ := fun i => i.rec (m : ℚ) (fun j => (m : ℚ) + r a j / θ j)
    have hm : 0 ≤ m := hLevel a m ha
    have hnonneg (i : Option (Fin n)) : 0 ≤ c i := by
      cases i with
      | none =>
        change (0 : ℚ) ≤ (m : ℚ)
        exact_mod_cast hm
      | some i =>
        change 0 ≤ (m : ℚ) + r a i / θ i
        by_cases h : m = 0
        · subst m
          simpa using div_nonneg (hPositive a ha i) (hθ i).le
        · have hm' : (1 : ℚ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
          have hdiv : -1 ≤ r a i / θ i := (le_div_iff₀ (hθ i)).mpr (by simpa using hLower a i)
          linarith
    have hformula (x : V) : A.wallValue (a, m) x =
        ∑ i, c i * (w i * A.wallValue (f i) x) := by
      rw [Fintype.sum_option, hnone]
      change A.root a x + (m : ℚ) =
        (m : ℚ) * (1 * (1 - ∑ i, θ i * coordinates x i)) +
          ∑ i, ((m : ℚ) + r a i / θ i) * (θ i * A.wallValue (f (some i)) x)
      rw [hRoot]
      simp only [hsome, one_mul, add_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hterm (i : Fin n) : r a i / θ i * (θ i * coordinates x i) =
          r a i * coordinates x i := by rw [← mul_assoc, div_mul_cancel₀ _ (hθ i).ne']
      simp only [hterm]
      ring
    have hcpos : ∃ i, 0 < c i := by
      apply Classical.byContradiction
      intro h
      have hz (i) : c i = 0 := le_antisymm (not_lt.mp (fun hi => h ⟨i, hi⟩)) (hnonneg i)
      change 0 < A.wallValue (a, m) p at ha
      rw [hformula] at ha
      simp [hz] at ha
    refine ⟨c, hnonneg, hcpos, ?_, hformula⟩
    intro i hi
    cases i with
    | none =>
      have hmpos : 0 < m := by
        obtain ⟨j, hj⟩ := hcpos
        cases j with
        | none =>
          change (0 : ℚ) < (m : ℚ) at hj
          exact_mod_cast hj
        | some j => rw [hi (some j) (by simp)] at hj; exact (lt_irrefl _ hj).elim
      have hrel (j : Fin n) : r a j = -(m : ℚ) * θ j := by
        have h := hi (some j) (by simp)
        change (m : ℚ) + r a j / θ j = 0 at h
        apply (div_eq_iff (hθ j).ne').mp
        linarith
      let j : Fin n := ⟨0, hn⟩
      have hle : (m : ℚ) ≤ 1 := by
        have h := hLower a j
        rw [hrel] at h
        nlinarith [(hθ j)]
      have hmone : m = 1 := by
        have hmle : m ≤ (1 : ℤ) := by exact_mod_cast hle
        omega
      have he : a = highestOpposite := by
        apply hReduced.1
        ext x
        rw [hHighest, hRoot]
        simp [hrel, hmone, neg_mul, Finset.sum_neg_distrib]
      exact Prod.ext he hmone
    | some j =>
      have hmzero : m = 0 := by
        have h := hi none (by simp)
        change (m : ℚ) = 0 at h
        exact_mod_cast h
      have hz (i : Fin n) (hne : i ≠ j) : r a i = 0 := by
        have h := hi (some i) (by simpa using hne)
        change (m : ℚ) + r a i / θ i = 0 at h
        simpa [hmzero, div_eq_zero_iff, (hθ i).ne'] using h
      have he : A.root a = (r a j) • A.root (simple j) := by
        ext x
        rw [hRoot, Finset.sum_eq_single j (fun i _ hi => by rw [hz i hi, zero_mul]) (by simp)]
        simp [hSimple, smul_eq_mul]
      rcases hReduced.2 (simple j) a (r a j) he with hx | hx
      · exact Prod.ext hx.symm hmzero
      · have hp := hposSimple j
        subst m
        change 0 < A.root (simple j) p + (0 : ℤ) at hp
        change 0 < A.root a p + (0 : ℤ) at ha
        rw [hx, LinearMap.neg_apply] at ha
        push_cast at hp ha
        linarith

end AlcoveVertices

section SplitAlcoveVertices

open Specs.Pinning (BasedRootDatum)
open scoped TensorProduct

universe u

/-- The vertices of the standard split exceptional alcove, in the
cocharacter apartment of the given based datum. -/
theorem splitAlcoveVertices {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (hNum : ExceptionalNumbering D n b) (p : ℚ ⊗[ℤ] D.Y)
    (hs : ∀ i m, (ApartmentRoots.split D.datum ℚ).positive p (i, m) ↔
      0 < m ∨ (m = 0 ∧ D.base.IsPos i)) :
    ∀ a : (ApartmentRoots.split D.datum ℚ).SimpleWall p,
      ∃! x, IsAlcoveVertex (ApartmentRoots.split D.datum ℚ) p a x := by
  classical
  let _ := D.finiteRoots
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := D.reduced
  let A := ApartmentRoots.split D.datum ℚ
  have hSym : (exceptionalCartan n).IsSymm := by
    rcases hn with rfl | rfl | rfl <;> decide
  obtain ⟨ρ, hρ⟩ := ExceptionalAffineRootSystems.pairedRootCoordinates D.datum D.base b
    (exceptionalCartan n) hSym (fun i j => (hNum.2 i j).symm)
  have hfinite : {r | IsRootCoordinate (exceptionalCartan n) r}.Finite := by
    have he : {r | IsRootCoordinate (exceptionalCartan n) r} =
        Set.range (fun i => (ρ i).val) := by
      ext r
      constructor
      · intro hr
        obtain ⟨i, hi⟩ := ρ.surjective ⟨r, hr⟩
        exact ⟨i, congrArg Subtype.val hi⟩
      · rintro ⟨i, rfl⟩
        exact (ρ i).property
    rw [he]
    exact Set.finite_range _
  obtain ⟨θ, hθ, hθroot, hBounds⟩ := exceptionalHighestCoordinates hn hfinite
  obtain ⟨t, ht⟩ := ρ.surjective ⟨-θ, hθroot⟩
  have ht' : (ρ t).val = -θ := congrArg Subtype.val ht
  obtain ⟨e, he⟩ := ExceptionalAffineRootSystems.cocharacterApartmentCoordinates
    (K := ℚ) D.datum D.base b hNum.1
  have hRoot (i : D.I) (x : ℚ ⊗[ℤ] D.Y) :
      A.root i x = ∑ j, ((ρ i).val j : ℚ) * e x j := by
    rw [ExceptionalAffineRootSystems.rootValuesFromCoordinates D.datum D.base b i _
      (hρ i).1, ← he]
    rfl
  have heval (i : Fin n) (x : ℚ ⊗[ℤ] D.Y) : A.root (b i) x = e x i := by
    change (simpleRootValues D.datum D.base b ℚ) x i = _
    rw [← he]
    rfl
  let s : Fin n ↪ D.I := ⟨fun i => (b i).val, fun _ _ h => b.injective (Subtype.ext h)⟩
  have hn' : 0 < n := by rcases hn with rfl | rfl | rfl <;> decide
  refine alcoveVertices_of_rootCoordinates hn' e s t (fun i => (θ i : ℚ))
    (fun i => by exact_mod_cast hθ i) (ExceptionalAffineRootSystems.splitReducedDirections D.datum)
    (fun x i => heval i x) ?_ ?_ ?_ ?_ (fun i j => ((ρ i).val j : ℚ)) hRoot ?_ ?_
  · intro x
    change A.root t x = _
    rw [hRoot, ht']
    simp [neg_mul, Finset.sum_neg_distrib]
  · intro i
    exact (hs _ _).2 (Or.inr ⟨rfl, D.base.isPos_of_mem_support (b i).property⟩)
  · exact (hs _ _).2 (Or.inl Int.one_pos)
  · intro i m hm
    rcases (hs i m).mp hm with h | ⟨h, _⟩
    · exact h.le
    · rw [h]
  · intro i j
    exact_mod_cast (hBounds (ρ i).val (ρ i).property j).1
  · intro i hi j
    have hpos : D.base.IsPos i := by
      rcases (hs i 0).mp hi with h | ⟨_, h⟩
      · exact (lt_irrefl _ h).elim
      · exact h
    obtain ⟨z, _, hz, hzroot⟩ := D.base.exists_root_eq_sum_int i
    have hsum (f : D.I → ℤ) : (∑ j, f (b j) • D.datum.root (b j)) =
        ∑ j ∈ D.base.support, f j • D.datum.root j := by
      rw [D.base.support.sum_subtype (p := (· ∈ D.base.support)) (by simp)]
      exact Equiv.sum_comp b (fun j : D.base.support => f j • D.datum.root j)
    let eval := Fintype.linearCombination ℤ (fun j : Fin n => D.datum.root (b j))
    have heq : (ρ i).val = fun j => z (b j) :=
      (linearIndependent_iff_injective_fintypeLinearCombination.mp
        (D.base.linearIndepOn_root.comp b b.injective) : Function.Injective eval)
        (by simp only [Fintype.linearCombination_apply, ← (hρ i).1, hsum, ← hzroot])
    rw [heq]
    rcases hz with hz | hz
    · exact_mod_cast hz.le (b j)
    · change 0 < D.base.height i at hpos
      rw [D.base.height_eq_sum hzroot] at hpos
      exact ((Finset.sum_nonpos fun k _ => hz.le k).not_gt hpos).elim

end SplitAlcoveVertices

section SplitUnramified

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open scoped TensorProduct
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

/-- The split comparisons and type quotients over the base field and all
finite unramified levels, with their actual scalar and coefficient maps. -/
theorem splitBruhatAtUnramifiedLevels
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (n : ℕ) (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) (hD : ExceptionalNumbering D n b)
    (hE : ExceptionalNumbering E n b')
    (hsc : D.datum.corootSpan ℤ = ⊤) (had : E.datum.rootSpan ℤ = ⊤) :
    ∃ (p : ℚ ⊗[ℤ] D.Y) (p' : ℚ ⊗[ℤ] E.Y)
      (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) (X : SplitLevel F c p p' e),
      e.toLinearMap = c.pushCocharacter.baseChange ℚ ∧ p' = e p ∧
      ∀ (K : Type u) [Field K] [Algebra F K] [FiniteDimensional F K]
        [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
        IsUnramifiedLocalExtension F K →
        ∃ Y : SplitLevel K c p p' e,
          let s := scalarPoints M (algebraMap F K)
          let s' := scalarPoints M' (algebraMap F K)
          ScalarComparison (algebraMap F K) s X.sc Y.sc ∧
          ScalarComparison (algebraMap F K) s' X.ad Y.ad ∧
          TypeQuotientTransport X.typeQuotient Y.typeQuotient s' (MonoidHom.id _) ∧
          Y.Coefficients (F := F) ∧
          (∀ w, ∀ a ∈ Y.sc.localIwahori.normalizer.word w, a ∈ D.base.support) ∧
          (∀ w, ∀ a ∈ Y.ad.localIwahori.normalizer.word w, a ∈ E.base.support) := by
  classical
  let _ := E.reduced
  let A' := ApartmentRoots.split E.datum ℚ
  have hReflection : A'.ReflectionClosed := fun i j => ⟨E.datum.reflectionPerm i j,
    ExceptionalAffineRootSystems.splitReflectionClosed (K := ℚ) E.datum i j⟩
  have hReduced : A'.ReducedDirections := ExceptionalAffineRootSystems.splitReducedDirections E.datum
  obtain ⟨p, e, negative, positive, negative', positive', he, all⟩ :=
    splitBruhatAtLocalField c n b hsc had hD.1 hE.1
  have levels (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] :
      ∃ X : SplitLevel K c p (e p) e,
        (∀ w, ∀ a ∈ X.sc.localIwahori.normalizer.word w, a ∈ D.base.support) ∧
        (∀ w, ∀ a ∈ X.ad.localIwahori.normalizer.word w, a ∈ E.base.support) ∧
        X.sc.chart.negative = negative ∧ X.sc.chart.positive = positive ∧
        X.ad.chart.negative = negative' ∧ X.ad.chart.positive = positive' := by
    obtain ⟨B, B', C, C', hC, hC', br, br', hcentral, hnormal, _, hTrans, hw, hw', hneg, hpos, hneg', hpos'⟩ :=
      all K
    have hsign (i : E.I) (m : ℤ) : A'.positive (e p) (i, m) ↔
        0 < m ∨ (m = 0 ∧ E.base.IsPos i) := by
      simpa [hC'.2.2.1] using C'.chart.signs.positive_iff i m
    obtain ⟨Q⟩ := typeQuotientOfTranslatedChart C' hnormal br'.ordinary_normalizer
      hC'.2.2.2.2.2.2.2.2 hReflection hReduced (splitAlcoveVertices b' hn hE _ hsign)
      br'.base_chart hTrans
    exact ⟨⟨C, C', B, B', hC, hC', br, br', hcentral, Q⟩, hw, hw', hneg, hpos, hneg', hpos'⟩
  obtain ⟨X, hwX, hwX', hnX, hpX, hnX', hpX'⟩ := levels F
  have hNormalSc : X.sc.G₀.Normal := by
    rw [ordinaryRange_generates _ X.sc_points.2.2.2.2.2.2.2.2]
    infer_instance
  refine ⟨p, e p, e, X, he, rfl, ?_⟩
  intro K _ _ _ _ _ _ _ hv
  obtain ⟨Y, hwY, hwY', hnY, hpY, hnY', hpY'⟩ := levels K
  let f : F →+* K := algebraMap F K
  have hSc := splitScalarComparison X.sc Y.sc X.sc_points Y.sc_points hwX hwY
    X.sc_bruhat Y.sc_bruhat hNormalSc f hv (hnX.trans hnY.symm) (hpX.trans hpY.symm)
  have hAd := splitScalarComparison X.ad Y.ad X.ad_points Y.ad_points hwX' hwY'
    X.ad_bruhat Y.ad_bruhat X.typeQuotient.normal f hv (hnX'.trans hnY'.symm) (hpX'.trans hpY'.symm)
  refine ⟨Y, hSc, hAd, ?_, splitLevelCoefficientActions Y hwY hwY' hv, hwY, hwY'⟩
  let s := scalarPoints M' f
  obtain ⟨_, _, _, hN, _, hG₀, _, _, hlabel, _, _, _⟩ := hAd
  apply typeQuotientTransport_of_lifts X.ad Y.ad X.typeQuotient Y.typeQuotient s
    (le_of_eq hG₀.symm) (MonoidHom.id _)
  intro ω
  let n := X.typeQuotient.lift ω
  let n' : Y.ad.N := ⟨s n, (SetLike.ext_iff.mp hN _).mpr n.property⟩
  exact sameLabel_div_mem_unitTorus Y.ad (n := n') (m := Y.typeQuotient.lift ω)
    ((hlabel n n' rfl).1.trans ((X.typeQuotient.affine_lift ω).trans (Y.typeQuotient.affine_lift ω).symm))

end SplitUnramified

end ExceptionalAlcoveVertices

section PinnedCoefficientActions

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum BasedIso transportCharacter)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint markedRootPoint
  markedWeylWord markedWall wallMatrix weylWordPerm integralTestAlgebra)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutation)
open Specs.IntegralRootRelations (upper)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.CharacterPairing (characterValue)
open Matrix (SpecialLinearGroup)
open scoped CategoryTheory.MonObj TensorProduct

open private fibrePointEquiv indexEquiv_reflectionPerm markedTorusEquiv markedTorusIncl
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private pinnedLift_character from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private simpleWeylWords weylWord_index
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private torusPoint_bijective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

universe u

attribute [local instance] integerAlgebra

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {D : BasedRootDatum.{u}} {M : Model D}
  (C : MarkedFibre M F)

/-- The pinned automorphisms acting on the marked scalar-extended points. -/
noncomputable def markedPinnedAction :
    Aut C.realization.pinned →* MulAut (FieldPoints M K) where
  toFun f :=
    let R := CommAlgCat.of F K
    let e := fibrePointEquiv C R
    let g := (((groupPointsFunctor F).mapIso f.asIso.hom.group).app R).groupIsoToMulEquiv
    (e.symm.trans g).trans e
  map_one' := by
    let R := CommAlgCat.of F K
    let e := fibrePointEquiv C R
    apply MulEquiv.ext
    intro x
    change e (e.symm x ≫ 𝟙 _) = x
    rw [Category.comp_id, MulEquiv.apply_symm_apply]
  map_mul' f g := by
    let R := CommAlgCat.of F K
    let e := fibrePointEquiv C R
    apply MulEquiv.ext
    intro x
    change e (e.symm x ≫ (g.asIso.hom.group.hom.hom.hom ≫ f.asIso.hom.group.hom.hom.hom)) =
      e (e.symm (e (e.symm x ≫ g.asIso.hom.group.hom.hom.hom)) ≫ f.asIso.hom.group.hom.hom.hom)
    rw [MulEquiv.symm_apply_apply, Category.assoc]

private theorem markedPinnedAction_apply (f : Aut C.realization.pinned)
    (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    markedPinnedAction (K := K) C f (markedFibrePoint C (CommAlgCat.of F K) v) =
      markedFibrePoint C (CommAlgCat.of F K) (v ≫ f.asIso.hom.group.hom.hom.hom) := by
  let e := fibrePointEquiv C (CommAlgCat.of F K)
  change e (e.symm (e v) ≫ _) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem markedCoefficientAction_apply (σ : Gal(K/F))
    (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    markedCoefficientAction M σ (markedFibrePoint C (CommAlgCat.of F K) v) =
      markedFibrePoint C (CommAlgCat.of F K) ((testSpec F).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v) := by
  obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  let f := CommAlgCat.ofHom σ.toAlgHom
  let R := CommAlgCat.of F K
  rw [← he, ← he]
  exact (ConcreteCategory.congr_hom (e.hom.naturality f) v).symm

private theorem markedCoefficientAction_commutes (σ : Gal(K/F)) (f : Aut C.realization.pinned) :
    Commute (markedCoefficientAction M σ) (markedPinnedAction (K := K) C f) := by
  apply MulEquiv.ext
  intro x
  let e := fibrePointEquiv C (CommAlgCat.of F K)
  obtain ⟨v, rfl⟩ := e.surjective x
  change markedCoefficientAction M σ (markedPinnedAction (K := K) C f (markedFibrePoint C (CommAlgCat.of F K) v)) =
    markedPinnedAction (K := K) C f (markedCoefficientAction M σ (markedFibrePoint C (CommAlgCat.of F K) v))
  rw [markedPinnedAction_apply, markedCoefficientAction_apply, markedCoefficientAction_apply,
    markedPinnedAction_apply, Category.assoc]

/-- The pinned coefficient action on split marked points over any splitting
level of the outer datum. -/
noncomputable def markedPinnedCoefficientAction
    (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased) : Gal(K/F) →* MulAut (FieldPoints M K) where
  toFun σ := markedPinnedAction (K := K) C (l (ω σ)) * markedCoefficientAction M σ
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (markedCoefficientAction M σ),
      (markedCoefficientAction_commutes C σ (l (ω τ))).eq, mul_assoc]

theorem markedPinnedCoefficientAction_apply (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased) (σ : Gal(K/F))
    (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    markedPinnedCoefficientAction (K := K) C l ω σ (markedFibrePoint C (CommAlgCat.of F K) v) =
      pinnedCoefficientPoint C (l (ω σ)) σ v := by
  change markedPinnedAction (K := K) C (l (ω σ)) (markedCoefficientAction M σ (markedFibrePoint C (CommAlgCat.of F K) v)) = _
  rw [markedCoefficientAction_apply, markedPinnedAction_apply]
  rfl

variable {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G}
  (hQ : SplitSequence C.realization.pinned C.realization.attached l Q)
  (δ : Aut C.realization.attached.toBased)

include hQ in
private theorem markedPinnedAction_rankOne (a : D.base.support)
    (U : SpecialLinearGroup (Fin 2) K) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    markedPinnedAction (K := K) C (l δ) ((M.rankOne a).app (integralRing K) U) =
      (M.rankOne (simplePermutation D τ a)).app (integralRing K) U := by
  intro τ
  let R := CommAlgCat.of F K
  let e := fibrePointEquiv C R
  let v := e.symm ((M.rankOne a).app (integralRing K) U)
  have hv : markedFibrePoint C R v = (M.rankOne a).app (integralRing K) U :=
    e.apply_symm_apply _
  have hpin := (ExceptionalValuedTorusNormalizer.markedPinnedDiagramAction C.realization hQ δ).1 a
  rw [← hv, markedPinnedAction_apply]
  exact ExceptionalMarkedRootDescent.pinnedSimpleRankOneEquivariance C (l δ) a
    (simplePermutation D τ a) hpin R U v hv

include hQ in
private theorem markedPinnedAction_word (word : List D.I)
    (hword : ∀ i ∈ word, i ∈ D.base.support) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    markedPinnedAction (K := K) C (l δ) (markedWeylWord M.toIntegralMarking (integralRing K) word) =
      markedWeylWord M.toIntegralMarking (integralRing K) (word.map τ.val.indexEquiv) := by
  intro τ
  induction word with
  | nil => exact map_one _
  | cons a word ih =>
    have ha := hword a (List.mem_cons_self)
    change markedPinnedAction (K := K) C (l δ) ((markedWall M.toIntegralMarking (integralRing K) a 1 : FieldPoints M K) *
      markedWeylWord M.toIntegralMarking (integralRing K) word) =
      (markedWall M.toIntegralMarking (integralRing K) (τ.val.indexEquiv a) 1 : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) (word.map τ.val.indexEquiv)
    rw [map_mul, ih (fun i hi => hword i (List.mem_cons_of_mem _ hi))]
    congr 1
    exact markedPinnedAction_rankOne C hQ δ ⟨a, ha⟩ (wallMatrix (1 : Kˣ))

private theorem diagram_weylWordPerm (τ : BasedIso D D) (l : List D.I) (i : D.I) :
    weylWordPerm (l.map τ.val.indexEquiv) (τ.val.indexEquiv i) =
      τ.val.indexEquiv (weylWordPerm l i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change D.datum.reflectionPerm (τ.val.indexEquiv a)
      (weylWordPerm (l.map τ.val.indexEquiv) (τ.val.indexEquiv i)) =
        τ.val.indexEquiv (D.datum.reflectionPerm a (weylWordPerm l i))
    rw [ih, indexEquiv_reflectionPerm τ]

include hQ in
/-- The actual pinned diagram automorphism permutes all absolute root
subgroups and changes their marked parameters by integral units. -/
theorem markedPinnedAction_root (i : D.I) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    ∃ c : Integers.{u}ˣ, ∀ z : K,
      markedPinnedAction (K := K) C (l δ) (markedRootPoint M.toIntegralMarking (integralRing K) i z) =
        markedRootPoint M.toIntegralMarking (integralRing K) (τ.val.indexEquiv i)
          (algebraMap Integers.{u} K (c : Integers.{u}) * z) := by
  intro τ
  obtain ⟨a, w, hw⟩ := simpleWeylTransport D i
  obtain ⟨word, hsimple, hwlabel⟩ := simpleWeylWords D
  let l₀ := word w
  let l₁ := l₀.map τ.val.indexEquiv
  have hlabel : weylWordPerm l₀ a.val = i := by rw [weylWord_index, hwlabel, hw]
  let b := simplePermutation D τ a
  have hlabel' : weylWordPerm l₁ b.val = τ.val.indexEquiv i := by
    change weylWordPerm (l₀.map τ.val.indexEquiv) (τ.val.indexEquiv a.val) = _
    rw [diagram_weylWordPerm, hlabel]
  obtain ⟨c, hc⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M l₀ a.val
  obtain ⟨d, hd⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M l₁ b.val
  let R := integralRing K
  let φ := markedPinnedAction (K := K) C (l δ)
  let n := markedWeylWord M.toIntegralMarking R l₀
  let n' := markedWeylWord M.toIntegralMarking R l₁
  have hn : φ n = n' := markedPinnedAction_word C hQ δ l₀ (hsimple w)
  have ha (z : K) : φ (markedRootPoint M.toIntegralMarking R a.val z) =
      markedRootPoint M.toIntegralMarking R b.val z := by
    change φ (M.line.point R z ≫ (M.root a.val).hom.hom) =
      M.line.point R z ≫ (M.root b.val).hom.hom
    simpa only [M.rankOneUpper] using markedPinnedAction_rankOne C hQ δ a (upper z)
  refine ⟨d * c⁻¹, fun z => ?_⟩
  let y : K := algebraMap Integers.{u} K (↑c⁻¹ : Integers.{u}) * z
  have hy : algebraMap Integers.{u} K (↑c : Integers.{u}) * y = z := by
    dsimp only [y]
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hsource := hc R y
  change n * markedRootPoint M.toIntegralMarking R a.val y * n⁻¹ =
    markedRootPoint M.toIntegralMarking R (weylWordPerm l₀ a.val)
      (algebraMap Integers.{u} K (↑c : Integers.{u}) * y) at hsource
  rw [hlabel, hy] at hsource
  rw [← hsource, map_mul, map_mul, map_inv, hn, ha]
  have htarget := hd R y
  change n' * markedRootPoint M.toIntegralMarking R b.val y * n'⁻¹ =
    markedRootPoint M.toIntegralMarking R (weylWordPerm l₁ b.val)
      (algebraMap Integers.{u} K (↑d : Integers.{u}) * y) at htarget
  rw [htarget, hlabel']
  congr 1
  rw [Units.val_mul, map_mul, mul_assoc]

include hQ in
/-- On the marked torus a pinned automorphism transports evaluation of
each character by the actual integral weight-lattice isomorphism. -/
theorem markedPinnedAction_torus (t : TorusValues D (integralRing K)) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    ∃ t' : TorusValues D (integralRing K),
      markedPinnedAction (K := K) C (l δ)
          (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) =
        torusPoint D (integralRing K) t' ≫ M.torus.hom.hom ∧
      ∀ χ : D.X, t' (Multiplicative.ofAdd (τ.val.weightEquiv χ)) = t (Multiplicative.ofAdd χ) := by
  intro τ
  let R := CommAlgCat.of F K
  let S := integralRing K
  let e := markedTorusEquiv C R
  let f := (l δ).asIso.hom
  let s := e.symm (torusPoint D S t)
  let s' : GroupPoints C.realization.pinned.pair.T.group R := s ≫ f.torus.hom.hom.hom
  obtain ⟨t', ht'⟩ := (torusPoint_bijective D S).2 (e s')
  have hs : e s = torusPoint D S t := e.apply_symm_apply _
  let i := C.realization.pinned.pair.T.inclusion.hom.hom
  have hcomm : i ≫ f.group.hom.hom.hom = f.torus.hom.hom.hom ≫ i :=
    congrArg (fun j => j.hom.hom) f.torus_comm
  refine ⟨t', ?_, ?_⟩
  · rw [← hs, ← markedTorusIncl, markedPinnedAction_apply]
    change markedFibrePoint C R ((s ≫ i) ≫ f.group.hom.hom.hom) = _
    rw [Category.assoc, hcomm, ← Category.assoc]
    change markedFibrePoint C R (s' ≫ i) = _
    rw [markedTorusIncl, ht']
  · intro χ
    let d := C.realization.datumIso.val
    let χ₀ (x : D.X) := Additive.toMul (d.weightEquiv x)
    have htval (z : GroupPoints C.realization.pinned.pair.T.group R) (v : TorusValues D S)
        (hv : e z = torusPoint D S v) (x : D.X) :
        characterValue (χ₀ x) R z = (v (Multiplicative.ofAdd x) : K) := by
      let z₀ : GroupPoints ((fibre F).obj (splitTorus D)) R := z ≫ C.torusIso.inv.hom.hom
      have h₀ : forgetFibrePoint (splitTorus D) R z₀ = torusPoint D S v := hv
      have heval := C.torus_eval R z₀ v h₀ x
      change characterValue (χ₀ x) R
        ((z ≫ C.torusIso.inv.hom.hom) ≫ C.torusIso.hom.hom.hom) = _ at heval
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id] at heval
      simpa only [Grp.id_hom_hom, Category.comp_id] using heval
    let _ := C.realization.attached.comm
    have hχ : transportCharacter f.torus (χ₀ χ) = χ₀ (τ.val.weightEquiv χ) := by
      rw [pinnedLift_character hQ]
      change Additive.toMul (δ.asIso.hom.val.weightEquiv (d.weightEquiv χ)) =
        Additive.toMul (d.weightEquiv (d.weightEquiv.symm
          (δ.asIso.hom.val.weightEquiv (d.weightEquiv χ))))
      rw [LinearEquiv.apply_symm_apply]
    have hh : f.torus.hom ≫ χ₀ (τ.val.weightEquiv χ) = χ₀ χ := by
      rw [← hχ, transportCharacter, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    apply Units.ext
    rw [← htval s' t' ht'.symm, ← htval s t hs]
    unfold characterValue
    dsimp only [s']
    rw [Category.assoc, ← Grp.comp_hom_hom, hh]

end PinnedCoefficientActions

section PinnedApartmentAction

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open CategoryTheory
open scoped TensorProduct

open private rationalCocharacterAction reflection_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private e6Diagram_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

universe u

variable {D : BasedRootDatum.{u}}

private theorem diagram_positive (τ : BasedIso D D) (i : D.I) :
    D.base.IsPos (τ.val.indexEquiv i) ↔ D.base.IsPos i := by
  let _ := D.finiteRoots
  have mono (τ : BasedIso D D) (i : D.I) (hi : D.base.IsPos i) :
      D.base.IsPos (τ.val.indexEquiv i) := by
    have hs (j : D.I) (hj : j ∈ D.base.support) : τ.val.indexEquiv j ∈ D.base.support := by
      change τ.val.indexEquiv j ∈ (↑D.base.support : Set D.I)
      exact (Set.ext_iff.mp τ.property (τ.val.indexEquiv j)).mp
        (Set.mem_image_of_mem τ.val.indexEquiv hj)
    have hr (j : D.I) : τ.val.weightEquiv (D.datum.root j) = D.datum.root (τ.val.indexEquiv j) :=
      congrFun τ.val.toHom.root_weightMap j
    refine hi.induction_on_add (p := fun j => D.base.IsPos (τ.val.indexEquiv j))
      (fun j hj => D.base.isPos_of_mem_support (hs j hj)) ?_
    intro i j k hk hi hj
    apply hi.add (D.base.isPos_of_mem_support (hs j hj))
    rw [← hr, hk, map_add, hr, hr]
  refine ⟨fun h => ?_, mono τ i⟩
  have he := mono (Groupoid.inv (show D ⟶ D from τ)) (τ.val.indexEquiv i) h
  change D.base.IsPos (τ.val.indexEquiv.symm (τ.val.indexEquiv i)) at he
  rwa [Equiv.symm_apply_apply] at he

private theorem diagram_rootValue (τ : BasedIso D D) (i : D.I) (x : ℚ ⊗[ℤ] D.Y) :
    (ApartmentRoots.split D.datum ℚ).root (τ.val.indexEquiv i) (diagramCocharacters τ.val x) =
      (ApartmentRoots.split D.datum ℚ).root i x := by
  let A := ApartmentRoots.split D.datum ℚ
  let g : (ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] ℚ := (A.root (τ.val.indexEquiv i)).comp
    (diagramCocharacters τ.val).toLinearMap
  suffices g = A.root i from LinearMap.congr_fun this x
  apply TensorProduct.AlgebraTensorModule.ext
  intro q y
  have h (y : D.Y) : g ((1 : ℚ) ⊗ₜ[ℤ] y) = A.root i (1 ⊗ₜ[ℤ] y) := by
    change RootData.extendFunctional ℚ (D.datum.root' (τ.val.indexEquiv i))
      (diagramCocharacters τ.val ((1 : ℚ) ⊗ₜ[ℤ] y)) =
        RootData.extendFunctional ℚ (D.datum.root' i) (1 ⊗ₜ[ℤ] y)
    rw [diagramCocharacters, LinearEquiv.baseChange_tmul, RootData.extendFunctional_one_tmul,
      RootData.extendFunctional_one_tmul, τ.val.root'_coweightEquiv]
  have hq : q ⊗ₜ[ℤ] y = q • ((1 : ℚ) ⊗ₜ[ℤ] y) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hq, map_smul, map_smul, h]

private theorem diagram_corootValue (τ : BasedIso D D) (i : D.I) :
    diagramCocharacters τ.val ((ApartmentRoots.split D.datum ℚ).coroot i) =
      (ApartmentRoots.split D.datum ℚ).coroot (τ.val.indexEquiv i) := by
  change τ.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y ((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i) =
    (1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot (τ.val.indexEquiv i)
  rw [LinearEquiv.baseChange_tmul]
  congr 1
  apply τ.val.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = τ.val.toHom.coweightMap _
  rw [RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]

private theorem diagram_preserves_alcove (τ : BasedIso D D) (p : ℚ ⊗[ℤ] D.Y)
    (hs : ∀ i m, (ApartmentRoots.split D.datum ℚ).positive p (i, m) ↔
      0 < m ∨ (m = 0 ∧ D.base.IsPos i)) :
    diagramCocharacters τ.val '' (ApartmentRoots.split D.datum ℚ).alcove p =
      (ApartmentRoots.split D.datum ℚ).alcove p := by
  let A := ApartmentRoots.split D.datum ℚ
  let h : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] _ := diagramCocharacters τ.val
  have hpos (i : D.I) (m : ℤ) : A.positive p (τ.val.indexEquiv i, m) ↔ A.positive p (i, m) := by
    rw [hs, hs, diagram_positive]
  have hval (x : ℚ ⊗[ℤ] D.Y) (i : D.I) (m : ℤ) :
      A.positive (h x) (τ.val.indexEquiv i, m) ↔ A.positive x (i, m) := by
    change 0 < A.root (τ.val.indexEquiv i) (h x) + (m : ℚ) ↔ 0 < A.root i x + (m : ℚ)
    rw [diagram_rootValue]
  ext x
  obtain ⟨x, rfl⟩ := h.surjective x
  change (∃ y ∈ A.alcove p, h y = h x) ↔ h x ∈ A.alcove p
  refine ⟨?_, fun hx => ⟨x, ?_, rfl⟩⟩
  · rintro ⟨y, hy, he⟩
    have hy' : x ∈ A.alcove p := (h.injective he) ▸ hy
    rintro ⟨i, m⟩ hp
    obtain ⟨j, rfl⟩ := τ.val.indexEquiv.surjective i
    exact (hval x j m).mpr (hy' (j, m) ((hpos j m).mp hp))
  · rintro ⟨i, m⟩ hp
    exact (hval x i m).mp (hx (τ.val.indexEquiv i, m) ((hpos i m).mpr hp))

end PinnedApartmentAction

section PinnedLocalComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedRootPoint markedWeylWord)
open Specs.ExceptionalIwahoriCongruence (integralRing cellValue CellValues markedRootFactors rootValuePoint)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.OrderedRootProducts (Enumerates)
open ValuativeRel
open scoped TensorProduct CategoryTheory.MonObj

open private cellValue_eq_mul rootWord_eq_prod from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private rationalCocharacterAction reflection_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer

attribute [local instance] integerAlgebra

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {p : ℚ ⊗[ℤ] D.Y}
  {B : MarkedFibre M K} {adjoint : Bool}
  (P : LocalComparison (j := identityPoints M K) (Wf := D.datum.weylGroup)
    (ApartmentRoots.split D.datum ℚ) p)
  (hP : SplitPointComparison B adjoint P)
  (C : MarkedFibre M F)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G}
  (hQ : SplitSequence C.realization.pinned C.realization.attached l Q)

include hP in
private theorem splitChartSigns :
    PinnedWallSigns (ApartmentRoots.split D.datum ℚ) p D.base.IsPos := by
  have hs := P.chart.signs
  rw [hP.2.2.1] at hs
  simpa only [id_eq, exists_eq_left] using hs

include hP in
private theorem splitIwahori_root_mem
    (a : D.I) (t : K) (ht : normalizedValuation K t ≤ 1)
    (hneg : ¬ D.base.IsPos a → normalizedValuation K t < 1) :
    markedRootPoint M.toIntegralMarking (integralRing K) a t ∈ P.I := by
  classical
  let P₀ := P.chart
  let n := P₀.negative
  let q := P₀.positive
  let C₀ := splitRootChart (M := M) (K := K) n q P₀.negative_enumerates P₀.positive_enumerates
    p (splitChartSigns P hP)
  let x := Function.update (fun _ : D.I => (0 : K)) a t
  let z := C₀.chart.coordinates ⟨1, Set.mem_univ _⟩ x
  refine (splitIwahori_absoluteChart P.localIwahori n q P₀.negative_enumerates P₀.positive_enumerates
    _).mpr ⟨z, splitCell_single P₀.negative_enumerates P₀.positive_enumerates (splitChartSigns P hP) a t,
      ?_, ?_, ?_⟩
  · intro χ
    change normalizedValuation K (↑((1 : TorusValues D (integralRing K)) χ) : K) = 1
    simp
  · intro i
    change normalizedValuation K (algebraMap Integers.{u} K 1 * x n[i]) < 1
    have hi : ¬ D.base.IsPos n[i] :=
      (P₀.negative_enumerates.2 _).mp (List.getElem_mem i.isLt)
    rw [map_one, one_mul, show x n[i] = if n[i] = a then t else 0 from Function.update_apply _ _ _ _]
    split_ifs with he
    · exact hneg (he ▸ hi)
    · simp
  · intro i
    change normalizedValuation K (algebraMap Integers.{u} K 1 * x q[i]) ≤ 1
    rw [map_one, one_mul, show x q[i] = if q[i] = a then t else 0 from Function.update_apply _ _ _ _]
    split_ifs
    · exact ht
    · simp

private theorem subgroup_map_eq_of_equiv {G : Type*} [Group G] (a : MulAut G) (H : Subgroup G)
    (h : ∀ g ∈ H, a g ∈ H) (h' : ∀ g ∈ H, a.symm g ∈ H) :
    H.map a.toMonoidHom = H := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h x hx
  · intro hg
    exact ⟨a.symm g, h' g hg, a.apply_symm_apply g⟩

include hP hQ in
private theorem markedPinnedAction_preservesI (δ : Aut C.realization.attached.toBased) :
    P.I.map (markedPinnedAction (K := K) C (l δ)).toMonoidHom = P.I := by
  have mono (δ : Aut C.realization.attached.toBased) (g : FieldPoints M K) (hg : g ∈ P.I) :
      markedPinnedAction (K := K) C (l δ) g ∈ P.I := by
    let R := integralRing K
    let n := P.chart.negative
    let q := P.chart.positive
    let v := normalizedValuation K
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    let φ := markedPinnedAction (K := K) C (l δ)
    obtain ⟨z, hz, ht, hn, hp⟩ :=
      (splitIwahori_absoluteChart P.localIwahori n q P.chart.negative_enumerates
        P.chart.positive_enumerates g).mp hg
    obtain ⟨t, htorus, htvals⟩ := markedPinnedAction_torus C hQ δ z.2.1
    have hT : φ (torusPoint D R z.2.1 ≫ M.torus.hom.hom : FieldPoints M K) ∈ P.I := by
      rw [htorus]
      apply unitTorus_le_iwahori P
      apply torusPoint_mem_unitTorus
      intro χ
      obtain ⟨χ, rfl⟩ := (Multiplicative.ofAdd.surjective.comp τ.val.weightEquiv.surjective) χ
      change v (t (Multiplicative.ofAdd (τ.val.weightEquiv χ)) : K) = 1
      rw [htvals]
      exact ht _
    have hroot (a : D.I) (s : K) (hs : v s ≤ 1) (hneg : ¬ D.base.IsPos a → v s < 1) :
        φ (markedRootPoint M.toIntegralMarking R a s) ∈ P.I := by
      obtain ⟨c, hc⟩ := markedPinnedAction_root (K := K) C hQ δ a
      rw [hc]
      have hv : v (algebraMap Integers.{u} K (c : Integers.{u}) * s) = v s := by
        rw [map_mul, integerUnit_value, one_mul]
      apply splitIwahori_root_mem P hP
      · rw [hv]
        exact hs
      · intro h
        rw [hv]
        exact hneg (fun ha => h ((diagram_positive τ a).mpr ha))
    have hN : φ (markedRootFactors M.toIntegralMarking R n z.1).prod ∈ P.I := by
      rw [map_list_prod]
      apply P.I.list_prod_mem
      intro f hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
      rw [markedRootFactors, List.mem_ofFn'] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hroot n[i] (z.1 i) (hn i).le (fun _ => hn i)
    have hP' : φ (markedRootFactors M.toIntegralMarking R q z.2.2).prod ∈ P.I := by
      rw [map_list_prod]
      apply P.I.list_prod_mem
      intro f hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
      rw [markedRootFactors, List.mem_ofFn'] at hx
      obtain ⟨i, rfl⟩ := hx
      have hi : D.base.IsPos q[i] := (P.chart.positive_enumerates.2 _).mp (List.getElem_mem i.isLt)
      exact hroot q[i] (z.2.2 i) (hp i) (fun h => (h hi).elim)
    change φ g ∈ P.I
    rw [← hz, cellValue_eq_mul, rootWord_eq_prod, rootWord_eq_prod, map_mul, map_mul]
    exact P.I.mul_mem hN (P.I.mul_mem hT hP')
  apply subgroup_map_eq_of_equiv _ _ (mono δ)
  intro g hg
  change ((markedPinnedAction (K := K) C (l δ))⁻¹) g ∈ P.I
  simpa only [map_inv] using mono δ⁻¹ g hg

private theorem diagram_word_mul (τ : BasedIso D D) (word : List D.I) :
    let s := RootPairing.weylGroup.ofIdx D.datum
    τ.val * (word.map s).prod.val =
      (((word.map τ.val.indexEquiv).map s).prod).val * τ.val := by
  intro s
  induction word with
  | nil => simp
  | cons a word ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
    change τ.val * (RootPairing.Equiv.reflection D.datum a * _) = _
    rw [← mul_assoc, reflection_natural, mul_assoc, ih, ← mul_assoc]
    rfl

include hP hQ in
private theorem markedPinnedAction_affine (δ : Aut C.realization.attached.toBased)
    (hword : ∀ w, ∀ a ∈ P.localIwahori.normalizer.word w, a ∈ D.base.support) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    let φ := markedPinnedAction (K := K) C (l δ)
    (∀ g ∈ P.localIwahori.normalizer.torus, φ g ∈ P.localIwahori.normalizer.torus) ∧
    (∀ g ∈ P.N, φ g ∈ P.N) ∧
    ∀ (n n' : P.N), (n' : FieldPoints M K) = φ n →
      P.affine n' = (diagramCocharacters τ.val).toAffineEquiv * P.affine n *
        (diagramCocharacters τ.val).toAffineEquiv⁻¹ := by
  classical
  intro τ φ
  let R := integralRing K
  let N := P.localIwahori.normalizer
  have hT (g : FieldPoints M K) (hg : g ∈ N.torus) : φ g ∈ N.torus := by
    obtain ⟨t, ht⟩ := (N.torusPoints g).mp hg
    obtain ⟨t', he, _⟩ := markedPinnedAction_torus (K := K) C hQ δ t
    exact (N.torusPoints _).mpr ⟨t', by rw [show g = _ from ht, he]; rfl⟩
  have hFact (n : P.N) :
      ∃ (t t' : TorusValues D R) (ls : List D.I),
        (∀ a ∈ ls, a ∈ D.base.support) ∧
        (∀ a ∈ ls.map τ.val.indexEquiv, a ∈ D.base.support) ∧
        (n : FieldPoints M K) =
          (torusPoint D R t ≫ M.torus.hom.hom : FieldPoints M K) * markedWeylWord M.toIntegralMarking R ls ∧
        φ n = (torusPoint D R t' ≫ M.torus.hom.hom : FieldPoints M K) *
          markedWeylWord M.toIntegralMarking R (ls.map τ.val.indexEquiv) ∧
        ∀ χ : D.X, t' (Multiplicative.ofAdd (τ.val.weightEquiv χ)) = t (Multiplicative.ofAdd χ) := by
    obtain ⟨t, _, h⟩ := normalizerTorusWord N n
    let word := N.word (N.label n)
    have hw : ∀ a ∈ word, a ∈ D.base.support := hword _
    have hw' : ∀ a ∈ word.map τ.val.indexEquiv, a ∈ D.base.support := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact (Set.ext_iff.mp τ.property (τ.val.indexEquiv i)).mp
        (Set.mem_image_of_mem τ.val.indexEquiv (hw i hi))
    obtain ⟨t', ht', hχ⟩ := markedPinnedAction_torus (K := K) C hQ δ t
    refine ⟨t, t', word, hw, hw', h, ?_, hχ⟩
    rw [show (n : FieldPoints M K) = _ from h, map_mul, ht', markedPinnedAction_word C hQ δ word hw]
  refine ⟨hT, ?_, ?_⟩
  · intro g hg
    let n : P.N := ⟨g, hg⟩
    obtain ⟨t, t', ls, hl, hl', ht, ht', _⟩ := hFact n
    change φ n ∈ P.N
    rw [ht']
    exact P.N.mul_mem (N.torus_le ((N.torusPoints _).2 ⟨t', rfl⟩))
      (markedWord_mem_splitNormalizer P hP _ hl')
  · intro n n' hn'
    obtain ⟨t, t', ls, hl, hl', ht, ht', hχ⟩ := hFact n
    let _ := D.freeY
    let _ := D.finiteY
    let b := Module.Free.chooseBasis ℤ D.Y
    let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
    obtain ⟨hw, hlog⟩ := labelAndTranslationOfWord P (MonoidHom.id _) hP.2.1 b n ls hl t ht
    obtain ⟨hw', hlog'⟩ := labelAndTranslationOfWord P (MonoidHom.id _) hP.2.1 b n'
      (ls.map τ.val.indexEquiv) hl' t' (hn'.trans ht')
    change N.label n = _ at hw
    change N.label n' = _ at hw'
    have hW : τ.val * (N.label n).val = (N.label n').val * τ.val := by
      rw [hw, hw']
      exact diagram_word_mul τ ls
    let e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] _ := diagramCocharacters τ.val
    have hL (x : ℚ ⊗[ℤ] D.Y) :
        e ((rationalCocharacterAction D (N.label n).val) x) =
          rationalCocharacterAction D (N.label n').val (e x) := by
      have he := congrArg (rationalCocharacterAction D) hW
      rw [map_mul, map_mul] at he
      exact DFunLike.congr_fun he x
    have hy :
        τ.val.coweightEquiv.symm (N.translation (N.torusPart n)).toAdd =
          (N.translation (N.torusPart n')).toAdd := by
      apply D.datum.toLinearMap.flip.toPerfPair.injective
      ext χ'
      obtain ⟨χ, rfl⟩ := τ.val.weightEquiv.surjective χ'
      change D.datum.toLinearMap (τ.val.weightEquiv χ)
          (τ.val.coweightEquiv.symm (N.translation (N.torusPart n)).toAdd) =
        D.datum.toLinearMap (τ.val.weightEquiv χ) (N.translation (N.torusPart n')).toAdd
      rw [τ.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply, hlog, hlog', hχ]
    have htrans : e ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) =
        (1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n')).toAdd := by
      change τ.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y _ = _
      rw [LinearEquiv.baseChange_tmul, hy]
    apply AffineEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := e.surjective x
    change P.affine n' (e x) = e (P.affine n (e.symm (e x)))
    rw [LinearEquiv.symm_apply_apply, hP.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.1, map_add, htrans]
    exact congrArg (fun z => z + ((1 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n')).toAdd)) (hL x).symm


private theorem diagram_preserves_ordinary (τ : BasedIso D D)
    (g : (ℚ ⊗[ℤ] D.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] D.Y))
    (hg : g ∈ (ApartmentRoots.split D.datum ℚ).affineWeylGroup) :
    (diagramCocharacters τ.val).toAffineEquiv * g * (diagramCocharacters τ.val).toAffineEquiv⁻¹ ∈
      (ApartmentRoots.split D.datum ℚ).affineWeylGroup := by
  let A := ApartmentRoots.split D.datum ℚ
  let e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] _ := diagramCocharacters τ.val
  have hm := transportAffineOrdinary (A := A) (A' := A) e τ.val.indexEquiv
    (diagram_rootValue τ) (diagram_corootValue τ)
  rw [← hm]
  exact ⟨g, hg, rfl⟩

include hP hQ in
/-- A pinned diagram automorphism acts on the actual split Iwahori and
normalizer by the indicated affine conjugation on their labels. -/
theorem markedPinnedAction_comparison (δ : Aut C.realization.attached.toBased)
    (hword : ∀ w, ∀ a ∈ P.localIwahori.normalizer.word w, a ∈ D.base.support) :
    let τ := (markedDiagramEquiv C.realization δ).asIso.hom
    AutomorphismComparison P (markedPinnedAction (K := K) C (l δ))
      (diagramCocharacters τ.val).toAffineEquiv := by
  intro τ
  let φ := markedPinnedAction (K := K) C (l δ)
  let A := ApartmentRoots.split D.datum ℚ
  let N := P.localIwahori.normalizer
  let N₀ := (A.affineWeylGroup.comap P.affine).map P.N.subtype
  obtain ⟨hT, hN, ha⟩ := markedPinnedAction_affine P hP C hQ δ hword
  obtain ⟨hT', hN', _⟩ := markedPinnedAction_affine P hP C hQ δ⁻¹ hword
  have hTorus : N.torus.map φ.toMonoidHom = N.torus :=
    subgroup_map_eq_of_equiv φ N.torus hT (fun g hg => by
      change φ⁻¹ g ∈ N.torus
      simpa only [map_inv] using hT' g hg)
  have hNorm : P.N.map φ.toMonoidHom = P.N :=
    subgroup_map_eq_of_equiv φ P.N hN (fun g hg => by
      change φ⁻¹ g ∈ P.N
      simpa only [map_inv] using hN' g hg)
  have hI := markedPinnedAction_preservesI P hP C hQ δ
  have hIneq : P.I ⊓ P.N = P.T₀ := P.localIwahori.intersection
  have hUnit : P.T₀.map φ.toMonoidHom = P.T₀ := by
    rw [← hIneq, Subgroup.map_inf _ _ _ φ.injective, hI, hNorm]
  have ordinary (δ : Aut C.realization.attached.toBased) (g : FieldPoints M K) (hg : g ∈ N₀) :
      markedPinnedAction (K := K) C (l δ) g ∈ N₀ := by
    obtain ⟨_, hm, h⟩ := markedPinnedAction_affine P hP C hQ δ hword
    obtain ⟨n, hn, rfl⟩ := hg
    let m : P.N := ⟨markedPinnedAction (K := K) C (l δ) n, hm _ n.property⟩
    refine ⟨m, ?_, rfl⟩
    change P.affine m ∈ A.affineWeylGroup
    rw [h n m rfl]
    exact diagram_preserves_ordinary _ _ hn
  have hOrd : N₀.map φ.toMonoidHom = N₀ :=
    subgroup_map_eq_of_equiv φ N₀ (ordinary δ) (fun g hg => by
      change φ⁻¹ g ∈ N₀
      simpa only [map_inv] using ordinary δ⁻¹ g hg)
  have hG : P.G₀.map φ.toMonoidHom = P.G₀ := by
    change (P.I ⊔ N₀).map φ.toMonoidHom = P.I ⊔ N₀
    rw [Subgroup.map_sup, hI, hOrd]
  refine ⟨hI, hNorm, hUnit, hG, hTorus, diagram_preserves_alcove τ p
    (splitChartSigns P hP).positive_iff, ha, ?_⟩
  intro w
  let e : (ℚ ⊗[ℤ] D.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] D.Y) := (diagramCocharacters τ.val).toAffineEquiv
  let w' : A.affineWeylGroup := ⟨e * w.val * e⁻¹, diagram_preserves_ordinary τ _ w.property⟩
  let n := P.lift w
  let n' : P.N := ⟨φ n, hN _ n.property⟩
  refine ⟨w', rfl, sameLabel_div_mem_unitTorus P (n := n') (m := P.lift w') ?_⟩
  rw [ha n n' rfl, P.lift_label, P.lift_label]

end PinnedLocalComparison

section AutomorphismTypeQuotients


open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open scoped CategoryTheory.MonObj

attribute [local instance] integerAlgebra

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G W : Type u} [Group G] [Group W] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

private theorem composeAutomorphismComparisons
    (C : LocalComparison (j := j) (Wf := W) A p)
    (a b : MulAut G) (e f : V ≃ᵃ[ℚ] V)
    (ha : AutomorphismComparison C a e) (hb : AutomorphismComparison C b f) :
    AutomorphismComparison C (a * b) (e * f) := by
  obtain ⟨haI, haN, haU, haG, haT, haC, haAff, haL⟩ := ha
  obtain ⟨hbI, hbN, hbU, hbG, hbT, hbC, hbAff, hbL⟩ := hb
  have hmul : (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := rfl
  have hAff (n n' : C.N) (hn' : (n' : G) = (a * b) n) :
      C.affine n' = (e * f) * C.affine n * (e * f)⁻¹ := by
    let m : C.N := ⟨b n, (SetLike.ext_iff.mp hbN _).mp ⟨n, n.property, rfl⟩⟩
    rw [haAff m n' hn', hbAff n m rfl, mul_inv_rev]
    simp only [mul_assoc]
  refine ⟨by rw [hmul, ← Subgroup.map_map, hbI, haI],
    by rw [hmul, ← Subgroup.map_map, hbN, haN],
    by rw [hmul, ← Subgroup.map_map, hbU, haU],
    by rw [hmul, ← Subgroup.map_map, hbG, haG],
    by rw [hmul, ← Subgroup.map_map, hbT, haT],
    by rw [AffineEquiv.coe_mul, Set.image_comp, hbC, haC], hAff, ?_⟩
  intro w
  obtain ⟨v, hv, _⟩ := hbL w
  obtain ⟨z, hz, _⟩ := haL v
  have he : z.val = (e * f) * w.val * (e * f)⁻¹ := by
    rw [hz, hv, mul_inv_rev]
    simp only [mul_assoc]
  let n := C.lift w
  have hm : b n ∈ C.N := (SetLike.ext_iff.mp hbN _).mp ⟨n, n.property, rfl⟩
  let m : C.N := ⟨(a * b) n, (SetLike.ext_iff.mp haN _).mp ⟨b n, hm, rfl⟩⟩
  exact ⟨z, he, sameLabel_div_mem_unitTorus C (n := m) (m := C.lift z)
    ((hAff n m rfl).trans (by rw [C.lift_label, C.lift_label, he]))⟩

/-- An action on the marked point group preserving the local comparison
induces conjugation on the length-zero quotient. -/
theorem typeQuotientOfAutomorphismAction
    (C : LocalComparison (j := j) (Wf := W) A p)
    (Q : C.TypeQuotient) (hrange : C.affine.range = A.extendedAffineWeylGroup)
    {Γ : Type*} [Group Γ] (a : Γ →* MulAut G) (e : Γ → (V ≃ᵃ[ℚ] V))
    (h : ∀ σ, AutomorphismComparison C (a σ) (e σ)) :
    ∃ β : Γ →* MulAut (alcoveStabilizer A (A.alcove p)),
      ∀ σ, TypeQuotientTransport Q Q (a σ).toMonoidHom (β σ).toMonoidHom ∧
        ∀ z, (β σ z).val.val = e σ * z.val.val * (e σ)⁻¹ := by
  let Ω := alcoveStabilizer A (A.alcove p)
  let _ := Q.normal
  let q := Q.quotient
  have hG (σ : Γ) : C.G₀.map (a σ).toMonoidHom = C.G₀ := (h σ).2.2.2.1
  let quotientAction : Γ → MulAut (G ⧸ C.G₀) := fun ξ =>
    QuotientGroup.congr C.G₀ C.G₀ (a ξ) (hG ξ)
  let β₀ (σ : Γ) : MulAut Ω := (q.symm.trans (quotientAction σ)).trans q
  have hb (σ : Γ) (g : G) : β₀ σ (q (QuotientGroup.mk g)) = q (QuotientGroup.mk (a σ g)) := by
    change q (quotientAction σ (q.symm (q (QuotientGroup.mk g)))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg q (QuotientGroup.congr_mk C.G₀ C.G₀ (a σ) (hG σ) g)
  have hq : Function.Surjective (fun g : G => q (QuotientGroup.mk g)) :=
    q.surjective.comp QuotientGroup.mk_surjective
  let β : Γ →* MulAut Ω :=
    { toFun := β₀
      map_one' := by
        apply MulEquiv.ext
        intro z
        obtain ⟨g, rfl⟩ := hq z
        change β₀ 1 (q (QuotientGroup.mk g)) = q (QuotientGroup.mk g)
        rw [hb, map_one]
        rfl
      map_mul' σ τ := by
        apply MulEquiv.ext
        intro z
        obtain ⟨g, rfl⟩ := hq z
        change β₀ (σ * τ) (q (QuotientGroup.mk g)) = β₀ σ (β₀ τ (q (QuotientGroup.mk g)))
        rw [hb, hb, hb, map_mul]
        rfl }
  refine ⟨β, fun σ => ?_⟩
  obtain ⟨_, hN, _, _, _, hAlcove, hAffine, _⟩ := h σ
  have comparison (z : Ω) :
      (β σ z).val.val = e σ * z.val.val * (e σ)⁻¹ ∧
        a σ (Q.lift z) * (Q.lift (β σ z) : G)⁻¹ ∈ C.T₀ := by
    let n := Q.lift z
    let n' : C.N := ⟨a σ n, (SetLike.ext_iff.mp hN _).mp ⟨n, n.property, rfl⟩⟩
    let v : A.extendedAffineWeylGroup := ⟨C.affine n', hrange ▸ ⟨n', rfl⟩⟩
    have he : v.val = e σ * z.val.val * (e σ)⁻¹ :=
      (hAffine n n' rfl).trans (by rw [Q.affine_lift])
    have hi : (((e σ)⁻¹ : V ≃ᵃ[ℚ] V) : V → V) '' A.alcove p = A.alcove p := by
      nth_rw 1 [← hAlcove]
      rw [Set.image_image]
      simp [AffineEquiv.inv_def]
    have hv : v.val '' A.alcove p = A.alcove p := by
      rw [he, AffineEquiv.coe_mul, AffineEquiv.coe_mul, Set.image_comp, Set.image_comp,
        hi, z.property, hAlcove]
    let z' : Ω := ⟨v, hv⟩
    have hd : (n' : G) * (Q.lift z' : G)⁻¹ ∈ C.T₀ :=
      sameLabel_div_mem_unitTorus C (n := n') (m := Q.lift z') (Q.affine_lift z').symm
    have hqz : q (QuotientGroup.mk (n' : G)) = z' := by
      rw [← Q.quotient_lift z']
      apply congrArg q
      apply (QuotientGroup.eq_iff_div_mem).mpr
      rw [div_eq_mul_inv]
      exact (show C.I ≤ C.G₀ from le_sup_left) (unitTorus_le_iwahori C hd)
    have hz : β σ z = z' := by
      change β₀ σ z = z'
      rw [← Q.quotient_lift z, hb]
      exact hqz
    exact ⟨hz.symm ▸ he, hz.symm ▸ hd⟩
  exact ⟨⟨fun g => (hb σ g).symm, fun z => (comparison z).2⟩, fun z => (comparison z).1⟩

end AutomorphismTypeQuotients

section E6TypeAction

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open scoped TensorProduct Matrix

open private e6Diagram_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

universe u

private def coweightCharge : (Fin 6 → ℤ) →+ ZMod 3 where
  toFun := Specs.ExceptionalAffineRootSystems.e6CoweightClass
  map_zero' := by decide
  map_add' := by
    intro a b
    unfold Specs.ExceptionalAffineRootSystems.e6CoweightClass
    simp only [Pi.add_apply]
    push_cast
    ring

/-- Conjugation by the nontrivial pinned diagram acts by inversion on the
actual alcove stabilizer in the extended E₆ affine Weyl group. -/
theorem e6Diagram_inverts_alcoveStabilizer {D : BasedRootDatum.{u}}
    (b : Fin 6 ≃ D.base.support) (hNum : ExceptionalNumbering D 6 b)
    (p : ℚ ⊗[ℤ] D.Y) (geom : AlcoveGeometry (ApartmentRoots.split D.datum ℚ) p)
    (τ : BasedIso D D) (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) :
    let A := ApartmentRoots.split D.datum ℚ
    let h := (diagramCocharacters τ.val).toAffineEquiv
    ∀ z z' : alcoveStabilizer A (A.alcove p), z'.val.val = h * z.val.val * h⁻¹ → z' = z⁻¹ := by
  classical
  intro A h z z' hlabel
  let _ := D.finiteRoots
  let _ := D.reduced
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  have hC (i j : Fin 6) :
      Specs.ExceptionalAffineRootSystems.e6Cartan i j = D.datum.pairing (b i) (b j) :=
    (congrFun (congrFun e6_standardCartan.symm i) j).trans (hNum.2 i j).symm
  let φ := simpleRootValues D.datum D.base b ℚ
  obtain ⟨e, he⟩ := ExceptionalAffineRootSystems.cocharacterApartmentCoordinates
    (K := ℚ) D.datum D.base b hNum.1
  obtain ⟨hP, _, hImagem⟩ := ExceptionalAffineRootSystems.cocharacterLatticeCoordinates
    (K := ℚ) D.datum D.base b _ hC
  have hD := (ExceptionalAffineRootSystems.e6DiagramCoordinates (K := ℚ)
    D.datum D.base b τ.val hτ hC).1
  obtain ⟨f, _, hf, hker⟩ := ExceptionalAffineRootSystems.extendedTranslationQuotient A
  have hval (g : A.extendedAffineWeylGroup) : g.val 0 ∈ A.coweightLattice :=
    ((ExceptionalAffineRootSystems.affineGroupNormalForms A).2.2 _ |>.mp g.property).1
  let t : A.coweightLattice := ⟨z.val.val 0, hval z.val⟩
  let t' : A.coweightLattice := ⟨z'.val.val 0, hval z'.val⟩
  obtain ⟨m, hm⟩ := (hP t.val).mp t.property
  have ht' : t'.val = diagramCocharacters τ.val t.val := by
    change z'.val.val 0 = _
    rw [hlabel]
    change diagramCocharacters τ.val (z.val.val ((diagramCocharacters τ.val).symm 0)) =
      diagramCocharacters τ.val (z.val.val 0)
    rw [map_zero]
  have hm' (i : Fin 6) :
      φ t'.val i = (Specs.ExceptionalAffineRootSystems.e6Diagram.mulVec m i : ℚ) := by
    rw [ht', hD, hm, e6Diagram_apply]
  have hcharge : coweightCharge (Specs.ExceptionalAffineRootSystems.e6Diagram.mulVec m + m) = 0 := by
    rw [map_add]
    change Specs.ExceptionalAffineRootSystems.e6CoweightClass
        (Specs.ExceptionalAffineRootSystems.e6Diagram.mulVec m) +
      Specs.ExceptionalAffineRootSystems.e6CoweightClass m = 0
    rw [e6CoweightQuotient.2.2, neg_add_cancel]
  obtain ⟨r, hr⟩ := (e6CoweightQuotient.2.1 _).mpr hcharge
  have hSum : t'.val + t.val ∈ A.corootLattice := by
    have himage : φ (t'.val + t.val) ∈ φ '' (A.corootLattice : Set _) := by
      rw [hImagem]
      refine ⟨r, funext fun i => ?_⟩
      change (Specs.ExceptionalAffineRootSystems.e6Cartan.mulVec r i : ℚ) = _
      rw [hr, map_add]
      change (((Specs.ExceptionalAffineRootSystems.e6Diagram.mulVec m i + m i : ℤ) : ℚ)) =
        φ t'.val i + φ t.val i
      rw [hm', show φ t.val i = (m i : ℚ) from congrFun hm i, Int.cast_add]
    obtain ⟨y, hy, hye⟩ := himage
    have he' : e.toLinearMap y = e.toLinearMap (t'.val + t.val) := by
      rw [he]
      exact hye
    exact (e.injective he') ▸ hy
  have hfOne : f (z' * z).val = 1 := by
    change f (z'.val * z.val) = 1
    rw [map_mul, hf z'.val t' rfl, hf z.val t rfl]
    let Q := A.corootLattice.comap A.coweightLattice.subtype
    change Multiplicative.ofAdd ((QuotientAddGroup.mk' Q t') + (QuotientAddGroup.mk' Q t)) = 1
    rw [← map_add]
    exact congrArg Multiplicative.ofAdd ((QuotientAddGroup.eq_zero_iff _).mpr hSum)
  let w : A.affineWeylGroup := ⟨(z' * z).val.val, (hker (z' * z).val).mp hfOne⟩
  have hw : w = 1 := (geom.simply_transitive p geom.regular).unique
    (y₁ := w) (y₂ := 1) (z' * z).property (by simp)
  have hw' := congrArg (fun w : A.affineWeylGroup => w.val) hw
  have hω : z' * z = 1 := Subtype.ext (Subtype.ext hw')
  exact eq_inv_of_mul_eq_one_left hω

end E6TypeAction

section SplitComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open scoped TensorProduct CategoryTheory.MonObj
open ValuativeRel

attribute [local instance] integerAlgebra
universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}

private theorem splitOuterE6CoefficientActions (X : SplitLevel K c p p' e)
    (hv : IsUnramifiedLocalExtension F K)
    (b : Fin 6 ≃ D.base.support) (b' : Fin 6 ≃ E.base.support)
    (hNum : ExceptionalNumbering E 6 b')
    (C : MarkedFibre M F) (C' : MarkedFibre M' F)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Q' : AdjointQuotient C'.realization.pinned.pair.G}
    (hword : ∀ w, ∀ a ∈ X.sc.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ X.ad.localIwahori.normalizer.word w, a ∈ E.base.support) :
    X.OuterE6Coefficients b b' C C' (l := l) (l' := l') (Q := Q) (Q' := Q') := by
  intro hQ hQ' ω ω' τ τ' _
  let h (σ : Gal(K/F)) : (ℚ ⊗[ℤ] D.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] D.Y) :=
    (diagramCocharacters (τ σ).val).toAffineEquiv
  let h' (σ : Gal(K/F)) : (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y) :=
    (diagramCocharacters (τ' σ).val).toAffineEquiv
  let a := markedPinnedCoefficientAction (K := K) C l ω
  let a' := markedPinnedCoefficientAction (K := K) C' l' ω'
  have hNormalSc : X.sc.G₀.Normal := by
    rw [ordinaryRange_generates _ X.sc_points.2.2.2.2.2.2.2.2]
    infer_instance
  have hs (σ : Gal(K/F)) : AutomorphismComparison X.sc (a σ) (h σ) := by
    have hd := markedPinnedAction_comparison X.sc X.sc_points C hQ (ω σ) hword
    have hc := (splitCoefficientComparison X.sc X.sc_points hword X.sc_bruhat hNormalSc hv σ).1
    change AutomorphismComparison X.sc
      (markedPinnedAction (K := K) C (l (ω σ)) * markedCoefficientAction M σ)
      (diagramCocharacters ((markedDiagramEquiv C.realization (ω σ)).asIso.hom).val).toAffineEquiv
    simpa only [mul_one] using composeAutomorphismComparisons X.sc _ _ _ _ hd hc
  have hs' (σ : Gal(K/F)) : AutomorphismComparison X.ad (a' σ) (h' σ) := by
    have hd := markedPinnedAction_comparison X.ad X.ad_points C' hQ' (ω' σ) hword'
    have hc := (splitCoefficientComparison X.ad X.ad_points hword' X.ad_bruhat X.typeQuotient.normal hv σ).1
    change AutomorphismComparison X.ad
      (markedPinnedAction (K := K) C' (l' (ω' σ)) * markedCoefficientAction M' σ)
      (diagramCocharacters ((markedDiagramEquiv C'.realization (ω' σ)).asIso.hom).val).toAffineEquiv
    simpa only [mul_one] using composeAutomorphismComparisons X.ad _ _ _ _ hd hc
  obtain ⟨β, hβ⟩ := typeQuotientOfAutomorphismAction X.ad X.typeQuotient
    X.ad_points.2.2.2.2.2.2.2.2 a' h' hs'
  refine ⟨a, a', β, markedPinnedCoefficientAction_apply C l ω,
    markedPinnedCoefficientAction_apply C' l' ω', fun σ => ⟨hs σ, hs' σ, (hβ σ).1, (hβ σ).2, ?_⟩⟩
  intro hτ z
  exact e6Diagram_inverts_alcoveStabilizer b' hNum p' X.ad.geometry (τ' σ) hτ z (β σ z) ((hβ σ).2 z)

/-- The marked split affine Bruhat comparison, including scalar extension
and the pinned coefficient action for a splitting field of outer E₆. -/
theorem splitAffineBruhatComparison : SplitAffineBruhatComparison := by
  intro F _ _ _ _ D E M M' c n b b' hn hd he hsc had
  obtain ⟨p, p', e, X, he, hp, h⟩ := splitBruhatAtUnramifiedLevels F c n b b' hn hd he hsc had
  refine ⟨p, p', e, X, he, hp, ?_⟩
  intro K _ _ _ _ _ _ _ hv
  obtain ⟨Y, hsc, had, ht, hc, hw, hw'⟩ := h K hv
  refine ⟨Y, hsc, had, ht, hc, ?_⟩
  intro hSix C C' l l' Q Q'
  subst n
  exact splitOuterE6CoefficientActions Y hv b b' he C C' (l := l) (l' := l') (Q := Q) (Q' := Q') hw hw'

end SplitComparison

section RamifiedLevelPoints

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint pinnedMarkedPoint
  coordinatePointEquiv integralTestAlgebra extendedTestAlgebra quadraticIntegralAlgebra
  conjugateTestAlgebra pinnedSchemeAction pinnedDiagram evaluateGroundTensor)
open Specs.AdjointCocharacters (coordinateHopf)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open scoped CategoryTheory.MonObj TensorProduct
open private pinnedSchemeAction_one quadraticGalois coordinatePointEquiv_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

open private groundSectionsEquiv groundSectionsEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

attribute [local instance] integerAlgebra

universe u

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D}

/-- The marked map on the descended coefficient points is an injective
homomorphism. Its image in the model over the compositum is exactly the
fixed points of the pinned diagram with its actual field involution. -/
theorem ramifiedLevelPointEmbedding (R : RamifiedReference F L M)
    (σ : Gal(L/F)) (σK : Gal(K/k)) (deg : Module.finrank F L = 2) (hne : σ ≠ 1)
    (T : (L ⊗[F] k) ≃ₐ[F] K) (f : L →ₐ[F] K)
    (hL : ∀ x, T (x ⊗ₜ[F] (1 : k)) = f x)
    (hk : ∀ x, T ((1 : L) ⊗ₜ[F] x) = algebraMap k K x)
    (hσ : ∀ x, σK (f x) = f (σ x)) :
    ∃ j : GroupPoints R.descent.group.val (CommAlgCat.of F k) →* FieldPoints M K,
      Function.Injective j ∧
      (∀ g, j g = ramifiedPoint R f (IsScalarTower.toAlgHom F k K) g) ∧
      ∀ v : GroupPoints R.fibre.realization.pinned.pair.G.val (CommAlgCat.of F K),
        markedFibrePoint R.fibre (CommAlgCat.of F K) v ∈ j.range ↔
        pinnedCoefficientPoint R.fibre (R.pin (R.outer σ))
          (σK.restrictScalars F : K ≃ₐ[F] K) v = markedFibrePoint R.fibre (CommAlgCat.of F K) v := by
  let S := CommAlgCat.of F k
  let U := (extendedTestAlgebra F L).obj S
  let W := CommAlgCat.of F K
  let g := IsScalarTower.toAlgHom F k K
  let c : U ≅ W :=
    { hom := CommAlgCat.ofHom T.toAlgHom
      inv := CommAlgCat.ofHom T.symm.toAlgHom
      hom_inv_id := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        exact T.symm_apply_apply x
      inv_hom_id := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        exact T.apply_symm_apply x }
  let E := (integralTestAlgebra F).mapIso c
  let a := ((integralPointFunctor M.group).mapIso E).groupIsoToMulEquiv
  let b := (((groupPointsFunctor F).obj R.fibre.realization.pinned.pair.G.val).mapIso c).groupIsoToMulEquiv
  have hEval (x : L) (y : k) : T (x ⊗ₜ[F] y) = f x * g y := by
    have h := T.map_mul (x ⊗ₜ[F] (1 : k)) ((1 : L) ⊗ₜ[F] y)
    change T ((x ⊗ₜ[F] (1 : k)) * ((1 : L) ⊗ₜ[F] y)) =
      T (x ⊗ₜ[F] (1 : k)) * T ((1 : L) ⊗ₜ[F] y) at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hL, hk] at h
    exact h
  have hLift : T.toAlgHom = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul x y => exact hEval x y
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨emb, hEmb, hFix⟩ :=
    ExceptionalMarkedRootDescent.pinnedMarkedPointEmbedding R.fibre R.descent.data
  let q := (coordinatePointEquiv R.descent.group S).symm
  let j : GroupPoints R.descent.group.val S →* FieldPoints M K :=
    a.toMonoidHom.comp ((emb.app S).hom.comp q.toMonoidHom)
  have hApp (x : GroupPoints R.descent.group.val S) :
      j x = ramifiedPoint R f g x := by
    have hE : E.hom = integralRingMap (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      change T.toAlgHom z = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z
      rw [hLift]
    change (integralPointFunctor M.group).map E.hom (emb.app S (q x)) = _
    rw [hE, hEmb]
    rfl
  have hRange : (j.range : Set (FieldPoints M K)) = a '' Set.range (emb.app S) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨q x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      obtain ⟨v, rfl⟩ := q.surjective x
      exact ⟨v, rfl⟩
  obtain ⟨i, hi⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison R.fibre
  have hFibre (p : GroupPoints R.fibre.realization.pinned.pair.G.val U) :
      a (markedFibrePoint R.fibre U p) = markedFibrePoint R.fibre W (b p) := by
    rw [← hi, ← hi]
    exact (ConcreteCategory.congr_hom (i.hom.naturality c.hom) p).symm
  let vσ := CommAlgCat.ofHom (σK.restrictScalars F).toAlgHom
  have hC : conjugateTestAlgebra σ S ≫ c.hom = c.hom ≫ vσ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change T (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F k) x) = σK (T x)
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hEval, hEval, map_mul, hσ]
      exact congrArg (f (σ x) * ·) (σK.commutes y).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have hP (p : GroupPoints R.fibre.realization.pinned.pair.G.val U) :
      a (markedFibrePoint R.fibre U (pinnedSchemeAction R.descent.data σ S p)) =
        pinnedCoefficientPoint R.fibre (R.pin (R.outer σ))
          (σK.restrictScalars F : K ≃ₐ[F] K) (b p) := by
    rw [hFibre]
    unfold pinnedCoefficientPoint
    change markedFibrePoint R.fibre W
        ((testSpec F).map c.hom.op ≫ (testSpec F).map (conjugateTestAlgebra σ S).op ≫ p ≫
          (pinnedDiagram R.descent.data σ).asIso.hom.group.hom.hom.hom) =
      markedFibrePoint R.fibre W ((testSpec F).map vσ.op ≫ ((testSpec F).map c.hom.op ≫ p) ≫
        (R.pin (R.outer σ)).asIso.hom.group.hom.hom.hom)
    have hsource : (testSpec F).map c.hom.op ≫ (testSpec F).map (conjugateTestAlgebra σ S).op =
        (testSpec F).map vσ.op ≫ (testSpec F).map c.hom.op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hC]
    simp only [← Category.assoc, hsource, pinnedDiagram, R.descent.outer_eq]
  refine ⟨j, a.injective.comp ((hFix S).1.comp q.injective), hApp, ?_⟩
  intro v
  obtain ⟨p, rfl⟩ := b.surjective v
  rw [← hFibre, ← hP]
  change a (markedFibrePoint R.fibre U p) ∈ (j.range : Set (FieldPoints M K)) ↔ _
  rw [hRange, a.injective.eq_iff]
  have hImg : a (markedFibrePoint R.fibre U p) ∈ a '' Set.range (emb.app S) ↔
      markedFibrePoint R.fibre U p ∈ Set.range (emb.app S) :=
    a.injective.mem_set_image
  rw [hImg, (hFix S).2]
  have hInj : Function.Injective (markedFibrePoint R.fibre U) := by
    intro x y he
    apply (i.app U).groupIsoToMulEquiv.injective
    change i.hom.app U x = i.hom.app U y
    rw [hi, hi, he]
  refine ⟨fun h => congrArg (markedFibrePoint R.fibre U) (h σ), fun h τ => ?_⟩
  rcases (quadraticGalois deg σ hne).1 τ with rfl | rfl
  · exact pinnedSchemeAction_one R.fibre R.descent.data S p
  · exact hInj h

/-- At the base field the test-algebra point map agrees with the ground
sections used to construct the ramified rational normalizer. -/
theorem ramifiedGroundPointComparison
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F L M) :
    ∃ e : (𝟙_ (SchemeOver F) ⟶ R.descent.group.val.X) ≃*
        GroupPoints R.descent.group.val (CommAlgCat.of F F),
      (∀ x, e x = CartesianMonoidalCategory.toUnit _ ≫ x) ∧
      ∀ x, ramifiedPoint R (AlgHom.id F L) (Algebra.ofId F L) (e x) =
        Specs.ExceptionalIwahoriImageComparison.pinnedGroundPoint R.fibre R.descent.data x := by
  let e : (𝟙_ (SchemeOver F) ⟶ R.descent.group.val.X) ≃*
      GroupPoints R.descent.group.val (CommAlgCat.of F F) := groundSectionsEquiv R.descent.group.val
  refine ⟨e, groundSectionsEquiv_apply R.descent.group.val, fun x => ?_⟩
  have he : e x = CartesianMonoidalCategory.toUnit _ ≫ x :=
    groundSectionsEquiv_apply R.descent.group.val x
  refine (congrArg (ramifiedPoint R (AlgHom.id F L) (Algebra.ofId F L)) he).trans ?_
  have hrid :
      (Algebra.TensorProduct.lift (AlgHom.id F L) (Algebra.ofId F L)
        (fun _ _ => Commute.all _ _)).toRingHom =
      (Algebra.TensorProduct.rid F L L).toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  unfold ramifiedPoint Specs.ExceptionalIwahoriImageComparison.pinnedGroundPoint
  change changeRingHom M.group (integralRingMap (Algebra.TensorProduct.lift
    (AlgHom.id F L) (Algebra.ofId F L) _).toRingHom) _ =
      (integralPointFunctor M.group).map (evaluateGroundTensor F L) _
  rw [hrid]
  rfl

omit [Algebra k K] [IsScalarTower F k K] in
/-- Naturality of the actual pinned point comparison in compatible
coefficient and splitting-field maps. -/
theorem ramifiedPoint_natural {k' K' : Type u} [Field k'] [Field K']
    [Algebra F k'] [Algebra F K'] (R : RamifiedReference F L M)
    (f : L →ₐ[F] K) (g : k →ₐ[F] K)
    (f' : L →ₐ[F] K') (g' : k' →ₐ[F] K')
    (s : k →ₐ[F] k') (t : K →ₐ[F] K')
    (hL : t.comp f = f') (hk : t.comp g = g'.comp s)
    (x : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    scalarPoints M t.toRingHom (ramifiedPoint R f g x) =
      ramifiedPoint R f' g' (coefficientPoints R.descent.group.val s x) := by
  let S := CommAlgCat.of F k
  let S' := CommAlgCat.of F k'
  let d := R.descent.data
  let h : S ⟶ S' := CommAlgCat.ofHom s
  let p := (coordinatePointEquiv R.descent.group S).symm x
  let y := coefficientPoints R.descent.group.val s x
  have hy : (coordinatePointEquiv R.descent.group S').symm y =
      WithConv.toConv (s.comp p.ofConv) := by
    apply (coordinatePointEquiv R.descent.group S').injective
    rw [MulEquiv.apply_symm_apply]
    change y = coordinatePointEquiv R.descent.group S' (WithConv.toConv (h.hom.comp p.ofConv))
    rw [coordinatePointEquiv_natural R.descent.group h]
    change y = (testSpec F).map h.op ≫ coordinatePointEquiv R.descent.group S p
    rw [MulEquiv.apply_symm_apply]
    rfl
  let l := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  let l' := Algebra.TensorProduct.lift f' g' (fun _ _ => Commute.all _ _)
  let e := (quadraticIntegralAlgebra F L).map h
  let r := integralRingMap l.toRingHom
  let r' := integralRingMap l'.toRingHom
  let a := integralRingMap t.toRingHom
  have he : r ≫ a = e ≫ r' := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change t (l z) = l' (Algebra.TensorProduct.map (AlgHom.id F L) s z)
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [l, l', Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        map_mul]
      exact congrArg₂ (· * ·) (DFunLike.congr_fun hL u) (DFunLike.congr_fun hk v)
    | add u v hu hv => simp only [map_add, hu, hv]
  obtain ⟨emb, hEmb, _⟩ :=
    ExceptionalMarkedRootDescent.pinnedMarkedPointEmbedding R.fibre d
  have hm :
      (integralPointFunctor M.group).map e (emb.app S p) =
        emb.app S' (WithConv.toConv (s.comp p.ofConv)) :=
    (ConcreteCategory.congr_hom (emb.naturality h) p).symm
  change (integralPointFunctor M.group).map a ((integralPointFunctor M.group).map r
      (pinnedMarkedPoint R.fibre d S p)) =
    (integralPointFunctor M.group).map r'
      (pinnedMarkedPoint R.fibre d S' ((coordinatePointEquiv R.descent.group S').symm y))
  rw [hy, ← hEmb, ← hEmb, ← hm]
  let Φ := integralPointFunctor M.group
  have hmap : Φ.map r ≫ Φ.map a = Φ.map e ≫ Φ.map r' := by
    rw [← Φ.map_comp, ← Φ.map_comp, he]
  exact ConcreteCategory.congr_hom hmap (emb.app S p)

end RamifiedLevelPoints

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra)
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus)
open scoped CategoryTheory.MonObj
attribute [local instance] integerAlgebra

universe u

section LocalIwahoriEquiv

variable {G H W : Type u} [Group G] [Group H] [Group W]
  {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} {j : H →* FieldPoints M K}

private def subgroupComapEquiv (e : G ≃* H) (N : Subgroup H) : N.comap e.toMonoidHom ≃* N where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by change e (e.symm x) ∈ N; rw [e.apply_symm_apply]; exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e x.val y.val)

private theorem subgroupComapEquiv_surjective (e : G ≃* H) (N : Subgroup H) :
    Function.Surjective (subgroupComapEquiv e N) := (subgroupComapEquiv e N).surjective

set_option backward.isDefEq.respectTransparency false in
private def comapMarkedLocalNormalizer (N : MarkedLocalNormalizer K j W) (e : G ≃* H) :
    MarkedLocalNormalizer K (j.comp e.toMonoidHom) W where
  torus := N.torus.comap e.toMonoidHom
  normalizer := N.normalizer.comap e.toMonoidHom
  torus_le := Subgroup.comap_mono N.torus_le
  torusPoints g := N.torusPoints (e g)
  label := N.label.comp (subgroupComapEquiv e N.normalizer).toMonoidHom
  labelKernel n := N.labelKernel (subgroupComapEquiv e N.normalizer n)
  translation := N.translation.comp (subgroupComapEquiv e N.torus).toMonoidHom
  characterLog t v h x := N.characterLog (subgroupComapEquiv e N.torus t) v h x
  word := N.word
  lift w := (subgroupComapEquiv e N.normalizer).symm (N.lift w)
  lift_label w := by
    change N.label (subgroupComapEquiv e N.normalizer ((subgroupComapEquiv e N.normalizer).symm (N.lift w))) = w
    rw [MulEquiv.apply_symm_apply, N.lift_label]
  lift_point w := by
    change j (e (e.symm (N.lift w))) = _
    rw [e.apply_symm_apply, N.lift_point]

set_option backward.isDefEq.respectTransparency false in
private theorem comapMarkedLocalNormalizer_torusPart (N : MarkedLocalNormalizer K j W) (e : G ≃* H)
    (n : (comapMarkedLocalNormalizer N e).normalizer) :
    subgroupComapEquiv e N.torus ((comapMarkedLocalNormalizer N e).torusPart n) =
      N.torusPart (subgroupComapEquiv e N.normalizer n) := by
  apply Subtype.ext
  change e ((n : G) * (e.symm (N.lift (N.label (subgroupComapEquiv e N.normalizer n))) : G)⁻¹) = _
  rw [map_mul, map_inv, e.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def comapLocalIwahori (P : LocalIwahori j W) (e : G ≃* H) :
    LocalIwahori (j.comp e.toMonoidHom) W where
  normalizer := comapMarkedLocalNormalizer P.normalizer e
  residueFibre := P.residueFibre
  residueBorel := P.residueBorel
  borel_eq := P.borel_eq
  intersection := by
    change P.iwahori.comap e.toMonoidHom ⊓ P.normalizer.normalizer.comap e.toMonoidHom = _
    rw [← Subgroup.comap_inf, LocalIwahori.iwahori, P.intersection, Subgroup.comap_comap]
  generation := by
    change P.iwahori.comap e.toMonoidHom ⊔ P.normalizer.normalizer.comap e.toMonoidHom = ⊤
    rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.comap_equiv_eq_map_symm', ← Subgroup.map_sup]
    rw [LocalIwahori.iwahori, P.generation, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.symm.surjective]

private theorem comapNormalizer_kernel {A : Type u} [Group A]
    (N : MarkedLocalNormalizer K j W) (e : G ≃* H)
    (a : N.normalizer →* A)
    (h : a.ker.map N.normalizer.subtype = (integralUnitTorus (K := K) M).comap j) :
    let N' := comapMarkedLocalNormalizer N e
    let a' := a.comp (subgroupComapEquiv e N.normalizer).toMonoidHom
    a'.ker.map N'.normalizer.subtype = (integralUnitTorus (K := K) M).comap (j.comp e.toMonoidHom) := by
  intro N' a'
  ext g
  have hg : j (e g) ∈ integralUnitTorus (K := K) M ↔ e g ∈ a.ker.map N.normalizer.subtype := by
    rw [h]
    rfl
  change g ∈ a'.ker.map N'.normalizer.subtype ↔ j (e g) ∈ integralUnitTorus (K := K) M
  rw [hg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨subgroupComapEquiv e N.normalizer x, hx, rfl⟩
  · rintro ⟨x, hx, hg'⟩
    exact ⟨(subgroupComapEquiv e N.normalizer).symm x, by
      change a ((subgroupComapEquiv e N.normalizer) ((subgroupComapEquiv e N.normalizer).symm x)) = 1
      rw [MulEquiv.apply_symm_apply]
      exact hx, e.injective ((e.apply_symm_apply _).trans hg')⟩

end LocalIwahoriEquiv

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Pointwise TensorProduct WithZero Classical
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots PinnedWallSigns FoldedRootDirection
  IsLongF4Doubled foldedDepthDenominator threshold)
open Specs.ExceptionalIwahoriCongruence (CellValues cellValue integralRing integralRingMap mapCellValues)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus pinnedGroundPoint)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre TransportedOrbit SimpleRootOrbit rationalOrbitParameter
  transportedLabels pinnedDiagram markedWeylWord weylWordPerm wallMatrix)
open Specs.ExceptionalFoldedRootChart (OrbitOrdering slotMap slotUnit IsTransportUnitSystem)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment fixedWeylGroup FibreNormalizer)
open ValuativeRel WithZero
attribute [local instance] integerAlgebra

universe u

section FoldedCharts

variable {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}
  {k K : Type u} [Field k] [Field K] [Algebra k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {G : Type u} [Group G] {j : G →* FieldPoints M K}

private def foldedTorusCoordinates (j : G →* FieldPoints M K) :
    Set (TorusValues D (integralRing K)) :=
  {t | (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈ j.range}

private noncomputable def foldedRootSlots (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k)) (j : G →* FieldPoints M K) :
    RootSlots (K := K) (o.negative.flatMap transportedLabels) (o.positive.flatMap transportedLabels)
      (fun a => rationalOrbitParameter k K (o.block a)) where
  torus := foldedTorusCoordinates j
  neg l := A.direction (o.negative.flatMap transportedLabels)[l]
  pos l := A.direction (o.positive.flatMap transportedLabels)[l]
  negMap l := slotMap σ (o.block (A.direction (o.negative.flatMap transportedLabels)[l])) (o.negative.flatMap transportedLabels)[l]
  posMap l := slotMap σ (o.block (A.direction (o.positive.flatMap transportedLabels)[l])) (o.positive.flatMap transportedLabels)[l]
  negUnit l := slotUnit u (o.block (A.direction (o.negative.flatMap transportedLabels)[l])) (o.negative.flatMap transportedLabels)[l]
  posUnit l := slotUnit u (o.block (A.direction (o.positive.flatMap transportedLabels)[l])) (o.positive.flatMap transportedLabels)[l]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem foldedRootSlots_values (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k)) (j : G →* FieldPoints M K)
    (t : (foldedRootSlots A o u σ j).torus) (x : ∀ a, rationalOrbitParameter k K (o.block a)) :
    (foldedRootSlots A o u σ j).coordinates t x = o.coordinates u σ t.val x := rfl

private noncomputable def foldedRootChart (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k)) (j : G →* FieldPoints M K)
    (hs : PinnedWallSigns A.roots A.basepoint (fun a => ∃ i, A.direction i = a ∧ D.base.IsPos i))
    (hj : ∀ z, cellValue M.toIntegralMarking (integralRing K) _ _ z ∈ j.range ↔
      ∃ (t : foldedTorusCoordinates j) (x : ∀ a, rationalOrbitParameter k K (o.block a)),
        o.coordinates u σ t.val x = z) :
    LocalRootChart (j := j) A.roots A.basepoint where
  direction := A.direction
  negative := o.negative.flatMap transportedLabels
  positive := o.positive.flatMap transportedLabels
  negative_enumerates := o.negative_enumerates
  positive_enumerates := o.positive_enumerates
  parameter a := rationalOrbitParameter k K (o.block a)
  parameterField _ := inferInstance
  value a := normalizedValuation (rationalOrbitParameter k K (o.block a))
  chart := foldedRootSlots A o u σ j
  neg_slots _ := rfl
  pos_slots _ := rfl
  rational z := hj z
  signs := hs

omit [Algebra k K] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem foldedBlock_singleton_iff (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (nodup : ∀ a, (transportedLabels (o.block a)).Nodup) (a : FoldedRootDirection) :
    (o.block a).1.2 = none ↔ IsLongF4Doubled a.val := by
  classical
  rcases hb : o.block a with ⟨⟨b, c⟩, w⟩
  let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
  have hfirst : A.direction (p b.val) = a :=
    (o.fibre a _).1 (by cases c <;> simp [hb, transportedLabels, SimpleRootOrbit.roots, p])
  have orbit (z : D.I) : z ∈ transportedLabels (o.block a) ↔ z = p b.val ∨ z = τ.val.indexEquiv (p b.val) := by
    rw [o.fibre, ← hfirst, eq_comm, A.orbits]
  rw [← hfirst, A.long]
  cases c with
  | none =>
    have hm := (orbit (τ.val.indexEquiv (p b.val))).2 (Or.inr rfl)
    simpa [hb, transportedLabels, SimpleRootOrbit.roots, p] using hm
  | some c =>
    have hm : p c.val ∈ transportedLabels (o.block a) := by
      simp [hb, transportedLabels, SimpleRootOrbit.roots, p]
    have hne : p b.val ≠ p c.val := by
      simpa [hb, transportedLabels, SimpleRootOrbit.roots, p] using nodup a
    have hsecond : p c.val = τ.val.indexEquiv (p b.val) :=
      ((orbit _).mp hm).resolve_left (Ne.symm hne)
    have hfixed : τ.val.indexEquiv (p b.val) ≠ p b.val := by rwa [← hsecond, ne_comm]
    simp [hfixed]

private noncomputable def foldedDepthExponent (a : FoldedRootDirection) : ℕ :=
  if IsLongF4Doubled a.val then 2 else 1

private theorem foldedDepthExponent_pos (a : FoldedRootDirection) : 0 < foldedDepthExponent a := by
  unfold foldedDepthExponent
  split <;> decide

private theorem foldedDepthExponent_denominator (a : FoldedRootDirection) :
    (foldedDepthExponent a : ℚ) * (foldedDepthDenominator a : ℚ) = 2 := by
  unfold foldedDepthExponent foldedDepthDenominator
  split_ifs <;> norm_num

set_option backward.isDefEq.respectTransparency false in
private theorem foldedSlot_value (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (nodup : ∀ a, (transportedLabels (o.block a)).Nodup)
    (σ : Gal(K/k)) (hσ : ∀ x, normalizedValuation K (σ x) = normalizedValuation K x)
    (hr : ∀ x, normalizedValuation K (algebraMap k K x) = normalizedValuation k x ^ 2)
    (a : FoldedRootDirection) (i : D.I) (x : rationalOrbitParameter k K (o.block a)) :
    normalizedValuation K (slotMap σ (o.block a) i x) =
      normalizedValuation (rationalOrbitParameter k K (o.block a)) x ^ foldedDepthExponent a := by
  classical
  have hlong := foldedBlock_singleton_iff A o nodup a
  generalize hb : o.block a = b at hlong x ⊢
  rcases b with ⟨⟨b, c⟩, w⟩
  cases c with
  | none =>
    rw [foldedDepthExponent, ite_eq_left (hlong.1 rfl)]
    exact hr x
  | some c =>
    rw [foldedDepthExponent, ite_eq_right (fun h => Option.some_ne_none c (hlong.2 h)), pow_one]
    change normalizedValuation K ((if i = weylWordPerm (w.flatMap SimpleRootOrbit.roots) b.val
      then RingHom.id K else σ.toRingHom) x) = normalizedValuation K x
    split_ifs
    · rfl
    · exact hσ x

private theorem foldedParameter_residue (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (hres : Nat.card (residue K) = Nat.card (residue k)) (a : FoldedRootDirection) :
    Nat.card (residue (rationalOrbitParameter k K (o.block a))) = Nat.card (residue k) := by
  generalize o.block a = b
  rcases b with ⟨⟨b, c⟩, w⟩
  cases c
  · rfl
  · exact hres

set_option backward.isDefEq.respectTransparency false in
private theorem foldedSingletonParameter (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (nodup : ∀ a, (transportedLabels (o.block a)).Nodup) (σ : Gal(K/k))
    (a : FoldedRootDirection) (ha : IsLongF4Doubled a.val) :
    ∃ e : rationalOrbitParameter k K (o.block a) ≃+* k,
      (∀ i, slotMap σ (o.block a) i = (algebraMap k K).comp e.toRingHom) ∧
      ∀ x, normalizedValuation (rationalOrbitParameter k K (o.block a)) x =
        normalizedValuation k (e x) := by
  have hn := (foldedBlock_singleton_iff A o nodup a).2 ha
  generalize o.block a = block at hn ⊢
  rcases block with ⟨⟨b, c⟩, w⟩
  cases c with
  | none => exact ⟨RingEquiv.refl k, fun _ => rfl, fun _ => rfl⟩
  | some c => contradiction

set_option backward.isDefEq.respectTransparency false in
private theorem foldedPairedParameter (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (nodup : ∀ a, (transportedLabels (o.block a)).Nodup) (σ : Gal(K/k))
    (a : FoldedRootDirection) (ha : ¬IsLongF4Doubled a.val) :
    ∃ i : D.I, A.direction i = a ∧
    ∃ e : rationalOrbitParameter k K (o.block a) ≃+* K,
      slotMap σ (o.block a) i = e.toRingHom ∧
      slotMap σ (o.block a) (τ.val.indexEquiv i) = σ.toRingHom.comp e.toRingHom ∧
      ∀ x, normalizedValuation (rationalOrbitParameter k K (o.block a)) x = normalizedValuation K (e x) := by
  have hn := (not_congr (foldedBlock_singleton_iff A o nodup a)).2 ha
  have hmem i := o.fibre a i
  have hnd := nodup a
  generalize o.block a = block at hn hmem hnd ⊢
  rcases block with ⟨⟨b, c⟩, w⟩
  cases c with
  | none => contradiction
  | some c =>
    let i := weylWordPerm (w.flatMap SimpleRootOrbit.roots) b.val
    have hi := (hmem i).1 (by simp [i, transportedLabels, SimpleRootOrbit.roots])
    have hne : τ.val.indexEquiv i ≠ i := fun h => ha (hi ▸ (A.long i).2 h)
    refine ⟨i, hi, RingEquiv.refl K, ?_, ?_, fun _ => rfl⟩
    · change (if i = i then RingHom.id K else σ.toRingHom) = _
      rw [ite_eq_left rfl]
      rfl
    · change (if τ.val.indexEquiv i = i then RingHom.id K else σ.toRingHom) = _
      rw [ite_eq_right hne]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem foldedChart_usesSlot (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k))
    (hs : PinnedWallSigns A.roots A.basepoint (fun a => ∃ i, A.direction i = a ∧ D.base.IsPos i))
    (hj : ∀ z, cellValue M.toIntegralMarking (integralRing K) _ _ z ∈ j.range ↔
      ∃ (t : foldedTorusCoordinates j) (x : ∀ a, rationalOrbitParameter k K (o.block a)),
        o.coordinates u σ t.val x = z)
    (i : D.I) (a : FoldedRootDirection) (hi : A.direction i = a)
    (e : rationalOrbitParameter k K (o.block a) →+* K)
    (he : slotMap σ (o.block a) i = e) :
    (foldedRootChart A o u σ j hs hj).UsesSlot i a e := by
  subst a
  refine ⟨rfl, ?_, ?_⟩
  · intro l hl x hi
    change (o.negative.flatMap transportedLabels)[l] = i at hi
    subst i
    have hh : hl = rfl := Subsingleton.elim _ _
    cases hh
    change slotMap σ (o.block _) _ x = e x
    exact DFunLike.congr_fun he x
  · intro l hl x hi
    change (o.positive.flatMap transportedLabels)[l] = i at hi
    subst i
    have hh : hl = rfl := Subsingleton.elim _ _
    cases hh
    change slotMap σ (o.block _) _ x = e x
    exact DFunLike.congr_fun he x

end FoldedCharts

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite Topology
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat (FieldPoints)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalIwahoriImageComparison (pinnedGroundPoint markedBorelReduction)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint integralTestAlgebra)
open Specs.ExceptionalIwahoriCongruence (integralRing changeRing pointAlgebraEquiv markedPointTopology
  affinePointTopology)
open private pointAlgebraEquiv_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

section FoldedTopology

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}

private theorem continuous_of_normalizedValuation (σ : K →+* K)
    (hσ : ∀ x, normalizedValuation K (σ x) = normalizedValuation K x) : Continuous σ := by
  apply continuous_of_tendsto_nhds_zero σ.toAddMonoidHom
  refine (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.mpr ?_
  intro c _
  have hv (x : K) : ValuativeRel.valuation K (σ x) = ValuativeRel.valuation K x :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective (hσ x)
  filter_upwards [(IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := c) trivial] with x hx
  change ValuativeRel.valuation K (σ x) < c
  rwa [hv]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
/-- A pinned action on the generic fibre is continuous in the marked
point topology. Evaluate it at the universal point of the affine chart
and use the tensor evaluation formula for its coordinates. -/
private theorem continuous_pinnedPointAction (C : MarkedFibre M k)
    (f : Aut C.realization.pinned) (σ : Gal(K/k)) (hσ : Continuous σ)
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (.op B) ≅ M.group.X)
    (E : (groupPointsFunctor k).obj C.realization.pinned.pair.G.val ≅
      integralTestAlgebra k ⋙ integralPointFunctor M.group) :
    let := markedPointTopology B iso K
    let R := CommAlgCat.of k K
    let e := (E.app R).groupIsoToMulEquiv
    Continuous (fun g : FieldPoints M K => (show FieldPoints M K from
      e ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      e.symm g ≫ f.asIso.hom.group.hom.hom.hom))) := by
  intro top R e
  let := top
  let T := integralTestAlgebra k
  let U := (B : Type u) ⊗[ℤ] k
  let S : TestAlgebra k := CommAlgCat.of k ((B : Type u) ⊗[ℤ] k)
  let left : (B : Type u) →ₐ[ℤ] U := Algebra.TensorProduct.includeLeft
  let : Algebra Integers.{u} (T.obj S) := (T.obj S).algebra
  let : Algebra Integers.{u} (T.obj R) := (T.obj R).algebra
  let : Algebra Integers.{u} B := B.algebra
  let AlgPoint (A : IntegralAlgebra.{u}) := @AlgHom Integers.{u} B A _ _ _ B.algebra A.algebra
  let q : AlgPoint (T.obj S) :=
    { toRingHom := left.toRingHom
      commutes' := fun n => by
        have h : @algebraMap Integers.{u} B _ _ B.algebra n = (n.down : B) := by
          exact DFunLike.congr_fun (RingHom.ext_int ((@algebraMap Integers.{u} B _ _ B.algebra).comp ULift.ringEquiv.symm.toRingHom)
            (Int.castRingHom B)) n.down
        change left (@algebraMap Integers.{u} B _ _ B.algebra n) = (n.down : U)
        rw [h, map_intCast] }
  let p (A : TestAlgebra k) := pointAlgebraEquiv B iso (T.obj A)
  let Φ (A : TestAlgebra k) :
      GroupPoints C.realization.pinned.pair.G.val A ≃* IntegralPoints M.group (T.obj A) :=
    (E.app A).groupIsoToMulEquiv
  let s := f.asIso.hom.group.hom.hom.hom
  let act (A : TestAlgebra k) (g : IntegralPoints M.group (T.obj A)) := Φ A ((Φ A).symm g ≫ s)
  have hnat {A B' : TestAlgebra k} (h : A ⟶ B') (g : IntegralPoints M.group (T.obj A)) :
      changeRing (T.map h) (act A g) = act B' (changeRing (T.map h) g) := by
    have he (x : GroupPoints C.realization.pinned.pair.G.val A) :
        changeRing (T.map h) (Φ A x) = Φ B' ((testSpec k).map h.op ≫ x) :=
      (ConcreteCategory.congr_hom (E.hom.naturality h) x).symm
    have hg : (Φ B').symm (changeRing (T.map h) g) = (testSpec k).map h.op ≫ (Φ A).symm g := by
      apply (Φ B').injective
      rw [MulEquiv.apply_symm_apply, ← he, MulEquiv.apply_symm_apply]
    change changeRing (T.map h) (Φ A ((Φ A).symm g ≫ s)) =
      Φ B' ((Φ B').symm (changeRing (T.map h) g) ≫ s)
    rw [he, hg, Category.assoc]
  have hcoef (g : IntegralPoints M.group (T.obj R)) :
      changeRing (T.map (CommAlgCat.ofHom σ.toAlgHom)) (act R g) =
      e ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ e.symm g ≫ s) := by
    change changeRing (T.map (CommAlgCat.ofHom σ.toAlgHom)) (Φ R ((Φ R).symm g ≫ s)) = _
    exact (ConcreteCategory.congr_hom (C := GrpCat.{u})
      (E.hom.naturality (CommAlgCat.ofHom σ.toAlgHom))
        (show GroupPoints C.realization.pinned.pair.G.val R from (Φ R).symm g ≫ s)).symm
  let α := (p S).symm (act S (p S q))
  let fₖ : k →ₐ[ℤ] K :=
    { toRingHom := algebraMap k K, commutes' n := map_intCast (algebraMap k K) n }
  let ev (x : AlgPoint (T.obj R)) : U →ₐ[ℤ] K :=
    Algebra.TensorProduct.lift
      ({ toRingHom := x.toRingHom, commutes' := fun n => map_intCast x n } : (B : Type u) →ₐ[ℤ] K)
      fₖ (fun _ _ => Commute.all _ _)
  let evₖ (x : AlgPoint (T.obj R)) : S ⟶ R :=
    CommAlgCat.ofHom { toRingHom := (ev x).toRingHom
                       commutes' y := by
                         change ev x (1 ⊗ₜ[ℤ] y) = _
                         rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
                         rfl }
  have hEval_q (x : AlgPoint (T.obj R)) : (T.map (evₖ x)).hom.comp q = x := by
    apply AlgHom.ext
    intro z
    change ev x (z ⊗ₜ[ℤ] (1 : k)) = x z
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hAct (x : AlgPoint (T.obj R)) : act R (p R x) = p R ((T.map (evₖ x)).hom.comp α) := by
    let h := T.map (evₖ x)
    have hq : changeRing h (p S q) = p R x :=
      (pointAlgebraEquiv_natural B iso h q).trans (congrArg (p R) (hEval_q x))
    calc
      act R (p R x) = act R (changeRing h (p S q)) := congrArg (act R) hq.symm
      _ = changeRing h (act S (p S q)) := (hnat (evₖ x) (p S q)).symm
      _ = changeRing h (p S α) := congrArg (changeRing h) ((p S).apply_symm_apply _).symm
      _ = p R (h.hom.comp α) := pointAlgebraEquiv_natural B iso h α
  let P := pointAlgebraEquiv B iso (integralRing K)
  let : TopologicalSpace (AlgPoint (T.obj R)) :=
    @affinePointTopology Integers.{u} B K _ _ _ B.algebra (T.obj R).algebra _
  have hp : IsEmbedding P.symm := ⟨⟨rfl⟩, P.symm.injective⟩
  apply hp.isInducing.continuous_iff.mpr
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  have h_eval (a : U) : Continuous (fun g => ev (P.symm g) a) := by
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      have hx : Continuous (fun g => P.symm g x) :=
        (continuous_apply x).comp (continuous_induced_dom.comp hp.continuous)
      have he (g : FieldPoints M K) : ev (P.symm g) (x ⊗ₜ[ℤ] y) = P.symm g x * fₖ y :=
        by
          unfold ev
          rw [Algebra.TensorProduct.lift_tmul]
          rfl
      simp only [he]
      exact hx.mul continuous_const
    | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy
  convert hσ.comp (h_eval (α b)) using 1
  funext g
  congr 1
  change (P.symm (e ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ e.symm g ≫ s))) b = _
  rw [← hcoef]
  have he := hAct (P.symm g)
  change act R (P (P.symm g)) = P _ at he
  rw [P.apply_symm_apply] at he
  rw [he, pointAlgebraEquiv_natural]
  exact congrArg (fun q => q b) (P.symm_apply_apply _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
private theorem foldedCompactOpen [FiniteDimensional k K] [IsGalois k K]
    (C : MarkedFibre M k) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {H : AffineAlgebraicGroup k} {B₀ T₀ : ClosedSubgroup H.val}
    (d : PinnedTwist K C.realization.attached l B₀ T₀) (σ : Gal(K/k))
    (deg : Module.finrank k K = 2) (hne : σ ≠ 1) (hσ : Continuous σ)
    {G W : Type u} [Group G] [Group W] (e : G ≃* (𝟙_ (SchemeOver k) ⟶ H.val.X))
    (j : (𝟙_ (SchemeOver k) ⟶ H.val.X) →* FieldPoints M K) (P : LocalIwahori j W)
    (hj : ∀ g, j g = pinnedGroundPoint C d g)
    (B : IntegralAlgebra.{u}) [ft : Algebra.FiniteType Integers.{u} B]
    (iso : integralSpec.obj (.op B) ≅ M.group.X) :
    letI : TopologicalSpace G := TopologicalSpace.induced (j.comp e.toMonoidHom) (markedPointTopology B iso K)
    IsCompact ((comapLocalIwahori P e).iwahori : Set G) ∧ IsOpen ((comapLocalIwahori P e).iwahori : Set G) := by
  let := markedPointTopology B iso K
  let j' := j.comp e.toMonoidHom
  let := TopologicalSpace.induced j' (markedPointTopology B iso K)
  let jInd : IsInducing j' := ⟨rfl⟩
  let I := markedBorelReduction M.group P.residueBorel
  let R := CommAlgCat.of k K
  obtain ⟨E, hE⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  let v := (E.app R).groupIsoToMulEquiv
  let s := (l (d.outer σ)).asIso.hom.group.hom.hom.hom
  let act (x : FieldPoints M K) : FieldPoints M K :=
    v ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v.symm x ≫ s)
  have hcont : Continuous act := continuous_pinnedPointAction C (l (d.outer σ)) σ hσ B iso E
  obtain ⟨j₁, _, hj₁, _, _, hFixed⟩ :=
    ExceptionalIwahoriImageComparison.pinnedGroundPointComparison C d σ deg hne
  have hj_eq : j = j₁ := MonoidHom.ext fun g => (hj g).trans (hj₁ g).symm
  have range_eq : Set.range j' = {x | act x = x} := by
    ext x
    obtain ⟨y, rfl⟩ := v.surjective x
    change (∃ x : G, j (e x) = v y) ↔ _
    have hRange : (∃ x : G, j (e x) = v y) ↔ v y ∈ j₁.range := by
      rw [← hj_eq]
      exact ⟨fun ⟨x, h⟩ => ⟨e x, h⟩, fun ⟨x, h⟩ => ⟨e.symm x, by rwa [e.apply_symm_apply]⟩⟩
    rw [hRange]
    set f := v y with hf
    have hf' : f = markedFibrePoint C R y := hE R y
    rw [show f ∈ j₁.range ↔ _ from hf'.symm ▸ hFixed y]
    change _ ↔ v ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ v.symm (v y) ≫ s) = v y
    rw [MulEquiv.symm_apply_apply, v.injective.eq_iff]
  obtain ⟨_, hO, hF⟩ := ExceptionalIwahoriCongruence.compactOpenLocalModel M.toIntegralMarking B iso K P.residueBorel
  obtain ⟨hC, _⟩ := hF act hcont
  change IsCompact (j' ⁻¹' (I : Set (FieldPoints M K))) ∧ IsOpen (j' ⁻¹' (I : Set (FieldPoints M K)))
  refine ⟨jInd.isCompact_iff.mpr ?_, hO.preimage jInd.continuous⟩
  rw [Set.image_preimage_eq_inter_range, range_eq]
  have h := hC.image continuous_subtype_val
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe] at h
  exact h

end FoldedTopology

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Pointwise TensorProduct WithZero Classical
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots AlcoveGeometry PinnedWallSigns FoldedRootDirection
  IsLongF4Doubled foldedDepthDenominator threshold e6Partner)
open Specs.ExceptionalIwahoriCongruence (CellValues cellValue integralRing markedPointTopology)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus pinnedGroundPoint)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation ramificationIndex)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre TransportedOrbit SimpleRootOrbit rationalOrbitParameter
  transportedLabels pinnedDiagram markedWeylWord weylWordPerm wallMatrix)
open Specs.ExceptionalFoldedRootChart (OrbitOrdering slotMap slotUnit IsTransportUnitSystem)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment fixedWeylGroup FibreNormalizer markedDiagramEquiv)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.PinnedPairDescent (DescendedPair)
open Specs.SchemeDerivedGroup (FactorsThrough)
open Specs.IntegralRootRelations (upper diagonal)
open ValuativeRel WithZero
attribute [local instance] integerAlgebra

open private weylWord_index from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private quadraticGalois from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

universe u

section FoldedLocal

variable {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}
  {k K : Type u} [Field k] [Field K] [Algebra k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [Algebra k K] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem transportedLabels_length (A : FoldedApartment τ) (o : OrbitOrdering A.direction)
    (a : FoldedRootDirection) (hnd : (transportedLabels (o.block a)).Nodup) :
    (transportedLabels (o.block a)).length =
      if ∃ i j : D.I, i ≠ j ∧ A.direction i = a ∧ A.direction j = a then 2 else 1 := by
  classical
  have hmem i := o.fibre a i
  generalize o.block a = b at hnd hmem ⊢
  rcases b with ⟨⟨i, j⟩, l⟩
  let p := weylWordPerm (l.flatMap SimpleRootOrbit.roots)
  cases j with
  | none =>
    change [p i.val].length = _
    have hu (z : D.I) (hz : A.direction z = a) : z = p i.val :=
      List.mem_singleton.mp ((hmem z).2 hz)
    rw [ite_eq_right (by rintro ⟨x, y, ne, hx, hy⟩; exact ne ((hu x hx).trans (hu y hy).symm))]
    rfl
  | some j =>
    change [p i.val, p j.val].length = _
    have nd : [p i.val, p j.val].Nodup := hnd
    rw [ite_eq_left ⟨p i.val, p j.val, (by simpa using nd),
      (hmem _).1 List.mem_cons_self, (hmem _).1 (by simp [transportedLabels, SimpleRootOrbit.roots, p])⟩]
    rfl

/-- A point comparison can use any presentation of the same rational
points by the indicated multiplicative equivalence with the terminal sections. -/
private structure FoldedLocalModel [FiniteDimensional k K] [IsGalois k K]
    (C : MarkedFibre M k) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {ω : Gal(K/k) →* Aut C.realization.attached.toBased} (d : DescendedPair (l := l) K ω)
    (σ : Gal(K/k)) (A : FoldedApartment τ)
    (o : OrbitOrdering A.direction) (u : TransportedOrbit D → D.I → Integers.{u}ˣ)
    {G : Type u} [Group G] (e : G ≃* (𝟙_ (SchemeOver k) ⟶ d.group.val.X)) where
  terminalPoint : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* FieldPoints M K
  point_eq (g) : terminalPoint g = pinnedGroundPoint C d.data g
  terminalIwahori : LocalIwahori terminalPoint (fixedWeylGroup D τ)
  comparison : LocalComparison (j := terminalPoint.comp e.toMonoidHom)
    (Wf := fixedWeylGroup D τ) A.roots A.basepoint
  local_eq : comparison.localIwahori = comapLocalIwahori terminalIwahori e
  normalizer (g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X) :
    g ∈ terminalIwahori.normalizer.normalizer ↔ Normalizes d.torus.inclusion g
  torus (g : 𝟙_ (SchemeOver k) ⟶ d.group.val.X) :
    g ∈ terminalIwahori.normalizer.torus ↔ FactorsThrough d.torus g
  words (w) (i) (hi : i ∈ terminalIwahori.normalizer.word w) : i ∈ D.base.support
  finite_labels : comparison.FiniteLabels
    (fixedWeylGroup D τ).subtype
  directions : comparison.chart.direction = A.direction
  chart_eq : ∃ hs hj, comparison.chart = foldedRootChart A o u σ (terminalPoint.comp e.toMonoidHom) hs hj
  singleton (i : D.I) (h : τ.val.indexEquiv i = i) :
    ∃ v : comparison.chart.parameter (A.direction i) ≃+* k,
      comparison.chart.UsesSlot i (A.direction i) ((algebraMap k K).comp v.toRingHom) ∧
      ∀ x, comparison.chart.value (A.direction i) x = normalizedValuation k (v x)
  pair (a : FoldedRootDirection) (h : ¬IsLongF4Doubled a.val) :
    ∃ i : D.I, A.direction i = a ∧
    ∃ v : comparison.chart.parameter a ≃+* K,
      comparison.chart.UsesSlot i a v.toRingHom ∧
      comparison.chart.UsesSlot (τ.val.indexEquiv i)
        a (σ.toRingHom.comp v.toRingHom) ∧
      ∀ x, comparison.chart.value a x = normalizedValuation K (v x)
  affine (n : comparison.N) (x : invariantApartment D τ) :
    let N := comparison.localIwahori.normalizer
    (comparison.affine n x).val =
      (N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
        ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)
  translations :
    let N := comparison.localIwahori.normalizer
    Set.range (fun t : N.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation t).toAdd) =
      (invariantApartment D τ).subtype ''
        (A.roots.corootLattice : Set _)
  range : comparison.affine.range = A.roots.affineWeylGroup
  bruhat : comparison.Bruhat (Nat.card (residue k))
  typeQuotient : comparison.TypeQuotient

variable [FiniteDimensional k K] [IsGalois k K] [ValuativeExtension k K]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
private theorem foldedBruhatOfPinning (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    (hQ : SplitSequence C.realization.pinned C.realization.attached l Q)
    {ω : Gal(K/k) →* Aut C.realization.attached.toBased} (d : DescendedPair (l := l) K ω)
    (σ : Gal(K/k)) (deg : Module.finrank k K = 2) (hne : σ ≠ 1)
    (hram : 1 < ramificationIndex k K)
    (b : Fin 6 ≃ D.base.support) (hNum : ExceptionalNumbering D 6 b)
    (hIsogeny : D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤) :
    let τ := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
    (∀ i, τ.val.indexEquiv (b i) = b (e6Partner i)) →
    ∀ (A : FoldedApartment τ) (o : FoldedOrdering A)
      (u : TransportedOrbit D → D.I → Integers.{u}ˣ), IsTransportUnitSystem M.toIntegralMarking u →
    PinnedWallSigns A.roots A.basepoint (fun a => ∃ i, A.direction i = a ∧ D.base.IsPos i) →
    AlcoveGeometry A.roots A.basepoint → A.roots.ReflectionClosed → A.roots.ReducedDirections →
    (∀ a : A.roots.SimpleWall A.basepoint, ∃! x, IsAlcoveVertex A.roots A.basepoint a x) →
    ∀ {G : Type u} [Group G] (e : G ≃* (𝟙_ (SchemeOver k) ⟶ d.group.val.X)),
    (∀ (j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* FieldPoints M K)
      (P : LocalIwahori j (fixedWeylGroup D τ)),
      (∀ g, j g = pinnedGroundPoint C d.data g) →
      ∀ (B : IntegralAlgebra.{u}) [Algebra.FiniteType Integers.{u} B] (i : integralSpec.obj (.op B) ≅ M.group.X),
        letI : TopologicalSpace G := TopologicalSpace.induced (j.comp e.toMonoidHom) (markedPointTopology B i K)
        IsCompact ((comapLocalIwahori P e).iwahori : Set G) ∧ IsOpen ((comapLocalIwahori P e).iwahori : Set G)) →
    Nonempty (FoldedLocalModel C d σ A (FoldedOrdering.order o) u e) := by
  classical
  intro τ hτ A o u hu hs hgeo href hred hvertices G _ e hcompact
  let _ := D.finiteRoots
  let _ : Fintype D.base.support := Fintype.ofFinite _
  let _ : Finite FoldedRootDirection := Finite.of_surjective A.direction A.surjective
  let _ : Fintype FoldedRootDirection := Fintype.ofFinite _
  let W := fixedWeylGroup D τ
  let V := invariantApartment D τ
  let B := A.roots
  let p := A.basepoint
  let l₀ := (FoldedOrdering.order o).negative.flatMap transportedLabels
  let l₁ := (FoldedOrdering.order o).positive.flatMap transportedLabels
  obtain ⟨hInv, hPos, hSym⟩ := e6LocalRootSymmetries D b τ hNum hτ
  have hMatch := foldedSimpleOrbitMatches C hQ d σ A hInv hSym
  have hBlock (a : FoldedRootDirection) : ((FoldedOrdering.order o).block a).1.Matches C (pinnedDiagram d.data σ) ∧
      ∀ v ∈ ((FoldedOrdering.order o).block a).2, v.Matches C (pinnedDiagram d.data σ) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := (FoldedOrdering.simple o) a
      rw [hi]
      exact hMatch i
    · intro v hv
      obtain ⟨i, rfl⟩ := (FoldedOrdering.word o) a v hv
      exact hMatch i
  obtain ⟨basis, j, P, FN, action, hj, hJ, hN, hT, hF, hWord, hLabel, hKer, hAff, hTr, hRange⟩ :=
    foldedIwahoriOfE6Pinning C hQ d σ deg hne hram b hNum hIsogeny hτ A o hBlock
  obtain ⟨_, hv, hRes⟩ := ExceptionalLocalRootCoordinates.ramifiedQuadratic k K deg hram
  have hres : Nat.card (residue K) = Nat.card (residue k) :=
    (Nat.card_congr (Equiv.ofBijective _ hRes)).symm
  have hσInv : Function.Involutive σ := fun z =>
    congrArg (fun g : Gal(K/k) => g z) (quadraticGalois deg σ hne).2
  have hσ := ExceptionalLocalRootCoordinates.involutionPreservesValuation σ hσInv
  let j' := j.comp e.toMonoidHom
  let P' := comapLocalIwahori P e
  let eN := subgroupComapEquiv e P.normalizer.normalizer
  let a := action.comp eN.toMonoidHom
  have hAff' (n : P'.normalizer.normalizer) (x : V) :
      (a n x).val = (P'.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
        ((1 / 2 : ℚ) ⊗ₜ[ℤ] (P'.normalizer.translation (P'.normalizer.torusPart n)).toAdd) := by
    change (action (eN n) x).val = _
    rw [hAff]
    change _ + _ = _ + ((1 / 2 : ℚ) ⊗ₜ[ℤ]
      (P.normalizer.translation ((subgroupComapEquiv e P.normalizer.torus) (P'.normalizer.torusPart n))).toAdd)
    have h := comapMarkedLocalNormalizer_torusPart P.normalizer e
      (show (comapMarkedLocalNormalizer P.normalizer e).normalizer from n)
    exact congrArg (fun t : P.normalizer.torus =>
      (P.normalizer.label (eN n)).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
        ((1 / 2 : ℚ) ⊗ₜ[ℤ] (P.normalizer.translation t).toAdd)) h.symm
  have hTr' : Set.range (fun t : P'.normalizer.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ] (P'.normalizer.translation t).toAdd) =
      V.subtype '' (B.corootLattice : Set _) := by
    change Set.range ((fun t : P.normalizer.torus => (1 / 2 : ℚ) ⊗ₜ[ℤ]
      (P.normalizer.translation t).toAdd) ∘ (subgroupComapEquiv e P.normalizer.torus)) = _
    rw [Set.range_comp, (subgroupComapEquiv e P.normalizer.torus).surjective.range_eq, Set.image_univ, hTr]
  have hRange' : a.range = B.affineWeylGroup := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eN.surjective, Subgroup.map_top, hRange]
  have hRangePoint : j'.range = j.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top]
  have hRational (z : CellValues D (integralRing K) l₀ l₁) :
      cellValue M.toIntegralMarking (integralRing K) l₀ l₁ z ∈ j'.range ↔
      ∃ (t : foldedTorusCoordinates j') (x : ∀ a, rationalOrbitParameter k K ((FoldedOrdering.order o).block a)),
        (FoldedOrdering.order o).coordinates u σ t.val x = z := by
    have hMat (v : TransportedOrbit D) (hv : v ∈ (FoldedOrdering.order o).negative ++ (FoldedOrdering.order o).positive) :
        v.1.Matches C (pinnedDiagram d.data σ) ∧ ∀ w ∈ v.2, w.Matches C (pinnedDiagram d.data σ) := by
      obtain ⟨a, rfl⟩ := (FoldedOrdering.order o).ordered v hv
      exact hBlock a
    have h := ExceptionalFoldedRootChart.foldedOrderedChart C d.data σ deg hne hSym
      A.direction (FoldedOrdering.order o) hMat u hu j hJ z
    refine ((show _ ↔ cellValue M.toIntegralMarking (integralRing K) l₀ l₁ z ∈ j.range by rw [hRangePoint]).trans h).trans ?_
    constructor
    · rintro ⟨t, x, ht, rfl⟩
      exact ⟨⟨t, by change _ ∈ j'.range; rwa [hRangePoint]⟩, x, rfl⟩
    · rintro ⟨t, x, rfl⟩
      exact ⟨t, x, by have := t.property; change _ ∈ j'.range at this; rwa [hRangePoint] at this, rfl⟩
  let chart := foldedRootChart A (FoldedOrdering.order o) u σ j' hs hRational
  have hlift (w : B.affineWeylGroup) : ∃ n : P'.normalizer.normalizer, a n = w.val :=
    show w.val ∈ a.range by rw [hRange']; exact w.property
  let C₀ : LocalComparison (j := j') (Wf := W) B p :=
    { point_injective := hj.comp e.injective
      localIwahori := P'
      compact_open := hcompact j P hJ
      chart := chart
      geometry := hgeo
      coxeter := hgeo.coxeter.some
      affine := a
      kernel := comapNormalizer_kernel P.normalizer e action hKer
      lift := fun w => (hlift w).choose
      lift_label := fun w => (hlift w).choose_spec }
  let i (a : B.SimpleWall p) := a.val.1
  let m (a : B.SimpleWall p) := a.val.2
  have hwall := ExceptionalFoldedRootChart.foldedWallLifts C d.data σ deg hne hv hSym hInv
    A.direction (FoldedOrdering.order o) A.orbits A.long hBlock (FoldedOrdering.nodup o) u hu j hj hJ P.normalizer FN hF
    B A.root_value A.coroot_value action hAff
  choose ρ t n hρ hup hdiag ht hn hwallLabel using fun a : B.SimpleWall p => hwall (i a) (m a)
  let n' (w : B.SimpleWall p) := eN.symm (n w)
  have hnlabel (w : B.SimpleWall p) : C₀.affine (n' w) = (C₀.coxeter.coxeter.simple w).val := by
    rw [C₀.coxeter.simple_eq]
    change action (eN (eN.symm (n w))) = _
    rw [MulEquiv.apply_symm_apply]
    exact hwallLabel w
  let C₁ := withSimpleLifts C₀ n' hnlabel
  have hlift' (w : B.SimpleWall p) :
      (C₁.lift (C₁.coxeter.coxeter.simple w) : G) = e.symm (ρ w (wallMatrix (t w))) :=
    (congrArg Subtype.val (withSimpleLifts_apply C₀ n' hnlabel w)).trans (congrArg e.symm (hn w))
  have hcover := rootChart_covers C₁.chart A.surjective
  let ex (a : FoldedRootDirection) := foldedDepthExponent a
  have hex (a) : 0 < ex a := foldedDepthExponent_pos a
  have hex' (a) : 0 < (ex a : ℤ) := by exact_mod_cast hex a
  let _ : ∀ a, ValuativeRel (C₁.chart.parameter a) := fun a =>
    Specs.ExceptionalFoldedRootChart.parameterValuativeRel ((FoldedOrdering.order o).block a)
  let _ : ∀ a, TopologicalSpace (C₁.chart.parameter a) := fun a =>
    Specs.ExceptionalFoldedRootChart.parameterTopology ((FoldedOrdering.order o).block a)
  let _ : ∀ a, IsNonarchimedeanLocalField (C₁.chart.parameter a) := fun a =>
    Specs.ExceptionalFoldedRootChart.parameterLocalField ((FoldedOrdering.order o).block a)
  have hsv (a) (z : C₁.chart.parameter a) : C₁.chart.value a z = normalizedValuation (C₁.chart.parameter a) z := rfl
  have hvn (l : Fin l₀.length) (z : C₁.chart.parameter (C₁.chart.chart.neg l)) :
      normalizedValuation K (C₁.chart.chart.negMap l z) = C₁.chart.value (C₁.chart.chart.neg l) z ^ ex (C₁.chart.chart.neg l) :=
    foldedSlot_value A (FoldedOrdering.order o) (FoldedOrdering.nodup o) σ hσ hv _ l₀[l] z
  have hvp (l : Fin l₁.length) (z : C₁.chart.parameter (C₁.chart.chart.pos l)) :
      normalizedValuation K (C₁.chart.chart.posMap l z) = C₁.chart.value (C₁.chart.chart.pos l) z ^ ex (C₁.chart.chart.pos l) :=
    foldedSlot_value A (FoldedOrdering.order o) (FoldedOrdering.nodup o) σ hσ hv _ l₁[l] z
  have hnDepth (l : Fin l₀.length) : threshold (B.root (C₁.chart.chart.neg l) p) = 1 := by
    apply hs.threshold_negative
    rintro ⟨i, h, hi⟩
    have hneg := ((FoldedOrdering.order o).negative_enumerates.2 l₀[l]).1 (List.getElem_mem l.isLt)
    rcases (A.orbits _ _).1 h with h | h
    · exact hneg (h.symm ▸ hi)
    · exact hneg (h.symm ▸ (hPos i).2 hi)
  have hpDepth (l : Fin l₁.length) : threshold (B.root (C₁.chart.chart.pos l) p) = 0 :=
    hs.threshold_positive _ ⟨l₁[l], rfl, ((FoldedOrdering.order o).positive_enumerates.2 _).1 (List.getElem_mem l.isLt)⟩
  have hbase (g : G) : g ∈ C₁.I ↔ C₁.chart.atPoint p g :=
    iwahori_basePoint_chart C₁.localIwahori C₁.chart hcover hnDepth hpDepth
      (fun a => (ex a : ℤ)) hex' (fun l z => by simpa only [zpow_natCast] using hvn l z)
      (fun l z => by simpa only [zpow_natCast] using hvp l z) g
  let embed (x : V) : ℚ ⊗[ℤ] D.Y := (2 : ℚ) • x.val
  have hroot (x : V) (a : D.I) : (ApartmentRoots.split D.datum ℚ).root a (embed x) =
      ((ex (C₁.chart.direction a) : ℤ) : ℚ) * B.root (C₁.chart.direction a) x := by
    change (ApartmentRoots.split D.datum ℚ).root a ((2 : ℚ) • x.val) =
      ((ex (A.direction a) : ℤ) : ℚ) * A.roots.root (A.direction a) x
    rw [A.root_value, Int.cast_natCast, ← mul_assoc, foldedDepthExponent_denominator, map_smul]
    rfl
  have haff (n : C₁.N) (x : V) :
      embed (C₁.affine n x) = (C₁.localIwahori.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y (embed x) +
        ((1 : ℚ) ⊗ₜ[ℤ] (C₁.localIwahori.normalizer.translation (C₁.localIwahori.normalizer.torusPart n)).toAdd) := by
    change (2 : ℚ) • (a n x).val = _
    unfold embed
    rw [hAff', smul_add, map_smul, TensorProduct.smul_tmul', smul_eq_mul]
    norm_num
    rfl
  have htranslated := normalizerTranslatedChart C₁ basis W.subtype hWord hLabel embed
    (fun a => (ex a : ℤ)) hex' hroot haff hcover
    (fun l z => by simpa only [zpow_natCast] using hvn l z)
    (fun l z => by simpa only [zpow_natCast] using hvp l z) hbase
  have hFinite : C₁.FiniteLabels W.subtype :=
    ⟨Subtype.val_injective, FN, fun n => hF (eN n), hLabel⟩
  let u₀ : chart.chart.torus := ⟨1, by
    change (torusPoint D (integralRing K) 1 ≫ M.torus.hom.hom) ∈ j'.range
    rw [← cellValue_torus M.toIntegralMarking (integralRing K) l₀ l₁ (1 : TorusValues D (integralRing K)),
      cellValue_identity]
    exact one_mem j'.range⟩
  let r (w : B.SimpleWall p) := e.symm.toMonoidHom.comp (ρ w)
  have hUp (w : B.SimpleWall p) (z : chart.parameter (i w)) :
      j' (r w (upper z)) = cellValue M.toIntegralMarking (integralRing K) l₀ l₁
        (chart.chart.coordinates u₀ (@Function.update FoldedRootDirection chart.parameter
          (Classical.decEq _) (fun _ => 0) (i w) ((1 : chart.parameter (i w)) * z))) := by
    rw [one_mul]
    change j (e (e.symm (ρ w (upper z)))) = _
    rw [e.apply_symm_apply]
    let dec : DecidableEq FoldedRootDirection := inferInstance
    have he : Classical.decEq FoldedRootDirection = dec := Subsingleton.elim _ _
    rw [he]
    exact hup w z
  have hRank : C₁.RankOneLifts := by
    intro w
    let block := (FoldedOrdering.order o).block (i w)
    let word := block.2.flatMap SimpleRootOrbit.roots
    let orbit := (block.1.1 :: block.1.2.toList).map
      (fun v => (v, slotMap σ block (weylWordPerm word v.val)))
    have hOrbit : (orbit.map fun v => ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv v.1.val) =
        transportedLabels block := by
      rw [← weylWord_index]
      simp only [orbit, List.map_map, Function.comp_def, transportedLabels, SimpleRootOrbit.roots,
        List.map_cons, List.map_map, word]
    refine ⟨word, orbit, r w, t w, 1, u₀, ?_, ?_, hOrbit ▸ (FoldedOrdering.nodup o) (i w), ?_, ?_,
      rfl, by simp, hUp w, ht w, hlift' w⟩
    · intro i hi
      obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hi
      change i ∈ v.1.val :: v.2.toList.map Subtype.val at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact v.1.property
      · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hv
        exact z.property
    · change orbit.length = if ∃ i j : D.I, i ≠ j ∧ A.direction i = _ ∧ A.direction j = _ then 2 else 1
      have hL := congrArg List.length hOrbit
      simp only [List.length_map] at hL
      exact hL.trans (transportedLabels_length A (FoldedOrdering.order o) (i w) (FoldedOrdering.nodup o (i w)))
    · intro i₀
      change A.direction i₀ = i w ↔ i₀ ∈ orbit.map
        (fun v => ((word.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv v.1.val)
      rw [hOrbit]
      exact ((FoldedOrdering.order o).fibre (i w) i₀).symm
    · intro U
      change j (e (e.symm (ρ w U))) = _
      rw [e.apply_symm_apply]
      simp only [orbit, List.map_map, Function.comp_def, word, block]
      exact hρ w U
  have hOrd := ordinaryRange_normalizer C₁ hRange'
  have hq : 2 ≤ Nat.card (residue k) := by
    let _ : Fintype (residue k) := Fintype.ofFinite (𝓀[k])
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hbr := bruhatFromValuedCharts C₁ _ hq hsv hcover ex hex hvn hvp
    (foldedParameter_residue A (FoldedOrdering.order o) hres) hbase htranslated hRank (fun w =>
      ⟨r w, t w, 1, u₀, rfl, by simp, hUp w, ht w, hlift' w, fun z hz => by
        apply unitTorus_le_iwahori C₁
        change j (e (e.symm (ρ w (diagonal z)))) ∈ integralUnitTorus M
        rw [e.apply_symm_apply]
        exact hdiag w z hz⟩) hOrd
  have hNormal : C₁.G₀.Normal := by
    rw [ordinaryRange_generates C₁ hRange']
    infer_instance
  obtain ⟨Q⟩ := typeQuotientOfTranslatedChart C₁ hNormal hOrd (hRange'.trans A.affine_eq)
    href hred hvertices hbase htranslated
  refine ⟨⟨j, hJ, P, C₁, rfl, hN, hT, hWord, hFinite, rfl, ⟨hs, hRational, rfl⟩, ?_, ?_,
    hAff', hTr', hRange', hbr, Q⟩⟩
  · intro i hi
    obtain ⟨v, hm, hν⟩ := foldedSingletonParameter A (FoldedOrdering.order o) (FoldedOrdering.nodup o) σ (A.direction i) ((A.long i).2 hi)
    exact ⟨v, foldedChart_usesSlot A (FoldedOrdering.order o) u σ hs hRational i _ rfl _ (hm i), hν⟩
  · intro a ha
    obtain ⟨i, hi, v, h₁, h₂, hν⟩ := foldedPairedParameter A (FoldedOrdering.order o) (FoldedOrdering.nodup o) σ a ha
    have hi' : A.direction (τ.val.indexEquiv i) = a := ((A.orbits i _).2 (Or.inr rfl)).symm.trans hi
    exact ⟨i, hi, v, foldedChart_usesSlot A (FoldedOrdering.order o) u σ hs hRational i a hi _ h₁,
      foldedChart_usesSlot A (FoldedOrdering.order o) u σ hs hRational _ a hi' _ h₂, hν⟩

end FoldedLocal

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots AlcoveGeometry PinnedWallSigns FoldedRootDirection
  IsLongF4Doubled foldedDepthDenominator e6Partner diagramCocharacters diagramAverage simpleRootValues)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment)
open scoped TensorProduct

open private cover_simple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

universe u

section FoldedGeometry

variable {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

private structure FoldedGeometry {D : BasedRootDatum.{u}} (τ : BasedIso D D) where
  apartment : FoldedApartment τ
  signs : PinnedWallSigns apartment.roots apartment.basepoint
    (fun a => ∃ i, apartment.direction i = a ∧ D.base.IsPos i)
  geometry : AlcoveGeometry apartment.roots apartment.basepoint
  reflection : apartment.roots.ReflectionClosed
  reduced : apartment.roots.ReducedDirections
  vertices : ∀ a : apartment.roots.SimpleWall apartment.basepoint,
    ∃! x, IsAlcoveVertex apartment.roots apartment.basepoint a x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem foldedCentralApartments (c : MarkedCentralCover M M')
    (b : Fin 6 ≃ D.base.support) (b' : Fin 6 ≃ E.base.support)
    (hD : ExceptionalNumbering D 6 b) (hE : ExceptionalNumbering E 6 b')
    (τ : BasedIso D D) (τ' : BasedIso E E)
    (hτ : ∀ i, τ.val.indexEquiv (b i) = b (e6Partner i))
    (hτ' : ∀ i, τ'.val.indexEquiv (b' i) = b' (e6Partner i))
    (hcτ : ∀ i, c.rootEquiv (τ.val.indexEquiv i) = τ'.val.indexEquiv (c.rootEquiv i)) :
    ∃ (F : FoldedGeometry τ) (F' : FoldedGeometry τ')
      (e₀ : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
      (e : invariantApartment D τ ≃ₗ[ℚ] invariantApartment E τ')
      (d : FoldedRootDirection ≃ FoldedRootDirection),
      e₀.toLinearMap = c.pushCocharacter.baseChange ℚ ∧
      (∀ x, (e x).val = e₀ x.val) ∧ F'.apartment.basepoint = e F.apartment.basepoint ∧
      (∀ a x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv a) (e₀ x) =
        (ApartmentRoots.split D.datum ℚ).root a x) ∧
      (∀ a, e₀ ((ApartmentRoots.split D.datum ℚ).coroot a) =
        (ApartmentRoots.split E.datum ℚ).coroot (c.rootEquiv a)) ∧
      e '' F.apartment.roots.alcove F.apartment.basepoint = F'.apartment.roots.alcove F'.apartment.basepoint ∧
      (∀ i, d (F.apartment.direction i) = F'.apartment.direction (c.rootEquiv i)) ∧
      (∀ a x, F'.apartment.roots.root (d a) (e x) = F.apartment.roots.root a x) ∧
      ∀ a, e (F.apartment.roots.coroot a) = F'.apartment.roots.coroot (d a) := by
  classical
  let _ := D.finiteRoots
  let _ := D.reduced
  let _ := D.freeX
  let _ := D.finiteX
  let _ := D.freeY
  let _ := D.finiteY
  let _ := E.finiteRoots
  let _ := E.reduced
  let _ := E.freeX
  let _ := E.finiteX
  let _ := E.freeY
  let _ := E.finiteY
  let B := ApartmentRoots.split D.datum ℚ
  let B' := ApartmentRoots.split E.datum ℚ
  obtain ⟨e₀, he₀, hr, hcor, _⟩ := centralCoverApartment c b hD.1 hE.1
  obtain ⟨x, t, ht, hx, hs⟩ :=
    ExceptionalAffineRootSystems.pinnedAlcovePoint (K := ℚ) D.datum D.base b hD.1
  have hx' (j : Fin 6) : simpleRootValues E.datum E.base b' ℚ (e₀ x) j = t := by
    obtain ⟨a, ha⟩ := c.rootEquiv.surjective (b' j).val
    obtain ⟨i, hi⟩ := b.surjective ⟨a, (cover_simple c a).mpr (ha.symm ▸ (b' j).property)⟩
    change B'.root (b' j).val (e₀ x) = t
    rw [← ha, hr]
    exact (congrArg (fun i : D.I => B.root i x) (congrArg Subtype.val hi)).symm.trans (hx i)
  have hs' (i : E.I) : (0 < B'.root i (e₀ x) ↔ E.base.IsPos i) ∧
      0 < |B'.root i (e₀ x)| ∧ |B'.root i (e₀ x)| < 1 / 2 := by
    obtain ⟨a, rfl⟩ := c.rootEquiv.surjective i
    rw [hr, ← c.marking.1]
    exact hs a
  obtain ⟨A, hA, hS, hG, hR, hRed, hV⟩ := foldedExceptionalApartmentAt D b τ hD hτ x t ht hx hs
  obtain ⟨A', hA', hS', hG', hR', hRed', hV'⟩ := foldedExceptionalApartmentAt E b' τ' hE hτ' (e₀ x) t ht hx' hs'
  obtain ⟨coords, hCoords⟩ := ExceptionalAffineRootSystems.cocharacterApartmentCoordinates (K := ℚ)
    E.datum E.base b' hE.1
  have hcomm (x : ℚ ⊗[ℤ] D.Y) : e₀ (diagramCocharacters τ.val x) = diagramCocharacters τ'.val (e₀ x) := by
    have h (i : D.I) : B'.root (c.rootEquiv (τ.val.indexEquiv i)) (e₀ (diagramCocharacters τ.val x)) =
        B'.root (c.rootEquiv (τ.val.indexEquiv i)) (diagramCocharacters τ'.val (e₀ x)) := by
      rw [hr, diagram_rootValue, hcτ, diagram_rootValue, hr]
    apply coords.injective
    change coords.toLinearMap _ = coords.toLinearMap _
    rw [hCoords]
    funext i
    obtain ⟨a, ha⟩ := (c.rootEquiv.surjective.comp τ.val.indexEquiv.surjective) (b' i).val
    change B'.root (b' i).val _ = B'.root (b' i).val _
    rw [← ha]
    exact h a
  have hFix (y : ℚ ⊗[ℤ] D.Y) : e₀ y ∈ invariantApartment E τ' ↔ y ∈ invariantApartment D τ := by
    change diagramCocharacters τ'.val (e₀ y) - e₀ y = 0 ↔ diagramCocharacters τ.val y - y = 0
    rw [sub_eq_zero, sub_eq_zero, ← hcomm, e₀.injective.eq_iff]
  let eMap : invariantApartment D τ →ₗ[ℚ] invariantApartment E τ' :=
    (e₀.toLinearMap.comp (invariantApartment D τ).subtype).codRestrict _ (fun y => (hFix y.val).2 y.property)
  let e : invariantApartment D τ ≃ₗ[ℚ] invariantApartment E τ' :=
    LinearEquiv.ofBijective eMap ⟨fun x y h => Subtype.ext (e₀.injective (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨x, h⟩ := e₀.surjective y.val
        exact ⟨⟨x, (hFix x).1 (h.symm ▸ y.property)⟩, Subtype.ext h⟩⟩
  have hp : A'.basepoint = e A.basepoint := by
    apply Subtype.ext
    change A'.basepoint.val = e₀ A.basepoint.val
    rw [hA', hA]
  let dMap (a : FoldedRootDirection) := A'.direction (c.rootEquiv ((A.surjective a).choose))
  have hdMap (i : D.I) : dMap (A.direction i) = A'.direction (c.rootEquiv i) := by
    let j := (A.surjective (A.direction i)).choose
    have hj : A.direction j = A.direction i := (A.surjective _).choose_spec
    apply Eq.symm
    apply (A'.orbits (c.rootEquiv i) (c.rootEquiv j)).2
    rcases (A.orbits i j).1 hj.symm with h | h
    · exact Or.inl (congrArg c.rootEquiv h)
    · exact Or.inr ((congrArg c.rootEquiv h).trans (hcτ i))
  have hdBij : Function.Bijective dMap := by
    constructor
    · intro a a'
      obtain ⟨i, rfl⟩ := A.surjective a
      obtain ⟨i', rfl⟩ := A.surjective a'
      rw [hdMap, hdMap]
      intro h
      apply (A.orbits i i').2
      rcases (A'.orbits _ _).1 h with h | h
      · exact Or.inl (c.rootEquiv.injective h)
      · exact Or.inr (c.rootEquiv.injective (h.trans (hcτ i).symm))
    · intro a
      obtain ⟨i', rfl⟩ := A'.surjective a
      obtain ⟨i, rfl⟩ := c.rootEquiv.surjective i'
      exact ⟨A.direction i, hdMap i⟩
  let d := Equiv.ofBijective dMap hdBij
  have hDir (i : D.I) : d (A.direction i) = A'.direction (c.rootEquiv i) := hdMap i
  have hRoot (a : FoldedRootDirection) (y : invariantApartment D τ) : A'.roots.root (d a) (e y) = A.roots.root a y := by
    obtain ⟨i, rfl⟩ := A.surjective a
    have hl : IsLongF4Doubled (A'.direction (c.rootEquiv i)).val ↔ IsLongF4Doubled (A.direction i).val := by
      rw [A'.long, A.long, ← hcτ, c.rootEquiv.injective.eq_iff]
    have he : foldedDepthDenominator (A'.direction (c.rootEquiv i)) = foldedDepthDenominator (A.direction i) := by
      unfold foldedDepthDenominator
      split_ifs <;> tauto
    rw [hDir, A'.root_value, A.root_value, he]
    change _ * B'.root (c.rootEquiv i) (e₀ y.val) = _
    rw [hr]
  have hCoroot (a : FoldedRootDirection) : e (A.roots.coroot a) = A'.roots.coroot (d a) := by
    obtain ⟨i, rfl⟩ := A.surjective a
    apply Subtype.ext
    rw [hDir]
    change e₀ (A.roots.coroot (A.direction i)).val = (A'.roots.coroot (A'.direction (c.rootEquiv i))).val
    rw [A.coroot_value, A'.coroot_value]
    simp only [diagramAverage, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_smul, map_add, hcomm, hcor]
  have hAlcove : e '' A.roots.alcove A.basepoint = A'.roots.alcove A'.basepoint := by
    have hW (a : FoldedRootDirection × ℤ) (y : invariantApartment D τ) :
        A'.roots.wallValue (d a.1, a.2) (e y) = A.roots.wallValue a y := by
      change _ + _ = _ + _
      rw [hRoot]
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨z', hz', hh⟩ ⟨a, m⟩ hs
      obtain rfl := e.injective hh
      obtain ⟨a, rfl⟩ := d.surjective a
      change 0 < A'.roots.wallValue (d a, m) (e z')
      rw [hW (a, m)]
      apply hz' (a, m)
      change 0 < A'.roots.wallValue (d a, m) A'.basepoint at hs
      rwa [hp, hW (a, m)] at hs
    · intro hz
      refine ⟨z, ?_, rfl⟩
      intro a ha
      change 0 < A.roots.wallValue a z
      rw [← hW a]
      apply hz (d a.1, a.2)
      change 0 < A'.roots.wallValue (d a.1, a.2) A'.basepoint
      rw [hp, hW]
      exact ha
  exact ⟨⟨A, hS, hG, hR, hRed, hV⟩, ⟨A', hS', hG', hR', hRed', hV'⟩,
    e₀, e, d, he₀, fun _ => rfl, hp, hr, hcor, hAlcove, hDir, hRoot, hCoroot⟩

end FoldedGeometry

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalPinnedBaseChange (ExtendsDiagram)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre pinnedMarkedPoint coordinatePointEquiv quadraticIntegralAlgebra)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom pinnedGroundPoint MarkedCentralCover pointHom)
open Specs.ExceptionalIwahoriCongruence (integralRingMap changeRingHom integralRing)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.SchemeDerivedGroup (FactorsThrough)
open private extensionPointEquiv extensionPointEquiv_natural normalizes_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private normalizes_coefficient_iff normalizes_groundSections_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private groundSectionsEquiv groundSectionsEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
attribute [local instance] integerAlgebra

universe u

section FoldedPointTransport

variable {F k : Type u} [Field F] [Field k] [Algebra F k]

private noncomputable def groupSectionsIso {G H : GroupScheme k} (a : G ≅ H) :
    (𝟙_ (SchemeOver k) ⟶ G.X) ≃* (𝟙_ (SchemeOver k) ⟶ H.X) :=
  ((yonedaGrp.mapIso a).app (.op (𝟙_ (SchemeOver k)))).groupIsoToMulEquiv

private theorem groupSectionsIso_apply {G H : GroupScheme k} (a : G ≅ H)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) : groupSectionsIso a x = x ≫ a.hom.hom.hom := rfl

private noncomputable def coefficientLevelEquiv (G : GroupScheme F) {H : GroupScheme k}
    (a : H ≅ (groupBaseChange F k).obj G) :
    (𝟙_ (SchemeOver k) ⟶ H.X) ≃* GroupPoints G (CommAlgCat.of F k) :=
  (groupSectionsIso a).trans (extensionPointEquiv G)

private theorem groundIso_toUnit (k : Type u) [Field k] :
    (groundIso (k := k)).hom =
      CartesianMonoidalCategory.toUnit ((testSpec k).obj (.op (CommAlgCat.of k k))) :=
  Subsingleton.elim _ _

private theorem coefficientLevelEquiv_apply (G : GroupScheme F) {H : GroupScheme k}
    (a : H ≅ (groupBaseChange F k).obj G) (x : 𝟙_ (SchemeOver k) ⟶ H.X) :
    coefficientLevelEquiv G a x = baseChangePoint F k G.X (CommAlgCat.of k k)
      (CartesianMonoidalCategory.toUnit _ ≫ x ≫ a.hom.hom.hom) := by
  change baseChangePoint F k G.X (CommAlgCat.of k k) ((groundIso (k := k)).hom ≫ (x ≫ a.hom.hom.hom)) = _
  rw [groundIso_toUnit]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem coefficientLevelEquiv_subgroups (G : AffineAlgebraicGroup F) (T : ClosedSubgroup G.val)
    {H : GroupScheme k} (U : ClosedSubgroup H)
    (a : H ≅ (groupBaseChange F k).obj G.val) (b : U.group ≅ (groupBaseChange F k).obj T.group)
    (h : U.inclusion ≫ a.hom = b.hom ≫ (groupBaseChange F k).map T.inclusion)
    (x : 𝟙_ (SchemeOver k) ⟶ H.X) :
    (Normalizes U.inclusion x ↔ Normalizes T.inclusion (coefficientLevelEquiv G.val a x)) ∧
    (FactorsThrough U x ↔ FactorsThrough T (coefficientLevelEquiv G.val a x)) := by
  let e := coefficientLevelEquiv G.val a
  let t := coefficientLevelEquiv T.group b
  have hx (z : 𝟙_ (SchemeOver k) ⟶ U.group.X) :
      e (z ≫ U.inclusion.hom.hom) = t z ≫ T.inclusion.hom.hom := by
    change extensionPointEquiv G.val ((z ≫ U.inclusion.hom.hom) ≫ a.hom.hom.hom) =
      extensionPointEquiv T.group (z ≫ b.hom.hom.hom) ≫ T.inclusion.hom.hom
    have hcomp := congrArg (fun v : U.group ⟶ (groupBaseChange F k).obj G.val => v.hom.hom) h
    change U.inclusion.hom.hom ≫ a.hom.hom.hom = b.hom.hom.hom ≫ ((groupBaseChange F k).map T.inclusion).hom.hom at hcomp
    rw [Category.assoc, hcomp, ← Category.assoc]
    exact extensionPointEquiv_natural (K := k) T.inclusion (z ≫ b.hom.hom.hom)
  have hclosed := LinearAlgebraicGroups.baseChangeClosedSubgroup F k T.inclusion T.isClosedImmersion
  let S := Specs.GeometricRadicals.baseChangedSubgroup k T hclosed
  have hs : b.hom ≫ S.inclusion = U.inclusion ≫ a.hom := h.symm
  have hsinv : b.inv ≫ U.inclusion = S.inclusion ≫ a.inv := by
    symm
    rw [Iso.comp_inv_eq, Category.assoc, hs.symm, Iso.inv_hom_id_assoc]
  refine ⟨?_, ?_⟩
  · change _ ↔ Normalizes T.inclusion (extensionPointEquiv G.val (x ≫ a.hom.hom.hom))
    rw [← normalizes_coefficient_iff G T]
    constructor
    · exact normalizes_of_iso U S a b hs
    · intro hy
      have hn := normalizes_of_iso S U a.symm b.symm hsinv hy
      change Normalizes U.inclusion ((x ≫ a.hom.hom.hom) ≫ a.inv.hom.hom) at hn
      have hcomp := congrArg (fun f => f.hom.hom) a.hom_inv_id
      change a.hom.hom.hom ≫ a.inv.hom.hom = 𝟙 _ at hcomp
      rwa [Category.assoc, hcomp, Category.comp_id] at hn
  · change (∃ z, z ≫ U.inclusion.hom.hom = x) ↔ ∃ z, z ≫ T.inclusion.hom.hom = e x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨t z, (hx z).symm⟩
    · rintro ⟨z, hz⟩
      obtain ⟨v, rfl⟩ := t.surjective z
      exact ⟨v, e.injective ((hx v).trans hz)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem groundSectionsEquiv_subgroups {G : AffineAlgebraicGroup F} (T : ClosedSubgroup G.val)
    (x : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    (Normalizes T.inclusion x ↔ Normalizes T.inclusion (groundSectionsEquiv G.val x)) ∧
    (FactorsThrough T x ↔ FactorsThrough T (groundSectionsEquiv G.val x)) := by
  have h := normalizes_groundSections_iff G T x
  rw [groundIso_toUnit] at h
  refine ⟨by rw [groundSectionsEquiv_apply]; exact h.symm, ?_⟩
  change (∃ z, z ≫ T.inclusion.hom.hom = x) ↔ ∃ z, z ≫ T.inclusion.hom.hom = groundSectionsEquiv G.val x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨groundSectionsEquiv T.group z, ?_⟩
    rw [groundSectionsEquiv_apply, groundSectionsEquiv_apply, Category.assoc]
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (groundSectionsEquiv T.group).surjective z
    refine ⟨y, (groundSectionsEquiv G.val).injective ?_⟩
    calc
      groundSectionsEquiv G.val (y ≫ T.inclusion.hom.hom) =
          groundSectionsEquiv T.group y ≫ T.inclusion.hom.hom := by
        rw [groundSectionsEquiv_apply, groundSectionsEquiv_apply, Category.assoc]
      _ = groundSectionsEquiv G.val x := hz

end FoldedPointTransport

section CompositumPoints

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {σ : Gal(L/F)} (T : DiagramCompositum F L k σ)

private theorem diagramCompositum_extends : ExtendsDiagram F L k T.field σ T.diagram T.tensor :=
  ⟨T.right_eq, fun z => by rw [T.left_eq, T.left_eq, T.diagram_extends]⟩

private theorem diagramCompositum_tensorMap : T.tensor.toAlgHom =
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom F L T.field) (IsScalarTower.toAlgHom F k T.field)
      (fun _ _ => Commute.all _ _) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.lift_tmul]
    have h := T.tensor.map_mul (x ⊗ₜ[F] (1 : k)) ((1 : L) ⊗ₜ[F] y)
    change T.tensor ((x ⊗ₜ[F] (1 : k)) * ((1 : L) ⊗ₜ[F] y)) =
      T.tensor (x ⊗ₜ[F] (1 : k)) * T.tensor ((1 : L) ⊗ₜ[F] y) at h
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, T.left_eq, T.right_eq] at h
    exact h
  | add x y hx hy => simp only [map_add, hx, hy]

end CompositumPoints

section CentralPoints

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K] [Algebra F L] [Algebra F k] [Algebra F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}

private theorem descendedCentralPointSquare (R : RamifiedReference F L M) (R' : RamifiedReference F L M')
    (c : MarkedCentralCover M M') (φ : R.descent.group.val ⟶ R'.descent.group.val)
    (hφ : ∀ (S : TestAlgebra F) (g : GroupPoints R.descent.group.val S),
      pinnedMarkedPoint R'.fibre R'.descent.data S ((coordinatePointEquiv R'.descent.group S).symm
        (pointHom φ ((testSpec F).obj (.op S)) g)) =
      integralPointHom c.map ((quadraticIntegralAlgebra F L).obj S)
        (pinnedMarkedPoint R.fibre R.descent.data S ((coordinatePointEquiv R.descent.group S).symm g)))
    (f : L →ₐ[F] K) (g : k →ₐ[F] K) (x : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    ramifiedPoint R' f g (pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k))) x) =
      integralPointHom c.map (integralRing K) (ramifiedPoint R f g x) := by
  let r := integralRingMap (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let S := CommAlgCat.of F k
  let p := pinnedMarkedPoint R.fibre R.descent.data S ((coordinatePointEquiv R.descent.group S).symm x)
  have hComm : changeRingHom M'.group r (integralPointHom c.map _ p) =
      integralPointHom c.map (integralRing K) (changeRingHom M.group r p) := by
    change integralSpec.map r.op ≫ p ≫ c.map.hom.hom = (integralSpec.map r.op ≫ p) ≫ c.map.hom.hom
    exact (Category.assoc _ _ _).symm
  exact (congrArg (changeRingHom M'.group r) (hφ S x)).trans hComm

end CentralPoints

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj Pointwise TensorProduct
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (FoldedRootDirection PinnedWallSigns)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom mapCellValues CellValues cellValue)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (TransportedOrbit SimpleRootOrbit rationalOrbitParameter transportedLabels weylWordPerm)
open Specs.ExceptionalFoldedRootChart (OrbitOrdering slotMap slotUnit)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment fixedWeylGroup)
open Specs.AdjointRepresentation (GroupPoints)
open private cellValue_torus changeRing_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
attribute [local instance] integerAlgebra

universe u

section FoldedScalar

variable {k K k' K' : Type u} [Field k] [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K']
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
  [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}
  {G H : Type u} [Group G] [Group H] {j : G →* FieldPoints M K} {j' : H →* FieldPoints M K'}
  {A : FoldedApartment τ}

private def foldedParameterScalar (f : k →+* k') (g : K →+* K') :
    ∀ b : TransportedOrbit D, rationalOrbitParameter k K b →+* rationalOrbitParameter k' K' b
  | (⟨_, none⟩, _) => f
  | (⟨_, some _⟩, _) => g

private theorem foldedSlotScalar (f : k →+* k') (g : K →+* K') (σ : Gal(K/k)) (σ' : Gal(K'/k'))
    (hfk : ∀ x, g (algebraMap k K x) = algebraMap k' K' (f x))
    (hfσ : ∀ x, g (σ x) = σ' (g x))
    (b : TransportedOrbit D) (i : D.I) (x : rationalOrbitParameter k K b) :
    g (slotMap σ b i x) = slotMap σ' b i (foldedParameterScalar f g b x) := by
  classical
  rcases b with ⟨⟨a, c⟩, l⟩
  cases c with
  | none => exact hfk x
  | some c =>
    let h := weylWordPerm (l.flatMap SimpleRootOrbit.roots) a.val
    change g ((if i = h then RingHom.id K else σ.toRingHom) x) =
      (if i = h then RingHom.id K' else σ'.toRingHom) (g x)
    split_ifs
    · rfl
    · exact hfσ x

private theorem foldedParameterScalar_value (f : k →+* k') (g : K →+* K') (b : TransportedOrbit D)
    (hf : ∀ x, normalizedValuation k' (f x) = normalizedValuation k x)
    (hg : ∀ x, normalizedValuation K' (g x) = normalizedValuation K x)
    (x : rationalOrbitParameter k K b) :
    normalizedValuation (rationalOrbitParameter k' K' b) (foldedParameterScalar f g b x) =
      normalizedValuation (rationalOrbitParameter k K b) x := by
  rcases b with ⟨⟨a, c⟩, l⟩
  cases c
  · exact hf x
  · exact hg x

set_option backward.isDefEq.respectTransparency false in
private theorem foldedOrderedCoordinates_scalar (o : OrbitOrdering A.direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (σ : Gal(K/k)) (σ' : Gal(K'/k')) (f : k →+* k') (g : K →+* K')
    (hfk : ∀ x, g (algebraMap k K x) = algebraMap k' K' (f x))
    (hfσ : ∀ x, g (σ x) = σ' (g x))
    (t : TorusValues D (integralRing K)) (x : ∀ a, rationalOrbitParameter k K (o.block a)) :
    mapCellValues (integralRingMap g) (o.coordinates u σ t x) =
      o.coordinates u σ' ((Units.map g.toMonoidHom).comp t)
        (fun a => foldedParameterScalar f g (o.block a) (x a)) := by
  let z (i : D.I) := x (A.direction i)
  have he (i : D.I) :
      g (algebraMap Integers.{u} K (slotUnit u (o.block (A.direction i)) i : Integers.{u}) *
        slotMap σ (o.block (A.direction i)) i (z i)) =
      algebraMap Integers.{u} K' (slotUnit u (o.block (A.direction i)) i : Integers.{u}) *
        slotMap σ' (o.block (A.direction i)) i (foldedParameterScalar f g _ (z i)) := by
    rw [map_mul, foldedSlotScalar f g σ σ' hfk hfσ]
    congr 1
    exact map_intCast g _
  exact Prod.ext (funext fun i => he _) (Prod.ext rfl (funext fun i => he _))

set_option backward.isDefEq.respectTransparency false in
private theorem foldedSubgroupsScalar
    (C : LocalComparison (j := j) (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (C' : LocalComparison (j := j') (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (hC : C.FiniteLabels (fixedWeylGroup D τ).subtype)
    (hC' : C'.FiniteLabels (fixedWeylGroup D τ).subtype)
    (hword : ∀ w, ∀ a ∈ C.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hword' : ∀ w, ∀ a ∈ C'.localIwahori.normalizer.word w, a ∈ D.base.support)
    (hRange : C.affine.range = A.roots.affineWeylGroup)
    (hRange' : C'.affine.range = A.roots.affineWeylGroup)
    (hAff : ∀ n x, (C.affine n x).val = (C.localIwahori.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (C.localIwahori.normalizer.translation (C.localIwahori.normalizer.torusPart n)).toAdd))
    (hAff' : ∀ n x, (C'.affine n x).val = (C'.localIwahori.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (C'.localIwahori.normalizer.translation (C'.localIwahori.normalizer.torusPart n)).toAdd))
    (g : K →+* K') (s : G →* H) (hv : ∀ x, normalizedValuation K' (g x) = normalizedValuation K x)
    (hj : ∀ x, j' (s x) = scalarPoints M g (j x)) (hN : C'.N.comap s = C.N)
    (hT : C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus) :
    C'.I.comap s = C.I ∧ C'.N.comap s = C.N ∧ C'.T₀.comap s = C.T₀ ∧ C'.G₀.comap s = C.G₀ ∧
    C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus ∧
    C.affine.range = C'.affine.range ∧
    (∀ (n : C.N) (n' : C'.N), (n' : H) = s n → C'.affine n' = C.affine n ∧
      C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n) ∧
    (∀ w, s (C.lift w) * (C'.lift w : H)⁻¹ ∈ C'.T₀) := by
  obtain ⟨hI, hU, hLabel⟩ := ExceptionalValuedScalarTransport.valuedLocalTransport j j'
    C.localIwahori C'.localIwahori (fixedWeylGroup D τ).subtype hC.1 hword hword'
    hC.2.choose_spec.2 hC'.2.choose_spec.2 g s hv hj hN hT
  have hAff'' (n : C.N) (n' : C'.N) (he : (n' : H) = s n) :
      C'.affine n' = C.affine n ∧
      C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n := by
    obtain ⟨hl, ht⟩ := hLabel n n' he
    refine ⟨AffineEquiv.ext fun x => Subtype.ext ?_, hl⟩
    rw [hAff, hAff', hl, ht]
  have hG : C'.G₀.comap s = C.G₀ := by
    rw [ordinaryRange_generates C hRange, ordinaryRange_generates C' hRange', Subgroup.comap_top]
  refine ⟨hI, hN, hU, hG, hT, hRange.trans hRange'.symm, hAff'', ?_⟩
  intro w
  let n := C.lift w
  let n' : C'.N := ⟨s n, (SetLike.ext_iff.mp hN _).mpr n.property⟩
  exact sameLabel_div_mem_unitTorus C' (n := n') (m := C'.lift w)
    ((hAff'' n n' rfl).1.trans ((C.lift_label w).trans (C'.lift_label w).symm))

private theorem foldedTypeQuotientScalar
    (C : LocalComparison (j := j) (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (C' : LocalComparison (j := j') (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (Q : C.TypeQuotient) (Q' : C'.TypeQuotient) (s : G →* H)
    (hN : C'.N.comap s = C.N)
    (hAff : ∀ (n : C.N) (n' : C'.N), (n' : H) = s n → C'.affine n' = C.affine n) :
    TypeQuotientTransport Q Q' s (MonoidHom.id _) := by
  let _ := A.omega_trivial
  refine ⟨fun _ => Subsingleton.elim _ _, ?_⟩
  intro ω
  let n := Q.lift ω
  let n' : C'.N := ⟨s n, (SetLike.ext_iff.mp hN _).mpr n.property⟩
  exact sameLabel_div_mem_unitTorus C' (n := n') (m := Q'.lift ω)
    ((hAff n n' rfl).trans ((Q.affine_lift ω).trans (Q'.affine_lift ω).symm))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 550000 in
private theorem foldedScalarComparison
    (C : LocalComparison (j := j) (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (C' : LocalComparison (j := j') (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (o : OrbitOrdering A.direction) (u : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (σ : Gal(K/k)) (σ' : Gal(K'/k'))
    (hChart : ∃ h hx, C.chart = foldedRootChart A o u σ j h hx)
    (hChart' : ∃ h hx, C'.chart = foldedRootChart A o u σ' j' h hx)
    (f : k →+* k') (g : K →+* K') (s : G →* H)
    (hf : ∀ x, normalizedValuation k' (f x) = normalizedValuation k x)
    (hg : ∀ x, normalizedValuation K' (g x) = normalizedValuation K x)
    (hfk : ∀ x, g (algebraMap k K x) = algebraMap k' K' (f x))
    (hfσ : ∀ x, g (σ x) = σ' (g x))
    (hs : ∀ x, j' (s x) = scalarPoints M g (j x))
    (hData : C'.I.comap s = C.I ∧ C'.N.comap s = C.N ∧ C'.T₀.comap s = C.T₀ ∧ C'.G₀.comap s = C.G₀ ∧
      C'.localIwahori.normalizer.torus.comap s = C.localIwahori.normalizer.torus ∧
      C.affine.range = C'.affine.range ∧
      (∀ (n : C.N) (n' : C'.N), (n' : H) = s n → C'.affine n' = C.affine n ∧
        C'.localIwahori.normalizer.label n' = C.localIwahori.normalizer.label n) ∧
      ∀ w, s (C.lift w) * (C'.lift w : H)⁻¹ ∈ C'.T₀) : ScalarComparison g s C C' := by
  have hInj : Function.Injective s := by
    intro x y h
    apply C.point_injective
    apply (changeRing_injective M.toIntegralMarking (integralRingMap g) g.injective)
    change scalarPoints M g (j x) = scalarPoints M g (j y)
    rw [← hs, ← hs, h]
  obtain ⟨hI, hN, hU, h₀, hT, hRange, hLab, hLift⟩ := hData
  refine ⟨hInj, hs, hI, hN, hU, h₀, hT, hRange, hLab, hLift, ?_, ?_⟩
  · obtain ⟨_, _, h⟩ := hChart
    obtain ⟨_, _, h'⟩ := hChart'
    rw [h, h']
    rfl
  · let coordinateTransport (P : LocalRootChart (j := j) A.roots A.basepoint)
        (Q : LocalRootChart (j := j') A.roots A.basepoint) : Prop :=
        ∃ (hn : P.negative = Q.negative) (hp : P.positive = Q.positive)
          (e : ∀ a, P.parameter a →+* Q.parameter a) (tmap : P.chart.torus → Q.chart.torus),
          (∀ a x, Q.value a (e a x) = P.value a x) ∧
          ∀ t x, mapCellValues (integralRingMap g) (P.chart.coordinates t x) =
            (hn.symm ▸ hp.symm ▸ Q.chart.coordinates (tmap t) (fun a => e a (x a)))
    change coordinateTransport C.chart C'.chart
    obtain ⟨_, _, h⟩ := hChart
    obtain ⟨_, _, h'⟩ := hChart'
    rw [h, h']
    unfold coordinateTransport
    let tmap (t : foldedTorusCoordinates j) : foldedTorusCoordinates j' :=
      ⟨(Units.map g.toMonoidHom).comp t.val, by
        obtain ⟨x, hx⟩ := t.property
        refine ⟨s x, ?_⟩
        rw [hs, hx]
        let neg := o.negative.flatMap transportedLabels
        let pos := o.positive.flatMap transportedLabels
        rw [← cellValue_torus M.toIntegralMarking (integralRing K) neg pos t.val,
          ← cellValue_torus M.toIntegralMarking (integralRing K') neg pos]
        have hnat := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking neg pos
          o.negative_enumerates o.positive_enumerates).2 (integralRingMap g)
          (0, t.val, 0)
        exact hnat.trans (congrArg (cellValue M.toIntegralMarking (integralRing K') neg pos) (by
          apply Prod.ext
          · funext i
            exact g.map_zero
          · apply Prod.ext
            · rfl
            · funext i
              exact g.map_zero))⟩
    refine ⟨rfl, rfl, fun a => foldedParameterScalar f g (o.block a), tmap, ?_, ?_⟩
    · intro a x
      exact foldedParameterScalar_value f g (o.block a) hf hg x
    · intro t x
      exact foldedOrderedCoordinates_scalar o u σ σ' f g hfk hfσ t.val x

end FoldedScalar

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (e6Partner)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.PinnedPairDescent (DescendedPair)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre TransportedOrbit markedFibrePoint)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.ExceptionalIwahoriImageComparison (pinnedGroundPoint)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex normalizedValuation)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.ExceptionalFoldedRootChart (IsTransportUnitSystem)
open Specs.SchemeDerivedGroup (FactorsThrough)
open private groundSectionsEquiv groundSectionsEquiv_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private quadraticGalois from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open ValuativeRel
attribute [local instance] integerAlgebra

universe u

section FoldedReference

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional k K] [IsGalois k K]
  {D : BasedRootDatum.{u}} {M : Model D}

private structure FoldedCoefficientReference (R : RamifiedReference F L M) (σ : Gal(L/F))
    (β : Gal(K/k)) (f : L →ₐ[F] K) where
  fibre : MarkedFibre M k
  pin : Aut fibre.realization.attached.toBased ≃* Aut fibre.realization.pinned
  adjoint : AdjointQuotient fibre.realization.pinned.pair.G
  sequence : SplitSequence fibre.realization.pinned fibre.realization.attached pin adjoint
  outer : Gal(K/k) →* Aut fibre.realization.attached.toBased
  descent : DescendedPair (l := pin) K outer
  same_diagram : (markedDiagramEquiv fibre.realization (descent.data.outer β)).asIso.hom = R.diagram σ
  points : GroupPoints R.descent.group.val (CommAlgCat.of F k) ≃* (𝟙_ (SchemeOver k) ⟶ descent.group.val.X)
  point_eq (x) : pinnedGroundPoint fibre descent.data (points x) =
    ramifiedPoint R f (IsScalarTower.toAlgHom F k K) x
  normalizes (x) : Normalizes descent.torus.inclusion (points x) ↔ Normalizes R.descent.torus.inclusion x
  factorsThrough (x) : FactorsThrough descent.torus (points x) ↔ FactorsThrough R.descent.torus x

omit [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K] [FiniteDimensional k K] [IsGalois k K] in
private theorem foldedBaseReference (R : RamifiedReference F L M) (σ : Gal(L/F)) :
    Nonempty (FoldedCoefficientReference R σ σ (AlgHom.id F L)) := by
  obtain ⟨e, he, hpoint⟩ := ramifiedGroundPointComparison R
  have hE : e = groundSectionsEquiv R.descent.group.val :=
    MulEquiv.ext fun x => (he x).trans (groundSectionsEquiv_apply R.descent.group.val x).symm
  refine ⟨⟨R.fibre, R.pin, R.adjoint, R.sequence, R.outer, R.descent,
    by rw [R.descent.outer_eq], e.symm, ?_, ?_, ?_⟩⟩
  · intro x
    have h := hpoint (e.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  · intro x
    rw [hE]
    have h := (groundSectionsEquiv_subgroups R.descent.torus
      ((groundSectionsEquiv R.descent.group.val).symm x)).1
    exact h.trans (Iff.of_eq (congrArg (fun x : GroupPoints R.descent.group.val (CommAlgCat.of F F) =>
      Normalizes R.descent.torus.inclusion x) ((groundSectionsEquiv R.descent.group.val).apply_symm_apply x)))
  · intro x
    rw [hE]
    have h := (groundSectionsEquiv_subgroups R.descent.torus
      ((groundSectionsEquiv R.descent.group.val).symm x)).2
    exact h.trans (Iff.of_eq (congrArg (fun x : GroupPoints R.descent.group.val (CommAlgCat.of F F) =>
      FactorsThrough R.descent.torus x) ((groundSectionsEquiv R.descent.group.val).apply_symm_apply x)))

omit [Algebra F K] [Algebra k K] [IsScalarTower F k K] [FiniteDimensional k K] [IsGalois k K] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem foldedCompositumReference [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (R : RamifiedReference F L M) (σ : Gal(L/F)) (deg : Module.finrank F L = 2) (hne : σ ≠ 1)
    (hIso : D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤)
    (T : DiagramCompositum F L k σ) :
    Nonempty (FoldedCoefficientReference R σ T.diagram (IsScalarTower.toAlgHom F L T.field)) := by
  obtain ⟨C, l, Q, ω, d, hseq, hDiag, J, JB, JT, hB, hT, hPoint⟩ :=
    ExceptionalPinnedBaseChange.pinnedBaseChange R.fibre R.descent σ R.sequence deg hne hIso
      k T.field T.degree T.diagram T.diagram_ne T.tensor (diagramCompositum_extends T)
  let e := coefficientLevelEquiv R.descent.group.val J
  refine ⟨⟨C, l, Q, hseq, ω, d, ?_, e.symm, ?_, ?_, ?_⟩⟩
  · rw [R.descent.outer_eq] at hDiag
    exact hDiag
  · intro x
    have h := hPoint (e.symm x)
    dsimp only at h
    rw [← coefficientLevelEquiv_apply, show coefficientLevelEquiv R.descent.group.val J (e.symm x) = x from
      e.apply_symm_apply x] at h
    have hRing := congrArg AlgHom.toRingHom (diagramCompositum_tensorMap T)
    change T.tensor.toRingEquiv.toRingHom = _ at hRing
    rw [hRing] at h
    exact h
  · intro x
    have h := (coefficientLevelEquiv_subgroups R.descent.group R.descent.torus d.torus J JT hT (e.symm x)).1
    rw [show coefficientLevelEquiv R.descent.group.val J (e.symm x) = x from e.apply_symm_apply x] at h
    exact h
  · intro x
    have h := (coefficientLevelEquiv_subgroups R.descent.group R.descent.torus d.torus J JT hT (e.symm x)).2
    rw [show coefficientLevelEquiv R.descent.group.val J (e.symm x) = x from e.apply_symm_apply x] at h
    exact h

section LocalReference

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension k K]
  {R : RamifiedReference F L M} {σ : Gal(L/F)} {β : Gal(K/k)} {f : L →ₐ[F] K}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem foldedReferenceLocalModel (T : FoldedCoefficientReference R σ β f)
    (deg : Module.finrank k K = 2) (hne : β ≠ 1) (hr : 1 < ramificationIndex k K)
    (b : Fin 6 ≃ D.base.support) (hNum : ExceptionalNumbering D 6 b)
    (hIso : D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i))
    (A : FoldedGeometry (R.diagram σ)) (o : FoldedOrdering (FoldedGeometry.apartment A))
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (hu : IsTransportUnitSystem M.toIntegralMarking u) :
    Nonempty (FoldedLocalModel (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.descent T)
      β (FoldedGeometry.apartment A) (FoldedOrdering.order o) u (FoldedCoefficientReference.points T)) := by
  have hInv : Function.Involutive β := fun z =>
    congrArg (fun s : Gal(K/k) => s z) (quadraticGalois deg β hne).2
  have hVal := ExceptionalLocalRootCoordinates.involutionPreservesValuation β hInv
  have hCont : Continuous β := continuous_of_normalizedValuation β.toRingHom hVal
  have build := foldedBruhatOfPinning (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.sequence T)
    (FoldedCoefficientReference.descent T) β deg hne hr b hNum hIso
  dsimp only at build
  rw [FoldedCoefficientReference.same_diagram T] at build
  apply build hτ (FoldedGeometry.apartment A) o u hu (FoldedGeometry.signs A) (FoldedGeometry.geometry A)
    (FoldedGeometry.reflection A) (FoldedGeometry.reduced A) (FoldedGeometry.vertices A)
    (FoldedCoefficientReference.points T)
  intro j P hJ B ft iso
  have heq : integerAlgebra B = B.algebra := by
    apply Algebra.algebra_ext
    rintro ⟨z⟩
    exact (map_intCast (integerAlgebra B).algebraMap z).trans (map_intCast B.algebra.algebraMap z).symm
  let _ : @Algebra.FiniteType Integers.{u} B _ _ B.algebra := heq ▸ ft
  exact foldedCompactOpen (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.descent T).data
    β deg hne hCont (FoldedCoefficientReference.points T) j P hJ B iso

private noncomputable def foldLevelOfLocalModel (T : FoldedCoefficientReference R σ β f)
    {A : FoldedApartment (R.diagram σ)} {o : Specs.ExceptionalFoldedRootChart.OrbitOrdering A.direction}
    {u : TransportedOrbit D → D.I → Integers.{u}ˣ}
    (X : FoldedLocalModel (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.descent T) β A o u
      (FoldedCoefficientReference.points T))
    (fixed : ∀ v : GroupPoints R.fibre.realization.pinned.pair.G.val (CommAlgCat.of F K),
      markedFibrePoint R.fibre (CommAlgCat.of F K) v ∈
        ((FoldedLocalModel.terminalPoint X).comp (FoldedCoefficientReference.points T).toMonoidHom).range ↔
      pinnedCoefficientPoint R.fibre (R.pin (R.outer σ)) ((β.restrictScalars F : K ≃ₐ[F] K)) v =
        markedFibrePoint R.fibre (CommAlgCat.of F K) v)
    (hr : ∀ x : k, normalizedValuation K (algebraMap k K x) = normalizedValuation k x ^ 2)
    (hres : Nat.card (residue K) = Nat.card (residue k))
    (S : ClosedSubgroup R.descent.group.val) (hS : IsSubgroupOf S R.descent.torus)
    (hmax : IsMaximalSplitTorus S)
    (hmaxLevel : ∃ h : IsClosedImmersion ((groupBaseChange F k).map S.inclusion).hom.hom.left,
      IsMaximalSplitTorus (Specs.GeometricRadicals.baseChangedSubgroup k S h))
    (hNorm : ∀ x : GroupPoints R.descent.group.val (CommAlgCat.of F k),
      Normalizes S.inclusion x ↔ Normalizes R.descent.torus.inclusion x) :
    FoldedLevel R σ β f A where
  points := (FoldedLocalModel.terminalPoint X).comp (FoldedCoefficientReference.points T).toMonoidHom
  point_eq x := (FoldedLocalModel.point_eq X _).trans (FoldedCoefficientReference.point_eq T x)
  fixed_points := fixed
  ramification := hr
  same_residue := hres
  comparison := FoldedLocalModel.comparison X
  splitTorus := S
  split_subtorus := hS
  maximal := hmax
  maximal_at_level := hmaxLevel
  normalizer x := by
    change x ∈ (FoldedLocalModel.comparison X).localIwahori.normalizer.normalizer ↔ _
    rw [FoldedLocalModel.local_eq X]
    exact (FoldedLocalModel.normalizer X _).trans ((FoldedCoefficientReference.normalizes T x).trans (hNorm x).symm)
  normalizer_torus x := by
    change x ∈ (FoldedLocalModel.comparison X).localIwahori.normalizer.normalizer ↔ _
    rw [FoldedLocalModel.local_eq X]
    exact (FoldedLocalModel.normalizer X _).trans (FoldedCoefficientReference.normalizes T x)
  torus_points x := by
    rw [FoldedLocalModel.local_eq X]
    exact (FoldedLocalModel.torus X _).trans (FoldedCoefficientReference.factorsThrough T x)
  finite_labels := FoldedLocalModel.finite_labels X
  directions := FoldedLocalModel.directions X
  singleton := FoldedLocalModel.singleton X
  pair := FoldedLocalModel.pair X
  affine := FoldedLocalModel.affine X
  translations := FoldedLocalModel.translations X
  range := FoldedLocalModel.range X
  bruhat := FoldedLocalModel.bruhat X
  typeQuotient := FoldedLocalModel.typeQuotient X

private theorem localModel_fixedPoints
    (T : FoldedCoefficientReference R σ β f)
    {A : FoldedApartment (R.diagram σ)} {o : Specs.ExceptionalFoldedRootChart.OrbitOrdering A.direction}
    {u : TransportedOrbit D → D.I → Integers.{u}ˣ}
    (X : FoldedLocalModel (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.descent T) β A o u
      (FoldedCoefficientReference.points T))
    (deg : Module.finrank F L = 2) (hne : σ ≠ 1)
    (a : (L ⊗[F] k) ≃ₐ[F] K)
    (hL : ∀ z : L, a (z ⊗ₜ[F] (1 : k)) = f z)
    (hk : ∀ z : k, a ((1 : L) ⊗ₜ[F] z) = algebraMap k K z)
    (hσ : ∀ z, β (f z) = f (σ z))
    (v : GroupPoints R.fibre.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    markedFibrePoint R.fibre (CommAlgCat.of F K) v ∈
      ((FoldedLocalModel.terminalPoint X).comp (FoldedCoefficientReference.points T).toMonoidHom).range ↔
      pinnedCoefficientPoint R.fibre (R.pin (R.outer σ)) ((β.restrictScalars F : K ≃ₐ[F] K)) v =
        markedFibrePoint R.fibre (CommAlgCat.of F K) v := by
  obtain ⟨j, _, hj, hf⟩ := ramifiedLevelPointEmbedding R σ β deg hne a f hL hk hσ
  have he : (FoldedLocalModel.terminalPoint X).comp (FoldedCoefficientReference.points T).toMonoidHom = j := by
    apply MonoidHom.ext
    intro x
    exact (FoldedLocalModel.point_eq X _).trans ((FoldedCoefficientReference.point_eq T x).trans (hj x).symm)
  rw [he]
  exact hf v

end LocalReference

end FoldedReference

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus MarkedCentralCover)
attribute [local instance] integerAlgebra

universe u

section FoldedCentralTransport

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {G H U V W W' : Type u} [Group G] [Group H] [Group U] [Group V] [Group W] [Group W']
  {j : U →* FieldPoints M K} {j' : V →* FieldPoints M' K}

private theorem centralLocalPreimagesTransport
    (P : LocalIwahori j W) (P' : LocalIwahori j' W')
    (e : G ≃* U) (e' : H ≃* V) (φ : G →* H) (ψ : U →* V) (hψ : ∀ g, e' (φ g) = ψ (e g)) :
    let T := (integralUnitTorus (K := K) M).comap j
    let T' := (integralUnitTorus (K := K) M').comap j'
    let B := comapLocalIwahori P e
    let B' := comapLocalIwahori P' e'
    P'.iwahori.comap ψ = P.iwahori →
    (∀ h, h ∈ P'.iwahori ↔ ∃ (g : P.iwahori) (t : T'), h = ψ g * t) →
    P'.normalizer.normalizer.comap ψ = P.normalizer.normalizer →
    T'.comap ψ = T → P'.normalizer.torus.comap ψ = P.normalizer.torus → ψ.range.Normal →
    B'.iwahori.comap φ = B.iwahori ∧
    (∀ h, h ∈ B'.iwahori ↔ ∃ (g : B.iwahori) (t : T'.comap e'.toMonoidHom), h = φ g * t) ∧
    B'.normalizer.normalizer.comap φ = B.normalizer.normalizer ∧
    (T'.comap e'.toMonoidHom).comap φ = T.comap e.toMonoidHom ∧
    B'.normalizer.torus.comap φ = B.normalizer.torus ∧ φ.range.Normal := by
  intro T T' B B' hI hProd hN hU hT hNorm
  have hpre (S : Subgroup V) : (S.comap e'.toMonoidHom).comap φ = (S.comap ψ).comap e.toMonoidHom := by
    ext x
    change e' (φ x) ∈ S ↔ ψ (e x) ∈ S
    rw [hψ]
  have hRange : φ.range = ψ.range.comap e'.toMonoidHom := by
    ext h
    change (∃ g, φ g = h) ↔ ∃ g, ψ g = e' h
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, (hψ g).symm⟩
    · rintro ⟨g, hg⟩
      obtain ⟨x, rfl⟩ := e.surjective g
      exact ⟨x, e'.injective ((hψ x).trans hg)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hRange.symm ▸ hNorm.comap e'.toMonoidHom⟩
  · change (P'.iwahori.comap e'.toMonoidHom).comap φ = P.iwahori.comap e.toMonoidHom
    rw [hpre, hI]
  · intro h
    change e' h ∈ P'.iwahori ↔ _
    rw [hProd]
    constructor
    · rintro ⟨g, t, ht⟩
      let g' : B.iwahori := ⟨e.symm g, by
        change e (e.symm g) ∈ P.iwahori
        rw [MulEquiv.apply_symm_apply]
        exact g.property⟩
      let t' : T'.comap e'.toMonoidHom := ⟨e'.symm t, by
        change e' (e'.symm t) ∈ T'
        rw [MulEquiv.apply_symm_apply]
        exact t.property⟩
      refine ⟨g', t', e'.injective ?_⟩
      rw [map_mul, hψ]
      change e' h = ψ (e (e.symm g)) * e' (e'.symm t)
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact ht
    · rintro ⟨g, t, rfl⟩
      refine ⟨⟨e g, g.property⟩, ⟨e' t, t.property⟩, ?_⟩
      rw [map_mul, hψ]
  · change (P'.normalizer.normalizer.comap e'.toMonoidHom).comap φ = P.normalizer.normalizer.comap e.toMonoidHom
    rw [hpre, hN]
  · rw [hpre, hU]
  · change (P'.normalizer.torus.comap e'.toMonoidHom).comap φ = P.normalizer.torus.comap e.toMonoidHom
    rw [hpre, hT]

set_option backward.isDefEq.respectTransparency false in
private theorem centralLocalLabelsTransport
    (P : LocalIwahori j W) (P' : LocalIwahori j' W')
    (e : G ≃* U) (e' : H ≃* V) (φ : G →* H) (ψ : U →* V) (hψ : ∀ g, e' (φ g) = ψ (e g))
    (q : W →* D.datum.weylGroup) (q' : W' →* E.datum.weylGroup)
    (d : D.datum.weylGroup ≃* E.datum.weylGroup) (c : MarkedCentralCover M M')
    (hlabel : ∀ (n : P.normalizer.normalizer) (n' : P'.normalizer.normalizer), (n' : V) = ψ n →
      q' (P'.normalizer.label n') = d (q (P.normalizer.label n)) ∧
      (P'.normalizer.translation (P'.normalizer.torusPart n')).toAdd =
        c.pushCocharacter (P.normalizer.translation (P.normalizer.torusPart n)).toAdd) :
    let N := (comapLocalIwahori P e).normalizer
    let N' := (comapLocalIwahori P' e').normalizer
    ∀ (n : N.normalizer) (n' : N'.normalizer), (n' : H) = φ n →
      q' (N'.label n') = d (q (N.label n)) ∧
      (N'.translation (N'.torusPart n')).toAdd = c.pushCocharacter (N.translation (N.torusPart n)).toAdd := by
  intro N N' n n' hn
  let x := subgroupComapEquiv e P.normalizer.normalizer n
  let x' := subgroupComapEquiv e' P'.normalizer.normalizer n'
  obtain ⟨hl, ht⟩ := hlabel x x' ((congrArg e' hn).trans (hψ n))
  refine ⟨hl, ?_⟩
  change (P'.normalizer.translation (subgroupComapEquiv e' P'.normalizer.torus (N'.torusPart n'))).toAdd =
    c.pushCocharacter (P.normalizer.translation (subgroupComapEquiv e P.normalizer.torus (N.torusPart n))).toAdd
  have hn := comapMarkedLocalNormalizer_torusPart P.normalizer e (show (comapMarkedLocalNormalizer P.normalizer e).normalizer from n)
  have hn' := comapMarkedLocalNormalizer_torusPart P'.normalizer e' (show (comapMarkedLocalNormalizer P'.normalizer e').normalizer from n')
  change _ = P.normalizer.torusPart x at hn
  change _ = P'.normalizer.torusPart x' at hn'
  calc
    _ = (P'.normalizer.translation (P'.normalizer.torusPart x')).toAdd :=
      congrArg (fun t : P'.normalizer.torus => (P'.normalizer.translation t).toAdd) hn'
    _ = c.pushCocharacter (P.normalizer.translation (P.normalizer.torusPart x)).toAdd := ht
    _ = _ := congrArg (fun t : P.normalizer.torus => c.pushCocharacter (P.normalizer.translation t).toAdd) hn.symm

end FoldedCentralTransport

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum BasedIso)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalValuedTorusNormalizer (fixedWeylGroup invariantApartment)
attribute [local instance] integerAlgebra

universe u

section FoldedCentralCore

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {τ : BasedIso D D} {τ' : BasedIso E E} {A : FoldedApartment τ} {A' : FoldedApartment τ'}
  {G H : Type u} [Group G] [Group H] {j : G →* FieldPoints M K} {j' : H →* FieldPoints M' K}

set_option backward.isDefEq.respectTransparency false in
private theorem foldedCentralComparison (c : MarkedCentralCover M M')
    (C : LocalComparison (j := j) (Wf := fixedWeylGroup D τ) A.roots A.basepoint)
    (C' : LocalComparison (j := j') (Wf := fixedWeylGroup E τ') A'.roots A'.basepoint)
    (hDir : C.chart.direction = A.direction) (hDir' : C'.chart.direction = A'.direction)
    (e₀ : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (e : invariantApartment D τ ≃ₗ[ℚ] invariantApartment E τ')
    (d : FoldedRootDirection ≃ FoldedRootDirection)
    (he₀ : e₀.toLinearMap = c.pushCocharacter.baseChange ℚ) (he : ∀ x, (e x).val = e₀ x.val)
    (hR₀ : ∀ a x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv a) (e₀ x) =
      (ApartmentRoots.split D.datum ℚ).root a x)
    (hC₀ : ∀ a, e₀ ((ApartmentRoots.split D.datum ℚ).coroot a) =
      (ApartmentRoots.split E.datum ℚ).coroot (c.rootEquiv a))
    (hAlcove : e '' A.roots.alcove A.basepoint = A'.roots.alcove A'.basepoint)
    (hDirMap : ∀ i, d (A.direction i) = A'.direction (c.rootEquiv i))
    (hRoot : ∀ a x, A'.roots.root (d a) (e x) = A.roots.root a x)
    (hCoroot : ∀ a, e (A.roots.coroot a) = A'.roots.coroot (d a))
    (hRange : C.affine.range = A.roots.affineWeylGroup)
    (hA : ∀ n x, (C.affine n x).val = (C.localIwahori.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (C.localIwahori.normalizer.translation (C.localIwahori.normalizer.torusPart n)).toAdd))
    (hA' : ∀ n x, (C'.affine n x).val = (C'.localIwahori.normalizer.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (C'.localIwahori.normalizer.translation (C'.localIwahori.normalizer.torusPart n)).toAdd))
    (φ : G →* H) (hφ : ∀ g, j' (φ g) = integralPointHom c.map (integralRing K) (j g))
    (hI : C'.I.comap φ = C.I) (hIprod : ∀ h, h ∈ C'.I ↔ ∃ (g : C.I) (t : C'.T₀), h = φ g * t)
    (hN : C'.N.comap φ = C.N) (hU : C'.T₀.comap φ = C.T₀)
    (hT : C'.localIwahori.normalizer.torus.comap φ = C.localIwahori.normalizer.torus)
    (hNormal : φ.range.Normal) (f : D.datum.weylGroup ≃* E.datum.weylGroup)
    (hf : ∀ i, f (RootPairing.weylGroup.ofIdx D.datum i) = RootPairing.weylGroup.ofIdx E.datum (c.rootEquiv i))
    (hNlabel : ∀ (n : C.N) (n' : C'.N), (n' : H) = φ n →
      (C'.localIwahori.normalizer.label n').val = f (C.localIwahori.normalizer.label n).val ∧
      (C'.localIwahori.normalizer.translation (C'.localIwahori.normalizer.torusPart n')).toAdd =
        c.pushCocharacter (C.localIwahori.normalizer.translation (C.localIwahori.normalizer.torusPart n)).toAdd) :
    CentralComparison c φ C C' e := by
  have haff (n : C.N) (n' : C'.N) (hn : (n' : H) = φ n) (x : invariantApartment D τ) :
      e (C.affine n x) = C'.affine n' (e x) := by
    obtain ⟨hl, ht⟩ := hNlabel n n' hn
    apply Subtype.ext
    rw [he, hA, hA', hl, ht, he, map_add]
    have htranslate (z : D.Y) : e₀ ((1 / 2 : ℚ) ⊗ₜ[ℤ] z) = (1 / 2 : ℚ) ⊗ₜ[ℤ] c.pushCocharacter z := by
      change e₀.toLinearMap _ = _
      rw [he₀]
      rfl
    rw [htranslate]
    exact congrArg (· + _) (linearActions_ofRootComparison c e₀ f hf hR₀ hC₀
      (C.localIwahori.normalizer.label n).val x.val)
  have hIsup : C'.I = C.I.map φ ⊔ C'.T₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, t, rfl⟩ := (hIprod x).1 hx
      exact mul_mem ((le_sup_left : C.I.map φ ≤ C.I.map φ ⊔ C'.T₀) ⟨y, y.property, rfl⟩)
        ((le_sup_right : C'.T₀ ≤ C.I.map φ ⊔ C'.T₀) t.property)
    · refine sup_le ?_ (unitTorus_le_iwahori C')
      rw [Subgroup.map_le_iff_le_comap, hI]
  have hOrd := ordinarySubgroup_ofCentralComparison C C' φ hNormal hIsup hN hRange e d hRoot hCoroot haff
  refine ⟨hφ, hI, hIprod, hN, hU, hT, haff, hOrd.2.2, hAlcove, d, ?_, hRoot, hCoroot⟩
  intro i
  rw [hDir, hDir', hDirMap]

end FoldedCentralCore

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection)
open Specs.ExceptionalFoldedRootChart (OrbitOrdering)
open Specs.ExceptionalMarkedRootDescent (TransportedOrbit)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment fixedWeylGroup)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom integralUnitTorus)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori)
open Specs.AdjointRepresentation (GroupPoints)
attribute [local instance] integerAlgebra

universe u

section FoldedCentralLevel

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
  [FiniteDimensional k K] [IsGalois k K]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {R : RamifiedReference F L M} {R' : RamifiedReference F L M'}
  {σ : Gal(L/F)} {β : Gal(K/k)} {f : L →ₐ[F] K}
  {A : FoldedApartment (R.diagram σ)} {A' : FoldedApartment (R'.diagram σ)}
  {o : OrbitOrdering A.direction} {o' : OrbitOrdering A'.direction}
  {u : TransportedOrbit D → D.I → Integers.{u}ˣ} {u' : TransportedOrbit E → E.I → Integers.{u}ˣ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem foldedCentralLevel (c : MarkedCentralCover M M')
    (T : FoldedCoefficientReference R σ β f) (T' : FoldedCoefficientReference R' σ β f)
    (X : FoldedLocalModel (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.descent T) β A o u
      (FoldedCoefficientReference.points T))
    (X' : FoldedLocalModel (FoldedCoefficientReference.fibre T') (FoldedCoefficientReference.descent T') β A' o' u'
      (FoldedCoefficientReference.points T'))
    (deg : Module.finrank k K = 2) (hne : β ≠ 1) (hE : E.datum.rootSpan ℤ = ⊤)
    (hs : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (hs' : ∀ i j, E.datum.pairing i j = E.datum.pairing j i)
    (hdgm : ∀ i, c.rootEquiv ((R.diagram σ).val.indexEquiv i) = (R'.diagram σ).val.indexEquiv (c.rootEquiv i))
    (e₀ : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (e : invariantApartment D (R.diagram σ) ≃ₗ[ℚ] invariantApartment E (R'.diagram σ))
    (d : FoldedRootDirection ≃ FoldedRootDirection)
    (he₀ : e₀.toLinearMap = c.pushCocharacter.baseChange ℚ) (he : ∀ x, (e x).val = e₀ x.val)
    (hR₀ : ∀ a x, (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv a) (e₀ x) =
      (ApartmentRoots.split D.datum ℚ).root a x)
    (hC₀ : ∀ a, e₀ ((ApartmentRoots.split D.datum ℚ).coroot a) =
      (ApartmentRoots.split E.datum ℚ).coroot (c.rootEquiv a))
    (hAlcove : e '' A.roots.alcove A.basepoint = A'.roots.alcove A'.basepoint)
    (hDirMap : ∀ i, d (A.direction i) = A'.direction (c.rootEquiv i))
    (hRoot : ∀ a x, A'.roots.root (d a) (e x) = A.roots.root a x)
    (hCoroot : ∀ a, e (A.roots.coroot a) = A'.roots.coroot (d a))
    (φ : GroupPoints R.descent.group.val (CommAlgCat.of F k) →* GroupPoints R'.descent.group.val (CommAlgCat.of F k))
    (hφ : ∀ g, (FoldedLocalModel.terminalPoint X') (FoldedCoefficientReference.points T' (φ g)) =
      integralPointHom c.map (integralRing K) ((FoldedLocalModel.terminalPoint X) (FoldedCoefficientReference.points T g))) :
    CentralComparison c φ (FoldedLocalModel.comparison X) (FoldedLocalModel.comparison X') e := by
  let eG := FoldedCoefficientReference.points T
  let eH := FoldedCoefficientReference.points T'
  let j := FoldedLocalModel.terminalPoint X
  let j' := FoldedLocalModel.terminalPoint X'
  let P := FoldedLocalModel.terminalIwahori X
  let P' := FoldedLocalModel.terminalIwahori X'
  let C := FoldedLocalModel.comparison X
  let C' := FoldedLocalModel.comparison X'
  let ψ := eH.toMonoidHom.comp (φ.comp eG.symm.toMonoidHom)
  have hψ (g : _) : j' (ψ g) = integralPointHom c.map (integralRing K) (j g) := by
    have h := hφ (eG.symm g)
    change j' (ψ g) = integralPointHom c.map (integralRing K) (j (eG (eG.symm g))) at h
    rw [eG.apply_symm_apply] at h
    exact h
  have hcompat (g : _) : eH (φ g) = ψ (eG g) := by
    change _ = eH (φ (eG.symm (eG g)))
    rw [eG.symm_apply_apply]
  have hCEq : C.localIwahori = comapLocalIwahori P eG := FoldedLocalModel.local_eq X
  have hCEq' : C'.localIwahori = comapLocalIwahori P' eH := FoldedLocalModel.local_eq X'
  have hWord (w : fixedWeylGroup D (R.diagram σ)) :
      ((P.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val := by
    have h := (FoldedLocalModel.finite_labels X).2.choose_spec.2 w
    change ((C.localIwahori.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val at h
    rw [hCEq] at h
    exact h
  have hWord' (w : fixedWeylGroup E (R'.diagram σ)) :
      ((P'.normalizer.word w).map (RootPairing.weylGroup.ofIdx E.datum)).prod = w.val := by
    have h := (FoldedLocalModel.finite_labels X').2.choose_spec.2 w
    change ((C'.localIwahori.normalizer.word w).map (RootPairing.weylGroup.ofIdx E.datum)).prod = w.val at h
    rw [hCEq'] at h
    exact h
  have hj' : Function.Injective j' := by
    intro a b h
    have hJ : Function.Injective (j'.comp eH.toMonoidHom) := C'.point_injective
    have he : eH.symm a = eH.symm b := hJ (by
      change j' (eH (eH.symm a)) = j' (eH (eH.symm b))
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, h])
    exact eH.symm.injective he
  have hLocal := ExceptionalPinnedCentralCover.pinnedCentralLocalComparison c
    (FoldedCoefficientReference.fibre T) (FoldedCoefficientReference.fibre T')
    (FoldedCoefficientReference.descent T) (FoldedCoefficientReference.descent T') β hE
    (FoldedCoefficientReference.sequence T) (FoldedCoefficientReference.sequence T') deg hne hs hs'
  dsimp only at hLocal
  rw [FoldedCoefficientReference.same_diagram T, FoldedCoefficientReference.same_diagram T'] at hLocal
  obtain ⟨hI, hProd, hN, hT, hU, hNorm, w, hw, hlabel⟩ :=
    hLocal hdgm j j' hj' (FoldedLocalModel.point_eq X) (FoldedLocalModel.point_eq X') P P'
      (FoldedLocalModel.normalizer X) (FoldedLocalModel.normalizer X')
      (FoldedLocalModel.torus X) (FoldedLocalModel.torus X')
      (FoldedLocalModel.words X) (FoldedLocalModel.words X') hWord hWord' ψ hψ
  obtain ⟨hI₁, hProd₁, hN₁, hU₁, hT₁, hNorm₁⟩ :=
    centralLocalPreimagesTransport P P' eG eH φ ψ hcompat hI hProd hN hU hT hNorm
  have hlabel₁ := centralLocalLabelsTransport P P' eG eH φ ψ hcompat
    (fixedWeylGroup D (R.diagram σ)).subtype (fixedWeylGroup E (R'.diagram σ)).subtype w c hlabel
  refine foldedCentralComparison c C C' (FoldedLocalModel.directions X) (FoldedLocalModel.directions X')
    e₀ e d he₀ he hR₀ hC₀ hAlcove hDirMap hRoot hCoroot (FoldedLocalModel.range X)
    (FoldedLocalModel.affine X) (FoldedLocalModel.affine X') φ hφ ?_ ?_ ?_ hU₁ ?_ hNorm₁ w hw ?_
  · change C'.localIwahori.iwahori.comap φ = C.localIwahori.iwahori
    rw [hCEq, hCEq']
    exact hI₁
  · change ∀ h, h ∈ C'.localIwahori.iwahori ↔ ∃ (g : C.localIwahori.iwahori) (t : C'.T₀), h = φ g * t
    rw [hCEq, hCEq']
    exact hProd₁
  · change C'.localIwahori.normalizer.normalizer.comap φ = C.localIwahori.normalizer.normalizer
    rw [hCEq, hCEq']
    exact hN₁
  · change C'.localIwahori.normalizer.torus.comap φ = C.localIwahori.normalizer.torus
    rw [hCEq, hCEq']
    exact hT₁
  · let labelComparison
        (B : LocalIwahori (j.comp eG.toMonoidHom) (fixedWeylGroup D (R.diagram σ)))
        (B' : LocalIwahori (j'.comp eH.toMonoidHom) (fixedWeylGroup E (R'.diagram σ))) : Prop :=
        ∀ (n : B.normalizer.normalizer) (n' : B'.normalizer.normalizer), (n' : _) = φ n →
          (B'.normalizer.label n').val = w (B.normalizer.label n).val ∧
          (B'.normalizer.translation (B'.normalizer.torusPart n')).toAdd =
            c.pushCocharacter (B.normalizer.translation (B.normalizer.torusPart n)).toAdd
    change labelComparison C.localIwahori C'.localIwahori
    rw [hCEq, hCEq']
    exact hlabel₁

end FoldedCentralLevel

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalFoldedRootChart (OrbitOrdering)
open Specs.ExceptionalMarkedRootDescent (TransportedOrbit)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex normalizedValuation residueMap)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriCongruence (integralRingMap)
open ValuativeRel WithZero
open private normalizedValuation_algebraMap_exp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
attribute [local instance] integerAlgebra

universe u

section CoefficientActions

variable {F k : Type u} [Field F] [Field k] [Algebra F k]

private noncomputable def coefficientAutomorphisms (G : GroupScheme F) :
    Gal(k/F) →* MulAut (GroupPoints G (CommAlgCat.of F k)) where
  toFun g := (((groupPointsFunctor F).obj G).mapIso (CommAlgCat.isoMk g)).groupIsoToMulEquiv
  map_one' := by
    ext x
    change coefficientPoints G (AlgHom.id F k) x = x
    change (((groupPointsFunctor F).obj G).map (𝟙 (CommAlgCat.of F k))).hom x = x
    exact ConcreteCategory.congr_hom (((groupPointsFunctor F).obj G).map_id (CommAlgCat.of F k)) x
  map_mul' g h := by
    ext x
    change coefficientPoints G ((g * h).toAlgHom) x = coefficientPoints G g.toAlgHom (coefficientPoints G h.toAlgHom x)
    change _ = _
    have he : (g * h).toAlgHom = g.toAlgHom.comp h.toAlgHom := rfl
    simp only [coefficientPoints, he, CommAlgCat.ofHom_comp, Functor.map_comp]
    rfl

end CoefficientActions

section FoldedScalarLevels

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeExtension F L] [ValuativeExtension F k] [FiniteDimensional F L] [IsGalois F L]
  [FiniteDimensional F k]
  {D : BasedRootDatum.{u}} {M : Model D}
  {R : RamifiedReference F L M} {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

private theorem diagramCompositum_ramification (T : DiagramCompositum F L k σ)
    (deg : Module.finrank F L = 2) (hr : 1 < ramificationIndex F L) (hu : IsUnramifiedLocalExtension F k) :
    1 < ramificationIndex k T.field := by
  obtain ⟨_, hRam, _⟩ := ExceptionalLocalRootCoordinates.ramifiedQuadratic F L deg hr
  obtain ⟨π, hπ⟩ := (ExceptionalIwahoriCongruence.localValuationNormalization F).1 (exp (-1))
  change normalizedValuation F π = exp (-1) at hπ
  have hn : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have h : exp (ramificationIndex k T.field * (-1)) = exp (-2 : ℤ) := by
    calc
      _ = normalizedValuation T.field (algebraMap k T.field (algebraMap F k π)) := by
        rw [normalizedValuation_algebraMap_exp (F := k) (L := T.field)
          ((map_ne_zero (algebraMap F k)).2 hn), hu π, hπ, log_exp]
      _ = normalizedValuation T.field (algebraMap L T.field (algebraMap F L π)) := by
        rw [← IsScalarTower.algebraMap_apply F k, ← IsScalarTower.algebraMap_apply F L]
      _ = _ := by rw [T.unramified _, hRam, hπ, sq, ← exp_add]; rfl
  have h := exp_injective h
  omega

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem foldedScalarAtExtension (T : DiagramCompositum F L k σ)
    (X : FoldedLevel R σ σ (AlgHom.id F L) A)
    (Y : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (h : IsUnramifiedLocalExtension F k)
    (o : OrbitOrdering A.direction) (u : TransportedOrbit D → D.I → Integers.{u}ˣ)
    (hX : ∃ h hx, X.comparison.chart = foldedRootChart A o u σ X.points h hx)
    (hY : ∃ h hx, Y.comparison.chart = foldedRootChart A o u T.diagram Y.points h hx)
    (hword : ∀ w, ∀ i ∈ X.comparison.localIwahori.normalizer.word w, i ∈ D.base.support)
    (hword' : ∀ w, ∀ i ∈ Y.comparison.localIwahori.normalizer.word w, i ∈ D.base.support) :
    let s := coefficientPoints R.descent.group.val (Algebra.ofId F k)
    ScalarComparison (algebraMap L T.field) s X.comparison Y.comparison ∧
    TypeQuotientTransport X.typeQuotient Y.typeQuotient s (MonoidHom.id _) := by
  intro s
  let f := IsScalarTower.toAlgHom F L T.field
  let g := IsScalarTower.toAlgHom F k T.field
  have hs (x : _) : Y.points (s x) = scalarPoints M (algebraMap L T.field) (X.points x) := by
    rw [Y.point_eq, X.point_eq]
    exact (ramifiedPoint_natural R (AlgHom.id F L) (Algebra.ofId F L) f g (Algebra.ofId F k) f
      (AlgHom.comp_id f) (by apply AlgHom.ext; intro x; exact (f.commutes x).trans (g.commutes x).symm) x).symm
  have hNT := ExceptionalValuedScalarTransport.torusConditionsScalar R.descent.group.val R.descent.torus
    (Algebra.ofId F k)
  have hN : Y.comparison.N.comap s = X.comparison.N := by
    ext x
    change s x ∈ Y.comparison.N ↔ x ∈ X.comparison.N
    rw [Y.normalizer_torus, X.normalizer_torus]
    exact (hNT x).1
  have hT : Y.comparison.localIwahori.normalizer.torus.comap s = X.comparison.localIwahori.normalizer.torus := by
    ext x
    change s x ∈ Y.comparison.localIwahori.normalizer.torus ↔ x ∈ X.comparison.localIwahori.normalizer.torus
    rw [Y.torus_points, X.torus_points]
    exact (hNT x).2
  have hData := foldedSubgroupsScalar X.comparison Y.comparison X.finite_labels Y.finite_labels
    hword hword' X.range Y.range X.affine Y.affine (algebraMap L T.field) s T.unramified hs hN hT
  refine ⟨foldedScalarComparison X.comparison Y.comparison o u σ T.diagram hX hY
    (algebraMap F k) (algebraMap L T.field) s h T.unramified ?_ ?_ hs hData, ?_⟩
  · intro x
    rw [← IsScalarTower.algebraMap_apply F L, ← IsScalarTower.algebraMap_apply F k]
  · intro x
    exact (T.diagram_extends x).symm
  · exact foldedTypeQuotientScalar X.comparison Y.comparison X.typeQuotient Y.typeQuotient s hN
      (fun n n' hn => (hData.2.2.2.2.2.2.1 n n' hn).1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
private theorem foldedCoefficientActions (T : DiagramCompositum F L k σ)
    (Y : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (hword : ∀ w, ∀ i ∈ Y.comparison.localIwahori.normalizer.word w, i ∈ D.base.support) :
    Y.Coefficients T := by
  let G := R.descent.group.val
  let a := coefficientAutomorphisms (k := k) G
  have ha (b : Gal(k/F)) (x : GroupPoints G (CommAlgCat.of F k)) : a b x = coefficientPoints G b.toAlgHom x := rfl
  let f := IsScalarTower.toAlgHom F L T.field
  let g := IsScalarTower.toAlgHom F k T.field
  have hpoint (b : Gal(k/F)) (x : GroupPoints G (CommAlgCat.of F k)) :
      Y.points (a b x) = scalarPoints M (T.coefficient b).toRingHom (Y.points x) := by
    let t := (T.coefficient b).restrictScalars F
    have hL : t.toAlgHom.comp f = f := by
      ext u
      exact (T.coefficient b).commutes u
    have hk : t.toAlgHom.comp g = g.comp b.toAlgHom := by
      ext u
      exact T.coefficient_extends b u
    rw [ha, Y.point_eq, Y.point_eq]
    exact (ramifiedPoint_natural R f g f g b.toAlgHom t.toAlgHom hL hk x).symm
  refine ⟨a, ha, hpoint, ?_⟩
  intro b
  let s := (a b).toMonoidHom
  have hSub := ExceptionalValuedScalarTransport.torusConditionsScalar G R.descent.torus b.toAlgHom
  have hN : Y.comparison.N.comap s = Y.comparison.N := by
    ext x
    change a b x ∈ Y.comparison.N ↔ x ∈ Y.comparison.N
    rw [Y.normalizer_torus, Y.normalizer_torus, ha]
    exact (hSub x).1
  have hT : Y.comparison.localIwahori.normalizer.torus.comap s = Y.comparison.localIwahori.normalizer.torus := by
    ext x
    change a b x ∈ Y.comparison.localIwahori.normalizer.torus ↔ x ∈ Y.comparison.localIwahori.normalizer.torus
    rw [Y.torus_points, Y.torus_points, ha]
    exact (hSub x).2
  let _ : FiniteDimensional F T.field := FiniteDimensional.trans F k T.field
  let _ : FiniteDimensional L T.field := Module.Finite.of_restrictScalars_finite F L T.field
  obtain ⟨hI, _, hU, hG, _, _, hLabels, hLifts⟩ :=
    foldedSubgroupsScalar Y.comparison Y.comparison Y.finite_labels Y.finite_labels hword hword
      Y.range Y.range Y.affine Y.affine (T.coefficient b).toRingHom s
      (normalizedValuation_unramifiedAut T.unramified (T.coefficient b)) (hpoint b) hN hT
  refine ⟨⟨map_eq_of_comap_eq (a b) Y.comparison.I hI, map_eq_of_comap_eq (a b) Y.comparison.N hN,
    map_eq_of_comap_eq (a b) Y.comparison.T₀ hU, map_eq_of_comap_eq (a b) Y.comparison.G₀ hG,
    map_eq_of_comap_eq (a b) Y.comparison.localIwahori.normalizer.torus hT, by simp, ?_, ?_⟩,
    foldedTypeQuotientScalar Y.comparison Y.comparison Y.typeQuotient Y.typeQuotient s hN
      (fun n n' hn => (hLabels n n' hn).1)⟩
  · intro n n' he
    simpa only [one_mul, inv_one, mul_one] using (hLabels n n' he).1
  · intro w
    exact ⟨w, by simp, hLifts w⟩

end FoldedScalarLevels

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineRootSystems (e6Partner)
open Specs.ExceptionalFoldedRootChart (OrbitOrdering IsTransportUnitSystem)
open Specs.ExceptionalMarkedRootDescent (TransportedOrbit SimpleRootOrbit transportedRootPoint markedRootPoint weylWordPerm)
open Specs.ExceptionalValuedTorusNormalizer (fixedWeylGroup invariantApartment)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom MarkedCentralCover pointHom)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalLocalRootCoordinates (ramificationIndex normalizedValuation)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalPinnedBaseChange (ExtendsDiagram)
attribute [local instance] integerAlgebra

universe u

section RamifiedBruhat

private theorem integralOrbitTransportUnits {D : BasedRootDatum.{u}} (M : Model D) :
    ∃ c : TransportedOrbit D → D.I → Integers.{u}ˣ, IsTransportUnitSystem M.toIntegralMarking c := by
  obtain ⟨c, hc⟩ := ExceptionalMarkedRootDescent.transportedIntegralCoordinates M
  refine ⟨c, ?_⟩
  intro S b a z
  have hscalar (n : Integers.{u}) : (integerAlgebra S).algebraMap n = S.algebra.algebraMap n := by
    rcases n with ⟨n⟩
    exact (map_intCast (integerAlgebra S).algebraMap n).trans (map_intCast S.algebra.algebraMap n).symm
  change _ = markedRootPoint M.toIntegralMarking S (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) a)
    ((integerAlgebra S).algebraMap (c b a : Integers.{u}) * z)
  rw [hscalar]
  exact hc S b a z

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- Affine Bruhat comparison for the two marked ramified quadratic forms,
with the central morphism and every finite unramified coefficient level. -/
theorem ramifiedAffineBruhatComparison : RamifiedAffineBruhatComparison.{u} := by
  classical
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ σ deg hne hr D E M M' c b b' hD hE hsc had R R' τ τ' hτ hτ' hDiag
  obtain ⟨G, G', e₀, e, d, he₀, he, hp, hR₀, hC₀, hAlcove, hDir, hRoot, hCoroot⟩ :=
    foldedCentralApartments c b b' hD hE τ τ' hτ hτ' hDiag
  let A := FoldedGeometry.apartment G
  let A' := FoldedGeometry.apartment G'
  obtain ⟨o⟩ := foldedOrdering b A hD hτ
  obtain ⟨o'⟩ := foldedOrdering b' A' hE hτ'
  obtain ⟨u, hu₀⟩ := integralOrbitTransportUnits M
  obtain ⟨u', hu₀'⟩ := integralOrbitTransportUnits M'
  have hIso : D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤ := Or.inl hsc
  have hIso' : E.datum.corootSpan ℤ = ⊤ ∨ E.datum.rootSpan ℤ = ⊤ := Or.inr had
  obtain ⟨S, hS, hMax, _, _, hLevels⟩ := ExceptionalPinnedBaseChange.splitTorusAtLevels
    R.fibre R.descent σ R.sequence deg hne hIso
  obtain ⟨S', hS', hMax', _, _, hLevels'⟩ := ExceptionalPinnedBaseChange.splitTorusAtLevels
    R'.fibre R'.descent σ R'.sequence deg hne hIso'
  have hCentral := ExceptionalPinnedCentralCover.descendedCentralMap c R.fibre R'.fibre
    R.descent R'.descent σ had R.sequence R'.sequence deg hne
  dsimp only at hCentral
  rw [R.descent.outer_eq, R'.descent.outer_eq] at hCentral
  obtain ⟨φ, hisog, hφ⟩ := hCentral hDiag
  have hSym := (e6LocalRootSymmetries D b τ hD hτ).2.2
  have hSym' := (e6LocalRootSymmetries E b' τ' hE hτ').2.2
  obtain ⟨J⟩ := foldedBaseReference R σ
  obtain ⟨J'⟩ := foldedBaseReference R' σ
  obtain ⟨X₀⟩ := foldedReferenceLocalModel J deg hne hr b hD hIso hτ G o u hu₀
  obtain ⟨X₀'⟩ := foldedReferenceLocalModel J' deg hne hr b' hE hIso' hτ' G' o' u' hu₀'
  obtain ⟨_, hram, hres⟩ := ExceptionalLocalRootCoordinates.ramifiedQuadratic F L deg hr
  have hRes : Nat.card (residue L) = Nat.card (residue F) :=
    (Nat.card_congr (Equiv.ofBijective _ hres)).symm
  let T₀ : (L ⊗[F] F) ≃ₐ[F] L := (Algebra.TensorProduct.rid F L L).restrictScalars F
  have hL₀ (z : L) : T₀ (z ⊗ₜ[F] (1 : F)) = z := by
    change Algebra.TensorProduct.rid F L L (z ⊗ₜ[F] (1 : F)) = _
    rw [Algebra.TensorProduct.rid_tmul, one_smul]
  have hk₀ (z : F) : T₀ ((1 : L) ⊗ₜ[F] z) = algebraMap F L z := by
    change Algebra.TensorProduct.rid F L L ((1 : L) ⊗ₜ[F] z) = _
    rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
  have hσ₀ : ExtendsDiagram F L F L σ σ T₀ :=
    ⟨hk₀, fun z => by rw [hL₀, hL₀]⟩
  obtain ⟨hcl, hMaxF, hNormF⟩ := hLevels F L deg σ hne T₀ hσ₀
  obtain ⟨hcl', hMaxF', hNormF'⟩ := hLevels' F L deg σ hne T₀ hσ₀
  let X := foldLevelOfLocalModel J X₀
    (localModel_fixedPoints J X₀ deg hne T₀ hL₀ hk₀ (fun _ => rfl))
    hram hRes S hS hMax ⟨hcl, hMaxF⟩ hNormF
  let X' := foldLevelOfLocalModel J' X₀'
    (localModel_fixedPoints J' X₀' deg hne T₀ hL₀ hk₀ (fun _ => rfl))
    hram hRes S' hS' hMax' ⟨hcl', hMaxF'⟩ hNormF'
  let φX := pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F F)))
  have hPointφ (g : _) : X'.points (φX g) = integralPointHom c.map (integralRing L) (X.points g) := by
    rw [X'.point_eq, X.point_eq]
    exact descendedCentralPointSquare R R' c φ hφ (AlgHom.id F L) (Algebra.ofId F L) g
  have hX : CentralComparison c φX X.comparison X'.comparison e :=
    foldedCentralLevel c J J' X₀ X₀' deg hne had hSym hSym' hDiag e₀ e d he₀ he hR₀ hC₀
      hAlcove hDir hRoot hCoroot φX hPointφ
  refine ⟨A, A', e, φ, X, X', fun x => (he x).trans (LinearMap.congr_fun he₀ x.val), hp, hisog, hX, ?_⟩
  intro k _ _ _ _ _ _ _ hk
  obtain ⟨T⟩ := diagramCompositum_exists σ hne deg hr hk
  let K := T.field
  let f := IsScalarTower.toAlgHom F L T.field
  obtain ⟨Q⟩ := foldedCompositumReference R σ deg hne hIso T
  obtain ⟨Q'⟩ := foldedCompositumReference R' σ deg hne hIso' T
  have hramT := diagramCompositum_ramification T deg hr hk
  obtain ⟨Y₀⟩ := foldedReferenceLocalModel Q T.degree T.diagram_ne hramT b hD hIso hτ G o u hu₀
  obtain ⟨Y₀'⟩ := foldedReferenceLocalModel Q' T.degree T.diagram_ne hramT b' hE hIso' hτ' G' o' u' hu₀'
  obtain ⟨_, hrK, hresK⟩ := ExceptionalLocalRootCoordinates.ramifiedQuadratic k T.field T.degree hramT
  have hResK : Nat.card (residue T.field) = Nat.card (residue k) :=
    (Nat.card_congr (Equiv.ofBijective _ hresK)).symm
  obtain ⟨hclK, hMaxK, hNormK⟩ := hLevels k T.field T.degree T.diagram T.diagram_ne T.tensor (diagramCompositum_extends T)
  obtain ⟨hclK', hMaxK', hNormK'⟩ := hLevels' k T.field T.degree T.diagram T.diagram_ne T.tensor (diagramCompositum_extends T)
  let Y := foldLevelOfLocalModel Q Y₀
    (localModel_fixedPoints Q Y₀ deg hne T.tensor T.left_eq T.right_eq T.diagram_extends)
    hrK hResK S hS hMax ⟨hclK, hMaxK⟩ hNormK
  let Y' := foldLevelOfLocalModel Q' Y₀'
    (localModel_fixedPoints Q' Y₀' deg hne T.tensor T.left_eq T.right_eq T.diagram_extends)
    hrK hResK S' hS' hMax' ⟨hclK', hMaxK'⟩ hNormK'
  let φY := pointHom φ ((testSpec F).obj (.op (CommAlgCat.of F k)))
  have hPointφY (g : _) : Y'.points (φY g) = integralPointHom c.map (integralRing K) (Y.points g) := by
    rw [Y'.point_eq, Y.point_eq]
    exact descendedCentralPointSquare R R' c φ hφ f (IsScalarTower.toAlgHom F k T.field) g
  have hY : CentralComparison c φY Y.comparison Y'.comparison e :=
    foldedCentralLevel c Q Q' Y₀ Y₀' T.degree T.diagram_ne had hSym hSym' hDiag e₀ e d he₀ he hR₀ hC₀
      hAlcove hDir hRoot hCoroot φY hPointφY
  have wX (w) (i) (hi : i ∈ X.comparison.localIwahori.normalizer.word w) : i ∈ D.base.support := by
    change i ∈ (FoldedLocalModel.comparison X₀).localIwahori.normalizer.word w at hi
    rw [FoldedLocalModel.local_eq X₀] at hi
    exact FoldedLocalModel.words X₀ w i hi
  have wX' (w) (i) (hi : i ∈ X'.comparison.localIwahori.normalizer.word w) : i ∈ E.base.support := by
    change i ∈ (FoldedLocalModel.comparison X₀').localIwahori.normalizer.word w at hi
    rw [FoldedLocalModel.local_eq X₀'] at hi
    exact FoldedLocalModel.words X₀' w i hi
  have wY (w) (i) (hi : i ∈ Y.comparison.localIwahori.normalizer.word w) : i ∈ D.base.support := by
    change i ∈ (FoldedLocalModel.comparison Y₀).localIwahori.normalizer.word w at hi
    rw [FoldedLocalModel.local_eq Y₀] at hi
    exact FoldedLocalModel.words Y₀ w i hi
  have wY' (w) (i) (hi : i ∈ Y'.comparison.localIwahori.normalizer.word w) : i ∈ E.base.support := by
    change i ∈ (FoldedLocalModel.comparison Y₀').localIwahori.normalizer.word w at hi
    rw [FoldedLocalModel.local_eq Y₀'] at hi
    exact FoldedLocalModel.words Y₀' w i hi
  obtain ⟨hScalar, _⟩ := foldedScalarAtExtension T X Y hk (FoldedOrdering.order o) u
    (FoldedLocalModel.chart_eq X₀) (FoldedLocalModel.chart_eq Y₀) wX wY
  obtain ⟨hScalar', hQuot⟩ := foldedScalarAtExtension T X' Y' hk (FoldedOrdering.order o') u'
    (FoldedLocalModel.chart_eq X₀') (FoldedLocalModel.chart_eq Y₀') wX' wY'
  exact ⟨T, Y, Y', hY, hScalar, hScalar', hQuot, foldedCoefficientActions T Y wY,
    foldedCoefficientActions T Y' wY'⟩

end RamifiedBruhat

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
