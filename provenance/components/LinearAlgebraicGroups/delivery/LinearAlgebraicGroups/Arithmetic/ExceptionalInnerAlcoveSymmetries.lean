import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerAlcoveSymmetries
import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerAlcoveSymmetries

open Specs.ExceptionalInnerAlcoveSymmetries
open Specs.ExceptionalAffineRootSystems
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalStableAlcoves
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.Pinning (BasedRootDatum)
open ValuativeRel
open scoped TensorProduct CategoryTheory.MonObj

attribute [local instance] integerAlgebra

universe u

open private highestRootCoordinates e7ScaledCartanInverse
  from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private threeTimesCartanInverse
  from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

private theorem e6Highest_bounds
    (hfinite : {r | IsRootCoordinate (exceptionalCartan 6) r}.Finite) :
    IsRootCoordinate (exceptionalCartan 6) (-e6Highest) ∧
      ∀ r, IsRootCoordinate (exceptionalCartan 6) r → ∀ j, -e6Highest j ≤ r j := by
  obtain ⟨hr, hb⟩ := highestRootCoordinates (C := exceptionalCartan 6) (d := 3)
    (B := threeTimesCartanInverse) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide) (by decide) 1 e6Highest (by decide) (by decide) hfinite
  exact ⟨hr, fun r h j => (hb r h j).1⟩

private theorem e7Highest_bounds
    (hfinite : {r | IsRootCoordinate (exceptionalCartan 7) r}.Finite) :
    IsRootCoordinate (exceptionalCartan 7) (-e7Highest) ∧
      ∀ r, IsRootCoordinate (exceptionalCartan 7) r → ∀ j, -e7Highest j ≤ r j := by
  obtain ⟨hr, hb⟩ := highestRootCoordinates (C := exceptionalCartan 7) (d := 2)
    (B := e7ScaledCartanInverse) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide) (by decide) 0 e7Highest (by decide) (by decide) hfinite
  exact ⟨hr, fun r h j => (hb r h j).1⟩

/-- Affine forms given by nonnegative combinations of barycentric functions
have a panel precisely when their coefficient vector is supported on that panel. -/
private theorem labelSimpleWalls
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {A : ApartmentRoots ℚ V J}
    {p : V} {n : ℕ} (hn : 0 < n)
    (f : Fin (n + 1) → J × ℤ) (hf : Function.Injective f)
    (v : V → Fin (n + 1) → ℚ)
    (hpos : ∀ i, A.positive p (f i))
    (hzero : ∀ x i, v x i = 0 ↔ A.wallValue (f i) x = 0)
    (hpositive : ∀ x i, 0 < v x i ↔ 0 < A.wallValue (f i) x)
    (hrealize : ∀ b : Fin (n + 1) → ℚ, ∑ i, b i = 1 → ∃ x, v x = b)
    (hcombination : ∀ a, A.positive p a →
      ∃ c : Fin (n + 1) → ℚ, (∀ i, 0 ≤ c i) ∧ (∃ i, 0 < c i) ∧
        (∀ i, (∀ j ≠ i, c j = 0) → a = f i) ∧
        ∀ x, A.wallValue a x = ∑ i, c i * v x i) :
    ∃ l : Fin (n + 1) ≃ A.SimpleWall p, ∀ i, (l i).val = f i := by
  classical
  have hsimple (i : Fin (n + 1)) : A.IsSimple p (f i) := by
    let b : Fin (n + 1) → ℚ := fun j => if j = i then 0 else (n : ℚ)⁻¹
    have hsum : ∑ j, b j = 1 := by
      have hnc : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      simp [b, Finset.sum_ite, Finset.filter_ne', hnc]
    obtain ⟨x, hx⟩ := hrealize b hsum
    refine ⟨hpos i, x, (hzero x i).mp (by simp [hx, b]), ?_⟩
    intro a ha hne
    obtain ⟨c, hc, _, hsupport, he⟩ := hcombination a ha
    have hex : ∃ j, j ≠ i ∧ 0 < c j := by
      by_contra! hnz
      exact hne (hsupport i (fun j hj => le_antisymm (hnz j hj) (hc j)))
    obtain ⟨j, hji, hj⟩ := hex
    change 0 < A.wallValue a x
    rw [he, hx]
    have hp : 0 < (n : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hc k) (by by_cases q : k = i <;> simp [b, q, hp.le]))
      ⟨j, Finset.mem_univ _, mul_pos hj (by simpa [b, hji] using hp)⟩
  let l : Fin (n + 1) → A.SimpleWall p := fun i => ⟨f i, hsimple i⟩
  refine ⟨Equiv.ofBijective l ⟨fun _ _ h => hf (congrArg Subtype.val h), ?_⟩, fun _ => rfl⟩
  intro a
  obtain ⟨ha, x, hx, hothers⟩ := a.property
  by_contra! hn'
  have hs (i : Fin (n + 1)) : 0 < v x i :=
    (hpositive x i).mpr (hothers (f i) (hpos i) (fun h => hn' i (Subtype.ext h)))
  obtain ⟨c, hc, ⟨j, hj⟩, _, he⟩ := hcombination a.val ha
  have hsum : (0 : ℚ) < ∑ i, c i * v x i :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hc i) (hs i).le)
      ⟨j, Finset.mem_univ _, mul_pos hj (hs j)⟩
  exact hsum.ne' (he x ▸ hx)

private theorem wallsOfSimplex
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {A : ApartmentRoots ℚ V J}
    {p : V} {n : ℕ} (hn : 0 < n) (coordinates : V ≃ₗ[ℚ] (Fin n → ℚ))
    (simple : Fin n ↪ J) (highestOpposite : J) (θ : Fin n → ℚ)
    (hθ : ∀ i, 0 < θ i) (hreduced : A.ReducedDirections)
    (hSimple : ∀ x i, A.root (simple i) x = coordinates x i)
    (hHighest : ∀ x, A.root highestOpposite x = -(∑ i, θ i * coordinates x i))
    (hposSimple : ∀ i, A.positive p (simple i, 0))
    (hposHighest : A.positive p (highestOpposite, 1))
    (hLevel : ∀ a m, A.positive p (a, m) → 0 ≤ m)
    (r : J → Fin n → ℚ) (hRoot : ∀ a x, A.root a x = ∑ i, r a i * coordinates x i)
    (hLower : ∀ a i, -θ i ≤ r a i)
    (hPositive : ∀ a, A.positive p (a, 0) → ∀ i, 0 ≤ r a i) :
    ∃ l : Fin (n + 1) ≃ A.SimpleWall p,
      (∀ i, (l i).val = Fin.cases (highestOpposite, 1) (fun j => (simple j, 0)) i) ∧
      ∀ i x, A.wallValue (l i).val x =
        Fin.cases (1 - ∑ j, θ j * coordinates x j) (coordinates x) i := by
  classical
  let f : Fin (n + 1) → J × ℤ := Fin.cases (highestOpposite, 1) (fun j => (simple j, 0))
  have hf : Function.Injective f := by
    intro i j he
    revert he
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro; rfl
    · intro h
      have hz : (1 : ℤ) = 0 := congrArg Prod.snd h
      omega
    · intro h
      have hz : (0 : ℤ) = 1 := congrArg Prod.snd h
      omega
    · intro h
      exact congrArg Fin.succ (simple.injective (congrArg Prod.fst h))
  have hfValue (i : Fin (n + 1)) (x : V) :
      A.wallValue (f i) x = Fin.cases (1 - ∑ j, θ j * coordinates x j) (coordinates x) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change A.root highestOpposite x + ((1 : ℤ) : ℚ) = _
      rw [hHighest, Fin.cases_zero]
      push_cast
      ring
    · change A.root (simple j) x + ((0 : ℤ) : ℚ) = _
      simpa using hSimple x j
  let w : Fin (n + 1) → ℚ := Fin.cases 1 θ
  let v (x : V) (i : Fin (n + 1)) := w i * A.wallValue (f i) x
  have hw (i : Fin (n + 1)) : 0 < w i := Fin.cases zero_lt_one hθ i
  have hv0 (x : V) : v x 0 = 1 - ∑ j, θ j * coordinates x j := by simpa [v, w] using hfValue 0 x
  have hvs (x : V) (j : Fin n) : v x j.succ = θ j * coordinates x j := by
    simp [v, w, hfValue]
  have hrealize (b : Fin (n + 1) → ℚ) (hb : ∑ i, b i = 1) : ∃ x, v x = b := by
    obtain ⟨x, hx⟩ := coordinates.surjective (fun j => b j.succ / θ j)
    have hxs (j : Fin n) : θ j * coordinates x j = b j.succ := by
      rw [congrFun hx j, mul_div_cancel₀ _ (hθ j).ne']
    refine ⟨x, funext (fun i => Fin.cases ?_ (fun j => (hvs x j).trans (hxs j)) i)⟩
    rw [hv0, Fin.sum_univ_succ] at *
    simp_rw [hxs]
    linarith
  have hcombination (a : J × ℤ) (ha : A.positive p a) :
      ∃ c : Fin (n + 1) → ℚ, (∀ i, 0 ≤ c i) ∧ (∃ i, 0 < c i) ∧
        (∀ i, (∀ j ≠ i, c j = 0) → a = f i) ∧
        ∀ x, A.wallValue a x = ∑ i, c i * v x i := by
    obtain ⟨a, m⟩ := a
    let c : Fin (n + 1) → ℚ := Fin.cases (m : ℚ) (fun j => (m : ℚ) + r a j / θ j)
    have hm := hLevel a m ha
    have hc (i : Fin (n + 1)) : 0 ≤ c i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · change (0 : ℚ) ≤ (m : ℚ)
        exact_mod_cast hm
      · change 0 ≤ (m : ℚ) + r a j / θ j
        by_cases hm0 : m = 0
        · subst m
          simpa using div_nonneg (hPositive a ha j) (hθ j).le
        · have h1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
          have hdiv : -1 ≤ r a j / θ j :=
            (le_div_iff₀ (hθ j)).mpr (by simpa using hLower a j)
          linarith
    have hvalue (x : V) : A.wallValue (a, m) x = ∑ i, c i * v x i := by
      rw [Fin.sum_univ_succ, hv0]
      simp only [c, Fin.cases_zero, Fin.cases_succ, hvs]
      change A.root a x + (m : ℚ) = _
      rw [hRoot]
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hterm (j : Fin n) : r a j / θ j * (θ j * coordinates x j) =
          r a j * coordinates x j := by rw [← mul_assoc, div_mul_cancel₀ _ (hθ j).ne']
      simp only [hterm]
      ring
    have hcp : ∃ i, 0 < c i := by
      by_contra! h
      have hz (i : Fin (n + 1)) : c i = 0 := le_antisymm (h i) (hc i)
      change 0 < A.wallValue (a, m) p at ha
      simp [hvalue, hz] at ha
    refine ⟨c, hc, hcp, ?_, hvalue⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      have hmpos : 0 < m := by
        obtain ⟨k, hk⟩ := hcp
        revert hk
        refine Fin.cases ?_ (fun j => ?_) k
        · intro hp
          change (0 : ℚ) < (m : ℚ) at hp
          exact_mod_cast hp
        · intro hp
          rw [hi _ (Fin.succ_ne_zero j)] at hp
          exact (lt_irrefl _ hp).elim
      have hrel (j : Fin n) : r a j = -(m : ℚ) * θ j := by
        have he := hi j.succ (Fin.succ_ne_zero j)
        change (m : ℚ) + r a j / θ j = 0 at he
        exact (div_eq_iff (hθ j).ne').mp (by linarith)
      let j : Fin n := ⟨0, hn⟩
      have hle : (m : ℚ) ≤ 1 := by
        have h := hLower a j
        rw [hrel] at h
        nlinarith [hθ j]
      have hmone : m = 1 := by
        have h : m ≤ (1 : ℤ) := by exact_mod_cast hle
        omega
      have he : a = highestOpposite := by
        apply hreduced.1
        ext x
        rw [hHighest, hRoot]
        simp [hrel, hmone, neg_mul, Finset.sum_neg_distrib]
      exact Prod.ext he hmone
    · intro hi
      have hmzero : m = 0 := by
        have he := hi 0 (Ne.symm (Fin.succ_ne_zero j))
        change (m : ℚ) = 0 at he
        exact_mod_cast he
      have hz (k : Fin n) (hne : k ≠ j) : r a k = 0 := by
        have he := hi k.succ (fun hk => hne (Fin.succ_injective _ hk))
        change (m : ℚ) + r a k / θ k = 0 at he
        simpa [hmzero, div_eq_zero_iff, (hθ k).ne'] using he
      have he : A.root a = r a j • A.root (simple j) := by
        ext x
        rw [hRoot, Finset.sum_eq_single j (fun k _ hk => by rw [hz k hk, zero_mul]) (by simp)]
        simp [hSimple, smul_eq_mul]
      rcases hreduced.2 (simple j) a (r a j) he with h | h
      · exact Prod.ext h.symm hmzero
      · have hp := hposSimple j
        subst m
        change 0 < A.root (simple j) p + ((0 : ℤ) : ℚ) at hp
        change 0 < A.root a p + ((0 : ℤ) : ℚ) at ha
        rw [h, LinearMap.neg_apply] at ha
        push_cast at hp ha
        linarith
  obtain ⟨l, hl⟩ := labelSimpleWalls hn f hf v
    (fun i => Fin.cases hposHighest hposSimple i)
    (fun x i => mul_eq_zero_iff_left (hw i).ne')
    (fun x i => mul_pos_iff_of_pos_left (hw i)) hrealize hcombination
  exact ⟨l, hl, fun i x => (congrArg (fun a => A.wallValue a x) (hl i)).trans (hfValue i x)⟩

private def extendedCartan {n : ℕ} (θ : Fin n → ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => Fin.cases
    (Fin.cases 2 (fun j => -∑ k, θ k * exceptionalCartan n k j) j)
    (fun i => Fin.cases (-∑ k, θ k * exceptionalCartan n i k)
      (fun j => exceptionalCartan n i j) j) i

private theorem markedWalls {E : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ E.base.support) (hn : 0 < n) (hNum : ExceptionalNumbering E n b)
    (θ : Fin n → ℤ) (hθ : ∀ i, 0 < θ i) (hSym : (exceptionalCartan n).IsSymm)
    (hhighest : {r | IsRootCoordinate (exceptionalCartan n) r}.Finite →
      IsRootCoordinate (exceptionalCartan n) (-θ) ∧
        ∀ r, IsRootCoordinate (exceptionalCartan n) r → ∀ j, -θ j ≤ r j)
    (p : ℚ ⊗[ℤ] E.Y) :
    let A := ApartmentRoots.split E.datum ℚ
    (∀ i, E.base.IsPos i → 0 < A.root i p ∧ A.root i p < 1) →
    ∃ (l : Fin (n + 1) ≃ A.SimpleWall p) (coordinates : (ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (Fin n → ℚ)),
      coordinates.toLinearMap = simpleRootValues E.datum E.base b ℚ ∧
      (∀ i x, A.wallValue (l i).val x =
        Fin.cases (1 - ∑ j, (θ j : ℚ) * coordinates x j) (coordinates x) i) ∧
      ∀ i j, A.root (l i).val.1 (A.coroot (l j).val.1) = (extendedCartan θ i j : ℚ) := by
  classical
  intro A hp
  let _ := E.finiteRoots
  let _ := E.freeX
  let _ := E.finiteX
  let _ := E.freeY
  let _ := E.finiteY
  let _ := E.reduced
  obtain ⟨ρ, hρ⟩ := ExceptionalAffineRootSystems.pairedRootCoordinates E.datum E.base b
    (exceptionalCartan n) hSym (fun i j => (hNum.2 i j).symm)
  have hfinite : {r | IsRootCoordinate (exceptionalCartan n) r}.Finite := by
    convert Set.finite_range (fun i => (ρ i).val) using 1
    ext r
    exact ⟨fun hr => ⟨ρ.symm ⟨r, hr⟩, congrArg Subtype.val (ρ.apply_symm_apply ⟨r, hr⟩)⟩,
      fun ⟨i, hi⟩ => hi ▸ (ρ i).property⟩
  obtain ⟨htRoot, hBounds⟩ := hhighest hfinite
  obtain ⟨t, ht⟩ := ρ.surjective ⟨-θ, htRoot⟩
  have ht' : (ρ t).val = -θ := congrArg Subtype.val ht
  obtain ⟨coordinates, hcoordinates⟩ := ExceptionalAffineRootSystems.cocharacterApartmentCoordinates
    (K := ℚ) E.datum E.base b hNum.1
  have hRoot (i : E.I) (x : ℚ ⊗[ℤ] E.Y) :
      A.root i x = ∑ j, ((ρ i).val j : ℚ) * coordinates x j := by
    rw [ExceptionalAffineRootSystems.rootValuesFromCoordinates E.datum E.base b i _
      (hρ i).1, ← hcoordinates]
    rfl
  have hSimple (x : ℚ ⊗[ℤ] E.Y) (i : Fin n) : A.root (b i) x = coordinates x i := by
    change simpleRootValues E.datum E.base b ℚ x i = _
    rw [← hcoordinates]
    rfl
  have hHighest (x : ℚ ⊗[ℤ] E.Y) : A.root t x = -∑ i, (θ i : ℚ) * coordinates x i := by
    rw [hRoot, ht']
    simp [neg_mul, Finset.sum_neg_distrib]
  let _ := E.datum.indexNeg
  have hval (i : E.I) : -1 < A.root i p ∧ A.root i p < 1 := by
    rcases RootPairing.Base.IsPos.or_neg E.base i with h | h
    · exact ⟨by linarith [(hp i h).1], (hp i h).2⟩
    · have hneg := hp (-i) h
      have heq : A.root (-i) p = -A.root i p := by
        change RootData.extendFunctional ℚ (E.datum.root' (-i)) p =
          -RootData.extendFunctional ℚ (E.datum.root' i) p
        change RootData.extendFunctional ℚ
          (E.datum.toLinearMap (E.datum.root (E.datum.reflectionPerm i i))) p = _
        rw [E.datum.root_reflectionPerm, E.datum.reflection_apply_self, map_neg]
        simp [RootData.extendFunctional]
      rw [heq] at hneg
      exact ⟨by linarith [hneg.2], by linarith [hneg.1]⟩
  have hposRoot (i : E.I) (hi : A.positive p (i, 0)) : E.base.IsPos i := by
    rcases RootPairing.Base.IsPos.or_neg E.base i with h | h
    · exact h
    · have heq : A.root (-i) p = -A.root i p := by
        change RootData.extendFunctional ℚ (E.datum.root' (-i)) p =
          -RootData.extendFunctional ℚ (E.datum.root' i) p
        change RootData.extendFunctional ℚ
          (E.datum.toLinearMap (E.datum.root (E.datum.reflectionPerm i i))) p = _
        rw [E.datum.root_reflectionPerm, E.datum.reflection_apply_self, map_neg]
        simp [RootData.extendFunctional]
      change 0 < A.root i p + ((0 : ℤ) : ℚ) at hi
      have hn := (hp (-i) h).1
      rw [heq] at hn
      push_cast at hi
      linarith
  let simple : Fin n ↪ E.I := ⟨fun i => (b i).val, fun _ _ h => b.injective (Subtype.ext h)⟩
  obtain ⟨l, hl, hwall⟩ := wallsOfSimplex hn coordinates simple t (fun i => (θ i : ℚ))
    (fun i => by exact_mod_cast hθ i) (ExceptionalAffineRootSystems.splitReducedDirections E.datum)
    hSimple hHighest (fun i => by
      change 0 < A.root (b i) p + ((0 : ℤ) : ℚ)
      simpa using (hp _ (E.base.isPos_of_mem_support (b i).property)).1)
    (by
      change 0 < A.root t p + ((1 : ℤ) : ℚ)
      push_cast
      linarith [(hval t).1])
    (fun i m h => by
      change 0 < A.root i p + (m : ℚ) at h
      by_contra! hm
      have hle : (m : ℚ) ≤ -1 := by exact_mod_cast (show m ≤ (-1 : ℤ) by omega)
      linarith [(hval i).2])
    (fun i j => ((ρ i).val j : ℚ)) hRoot
    (fun i j => by exact_mod_cast hBounds _ (ρ i).property j)
    (fun i h j => by
      obtain ⟨z, _, hz, hzroot⟩ := E.base.exists_root_eq_sum_int i
      have hsum : (∑ j, z (b j) • E.datum.root (b j)) =
          ∑ j ∈ E.base.support, z j • E.datum.root j := by
        rw [E.base.support.sum_subtype (p := (· ∈ E.base.support)) (by simp)]
        exact Equiv.sum_comp b (fun j : E.base.support => z j • E.datum.root j)
      let eval := Fintype.linearCombination ℤ (fun j : Fin n => E.datum.root (b j))
      have heq : (ρ i).val = fun j => z (b j) :=
        (linearIndependent_iff_injective_fintypeLinearCombination.mp
          (E.base.linearIndepOn_root.comp b b.injective) : Function.Injective eval)
          (by simp only [Fintype.linearCombination_apply, ← (hρ i).1, hsum, ← hzroot])
      rw [heq]
      rcases hz with hz | hz
      · exact_mod_cast hz.le (b j)
      · have hp' := hposRoot i h
        change 0 < E.base.height i at hp'
        rw [E.base.height_eq_sum hzroot] at hp'
        exact ((Finset.sum_nonpos fun k _ => hz.le k).not_gt hp').elim)
  have hpair (i j : Fin n) :
      A.root (b i) (A.coroot (b j)) = (exceptionalCartan n i j : ℚ) := by
    change RootData.extendFunctional ℚ (E.datum.root' (b i)) (1 ⊗ₜ[ℤ] E.datum.coroot (b j)) = _
    simp [hNum.2]
  have hcoroot : A.coroot t = -∑ j, θ j • A.coroot (b j) := by
    let f : E.Y →ₗ[ℤ] (ℚ ⊗[ℤ] E.Y) := TensorProduct.mk ℤ ℚ E.Y 1
    change f (E.datum.coroot t) = -∑ j, θ j • f (E.datum.coroot (b j))
    rw [(hρ t).2, ht', map_sum]
    simp [Finset.sum_neg_distrib]
  have hzero : (l 0).val.1 = t := congrArg Prod.fst (hl 0)
  have hsucc (j : Fin n) : (l j.succ).val.1 = b j := congrArg Prod.fst (hl j.succ)
  refine ⟨l, coordinates, hcoordinates, hwall, ?_⟩
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [hzero, extendedCartan, Fin.cases_zero, Int.cast_ofNat] using A.diagonal t
  · rw [hzero, hsucc, hHighest]
    simp [extendedCartan, ← hSimple, hpair]
  · rw [hsucc, hzero, hcoroot]
    simp [extendedCartan, hpair, zsmul_eq_mul]
  · simpa only [hsucc, extendedCartan, Fin.cases_succ] using hpair i j

section Normalizer

variable {K G W V : Type u} {J : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Group G] [Group W] [AddCommGroup V] [Module ℚ V]
  {D : BasedRootDatum.{u}} {M : Model D} {j : G →* FieldPoints M K}
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}

/-- The affine value of a length-zero normalizer point is its type class. -/
private theorem affine_eq_typeChange (B : Building C) (Q : C.TypeQuotient)
    (t : C.N) (ht : (t : G) ∈ lengthZeroNormalizer C) :
    C.affine t = (typeChange Q (t : G)).val.val := by
  let := Q.normal
  obtain ⟨t', ⟨w, hw, hω⟩, ht'⟩ := ht
  have he : t' = t := Subtype.ext ht'
  subst t'
  let ω : alcoveStabilizer A (A.alcove p) := ⟨w, hw⟩
  have hlift : C.affine (Q.lift ω) = C.affine t := (Q.affine_lift ω).trans hω
  let d := (Q.lift ω)⁻¹ * t
  have hd : d ∈ C.affine.ker := by
    change C.affine d = 1
    simp [d, hlift]
  have ht₀ : (d : G) ∈ C.T₀ := by
    change (d : G) ∈ (Specs.ExceptionalIwahoriImageComparison.integralUnitTorus (K := K) M).comap j
    rw [← C.kernel]
    exact Subgroup.mem_map_of_mem _ hd
  have hdI : (d : G) ∈ C.I := (show (d : G) ∈ C.I ⊓ C.N from
    B.iwahori_inter_normalizer.symm ▸ ht₀).1
  have hdType : typeChange Q (d : G) = 1 := by
    change Q.quotient (QuotientGroup.mk (d : G)) = 1
    rw [(QuotientGroup.eq_one_iff (d : G)).mpr (B.realization.iwahori_mem hdI), map_one]
  have htType : typeChange Q (t : G) = ω := by
    have hprod : (t : G) = (Q.lift ω : G) * (d : G) := by simp [d]
    rw [hprod, map_mul, hdType, mul_one]
    exact Q.quotient_lift ω
  rw [htType]
  exact hω.symm

private theorem transports_typeWall (Q : C.TypeQuotient)
    (ω : alcoveStabilizer A (A.alcove p)) (a : A.SimpleWall p) :
    A.Transports ω.val.val a.val (Q.wallPerm ω a).val := by
  obtain ⟨s, hs⟩ := C.geometry.extended_symmetries ω.val.property
  have hp : p ∈ A.alcove p := fun _ h => h
  have hpre : ω.val.val.symm p ∈ A.alcove p := by
    have hi : ω.val.val.symm '' A.alcove p = A.alcove p :=
      (ω⁻¹ : alcoveStabilizer A (A.alcove p)).property
    exact (Set.ext_iff.mp hi _).mp (Set.mem_image_of_mem _ hp)
  have hspos : A.positive p (s a.val) := by
    change 0 < A.value (s a.val) p
    have h := (hs a.val).1 (ω.val.val.symm p)
    rw [AffineEquiv.apply_symm_apply] at h
    rw [h]
    exact hpre _ a.property.1
  obtain ⟨_, x, hx, hunique⟩ := (Q.wallPerm ω a).property
  have hx' : x ∈ ω.val.val '' A.wallHyperplane a.val := by
    rw [Q.wall_action]
    exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have he : s a.val = (Q.wallPerm ω a).val := by
    by_contra hne
    exact (hunique _ hspos hne).ne' (((hs a.val).1 y).trans hy)
  simpa only [he] using hs a.val

end Normalizer

section LinearParts

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

/-- Subtracting the value at the origin removes the translation term. -/
private theorem root_transport {g : V ≃ᵃ[ℚ] V} {a b : J × ℤ}
    (h : ∀ x, A.wallValue b (g x) = A.wallValue a x) (x : V) :
    A.root b.1 (g.linear x) = A.root a.1 x := by
  have ha : g x = g.linear x + g 0 := by simpa using g.map_vadd (0 : V) x
  have hx := h x
  have h₀ := h 0
  rw [ha] at hx
  simp only [AffineArrangement.Datum.value, map_add, map_zero] at hx h₀
  linarith

private theorem normalized_root {n : ℕ} {θ : Fin n → ℤ} {coord : V ≃ₗ[ℚ] (Fin n → ℚ)}
    {f : Fin (n + 1) → A.SimpleWall p}
    (hwall : ∀ i x, A.wallValue (f i).val x =
      Fin.cases (1 - ∑ j, (θ j : ℚ) * coord x j) (coord x) i)
    (i : Fin (n + 1)) (x : V) :
    A.root (f i).val.1 x = directionalValues θ (coord x) i := by
  have hx := hwall i x
  have h₀ := hwall i 0
  simp only [AffineArrangement.Datum.value, map_zero] at hx h₀
  revert hx h₀
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
      directionalValues]
    intros
    linarith
  · simp only [Fin.cases_succ, Pi.zero_apply, directionalValues]
    intros
    linarith

private theorem fixedDirections_map {n : ℕ} {θ : Fin n → ℤ}
    {coord : V ≃ₗ[ℚ] (Fin n → ℚ)} {f : Fin (n + 1) → A.SimpleWall p}
    (hwall : ∀ i x, A.wallValue (f i).val x =
      Fin.cases (1 - ∑ j, (θ j : ℚ) * coord x j) (coord x) i)
    {σ : Equiv.Perm (Fin (n + 1))} {g : V ≃ᵃ[ℚ] V}
    (h : ∀ i x, A.wallValue (f (σ i)).val (g x) = A.wallValue (f i).val x) :
    (fixedDirections g.linear).map coord.toLinearMap = invariantDirections θ σ := by
  have ht (i : Fin (n + 1)) (x : V) :
      directionalValues θ (coord (g.linear x)) (σ i) = directionalValues θ (coord x) i := by
    rw [← normalized_root hwall, ← normalized_root hwall]
    exact root_transport (h i) x
  have hf (x : V) : x ∈ fixedDirections g.linear ↔ coord x ∈ invariantDirections θ σ := by
    change g.linear x - x = 0 ↔ ∀ i, directionalValues θ (coord x) (σ i) =
      directionalValues θ (coord x) i
    rw [sub_eq_zero]
    refine ⟨fun hx i => ?_, fun hx => ?_⟩
    · simpa only [hx] using ht i x
    apply coord.injective
    funext j
    obtain ⟨i, hi⟩ := σ.surjective j.succ
    have he := (ht i x).trans (hx i).symm
    rw [hi] at he
    exact he
  ext y
  obtain ⟨x, rfl⟩ := coord.surjective y
  constructor
  · rintro ⟨z, hz, he⟩
    have hz' : z = x := coord.injective he
    exact (hf x).mp (hz' ▸ hz)
  · intro hx
    exact ⟨x, (hf x).mpr hx, rfl⟩

private theorem typePermutation_ne_one {n : ℕ} {coord : V ≃ₗ[ℚ] (Fin n → ℚ)}
    {f : Fin (n + 1) → A.SimpleWall p}
    (hwall : ∀ i : Fin n, ∀ x, A.wallValue (f i.succ).val x = coord x i)
    {σ : Equiv.Perm (Fin (n + 1))} {g : V ≃ᵃ[ℚ] V} (hg : g ≠ 1)
    (h : ∀ i x, A.wallValue (f (σ i)).val (g x) = A.wallValue (f i).val x) :
    σ ≠ 1 := by
  intro hσ
  subst σ
  apply hg
  ext x
  apply coord.injective
  funext j
  change coord (g x) j = coord x j
  simpa only [Equiv.Perm.one_apply, hwall] using h j.succ x

end LinearParts

section Diagrams

/-- A distance table is preserved if neighboring vertices satisfy the triangle
inequality and every vertex at positive distance has a step towards the target. -/
private theorem preservesDiagramDistance {J : Type*} (adjacent : J → J → Prop)
    (d : J → J → ℕ) (hzero : ∀ i j, d i j = 0 ↔ i = j)
    (htriangle : ∀ i j k, adjacent i j → d i k ≤ d j k + 1)
    (hstep : ∀ i k, d i k ≠ 0 → ∃ j, adjacent i j ∧ d j k + 1 = d i k)
    (σ : Equiv.Perm J) (hσ : ∀ i j, adjacent (σ i) (σ j) ↔ adjacent i j) :
    ∀ i j, d (σ i) (σ j) = d i j := by
  have bound (τ : Equiv.Perm J) (hτ : ∀ i j, adjacent i j → adjacent (τ i) (τ j)) :
      ∀ k i j, d i j ≤ k → d (τ i) (τ j) ≤ k := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have he := (hzero i j).mp (Nat.eq_zero_of_le_zero hij)
      subst j
      rw [(hzero _ _).mpr rfl]
    | succ k ih =>
      intro i j hij
      by_cases hz : d i j = 0
      · have he := (hzero i j).mp hz
        subst j
        rw [(hzero _ _).mpr rfl]
        exact Nat.zero_le _
      · obtain ⟨a, ha, he⟩ := hstep i j hz
        have h := ih a j (by omega)
        exact (htriangle _ _ _ (hτ i a ha)).trans (Nat.succ_le_succ h)
  have hinv (i j : J) (h : adjacent i j) : adjacent (σ.symm i) (σ.symm j) := by
    apply (hσ _ _).mp
    simpa only [Equiv.apply_symm_apply] using h
  intro i j
  refine le_antisymm (bound σ (fun i j => (hσ i j).mpr) _ i j le_rfl) ?_
  simpa only [Equiv.symm_apply_apply] using bound σ.symm hinv _ (σ i) (σ j) le_rfl

private theorem eq_of_anchorImages {J : Type*} (d : J → J → ℕ) (a b : J)
    (hsep : ∀ i j, d a i = d a j → d b i = d b j → i = j)
    {σ τ : Equiv.Perm J} (hσ : ∀ i j, d (σ i) (σ j) = d i j)
    (hτ : ∀ i j, d (τ i) (τ j) = d i j) (ha : σ a = τ a) (hb : σ b = τ b) :
    σ = τ := by
  ext i
  apply τ.symm.injective
  rw [Equiv.symm_apply_apply]
  apply hsep
  · rw [← hτ a (τ.symm (σ i)), τ.apply_symm_apply, ← ha, hσ]
  · rw [← hτ b (τ.symm (σ i)), τ.apply_symm_apply, ← hb, hσ]

private def e6Distance : Fin 7 → Fin 7 → ℕ :=
  ![
    ![0, 4, 1, 3, 2, 3, 4],
    ![4, 0, 3, 1, 2, 3, 4],
    ![1, 3, 0, 2, 1, 2, 3],
    ![3, 1, 2, 0, 1, 2, 3],
    ![2, 2, 1, 1, 0, 1, 2],
    ![3, 3, 2, 2, 1, 0, 1],
    ![4, 4, 3, 3, 2, 1, 0]]

private def e7Distance : Fin 8 → Fin 8 → ℕ :=
  ![
    ![0, 1, 4, 2, 3, 4, 5, 6],
    ![1, 0, 3, 1, 2, 3, 4, 5],
    ![4, 3, 0, 2, 1, 2, 3, 4],
    ![2, 1, 2, 0, 1, 2, 3, 4],
    ![3, 2, 1, 1, 0, 1, 2, 3],
    ![4, 3, 2, 2, 1, 0, 1, 2],
    ![5, 4, 3, 3, 2, 1, 0, 1],
    ![6, 5, 4, 4, 3, 2, 1, 0]]

private def e6ArmPerm : Fin 6 → Equiv.Perm (Fin 7) :=
  ![1, e6Rotate, e6Rotate.symm,
    Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 6 * Equiv.swap 2 5,
    Equiv.swap 1 6 * Equiv.swap 3 5]

set_option maxHeartbeats 1600000 in
private theorem e6_permutation (σ : Equiv.Perm (Fin 7)) (hne : σ ≠ 1) (hpow : σ ^ 3 = 1)
    (hC : ∀ i j, extendedCartan e6Highest (σ i) (σ j) = extendedCartan e6Highest i j) :
    σ = e6Rotate ∨ σ = e6Rotate.symm := by
  have hadj : ∀ i j, e6Distance i j = 1 ↔ extendedCartan e6Highest i j = -1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [extendedCartan, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> decide
  have htriangle : ∀ i j k, e6Distance i j = 1 → e6Distance i k ≤ e6Distance j k + 1 := by decide
  have hstep : ∀ i k, e6Distance i k ≠ 0 →
      ∃ j, e6Distance i j = 1 ∧ e6Distance j k + 1 = e6Distance i k := by decide
  have hdist := preservesDiagramDistance (fun i j => e6Distance i j = 1)
    e6Distance (by decide) htriangle hstep σ (fun i j => by rw [hadj, hadj, hC])
  have hdiam : ∀ i j, e6Distance i j = 4 → i = 0 ∨ i = 1 ∨ i = 6 := by decide
  have h0 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 6 :=
    hdiam _ _ ((hdist 0 1).trans (by decide))
  have h1 : σ 1 = 0 ∨ σ 1 = 1 ∨ σ 1 = 6 :=
    hdiam _ _ ((hdist 1 0).trans (by decide))
  have hfind : ∀ a b : Fin 7, (a = 0 ∨ a = 1 ∨ a = 6) → (b = 0 ∨ b = 1 ∨ b = 6) →
      a ≠ b → ∃ k : Fin 6, e6ArmPerm k 0 = a ∧ e6ArmPerm k 1 = b := by decide
  obtain ⟨k, ha, hb⟩ := hfind _ _ h0 h1 (fun h => (by decide : (0 : Fin 7) ≠ 1) (σ.injective h))
  have hc : ∀ (k : Fin 6) i j, e6Distance (e6ArmPerm k i) (e6ArmPerm k j) = e6Distance i j := by decide
  have he := eq_of_anchorImages e6Distance 0 1 (by decide) hdist (hc k) ha.symm hb.symm
  subst σ
  have hnontrivial : ∀ k : Fin 6, e6ArmPerm k ≠ 1 → e6ArmPerm k ^ 3 = 1 →
      e6ArmPerm k = e6Rotate ∨ e6ArmPerm k = e6Rotate.symm := by decide
  exact hnontrivial k hne hpow

private def e7ChainPerm : Fin 2 → Equiv.Perm (Fin 8) := ![1, e7Reverse]

set_option maxHeartbeats 1600000 in
private theorem e7_permutation (σ : Equiv.Perm (Fin 8)) (hne : σ ≠ 1)
    (hC : ∀ i j, extendedCartan e7Highest (σ i) (σ j) = extendedCartan e7Highest i j) :
    σ = e7Reverse := by
  have hadj : ∀ i j, e7Distance i j = 1 ↔ extendedCartan e7Highest i j = -1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [extendedCartan, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> decide
  have htriangle : ∀ i j k, e7Distance i j = 1 → e7Distance i k ≤ e7Distance j k + 1 := by decide
  have hstep : ∀ i k, e7Distance i k ≠ 0 →
      ∃ j, e7Distance i j = 1 ∧ e7Distance j k + 1 = e7Distance i k := by decide
  have hdist := preservesDiagramDistance (fun i j => e7Distance i j = 1)
    e7Distance (by decide) htriangle hstep σ (fun i j => by rw [hadj, hadj, hC])
  have hfind : ∀ a b : Fin 8, e7Distance a b = 6 →
      ∃ k : Fin 2, e7ChainPerm k 0 = a ∧ e7ChainPerm k 7 = b := by decide
  obtain ⟨k, ha, hb⟩ := hfind _ _ ((hdist 0 7).trans (by decide))
  have hc : ∀ (k : Fin 2) i j, e7Distance (e7ChainPerm k i) (e7ChainPerm k j) = e7Distance i j := by decide
  have he := eq_of_anchorImages e7Distance 0 7 (by decide) hdist (hc k) ha.symm hb.symm
  subst σ
  have hnontrivial : ∀ k : Fin 2, e7ChainPerm k ≠ 1 → e7ChainPerm k = e7Reverse := by decide
  exact hnontrivial k hne

end Diagrams

private theorem e6InvariantValues (r : Fin 6 → ℚ)
    (hr : r ∈ invariantDirections e6Highest e6Rotate) :
    ∃ a b : ℚ, r = ![-2*a-b, a, a, b, a, -2*a-b] := by
  change ∀ i, directionalValues e6Highest r (e6Rotate i) = directionalValues e6Highest r i at hr
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  change r 0 = -(∑ i, (e6Highest i : ℚ) * r i) at h0
  change r 5 = r 0 at h1
  change r 2 = r 1 at h2
  change r 4 = r 2 at h3
  norm_num [e6Highest, Fin.sum_univ_succ] at h0
  refine ⟨r 1, r 3, ?_⟩
  ext i
  fin_cases i <;> simp <;> linarith

private theorem e7InvariantValues (r : Fin 7 → ℚ)
    (hr : r ∈ invariantDirections e7Highest e7Reverse) :
    ∃ a b c d : ℚ, r = ![a, d, b, c, b, a, -2*a-3*b-2*c-d] := by
  change ∀ i, directionalValues e7Highest r (e7Reverse i) = directionalValues e7Highest r i at hr
  have h0 := hr 0
  have h1 := hr 1
  have h3 := hr 3
  change r 6 = -(∑ i, (e7Highest i : ℚ) * r i) at h0
  change r 5 = r 0 at h1
  change r 4 = r 2 at h3
  norm_num [e7Highest, Fin.sum_univ_succ] at h0
  refine ⟨r 0, r 2, r 3, r 1, ?_⟩
  ext i
  fin_cases i <;> simp <;> linarith

private theorem e6InvariantValues_mem (a b : ℚ) :
    ![-2*a-b, a, a, b, a, -2*a-b] ∈ invariantDirections e6Highest e6Rotate := by
  intro i
  fin_cases i <;> try rfl
  · change -2*a-b = -(∑ j, (e6Highest j : ℚ) * (![-2*a-b, a, a, b, a, -2*a-b] : Fin 6 → ℚ) j)
    norm_num [e6Highest, Fin.sum_univ_succ]; ring
  · change -(∑ j, (e6Highest j : ℚ) * (![-2*a-b, a, a, b, a, -2*a-b] : Fin 6 → ℚ) j) = -2*a-b
    norm_num [e6Highest, Fin.sum_univ_succ]; ring

private theorem e7InvariantValues_mem (a b c d : ℚ) :
    ![a, d, b, c, b, a, -2*a-3*b-2*c-d] ∈ invariantDirections e7Highest e7Reverse := by
  intro i
  fin_cases i <;> try rfl
  · change -2*a-3*b-2*c-d = -(∑ j, (e7Highest j : ℚ) * (![a, d, b, c, b, a, -2*a-3*b-2*c-d] : Fin 7 → ℚ) j)
    norm_num [e7Highest, Fin.sum_univ_succ]; ring
  · change -(∑ j, (e7Highest j : ℚ) * (![a, d, b, c, b, a, -2*a-3*b-2*c-d] : Fin 7 → ℚ) j) = -2*a-3*b-2*c-d
    norm_num [e7Highest, Fin.sum_univ_succ]; ring

private theorem invariantDirections_symm {n : ℕ} (highest : Fin n → ℤ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    invariantDirections highest σ.symm = invariantDirections highest σ := by
  ext r
  change (∀ i, directionalValues highest r (σ.symm i) = directionalValues highest r i) ↔
    (∀ i, directionalValues highest r (σ i) = directionalValues highest r i)
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using (h (σ i)).symm
  · intro h i
    simpa only [Equiv.apply_symm_apply] using (h (σ.symm i)).symm

/-- The invariant directions of a nontrivial E₆ rotation have dimension two. -/
private theorem e6InvariantDirections_finrank :
    Module.finrank ℚ (invariantDirections e6Highest e6Rotate) = 2 := by
  let U := invariantDirections e6Highest e6Rotate
  let f : U →ₗ[ℚ] (Fin 2 → ℚ) :=
    LinearMap.pi fun i => (LinearMap.proj (![1, 3] i)).comp U.subtype
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have h₁ : (x : Fin 6 → ℚ) 1 = (y : Fin 6 → ℚ) 1 := congrFun h 0
      have h₂ : (x : Fin 6 → ℚ) 3 = (y : Fin 6 → ℚ) 3 := congrFun h 1
      obtain ⟨a, b, hx⟩ := e6InvariantValues x.val x.property
      obtain ⟨a', b', hy⟩ := e6InvariantValues y.val y.property
      rw [hx, hy] at h₁ h₂
      change a = a' at h₁
      change b = b' at h₂
      exact Subtype.ext (hx.trans (h₁ ▸ h₂ ▸ hy.symm))
    · intro z
      refine ⟨⟨![-2*z 0-z 1, z 0, z 0, z 1, z 0, -2*z 0-z 1],
        e6InvariantValues_mem (z 0) (z 1)⟩, ?_⟩
      funext i
      fin_cases i <;> rfl
  simpa using (LinearEquiv.ofBijective f hf).finrank_eq

/-- The invariant directions of the E₇ reversal have dimension four. -/
private theorem e7InvariantDirections_finrank :
    Module.finrank ℚ (invariantDirections e7Highest e7Reverse) = 4 := by
  let U := invariantDirections e7Highest e7Reverse
  let f : U →ₗ[ℚ] (Fin 4 → ℚ) :=
    LinearMap.pi fun i => (LinearMap.proj (![0, 2, 3, 1] i)).comp U.subtype
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have h₁ : (x : Fin 7 → ℚ) 0 = (y : Fin 7 → ℚ) 0 := congrFun h 0
      have h₂ : (x : Fin 7 → ℚ) 2 = (y : Fin 7 → ℚ) 2 := congrFun h 1
      have h₃ : (x : Fin 7 → ℚ) 3 = (y : Fin 7 → ℚ) 3 := congrFun h 2
      have h₄ : (x : Fin 7 → ℚ) 1 = (y : Fin 7 → ℚ) 1 := congrFun h 3
      obtain ⟨a, b, c, d, hx⟩ := e7InvariantValues x.val x.property
      obtain ⟨a', b', c', d', hy⟩ := e7InvariantValues y.val y.property
      rw [hx, hy] at h₁ h₂ h₃ h₄
      change a = a' at h₁
      change b = b' at h₂
      change c = c' at h₃
      change d = d' at h₄
      exact Subtype.ext (hx.trans (h₁ ▸ h₂ ▸ h₃ ▸ h₄ ▸ hy.symm))
    · intro z
      refine ⟨⟨![z 0, z 3, z 1, z 2, z 1, z 0, -2*z 0-3*z 1-2*z 2-z 3],
        e7InvariantValues_mem (z 0) (z 1) (z 2) (z 3)⟩, ?_⟩
      funext i
      fin_cases i <;> rfl
  simpa using (LinearEquiv.ofBijective f hf).finrank_eq

/-- A scaled integral inverse to the Cartan matrix annihilates the type quotient. -/
private theorem alcoveStabilizer_pow_eq_one
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {A : ApartmentRoots ℚ V J} {p : V}
    {n k : ℕ} (coord : V ≃ₗ[ℚ] (Fin n → ℚ))
    {C S : Matrix (Fin n) (Fin n) ℤ} (hCS : C * S = k • 1)
    (hP : ∀ x ∈ A.coweightLattice, ∃ m : Fin n → ℤ, coord x = fun j => (m j : ℚ))
    (hQ : coord '' (A.corootLattice : Set V) =
      Set.range (fun m : Fin n → ℤ => fun j => (C.mulVec m j : ℚ)))
    (geometry : AlcoveGeometry A p) (ω : alcoveStabilizer A (A.alcove p)) :
    ω ^ k = 1 := by
  obtain ⟨f⟩ := geometry.stabilizer
  let Q := A.corootLattice.comap A.coweightLattice.subtype
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective Q (f ω).toAdd
  obtain ⟨m, hm⟩ := hP x x.property
  have hmul : C.mulVec (S.mulVec m) = k • m := by
    rw [Matrix.mulVec_mulVec, hCS, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hmem : k • x ∈ Q := by
    have hcoord : coord (k • (x : V)) ∈ coord '' (A.corootLattice : Set V) := by
      rw [hQ]
      refine ⟨S.mulVec m, ?_⟩
      change (fun j => (C.mulVec (S.mulVec m) j : ℚ)) = coord (k • (x : V))
      rw [hmul, map_nsmul, hm]
      ext j
      simp [nsmul_eq_mul]
    obtain ⟨y, hy, hxy⟩ := hcoord
    change k • (x : V) ∈ A.corootLattice
    rwa [← coord.injective hxy]
  apply f.injective
  rw [map_pow, map_one]
  change k • (f ω).toAdd = (0 : A.coweightLattice ⧸ Q)
  rw [← hx, ← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).2 hmem

set_option maxHeartbeats 1000000 in
private theorem markedAlcoveSymmetriesFor_of_permutations
    {n rank k : ℕ} {θ : Fin n → ℤ} {perms : Set (Equiv.Perm (Fin (n + 1)))}
    (hn : 0 < n) {S : Matrix (Fin n) (Fin n) ℤ}
    (hCS : exceptionalCartan n * S = k • 1)
    (hθ : ∀ i, 0 < θ i) (hSym : (exceptionalCartan n).IsSymm)
    (hhighest : {r | IsRootCoordinate (exceptionalCartan n) r}.Finite →
      IsRootCoordinate (exceptionalCartan n) (-θ) ∧
        ∀ r, IsRootCoordinate (exceptionalCartan n) r → ∀ j, -θ j ≤ r j)
    (hperms : ∀ σ : Equiv.Perm (Fin (n + 1)), σ ≠ 1 → σ ^ k = 1 →
      (∀ i j, extendedCartan θ (σ i) (σ j) = extendedCartan θ i j) → σ ∈ perms)
    (hrank : ∀ σ ∈ perms, Module.finrank ℚ (invariantDirections θ σ) = rank) :
    MarkedAlcoveSymmetriesFor.{u} n rank θ perms := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ hUnram D E M M' c b b' hNum hNum' hSC hAdj p p' e Y B A hp
  classical
  let _ := E.finiteRoots
  let _ := E.reduced
  obtain ⟨l, coordinates, hcoordinates, hwall, hpair⟩ := markedWalls b' hn hNum' θ hθ hSym hhighest p' hp
  obtain ⟨hlatticeP, _, hlatticeQ⟩ :=
    ExceptionalAffineRootSystems.cocharacterLatticeCoordinates (K := ℚ) E.datum E.base b'
      (exceptionalCartan n) (fun i j => (hNum'.2 i j).symm)
  rw [← hcoordinates] at hlatticeP hlatticeQ
  refine ⟨l, coordinates, hcoordinates, hlatticeP, hlatticeQ, hwall, ?_⟩
  intro t ht hω g ω w
  have hAffine : g = ω.val.val := affine_eq_typeChange B.ad Y.typeQuotient t ht
  have hLinear : g.linear = w.val.coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y := by
    rcases Y.ad_points with ⟨_, _, _, _, _, _, hformula, _, _⟩
    apply LinearEquiv.ext
    intro x
    have he : g x = g.linear x + g 0 := by simpa using g.map_vadd (0 : ℚ ⊗[ℤ] E.Y) x
    have horigin := hformula t 0
    rw [LinearEquiv.map_zero, zero_add] at horigin
    rw [horigin] at he
    exact add_right_cancel (he.symm.trans (hformula t x))
  let P : alcoveStabilizer A (A.alcove p') →* Equiv.Perm (Fin (n + 1)) :=
    l.symm.permCongrHom.toMonoidHom.comp Y.typeQuotient.wallPerm
  let σ := P ω
  have hlabel (i : Fin (n + 1)) : Y.typeQuotient.wallPerm ω (l i) = l (σ i) := by
    change _ = l (l.symm (Y.typeQuotient.wallPerm ω (l.symm.symm i)))
    simp
  have htransport (i : Fin (n + 1)) : A.Transports g (l i).val (l (σ i)).val := by
    rw [hAffine, ← hlabel]
    exact transports_typeWall Y.typeQuotient ω (l i)
  have hvalues (i : Fin (n + 1)) (x : ℚ ⊗[ℤ] E.Y) :
      A.wallValue (l (σ i)).val (g x) = A.wallValue (l i).val x :=
    (htransport i).1 x
  have hg : g ≠ 1 := by
    intro he
    apply hω
    apply Subtype.ext
    apply Subtype.ext
    exact hAffine.symm.trans he
  have hσ : σ ≠ 1 := typePermutation_ne_one
    (fun i x => by simpa only [Fin.cases_succ] using hwall i.succ x) hg hvalues
  have hpow : σ ^ k = 1 := by
    have hωpow := alcoveStabilizer_pow_eq_one coordinates hCS
      (fun x hx => (hlatticeP x).mp hx) hlatticeQ Y.ad.geometry ω
    change (P ω) ^ k = 1
    rw [← map_pow, hωpow, map_one]
  have hCartan (i j : Fin (n + 1)) : extendedCartan θ (σ i) (σ j) = extendedCartan θ i j := by
    have he : (extendedCartan θ (σ i) (σ j) : ℚ) = (extendedCartan θ i j : ℚ) := by
      rw [← hpair, ← hpair, ← (htransport j).2]
      exact root_transport (hvalues i) _
    exact_mod_cast he
  have hmem := hperms σ hσ hpow hCartan
  have hFixed := fixedDirections_map hwall hvalues
  refine ⟨hAffine, hLinear, σ, hmem, hlabel, hvalues, hFixed, ?_⟩
  rw [← coordinates.finrank_map_eq (fixedDirections g.linear), hFixed]
  exact hrank σ hmem

/-- The marked affine symmetry calculation under the ordered upstream proof premises. -/
theorem markedAlcoveSymmetries_conditional
    (_ : ExceptionalAlcoveNormalForm.{u})
    (_ : IntegralScalingDenominator.{u})
    (_ : StableIncidentAlcoves.{u}) :
    MarkedAlcoveSymmetries.{u} := by
  constructor
  · apply markedAlcoveSymmetriesFor_of_permutations
      (k := 3) (S := threeTimesCartanInverse) (by decide)
      (by decide) (by decide) (by decide) e6Highest_bounds
    · intro σ hσ hpow hCartan
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using e6_permutation σ hσ hpow hCartan
    · intro σ hσ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl
      · exact e6InvariantDirections_finrank
      · rw [invariantDirections_symm]
        exact e6InvariantDirections_finrank
  · apply markedAlcoveSymmetriesFor_of_permutations
      (k := 2) (S := e7ScaledCartanInverse) (by decide)
      (by decide) (by decide) (by decide) e7Highest_bounds
    · intro σ hσ _ hCartan
      simpa only [Set.mem_singleton_iff] using e7_permutation σ hσ hCartan
    · intro σ hσ
      have h : σ = e7Reverse := hσ
      subst σ
      exact e7InvariantDirections_finrank

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerAlcoveSymmetries

universe v8_closure_309ba731fa47b5c9_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerAlcoveSymmetries».«markedAlcoveSymmetries» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalInnerAlcoveSymmetries».«MarkedAlcoveSymmetries».{v8_closure_309ba731fa47b5c9_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerAlcoveSymmetries».«markedAlcoveSymmetries_conditional».{v8_closure_309ba731fa47b5c9_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«exceptionalAlcoveNormalForm».{v8_closure_309ba731fa47b5c9_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«integralScalingDenominator».{v8_closure_309ba731fa47b5c9_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«stableIncidentAlcoves».{v8_closure_309ba731fa47b5c9_u0})
