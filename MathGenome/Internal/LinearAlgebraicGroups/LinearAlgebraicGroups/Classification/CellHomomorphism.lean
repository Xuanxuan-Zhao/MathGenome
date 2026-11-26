import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CellHomomorphism
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open scoped commutatorElement

namespace LinearAlgebraicGroups.Classification.CellHomomorphism

private def generators {I P : Type*} [Group P] (F : ℕ → I → Subgroup P) (n : ℕ) :
    Set P := {x | ∃ i, x ∈ F n i}

private abbrev level {I P : Type*} [Group P] (F : ℕ → I → Subgroup P) (n : ℕ) :
    Subgroup P := Subgroup.normalClosure (generators F n)

private theorem product_update {I P Q : Type*} [DecidableEq I] [Group P] [Group Q]
    (π : P →* Q) (x : I → P) {l : List I} (hl : l.Nodup) {i : I} (hi : i ∈ l)
    (z : P) (hz : ∀ q : Q, Commute (π z) q) :
    (l.map (fun j ↦ π (Function.update x i (z * x i) j))).prod =
      π z * (l.map fun j ↦ π (x j)).prod := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    rcases List.mem_cons.mp hi with rfl | hi
    · have ht : l.map (fun a ↦ π (Function.update x i (z * x i) a)) =
          l.map (fun a ↦ π (x a)) := by
        apply List.map_congr_left
        intro a ha
        rw [Function.update_of_ne (by rintro rfl; exact hl.1 ha)]
      simp [ht, mul_assoc]
    · have hji : j ≠ i := by
        rintro rfl
        exact hl.1 hi
      simp only [List.map_cons, List.prod_cons, Function.update_of_ne hji]
      rw [ih hl.2 hi, ← mul_assoc, (hz (π (x j))).symm.eq, mul_assoc]

/-- At a nilpotent congruence level the paired generators collect in the
chosen order. Commutation is only required modulo the next level. -/
private theorem ordered_product_of_nilpotent_filtration {I P : Type*} [Group P]
    (F : ℕ → I → Subgroup P)
    (hgen : Subgroup.closure (generators F 1) = ⊤)
    (hle : ∀ n i, 1 ≤ n → F n i ≤ F 1 i)
    (hcomm : ∀ n i j x y, 1 ≤ n → x ∈ F n i → y ∈ F 1 j →
      ⁅x, y⁆ ∈ level F (n + 1))
    {N : ℕ} (hN : level F (N + 1) = ⊥)
    (l : List I) (hl : l.Nodup) (hall : ∀ i, i ∈ l) (g : P) :
    ∃ x : I → P, (∀ i, x i ∈ F 1 i) ∧ g = (l.map x).prod := by
  classical
  have approx (n : ℕ) : ∃ x : I → P, (∀ i, x i ∈ F 1 i) ∧
      g / (l.map x).prod ∈ level F (n + 1) := by
    induction n with
    | zero =>
      refine ⟨fun _ ↦ 1, fun i ↦ (F 1 i).one_mem, ?_⟩
      apply Subgroup.closure_le_normalClosure
      rw [hgen]
      trivial
    | succ n ih =>
      obtain ⟨x, hx, hg⟩ := ih
      let π := QuotientGroup.mk' (level F (n + 1 + 1))
      let Q := P ⧸ level F (n + 1 + 1)
      let S : Set Q := {q | ∃ a : I → P, (∀ i, a i ∈ F 1 i) ∧ q = (l.map (π ∘ a)).prod}
      let K : Subgroup Q :=
        { carrier := {z | ∀ q ∈ S, z * q ∈ S ∧ z⁻¹ * q ∈ S}
          one_mem' := by simp
          mul_mem' := by
            intro a b ha hb q hq
            exact ⟨by simpa only [mul_assoc] using (ha _ (hb _ hq).1).1,
              by simpa only [mul_inv_rev, mul_assoc] using (hb _ (ha _ hq).2).2⟩
          inv_mem' := by
            intro a ha q hq
            exact ⟨(ha q hq).2, by rw [inv_inv]; exact (ha q hq).1⟩ }
      have hcentral {z : P} {i : I} (hz : z ∈ F (n + 1) i) :
          ∀ q : Q, Commute (π z) q := by
        have hc : Subgroup.closure (generators F 1) ≤
            (Subgroup.centralizer ({π z} : Set Q)).comap π := by
          rw [Subgroup.closure_le]
          rintro y ⟨j, hy⟩
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          have h := hcomm (n + 1) i j z y (by omega) hz hy
          have h' : π ⁅z, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h
          rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h'
          exact h'.symm.eq
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
        have hy : y ∈ Subgroup.closure (generators F 1) := by rw [hgen]; trivial
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hc hy)).symm
      have hpreserve {z : P} {i : I} (hz : z ∈ F (n + 1) i)
          (q : Q) (hq : q ∈ S) : π z * q ∈ S := by
        obtain ⟨a, ha, rfl⟩ := hq
        refine ⟨Function.update a i (z * a i), ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            rw [Function.update_self]
            exact mul_mem (hle _ _ (by omega) hz) (ha _)
          · simpa only [Function.update_of_ne hji] using ha j
        · exact (product_update π a hl (hall i) z (hcentral hz)).symm
      have hK : level F (n + 1) ≤ K.comap π := by
        apply (Subgroup.closure_le _).mpr
        intro v hv
        obtain ⟨z, ⟨i, hz⟩, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hv
        obtain ⟨c, rfl⟩ := isConj_iff.mp hc
        have he : π (c * z * c⁻¹) = π z := by
          rw [map_mul, map_mul, map_inv, (hcentral hz (π c)).symm.eq]
          simp [mul_assoc]
        change π (c * z * c⁻¹) ∈ K
        rw [he]
        intro q hq
        exact ⟨hpreserve hz q hq, by simpa only [map_inv] using hpreserve (inv_mem hz) q hq⟩
      have hxS : π (l.map x).prod ∈ S :=
        ⟨x, hx, by rw [MonoidHom.map_list_prod, List.map_map]⟩
      have hπg : π g ∈ S := by
        have hm := (hK hg : π (g / (l.map x).prod) ∈ K) (π (l.map x).prod) hxS
        simpa only [← map_mul, div_mul_cancel] using hm.1
      obtain ⟨a, ha, he⟩ := hπg
      refine ⟨a, ha, QuotientGroup.eq_iff_div_mem.mp ?_⟩
      change π g = π (l.map a).prod
      rwa [MonoidHom.map_list_prod, List.map_map]
  obtain ⟨x, hx, hg⟩ := approx N
  rw [hN, Subgroup.mem_bot, div_eq_one] at hg
  exact ⟨x, hx, hg⟩

section Collection

variable {R U P I : Type*} [CommRing R] [Group U] [Group P]
variable (J : Ideal R) (root : I → Multiplicative R →* P)
variable (torus : U →* P) (K : ℕ → Subgroup U)

private def parameterSubgroup (J : Ideal R) : Subgroup (Multiplicative R) where
  carrier := {x | x.toAdd ∈ J}
  one_mem' := J.zero_mem
  mul_mem' := J.add_mem
  inv_mem' := J.neg_mem

/-- One letter at a specified congruence level, either a root or the torus. -/
private def letters (n : ℕ) : Option I → Subgroup P
  | some α => (parameterSubgroup (J ^ n)).map (root α)
  | none => (K n).map torus

private abbrev generated := Subgroup.closure (generators (letters J root torus K) 1)

private abbrev filteredLetters (n : ℕ) (i : Option I) :
    Subgroup (generated J root torus K) :=
  (letters J root torus K n i).subgroupOf (generated J root torus K)

private theorem filteredLetters_generate :
    Subgroup.closure (generators (filteredLetters J root torus K) 1) = ⊤ := by
  let L := generated J root torus K
  let F := filteredLetters J root torus K
  let C := Subgroup.closure (generators F 1)
  have h : L ≤ C.map L.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨⟨x, Subgroup.subset_closure ⟨i, hi⟩⟩, Subgroup.subset_closure ⟨i, hi⟩, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, e⟩ := h x.property
  have he : y = x := Subtype.ext e
  exact he ▸ hy

private theorem filteredLetters_le (hK : ∀ n, 1 ≤ n → K n ≤ K 1)
    (n : ℕ) (i : Option I) (hn : 1 ≤ n) :
    filteredLetters J root torus K n i ≤ filteredLetters J root torus K 1 i := by
  intro x hx
  change (x : P) ∈ letters J root torus K n i at hx
  change (x : P) ∈ letters J root torus K 1 i
  cases i with
  | none => exact Subgroup.map_mono (hK n hn) hx
  | some α =>
    exact Subgroup.map_mono (show parameterSubgroup (J ^ n) ≤ parameterSubgroup (J ^ 1)
      from fun z hz ↦ (Ideal.pow_le_pow_right (I := J) hn) (show z.toAdd ∈ J ^ n from hz)) hx

private theorem filteredLetters_last {N : ℕ}
    (hJ : J ^ (N + 1) = ⊥) (hK : K (N + 1) = ⊥) :
    level (filteredLetters J root torus K) (N + 1) = ⊥ := by
  apply bot_unique
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨i, hi⟩
  change (x : P) ∈ letters J root torus K (N + 1) i at hi
  have he : (x : P) = 1 := by
    cases i with
    | none => simpa [letters, hK] using hi
    | some α =>
      obtain ⟨a, ha, rfl₁⟩ := hi
      change a.toAdd ∈ J ^ (N + 1) at ha
      rw [hJ, Ideal.mem_bot] at ha
      have : a = 1 := ha
      rw [← rfl₁, this, map_one]
  exact Subgroup.mem_bot.mpr (Subtype.ext he)

private theorem product_mem_power {n : ℕ} {x y : R}
    (hx : x ∈ J ^ n) (hy : y ∈ J ^ 1) : x * y ∈ J ^ (n + 1) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hx hy

private theorem positive_power_product_mem {n i j : ℕ} {x y : R}
    (hx : x ∈ J ^ n) (hy : y ∈ J ^ 1) (hi : 0 < i) (hj : 0 < j) (a : R) :
    a * x ^ i * y ^ j ∈ J ^ (n + 1) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have e : a * x ^ (i + 1) * y ^ (j + 1) = (a * x ^ i * y ^ j) * (x * y) := by
    simp only [pow_succ]
    ac_rfl
  rw [e]
  exact (J ^ (n + 1)).mul_mem_left _ (product_mem_power J hx hy)

private theorem divide_sub_mem {n : ℕ} {x y : R} (v : R) (c : Rˣ)
    (hc : (c : R) = 1 + x * y) (hx : x ∈ J ^ n) (hy : y ∈ J ^ 1) :
    v * (↑c⁻¹ : R) - v ∈ J ^ (n + 1) := by
  have e : (↑c⁻¹ : R) - 1 = -(↑c⁻¹ : R) * (x * y) := by
    calc
      (↑c⁻¹ : R) - 1 = (↑c⁻¹ : R) - ↑c⁻¹ * ↑c := by rw [Units.inv_mul]
      _ = _ := by rw [hc]; ring
  rw [← mul_sub_one, e]
  exact (J ^ (n + 1)).mul_mem_left _ ((J ^ (n + 1)).mul_mem_left _ (product_mem_power J hx hy))

private theorem mem_generated {n : ℕ} (hn : 1 ≤ n)
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1)
    {i : Option I} {x : P} (hx : x ∈ letters J root torus K n i) :
    x ∈ generated J root torus K := by
  apply Subgroup.subset_closure
  refine ⟨i, ?_⟩
  cases i with
  | none => exact Subgroup.map_mono (hK n hn) hx
  | some α =>
    exact Subgroup.map_mono (show parameterSubgroup (J ^ n) ≤ parameterSubgroup (J ^ 1)
      from fun z hz ↦ (Ideal.pow_le_pow_right (I := J) hn) (show z.toAdd ∈ J ^ n from hz)) hx

private theorem exists_level_letter {n : ℕ} (hn : 1 ≤ n)
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1)
    {i : Option I} {x : P} (hx : x ∈ letters J root torus K n i) :
    ∃ a : generated J root torus K, a ∈ level (filteredLetters J root torus K) n ∧
      (a : P) = x :=
  ⟨⟨x, mem_generated J root torus K hn hK hx⟩,
    Subgroup.subset_normalClosure ⟨i, hx⟩, rfl⟩

private theorem exists_level_root {n : ℕ} (hn : 1 ≤ n)
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1)
    (i : I) {x : R} (hx : x ∈ J ^ n) :
    ∃ a : generated J root torus K, a ∈ level (filteredLetters J root torus K) n ∧
      (a : P) = root i (Multiplicative.ofAdd x) :=
  exists_level_letter J root torus K hn hK (i := some i) ⟨_, hx, rfl⟩

private theorem exists_level_root_product {n : ℕ} (hn : 1 ≤ n)
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1) (l : List (I × R))
    (hl : ∀ p ∈ l, p.2 ∈ J ^ n) :
    ∃ a : generated J root torus K, a ∈ level (filteredLetters J root torus K) n ∧
      (a : P) = (l.map fun p ↦ root p.1 (Multiplicative.ofAdd p.2)).prod := by
  induction l with
  | nil => exact ⟨1, one_mem _, rfl⟩
  | cons p l ih =>
    obtain ⟨b, hb, eb⟩ := exists_level_root J root torus K hn hK p.1
      (hl p List.mem_cons_self)
    obtain ⟨a, ha, ea⟩ := ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))
    refine ⟨b * a, mul_mem hb ha, ?_⟩
    change (b : P) * (a : P) = _
    rw [eb, ea, List.map_cons, List.prod_cons]

private theorem commutator_root_root_mem {n : ℕ} {i j : I}
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1) (hn : 1 ≤ n)
    {a b : generated J root torus K}
    {x y : R} (hx : x ∈ J ^ n) (hy : y ∈ J ^ 1)
    (ha : (a : P) = root i (Multiplicative.ofAdd x))
    (hb : (b : P) = root j (Multiplicative.ofAdd y))
    (opposite : I → I) (coroot : I → Rˣ → U)
    (hcoroot : ∀ i n (c : Rˣ), (c : R) - 1 ∈ J ^ n → coroot i c ∈ K n)
    (hnil : IsNilpotent J)
    (hgauss : ∀ i x y (c : Rˣ), (c : R) = 1 + x * y →
      root i (Multiplicative.ofAdd x) * root (opposite i) (Multiplicative.ofAdd y) =
        root (opposite i) (Multiplicative.ofAdd (y * (↑c⁻¹ : R))) *
          torus (coroot i c) * root i (Multiplicative.ofAdd (x * (↑c⁻¹ : R))))
    (hsigned : i ≠ j → j ≠ opposite i →
      ∃ l : List (I × R), (∀ p ∈ l, p.2 ∈ J ^ (n + 1)) ∧
        ⁅root i (Multiplicative.ofAdd x), root j (Multiplicative.ofAdd y)⁆ =
          (l.map fun p ↦ root p.1 (Multiplicative.ofAdd p.2)).prod) :
    ⁅a, b⁆ ∈ level (filteredLetters J root torus K) (n + 1) := by
  by_cases he : j = i
  · subst j
    have hh : ⁅a, b⁆ = 1 := by
      apply Subtype.ext
      change ⁅(a : P), (b : P)⁆ = 1
      rw [ha, hb, commutatorElement_eq_one_iff_commute]
      exact (Commute.all _ _).map (root i)
    rw [hh]
    exact one_mem _
  by_cases hop : j = opposite i
  · subst j
    have hxy : x * y ∈ J := by
      rw [← pow_one J]
      exact (Ideal.pow_le_pow_right (I := J) (by omega : 1 ≤ n + 1)) (product_mem_power J hx hy)
    have hnilxy : IsNilpotent (x * y) := by
      obtain ⟨m, hm⟩ := hnil
      refine ⟨m, Ideal.mem_bot.mp ?_⟩
      simpa only [hm, Ideal.zero_eq_bot] using Ideal.pow_mem_pow hxy m
    obtain ⟨c, hc⟩ := hnilxy.isUnit_one_add
    have hcJ : (c : R) - 1 ∈ J ^ (n + 1) := by
      rw [hc, add_sub_cancel_left]
      exact product_mem_power J hx hy
    obtain ⟨x', hx', ex'⟩ := exists_level_root J root torus K
      (n := n + 1) (by omega) hK i (divide_sub_mem J x c hc hx hy)
    obtain ⟨y', hy', ey'⟩ := exists_level_root J root torus K
      (n := n + 1) (by omega) hK (opposite i) (divide_sub_mem J y c hc hx hy)
    obtain ⟨c', hc', ec'⟩ := exists_level_letter J root torus K
      (n := n + 1) (by omega) hK (i := none) ⟨_, hcoroot i _ c hcJ, rfl⟩
    have e : a * b = y' * b * c' * (x' * a) := by
      apply Subtype.ext
      change (a : P) * (b : P) = (y' : P) * (b : P) * (c' : P) * ((x' : P) * (a : P))
      have ey : root (opposite i) (Multiplicative.ofAdd (y * (↑c⁻¹ : R) - y)) *
          root (opposite i) (Multiplicative.ofAdd y) =
          root (opposite i) (Multiplicative.ofAdd (y * (↑c⁻¹ : R))) := by
        rw [← (root (opposite i)).map_mul]
        exact congrArg (fun r : R ↦ root (opposite i) (Multiplicative.ofAdd r))
          (sub_add_cancel _ _)
      have ex : root i (Multiplicative.ofAdd (x * (↑c⁻¹ : R) - x)) *
          root i (Multiplicative.ofAdd x) = root i (Multiplicative.ofAdd (x * (↑c⁻¹ : R))) := by
        rw [← (root i).map_mul]
        exact congrArg (fun r : R ↦ root i (Multiplicative.ofAdd r)) (sub_add_cancel _ _)
      rw [ha, hb, ey', ec', ex', ey, ex, hgauss i x y c hc]
    rw [commutatorElement_def, e]
    have e' : y' * b * c' * (x' * a) * a⁻¹ * b⁻¹ = y' * (b * (c' * x') * b⁻¹) := by
      group
    rw [e']
    exact mul_mem hy' (Subgroup.Normal.conj_mem inferInstance _ (mul_mem hc' hx') b)
  · obtain ⟨l, hl, e⟩ := hsigned (Ne.symm he) hop
    obtain ⟨z, hz, ez⟩ := exists_level_root_product J root torus K (by omega) hK l hl
    have eq : ⁅a, b⁆ = z := by
      apply Subtype.ext
      change ⁅(a : P), (b : P)⁆ = (z : P)
      rw [ha, hb, e, ez]
    exact eq ▸ hz

private theorem commutator_torus_root_mem {n : ℕ} {i : I}
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1) (hn : 1 ≤ n)
    {a b : generated J root torus K}
    {t : U} {x v : R} (hv : (v - 1) * x ∈ J ^ (n + 1))
    (ha : (a : P) = torus t) (hb : (b : P) = root i (Multiplicative.ofAdd x))
    (h : torus t * root i (Multiplicative.ofAdd x) * (torus t)⁻¹ =
      root i (Multiplicative.ofAdd (v * x))) :
    ⁅a, b⁆ ∈ level (filteredLetters J root torus K) (n + 1) := by
  obtain ⟨c, hc, ec⟩ := exists_level_root J root torus K (by omega) hK i hv
  have e : ⁅a, b⁆ = c := by
    apply Subtype.ext
    change ⁅(a : P), (b : P)⁆ = (c : P)
    rw [ha, hb, ec, commutatorElement_def, h, ← (root i).map_inv, ← (root i).map_mul]
    apply congrArg (fun r : R ↦ root i (Multiplicative.ofAdd r))
    change v * x + -x = (v - 1) * x
    rw [sub_mul, one_mul, sub_eq_add_neg]
  exact e ▸ hc

private theorem commutator_filteredLetters_mem
    (hK : ∀ n, 1 ≤ n → K n ≤ K 1) (hTorus : ∀ t s : U, Commute t s)
    (opposite : I → I) (coroot : I → Rˣ → U) (weight : I → U → R)
    (hcoroot : ∀ i n (c : Rˣ), (c : R) - 1 ∈ J ^ n → coroot i c ∈ K n)
    (hweight : ∀ i n t, t ∈ K n → weight i t - 1 ∈ J ^ n)
    (hnil : IsNilpotent J)
    (hgauss : ∀ i x y (c : Rˣ), (c : R) = 1 + x * y →
      root i (Multiplicative.ofAdd x) * root (opposite i) (Multiplicative.ofAdd y) =
        root (opposite i) (Multiplicative.ofAdd (y * (↑c⁻¹ : R))) *
          torus (coroot i c) * root i (Multiplicative.ofAdd (x * (↑c⁻¹ : R))))
    (hscalar : ∀ i t x, torus t * root i (Multiplicative.ofAdd x) * (torus t)⁻¹ =
      root i (Multiplicative.ofAdd (weight i t * x)))
    (hsigned : ∀ n i j x y, x ∈ J ^ n → y ∈ J ^ 1 → i ≠ j → j ≠ opposite i →
      ∃ l : List (I × R), (∀ p ∈ l, p.2 ∈ J ^ (n + 1)) ∧
        ⁅root i (Multiplicative.ofAdd x), root j (Multiplicative.ofAdd y)⁆ =
          (l.map fun p ↦ root p.1 (Multiplicative.ofAdd p.2)).prod)
    (n : ℕ) (i j : Option I) (a b : generated J root torus K) (hn : 1 ≤ n)
    (ha : a ∈ filteredLetters J root torus K n i)
    (hb : b ∈ filteredLetters J root torus K 1 j) :
    ⁅a, b⁆ ∈ level (filteredLetters J root torus K) (n + 1) := by
  cases i with
  | none =>
    obtain ⟨t, ht, et⟩ : ∃ t ∈ K n, torus t = (a : P) := ha
    cases j with
    | none =>
      obtain ⟨s, _, es⟩ : ∃ s ∈ K 1, torus s = (b : P) := hb
      have e : ⁅a, b⁆ = 1 := by
        apply Subtype.ext
        change ⁅(a : P), (b : P)⁆ = 1
        rw [← et, ← es, commutatorElement_eq_one_iff_commute]
        exact (hTorus t s).map torus
      rw [e]
      exact one_mem _
    | some j =>
      obtain ⟨x, hx, ex⟩ := (show (b : P) ∈
        (parameterSubgroup (J ^ (1 : ℕ))).map (root j) from hb)
      exact commutator_torus_root_mem J root torus K hK hn
        (product_mem_power J (hweight j n t ht) hx) et.symm ex.symm (hscalar j t x.toAdd)
  | some i =>
    obtain ⟨x, hx, ex⟩ : ∃ x : R, x ∈ J ^ n ∧
        root i (Multiplicative.ofAdd x) = (a : P) := ha
    cases j with
    | none =>
      obtain ⟨t, ht, et⟩ : ∃ t ∈ K 1, torus t = (b : P) := hb
      have hv : (weight i t - 1) * x ∈ J ^ (n + 1) := by
        rw [mul_comm]
        exact product_mem_power J hx (hweight i 1 t ht)
      rw [← commutatorElement_inv b a]
      exact inv_mem (commutator_torus_root_mem J root torus K hK hn
        hv et.symm ex.symm (hscalar i t x))
    | some j =>
      obtain ⟨y, hy, ey⟩ := (show (b : P) ∈
        (parameterSubgroup (J ^ (1 : ℕ))).map (root j) from hb)
      exact commutator_root_root_mem J root torus K hK hn hx hy ex.symm ey.symm
        opposite coroot hcoroot hnil hgauss (hsigned n i j x y.toAdd hx hy)


end Collection

section CellPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CellHomomorphism (Coordinates SameSignedCommutators cellCoordinatesMap
  rootFactorsIso)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.OrderedRootProducts (Enumerates product rootCellMap rootProduct)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint mapPoints_cocharacterPoint)

open private rootPoint_add rootPoint_zero mapPoints_rootPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private rootPoint_injective rootPoint_surjective cocharacterPoint_postcompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private characterValue_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private unitPointHom unitPointHom_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]
variable {G H : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
variable [IsCommMonObj T.group.X] [IsCommMonObj S.group.X]
variable {D : Datum T} {E : Datum S} {A : AdditiveLine k}

private abbrev onPoints {J L : GroupScheme k} (f : J ⟶ L) (R : TestAlgebra k) :
    GroupPoints J R →* GroupPoints L R :=
  (((groupPointsFunctor k).map f).app R).hom

private abbrev changePoints (J : GroupScheme k) {R R' : TestAlgebra k} (a : R ⟶ R') :
    GroupPoints J R →* GroupPoints J R' :=
  (((groupPointsFunctor k).obj J).map a).hom

private def rootHom {J : GroupScheme k} (f : A.group ⟶ J) (R : TestAlgebra k) :
    Multiplicative R →* GroupPoints J R where
  toFun x := rootPoint f R x.toAdd
  map_one' := rootPoint_zero f R
  map_mul' := rootPoint_add f R

private abbrev rootFactors (X : Coordinates D A) (l : List (Root T)) :=
  product (fun α ↦ (X.groups α).val.group.X) l

private abbrev cell (X : Coordinates D A) (negative positive : List (Root T)) :=
  rootFactors X negative ⊗ (T.group.X ⊗ rootFactors X positive)

private def rootFactorsPoint (X : Coordinates D A) (R : TestAlgebra k)
    (v : Root T → R) : (l : List (Root T)) → Points (rootFactors X l) R
  | [] => toUnit _
  | α :: l => lift (rootPoint (X.parametrization α).hom R (v α)) (rootFactorsPoint X R v l)

private theorem rootFactorsPoint_eq_iff (X : Coordinates D A) (R : TestAlgebra k)
    (v w : Root T → R) (l : List (Root T)) :
    rootFactorsPoint X R v l = rootFactorsPoint X R w l ↔ ∀ α ∈ l, v α = w α := by
  induction l with
  | nil => exact ⟨fun _ _ h ↦ False.elim (List.not_mem_nil h), fun _ ↦ toUnit_unique _ _⟩
  | cons α l ih =>
    constructor
    · intro h β hβ
      rcases List.mem_cons.mp hβ with rfl | hβ
      · apply rootPoint_injective (X.parametrization β)
        simpa only [rootFactorsPoint, lift_fst] using
          congrArg (fun p : Points (rootFactors X (β :: l)) R ↦ p ≫ fst _ _) h
      · apply ih.mp _ β hβ
        simpa only [rootFactorsPoint, lift_snd] using
          congrArg (fun p : Points (rootFactors X (α :: l)) R ↦ p ≫ snd _ _) h
    · intro h
      apply CartesianMonoidalCategory.hom_ext
      · simp only [rootFactorsPoint, lift_fst, h α List.mem_cons_self]
      · simp only [rootFactorsPoint, lift_snd]
        exact ih.mpr (fun β hβ ↦ h β (List.mem_cons_of_mem α hβ))

private theorem rootFactorsPoint_surjective (X : Coordinates D A) (R : TestAlgebra k)
    (l : List (Root T)) (hl : l.Nodup) :
    Function.Surjective (fun v : Root T → R ↦ rootFactorsPoint X R v l) := by
  classical
  induction l with
  | nil => exact fun p ↦ ⟨0, toUnit_unique _ _⟩
  | cons α l ih =>
    intro p
    obtain ⟨a, ha⟩ := rootPoint_surjective (X.parametrization α) R (p ≫ fst _ _)
    obtain ⟨v, hv⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update v α a, CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
    · simpa only [rootFactorsPoint, lift_fst, Function.update_self] using ha
    · simp only [rootFactorsPoint, lift_snd, ← hv]
      apply (rootFactorsPoint_eq_iff X R _ _ l).mpr
      intro β hβ
      have hne : β ≠ α := by rintro rfl; exact (List.nodup_cons.mp hl).1 hβ
      exact Function.update_of_ne hne a v

private theorem rootFactorsPoint_map (X : Coordinates D A) {R R' : TestAlgebra k}
    (f : R ⟶ R') (v : Root T → R) (l : List (Root T)) :
    mapPoints f (rootFactorsPoint X R v l) =
      rootFactorsPoint X R' (fun α ↦ f.hom (v α)) l := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons α l ih =>
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [rootFactorsPoint, mapPoints, Category.assoc, lift_fst] using
        mapPoints_rootPoint (X.parametrization α).hom f (v α)
    · simpa only [rootFactorsPoint, mapPoints, Category.assoc, lift_snd] using ih

private theorem rootFactorsPoint_mul (X : Coordinates D A) (R : TestAlgebra k)
    (v : Root T → R) (l : List (Root T)) :
    rootFactorsPoint X R v l ≫ rootProduct X.groups l =
      (l.map fun α ↦ rootPoint (X.root α) R (v α)).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons α l ih =>
    simp only [rootFactorsPoint, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      List.map_cons, List.prod_cons, ih]
    rfl

private theorem rootFactorsPoint_transport (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (R : TestAlgebra k) (v : Root T → R) (l : List (Root T)) :
    rootFactorsPoint X R v l ≫ (rootFactorsIso X Y d l).hom =
      rootFactorsPoint Y R (v ∘ d.symm) (l.map d) := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons α l ih =>
    change lift (rootPoint (X.parametrization α).hom R (v α)) (rootFactorsPoint X R v l) ≫
        (((Grp.forget (SchemeOver k)).mapIso
          ((X.parametrization α).symm ≪≫ Y.parametrization (d α))).hom ⊗ₘ
          (rootFactorsIso X Y d l).hom) =
      lift (rootPoint (Y.parametrization (d α)).hom R ((v ∘ d.symm) (d α)))
        (rootFactorsPoint Y R (v ∘ d.symm) (l.map d))
    rw [lift_map, ih, Function.comp_apply, Equiv.symm_apply_apply]
    congr 1
    change rootPoint (X.parametrization α).hom R (v α) ≫
      ((X.parametrization α).inv ≫ (Y.parametrization (d α)).hom).hom.hom = _
    simp only [rootPoint, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id_assoc]

private def cellPoint (X : Coordinates D A) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    Points (cell X negative positive) R :=
  lift (rootFactorsPoint X R v negative) (lift t (rootFactorsPoint X R v positive))

private theorem cellPoint_surjective (X : Coordinates D A) (R : TestAlgebra k)
    (negative positive : List (Root T)) (hn : negative.Nodup) (hp : positive.Nodup)
    (hd : negative.Disjoint positive) (p : Points (cell X negative positive) R) :
    ∃ v t, cellPoint X R negative positive v t = p := by
  classical
  obtain ⟨v, hv⟩ := rootFactorsPoint_surjective X R negative hn (p ≫ fst _ _)
  obtain ⟨w, hw⟩ := rootFactorsPoint_surjective X R positive hp (p ≫ snd _ _ ≫ snd _ _)
  change rootFactorsPoint X R v negative = _ at hv
  change rootFactorsPoint X R w positive = _ at hw
  let a := fun α ↦ if α ∈ negative then v α else w α
  have hn' : rootFactorsPoint X R a negative = rootFactorsPoint X R v negative :=
    (rootFactorsPoint_eq_iff X R _ _ _).mpr (fun α hα ↦ if_pos hα)
  have hp' : rootFactorsPoint X R a positive = rootFactorsPoint X R w positive :=
    (rootFactorsPoint_eq_iff X R _ _ _).mpr (fun α hα ↦ if_neg (fun h ↦ hd h hα))
  refine ⟨a, p ≫ snd _ _ ≫ fst _ _, ?_⟩
  unfold cellPoint
  rw [hn', hp', hv, hw]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [lift_fst]
  · simp only [lift_snd]
    exact lift_comp_fst_snd (p ≫ snd _ _)

private theorem cellPoint_map (X : Coordinates D A) {R R' : TestAlgebra k}
    (f : R ⟶ R') (negative positive : List (Root T)) (v : Root T → R)
    (t : GroupPoints T.group R) :
    mapPoints f (cellPoint X R negative positive v t) =
      cellPoint X R' negative positive (fun α ↦ f.hom (v α)) (changePoints T.group f t) := by
  unfold cellPoint
  simp only [mapPoints, comp_lift]
  change lift (mapPoints f _) (lift (changePoints T.group f t) (mapPoints f _)) = _
  rw [rootFactorsPoint_map, rootFactorsPoint_map]

private theorem cellPoint_transport (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    cellPoint X R negative positive v t ≫ cellCoordinatesMap X Y d τ negative positive =
      cellPoint Y R (negative.map d) (positive.map d) (v ∘ d.symm) (onPoints τ R t) := by
  simp only [cellPoint, cellCoordinatesMap, lift_map, rootFactorsPoint_transport]
  rfl

private theorem cellPoint_mul (X : Coordinates D A) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    cellPoint X R negative positive v t ≫ rootCellMap T X.groups negative positive =
      (negative.map (fun α ↦ rootPoint (X.root α) R (v α))).prod *
        (onPoints T.inclusion R t *
          (positive.map (fun α ↦ rootPoint (X.root α) R (v α))).prod) := by
  simp only [cellPoint, rootCellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    rootFactorsPoint_mul]
  rfl

private abbrev quotientAlgebra {R : TestAlgebra k} (I : Ideal R) : TestAlgebra k :=
  CommAlgCat.of k (R ⧸ I)

private abbrev quotientMap {R : TestAlgebra k} (I : Ideal R) : R ⟶ quotientAlgebra I :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)

private def torusCongruence {R : TestAlgebra k} (J : Ideal R) (n : ℕ) :
    Subgroup (GroupPoints T.group R) :=
  (changePoints T.group (quotientMap (J ^ n))).ker

private theorem torusCongruence_mono {R : TestAlgebra k} (J : Ideal R) {m n : ℕ}
    (h : m ≤ n) : torusCongruence (T := T) J n ≤ torusCongruence (T := T) J m := by
  intro t ht
  let f : quotientAlgebra (J ^ n) ⟶ quotientAlgebra (J ^ m) :=
    CommAlgCat.ofHom (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right h))
  have hf : quotientMap (J ^ n) ≫ f = quotientMap (J ^ m) := rfl
  change changePoints T.group (quotientMap (J ^ m)) t = 1
  change changePoints T.group (quotientMap (J ^ n)) t = 1 at ht
  rw [← hf]
  change (((groupPointsFunctor k).obj T.group).map (quotientMap (J ^ n) ≫ f)) t = 1
  rw [((groupPointsFunctor k).obj T.group).map_comp]
  change changePoints T.group f (changePoints T.group (quotientMap (J ^ n)) t) = 1
  rw [ht, map_one]

private theorem torusCongruence_eq_bot {R : TestAlgebra k} (J : Ideal R) {n : ℕ}
    (h : J ^ n = ⊥) : torusCongruence (T := T) J n = ⊥ := by
  unfold torusCongruence
  rw [h]
  have e : IsIso (quotientMap (⊥ : Ideal R)) := by
    change IsIso (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k (⊥ : Ideal R)))
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨fun x y he ↦ sub_eq_zero.mp (Ideal.mem_bot.mp (Ideal.Quotient.eq.mp he)),
        Ideal.Quotient.mkₐ_surjective k _⟩
  exact MonoidHom.ker_eq_bot _
    (ConcreteCategory.bijective_of_isIso (((groupPointsFunctor k).obj T.group).map
      (quotientMap (⊥ : Ideal R)))).1

private theorem cocharacterPoint_mem_congruence {R : TestAlgebra k} (J : Ideal R)
    (c : Cocharacter T.group) (n : ℕ) (z : Rˣ) (hz : (z : R) - 1 ∈ J ^ n) :
    cocharacterPoint c R z ∈ torusCongruence (T := T) J n := by
  change mapPoints (quotientMap (J ^ n)) (cocharacterPoint c R z) = 1
  rw [mapPoints_cocharacterPoint]
  have ez : Units.map (quotientMap (J ^ n)).hom.toMonoidHom z = 1 :=
    Units.ext (Ideal.Quotient.mk_eq_one_iff_sub_mem _ |>.mpr hz)
  rw [ez]
  change onPoints c _ (LinearAlgebraicGroups.CocharacterDynamics.unitPoint _ 1) = 1
  rw [← unitPointHom_apply, map_one, map_one]

private theorem characterValue_identity {L : GroupScheme k} (χ : Character L)
    (R : TestAlgebra k) : characterValue χ R 1 = 1 := by
  have e : (1 : GroupPoints L R) ≫ χ.hom.hom =
      (1 : GroupPoints L R) ≫ (1 : Character L).hom.hom := by
    change onPoints χ R 1 = onPoints (1 : Character L) R 1
    rw [map_one, map_one]
  simpa only [characterValue, e] using characterValue_one R (1 : GroupPoints L R)

private theorem characterValue_sub_one_mem {R : TestAlgebra k} (J : Ideal R)
    (χ : Character T.group) (n : ℕ) (t : GroupPoints T.group R)
    (ht : t ∈ torusCongruence (T := T) J n) : characterValue χ R t - 1 ∈ J ^ n := by
  apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp
  change (quotientMap (J ^ n)).hom (characterValue χ R t) = 1
  change mapPoints (quotientMap (J ^ n)) t = 1 at ht
  rw [← characterValue_naturality, ht, characterValue_identity]

private abbrev PairedPoints (R : TestAlgebra k) :=
  GroupPoints G.val R × GroupPoints H.val R

private def pairedRoot (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (R : TestAlgebra k) (α : Root T) :
    Multiplicative R →* PairedPoints (G := G) (H := H) R :=
  (rootHom (X.root α) R).prod (rootHom (Y.root (d α)) R)

private def pairedTorus (τ : T.group ⟶ S.group) (R : TestAlgebra k) :
    GroupPoints T.group R →* PairedPoints (G := G) (H := H) R :=
  (onPoints T.inclusion R).prod (onPoints (τ ≫ S.inclusion) R)

private theorem opposite_transport (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hinj : Function.Injective (Specs.CellHomomorphism.pullbackCharacters τ))
    (hχ : ∀ α, τ ≫ (d α).val = α.val) (α : Root T) :
    d (X.opposite α) = Y.opposite (d α) := by
  apply Subtype.ext
  apply hinj
  change τ ≫ (d (X.opposite α)).val =
    Specs.CellHomomorphism.pullbackCharacters τ (Y.opposite (d α)).val
  rw [hχ, X.opposite_eq, Y.opposite_eq, map_inv]
  exact congrArg Inv.inv (hχ α).symm

private theorem pairedGauss
    (hG : IsReductive G) (hH : IsReductive H)
    (hT : IsSplitTorus T.group) (hS : IsSplitTorus S.group)
    (hmT : IsGeometricallyMaximal T) (hmS : IsGeometricallyMaximal S)
    (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hop : ∀ α, d (X.opposite α) = Y.opposite (d α))
    (hc : ∀ α, Additive.toMul (D.rootDatum.coroot α) ≫ τ =
      Additive.toMul (E.rootDatum.coroot (d α))) (R : TestAlgebra k)
    (α : Root T) (x y : R) (z : Rˣ) (hz : (z : R) = 1 + x * y) :
    pairedRoot X Y d R α (Multiplicative.ofAdd x) *
      pairedRoot X Y d R (X.opposite α) (Multiplicative.ofAdd y) =
      pairedRoot X Y d R (X.opposite α) (Multiplicative.ofAdd (y * (↑z⁻¹ : R))) *
        pairedTorus τ R (cocharacterPoint (X.reflection α).coroot R z) *
        pairedRoot X Y d R α (Multiplicative.ofAdd (x * (↑z⁻¹ : R))) := by
  have hx : HasScalarAction T α.val⁻¹ (X.root (X.opposite α)) :=
    X.opposite_eq α ▸ X.scalarAction (X.opposite α)
  have hy : HasScalarAction S (d α).val⁻¹ (Y.root (Y.opposite (d α))) :=
    Y.opposite_eq (d α) ▸ Y.scalarAction (Y.opposite (d α))
  have hcoroot : (X.reflection α).coroot ≫ τ = (Y.reflection (d α)).coroot := by
    rw [X.coroot_eq, Y.coroot_eq]
    exact hc α
  apply Prod.ext
  · exact (LinearAlgebraicGroups.Classification.RankOneRelations.oppositeRootRelations G hG T hT hmT α.val α.property
      (X.root α) (X.root (X.opposite α)) (X.reflection α) (X.scalarAction α) hx R).1
      x y z hz
  · change rootPoint (Y.root (d α)) R x * rootPoint (Y.root (d (X.opposite α))) R y =
      rootPoint (Y.root (d (X.opposite α))) R (y * (↑z⁻¹ : R)) *
        (show GroupPoints H.val R from
          cocharacterPoint (X.reflection α).coroot R z ≫ (τ ≫ S.inclusion).hom.hom) *
        rootPoint (Y.root (d α)) R (x * (↑z⁻¹ : R))
    rw [hop, Grp.comp_hom_hom, ← Category.assoc, ← cocharacterPoint_postcompose, hcoroot]
    exact (LinearAlgebraicGroups.Classification.RankOneRelations.oppositeRootRelations H hH S hS hmS (d α).val (d α).property
      (Y.root (d α)) (Y.root (Y.opposite (d α))) (Y.reflection (d α))
      (Y.scalarAction (d α)) hy R).1 x y z hz

private theorem pairedScalar (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hχ : ∀ α, τ ≫ (d α).val = α.val) (R : TestAlgebra k)
    (α : Root T) (t : GroupPoints T.group R) (x : R) :
    pairedTorus τ R t * pairedRoot X Y d R α (Multiplicative.ofAdd x) *
      (pairedTorus τ R t)⁻¹ =
        pairedRoot X Y d R α (Multiplicative.ofAdd (characterValue α.val R t * x)) := by
  apply Prod.ext
  · exact X.scalarAction α R t x
  · have e : characterValue (d α).val R (onPoints τ R t) = characterValue α.val R t := by
      have h := congrArg (fun a : T.group ⟶ _ ↦ t ≫ a.hom.hom) (hχ α)
      unfold characterValue
      dsimp only
      rw [← h, Grp.comp_hom_hom, ← Category.assoc]
      rfl
    have h := Y.scalarAction (d α) R (onPoints τ R t) x
    rw [e] at h
    change (show GroupPoints H.val R from t ≫ (τ ≫ S.inclusion).hom.hom) *
        rootPoint (Y.root (d α)) R x *
        (show GroupPoints H.val R from t ≫ (τ ≫ S.inclusion).hom.hom)⁻¹ =
      rootPoint (Y.root (d α)) R (characterValue α.val R t * x)
    change (show GroupPoints H.val R from (t ≫ τ.hom.hom) ≫ S.inclusion.hom.hom) *
        rootPoint (Y.root (d α)) R x *
        (show GroupPoints H.val R from (t ≫ τ.hom.hom) ≫ S.inclusion.hom.hom)⁻¹ = _ at h
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact h

private theorem pairedSigned (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) {R : TestAlgebra k} (J : Ideal R)
    (h : SameSignedCommutators X Y d) (n : ℕ) (α β : Root T) (x y : R)
    (hx : x ∈ J ^ n) (hy : y ∈ J ^ 1) (hne : α ≠ β) (hop : β ≠ X.opposite α) :
    ∃ l : List (Root T × R), (∀ p ∈ l, p.2 ∈ J ^ (n + 1)) ∧
      ⁅pairedRoot X Y d R α (Multiplicative.ofAdd x),
        pairedRoot X Y d R β (Multiplicative.ofAdd y)⁆ =
        (l.map fun p ↦ pairedRoot X Y d R p.1 (Multiplicative.ofAdd p.2)).prod := by
  obtain ⟨l, hl⟩ := h α β hne (fun e ↦ hop (Subtype.ext (e.trans (X.opposite_eq α).symm)))
  let p (t : Specs.CellHomomorphism.CommutatorTerm α β) :=
    (t.root, algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)
  refine ⟨l.map p, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ht
    exact positive_power_product_mem J hx hy q.i_pos q.j_pos _
  · have e := hl R x y
    apply Prod.ext
    · change _ = MonoidHom.fst _ _ ((List.map _ _).prod)
      rw [MonoidHom.map_list_prod, List.map_map, List.map_map]
      exact e.1
    · change _ = MonoidHom.snd _ _ ((List.map _ _).prod)
      rw [MonoidHom.map_list_prod, List.map_map, List.map_map]
      exact e.2

private def pairedCellPoint (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    PairedPoints (G := G) (H := H) R :=
  let p := cellPoint X R negative positive v t
  (p ≫ rootCellMap T X.groups negative positive,
    p ≫ cellCoordinatesMap X Y d τ negative positive ≫
      rootCellMap S Y.groups (negative.map d) (positive.map d))

private def cellOrder {I : Type*} (negative positive : List I) : List (Option I) :=
  negative.map some ++ [none] ++ positive.map some

private theorem cellOrder_nodup {I : Type*} {negative positive : List I}
    (hn : negative.Nodup) (hp : positive.Nodup) (hd : negative.Disjoint positive) :
    (cellOrder negative positive).Nodup := by
  rw [cellOrder, List.append_assoc, List.nodup_append']
  refine ⟨hn.map (fun _ _ h ↦ Option.some.inj h), ?_, ?_⟩
  · rw [List.singleton_append, List.nodup_cons]
    exact ⟨by simp, hp.map (fun _ _ h ↦ Option.some.inj h)⟩
  · intro i hi hj
    obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hi
    simp only [List.singleton_append, List.mem_cons, reduceCtorEq, false_or] at hj
    obtain ⟨β, hβ, he⟩ := List.mem_map.mp hj
    exact hd (Option.some.inj he ▸ hα) hβ

private theorem mem_cellOrder {I : Type*} {negative positive : List I}
    (h : ∀ i, i ∈ negative ∨ i ∈ positive) (i : Option I) :
    i ∈ cellOrder negative positive := by
  cases i with
  | none => simp [cellOrder]
  | some α =>
    rcases h α with hα | hα
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hα))
    · exact List.mem_append_right _ (List.mem_map_of_mem hα)

private def cellLetter (X : Coordinates D A) (Y : Coordinates E A) (d : Root T ≃ Root S)
    (τ : T.group ⟶ S.group) (R : TestAlgebra k) (v : Root T → R)
    (t : GroupPoints T.group R) : Option (Root T) → PairedPoints (G := G) (H := H) R
  | none => pairedTorus τ R t
  | some α => pairedRoot X Y d R α (Multiplicative.ofAdd (v α))

private theorem pairedCellPoint_eq_prod (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    pairedCellPoint X Y d τ R negative positive v t =
      ((cellOrder negative positive).map (cellLetter X Y d τ R v t)).prod := by
  apply Prod.ext
  · change cellPoint X R negative positive v t ≫ rootCellMap T X.groups negative positive =
      MonoidHom.fst _ _ _
    rw [MonoidHom.map_list_prod, cellPoint_mul]
    simp only [cellOrder, List.map_append, List.prod_append, List.append_assoc, List.map_map,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · change cellPoint X R negative positive v t ≫ cellCoordinatesMap X Y d τ negative positive ≫
      rootCellMap S Y.groups (negative.map d) (positive.map d) = MonoidHom.snd _ _ _
    rw [← Category.assoc, cellPoint_transport, MonoidHom.map_list_prod, cellPoint_mul]
    simp only [cellOrder, List.map_append, List.prod_append, List.append_assoc, List.map_map,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Function.comp_def,
      Equiv.symm_apply_apply]
    rfl

private abbrev pairedCongruence (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) {R : TestAlgebra k} (J : Ideal R) :=
  generated J (pairedRoot X Y d R) (pairedTorus τ R) (torusCongruence (T := T) J)

private theorem pairedCellPoint_mem (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) {R : TestAlgebra k} (J : Ideal R)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R)
    (hv : ∀ α, v α ∈ J ^ 1) (ht : t ∈ torusCongruence (T := T) J 1) :
    pairedCellPoint X Y d τ R negative positive v t ∈ pairedCongruence X Y d τ J := by
  rw [pairedCellPoint_eq_prod]
  apply Subgroup.list_prod_mem
  intro b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  apply Subgroup.subset_closure
  refine ⟨i, ?_⟩
  cases i with
  | none => exact ⟨t, ht, rfl⟩
  | some α => exact ⟨Multiplicative.ofAdd (v α), hv α, rfl⟩

/-- The subgroup of paired points generated by congruence letters is already
the ordered cell on those letters when the congruence ideal is nilpotent. -/
private theorem pairedCongruence_ordered
    (hG : IsReductive G) (hH : IsReductive H)
    (hT : IsSplitTorus T.group) (hS : IsSplitTorus S.group)
    (hmT : IsGeometricallyMaximal T) (hmS : IsGeometricallyMaximal S)
    (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hinj : Function.Injective (Specs.CellHomomorphism.pullbackCharacters τ))
    (hχ : ∀ α, τ ≫ (d α).val = α.val)
    (hc : ∀ α, Additive.toMul (D.rootDatum.coroot α) ≫ τ =
      Additive.toMul (E.rootDatum.coroot (d α)))
    (hs : SameSignedCommutators X Y d) {R : TestAlgebra k} (J : Ideal R)
    (hJ : IsNilpotent J) (negative positive : List (Root T))
    (hn : negative.Nodup) (hp : positive.Nodup) (hd : negative.Disjoint positive)
    (hall : ∀ α, α ∈ negative ∨ α ∈ positive) (p : pairedCongruence X Y d τ J) :
    ∃ v t, (∀ α, v α ∈ J ^ 1) ∧ t ∈ torusCongruence (T := T) J 1 ∧
      (p : PairedPoints R) = pairedCellPoint X Y d τ R negative positive v t := by
  classical
  let root := pairedRoot X Y d R
  let torus := pairedTorus τ R
  let K := torusCongruence (T := T) J
  let L := pairedCongruence X Y d τ J
  let F := filteredLetters J root torus K
  let l := cellOrder negative positive
  have hK (n : ℕ) (h : 1 ≤ n) : K n ≤ K 1 := torusCongruence_mono J h
  obtain ⟨N, hN⟩ := hJ
  have hlast : J ^ (N + 1) = ⊥ := by
    rw [pow_succ, hN, zero_mul, Ideal.zero_eq_bot]
  have hlast' := filteredLetters_last J root torus K hlast (torusCongruence_eq_bot J hlast)
  have htcomm (t s : GroupPoints T.group R) : Commute t s := by
    let M := (testSpec k).obj (op R) ⟶ T.group.X
    letI : CommGroup M := Hom.commGroup
    have h := @Commute.all M (inferInstanceAs (CommMagma M)) (t : M) (s : M)
    exact h
  have hcomm := commutator_filteredLetters_mem J root torus K hK htcomm X.opposite
    (fun α ↦ cocharacterPoint (X.reflection α).coroot R)
    (fun α ↦ characterValue α.val R)
    (fun α n z hz ↦ cocharacterPoint_mem_congruence J (X.reflection α).coroot n z hz)
    (fun α n t ht ↦ characterValue_sub_one_mem J α.val n t ht)
    ⟨N, hN⟩
    (pairedGauss hG hH hT hS hmT hmS X Y d τ (opposite_transport X Y d τ hinj hχ) hc R)
    (pairedScalar X Y d τ hχ R) (pairedSigned X Y d J hs)
  obtain ⟨a, ha, hprod⟩ := ordered_product_of_nilpotent_filtration F
    (filteredLetters_generate J root torus K) (filteredLetters_le J root torus K hK)
    hcomm hlast' l (cellOrder_nodup hn hp hd) (mem_cellOrder hall) p
  have hroot (α : Root T) : ∃ x : R, x ∈ J ^ 1 ∧
      ((a (some α)) : PairedPoints R) = root α (Multiplicative.ofAdd x) := by
    obtain ⟨x, hx, he⟩ := (show ((a (some α)) : PairedPoints R) ∈
      (parameterSubgroup (J ^ (1 : ℕ))).map (root α) from ha (some α))
    exact ⟨x.toAdd, hx, he.symm⟩
  choose v hv he using hroot
  obtain ⟨t, ht, et⟩ : ∃ t ∈ K 1, torus t = (a none : PairedPoints R) := ha none
  refine ⟨v, t, hv, ht, ?_⟩
  rw [pairedCellPoint_eq_prod]
  have ee := congrArg L.subtype hprod
  rw [MonoidHom.map_list_prod, List.map_map] at ee
  refine ee.trans (congrArg List.prod ?_)
  apply List.map_congr_left
  intro i _
  cases i with
  | none => exact et.symm
  | some α => exact he α

private abbrev coordinateUnit (V : SchemeOver k) :=
  (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app V

private theorem coordinateUnit_isIso (V : SchemeOver k) [IsAffine V.left] :
    IsIso (coordinateUnit V) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  letI := F.faithful
  letI := F.full
  exact ((algΓAlgSpecAdjunction (CommRingCat.of k)).isIso_unit_app_iff_mem_essImage).mpr
      (essImage_algSpec.mpr inferInstance)

private noncomputable def universalPoint (V : SchemeOver k) [IsAffine V.left] :
    Points V (coordinates V) :=
  letI := coordinateUnit_isIso V
  inv (coordinateUnit V)

private theorem universalPoint_comp (V : SchemeOver k) [IsAffine V.left] :
    universalPoint V ≫ coordinateUnit V = 𝟙 _ := by
  haveI := coordinateUnit_isIso V
  exact IsIso.inv_hom_id _

private def pointAlgebraMap {V : SchemeOver k} {R : TestAlgebra k}
    (p : Points V R) : coordinates V →ₐ[k] R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (p ≫ coordinateUnit V)).unop.hom

private theorem pointAlgebraMap_injective (V : SchemeOver k) [IsAffine V.left]
    (R : TestAlgebra k) : Function.Injective (pointAlgebraMap (V := V) (R := R)) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  intro p q h
  have e : F.preimage (p ≫ coordinateUnit V) = F.preimage (q ≫ coordinateUnit V) :=
    Quiver.Hom.unop_inj (CommAlgCat.hom_ext h)
  haveI := coordinateUnit_isIso V
  apply (cancel_mono (coordinateUnit V)).mp
  simpa only [Functor.FullyFaithful.map_preimage] using congrArg ((testSpec k).map) e

private theorem pointAlgebraMap_change {V : SchemeOver k} {R R' : TestAlgebra k}
    (a : R ⟶ R') (p : Points V R) :
    pointAlgebraMap (mapPoints a p) = a.hom.comp (pointAlgebraMap p) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  change (F.preimage (((testSpec k).map a.op ≫ p) ≫ coordinateUnit V)).unop.hom = _
  rw [Category.assoc, F.preimage_comp, F.preimage_map]
  rfl

private theorem pointAlgebraMap_comp {V W : SchemeOver k} {R : TestAlgebra k}
    (p : Points V R) (f : V ⟶ W) :
    pointAlgebraMap (p ≫ f) = (pointAlgebraMap p).comp (coordinateMap f) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  have e : f ≫ coordinateUnit W =
      coordinateUnit V ≫ (testSpec k).map ((algΓ (CommRingCat.of k)).map f) :=
    (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.naturality f
  change (F.preimage ((p ≫ f) ≫ coordinateUnit W)).unop.hom = _
  rw [Category.assoc, e, ← Category.assoc, F.preimage_comp, F.preimage_map]
  rfl

private theorem pointAlgebraMap_universal (V : SchemeOver k) [IsAffine V.left] :
    pointAlgebraMap (universalPoint V) = AlgHom.id k (coordinates V) := by
  unfold pointAlgebraMap
  rw [universalPoint_comp, ← (testSpec k).map_id _, Functor.FullyFaithful.preimage_map]
  rfl

/-- If a morphism takes every infinitesimal neighbourhood of the indicated
point into a closed locus, its pullback vanishes on the defining ideal of that
locus. The source is affine, integral and locally Noetherian. -/
private theorem ker_le_of_jets {V W P : SchemeOver k} [IsAffine V.left] [IsAffine P.left]
    [IsIntegral V.left] [IsLocallyNoetherian V.left] (i : W ⟶ P) (z : V ⟶ P)
    (J : Ideal (coordinates V)) (hJ : J ≠ ⊤)
    (h : ∀ n : ℕ, ∃ p : Points W (quotientAlgebra (J ^ (n + 1))),
      p ≫ i = mapPoints (quotientMap (J ^ (n + 1))) (universalPoint V) ≫ z) :
    i.left.ker ≤ z.left.ker := by
  haveI : IsDomain (coordinates V) := inferInstanceAs (IsDomain Γ(V.left, ⊤))
  haveI : IsNoetherianRing (coordinates V) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.left⟩
  rw [Scheme.ker_of_isAffine i.left, Scheme.ker_of_isAffine z.left]
  let e := Scheme.IdealSheafData.equivOfIsAffine (X := P.left)
  change e.symm _ ≤ e.symm _
  apply e.symm.toOrderIso.monotone
  intro x hx
  change coordinateMap i x = 0 at hx
  change coordinateMap z x = 0
  apply Ideal.mem_bot.mp
  rw [← Ideal.iInf_pow_eq_bot_of_isDomain J hJ, Ideal.mem_iInf]
  intro n
  cases n with
  | zero => simp
  | succ n =>
    obtain ⟨p, hp⟩ := h n
    let a := quotientMap (J ^ (n + 1))
    have e : pointAlgebraMap (p ≫ i) =
        pointAlgebraMap (mapPoints a (universalPoint V) ≫ z) := congrArg pointAlgebraMap hp
    rw [pointAlgebraMap_comp p i, pointAlgebraMap_comp (mapPoints a (universalPoint V)) z,
      pointAlgebraMap_change, pointAlgebraMap_universal] at e
    have ex := (DFunLike.congr_fun e x).symm
    change a.hom (coordinateMap z x) = pointAlgebraMap p (coordinateMap i x) at ex
    rw [hx, map_zero] at ex
    exact Ideal.Quotient.eq_zero_iff_mem.mp ex

private def augmentationIdeal {V : SchemeOver k} (e : Points V (CommAlgCat.of k k)) :
    Ideal (coordinates V) :=
  RingHom.ker (pointAlgebraMap e).toRingHom

private theorem augmentationIdeal_ne_top {V : SchemeOver k} (e : Points V (CommAlgCat.of k k)) :
    augmentationIdeal e ≠ ⊤ := by
  intro h
  have hx : (1 : coordinates V) ∈ augmentationIdeal e := h ▸ (show (1 : coordinates V) ∈ (⊤ : Ideal (coordinates V)) from trivial)
  change pointAlgebraMap e 1 = 0 at hx
  exact one_ne_zero ((map_one _).symm.trans hx)

private def jetReduction {V : SchemeOver k} (e : Points V (CommAlgCat.of k k)) (n : ℕ) :
    quotientAlgebra (augmentationIdeal e ^ (n + 1)) ⟶ CommAlgCat.of k k :=
  CommAlgCat.ofHom <| Ideal.Quotient.liftₐ _ (pointAlgebraMap e) fun x hx ↦ by
    have hx' := (Ideal.pow_le_pow_right (I := augmentationIdeal e) (by omega : 1 ≤ n + 1)) hx
    rw [pow_one] at hx'
    exact hx' 

private theorem jetReduction_ker_nilpotent {V : SchemeOver k}
    (e : Points V (CommAlgCat.of k k)) (n : ℕ) :
    IsNilpotent (RingHom.ker (jetReduction e n).hom.toRingHom) := by
  refine ⟨n + 1, ?_⟩
  change (RingHom.ker (Ideal.Quotient.lift _ (pointAlgebraMap e).toRingHom _)) ^ (n + 1) = _
  rw [Ideal.ker_quotient_lift, ← Ideal.map_pow, Ideal.zero_eq_bot]
  exact Ideal.map_quotient_self _

private theorem jetPoint_reduce {V : SchemeOver k} [IsAffine V.left]
    (e : Points V (CommAlgCat.of k k)) (n : ℕ) :
    mapPoints (jetReduction e n)
      (mapPoints (quotientMap (augmentationIdeal e ^ (n + 1))) (universalPoint V)) = e := by
  apply pointAlgebraMap_injective
  rw [pointAlgebraMap_change, pointAlgebraMap_change, pointAlgebraMap_universal,
    AlgHom.comp_id]
  exact Ideal.Quotient.liftₐ_comp _ _ _

private theorem dominant_open_factor {X Y Z : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ Z)
    [IsOpenImmersion p] [QuasiCompact (s ≫ p)] [IsSchemeTheoreticallyDominant (s ≫ p)] :
    IsSchemeTheoreticallyDominant s :=
  IsSchemeTheoreticallyDominant.of_isPullback
    (IsPullback.of_horiz_isIso_mono
      (f := s ≫ p) (g := p) (fst := 𝟙 X) (snd := s) ⟨Category.id_comp _⟩)

/-- A finite morphism on a dense open mapping into an open of the target
identifies the source open with the whole inverse image. -/
private theorem isPullback_of_finite_on_open {X Y G H : SchemeOver k}
    (m : X ⟶ G) (j : X ⟶ Y) (f : G ⟶ H) (m' : Y ⟶ H)
    [IsOpenImmersion m.left] [IsOpenImmersion m'.left] [IsSeparated f.left]
    [IsFinite j.left] [QuasiCompact m.left] [IsSchemeTheoreticallyDominant m.left]
    (e : m ≫ f = j ≫ m') : IsPullback m j f m' := by
  let h := congrArg Over.Hom.left e
  let l := pullback.lift m.left j.left h
  have hl₁ : l ≫ pullback.fst f.left m'.left = m.left := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd f.left m'.left = j.left := pullback.lift_snd _ _ _
  have : IsOpenImmersion (l ≫ pullback.fst f.left m'.left) := hl₁.symm ▸ inferInstance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp _ (pullback.fst f.left m'.left)
  have : IsProper (l ≫ pullback.snd f.left m'.left) := hl₂.symm ▸ inferInstance
  have : IsProper l := IsProper.of_comp l (pullback.snd f.left m'.left)
  have : QuasiCompact (l ≫ pullback.fst f.left m'.left) := hl₁.symm ▸ inferInstance
  have : IsSchemeTheoreticallyDominant (l ≫ pullback.fst f.left m'.left) :=
    hl₁.symm ▸ inferInstance
  have : IsSchemeTheoreticallyDominant l := dominant_open_factor l (pullback.fst f.left m'.left)
  have : IsDominant l := inferInstance
  have : Surjective l := ⟨fun x ↦ by
    have hx := l.denseRange x
    rwa [(l.isClosedMap.isClosed_range).closure_eq] at hx⟩
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).mpr ⟨inferInstance, inferInstance⟩
  exact IsPullback.of_map (Over.forget _) e
    (IsPullback.of_iso_pullback ⟨h⟩ (asIso l) hl₁ hl₂)

private theorem isPullback_of_section_over_open {X P G : SchemeOver k}
    (w : X ⟶ P) (p : P ⟶ G) (m : X ⟶ G)
    [IsOpenImmersion m.left] [IsSeparated p.left] [QuasiCompact w.left]
    [IsSchemeTheoreticallyDominant w.left] (e : w ≫ p = m) :
    IsPullback w (𝟙 X) p m := by
  have h : w.left ≫ p.left = ((𝟙 X : X ⟶ X)).left ≫ m.left := by
    rw [Over.id_left, Category.id_comp]
    exact congrArg Over.Hom.left e
  let s := pullback.lift w.left ((𝟙 X : X ⟶ X)).left h
  have hs₁ : s ≫ pullback.fst p.left m.left = w.left := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd p.left m.left = 𝟙 X.left := pullback.lift_snd _ _ _
  have : QuasiCompact (s ≫ pullback.fst p.left m.left) := hs₁.symm ▸ inferInstance
  have : IsSchemeTheoreticallyDominant (s ≫ pullback.fst p.left m.left) :=
    hs₁.symm ▸ inferInstance
  have : IsSchemeTheoreticallyDominant s := dominant_open_factor s (pullback.fst p.left m.left)
  have : IsClosedImmersion (s ≫ pullback.snd p.left m.left) := hs₂.symm ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (pullback.snd p.left m.left)
  have : IsIso s := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr s.ker_eq_bot
  exact IsPullback.of_map (Over.forget _) (by rw [e, Category.id_comp])
    (IsPullback.of_iso_pullback ⟨h⟩ (asIso s) hs₁ hs₂)

private theorem mono_of_trivial_kernel {G H : GroupScheme k} (p : G ⟶ H)
    (h : ∀ (Z : SchemeOver k) (a : Z ⟶ G.X), a ≫ p.hom.hom = 1 → a = 1) :
    Mono p.hom.hom := by
  constructor
  intro Z a b hab
  have ha := h Z (a * b⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel])
  exact div_eq_one.mp ha

private theorem mono_of_identity_cell {G H : GroupScheme k} (p : G ⟶ H)
    {X : SchemeOver k} (w : X ⟶ G.X) (m : X ⟶ H.X)
    (h : IsPullback w (𝟙 X) p.hom.hom m)
    (e : 𝟙_ (SchemeOver k) ⟶ X) (he : e ≫ m = 1) :
    Mono p.hom.hom := by
  apply mono_of_trivial_kernel
  intro Z a ha
  let eZ := toUnit Z ≫ e
  have heZ : eZ ≫ m = 1 := by
    rw [Category.assoc, he, MonObj.comp_one]
  have eq (a : Z ⟶ G.X) (ha : a ≫ p.hom.hom = 1) : eZ ≫ w = a := by
    let v := h.lift a eZ (ha.trans heZ.symm)
    have hv : v = eZ := by simpa only [Category.comp_id] using h.lift_snd a eZ _
    have hh : v ≫ w = a := h.lift_fst a eZ (ha.trans heZ.symm)
    rwa [hv] at hh
  exact (eq a ha).symm.trans (eq 1 (MonObj.one_comp _))

private theorem faithfullyFlat_of_dense (imageFactor : SchemeImageFactorization.{u})
    (G H : AffineAlgebraicGroup k) [IsReduced H.val.X.left]
    (f : G.val ⟶ H.val) (hd : DenseRange f.hom.hom.left) :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  obtain ⟨I, p, i, ⟨h, hp, hs, _, _, hi⟩, _⟩ := imageFactor G H f
  have hcomp : p.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun g : G.val ⟶ H.val ↦ g.hom.hom.left) h
  have : Surjective i.hom.hom.left := ⟨fun x ↦ by
    have hx : x ∈ closure (Set.range i.hom.hom.left) :=
      closure_mono (by
        rintro _ ⟨a, rfl⟩
        exact ⟨p.hom.hom.left a, by rw [← Scheme.Hom.comp_apply, hcomp]⟩) (hd x)
    rwa [(i.hom.hom.left.isClosedEmbedding.isClosed_range).closure_eq] at hx⟩
  have : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  rw [← hcomp]
  exact ⟨inferInstance, inferInstance⟩

private theorem finite_of_finite_kernel {G H : GroupScheme k} (f : G ⟶ H)
    [IsAffineHom f.hom.hom.left] [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    [LocallyOfFiniteType f.hom.hom.left]
    {N : ClosedSubgroup G} (hN : IsSchemeKernel f N) [IsFinite N.group.X.hom] :
    IsFinite f.hom.hom.left := by
  let a := fst G.X N.group.X
  let b := snd G.X N.group.X ≫ N.inclusion.hom.hom
  have hb : b ≫ f.hom.hom = 1 := by
    simp only [b, Category.assoc, hN.w, comp_toUnit_assoc]
    rfl
  have h : IsPullback (a * b) a f.hom.hom f.hom.hom := by
    have e : (a * b) ≫ f.hom.hom = a ≫ f.hom.hom := by
      rw [MonObj.mul_comp, hb, mul_one]
    apply IsPullback.of_isLimit' ⟨e⟩
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      have e : (s.snd⁻¹ * s.fst) ≫ f.hom.hom = toUnit s.pt ≫ η[H.X] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel]
        rfl
      exact lift s.snd (hN.lift (s.snd⁻¹ * s.fst) (toUnit s.pt) e)
    · intro s
      simp only [a, b, MonObj.comp_mul, lift_fst, lift_snd_assoc, hN.lift_fst,
        mul_inv_cancel_left]
    · intro s
      simp only [a, lift_fst]
    · intro s q h₁ h₂
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [a, lift_fst] using h₂
      · simp only [lift_snd]
        haveI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
        haveI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
        apply (cancel_mono N.inclusion.hom.hom).mp
        rw [hN.lift_fst]
        have e : s.snd * (q ≫ snd _ _ ≫ N.inclusion.hom.hom) = s.fst := by
          rw [MonObj.comp_mul, h₂] at h₁
          exact h₁
        exact eq_inv_mul_of_mul_eq e
  have hp : IsPullback (a * b).left a.left f.hom.hom.left f.hom.hom.left :=
    (Over.forget _).map_isPullback h
  have : IsFinite a.left := inferInstanceAs
    (IsFinite (pullback.fst G.X.hom N.group.X.hom))
  have hc : UniversallyClosed f.hom.hom.left :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := f.hom.hom.left) (g := f.hom.hom.left)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (by
        rw [← MorphismProperty.cancel_left_of_respectsIso @UniversallyClosed hp.isoPullback.hom,
          hp.isoPullback_hom_snd]
        infer_instance)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨⟨⟩, inferInstance⟩

open private affine_tensor liftClosed liftClosed_fac ker_comp_eq dominant_tensor
  dominant_toImage subgroupStructure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private dense_cell eq_of_precomp_dense from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private abbrev productGroup (J L : GroupScheme k) : GroupScheme k :=
  Grp.mk (J.X ⊗ L.X)

private theorem graph_closure_extension (G H : AffineAlgebraicGroup k)
    [IsReduced G.val.X.left] {V : SchemeOver k} [IsAffine V.left]
    (m : V ⟶ G.val.X) (j : V ⟶ H.val.X) [IsOpenImmersion m.left]
    [IsSchemeTheoreticallyDominant m.left] [QuasiCompact m.left]
    (e : 𝟙_ (SchemeOver k) ⟶ V) (he : e ≫ (lift m j : V ⟶ (productGroup G.val H.val).X) = 1)
    (hm : let g : V ⟶ (productGroup G.val H.val).X := lift m j
      g.left.ker ≤ ((fst V V ≫ g) * (snd V V ≫ g)).left.ker)
    (hv : let g : V ⟶ (productGroup G.val H.val).X := lift m j
      g.left.ker ≤ g⁻¹.left.ker) :
    ∃ f : G.val ⟶ H.val, m ≫ f.hom.hom = j := by
  let P := productGroup G.val H.val
  let g : V ⟶ P.X := lift m j
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine P.X.left := affine_tensor
  haveI : LocallyOfFiniteType P.X.hom := by
    letI := G.property.2.1
    letI := H.property.2.1
    change LocallyOfFiniteType (G.val.X ⊗ H.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  haveI : QuasiCompact P.X.hom := by
    letI := G.property.2.2
    letI := H.property.2.2
    change QuasiCompact (G.val.X ⊗ H.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  let C : SchemeOver k := Over.mk (g.left.imageι ≫ P.X.hom)
  let i : C ⟶ P.X := Over.homMk g.left.imageι rfl
  let w : V ⟶ C := Over.homMk g.left.toImage (by
    change g.left.toImage ≫ g.left.imageι ≫ P.X.hom = _
    rw [← Category.assoc, g.left.toImage_imageι, g.w])
  have hw : w ≫ i = g := Over.OverMorphism.ext g.left.toImage_imageι
  have hi : i.left.ker = g.left.ker := g.left.ker.ker_subschemeι
  haveI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion g.left.imageι)
  haveI : IsAffine C.left := isAffine_of_isAffineHom i.left
  haveI : Mono i := Over.mono_of_mono_left i
  haveI : QuasiCompact g.left := by infer_instance
  haveI : QuasiCompact w.left := inferInstanceAs (QuasiCompact g.left.toImage)
  haveI : IsSchemeTheoreticallyDominant w.left := dominant_toImage g.left
  let u := e ≫ w
  have hu : u ≫ i = 1 := by rw [Category.assoc, hw]; exact he
  let mulC := (fst C C ≫ i) * (snd C C ≫ i)
  have hmk : i.left.ker ≤ mulC.left.ker := by
    haveI : IsSchemeTheoreticallyDominant (w ⊗ₘ w).left := dominant_tensor w
    rw [← ker_comp_eq (w ⊗ₘ w) mulC, hi]
    simpa only [mulC, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, hw] using hm
  let invC : C ⟶ P.X := i⁻¹
  have hvk : i.left.ker ≤ invC.left.ker := by
    rw [← ker_comp_eq w invC, hi]
    simpa only [invC, GrpObj.comp_inv, hw] using hv
  let mulLift := liftClosed i mulC hmk
  let invLift := liftClosed i invC hvk
  have hμ := liftClosed_fac i mulC hmk
  have hι := liftClosed_fac i invC hvk
  letI : GrpObj C := subgroupStructure i u mulLift invLift hu hμ hι
  haveI : IsMonHom i := by
    constructor
    · exact hu.trans (MonObj.one_eq_one P.X).symm
    · change mulLift ≫ i = (i ⊗ₘ i) ≫ μ[P.X]
      rw [hμ, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  let K : AffineAlgebraicGroup k :=
    ⟨Grp.mk C, ‹IsAffine C.left›, by
      change LocallyOfFiniteType (i.left ≫ P.X.hom)
      infer_instance, by
      change QuasiCompact (i.left ≫ P.X.hom)
      infer_instance⟩
  let iG : K.val ⟶ P := Grp.ofHom i
  let p : K.val ⟶ G.val := iG ≫ Grp.ofHom (fst G.val.X H.val.X)
  let q : K.val ⟶ H.val := iG ≫ Grp.ofHom (snd G.val.X H.val.X)
  have hwp : w ≫ p.hom.hom = m := by
    change w ≫ i ≫ fst _ _ = _
    rw [← Category.assoc, hw, lift_fst]
  have hwq : w ≫ q.hom.hom = j := by
    change w ≫ i ≫ snd _ _ = _
    rw [← Category.assoc, hw, lift_snd]
  haveI : IsSeparated p.hom.hom.left := inferInstanceAs (IsSeparated (f := p.hom.hom.left))
  have hp := isPullback_of_section_over_open w p.hom.hom m hwp
  have hem : e ≫ m = 1 := by
    have h := congrArg (fun z : 𝟙_ (SchemeOver k) ⟶ P.X ↦ z ≫ fst G.val.X H.val.X) he
    simpa only [Category.assoc, lift_fst, MonObj.one_comp] using h
  haveI : Mono p.hom.hom := mono_of_identity_cell p w m hp e hem
  have hd : DenseRange p.hom.hom.left := by
    have h := congrArg Over.Hom.left hwp
    have hl : Set.range m.left ⊆ Set.range p.hom.hom.left := by
      rintro x ⟨a, ha⟩
      refine ⟨w.left a, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact (congrArg (fun r : V.left ⟶ G.val.X.left ↦ r a) h).trans ha
    haveI : IsDominant m.left := inferInstance
    exact m.left.denseRange.mono hl
  have hff := faithfullyFlat_of_dense LinearAlgebraicGroups.schemeImageFactorization K G p hd
  haveI := hff.1
  haveI := hff.2
  haveI : IsIso p.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map p.hom.hom) :=
    inferInstanceAs (IsIso p.hom.hom.left)
  haveI : IsIso p.hom.hom := isIso_of_reflects_iso p.hom.hom (Over.forget _)
  let ep : K.val ≅ G.val := Grp.mkIso' (asIso p.hom.hom)
  have hp' : ep.hom = p := Grp.hom_ext _ _ rfl
  haveI : IsIso p := hp' ▸ (inferInstance : IsIso ep.hom)
  refine ⟨inv p ≫ q, ?_⟩
  change m ≫ (inv p).hom.hom ≫ q.hom.hom = j
  rw [← hwp, Category.assoc, ← Category.assoc p.hom.hom, ← Grp.comp_hom_hom,
    IsIso.hom_inv_id, Grp.id_hom_hom, Category.id_comp, hwq]

open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalRestriction
  diagonalClosedInclusion)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)
open Specs.CellHomomorphism (pullbackCharacters)
open private split_character_presentation value_for_presented_character
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
open private integerHomEquiv specIso pointsIso_precompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private finiteSpectrumIff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private theorem split_map_presentation {J L : GroupScheme k} (τ : J ⟶ L)
    (e : specGroup (groupAlgebra k (Character J)) ≅ J)
    (f : specGroup (groupAlgebra k (Character L)) ≅ L)
    (he : ∀ χ, e.hom ≫ χ =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character J) χ)))
    (hf : ∀ χ, f.hom ≫ χ =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character L) χ))) :
    e.hom ≫ τ = specGroupMap (groupAlgebraMap k (pullbackCharacters τ)) ≫ f.hom := by
  apply Grp.hom_ext
  apply hom_ext_of_points (by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k (Character J))))
    infer_instance)
  intro R t
  let C := Grp.forget (SchemeOver k)
  let g := specGroupMap (groupAlgebraMap k (pullbackCharacters τ))
  have hl : Mono (C.map f.inv) := inferInstance
  apply (cancel_mono (C.map f.inv)).mp
  let j := (groupAlgebraPointsIso k (Character L)).hom.app R
  apply (ConcreteCategory.bijective_of_isIso j).1
  apply MonoidHom.ext
  intro χ
  apply Units.ext
  let P := fun q : GroupPoints (specGroup (groupAlgebra k (Character L))) R ↦
    ((show Character L →* Rˣ from j q) χ : R)
  have e₁ : (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = t := by
    change (t ≫ (C.mapIso e).hom) ≫ (C.mapIso e).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e₂ : (t ≫ (g ≫ f.hom).hom.hom) ≫ f.inv.hom.hom = t ≫ g.hom.hom := by
    change (t ≫ C.map (g ≫ f.hom)) ≫ C.map f.inv = _
    rw [Category.assoc, ← C.map_comp, Category.assoc, f.hom_inv_id, Category.comp_id]
    rfl
  change P ((t ≫ (e.hom ≫ τ).hom.hom) ≫ f.inv.hom.hom) =
    P ((t ≫ (g ≫ f.hom).hom.hom) ≫ f.inv.hom.hom)
  rw [e₂]
  calc
    _ = characterValue χ R (t ≫ (e.hom ≫ τ).hom.hom) :=
      (value_for_presented_character f hf R _ χ).symm
    _ = characterValue (pullbackCharacters τ χ) R (t ≫ e.hom.hom.hom) := by
      simp only [characterValue, ← Category.assoc, Grp.comp_hom_hom]
      rfl
    _ = ((show Character J →* Rˣ from (groupAlgebraPointsIso k (Character J)).hom.app R t)
        (pullbackCharacters τ χ) : R) := by
      rw [value_for_presented_character e he, e₁]
    _ = _ := congrArg Units.val (pointsIso_precompose (pullbackCharacters τ) R t χ).symm

set_option maxHeartbeats 520000 in
private theorem finite_torus_map {J L : GroupScheme k}
    (τ : J ⟶ L) (hJ : IsSplitTorus J) (hL : IsSplitTorus L)
    [IsAffine J.X.left] [IsAffine L.X.left] [LocallyOfFiniteType τ.hom.hom.left]
    (hi : Function.Injective (pullbackCharacters τ))
    (hfin : Finite (Character J ⧸ (pullbackCharacters τ).range)) :
    IsFinite τ.hom.hom.left ∧ Flat τ.hom.hom.left ∧ Surjective τ.hom.hom.left ∧
      ∃ N : ClosedSubgroup J, IsFinite N.group.X.hom ∧ IsSchemeKernel τ N := by
  let M := Character J
  let W := Character L
  let m : W →* M := pullbackCharacters τ
  let a := m.ofInjective hi
  obtain ⟨hfg, e, he⟩ := split_character_presentation hJ
  obtain ⟨_, f, hf⟩ := split_character_presentation hL
  letI : Group.FG M := hfg
  let F := Grp.forget (SchemeOver k)
  let g := specIso (A := groupAlgebra k W) (B := groupAlgebra k m.range)
    (MonoidAlgebra.domCongrBialgEquiv k k a)
  let p := diagonalRestriction (k := k) m.range
  have hg : p ≫ g.hom = specGroupMap (groupAlgebraMap k m) := by
    change specGroupMap (groupAlgebraMap k m.range.subtype) ≫ g.hom = _
    rw [show g.hom = specGroupMap (groupAlgebraMap k a.toMonoidHom) from rfl,
      ← specGroupMap_comp]
    congr 1
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k m.range.subtype).comp
      (MonoidAlgebra.mapDomainBialgHom k a.toMonoidHom) =
      MonoidAlgebra.mapDomainBialgHom k m
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    rfl
  have hmap : e.hom ≫ τ = p ≫ (g ≪≫ f).hom := by
    rw [split_map_presentation τ e f he hf, ← hg, Iso.trans_hom, Category.assoc]
  obtain ⟨hN, hpfl, hps, _, hk, _⟩ :=
    LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k M m.range
  let i := diagonalClosedInclusion (k := k) m.range
  haveI : IsClosedImmersion i.hom.hom.left := hN
  have hclosed : IsClosedImmersion (i ≫ e.hom).hom.hom.left := by
    change IsClosedImmersion (i.hom.hom.left ≫ (F.mapIso e).hom.left)
    haveI : IsIso (F.mapIso e).hom.left := (Over.forget _).map_isIso (F.mapIso e).hom
    infer_instance
  let N : ClosedSubgroup J := ⟨_, i ≫ e.hom, hclosed⟩
  have hkernel : IsSchemeKernel τ N := by
    apply hk.of_iso (Iso.refl _) (F.mapIso e) (Iso.refl _) (F.mapIso (g ≪≫ f))
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact congrArg F.map hmap.symm
    · change η[(specGroup (groupAlgebra k m.range)).X] ≫ F.map (g ≪≫ f).hom = _
      exact IsMonHom.one_hom (f := (g ≪≫ f).hom.hom.hom)
  letI : Finite (M ⧸ m.range) := hfin
  haveI : IsFinite N.group.X.hom :=
    (finiteSpectrumIff (groupAlgebra k (M ⧸ m.range))).mpr
      (Module.Finite.of_basis (MonoidAlgebra.basis (M ⧸ m.range) k))
  have eτ : τ = e.inv ≫ p ≫ (g ≪≫ f).hom := by rw [← hmap, Iso.inv_hom_id_assoc]
  let U := F ⋙ Over.forget (Spec (CommRingCat.of k))
  haveI : Flat (U.map p) := hpfl
  haveI : Surjective (U.map p) := hps
  haveI : IsIso (U.map e.inv) := U.map_isIso e.inv
  haveI : IsIso (U.map (g ≪≫ f).hom) := U.map_isIso _
  haveI : Flat τ.hom.hom.left := by
    change Flat (U.map τ)
    rw [eτ, U.map_comp, U.map_comp]
    infer_instance
  haveI : Surjective τ.hom.hom.left := by
    change Surjective (U.map τ)
    rw [eτ, U.map_comp, U.map_comp]
    infer_instance
  haveI : IsAffineHom τ.hom.hom.left := isAffineHom_of_isAffine _
  exact ⟨finite_of_finite_kernel τ hkernel, inferInstance, inferInstance, N, inferInstance, hkernel⟩

private def rootIdentity (X : Coordinates D A) (V : SchemeOver k) :
    (l : List (Root T)) → V ⟶ rootFactors X l
  | [] => toUnit _
  | _ :: l => lift 1 (rootIdentity X V l)

private theorem rootIdentity_natural (X : Coordinates D A) {V W : SchemeOver k} (f : V ⟶ W)
    (l : List (Root T)) : f ≫ rootIdentity X W l = rootIdentity X V l := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons α l ih => simp only [rootIdentity, comp_lift, MonObj.comp_one, ih]

private theorem rootIdentity_mul (X : Coordinates D A) (V : SchemeOver k) (l : List (Root T)) :
    rootIdentity X V l ≫ rootProduct X.groups l = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons α l ih =>
    simp only [rootIdentity, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, ih, mul_one]

private theorem rootIdentity_transport (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (V : SchemeOver k) (l : List (Root T)) :
    rootIdentity X V l ≫ (rootFactorsIso X Y d l).hom = rootIdentity Y V (l.map d) := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons α l ih =>
    let m := (X.parametrization α).inv ≫ (Y.parametrization (d α)).hom
    change lift (1 : V ⟶ (X.groups α).val.group.X) (rootIdentity X V l) ≫
        (m.hom.hom ⊗ₘ (rootFactorsIso X Y d l).hom) =
      lift (1 : V ⟶ (Y.groups (d α)).val.group.X) (rootIdentity Y V (l.map d))
    rw [lift_map, ih, MonObj.one_comp]

private def neutralCell (X : Coordinates D A) (V : SchemeOver k)
    (negative positive : List (Root T)) :
    V ⟶ cell X negative positive :=
  lift (rootIdentity X V negative) (lift 1 (rootIdentity X V positive))

private theorem neutralCell_mul (X : Coordinates D A) (V : SchemeOver k)
    (negative positive : List (Root T)) :
    neutralCell X V negative positive ≫ rootCellMap T X.groups negative positive = 1 := by
  simp only [neutralCell, rootCellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    rootIdentity_mul, MonObj.one_comp, mul_one]

private theorem neutralCell_transport (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (V : SchemeOver k)
    (negative positive : List (Root T)) :
    neutralCell X V negative positive ≫ cellCoordinatesMap X Y d τ negative positive =
      neutralCell Y V (negative.map d) (positive.map d) := by
  simp only [neutralCell, cellCoordinatesMap, lift_map, rootIdentity_transport, MonObj.one_comp]


open private mapPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private product_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private affine_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private whiskerLeft_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem whiskerRight_pullback {U V : SchemeOver k} (W : SchemeOver k) (f : U ⟶ V) :
    IsPullback (f ▷ W) (fst U W) (fst V W) f := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.snd (c.fst ≫ snd V W)) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simpa using c.condition.symm
    · simp
  · intro c
    simp
  · intro c g h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂
    · simpa using congrArg (fun t ↦ t ≫ snd V W) h₁

private theorem tensor_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {V V' W W' : SchemeOver k} (a : V ⟶ V') (b : W ⟶ W')
    (ha : P a.left) (hb : P b.left) : P (a ⊗ₘ b).left := by
  let U := Over.forget (Spec (CommRingCat.of k))
  have hA : IsPullback (a ▷ W).left (fst V W).left (fst V' W).left a.left :=
    U.map_isPullback (whiskerRight_pullback W a)
  have hB : IsPullback (V' ◁ b).left (snd V' W).left (snd V' W').left b.left :=
    U.map_isPullback (whiskerLeft_pullback b)
  have h₁ : P (a ▷ W).left := P.of_isPullback hA.flip ha
  have h₂ : P (V' ◁ b).left := P.of_isPullback hB.flip hb
  rw [tensorHom_def, Over.comp_left]
  exact P.comp_mem _ _ h₁ h₂

private theorem cell_affine (X : Coordinates D A) (negative positive : List (Root T)) :
    IsAffine (cell X negative positive).left := by
  have : IsAffine T.group.X.left := affine_subgroup G.property.1 T
  have : IsAffine (rootFactors X negative).left := product_affine (U := X.groups) negative
  have : IsAffine (rootFactors X positive).left := product_affine (U := X.groups) positive
  have : IsAffine (T.group.X ⊗ rootFactors X positive).left :=
    affine_tensor (A := T.group.X) (B := rootFactors X positive)
  exact affine_tensor (A := rootFactors X negative) (B := T.group.X ⊗ rootFactors X positive)

private theorem torusCongruence_of_reduction {R R' : TestAlgebra k} (a : R ⟶ R')
    (t : GroupPoints T.group R) (ht : mapPoints a t = 1) :
    t ∈ torusCongruence (T := T) (RingHom.ker a.hom.toRingHom) 1 := by
  let J := RingHom.ker a.hom.toRingHom
  have hJ : (J ^ (1 : ℕ)) ≤ RingHom.ker a.hom.toRingHom := by rw [pow_one]
  let b : quotientAlgebra (J ^ (1 : ℕ)) ⟶ R' :=
    CommAlgCat.ofHom (Ideal.Quotient.liftₐ _ a.hom (fun _ hx ↦ hJ hx))
  have e : quotientMap (J ^ (1 : ℕ)) ≫ b = a := CommAlgCat.hom_ext <|
    Ideal.Quotient.liftₐ_comp _ _ _
  have hi : Function.Injective b.hom := by
    apply (RingHom.injective_iff_ker_eq_bot b.hom.toRingHom).mpr
    change RingHom.ker (Ideal.Quotient.lift (J ^ (1 : ℕ)) a.hom.toRingHom hJ) = _
    rw [Ideal.ker_quotient_lift, show RingHom.ker a.hom.toRingHom = J ^ (1 : ℕ)
      by rw [pow_one], Ideal.map_quotient_self]
  have hred : mapPoints b (mapPoints (quotientMap (J ^ (1 : ℕ))) t) =
      mapPoints b (1 : GroupPoints T.group (quotientAlgebra (J ^ (1 : ℕ)))) := by
    change (testSpec k).map b.op ≫ (testSpec k).map (quotientMap (J ^ (1 : ℕ))).op ≫ t =
      (testSpec k).map b.op ≫ 1
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, e, MonObj.comp_one]
    exact ht
  exact (mapPoints_injective (affine_subgroup G.property.1 T) b hi) hred

private def pairOfPoint (G H : GroupScheme k) (R : TestAlgebra k) :
    GroupPoints (productGroup G H) R →* (GroupPoints G R × GroupPoints H R) :=
  (onPoints (Grp.ofHom (fst G.X H.X)) R).prod (onPoints (Grp.ofHom (snd G.X H.X)) R)

private theorem pairOfPoint_injective (G H : GroupScheme k) (R : TestAlgebra k) :
    Function.Injective (pairOfPoint G H R) :=
  fun a b h ↦ CartesianMonoidalCategory.hom_ext a b
    (congrArg Prod.fst h) (congrArg Prod.snd h)

private def cellGraph (X : Coordinates D A) (Y : Coordinates E A) (d : Root T ≃ Root S)
    (τ : T.group ⟶ S.group) (negative positive : List (Root T)) :
    cell X negative positive ⟶ (productGroup G.val H.val).X :=
  lift (rootCellMap T X.groups negative positive)
    (cellCoordinatesMap X Y d τ negative positive ≫
      rootCellMap S Y.groups (negative.map d) (positive.map d))

private theorem cellGraph_on_points (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (R : TestAlgebra k)
    (negative positive : List (Root T)) (v : Root T → R) (t : GroupPoints T.group R) :
    pairOfPoint G.val H.val R
      (cellPoint X R negative positive v t ≫ cellGraph X Y d τ negative positive) =
      pairedCellPoint X Y d τ R negative positive v t := by
  let p := cellPoint X R negative positive v t
  let m := rootCellMap T X.groups negative positive
  let m' := cellCoordinatesMap X Y d τ negative positive ≫
    rootCellMap S Y.groups (negative.map d) (positive.map d)
  change pairOfPoint G.val H.val R (p ≫ lift m m') = (p ≫ m, p ≫ m')
  apply Prod.ext
  · change (p ≫ lift m m') ≫ fst G.val.X H.val.X = p ≫ m
    rw [Category.assoc, lift_fst]
  · change (p ≫ lift m m') ≫ snd G.val.X H.val.X = p ≫ m'
    rw [Category.assoc, lift_snd]

private theorem reduction_mem_pairedCongruence (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (negative positive : List (Root T))
    (hn : negative.Nodup) (hp : positive.Nodup) (hd : negative.Disjoint positive)
    (hall : ∀ α, α ∈ negative ∨ α ∈ positive)
    {R R' : TestAlgebra k} (a : R ⟶ R') (p : Points (cell X negative positive) R)
    (ha : mapPoints a p = cellPoint X R' negative positive (fun _ ↦ 0) 1) :
    pairOfPoint G.val H.val R (p ≫ cellGraph X Y d τ negative positive) ∈
      pairedCongruence X Y d τ (RingHom.ker a.hom.toRingHom) := by
  obtain ⟨v, t, rfl⟩ := cellPoint_surjective X R negative positive hn hp hd p
  rw [cellGraph_on_points]
  rw [cellPoint_map] at ha
  have en := congrArg (fun q : Points (cell X negative positive) R' ↦ q ≫ fst _ _) ha
  have ep := congrArg (fun q : Points (cell X negative positive) R' ↦ q ≫ snd _ _ ≫ snd _ _) ha
  have et := congrArg (fun q : Points (cell X negative positive) R' ↦ q ≫ snd _ _ ≫ fst _ _) ha
  simp only [cellPoint, lift_fst, lift_snd_assoc, lift_snd] at en ep et
  apply pairedCellPoint_mem
  · intro α
    rw [pow_one]
    exact (hall α).elim
      (fun hn ↦ (rootFactorsPoint_eq_iff X R' _ _ _).mp en α hn)
      (fun hp ↦ (rootFactorsPoint_eq_iff X R' _ _ _).mp ep α hp)
  · exact torusCongruence_of_reduction a t et

private theorem integral_reductive (G : AffineAlgebraicGroup k) (hG : IsReductive G) :
    IsIntegral G.val.X.left := by
  letI := G.property.2.1
  letI := G.property.2.2
  letI := hG.1
  letI := hG.2.1
  haveI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton
    G.val.X.hom
  haveI := geometricallyIrreducible_of_connected G
  exact (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2

private theorem integral_reductive_square (G : AffineAlgebraicGroup k) (hG : IsReductive G) :
    IsIntegral (G.val.X ⊗ G.val.X).left := by
  letI := G.property.2.1
  letI := G.property.2.2
  letI := hG.1
  letI := hG.2.1
  haveI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton
    G.val.X.hom
  haveI := geometricallyIrreducible_of_connected G
  have h := smooth_geometricallyIrreducible_tensor G.val.X G.val.X
  letI := h.1
  letI := h.2
  exact (geometry_of_smooth_geometricallyIrreducible _).2.2

private theorem extension_of_cell_agreement
    (hG : IsReductive G) (hH : IsReductive H) (hT : IsSplitTorus T.group) (hS : IsSplitTorus S.group)
    (hmT : IsGeometricallyMaximal T) (hmS : IsGeometricallyMaximal S)
    (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hinj : Function.Injective (pullbackCharacters τ))
    (hχ : ∀ α, τ ≫ (d α).val = α.val)
    (hc : ∀ α, Additive.toMul (D.rootDatum.coroot α) ≫ τ =
      Additive.toMul (E.rootDatum.coroot (d α)))
    (hs : SameSignedCommutators X Y d)
    (negative positive : List (Root T))
    (hn : negative.Nodup) (hp : positive.Nodup) (hd : negative.Disjoint positive)
    (hall : ∀ α, α ∈ negative ∨ α ∈ positive)
    [IsOpenImmersion (rootCellMap T X.groups negative positive).left] :
    ∃ f : G.val ⟶ H.val,
      rootCellMap T X.groups negative positive ≫ f.hom.hom =
        cellCoordinatesMap X Y d τ negative positive ≫
          rootCellMap S Y.groups (negative.map d) (positive.map d) := by
  let V := cell X negative positive
  let m := rootCellMap T X.groups negative positive
  let j := cellCoordinatesMap X Y d τ negative positive ≫
    rootCellMap S Y.groups (negative.map d) (positive.map d)
  let g : V ⟶ (productGroup G.val H.val).X := cellGraph X Y d τ negative positive
  let e : Points V (CommAlgCat.of k k) := cellPoint X _ negative positive (fun _ ↦ 0) 1
  let e₀ := neutralCell X (𝟙_ (SchemeOver k)) negative positive
  haveI : Nonempty V.left := ⟨e₀.left (IsLocalRing.closedPoint k)⟩
  haveI : Nonempty (V ⊗ V).left := ⟨(lift e₀ e₀).left (IsLocalRing.closedPoint k)⟩
  haveI : IsAffine V.left := cell_affine X negative positive
  haveI : IsAffine (V ⊗ V).left := affine_tensor (A := V) (B := V)
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine (productGroup G.val H.val).X.left :=
    affine_tensor (A := G.val.X) (B := H.val.X)
  haveI : QuasiCompact m.left := inferInstance
  haveI : IsIntegral G.val.X.left := integral_reductive G hG
  haveI : IsIntegral (G.val.X ⊗ G.val.X).left := integral_reductive_square G hG
  haveI : IsIntegral V.left := isIntegral_of_isOpenImmersion m.left
  haveI : IsOpenImmersion (m ⊗ₘ m).left :=
    tensor_property @IsOpenImmersion m m inferInstance inferInstance
  haveI : IsIntegral (V ⊗ V).left := isIntegral_of_isOpenImmersion (m ⊗ₘ m).left
  haveI : LocallyOfFiniteType V.hom := by
    rw [← Over.w m]
    letI := G.property.2.1
    infer_instance
  haveI : LocallyOfFiniteType (V ⊗ V).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  haveI : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  haveI : IsLocallyNoetherian (V ⊗ V).left := LocallyOfFiniteType.isLocallyNoetherian (V ⊗ V).hom
  haveI : IsSchemeTheoreticallyDominant m.left := dense_cell m hG inferInstance
  have he : e₀ ≫ g = 1 := by
    have he₁ : e₀ ≫ m = 1 := neutralCell_mul X _ _ _
    have he₂ : e₀ ≫ j = 1 := by
      dsimp only [e₀, j]
      rw [← Category.assoc, neutralCell_transport, neutralCell_mul]
    change e₀ ≫ lift m j = 1
    rw [comp_lift, he₁, he₂]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, MonObj.one_comp]
    · rw [lift_snd, MonObj.one_comp]
  have factor {R : TestAlgebra k} (J : Ideal R) (hJ : IsNilpotent J)
      (p : GroupPoints (productGroup G.val H.val) R)
      (hp' : pairOfPoint G.val H.val R p ∈ pairedCongruence X Y d τ J) :
      ∃ q : Points V R, q ≫ g = p := by
    obtain ⟨v, t, _, _, hvt⟩ := pairedCongruence_ordered hG hH hT hS hmT hmS X Y d τ
      hinj hχ hc hs J hJ negative positive hn hp hd hall ⟨_, hp'⟩
    refine ⟨cellPoint X R negative positive v t, pairOfPoint_injective G.val H.val R ?_⟩
    dsimp only [g]
    rw [cellGraph_on_points]
    exact hvt.symm
  have hinv : g.left.ker ≤ g⁻¹.left.ker := by
    apply ker_le_of_jets g g⁻¹ (augmentationIdeal e) (augmentationIdeal_ne_top e)
    intro n
    let a := jetReduction e n
    let q := mapPoints (quotientMap (augmentationIdeal e ^ (n + 1))) (universalPoint V)
    have hq := reduction_mem_pairedCongruence X Y d τ negative positive hn hp hd hall a q
      (jetPoint_reduce e n)
    apply factor (RingHom.ker a.hom.toRingHom) (jetReduction_ker_nilpotent e n)
    rw [GrpObj.comp_inv, map_inv]
    exact inv_mem hq
  have hmul : g.left.ker ≤ ((fst V V ≫ g) * (snd V V ≫ g)).left.ker := by
    let e₂ := lift e e
    apply ker_le_of_jets g _ (augmentationIdeal e₂) (augmentationIdeal_ne_top e₂)
    intro n
    let a := jetReduction e₂ n
    let q := mapPoints (quotientMap (augmentationIdeal e₂ ^ (n + 1))) (universalPoint (V ⊗ V))
    have e₁ : mapPoints a (q ≫ fst V V) = e := by
      change mapPoints a q ≫ fst V V = e
      rw [jetPoint_reduce e₂ n]
      exact lift_fst _ _
    have e₂' : mapPoints a (q ≫ snd V V) = e := by
      change mapPoints a q ≫ snd V V = e
      rw [jetPoint_reduce e₂ n]
      exact lift_snd _ _
    have h₁ := reduction_mem_pairedCongruence X Y d τ negative positive hn hp hd hall a _ e₁
    have h₂ := reduction_mem_pairedCongruence X Y d τ negative positive hn hp hd hall a _ e₂'
    apply factor (RingHom.ker a.hom.toRingHom) (jetReduction_ker_nilpotent e₂ n)
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, map_mul]
    exact mul_mem h₁ h₂
  exact graph_closure_extension G H m j e₀ he hmul hinv

open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (absoluteRoots)
open Specs.OpenCell (cellMap)
open Specs.CellHomomorphism (Matches)
open private exists_enumeration centralizes_precomp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre

private theorem rootCell_isOpen (bruhat : Specs.BruhatCells.Statement.{u})
    (openCell : Specs.OpenCell.Statement.{u})
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (X : Coordinates D A) (negative positive : List (Root T))
    (hn : Enumerates negative (subgroupRoots T B)ᶜ)
    (hp : Enumerates positive (subgroupRoots T B)) :
    IsOpenImmersion (rootCellMap T X.groups negative positive).left := by
  obtain ⟨_, _, _, _, Bneg, _, _, _, _, hBneg, hTneg, hroots, _⟩ :=
    bruhat G hG T B hT hm hB hTB
  obtain ⟨U, hU, hu⟩ := RootData.OrderedRootProducts.borelRadicalProduct G hG T hT hm B hB hTB
  obtain ⟨V, hV, hv⟩ :=
    RootData.OrderedRootProducts.borelRadicalProduct G hG T hT hm Bneg hBneg hTneg
  have h := (openCell G hG T hT hm B Bneg hB hBneg hTB hTneg hroots V U hV hU).1
  obtain ⟨en, hen⟩ := hv X.groups negative (hroots.symm ▸ hn)
  obtain ⟨ep, hep⟩ := hu X.groups positive hp
  let j := en ⊗ᵢ ((Iso.refl T.group.X) ⊗ᵢ ep)
  have hj : j.hom ≫ cellMap T V U = rootCellMap T X.groups negative positive := by
    have hinner : (𝟙 T.group.X ⊗ₘ ep.hom) ≫
        CocharacterDynamics.multiplyFactors T.inclusion (U.inclusion ≫ B.inclusion) =
        (fst _ _ ≫ T.inclusion.hom.hom) * (snd _ _ ≫ rootProduct X.groups positive) := by
      simp only [CocharacterDynamics.multiplyFactors, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc, Category.id_comp, Grp.comp_hom_hom, hep]
    change (en.hom ⊗ₘ (𝟙 T.group.X ⊗ₘ ep.hom)) ≫ cellMap T V U = _
    unfold cellMap rootCellMap
    simp only [MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, Grp.comp_hom_hom,
      hen, hinner]
  rw [← hj, Over.comp_left]
  haveI : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  infer_instance

private theorem rootWord_single (X : Coordinates D A) (R : TestAlgebra k)
    [DecidableEq (Root T)] (α : Root T)
    (x : R) (l : List (Root T)) (hl : l.Nodup) :
    ((l.map fun β ↦ rootPoint (X.root β) R (if β = α then x else 0)).prod) =
      if α ∈ l then rootPoint (X.root α) R x else 1 := by
  classical
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, ih hl.of_cons]
    by_cases h : β = α
    · subst β
      simp [(List.nodup_cons.mp hl).1]
    · simp [h, Ne.symm h, rootPoint_zero]

private theorem cell_matches_of_extension (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (f : G.val ⟶ H.val)
    (negative positive : List (Root T))
    (hn : negative.Nodup) (hp : positive.Nodup) (hd : negative.Disjoint positive)
    (hall : ∀ α, α ∈ negative ∨ α ∈ positive)
    (h : rootCellMap T X.groups negative positive ≫ f.hom.hom =
      cellCoordinatesMap X Y d τ negative positive ≫
        rootCellMap S Y.groups (negative.map d) (positive.map d)) :
    Matches X Y d τ f := by
  classical
  have pt (R : TestAlgebra k) (v : Root T → R) (t : GroupPoints T.group R) :
      onPoints f R (pairedCellPoint X Y d τ R negative positive v t).1 =
        (pairedCellPoint X Y d τ R negative positive v t).2 := by
    change (cellPoint X R negative positive v t ≫ rootCellMap T X.groups negative positive) ≫
      f.hom.hom = _
    rw [Category.assoc, h]
    rfl
  have hcalc (R : TestAlgebra k) (v : Root T → R) (t : GroupPoints T.group R) :
      onPoints f R (((negative.map fun α ↦ rootPoint (X.root α) R (v α)).prod) *
        (onPoints T.inclusion R t * (positive.map fun α ↦ rootPoint (X.root α) R (v α)).prod)) =
      ((negative.map (fun α ↦ rootPoint (Y.root (d α)) R (v α))).prod) *
        (onPoints S.inclusion R (onPoints τ R t) *
          (positive.map (fun α ↦ rootPoint (Y.root (d α)) R (v α))).prod) := by
    have e := pt R v t
    change onPoints f R (cellPoint X R negative positive v t ≫ rootCellMap T X.groups _ _) =
      cellPoint X R negative positive v t ≫ cellCoordinatesMap X Y d τ _ _ ≫
        rootCellMap S Y.groups _ _ at e
    rw [cellPoint_mul, ← Category.assoc, cellPoint_transport, cellPoint_mul] at e
    simpa only [List.map_map, Function.comp_def, Equiv.symm_apply_apply] using e
  constructor
  · apply Grp.hom_ext
    apply hom_ext_of_points (affine_subgroup G.property.1 T)
    intro R t
    have e := hcalc R (fun _ ↦ 0) t
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    change onPoints f R (onPoints T.inclusion R t) =
      onPoints S.inclusion R (onPoints τ R t)
    simpa only [rootPoint_zero, List.map_const', List.prod_replicate, one_pow, mul_one, one_mul]
      using e
  · intro α
    apply Grp.hom_ext
    apply hom_ext_of_points (by
      change IsAffine (Spec (CommRingCat.of (Polynomial k)))
      infer_instance)
    intro R a
    obtain ⟨x, rfl⟩ := rootPoint_surjective (Iso.refl A.group) R a
    have e := hcalc R (fun β ↦ if β = α then x else 0) 1
    have hneg : (negative.map (fun β ↦ rootPoint (Y.root (d β)) R
        (if β = α then x else 0))).prod =
        if α ∈ negative then rootPoint (Y.root (d α)) R x else 1 := by
      have ee := rootWord_single Y R (d α) x (negative.map d) (hn.map d.injective)
      simpa only [List.map_map, List.mem_map_of_injective d.injective, Function.comp_def, EmbeddingLike.apply_eq_iff_eq]
        using ee
    have hpos : (positive.map (fun β ↦ rootPoint (Y.root (d β)) R
        (if β = α then x else 0))).prod =
        if α ∈ positive then rootPoint (Y.root (d α)) R x else 1 := by
      have ee := rootWord_single Y R (d α) x (positive.map d) (hp.map d.injective)
      simpa only [List.map_map, List.mem_map_of_injective d.injective, Function.comp_def, EmbeddingLike.apply_eq_iff_eq]
        using ee
    rw [rootWord_single X R α x _ hn, rootWord_single X R α x _ hp, hneg, hpos,
      map_one, map_one, map_one] at e
    simp only [rootPoint, Iso.refl_hom, Grp.id_hom_hom, Category.comp_id, Grp.comp_hom_hom,
      ← Category.assoc]
    change onPoints f R (rootPoint (X.root α) R x) = rootPoint (Y.root (d α)) R x
    rcases hall α with hα | hα
    · have hα' : α ∉ positive := fun h ↦ hd hα h
      simpa only [if_pos hα, if_neg hα', mul_one, one_mul] using e
    · have hα' : α ∉ negative := fun h ↦ hd h hα
      simpa only [if_pos hα, if_neg hα', mul_one, one_mul] using e

private theorem rootProduct_matches (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (f : G.val ⟶ H.val)
    (h : Matches X Y d τ f) (l : List (Root T)) :
    rootProduct X.groups l ≫ f.hom.hom =
      (rootFactorsIso X Y d l).hom ≫ rootProduct Y.groups (l.map d) := by
  induction l with
  | nil =>
    change (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ f.hom.hom = (𝟙 _) ≫ 1
    rw [MonObj.one_comp, Category.id_comp]
  | cons α l ih =>
    let a := X.parametrization α
    let b := Y.parametrization (d α)
    let m := a.inv ≫ b.hom
    have er : (X.groups α).val.inclusion ≫ f = m ≫ (Y.groups (d α)).val.inclusion := by
      have e := h.2 α
      change (a.hom ≫ (X.groups α).val.inclusion) ≫ f = b.hom ≫ (Y.groups (d α)).val.inclusion at e
      apply (cancel_epi a.hom).mp
      simpa only [m, Category.assoc, Iso.hom_inv_id_assoc] using e
    have e : (X.groups α).val.inclusion.hom.hom ≫ f.hom.hom =
        m.hom.hom ≫ (Y.groups (d α)).val.inclusion.hom.hom :=
      congrArg (fun i : (X.groups α).val.group ⟶ H.val ↦ i.hom.hom) er
    change ((fst _ _ ≫ (X.groups α).val.inclusion.hom.hom) *
        (snd _ _ ≫ rootProduct X.groups l)) ≫ f.hom.hom =
      (m.hom.hom ⊗ₘ (rootFactorsIso X Y d l).hom) ≫
        ((fst _ _ ≫ (Y.groups (d α)).val.inclusion.hom.hom) *
          (snd _ _ ≫ rootProduct Y.groups (l.map d)))
    simp only [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, tensorHom_fst_assoc,
      tensorHom_snd_assoc, e, ih]

private theorem cell_commutes_of_matches (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (f : G.val ⟶ H.val)
    (h : Matches X Y d τ f) (negative positive : List (Root T)) :
    rootCellMap T X.groups negative positive ≫ f.hom.hom =
      cellCoordinatesMap X Y d τ negative positive ≫
        rootCellMap S Y.groups (negative.map d) (positive.map d) := by
  have ht := congrArg (fun g : T.group ⟶ H.val ↦ g.hom.hom) h.1
  have hi : T.inclusion.hom.hom ≫ f.hom.hom = τ.hom.hom ≫ S.inclusion.hom.hom := ht
  simp only [rootCellMap, cellCoordinatesMap, MonObj.mul_comp, MonObj.comp_mul,
    Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc, hi,
    rootProduct_matches X Y d τ f h]

private theorem cell_kernel (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (negative positive : List (Root T)) (f : G.val ⟶ H.val) (N : ClosedSubgroup T.group)
    (hN : IsSchemeKernel τ N)
    (h : IsPullback (rootCellMap T X.groups negative positive)
      (cellCoordinatesMap X Y d τ negative positive) f.hom.hom
      (rootCellMap S Y.groups (negative.map d) (positive.map d)))
    (hi : IsClosedImmersion (N.inclusion ≫ T.inclusion).hom.hom.left) :
    IsSchemeKernel f (⟨N.group, N.inclusion ≫ T.inclusion, hi⟩ : ClosedSubgroup G.val) := by
  let b := neutralCell Y (𝟙_ (SchemeOver k)) (negative.map d) (positive.map d)
  let a : N.group.X ⟶ cell X negative positive :=
    lift (rootIdentity X _ negative) (lift N.inclusion.hom.hom (rootIdentity X _ positive))
  let j := cellCoordinatesMap X Y d τ negative positive
  have hj : IsPullback a (toUnit _) j b := by
    have comm : a ≫ j = toUnit _ ≫ b := by
      simp only [a, j, b, neutralCell, cellCoordinatesMap, lift_map, comp_lift, MonObj.comp_one,
        rootIdentity_transport, rootIdentity_natural, hN.w]
      rfl
    apply IsPullback.of_isLimit' ⟨comm⟩
    let v (p : PullbackCone j b) := p.fst ≫ snd _ _ ≫ fst _ _
    have hv (p : PullbackCone j b) : v p ≫ τ.hom.hom = toUnit p.pt ≫ η[S.group.X] := by
      have eq := congrArg
        (fun q : p.pt ⟶ cell Y (negative.map d) (positive.map d) ↦ q ≫ snd _ _ ≫ fst _ _)
        p.condition
      simpa only [b, neutralCell, j, cellCoordinatesMap, Category.assoc, tensorHom_snd_assoc,
        tensorHom_fst_assoc, tensorHom_fst, lift_snd_assoc, lift_fst, MonObj.comp_one, comp_toUnit_assoc, v, Hom.one_def]
        using eq
    let q (p : PullbackCone j b) := hN.lift (v p) (toUnit p.pt) (hv p)
    have hq (p : PullbackCone j b) : q p ≫ a = p.fst := by
      have el := congrArg
        (fun z : p.pt ⟶ cell Y (negative.map d) (positive.map d) ↦ z ≫ fst _ _) p.condition
      have er := congrArg
        (fun z : p.pt ⟶ cell Y (negative.map d) (positive.map d) ↦ z ≫ snd _ _ ≫ snd _ _)
        p.condition
      apply CartesianMonoidalCategory.hom_ext
      · haveI : IsIso (rootFactorsIso X Y d negative).hom := inferInstance
        apply (cancel_mono (rootFactorsIso X Y d negative).hom).mp
        simpa only [a, b, j, neutralCell, cellCoordinatesMap, comp_lift, Category.assoc,
          lift_fst, lift_fst_assoc, rootIdentity_natural, rootIdentity_transport,
          tensorHom_fst_assoc, tensorHom_fst] using el.symm
      · apply CartesianMonoidalCategory.hom_ext
        · simpa only [a, comp_lift, lift_snd, lift_fst, q, v, Category.assoc] using
            hN.lift_fst (v p) (toUnit p.pt) (hv p)
        · haveI : IsIso (rootFactorsIso X Y d positive).hom := inferInstance
          apply (cancel_mono (rootFactorsIso X Y d positive).hom).mp
          simpa only [a, b, j, neutralCell, cellCoordinatesMap, comp_lift, Category.assoc,
            lift_snd_assoc, lift_snd, rootIdentity_transport, rootIdentity_natural,
            tensorHom_snd_assoc, tensorHom_snd] using er.symm
    refine PullbackCone.IsLimit.mk _ q hq (fun p ↦ toUnit_unique _ _) ?_
    intro p z hz _
    apply hN.hom_ext
    · have eq := congrArg (fun u ↦ u ≫ snd _ _ ≫ fst _ _) hz
      simpa only [a, Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, q,
        hN.lift_fst, v] using eq
    · exact toUnit_unique _ _
  have hp := hj.paste_horiz h
  have ha : a ≫ rootCellMap T X.groups negative positive =
      (N.inclusion ≫ T.inclusion).hom.hom := by
    simp only [a, rootCellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      rootIdentity_mul, mul_one, one_mul, Grp.comp_hom_hom]
  have hb : b ≫ rootCellMap S Y.groups (negative.map d) (positive.map d) = η[H.val.X] :=
    (neutralCell_mul Y _ _ _).trans (MonObj.one_eq_one _).symm
  change IsPullback (N.inclusion ≫ T.inclusion).hom.hom (toUnit N.group.X) f.hom.hom η[H.val.X]
  simpa only [ha, hb] using hp

private theorem torus_kernel_central (hG : IsReductive G) (hT : IsSplitTorus T.group)
    (hmT : IsGeometricallyMaximal T) (d : Root T ≃ Root S) (τ : T.group ⟶ S.group)
    (hχ : ∀ α, τ ≫ (d α).val = α.val) (N : ClosedSubgroup T.group)
    (hN : IsSchemeKernel τ N) :
    Centralizes (𝟙 G.val) (N.inclusion ≫ T.inclusion).hom.hom := by
  obtain ⟨_, _, _, _, _, h⟩ := RootData.SchemeCentre.schemeCentre G hG T hT hmT
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr (affine_subgroup (affine_subgroup G.property.1 T) N)
  let t : Points T.group.X R.unop := e.hom ≫ N.inclusion.hom.hom
  have ht := (h R.unop t).mpr (by
    intro α hα
    have hα' := congrArg (fun f : T.group ⟶ _ ↦ f.hom.hom) (hχ ⟨α, hα⟩)
    rw [← hα', Grp.comp_hom_hom]
    change (e.hom ≫ N.inclusion.hom.hom) ≫ τ.hom.hom ≫ (d ⟨α, hα⟩).val.hom.hom = _
    have e₁ : (e.hom ≫ N.inclusion.hom.hom) ≫ τ.hom.hom = 1 := by
      rw [Category.assoc, hN.w, ← Category.assoc, comp_toUnit]
      rfl
    rw [← Category.assoc, e₁, MonObj.one_comp])
  have hz := centralizes_precomp ht e.inv
  simpa only [t, Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id_assoc] using hz

private theorem transported_enumeration (d : Root T ≃ Root S)
    {l : List (Root T)} {U : Set (Root T)} {V : Set (Root S)}
    (h : ∀ α, α ∈ U ↔ d α ∈ V) (hl : Enumerates l U) :
    Enumerates (l.map d) V := by
  refine ⟨hl.1.map d.injective, ?_⟩
  intro β
  obtain ⟨α, rfl⟩ := d.surjective β
  exact (List.mem_map_of_injective d.injective).trans ((hl.2 α).trans (h α))

/-- The prescribed cell coordinates extend under the full Bruhat cell and
open cell statements, in their adopted dependency order. -/
theorem cellHomomorphism_conditional
    (bruhatCells : Specs.BruhatCells.Statement.{u}) (openCell : Specs.OpenCell.Statement.{u}) :
    Specs.CellHomomorphism.Statement.{u} := by
  intro k _ G H hG hH T S hT hS hmT hmS B C hB hC hTB hSC ct cs
  letI := ct
  letI := cs
  intro D E b c hb hc A X Y d τ hinj hindex hχ hcoroot hpos _ hsigned
  have hl₁ (negative positive : List (Root T))
      (hn : Enumerates negative {α | ¬ b.IsPos α}) (hp : Enumerates positive {α | b.IsPos α}) :
      IsOpenImmersion (rootCellMap T X.groups negative positive).left := by
    apply rootCell_isOpen bruhatCells openCell hG hT hmT B hB hTB X
    · exact ⟨hn.1, fun α ↦ (hn.2 α).trans (not_congr (hb α))⟩
    · exact ⟨hp.1, fun α ↦ (hp.2 α).trans (hb α)⟩
  have hl₂ (negative positive : List (Root T))
      (hn : Enumerates negative {α | ¬ b.IsPos α}) (hp : Enumerates positive {α | b.IsPos α}) :
      IsOpenImmersion (rootCellMap S Y.groups (negative.map d) (positive.map d)).left := by
    apply rootCell_isOpen bruhatCells openCell hH hS hmS C hC hSC Y
    · exact transported_enumeration d (fun α ↦ not_congr ((hpos α).trans (hc (d α)))) hn
    · exact transported_enumeration d (fun α ↦ (hpos α).trans (hc (d α))) hp
  obtain ⟨hfinite, _, _⟩ := RootData.OrderedRootProducts.contractingProduct G hG T hT hmT
  obtain ⟨negative, hn⟩ := exists_enumeration {α | ¬ b.IsPos α} hfinite
  obtain ⟨positive, hp⟩ := exists_enumeration {α | b.IsPos α} hfinite
  have hdp : negative.Disjoint positive :=
    fun ⦃α⦄ h₁ h₂ ↦ (hn.2 α).mp h₁ ((hp.2 α).mp h₂)
  have hall (α : Root T) : α ∈ negative ∨ α ∈ positive := by
    by_cases ha : b.IsPos α
    · exact Or.inr ((hp.2 α).mpr ha)
    · exact Or.inl ((hn.2 α).mpr ha)
  haveI := hl₁ negative positive hn hp
  obtain ⟨f, hf⟩ := extension_of_cell_agreement hG hH hT hS hmT hmS X Y d τ
    hinj hχ hcoroot hsigned negative positive hn.1 hp.1 hdp hall
  have hm := cell_matches_of_extension X Y d τ f negative positive hn.1 hp.1 hdp hall hf
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine H.val.X.left := H.property.1
  haveI : IsAffine T.group.X.left := affine_subgroup G.property.1 T
  haveI : IsAffine S.group.X.left := affine_subgroup H.property.1 S
  haveI : LocallyOfFiniteType T.group.X.hom := by
    haveI := G.property.2.1
    haveI := T.isClosedImmersion
    rw [← Over.w T.inclusion.hom.hom]
    infer_instance
  haveI : LocallyOfFiniteType τ.hom.hom.left := by
    haveI : LocallyOfFiniteType (τ.hom.hom.left ≫ S.group.X.hom) := by
      rw [Over.w τ.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp τ.hom.hom.left S.group.X.hom
  obtain ⟨hτfin, _, hτsurj, N, hNfin, hN⟩ :=
    finite_torus_map τ hT hS hinj hindex
  have hpb (negative positive : List (Root T))
      (hn : Enumerates negative {α | ¬ b.IsPos α}) (hp : Enumerates positive {α | b.IsPos α}) :
      IsPullback (rootCellMap T X.groups negative positive)
        (cellCoordinatesMap X Y d τ negative positive) f.hom.hom
        (rootCellMap S Y.groups (negative.map d) (positive.map d)) := by
    let m := rootCellMap T X.groups negative positive
    let m' := rootCellMap S Y.groups (negative.map d) (positive.map d)
    let j := cellCoordinatesMap X Y d τ negative positive
    haveI : Nonempty (cell X negative positive).left :=
      ⟨(neutralCell X (𝟙_ (SchemeOver k)) negative positive).left (IsLocalRing.closedPoint k)⟩
    haveI : IsAffine (cell X negative positive).left := cell_affine X negative positive
    haveI : IsOpenImmersion m.left := hl₁ negative positive hn hp
    haveI : IsOpenImmersion m'.left := hl₂ negative positive hn hp
    haveI : QuasiCompact m.left := inferInstance
    haveI : IsSchemeTheoreticallyDominant m.left := dense_cell m hG inferInstance
    haveI : IsFinite j.left := by
      haveI : IsIso (rootFactorsIso X Y d negative).hom.left := (Over.forget _).map_isIso _
      haveI : IsIso (rootFactorsIso X Y d positive).hom.left := (Over.forget _).map_isIso _
      let u := (rootFactorsIso X Y d negative).hom
      let v := (rootFactorsIso X Y d positive).hom
      exact tensor_property @IsFinite u (τ.hom.hom ⊗ₘ v) inferInstance
        (tensor_property @IsFinite τ.hom.hom v hτfin inferInstance)
    exact isPullback_of_finite_on_open m j f.hom.hom m'
      (cell_commutes_of_matches X Y d τ f hm negative positive)
  have hsurjFlat : Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
    let m := rootCellMap T X.groups negative positive
    let m' := rootCellMap S Y.groups (negative.map d) (positive.map d)
    let j := cellCoordinatesMap X Y d τ negative positive
    haveI : Nonempty (cell Y (negative.map d) (positive.map d)).left :=
      ⟨(neutralCell Y (𝟙_ (SchemeOver k)) _ _).left (IsLocalRing.closedPoint k)⟩
    haveI : IsOpenImmersion m'.left := hl₂ negative positive hn hp
    haveI : IsAffine (cell Y (negative.map d) (positive.map d)).left := cell_affine Y _ _
    haveI : IsSchemeTheoreticallyDominant m'.left := dense_cell m' hH inferInstance
    haveI : QuasiCompact m'.left := inferInstance
    haveI : IsDominant m'.left := inferInstance
    haveI : Surjective j.left := by
      haveI : IsIso (rootFactorsIso X Y d negative).hom.left := (Over.forget _).map_isIso _
      haveI : IsIso (rootFactorsIso X Y d positive).hom.left := (Over.forget _).map_isIso _
      let u := (rootFactorsIso X Y d negative).hom
      let v := (rootFactorsIso X Y d positive).hom
      exact tensor_property @Surjective u (τ.hom.hom ⊗ₘ v) inferInstance
        (tensor_property @Surjective τ.hom.hom v hτsurj inferInstance)
    have eq : m.left ≫ f.hom.hom.left = j.left ≫ m'.left := congrArg Over.Hom.left hf
    have hsub : Set.range m'.left ⊆ Set.range f.hom.hom.left := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨v, hv⟩ := j.left.surjective x
      exact ⟨m.left v, by rw [← Scheme.Hom.comp_apply, eq, Scheme.Hom.comp_apply, hv]⟩
    haveI : IsIntegral H.val.X.left := integral_reductive H hH
    exact faithfullyFlat_of_dense LinearAlgebraicGroups.schemeImageFactorization G H f
      (m'.left.denseRange.mono hsub)
  haveI := hsurjFlat.1
  haveI := hsurjFlat.2
  have hclosed : IsClosedImmersion (N.inclusion ≫ T.inclusion).hom.hom.left := by
    haveI := N.isClosedImmersion
    haveI := T.isClosedImmersion
    change IsClosedImmersion (N.inclusion.hom.hom.left ≫ T.inclusion.hom.hom.left)
    infer_instance
  let NG : ClosedSubgroup G.val := ⟨N.group, N.inclusion ≫ T.inclusion, hclosed⟩
  have hker : IsSchemeKernel f NG := cell_kernel X Y d τ negative positive f N hN
    (hpb negative positive hn hp) hclosed
  haveI : IsFinite NG.group.X.hom := hNfin
  haveI : IsAffineHom f.hom.hom.left := isAffineHom_of_isAffine _
  haveI : LocallyOfFiniteType f.hom.hom.left := by
    haveI : LocallyOfFiniteType (f.hom.hom.left ≫ H.val.X.hom) := by
      rw [Over.w f.hom.hom]
      exact G.property.2.1
    exact locallyOfFiniteType_of_comp f.hom.hom.left H.val.X.hom
  refine ⟨f, ⟨hm, finite_of_finite_kernel f hker, hsurjFlat.1, hsurjFlat.2, ?_,
    ?_, ?_⟩, ?_⟩
  · exact ⟨N, hNfin, hN, hclosed, hker, torus_kernel_central hG hT hmT d τ hχ N hN⟩
  · intro n p hn hp
    exact ⟨hl₁ n p hn hp, hl₂ n p hn hp, hpb n p hn hp⟩
  · intro hτ
    let j := cellCoordinatesMap X Y d τ negative positive
    haveI : IsIso τ.hom.hom := (Grp.forget _).map_isIso τ
    haveI : IsIso j := by
      change IsIso ((rootFactorsIso X Y d negative).hom ⊗ₘ
        (τ.hom.hom ⊗ₘ (rootFactorsIso X Y d positive).hom))
      infer_instance
    let q := rootCellMap S Y.groups (negative.map d) (positive.map d)
    have hb' : IsPullback (inv j ≫ rootCellMap T X.groups negative positive)
        (𝟙 _) f.hom.hom q :=
      (hpb negative positive hn hp).of_iso' (asIso j).symm
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [j]) (by simp) (by simp [q])
    haveI : Mono f.hom.hom := mono_of_identity_cell f _ q hb'
      (neutralCell Y (𝟙_ (SchemeOver k)) _ _) (neutralCell_mul Y _ _ _)
    haveI : IsIso f.hom.hom.left := Flat.isIso_of_surjective_of_mono _
    haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map f.hom.hom) :=
      inferInstanceAs (IsIso f.hom.hom.left)
    haveI : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget _)
    let ef : G.val ≅ H.val := Grp.mkIso' (asIso f.hom.hom)
    have hef : ef.hom = f := Grp.hom_ext _ _ rfl
    exact hef ▸ (inferInstance : IsIso ef.hom)
  · intro g hg
    apply Grp.hom_ext
    let m := rootCellMap T X.groups negative positive
    haveI : Nonempty (cell X negative positive).left :=
      ⟨(neutralCell X (𝟙_ (SchemeOver k)) negative positive).left (IsLocalRing.closedPoint k)⟩
    haveI : IsSchemeTheoreticallyDominant m.left := dense_cell m hG inferInstance
    haveI : IsSeparated H.val.X.hom := inferInstance
    exact eq_of_precomp_dense ((cell_commutes_of_matches X Y d τ g hg.1 _ _).trans hf.symm)


end

end CellPoints

end LinearAlgebraicGroups.Classification.CellHomomorphism

universe v8_closure_b746b4bee79327b4_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«CellHomomorphism».«cellHomomorphism» : _root_.«LinearAlgebraicGroups».«Specs».«CellHomomorphism».«Statement».{v8_closure_b746b4bee79327b4_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«CellHomomorphism».«cellHomomorphism_conditional».{v8_closure_b746b4bee79327b4_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«BruhatCells».«bruhatCells».{v8_closure_b746b4bee79327b4_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«OpenCell».«openCell».{v8_closure_b746b4bee79327b4_u0})
