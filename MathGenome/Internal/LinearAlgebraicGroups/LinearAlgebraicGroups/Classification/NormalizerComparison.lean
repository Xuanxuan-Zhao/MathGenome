import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.NormalizerComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.GroupTheory.QuotientGroup.Basic

universe u

namespace LinearAlgebraicGroups.Classification.NormalizerComparison

open _root_.LinearAlgebraicGroups.Specs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.NormalizerComparison
open Specs.SimpleRoots (wordLength wordProduct)
open RootPairing

noncomputable section

section WordRelations

variable {S W H : Type*} [Group W] [Group H]

private def evaluateWord (s : S → W) (p : List S) : W := (p.map s).prod

@[simp] private theorem evaluateWord_nil (s : S → W) : evaluateWord s [] = 1 := rfl

@[simp] private theorem evaluateWord_cons (s : S → W) (i : S) (p : List S) :
    evaluateWord s (i :: p) = s i * evaluateWord s p := rfl

private def alternating (i j : S) : ℕ → List S
  | 0 => []
  | n + 1 => i :: alternating j i n

private theorem alternating_difference (g : S → H) (hg : ∀ i, g i * g i = 1)
    (i j : S) (n : ℕ) :
    evaluateWord g (alternating i j n) * (evaluateWord g (alternating j i n))⁻¹ =
      (g i * g j) ^ n := by
  induction n generalizing i j with
  | zero => simp [alternating]
  | succ n ih =>
    have hj : (g j)⁻¹ = g j := inv_eq_of_mul_eq_one_right (hg j)
    simp only [alternating, evaluateWord_cons, mul_inv_rev, ← mul_assoc, hj]
    rw [mul_assoc (g i), ih j i]
    have shuffle (a b : H) (m : ℕ) : a * (b * a) ^ m = (a * b) ^ m * a := by
      induction m with
      | zero => simp
      | succ m hm => simp only [pow_succ, ← mul_assoc, hm]
    rw [shuffle, mul_assoc, ← pow_succ]

variable (s : S → W) (len : W → ℕ)

private def Descends (w : W) : List S → Prop
  | [] => True
  | i :: p => len (w * s i) < len w ∧ Descends (w * s i) p

private theorem alternating_to_minimum
    (hs : ∀ i, s i * s i = 1) (w : W) (i j : S)
    (hj : ¬ len (w * s j) < len w) :
    ∃ n, Descends s len w (alternating i j n) ∧
      let v := w * evaluateWord s (alternating i j n)
      ¬ len (v * s i) < len v ∧ ¬ len (v * s j) < len v := by
  by_cases hi : len (w * s i) < len w
  · have hi' : ¬ len (w * s i * s i) < len (w * s i) := by
      rw [mul_assoc, hs, mul_one]
      omega
    obtain ⟨n, hp, hv⟩ := alternating_to_minimum hs (w * s i) j i hi'
    exact ⟨n + 1, ⟨hi, hp⟩, by simpa [alternating, mul_assoc] using hv.symm⟩
  · exact ⟨0, trivial, by simpa only [alternating, evaluateWord_nil, mul_one] using
      (And.intro hi hj)⟩
termination_by len w

private theorem descent_length
    (hstep : ∀ w i, len (w * s i) + 1 = len w ∨ len w + 1 = len (w * s i))
    (w : W) (p : List S) (hp : Descends s len w p) :
    len (w * evaluateWord s p) + p.length = len w := by
  induction p generalizing w with
  | nil => simp
  | cons i p ih =>
    obtain ⟨hi, hp⟩ := hp
    rw [evaluateWord_cons, ← mul_assoc, List.length_cons, ← Nat.add_assoc, ih _ hp]
    rcases hstep w i with h | h <;> omega

@[simp] private theorem alternating_length (i j : S) (n : ℕ) :
    (alternating i j n).length = n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp [alternating, ih]

private def descentLift (g : S → H) (w : W) : H :=
  open Classical in
  if h : ∃ i, len (w * s i) < len w then
    descentLift g (w * s h.choose) * g h.choose
  else 1
termination_by len w
decreasing_by exact h.choose_spec

private theorem lift_along_descent (g : S → H) (hg : ∀ i, g i * g i = 1)
    (w : W) (p : List S)
    (hp : Descends s len w p) {bound : ℕ} (hb : len w < bound)
    (h : ∀ v, len v < bound → ∀ i, len (v * s i) < len v →
      descentLift s len g v = descentLift s len g (v * s i) * g i) :
    descentLift s len g w = descentLift s len g (w * evaluateWord s p) *
      (evaluateWord g p)⁻¹ := by
  induction p generalizing w with
  | nil => simp
  | cons i p ih =>
    obtain ⟨hi, hp⟩ := hp
    have he := (h w hb i hi).trans (congrArg (· * g i) (ih _ hp (hi.trans hb)))
    simpa only [evaluateWord_cons, ← mul_assoc, mul_inv_rev,
      inv_eq_of_mul_eq_one_right (hg i)] using he

/-- The local minimum property for two generators gives confluence of descent
and hence the presentation by squares and two-generator relations. -/
private theorem presentation_of_descent (g : S → H) (hs : ∀ i, s i * s i = 1)
    (hg : ∀ i, g i * g i = 1)
    (hrel : ∀ i j, (g i * g j) ^ orderOf (s i * s j) = 1)
    (hword : ∀ w, ∃ p, evaluateWord s p = w)
    (hzero : len 1 = 0)
    (hstep : ∀ w i, len (w * s i) + 1 = len w ∨ len w + 1 = len (w * s i))
    (hminimum : ∀ (w : W) (i j : S) (a b : ℕ),
      let v := w * evaluateWord s (alternating i j a)
      let z := w * evaluateWord s (alternating j i b)
      (¬ len (v * s i) < len v) → (¬ len (v * s j) < len v) →
      (¬ len (z * s i) < len z) → (¬ len (z * s j) < len z) → v = z) :
    ∃! f : W →* H, ∀ i, f (s i) = g i := by
  classical
  have hdown : ∀ w i, len (w * s i) < len w →
      descentLift s len g w = descentLift s len g (w * s i) * g i := by
    intro w
    induction w using (measure len).wf.induction with
    | h w ih =>
      intro i hi
      have hd : ∃ j, len (w * s j) < len w := ⟨i, hi⟩
      let j := hd.choose
      have hj : len (w * s j) < len w := hd.choose_spec
      rw [descentLift, dite_eq_left hd]
      change descentLift s len g (w * s j) * g j = descentLift s len g (w * s i) * g i
      have hback (t : S) (ht : len (w * s t) < len w) :
          ¬ len (w * s t * s t) < len (w * s t) := by
        rw [mul_assoc, hs, mul_one]
        omega
      obtain ⟨a, ha, hvi, hvj⟩ := alternating_to_minimum s len hs (w * s i) j i (hback i hi)
      obtain ⟨b, hb, hzj, hzi⟩ := alternating_to_minimum s len hs (w * s j) i j (hback j hj)
      let v := w * evaluateWord s (alternating i j (a + 1))
      let z := w * evaluateWord s (alternating j i (b + 1))
      have hv : v = (w * s i) * evaluateWord s (alternating j i a) := by
        simp [v, alternating, mul_assoc]
      have hz : z = (w * s j) * evaluateWord s (alternating i j b) := by
        simp [z, alternating, mul_assoc]
      have he : v = z := by
        refine hminimum w i j (a + 1) (b + 1) ?_ ?_ ?_ ?_
        · change ¬ len (v * s i) < len v
          simpa only [hv] using hvj
        · change ¬ len (v * s j) < len v
          simpa only [hv] using hvi
        · change ¬ len (z * s i) < len z
          simpa only [hz] using hzj
        · change ¬ len (z * s j) < len z
          simpa only [hz] using hzi
      have hla := descent_length s len hstep w (alternating i j (a + 1)) ⟨hi, ha⟩
      have hlb := descent_length s len hstep w (alternating j i (b + 1)) ⟨hj, hb⟩
      change len v + _ = _ at hla
      change len z + _ = _ at hlb
      rw [he, alternating_length] at hla
      rw [alternating_length] at hlb
      have hab : a = b := by omega
      have hwords : evaluateWord g (alternating i j (a + 1)) =
          evaluateWord g (alternating j i (b + 1)) := by
        rw [← hab]
        have hW : evaluateWord s (alternating i j (a + 1)) =
            evaluateWord s (alternating j i (a + 1)) :=
          mul_left_cancel (by simpa only [← hab, v, z] using he)
        have hpow : (s i * s j) ^ (a + 1) = 1 := by
          rw [← alternating_difference s hs i j, hW, mul_inv_cancel]
        have hdiv := orderOf_dvd_of_pow_eq_one hpow
        obtain ⟨m, hm⟩ := hdiv
        apply mul_inv_eq_one.mp
        rw [alternating_difference g hg i j, hm, pow_mul, hrel, one_pow]
      have ei := lift_along_descent s len g hg (w * s i) _ ha hi ih
      have ej := lift_along_descent s len g hg (w * s j) _ hb hj ih
      rw [← hv] at ei
      rw [← hz, ← he] at ej
      have ei' : descentLift s len g (w * s i) * g i =
          descentLift s len g v * (evaluateWord g (alternating i j (a + 1)))⁻¹ := by
        rw [ei]
        simp only [alternating, evaluateWord_cons, mul_inv_rev, ← mul_assoc,
          inv_eq_of_mul_eq_one_right (hg i)]
      have ej' : descentLift s len g (w * s j) * g j =
          descentLift s len g v * (evaluateWord g (alternating j i (b + 1)))⁻¹ := by
        rw [ej]
        simp only [alternating, evaluateWord_cons, mul_inv_rev, ← mul_assoc,
          inv_eq_of_mul_eq_one_right (hg j)]
      rw [ei', ej', hwords]
  have hlift (w : W) (i : S) : descentLift s len g (w * s i) =
      descentLift s len g w * g i := by
    rcases hstep w i with h | h
    · rw [hdown w i (by omega), mul_assoc, hg, mul_one]
    · have he : w * s i * s i = w := by rw [mul_assoc, hs, mul_one]
      have h' : len (w * s i * s i) < len (w * s i) := by rw [he]; omega
      simpa only [he] using hdown (w * s i) i h'
  have hone : descentLift s len g 1 = 1 := by
    have h : ¬ ∃ i, len ((1 : W) * s i) < len 1 := by simp [hzero]
    rw [descentLift, dite_eq_right h]
  have hprod (w : W) (p : List S) : descentLift s len g (w * evaluateWord s p) =
      descentLift s len g w * evaluateWord g p := by
    induction p generalizing w with
    | nil => simp
    | cons i p ih => simp only [evaluateWord_cons, ← mul_assoc, ih, hlift]
  have hprod' (p : List S) : descentLift s len g (evaluateWord s p) = evaluateWord g p := by
    simpa [hone] using hprod 1 p
  let F : W →* H :=
    { toFun := descentLift s len g
      map_one' := hone
      map_mul' w v := by
        obtain ⟨p, rfl⟩ := hword v
        rw [hprod, hprod'] }
  refine ⟨F, ?_, ?_⟩
  · intro i
    change descentLift s len g (s i) = g i
    simpa using hprod' [i]
  · intro F' hF'
    ext w
    obtain ⟨p, rfl⟩ := hword w
    change F' (evaluateWord s p) = descentLift s len g (evaluateWord s p)
    rw [hprod']
    induction p with
    | nil => simp
    | cons i p ih => simp [hF', ih]

end WordRelations

section GroupComparison

open Function

variable {S W T N M : Type u} [Group W] [Group T] [Group N] [Group M]

/-- The graph of the map on the kernel allows the lifted relations to be
applied in an honest group quotient, even when the kernel map is not injective. -/
private theorem compare_extensions (s : S → W) (n : S → N) (m : S → M)
    (q : N →* W) (j : T →* N) (l : T →* M)
    (hj : Injective j) (hq : q.ker = j.range) (hn : ∀ i, q (n i) = s i)
    (hact : ∀ i, ∃ e : T ≃* T, ∀ t,
      n i * j t * (n i)⁻¹ = j (e t) ∧ m i * l t * (m i)⁻¹ = l (e t))
    (hrel : ∀ i i', ∃ t,
      (n i * n i') ^ orderOf (s i * s i') = j t ∧
      (m i * m i') ^ orderOf (s i * s i') = l t)
    (hpres : ∀ {H : Type u} [Group H] (g : S → H),
      (∀ i i', (g i * g i') ^ orderOf (s i * s i') = 1) →
        ∃! f : W →* H, ∀ i, f (s i) = g i) :
    ∃ f : N →* M, f.comp j = l ∧ ∀ i, f (n i) = m i := by
  let D := (j.prod l).range
  let C := Subgroup.normalizer (D : Set (N × M))
  let D' := D.subgroupOf C
  let hnormal : D'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let first : C →* N := (MonoidHom.fst N M).comp C.subtype
  let second : C →* M := (MonoidHom.snd N M).comp C.subtype
  let r : C ⧸ D' →* W := QuotientGroup.lift D' (q.comp first) (by
    rintro a ⟨t, ht⟩
    change q a.val.1 = 1
    have ht' : j t = a.val.1 := congrArg Prod.fst ht
    rw [← ht']
    have h : j t ∈ q.ker := hq.symm ▸ (show j t ∈ j.range from ⟨t, rfl⟩)
    exact h)
  let p : C →* C ⧸ D' := QuotientGroup.mk' D'
  have hr (a : C) : r (p a) = q (first a) := rfl
  have hnC (i : S) : (n i, m i) ∈ C := by
    obtain ⟨e, he⟩ := hact i
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    ext z
    constructor
    · rintro ⟨-, ⟨t, rfl⟩, rfl⟩
      exact ⟨e t, Prod.ext (he t).1.symm (he t).2.symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨(j (e.symm t), l (e.symm t)), ⟨e.symm t, rfl⟩, ?_⟩
      exact Prod.ext (by simpa using (he (e.symm t)).1) (by simpa using (he (e.symm t)).2)
  let a (i : S) : C := ⟨(n i, m i), hnC i⟩
  have relation (i i' : S) : (p (a i) * p (a i')) ^ orderOf (s i * s i') = 1 := by
    rw [← map_mul, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨t, ht₁, ht₂⟩ := hrel i i'
    exact ⟨t, Prod.ext ht₁.symm ht₂.symm⟩
  obtain ⟨F, hF, _⟩ := hpres (p ∘ a) relation
  have hrs : r.comp F = MonoidHom.id W := by
    obtain ⟨g, _, hg⟩ := hpres s (fun i i' ↦ pow_orderOf_eq_one (s i * s i'))
    apply (hg (r.comp F) ?_).trans (hg (MonoidHom.id W) (fun _ ↦ rfl)).symm
    intro i
    change r (F (s i)) = s i
    rw [hF]
    exact (hr (a i)).trans (hn i)
  have hrs' (w : W) : r (F w) = w := DFunLike.congr_fun hrs w
  let K := F.range.comap p
  let π := first.comp K.subtype
  let torus (t : T) : C := ⟨(j t, l t), D.le_normalizer ⟨t, rfl⟩⟩
  have hpT (t : T) : p (torus t) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
  have hT (t : T) : torus t ∈ K := by
    change p (torus t) ∈ F.range
    rw [hpT]
    exact F.range.one_mem
  have ha (i : S) : a i ∈ K := ⟨s i, hF i⟩
  have hbij : Bijective π := by
    constructor
    · apply (injective_iff_map_eq_one π).mpr
      intro b hb
      obtain ⟨w, hw⟩ : p b.val ∈ F.range := b.property
      have hqw : w = 1 := by rw [← hrs' w, hw, hr, ← show π b = first b.val from rfl, hb, map_one]
      have hpb : p b.val = 1 := by rw [← hw, hqw, map_one]
      obtain ⟨t, ht⟩ := (QuotientGroup.eq_one_iff _).mp hpb
      have ht₁ : j t = 1 := (congrArg Prod.fst ht).trans hb
      have ht' : t = 1 := hj (ht₁.trans (map_one j).symm)
      apply Subtype.ext
      apply Subtype.ext
      exact ht.symm.trans (by simp [ht'])
    · intro x
      obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective D' (F (q x))
      change p b = F (q x) at hb
      have hb' : b ∈ K := ⟨q x, hb.symm⟩
      have hqb : q (first b) = q x := by rw [← hr, hb, hrs']
      have ht : (first b)⁻¹ * x ∈ j.range := by
        rw [← hq, MonoidHom.mem_ker, map_mul, map_inv, hqb, inv_mul_cancel]
      obtain ⟨t, ht⟩ := ht
      refine ⟨⟨b, hb'⟩ * ⟨torus t, hT t⟩, ?_⟩
      rw [map_mul]
      change first b * j t = x
      rw [ht, mul_inv_cancel_left]
  let e := MulEquiv.ofBijective π hbij
  let f := second.comp (K.subtype.comp e.symm.toMonoidHom)
  refine ⟨f, ?_, ?_⟩
  · ext t
    have he : e.symm (j t) = ⟨torus t, hT t⟩ := e.symm_apply_eq.mpr rfl
    change second (e.symm (j t)).val = l t
    rw [he]
    rfl
  · intro i
    have he : e.symm (n i) = ⟨a i, ha i⟩ := e.symm_apply_eq.mpr rfl
    change second (e.symm (n i)).val = m i
    rw [he]
    rfl

end GroupComparison

open private reflection_conjugate reflection_inverse reflection_cancel exists_word
  exists_shortest_word perm_mul perm_reflection reflected_value rightInversions
  rightInversions_card_mul length_eq_inversions length_inverse exists_integralValues
  positive_coefficients positive_height from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots

section RootDatum

open Finset

variable {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Finite I]
  [Module.Free ℤ X] [Module.Finite ℤ X] (D : RootDatum I X Y) [D.IsReduced] (b : D.Base)

private abbrev simpleReflection (i : b.support) : D.weylGroup :=
  weylGroup.ofIdx D i.val

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
private theorem simple_reflections_generate :
    Subgroup.closure (Set.range (simpleReflection D b)) = ⊤ := by
  let K := Subgroup.closure (Set.range (simpleReflection D b))
  have h (i : I) : weylGroup.ofIdx D i ∈ K := by
    apply b.induction_reflect i
    · intro a ha
      have he := reflection_conjugate D (weylGroup.ofIdx D a) a
      rw [perm_reflection, reflection_inverse, reflection_cancel, one_mul] at he
      rwa [he]
    · intro a ha
      exact Subgroup.subset_closure (Set.mem_range_self (f := simpleReflection D b) ⟨a, ha⟩)
    · intro a j ha hj
      have hm : weylGroup.ofIdx D j ∈ K :=
        Subgroup.subset_closure (Set.mem_range_self (f := simpleReflection D b) ⟨j, hj⟩)
      rw [← perm_reflection, reflection_conjugate]
      exact K.mul_mem (K.mul_mem hm ha) (K.inv_mem hm)
  apply top_unique
  rintro ⟨w, hw⟩ -
  induction hw using weylGroup.induction with
  | mem i => exact h i
  | one => exact K.one_mem
  | mul a c ha hc ha' hc' => exact K.mul_mem ha' hc'

omit [Finite I] [D.IsReduced] in
private theorem exists_regular_functional :
    ∃ f : X →ₗ[ℤ] ℤ, (∀ i, f (D.root i) ≠ 0) ∧
      ∀ i, b.IsPos i ↔ 0 < f (D.root i) := by
  obtain ⟨f, m, hm, hf⟩ := exists_integralValues b.linearIndepOn_root (fun _ ↦ 1)
  have he (α : I) : f (D.root α) = m * b.height α := by
    obtain ⟨c, -, -, hc⟩ := b.exists_root_eq_sum_int α
    rw [b.height_eq_sum hc]
    nth_rw 1 [hc]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_zsmul, hf ⟨a, ha⟩, mul_one, Int.zsmul_eq_mul, mul_comm]
  exact ⟨f, fun i ↦ by rw [he]; exact mul_ne_zero hm.ne' (b.height_ne_zero i),
    fun i ↦ by rw [he, b.isPos_iff, mul_pos_iff_of_pos_left hm]⟩

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] [D.IsReduced] in
private theorem face_functional_sign (r : X →ₗ[ℤ] ℤ) (hr : ∀ j : b.support, 0 ≤ r (D.root j))
    {α : I} (hα : b.IsPos α) : 0 ≤ r (D.root α) := by
  obtain ⟨c, hc, -, he⟩ := positive_coefficients D b hα
  rw [← he, map_sum]
  exact Finset.sum_nonneg fun j _ ↦ by
    rw [map_zsmul, zsmul_eq_mul]
    exact mul_nonneg (hc j) (hr j)

omit [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X] [D.IsReduced] in
private theorem pair_face_sign (f r : X →ₗ[ℤ] ℤ) (hf : ∀ α, b.IsPos α ↔ 0 < f (D.root α))
    (i j : b.support) (hi : r (D.root i) = 0) (hj : r (D.root j) = 0)
    (hout : ∀ t : b.support, t ≠ i → t ≠ j → 0 < r (D.root t)) (w : D.weylGroup)
    (hwi : 0 < f (D.root (D.weylGroupToPerm w i)))
    (hwj : 0 < f (D.root (D.weylGroupToPerm w j)))
    {α : I} (hα : r (D.root α) = 0) :
    b.IsPos (D.weylGroupToPerm w α) ↔ b.IsPos α := by
  classical
  have hpos {β : I} (hβ : r (D.root β) = 0) (hp : b.IsPos β) :
      0 < f (D.root (D.weylGroupToPerm w β)) := by
    obtain ⟨c, hc, hne, he⟩ := positive_coefficients D b hp
    have hr (t : b.support) : 0 ≤ r (D.root t) := by
      by_cases ht : t = i
      · simp [ht, hi]
      by_cases ht' : t = j
      · simp [ht', hj]
      · exact (hout t ht ht').le
    have hsum : ∑ t : b.support, c t * r (D.root t) = 0 := by
      rw [← hβ, ← he, map_sum]
      simp only [map_zsmul, Int.zsmul_eq_mul]
    have tests (t : b.support) (ht : 0 < c t) : t = i ∨ t = j := by
      by_contra! h
      have := Finset.single_le_sum (s := Finset.univ)
        (f := fun t : b.support ↦ c t * r (D.root t))
        (fun a _ ↦ mul_nonneg (hc a) (hr a)) (Finset.mem_univ t)
      rw [hsum] at this
      exact (not_lt_of_ge this) (mul_pos ht (hout _ h.1 h.2))
    let f' : X →ₗ[ℤ] ℤ := f.comp w.val.weightEquiv.toLinearMap
    have he' : f' (D.root β) = ∑ t : b.support, c t * f' (D.root t) := by
      rw [← he, map_sum]
      simp only [map_zsmul, Int.zsmul_eq_mul]
    have hh (t : b.support) (ht : 0 < c t) : 0 < c t * f' (D.root t) := by
      rcases tests t ht with heq | heq
      · apply mul_pos ht
        rw [heq]
        change 0 < f (w • D.root i.val)
        rwa [D.weylGroup_apply_root]
      · apply mul_pos ht
        rw [heq]
        change 0 < f (w • D.root j.val)
        rwa [D.weylGroup_apply_root]
    have hsumpos : 0 < f' (D.root β) := by
      rw [he']
      apply Finset.sum_pos'
      · intro t _
        rcases (hc t).eq_or_lt with ht | ht
        · simp [← ht]
        · exact (hh t ht).le
      · obtain ⟨t, ht⟩ := hne
        exact ⟨t, Finset.mem_univ t, hh t ht⟩
    change 0 < f (w • D.root β) at hsumpos
    simpa only [D.weylGroup_apply_root] using hsumpos
  refine ⟨?_, fun hp ↦ (hf _).mpr (hpos hα hp)⟩
  intro hp
  by_contra hn
  let β := D.reflectionPerm α α
  have hβ : r (D.root β) = 0 := by
    simp [β, root_reflectionPerm, reflection_apply_self, hα]
  have hnβ : b.IsPos β := (Base.IsPos.neg_iff_not b α).mpr hn
  have ht := hpos hβ hnβ
  rw [show β = D.reflectionPerm α α from rfl, reflected_value] at ht
  exact not_lt_of_ge (neg_nonpos_of_nonneg ((hf _).mp hp).le) ht

omit [Finite I] [D.IsReduced] in
private theorem pair_minimum_unique (f : X →ₗ[ℤ] ℤ) (hf : ∀ α, b.IsPos α ↔ 0 < f (D.root α))
    (hfaithful : ∀ w : D.weylGroup,
      (∀ α, b.IsPos α → b.IsPos (D.weylGroupToPerm w α)) → w = 1)
    (w : D.weylGroup) (i j : b.support) (a c : ℕ) :
    let x := evaluateWord (simpleReflection D b) (alternating i j a)
    let y := evaluateWord (simpleReflection D b) (alternating j i c)
    let v := w * x
    let z := w * y
    0 < f (D.root (D.weylGroupToPerm v i)) →
    0 < f (D.root (D.weylGroupToPerm v j)) →
    0 < f (D.root (D.weylGroupToPerm z i)) →
    0 < f (D.root (D.weylGroupToPerm z j)) → v = z := by
  classical
  dsimp only
  set x := evaluateWord (simpleReflection D b) (alternating i j a) with hx
  set y := evaluateWord (simpleReflection D b) (alternating j i c) with hy
  intro hvi hvj hzi hzj
  obtain ⟨r, m, hm, hr⟩ := exists_integralValues b.linearIndepOn_root
    (fun t ↦ if t = i ∨ t = j then 0 else 1)
  have hi : r (D.root i) = 0 := by rw [hr]; simp
  have hj : r (D.root j) = 0 := by rw [hr]; simp
  have hout (t : b.support) (hti : t ≠ i) (htj : t ≠ j) : 0 < r (D.root t) := by
    rw [hr]; simpa [hti, htj] using hm
  have hnonneg (t : b.support) : 0 ≤ r (D.root t) := by
    rw [hr]
    split <;> simp [hm.le]
  have hnonpos {α : I} (hα : ¬ b.IsPos α) : r (D.root α) ≤ 0 := by
    have he := face_functional_sign D b r hnonneg ((Base.IsPos.neg_iff_not b α).mpr hα)
    change 0 ≤ r (D.root (D.reflectionPerm α α)) at he
    simpa only [root_reflectionPerm, reflection_apply_self, map_neg, neg_nonneg] using he
  have hreflect (t : b.support) (ht : r (D.root t) = 0) (α : I) :
      r (D.root (D.weylGroupToPerm (simpleReflection D b t) α)) = r (D.root α) := by
    rw [perm_reflection, root_reflectionPerm, reflection_apply_root, map_sub, map_zsmul,
      ht, smul_zero, sub_zero]
  have hword (p q : b.support) (hp : r (D.root p) = 0) (hq : r (D.root q) = 0)
      (n : ℕ) (α : I) :
      r (D.root (D.weylGroupToPerm (evaluateWord (simpleReflection D b) (alternating p q n)) α)) =
        r (D.root α) := by
    induction n generalizing p q with
    | zero => simp [alternating]
    | succ n ih =>
      rw [alternating, evaluateWord_cons, perm_mul, hreflect p hp, ih q p hq hp]
  let e := x⁻¹ * y
  have hxe : x * e = y := by simp [e]
  have he (α : I) : r (D.root (D.weylGroupToPerm e α)) = r (D.root α) := by
    have h₁ := hword i j hi hj a (D.weylGroupToPerm e α)
    rw [← hx, ← perm_mul, hxe] at h₁
    exact h₁.symm.trans (hy.symm ▸ hword j i hj hi c α)
  have he₁ : e = 1 := hfaithful e fun α hα ↦ by
    by_cases hα₀ : r (D.root α) = 0
    · have hβ₀ : r (D.root (D.weylGroupToPerm e α)) = 0 := (he α).trans hα₀
      apply (pair_face_sign D b f r hf i j hi hj hout (w * x) hvi hvj hβ₀).mp
      rw [← perm_mul, mul_assoc, hxe]
      exact (pair_face_sign D b f r hf i j hi hj hout (w * y) hzi hzj hα₀).mpr hα
    · have hαp := lt_of_le_of_ne (face_functional_sign D b r hnonneg hα) (Ne.symm hα₀)
      by_contra hn
      exact not_lt_of_ge (hnonpos hn) ((he α).symm ▸ hαp)
  calc
    w * x = w * (x * e) := by rw [he₁, mul_one]
    _ = w * y := by rw [hxe]

omit [Module.Free ℤ X] [Module.Finite ℤ X] [D.IsReduced] in
/-- A positive face root is indecomposable within the face precisely when it
is an ambient simple root. A decomposition of a zero-weight positive root
into positive roots can only have zero-weight summands. -/
private theorem simple_on_face_iff (r : X →ₗ[ℤ] ℤ) (hr : ∀ j : b.support, 0 ≤ r (D.root j))
    (i : I) (hi : r (D.root i) = 0) :
    (b.IsPos i ∧ ∀ j j' : I, b.IsPos j → b.IsPos j' →
      r (D.root j) = 0 → r (D.root j') = 0 → D.root i ≠ D.root j + D.root j') ↔
    i ∈ b.support := by
  constructor
  · rintro ⟨hp, hind⟩
    have decompose : i ∈ b.support ∨
        ∃ j j', b.IsPos j ∧ b.IsPos j' ∧ D.root i = D.root j + D.root j' := by
      obtain ⟨_, h⟩ := hp.induction_on_add (p := fun k ↦ b.IsPos k ∧ (k ∈ b.support ∨
          ∃ j j', b.IsPos j ∧ b.IsPos j' ∧ D.root k = D.root j + D.root j'))
        (fun _ hk ↦ ⟨b.isPos_of_mem_support hk, Or.inl hk⟩)
        (fun j j' _ he h hj' ↦ ⟨h.1.add (b.isPos_of_mem_support hj') he,
          Or.inr ⟨j, j', h.1, b.isPos_of_mem_support hj', he⟩⟩)
      exact h
    rcases decompose with h | ⟨j, j', hj, hj', h⟩
    · exact h
    · have h₁ := face_functional_sign D b r hr hj
      have h₂ := face_functional_sign D b r hr hj'
      have hz : r (D.root j) + r (D.root j') = 0 := by rw [← map_add, ← h, hi]
      exact (hind j j' hj hj' (by omega) (by omega) h).elim
  · intro h
    refine ⟨b.isPos_of_mem_support h, fun j j' hj hj' _ _ he ↦ ?_⟩
    have hsum := b.height_add he
    rw [b.height_one_of_mem_support h] at hsum
    rw [b.isPos_iff] at hj hj'
    omega

end RootDatum

/-- An injective map of character lattices that matches the roots identifies
the roots in the integral spans of corresponding subsets. -/
private theorem mem_root_span_iff_of_injective {I J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (α : I → X) (β : J → Y) (e : I ≃ J) (h : Y →ₗ[ℤ] X) (hinj : Function.Injective h)
    (hroot : ∀ i, h (β (e i)) = α i) (B : Set I) (i : I) :
    α i ∈ Submodule.span ℤ (α '' B) ↔ β (e i) ∈ Submodule.span ℤ (β '' (e '' B)) := by
  have himage : h '' (β '' (e '' B)) = α '' B := by
    rw [Set.image_image, Set.image_image]
    simp only [hroot]
  rw [← hroot i, ← himage, ← Submodule.map_span]
  constructor
  · rintro ⟨y, hy, hey⟩
    exact hinj hey ▸ hy
  · intro hmem
    exact ⟨β (e i), hmem, rfl⟩

private theorem positive_iff_of_injective {I J X X' Y Y' : Type u}
    [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y] [AddCommGroup Y']
    (D : RootDatum I X Y) (E : RootDatum J X' Y') (b : D.Base) (c : E.Base)
    (d : I ≃ J) (h : X' →ₗ[ℤ] X) (hinj : Function.Injective h)
    (hroot : ∀ i, h (E.root (d i)) = D.root i)
    (hbase : ∀ i, i ∈ b.support ↔ d i ∈ c.support) (i : I) :
    b.IsPos i ↔ c.IsPos (d i) := by
  let e : b.support ≃ c.support := d.subtypeEquiv hbase
  have he (j : b.support) : h (E.root (e j).val) = D.root j := hroot j
  have he' (j : c.support) : h (E.root j) = D.root (e.symm j).val := by
    simpa only [e.apply_symm_apply] using he (e.symm j)
  constructor
  · intro hi
    obtain ⟨a, hnonneg, -, ha⟩ := positive_coefficients D b hi
    apply positive_height E c (a ∘ e.symm) (fun j ↦ hnonneg _)
    apply hinj
    rw [map_sum, hroot, ← ha]
    simp only [map_zsmul, he', Function.comp_apply]
    exact e.symm.sum_comp (fun j ↦ a j • D.root j.val)
  · intro hi
    obtain ⟨a, hnonneg, -, ha⟩ := positive_coefficients E c hi
    apply positive_height D b (a ∘ e) (fun j ↦ hnonneg _)
    rw [← hroot, ← ha, map_sum]
    simp only [map_zsmul, Function.comp_apply]
    calc
      _ = ∑ j : b.support, a (e j) • h (E.root (e j).val) := by simp only [he]
      _ = _ := e.sum_comp (fun j ↦ a j • h (E.root j.val))

private theorem weyl_presentation : WeylPresentation.{u} := by
  classical
  intro I X Y _ _ _ _ _ D _ b H _ g s hrel
  let len := wordLength D b
  have hs (i : b.support) : s i * s i = 1 := reflection_cancel D i.val
  have hg (i : b.support) : g i * g i = 1 := by simpa [hs] using hrel i i
  have hgen := simple_reflections_generate D b
  have hword (w : D.weylGroup) : ∃ p, evaluateWord s p = w := exists_word D b hgen w
  have hzero : len 1 = 0 := by
    obtain ⟨p, -, hp, hmin⟩ := exists_shortest_word D b hgen 1
    have h := hmin [] (by rfl)
    simpa only [hp, List.length_nil, Nat.le_zero] using h
  have hzero' (w : D.weylGroup) (hw : len w = 0) : w = 1 := by
    obtain ⟨p, hp, hl, -⟩ := exists_shortest_word D b hgen w
    have he : p = [] := List.length_eq_zero_iff.mp (hl.trans hw)
    simpa [he, wordProduct] using hp.symm
  obtain ⟨f, hfreg, hf⟩ := exists_regular_functional D b
  have hinv (w : D.weylGroup) : len w = (rightInversions D f w).ncard := by
    change wordLength D b w = _
    rw [← length_inverse D b w, length_eq_inversions D b f hfreg hf hgen]
    simp only [Specs.SimpleRoots.inversions, rightInversions, inv_inv]
  have hfaithful (w : D.weylGroup)
      (hw : ∀ α, b.IsPos α → b.IsPos (D.weylGroupToPerm w α)) : w = 1 := by
    apply hzero'
    have he : rightInversions D f w = ∅ := by
      ext α
      simp only [rightInversions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨hα, hc⟩
      exact (not_lt_of_gt ((hf _).mp (hw α ((hf _).mpr hα)))) hc
    rw [hinv, he, Set.ncard_empty]
  have hup (w : D.weylGroup) (i : b.support)
      (hi : 0 < f (D.root (D.weylGroupToPerm w i))) : len (w * s i) = len w + 1 := by
    rw [hinv, hinv w]
    exact rightInversions_card_mul D b f hf w i hi
  have hdown (w : D.weylGroup) (i : b.support)
      (hi : f (D.root (D.weylGroupToPerm w i)) < 0) : len w = len (w * s i) + 1 := by
    have he : 0 < f (D.root (D.weylGroupToPerm (w * s i) i)) := by
      change 0 < f (D.root (D.weylGroupToPerm (w * weylGroup.ofIdx D i.val) i.val))
      rw [perm_mul, perm_reflection, reflected_value]
      exact neg_pos.mpr hi
    simpa only [mul_assoc, hs, mul_one] using hup (w * s i) i he
  have hstep (w : D.weylGroup) (i : b.support) :
      len (w * s i) + 1 = len w ∨ len w + 1 = len (w * s i) := by
    rcases lt_or_gt_of_ne (hfreg (D.weylGroupToPerm w i)) with hn | hp
    · exact Or.inl (hdown w i hn).symm
    · exact Or.inr (hup w i hp).symm
  have hpositive (w : D.weylGroup) (i : b.support) (hw : ¬ len (w * s i) < len w) :
      0 < f (D.root (D.weylGroupToPerm w i)) := by
    rcases lt_or_gt_of_ne (hfreg (D.weylGroupToPerm w i)) with hn | hp
    · have := hdown w i hn
      exact (hw (by omega)).elim
    · exact hp
  apply presentation_of_descent s len g hs hg hrel hword hzero hstep
  intro w i j a c
  dsimp only
  intro hvi hvj hzi hzj
  exact pair_minimum_unique D b f hf hfaithful w i j a c
    (hpositive _ _ hvi) (hpositive _ _ hvj) (hpositive _ _ hzi) (hpositive _ _ hzj)

/-- The reflections in the base give the presentation of the actual Weyl group. -/
theorem weylPresentation : WeylPresentation.{u} := weyl_presentation

section SchemeComparison

open Specs.NormalizerLatticeAction (ConstantGroup)

variable {k : Type u} [Field k]

private abbrev RationalPoint (G : GroupScheme k) := 𝟙_ (SchemeOver k) ⟶ G.X

private def constantSection {G : GroupScheme k} (Y : SchemeOver k) :
    RationalPoint G →* (Y ⟶ G.X) where
  toFun x := toUnit Y ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private theorem constantSection_precomp {G : GroupScheme k} {Y Z : SchemeOver k}
    (v : Y ⟶ Z) (x : RationalPoint G) : v ≫ constantSection Z x = constantSection Y x := by
  change v ≫ toUnit Z ≫ x = toUnit Y ≫ x
  rw [← Category.assoc, comp_toUnit]

private def sectionMap {G H : GroupScheme k} (f : G ⟶ H) (Y : SchemeOver k) :
    (Y ⟶ G.X) →* (Y ⟶ H.X) where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

private theorem constantSection_map {G H : GroupScheme k} (f : G ⟶ H) (Y : SchemeOver k)
    (x : RationalPoint G) : sectionMap f Y (constantSection Y x) =
      constantSection Y (sectionMap f _ x) := by
  change (toUnit Y ≫ x) ≫ f.hom.hom = toUnit Y ≫ x ≫ f.hom.hom
  exact Category.assoc _ _ _

private theorem constantSection_unit {G : GroupScheme k} (x : RationalPoint G) :
    constantSection (𝟙_ (SchemeOver k)) x = x := by
  change toUnit _ ≫ x = x
  rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]

variable {T N L M : GroupScheme k} {W : Type u} [Group W]

private theorem torus_parameter (j : T ⟶ N) (q : N ⟶ L)
    (hker : IsPullback j.hom.hom (toUnit _) q.hom.hom η[L.X])
    (Y : SchemeOver k) (x y : Y ⟶ N.X)
    (h : sectionMap q Y x = sectionMap q Y y) :
    ∃ t : Y ⟶ T.X, x = sectionMap j Y t * y := by
  have he : (x * y⁻¹) ≫ q.hom.hom = toUnit Y ≫ η[L.X] := by
    change sectionMap q Y (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  refine ⟨hker.lift (x * y⁻¹) (toUnit Y) he, ?_⟩
  change x = (hker.lift _ _ he ≫ j.hom.hom) * y
  rw [hker.lift_fst, inv_mul_cancel_right]

/-- The morphism of underlying schemes is obtained by translation on the
open fibres of the constant quotient. -/
private theorem glue_labelled_sections (j : T ⟶ N) (l : T ⟶ M) (q : N ⟶ L)
    [Mono j.hom.hom] (hker : IsPullback j.hom.hom (toUnit _) q.hom.hom η[L.X])
    (C : ConstantGroup L W) (s : W → RationalPoint N) (m : W → RationalPoint M)
    (hs : ∀ w, sectionMap q _ (s w) = C.sectionPoint w) :
    ∃ a : N.X ⟶ M.X, ∀ (Y : SchemeOver k) (y : Y ⟶ T.X) (w : W),
      (sectionMap j Y y * constantSection Y (s w)) ≫ a =
        sectionMap l Y y * constantSection Y (m w) := by
  let c := C.families N.X q.hom.hom
  let U (w : W) : N.X.left.Opens := ⟨{x | c x = w}, c.isLocallyConstant.isOpen_fiber w⟩
  let P : N.X.left.OpenCover := {
    I₀ := W
    X w := U w
    f w := (U w).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨c x, ⟨⟨x, rfl⟩, rfl⟩⟩, fun w ↦ inferInstance⟩ }
  let Z (w : W) : SchemeOver k := Over.mk ((U w).ι ≫ N.X.hom)
  let p (w : W) : Z w ⟶ N.X := Over.homMk (U w).ι
  have hlabel (w : W) : C.families (Z w) (sectionMap q _ (p w)) =
      LocallyConstant.const _ w := by
    change C.families (Z w) (p w ≫ q.hom.hom) = _
    rw [C.naturality]
    exact LocallyConstant.ext fun x ↦ x.property
  have hp (w : W) : sectionMap q _ (p w) = sectionMap q _ (constantSection (Z w) (s w)) := by
    apply (C.families (Z w)).injective
    rw [hlabel, constantSection_map, hs]
    exact (C.constant (Z w) w).symm
  choose t ht using fun w ↦ torus_parameter j q hker (Z w) (p w) (constantSection _ (s w)) (hp w)
  let localMap (w : W) : Z w ⟶ M.X := sectionMap l _ (t w) * constantSection _ (m w)
  have hglue (v w : W) : pullback.fst (P.f v) (P.f w) ≫ (localMap v).left =
      pullback.snd (P.f v) (P.f w) ≫ (localMap w).left := by
    by_cases h : v = w
    · subst w
      congr 1
      exact (cancel_mono (P.f v)).mp (pullback.condition)
    · let hEmpty : IsEmpty ↥(pullback (P.f v) (P.f w) : Scheme) := ⟨fun z ↦ by
        let x := pullback.fst (P.f v) (P.f w) z
        let y := pullback.snd (P.f v) (P.f w) z
        have he : (P.f v) x = (P.f w) y := by
          dsimp only [x, y]
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        have hx : c ((P.f v) x) = v := x.property
        have hy : c ((P.f w) y) = w := y.property
        exact h (hx.symm.trans ((congrArg c he).trans hy))⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  let a₀ := P.glueMorphisms (fun w ↦ (localMap w).left) hglue
  have ha : a₀ ≫ M.X.hom = N.X.hom := by
    apply P.hom_ext
    intro w
    rw [← Category.assoc, P.ι_glueMorphisms, Over.w (localMap w)]
    rfl
  let a : N.X ⟶ M.X := Over.homMk a₀ ha
  have ha' (w : W) : p w ≫ a = localMap w :=
    Over.OverMorphism.ext (P.ι_glueMorphisms _ hglue w)
  refine ⟨a, ?_⟩
  intro Y y w
  let x := sectionMap j Y y * constantSection Y (s w)
  have hxq : sectionMap q Y x = constantSection Y (C.sectionPoint w) := by
    rw [map_mul, constantSection_map, hs]
    have hy : sectionMap q Y (sectionMap j Y y) = 1 := by
      change (y ≫ j.hom.hom) ≫ q.hom.hom = toUnit Y ≫ η[L.X]
      rw [Category.assoc, hker.w, ← Category.assoc, comp_toUnit]
    rw [hy, one_mul]
  have hxf : ∀ z : Y.left, c (x.left z) = w := by
    have h := (C.naturality x q.hom.hom).symm.trans
      ((congrArg (C.families Y) hxq).trans (C.constant Y w))
    exact fun z ↦ congrArg (fun f : LocallyConstant Y.left W ↦ f z) h
  have hxr : Set.range ⇑x.left ⊆ Set.range ⇑(U w).ι := by
    rintro z ⟨z', rfl⟩
    exact ⟨⟨x.left z', hxf z'⟩, rfl⟩
  let v₀ := IsOpenImmersion.lift (U w).ι x.left hxr
  have hv₀ : v₀ ≫ (U w).ι = x.left := IsOpenImmersion.lift_fac _ _ _
  let v : Y ⟶ Z w := Over.homMk v₀ (by
    change v₀ ≫ (U w).ι ≫ N.X.hom = Y.hom
    rw [← Category.assoc, hv₀, Over.w x])
  have hv : v ≫ p w = x := Over.OverMorphism.ext hv₀
  have ht' : v ≫ t w = y := by
    apply (cancel_mono j.hom.hom).mp
    apply mul_right_cancel (b := constantSection Y (s w))
    have he := congrArg (v ≫ ·) (ht w)
    change v ≫ p w = v ≫ ((t w ≫ j.hom.hom) * constantSection (Z w) (s w)) at he
    rw [hv, MonObj.comp_mul, constantSection_precomp, ← Category.assoc] at he
    exact he.symm
  change x ≫ a = _
  rw [← hv, Category.assoc, ha']
  change v ≫ ((t w ≫ l.hom.hom) * constantSection (Z w) (m w)) = _
  rw [MonObj.comp_mul, constantSection_precomp, ← Category.assoc, ht']
  rfl

/-- A homomorphism on rational sections that respects the torus and its
conjugation on schemes extends over the constant quotient. -/
private theorem extend_rational_comparison (j : T ⟶ N) (l : T ⟶ M) (q : N ⟶ L)
    [Mono j.hom.hom] (hker : IsPullback j.hom.hom (toUnit _) q.hom.hom η[L.X])
    (C : ConstantGroup L W) (s : W → RationalPoint N)
    (hs : ∀ w, sectionMap q _ (s w) = C.sectionPoint w) (hs₁ : s 1 = 1)
    (f : RationalPoint N →* RationalPoint M)
    (hT : ∀ t, f (sectionMap j _ t) = sectionMap l _ t)
    (act : W → (T ⟶ T))
    (hN : ∀ (Y : SchemeOver k) (t : Y ⟶ T.X) (w : W),
      constantSection Y (s w) * sectionMap j Y t =
        sectionMap j Y (sectionMap (act w) Y t) * constantSection Y (s w))
    (hM : ∀ (Y : SchemeOver k) (t : Y ⟶ T.X) (w : W),
      constantSection Y (f (s w)) * sectionMap l Y t =
        sectionMap l Y (sectionMap (act w) Y t) * constantSection Y (f (s w))) :
    ∃ F : N ⟶ M, j ≫ F = l ∧ sectionMap F _ = f := by
  obtain ⟨a, ha⟩ := glue_labelled_sections j l q hker C s (f ∘ s) hs
  have haj : j.hom.hom ≫ a = l.hom.hom := by
    simpa [hs₁, sectionMap, Function.comp_apply] using ha T.X (𝟙 T.X) 1
  have one : η[N.X] ≫ a = η[M.X] := by
    rw [← IsMonHom.one_hom j.hom.hom, Category.assoc, haj, IsMonHom.one_hom]
  have hconst (Y : SchemeOver k) (w : W) :
      sectionMap q Y (constantSection Y (s w)) = constantSection Y (C.sectionPoint w) := by
    rw [constantSection_map, hs]
  have hmul (Y : SchemeOver k) (x y : Y ⟶ N.X) (v w : W)
      (hx : C.families Y (sectionMap q Y x) = LocallyConstant.const _ v)
      (hy : C.families Y (sectionMap q Y y) = LocallyConstant.const _ w) :
      (x * y) ≫ a = (x ≫ a) * (y ≫ a) := by
    have label (n : Y ⟶ N.X) (r : W)
        (h : C.families Y (sectionMap q Y n) = LocallyConstant.const _ r) :
        sectionMap q Y n = sectionMap q Y (constantSection Y (s r)) := by
      apply (C.families Y).injective
      rw [h, hconst]
      exact (C.constant Y r).symm
    obtain ⟨t, ht⟩ := torus_parameter j q hker Y x (constantSection Y (s v)) (label x v hx)
    obtain ⟨u₀, hu⟩ := torus_parameter j q hker Y y (constantSection Y (s w)) (label y w hy)
    obtain ⟨r, hr⟩ := torus_parameter j q hker (𝟙_ (SchemeOver k)) (s v * s w) (s (v * w))
      (by rw [map_mul, hs, hs, hs, map_mul])
    have hr' := congrArg f hr
    rw [map_mul, map_mul, hT] at hr'
    have hN' := congrArg (constantSection Y : RationalPoint N →* (Y ⟶ N.X)) hr
    have hM' := congrArg (constantSection Y : RationalPoint M →* (Y ⟶ M.X)) hr'
    simp only [map_mul, ← constantSection_map] at hN' hM'
    let z := t * sectionMap (act v) Y u₀ * constantSection Y r
    have multiply_translates : ∀ (K : GroupScheme k) (i : T ⟶ K) (b c d : Y ⟶ K.X),
        b * sectionMap i Y u₀ = sectionMap i Y (sectionMap (act v) Y u₀) * b →
        b * c = sectionMap i Y (constantSection Y r) * d →
        (sectionMap i Y t * b) * (sectionMap i Y u₀ * c) = sectionMap i Y z * d := by
      intro K i b c d h₁ h₂
      calc
        _ = (sectionMap i Y t * (b * sectionMap i Y u₀)) * c := by simp only [mul_assoc]
        _ = (sectionMap i Y t * sectionMap i Y (sectionMap (act v) Y u₀)) * (b * c) := by
          rw [h₁]; simp only [mul_assoc]
        _ = sectionMap i Y z * d := by rw [h₂]; simp only [z, map_mul, mul_assoc]
    have hxy : x * y = sectionMap j Y z * constantSection Y (s (v * w)) := by
      rw [ht, hu]
      exact multiply_translates N j _ _ _ (hN Y u₀ v) hN'
    rw [hxy, ha, ht, hu, ha, ha]
    exact (multiply_translates M l _ _ _ (hM Y u₀ v) hM').symm
  have mul : μ[N.X] ≫ a = (a ⊗ₘ a) ≫ μ[M.X] := by
    let p := fst N.X N.X
    let r := snd N.X N.X
    have e₁ : p * r = μ[N.X] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have e₂ : (p ≫ a) * (r ≫ a) = (a ⊗ₘ a) ≫ μ[M.X] := by
      rw [Hom.mul_def]
      have e : lift (p ≫ a) (r ≫ a) = a ⊗ₘ a := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [p, r]
      rw [e]
    rw [← e₁, ← e₂]
    apply Over.OverMorphism.ext
    apply Scheme.hom_ext_of_forall
    intro b
    let V := N.X ⊗ N.X
    let cp := C.families V (sectionMap q V p)
    let cr := C.families V (sectionMap q V r)
    let U : V.left.Opens := ⟨{z | cp z = cp b ∧ cr z = cr b},
      (cp.isLocallyConstant.isOpen_fiber (cp b)).inter (cr.isLocallyConstant.isOpen_fiber (cr b))⟩
    let Z : SchemeOver k := Over.mk (U.ι ≫ V.hom)
    let i : Z ⟶ V := Over.homMk U.ι
    have hp : C.families Z (sectionMap q Z (i ≫ p)) = LocallyConstant.const _ (cp b) := by
      change C.families Z ((i ≫ p) ≫ q.hom.hom) = _
      rw [Category.assoc, C.naturality]
      exact LocallyConstant.ext fun z ↦ z.property.1
    have hr : C.families Z (sectionMap q Z (i ≫ r)) = LocallyConstant.const _ (cr b) := by
      change C.families Z ((i ≫ r) ≫ q.hom.hom) = _
      rw [Category.assoc, C.naturality]
      exact LocallyConstant.ext fun z ↦ z.property.2
    refine ⟨U, ⟨rfl, rfl⟩, ?_⟩
    have h := hmul Z (i ≫ p) (i ≫ r) (cp b) (cr b) hp hr
    have h' : i ≫ ((p * r) ≫ a) = i ≫ ((p ≫ a) * (r ≫ a)) := by
      rw [← Category.assoc, MonObj.comp_mul, h, MonObj.comp_mul, Category.assoc, Category.assoc]
    exact congrArg (fun g : Z ⟶ M.X ↦ g.left) h'
  let F : N ⟶ M := Grp.homMk'' a one mul
  refine ⟨F, Grp.hom_ext _ _ haj, ?_⟩
  apply MonoidHom.ext
  intro x
  let U := 𝟙_ (SchemeOver k)
  let qx := C.families U (sectionMap q U x)
  let b : U.left := IsLocalRing.closedPoint k
  let w := qx b
  have he : sectionMap q U x = sectionMap q U (s w) := by
    apply (C.families U).injective
    rw [hs]
    have h : C.families U (C.sectionPoint w) = LocallyConstant.const U.left w := by
      have hc := C.constant U w
      change C.families U (constantSection U (C.sectionPoint w)) = _ at hc
      rwa [constantSection_unit] at hc
    rw [h]
    exact LocallyConstant.ext fun z ↦ congrArg qx (@Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance z b)
  obtain ⟨t, ht⟩ := torus_parameter j q hker U x (s w) he
  have ht' := congrArg f ht
  rw [map_mul, hT] at ht'
  change x ≫ a = f x
  rw [ht', ht]
  simpa only [constantSection_unit, Function.comp_apply] using ha (𝟙_ (SchemeOver k)) t w

private def actionOfWord {S : Type u} (act : S → (T ≅ T)) : List S → (T ⟶ T)
  | [] => 𝟙 T
  | i :: p => actionOfWord act p ≫ (act i).hom

private theorem move_through_word {S : Type u} {K : GroupScheme k}
    (act : S → (T ≅ T)) (r : S → RationalPoint K) (j : T ⟶ K)
    (hact : ∀ (Y : SchemeOver k) (t : Y ⟶ T.X) (i : S),
      constantSection Y (r i) * sectionMap j Y t =
        sectionMap j Y (sectionMap (act i).hom Y t) * constantSection Y (r i))
    (Y : SchemeOver k) (t : Y ⟶ T.X) (p : List S) :
    constantSection Y (evaluateWord r p) * sectionMap j Y t =
      sectionMap j Y (sectionMap (actionOfWord act p) Y t) *
        constantSection Y (evaluateWord r p) := by
  induction p with
  | nil => simp [actionOfWord, sectionMap]
  | cons i p ih =>
    simp only [evaluateWord_cons, map_mul, actionOfWord]
    rw [mul_assoc, ih, ← mul_assoc, hact, mul_assoc]
    rfl

/-- Exact torus relations for the simple lifts suffice to obtain a map of
split extensions by the Weyl group. -/
private theorem compare_split_extensions {S : Type u} (j : T ⟶ N) (l : T ⟶ M) (q : N ⟶ L)
    [Mono j.hom.hom] (hker : IsPullback j.hom.hom (toUnit _) q.hom.hom η[L.X])
    (C : ConstantGroup L W) (e : W ≃* RationalPoint L) (he : ∀ w, e w = C.sectionPoint w)
    (s : S → W) (n : S → RationalPoint N) (m : S → RationalPoint M)
    (hn : ∀ i, sectionMap q _ (n i) = C.sectionPoint (s i))
    (act : S → (T ≅ T))
    (hN : ∀ (Y : SchemeOver k) (t : Y ⟶ T.X) (i : S),
      constantSection Y (n i) * sectionMap j Y t =
        sectionMap j Y (sectionMap (act i).hom Y t) * constantSection Y (n i))
    (hM : ∀ (Y : SchemeOver k) (t : Y ⟶ T.X) (i : S),
      constantSection Y (m i) * sectionMap l Y t =
        sectionMap l Y (sectionMap (act i).hom Y t) * constantSection Y (m i))
    (hrel : ∀ i i', ∃ t : RationalPoint T,
      (n i * n i') ^ orderOf (s i * s i') = sectionMap j _ t ∧
      (m i * m i') ^ orderOf (s i * s i') = sectionMap l _ t)
    (hword : ∀ w, ∃ p, evaluateWord s p = w)
    (hpres : ∀ {H : Type u} [Group H] (g : S → H),
      (∀ i i', (g i * g i') ^ orderOf (s i * s i') = 1) →
        ∃! f : W →* H, ∀ i, f (s i) = g i) :
    ∃ F : N ⟶ M, j ≫ F = l ∧ ∀ i, sectionMap F _ (n i) = m i := by
  classical
  let U := 𝟙_ (SchemeOver k)
  let q' := e.symm.toMonoidHom.comp (sectionMap q U)
  have hq' (i : S) : q' (n i) = s i := by
    change e.symm (sectionMap q U (n i)) = s i
    rw [hn, ← he, e.symm_apply_apply]
  have hkernel (x : RationalPoint N) : q' x = 1 ↔ sectionMap q U x = 1 := by
    change e.symm (sectionMap q U x) = 1 ↔ _
    rw [← map_one e.symm]
    exact e.symm.injective.eq_iff
  have hkj : q'.ker = (sectionMap j U).range := by
    ext x
    change q' x = 1 ↔ ∃ t, sectionMap j U t = x
    rw [hkernel]
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := torus_parameter j q hker U x 1 (by simpa using hx)
      exact ⟨t, by simpa using ht.symm⟩
    · rintro ⟨t, rfl⟩
      change (t ≫ j.hom.hom) ≫ q.hom.hom = toUnit U ≫ η[L.X]
      rw [Category.assoc, hker.w, ← Category.assoc, comp_toUnit]
  have hinj : Function.Injective (sectionMap j U) := fun _ _ h ↦ (cancel_mono j.hom.hom).mp h
  have hact (i : S) : ∃ a : RationalPoint T ≃* RationalPoint T, ∀ t,
      n i * sectionMap j U t * (n i)⁻¹ = sectionMap j U (a t) ∧
      m i * sectionMap l U t * (m i)⁻¹ = sectionMap l U (a t) := by
    let a : RationalPoint T ≃* RationalPoint T :=
      { toFun := sectionMap (act i).hom U
        invFun := sectionMap (act i).inv U
        left_inv := fun t ↦ by
          change (t ≫ (act i).hom.hom.hom) ≫ (act i).inv.hom.hom = t
          rw [Category.assoc]
          change t ≫ ((act i).hom ≫ (act i).inv).hom.hom = t
          rw [Iso.hom_inv_id]
          exact Category.comp_id _
        right_inv := fun t ↦ by
          change (t ≫ (act i).inv.hom.hom) ≫ (act i).hom.hom.hom = t
          rw [Category.assoc]
          change t ≫ ((act i).inv ≫ (act i).hom).hom.hom = t
          rw [Iso.inv_hom_id]
          exact Category.comp_id _
        map_mul' := map_mul (sectionMap (act i).hom U) }
    refine ⟨a, fun t ↦ ⟨mul_inv_eq_iff_eq_mul.mpr ?_, mul_inv_eq_iff_eq_mul.mpr ?_⟩⟩
    · change n i * sectionMap j U t = sectionMap j U (sectionMap (act i).hom U t) * n i
      simpa only [constantSection_unit] using hN (𝟙_ (SchemeOver k)) t i
    · change m i * sectionMap l U t = sectionMap l U (sectionMap (act i).hom U t) * m i
      simpa only [constantSection_unit] using hM (𝟙_ (SchemeOver k)) t i
  obtain ⟨f, hf, hnm⟩ := compare_extensions s n m q' (sectionMap j U) (sectionMap l U)
    hinj hkj hq' hact hrel @hpres
  let p (w : W) := if h : w = 1 then [] else (hword w).choose
  have hp (w : W) : evaluateWord s (p w) = w := by
    by_cases h : w = 1
    · simp [p, h]
    · simpa [p, h] using (hword w).choose_spec
  have hqe (w : W) : sectionMap q U (evaluateWord n (p w)) = C.sectionPoint w := by
    have h (p : List S) : q' (evaluateWord n p) = evaluateWord s p := by
      induction p with
      | nil => simp
      | cons i p ih => simp [hq', ih]
    apply e.symm.injective
    change q' (evaluateWord n (p w)) = _
    rw [h, hp, ← he, e.symm_apply_apply]
  have hfe (p : List S) : f (evaluateWord n p) = evaluateWord m p := by
    induction p with
    | nil => simp
    | cons i p ih => simp [hnm, ih]
  obtain ⟨F, hFj, hF⟩ := extend_rational_comparison j l q hker C
    (fun w ↦ evaluateWord n (p w)) hqe (by simp [p]) f (DFunLike.congr_fun hf)
    (fun w ↦ actionOfWord act (p w))
    (fun Y t w ↦ move_through_word act n j hN Y t (p w))
    (fun Y t w ↦ by simpa only [hfe] using move_through_word act m l hM Y t (p w))
  exact ⟨F, hFj, fun i ↦ by rw [hF, hnm]⟩

end SchemeComparison

open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.RankTwoLifting (Compatible)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character compositionPairing)
open Specs.CellHomomorphism (pullbackCharacters)

section PinnedCompatibility

variable {k : Type u} [Field k] {A : AdditiveLine k} {P Q : PinnedGroup A}
  {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
  {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}

private def compatibleSimpleRoots (h : Compatible P Q D E d τ) :
    SimpleRoot P.pair ≃ SimpleRoot Q.pair :=
  d.subtypeEquiv fun α ↦ (D.simple_iff α).symm.trans ((h.simple α).trans (E.simple_iff (d α)))

private theorem compatible_opposites (h : Compatible P Q D E d τ)
    (α β : Root P.pair.T) (hβ : β.val = α.val⁻¹) : (d β).val = (d α).val⁻¹ := by
  apply h.injective
  rw [map_inv]
  change (τ ≫ (d β).val) = (τ ≫ (d α).val)⁻¹
  rwa [h.root, h.root]

/-- The torus conjugations of the pinned representatives intertwine after
pullback on each character, including characters outside the root lattice. -/
private theorem compatible_reflection_characters (h : Compatible P Q D E d τ)
    (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair) (hj : d i.val = j.val)
    (n : SimpleRepresentative P D i) (m : SimpleRepresentative Q E j)
    (χ : Character Q.pair.T.group) :
    n.reflection.conjugation.inv ≫ τ ≫ χ = τ ≫ m.reflection.conjugation.inv ≫ χ := by
  let hD := D.comm
  let hE := E.comm
  have hroot : τ ≫ j.val.val = i.val.val := by simpa only [hj] using h.root i.val
  have hcore : n.reflection.coroot ≫ τ = m.reflection.coroot := by
    rw [n.coroot_eq, m.coroot_eq]
    simpa only [hj] using h.coroot i.val
  have hpair : CharacterPairing.pairing P.pair.T.group (τ ≫ χ) n.reflection.coroot =
      CharacterPairing.pairing Q.pair.T.group χ m.reflection.coroot := by
    unfold CharacterPairing.pairing compositionPairing
    rw [← Category.assoc, hcore]
  rw [n.reflection.reflection, m.reflection.reflection, hpair]
  change _ = pullbackCharacters τ (χ * j.val.val ^ _)
  rw [map_mul, map_zpow]
  change _ = (τ ≫ χ) * (τ ≫ j.val.val) ^ _
  rw [hroot]

end PinnedCompatibility

open Specs.CharacterDescent (Character StandardLattice)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus)

open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

section Torus

variable {k : Type u} [Field k]

private theorem split_character_hom_ext {T S : GroupScheme k} (hT : IsSplitTorus T)
    (hS : IsSplitTorus S) (f g : T ⟶ S)
    (h : ∀ χ : Character S, f ≫ χ = g ≫ χ) : f = g := by
  obtain ⟨r, ⟨a⟩⟩ := splitPresentation hT
  obtain ⟨s, ⟨b⟩⟩ := splitPresentation hS
  let X := StandardLattice.{u} r
  let Y := StandardLattice.{u} s
  let e := splitGroupHomEquiv (k := k) Y X
  let f' := e.symm (a.hom ≫ f ≫ b.inv)
  let g' := e.symm (a.hom ≫ g ≫ b.inv)
  have hf : e f' = a.hom ≫ f ≫ b.inv := e.apply_symm_apply _
  have hg : e g' = a.hom ≫ g ≫ b.inv := e.apply_symm_apply _
  apply (cancel_epi a.hom).mp
  apply (cancel_mono b.inv).mp
  rw [Category.assoc, Category.assoc, ← hf, ← hg]
  apply congrArg e
  apply MonoidHom.ext
  intro y
  let d : IntegerCharacters.{u} →* Y := (zpowersHom Y y).comp MulEquiv.ulift.toMonoidHom
  let χ : Character (specGroup (groupAlgebra k Y)) := specGroupMap (groupAlgebraMap k d)
  have hχ : e f' ≫ χ = e g' ≫ χ := by
    simp only [hf, hg, Category.assoc]
    exact congrArg (a.hom ≫ ·) (h (b.inv ≫ χ))
  have comp (l : Y →* X) : e l ≫ χ =
      splitGroupHomEquiv (k := k) IntegerCharacters X (l.comp d) := by
    change specGroupMap (groupAlgebraMap k l) ≫ specGroupMap (groupAlgebraMap k d) =
      specGroupMap (groupAlgebraMap k (l.comp d))
    rw [← specGroupMap_comp]
    congr 1
    apply CommHopfAlgCat.hom_ext
    exact (MonoidAlgebra.mapDomainBialgHom_comp (R := k) l d).symm
  rw [comp, comp] at hχ
  have h' := (splitGroupHomEquiv (k := k) IntegerCharacters X).injective hχ
  have hd : d integerGenerator = y := by
    change y ^ (1 : ℤ) = y
    exact zpow_one _
  simpa only [MonoidHom.comp_apply, hd] using DFunLike.congr_fun h' integerGenerator

end Torus

open Specs.AbstractPairing (Datum Root)
open Specs.CharacterDescent (Character Cocharacter)

private theorem root_datum_eq {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (D E : RootDatum I X Y) (hpair : D.toLinearMap = E.toLinearMap)
    (hroot : D.root = E.root) (hcoroot : D.coroot = E.coroot) : D = E := by
  have hperm : D.reflectionPerm = E.reflectionPerm := by
    funext i
    apply Equiv.ext
    intro j
    apply D.root.injective
    rw [← D.reflectionPerm_root, hroot, hcoroot, hpair, E.reflectionPerm_root]
  cases D
  cases E
  cases hpair
  cases hroot
  cases hcoroot
  cases hperm
  rfl

private theorem datum_eq_of_coroots {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (D E : Datum T)
    (h : ∀ i : Root T, D.rootDatum.coroot i = E.rootDatum.coroot i) : D = E := by
  have hpair : D.rootDatum.toLinearMap = E.rootDatum.toLinearMap := by
    apply LinearMap.ext
    intro χ
    apply LinearMap.ext
    intro lam
    exact (D.pairing_eq (Additive.toMul χ) (Additive.toMul lam)).trans
      (E.pairing_eq (Additive.toMul χ) (Additive.toMul lam)).symm
  have hroot : D.rootDatum.root = E.rootDatum.root := by
    apply Function.Embedding.ext
    intro i
    exact (D.root_eq i).trans (E.root_eq i).symm
  have hD : D.rootDatum = E.rootDatum := root_datum_eq _ _ hpair hroot (Function.Embedding.ext h)
  cases D
  cases E
  cases hD
  rfl

section CorootUniqueness

open Specs.AbstractPairing (Datum)
open Specs.RootGroups (CorootReflection)
open Specs.NormalizerLatticeAction (SplitImage)
open Specs.CharacterDescent (Cocharacter)
open private root_determines_coroot latticeAction quotientLabel quotientLabel_conjugates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
open private inducedConjugation_unique
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl

variable {k : Type u} [Field k] {A A' : AdditiveLine k}

private theorem coroot_eq_of_linked_coordinates {G : AffineAlgebraicGroup k}
    {T N : ClosedSubgroup G.val} {Q : GroupScheme k} [IsCommMonObj T.group.X]
    {q : N.group ⟶ Q} (I : SplitImage T.inclusion N.inclusion q)
    (hN : RepresentsSubgroup N (fun _ n ↦ Normalizes T.inclusion n)) (D : Datum T)
    {α : Character T.group} {x y : A.group ⟶ G.val} {x' y' : A'.group ⟶ G.val}
    (r : CorootReflection T α x y) (s : CorootReflection T α x' y') : r.coroot = s.coroot := by
  letI := D.freeCharacters
  letI := I.finite
  let B := D.rootDatum.toLinearMap
  let ρ := latticeAction I
  have matching_label {L : AdditiveLine k} {xp xn : L.group ⟶ G.val}
      (a : CorootReflection T α xp xn) :
      ∃ w : I.labels, ∀ χ : Additive (Character T.group),
        ρ w χ = χ - B χ (Additive.ofMul a.coroot) • Additive.ofMul α := by
    obtain ⟨n, hn⟩ := (hN _ _).mp a.normalizes
    let w := quotientLabel I n
    refine ⟨w, fun χ ↦ ?_⟩
    have h := quotientLabel_conjugates I n
    have he : a.conjugation = I.conjugation w := by
      apply inducedConjugation_unique a.conjugates
      rw [← hn]
      exact h
    change Additive.ofMul (w.val (Additive.toMul χ)) = _
    rw [I.characterAction, ← he, a.reflection]
    change _ = Additive.ofMul (Additive.toMul χ) -
      D.rootDatum.toLinearMap (Additive.ofMul (Additive.toMul χ)) (Additive.ofMul a.coroot) •
        Additive.ofMul α
    rw [D.pairing_eq, sub_eq_add_neg, ← neg_smul, ofMul_mul, ofMul_zpow]
  obtain ⟨v, hv⟩ := matching_label r
  obtain ⟨w, hw⟩ := matching_label s
  have hr : B (Additive.ofMul α) (Additive.ofMul r.coroot) = 2 :=
    (D.pairing_eq α r.coroot).trans r.root_pairing
  have hs : B (Additive.ofMul α) (Additive.ofMul s.coroot) = 2 :=
    (D.pairing_eq α s.coroot).trans s.root_pairing
  exact Additive.ofMul.injective (root_determines_coroot ρ B hr hs hv hw)

private theorem identification_of_attached_datum (P : Pinning.SplitBorelPair k)
    (D : AttachedDatum P) : Nonempty (@DatumAndWeyl.Identification _ _ _ _ D.comm D.datum) := by
  obtain ⟨hcomm, h⟩ := RootData.DatumAndWeyl.datumAndWeyl P.G P.reductive P.T P.split P.maximal
  letI := hcomm
  obtain ⟨D₀, ⟨W⟩⟩ := h
  have hcoroot (i : Root P.T) : D₀.rootDatum.coroot i = D.datum.rootDatum.coroot i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr⟩ := D₀.attached i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s, hs⟩ := D.datum.attached i
    apply Additive.toMul.injective
    rw [← hr, ← hs]
    exact coroot_eq_of_linked_coordinates W.image W.representsNormalizer D₀ r s
  exact ⟨datum_eq_of_coroots D₀ D.datum hcoroot ▸ W⟩

end CorootUniqueness

section PinnedNormalizer

open Specs.NormalizerLatticeAction (ConstantGroup)
open Specs.DatumAndWeyl (Identification)
open Specs.RootGroups (CorootReflection)
open private rationalSectionsEquiv inducedConjugation_unique labelConjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private relabelConstantGroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem sectionMap_comp {G H K : GroupScheme k} (f : G ⟶ H) (g : H ⟶ K)
    (Y : SchemeOver k) (t : Y ⟶ G.X) :
    sectionMap (f ≫ g) Y t = sectionMap g Y (sectionMap f Y t) := by
  change t ≫ (f ≫ g).hom.hom = (t ≫ f.hom.hom) ≫ g.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem representative_moves_torus {G : GroupScheme k} {T N : ClosedSubgroup G}
    (j : T.group ⟶ N.group) (hj : j ≫ N.inclusion = T.inclusion)
    {α : Character T.group} {xp xn : A.group ⟶ G}
    (r : CorootReflection T α xp xn) (n : RationalPoint N.group)
    (hn : sectionMap N.inclusion _ n = r.representative)
    (Y : SchemeOver k) (t : Y ⟶ T.group.X) :
    constantSection Y n * sectionMap j Y t =
      sectionMap j Y (sectionMap r.conjugation.hom Y t) * constantSection Y n := by
  let hc : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  let hm : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono N.inclusion.hom.hom).mp
  change sectionMap N.inclusion Y (constantSection Y n * sectionMap j Y t) =
    sectionMap N.inclusion Y (sectionMap j Y (sectionMap r.conjugation.hom Y t) * constantSection Y n)
  rw [map_mul, map_mul, constantSection_map, hn]
  have ht (t : Y ⟶ T.group.X) : sectionMap N.inclusion Y (sectionMap j Y t) =
      sectionMap T.inclusion Y t := by
    change (t ≫ j.hom.hom) ≫ N.inclusion.hom.hom = _
    rw [Category.assoc]
    change t ≫ (j ≫ N.inclusion).hom.hom = _
    rw [hj]
    rfl
  rw [ht, ht]
  apply mul_inv_eq_iff_eq_mul.mp
  change constantSection Y r.representative * sectionMap T.inclusion Y t *
    (constantSection Y r.representative)⁻¹ = (t ≫ r.conjugation.hom.hom.hom) ≫ T.inclusion.hom.hom
  have he := congrArg (fun h : T.group.X ⟶ G.X ↦ t ≫ h) r.conjugates
  simp only [Grp.comp_hom_hom, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc t (toUnit T.group.X), comp_toUnit] at he
  simpa only [Category.assoc, sectionMap, constantSection, MonoidHom.coe_mk, OneHom.coe_mk] using he.symm

private theorem representative_label {P : PinnedGroup A} (D : AttachedDatum P.pair)
    [IsCommMonObj P.pair.T.group.X] (I : Identification D.datum) (i : SimpleRoot P.pair)
    (r : SimpleRepresentative P D i) (n : RationalPoint I.normalizer.group)
    (hn : sectionMap I.normalizer.inclusion _ n = r.reflection.representative)
    (w : I.image.labels) (hw : sectionMap I.quotient _ n = I.image.constantGroup.sectionPoint w) :
    w = I.labelEquiv (weylGroup.ofIdx D.datum.rootDatum i.val) := by
  have hconj : r.reflection.conjugation = I.image.conjugation w := by
    apply inducedConjugation_unique
    · exact r.reflection.conjugates
    · rw [← hn]
      exact labelConjugation I.image w n hw
  apply Subtype.ext
  apply MulEquiv.ext
  intro χ
  apply Additive.ofMul.injective
  rw [I.image.characterAction, ← hconj, r.reflection.reflection, ← I.characterAction]
  change Additive.ofMul _ =
    (RootPairing.Equiv.reflection D.datum.rootDatum i.val).weightEquiv (Additive.ofMul χ)
  rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, D.datum.root_eq]
  have hp : D.datum.rootDatum.coroot' i.val (Additive.ofMul χ) =
      CharacterPairing.pairing P.pair.T.group χ r.reflection.coroot := by
    rw [r.coroot_eq]
    exact D.datum.pairing_eq χ _
  rw [hp, sub_eq_add_neg, ← neg_smul, ofMul_mul, ofMul_zpow]

private theorem compatible_conjugations {P Q : PinnedGroup A}
    {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}
    (h : Compatible P Q D E d τ) (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair)
    (hj : d i.val = j.val) (n : SimpleRepresentative P D i) (m : SimpleRepresentative Q E j) :
    n.reflection.conjugation.hom ≫ τ = τ ≫ m.reflection.conjugation.hom := by
  have he := split_character_hom_ext P.pair.split Q.pair.split
    (n.reflection.conjugation.inv ≫ τ) (τ ≫ m.reflection.conjugation.inv)
    (fun χ ↦ by simpa only [Category.assoc] using compatible_reflection_characters h i j hj n m χ)
  calc
    _ = n.reflection.conjugation.hom ≫ (τ ≫ m.reflection.conjugation.inv) ≫
        m.reflection.conjugation.hom := by simp
    _ = n.reflection.conjugation.hom ≫ (n.reflection.conjugation.inv ≫ τ) ≫
        m.reflection.conjugation.hom := by rw [he]
    _ = _ := by simp

private def simpleRootOfIndex {P : PinnedGroup A} (D : AttachedDatum P.pair) :
    letI := D.comm
    D.base.support → SimpleRoot P.pair := fun i ↦ ⟨i.val, (D.simple_iff i.val).mp i.property⟩

/-- Once the torus powers are matched, the comparison is a morphism of the
actual scheme normalizers and agrees with the specified pinned lifts. -/
private theorem compare_pinned_from_powers (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) [IsCommMonObj P.pair.T.group.X]
    (d : Root P.pair.T ≃ Root Q.pair.T) (τ : P.pair.T.group ⟶ Q.pair.T.group)
    (h : Compatible P Q D E d τ) (W : Identification D.datum)
    (M : ClosedSubgroup Q.pair.G.val)
    (hM : RepresentsSubgroup M (fun _ g ↦ Normalizes Q.pair.T.inclusion g))
    (l : Q.pair.T.group ⟶ M.group) (hl : l ≫ M.inclusion = Q.pair.T.inclusion)
    (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
    (m : ∀ i : SimpleRoot Q.pair, SimpleRepresentative Q E i)
    (hpowers : letI := D.comm
      let e := compatibleSimpleRoots h
      let s := simpleReflection D.datum.rootDatum D.base
      ∀ i j : D.base.support, ∃ t : RationalPoint P.pair.T.group,
        ((n (simpleRootOfIndex D i)).reflection.representative *
          (n (simpleRootOfIndex D j)).reflection.representative) ^ orderOf (s i * s j) =
            sectionMap P.pair.T.inclusion _ t ∧
        ((m (e (simpleRootOfIndex D i))).reflection.representative *
          (m (e (simpleRootOfIndex D j))).reflection.representative) ^ orderOf (s i * s j) =
            sectionMap (τ ≫ Q.pair.T.inclusion) _ t) :
    ∃ F : W.normalizer.group ⟶ M.group, W.torusInclusion ≫ F = τ ≫ l ∧
      ∀ (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair), d i.val = j.val →
        ∃ x : RationalPoint W.normalizer.group,
          x ≫ W.normalizer.inclusion.hom.hom = (n i).reflection.representative ∧
          x ≫ F.hom.hom ≫ M.inclusion.hom.hom = (m j).reflection.representative := by
  letI : Finite (Root P.pair.T) := D.datum.finiteRoots
  letI : Module.Free ℤ (Additive (Character P.pair.T.group)) := D.datum.freeCharacters
  letI : Module.Finite ℤ (Additive (Character P.pair.T.group)) := D.datum.finiteCharacters
  letI : D.datum.rootDatum.IsReduced := D.datum.reduced
  let S := D.base.support
  let s := simpleReflection D.datum.rootDatum D.base
  let a := simpleRootOfIndex D
  let b := compatibleSimpleRoots h ∘ a
  obtain ⟨x, hx⟩ := Classical.axiomOfChoice (fun i : S ↦
    (W.representsNormalizer _ _).mp (n (a i)).reflection.normalizes)
  obtain ⟨y, hy⟩ := Classical.axiomOfChoice (fun i : S ↦
    (hM _ _).mp (m (b i)).reflection.normalizes)
  have hx' (i : S) : sectionMap W.normalizer.inclusion _ (x i) =
      (n (a i)).reflection.representative := hx i
  have hy' (i : S) : sectionMap M.inclusion _ (y i) =
      (m (b i)).reflection.representative := hy i
  obtain ⟨e, he⟩ := rationalSectionsEquiv W.image.constantGroup
  let C := relabelConstantGroup W.image.constantGroup W.labelEquiv
  let e' := W.labelEquiv.trans e
  have he' (w : D.datum.rootDatum.weylGroup) : e' w = C.sectionPoint w := he _
  have hlabels (i : S) : sectionMap W.quotient _ (x i) = C.sectionPoint (s i) := by
    obtain ⟨w, hw⟩ := e.surjective (sectionMap W.quotient _ (x i))
    have hw' := hw.symm.trans (he w)
    calc
      _ = W.image.constantGroup.sectionPoint w := hw'
      _ = C.sectionPoint (s i) := congrArg W.image.constantGroup.sectionPoint
        (representative_label D W (a i) (n (a i)) (x i) (hx i) w hw')
  have hclosedN : IsClosedImmersion W.normalizer.inclusion.hom.hom.left := W.normalizer.isClosedImmersion
  have hclosedM : IsClosedImmersion M.inclusion.hom.hom.left := M.isClosedImmersion
  have hclosedj : IsClosedImmersion W.torusInclusion.hom.hom.left := W.torusClosed
  let monoN : Mono W.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  let monoM : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  let monoj : Mono W.torusInclusion.hom.hom := Over.mono_of_mono_left _
  have torus_powers (i j : S) : ∃ t : RationalPoint P.pair.T.group,
      (x i * x j) ^ orderOf (s i * s j) = sectionMap W.torusInclusion _ t ∧
      (y i * y j) ^ orderOf (s i * s j) = sectionMap (τ ≫ l) _ t := by
    obtain ⟨t, h₁, h₂⟩ := hpowers i j
    refine ⟨t, ?_, ?_⟩
    · apply (cancel_mono W.normalizer.inclusion.hom.hom).mp
      change sectionMap W.normalizer.inclusion _ _ = sectionMap W.normalizer.inclusion _ _
      rw [map_pow, map_mul]
      change (_ * _) ^ _ = (t ≫ W.torusInclusion.hom.hom) ≫ W.normalizer.inclusion.hom.hom
      rw [Category.assoc]
      change (_ * _) ^ _ = t ≫ (W.torusInclusion ≫ W.normalizer.inclusion).hom.hom
      rw [W.inclusion_eq, hx' i, hx' j]
      exact h₁
    · apply (cancel_mono M.inclusion.hom.hom).mp
      change sectionMap M.inclusion _ _ = sectionMap M.inclusion _ _
      rw [map_pow, map_mul]
      change (_ * _) ^ _ = (t ≫ (τ ≫ l).hom.hom) ≫ M.inclusion.hom.hom
      rw [Category.assoc]
      change (_ * _) ^ _ = t ≫ ((τ ≫ l) ≫ M.inclusion).hom.hom
      rw [Category.assoc, hl, hy' i, hy' j]
      exact h₂
  let act (i : S) := (n (a i)).reflection.conjugation
  have target_acts (Y : SchemeOver k) (t : Y ⟶ P.pair.T.group.X) (i : S) :
      constantSection Y (y i) * sectionMap (τ ≫ l) Y t =
        sectionMap (τ ≫ l) Y (sectionMap (act i).hom Y t) * constantSection Y (y i) := by
    have he := compatible_conjugations h (a i) (b i) rfl (n (a i)) (m (b i))
    have hr := representative_moves_torus l hl (m (b i)).reflection (y i) (hy i)
      Y (sectionMap τ Y t)
    simp only [sectionMap_comp]
    have ht : sectionMap τ Y (sectionMap (act i).hom Y t) =
        sectionMap (m (b i)).reflection.conjugation.hom Y (sectionMap τ Y t) := by
      rw [← sectionMap_comp, ← sectionMap_comp]
      exact congrArg (fun f : P.pair.T.group ⟶ Q.pair.T.group ↦ sectionMap f Y t) he
    rw [ht]
    exact hr
  obtain ⟨F, hFt, hF⟩ := compare_split_extensions W.torusInclusion (τ ≫ l) W.quotient
    W.isQuotient.1 C e' he' s x y hlabels act
    (fun Y t i ↦ representative_moves_torus W.torusInclusion W.inclusion_eq
      (n (a i)).reflection (x i) (hx i) Y t)
    target_acts torus_powers
    (exists_word D.datum.rootDatum D.base (simple_reflections_generate D.datum.rootDatum D.base))
    (weyl_presentation D.datum.rootDatum D.base)
  refine ⟨F, hFt, ?_⟩
  intro i j hEq
  let a₀ : S := ⟨i.val, (D.simple_iff i.val).mpr i.property⟩
  have ha : a a₀ = i := Subtype.ext rfl
  have hb : b a₀ = j := Subtype.ext hEq
  refine ⟨x a₀, ?_, ?_⟩
  · have ht := hx' a₀
    rw [ha] at ht
    exact ht
  · have heq : x a₀ ≫ F.hom.hom = y a₀ := hF a₀
    rw [← Category.assoc, heq]
    have ht := hy' a₀
    rw [hb] at ht
    exact ht

end PinnedNormalizer

section Centralizer

open Specs.CharacterDescent (Character)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open Specs.SubtorusCentralizer (IsCentralizer)
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)

open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

variable {k : Type u} [Field k] {A : AdditiveLine k} {G : GroupScheme k}

set_option backward.isDefEq.respectTransparency false in
/-- A root coordinate whose weight is trivial on a subtorus factors through
its scheme centralizer. -/
private theorem root_coordinate_in_centralizer {T S C : ClosedSubgroup G}
    (j : S.group ⟶ T.group) (hj : j ≫ T.inclusion = S.inclusion)
    (hC : IsCentralizer S C) {α : Character T.group} (hα : j ≫ α = 1)
    (x : A.group ⟶ G) (hx : HasScalarAction T α x) :
    ∃ y : A.group ⟶ C.group, y ≫ C.inclusion = x := by
  have h : Centralizes S.inclusion x.hom.hom := by
    apply (centralizes_iff_affine _ _).mpr
    intro R t s
    obtain ⟨a, ha⟩ := (additivePoints A R).surjective t
    have hval : characterValue α R (s ≫ j.hom.hom) = 1 := by
      have h' := characterValue_one (T := S.group) R s
      rw [← hα] at h'
      unfold characterValue at h' ⊢
      simpa only [Grp.comp_hom_hom, ← Category.assoc] using h'
    have ht : rootPoint x R a = t ≫ x.hom.hom := by
      rw [← ha]
      change rootPoint x R a = rootPoint (𝟙 A.group) R a ≫ x.hom.hom
      rw [← rootPoint_comp, Category.id_comp]
    let g : GroupPoints G R := (s ≫ j.hom.hom) ≫ T.inclusion.hom.hom
    have hact : g * rootPoint x R a * g⁻¹ = rootPoint x R (characterValue α R (s ≫ j.hom.hom) * a) :=
      hx R (s ≫ j.hom.hom) a
    rw [hval, one_mul, ht] at hact
    have he : j.hom.hom ≫ T.inclusion.hom.hom = S.inclusion.hom.hom := congrArg
      (fun f : S.group ⟶ G ↦ f.hom.hom) hj
    have hg : g = s ≫ S.inclusion.hom.hom := by
      dsimp only [g]
      rw [Category.assoc, he]
    rw [hg] at hact
    change Commute (t ≫ x.hom.hom) (s ≫ S.inclusion.hom.hom)
    exact (mul_inv_eq_iff_eq_mul.mp hact).symm
  obtain ⟨f, hf⟩ := (hC _ _).mp h
  exact factor_group_through_subgroup C x f hf

end Centralizer

section RankOneSquares

open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot SplitBorelPair IsSimple)
open Specs.NormalizerComparison (SimpleRepresentative)
open Specs.RankTwoLifting (Compatible)
open Specs.RootGroups (AdditiveLine CorootReflection)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.SimpleRoots (IsBaseFor evaluate)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open Specs.AdjointRepresentation (GroupPoints)
open private word_one_square torusPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem regular_positive_system_of_attached (P : SplitBorelPair k) (D : AttachedDatum P) :
    letI := D.comm
    ∃ c : Cocharacter P.T.group, IsRegular P.T c ∧ positiveRoots P.T c = subgroupRoots P.T P.B ∧
      IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  obtain ⟨c, _, hreg, _, hc⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let f := evaluate D.datum c
  have hf (i : Root P.T) : f (D.datum.rootDatum.root i) = CharacterPairing.pairing P.T.group i.val c := by
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.datum.rootDatum f (fun i ↦ hf i ▸ hreg i)
  have hpos : SimpleRoots.positive D.datum.rootDatum f = subgroupRoots P.T P.B := by
    rw [hc]
    ext i
    change 0 < f (D.datum.rootDatum.root i) ↔ 0 < CharacterPairing.pairing P.T.group i.val c
    rw [hf]
  have hsupport : b.support = D.base.support := by
    ext i
    rw [hb.simple_iff, hpos, D.simple_iff]
    unfold IsSimple
    simp only [D.datum.root_eq]
    rfl
  have eq_base {P : SplitBorelPair k} [IsCommMonObj P.T.group.X] {d : AbstractPairing.Datum P.T}
      (b₁ b₂ : d.rootDatum.Base) (h : b₁.support = b₂.support) : b₁ = b₂ := by
    cases b₁
    cases b₂
    cases h
    rfl
  exact ⟨c, hreg, hc.symm, eq_base _ _ hsupport ▸ hb⟩

private def rationalCorootValue {T : GroupScheme k} (c : Cocharacter T) :
    𝟙_ (SchemeOver k) ⟶ T.X := (groundIso (k := k)).inv ≫ cocharacterPoint c (CommAlgCat.of k k) (-1)

set_option backward.isDefEq.respectTransparency false in
private theorem representative_square {G : GroupScheme k} {T : ClosedSubgroup G}
    {α : Character T.group} {x y : A.group ⟶ G} (r : CorootReflection T α x y) :
    r.representative ^ 2 = rationalCorootValue r.coroot ≫ T.inclusion.hom.hom := by
  let e := groundIso (k := k)
  have he := word_one_square r (CommAlgCat.of k k)
  rw [torusPointHom_apply, ← r.representative_word, pow_two] at he
  let U := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  change (toUnit U ≫ r.representative) * (toUnit U ≫ r.representative) =
    cocharacterPoint r.coroot (CommAlgCat.of k k) (-1) ≫ T.inclusion.hom.hom at he
  have hv := congrArg (fun x : U ⟶ G.X ↦ e.inv ≫ x) he
  have hc : e.inv ≫ toUnit U ≫ r.representative = r.representative := by
    rw [← Category.assoc, comp_toUnit]
    have hid : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
    rw [hid, Category.id_comp]
  rw [MonObj.comp_mul, hc, ← Category.assoc] at hv
  exact (pow_two _).trans hv

private theorem compatible_simple_squares {P Q : PinnedGroup A}
    {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}
    (h : Compatible P Q D E d τ) (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair)
    (hj : d i.val = j.val) (n : SimpleRepresentative P D i) (m : SimpleRepresentative Q E j) :
    ∃ t : 𝟙_ (SchemeOver k) ⟶ P.pair.T.group.X,
      n.reflection.representative * n.reflection.representative = t ≫ P.pair.T.inclusion.hom.hom ∧
      m.reflection.representative * m.reflection.representative = t ≫ (τ ≫ Q.pair.T.inclusion).hom.hom := by
  have hcore : n.reflection.coroot ≫ τ = m.reflection.coroot := by
    rw [n.coroot_eq, m.coroot_eq]
    simpa only [hj] using h.coroot i.val
  let t := rationalCorootValue n.reflection.coroot
  refine ⟨t, ?_, ?_⟩
  · simpa only [pow_two] using representative_square n.reflection
  · rw [← pow_two, representative_square m.reflection, ← hcore]
    let v : (testSpec k).obj (Opposite.op (CommAlgCat.of k k)) ⟶
        (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X :=
      CocharacterDynamics.unitPoint (CommAlgCat.of k k) (-1)
    change (groundIso (k := k)).inv ≫ (v ≫ (n.reflection.coroot ≫ τ).hom.hom) ≫
      Q.pair.T.inclusion.hom.hom =
      ((groundIso (k := k)).inv ≫ (v ≫ n.reflection.coroot.hom.hom)) ≫
        (τ ≫ Q.pair.T.inclusion).hom.hom
    simp only [Grp.comp_hom_hom, Category.assoc]

end RankOneSquares

section StandardLevi

open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.Pinning (SplitBorelPair AttachedDatum IsSimple)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.SimpleRoots (evaluate)
open Specs.StandardParabolicLevi (StandardParabolic)

variable {k : Type u} [Field k]

/-- The standard Levi theorem supplies the face of the given attached datum,
with its full torus and its actual roots. -/
private theorem standard_levi_for_attached (P : SplitBorelPair k) (D : AttachedDatum P) :
    letI := D.comm
    ∀ I : Set (Root P.T), I ⊆ D.base.support →
      ∃ U : RootSubgroupFamily P.T, Nonempty (StandardParabolic P.B D.datum D.base U I) := by
  intro I hI
  obtain ⟨hcomm', h⟩ := Flag.StandardParabolicLevi.standardParabolicLevi P.G P.reductive P.T P.B
    P.split P.maximal P.borel P.containsTorus
  letI := hcomm'
  obtain ⟨D₀, W, U, c, b, hreg, hc, hb, hstandard⟩ := h
  have hcoroot (i : Root P.T) : D₀.rootDatum.coroot i = D.datum.rootDatum.coroot i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr⟩ := D₀.attached i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s, hs⟩ := D.datum.attached i
    apply Additive.toMul.injective
    rw [← hr, ← hs]
    exact coroot_eq_of_linked_coordinates W.image W.representsNormalizer D₀ r s
  have hdatum := datum_eq_of_coroots D₀ D.datum hcoroot
  subst D₀
  have hf (i : Root P.T) : evaluate D.datum c (D.datum.rootDatum.root i) = CharacterPairing.pairing P.T.group i.val c := by
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  have hpos : SimpleRoots.positive D.datum.rootDatum (evaluate D.datum c) = subgroupRoots P.T P.B := by
    rw [← hc]
    ext i
    change 0 < evaluate D.datum c (D.datum.rootDatum.root i) ↔ 0 < CharacterPairing.pairing P.T.group i.val c
    rw [hf]
  have hsupport : b.support = D.base.support := by
    ext i
    rw [hb.simple_iff, hpos, D.simple_iff]
    unfold IsSimple
    simp only [D.datum.root_eq]
    rfl
  have eq_base {P : SplitBorelPair k} [IsCommMonObj P.T.group.X] {d : AbstractPairing.Datum P.T}
      (b₁ b₂ : d.rootDatum.Base) (h : b₁.support = b₂.support) : b₁ = b₂ := by
    cases b₁
    cases b₂
    cases h
    rfl
  have he : b = D.base := eq_base _ _ hsupport
  subst b
  obtain ⟨C, _⟩ := hstandard I hI
  exact ⟨U, ⟨C⟩⟩

open Specs.CharacterDescent (Cocharacter compositionPairing)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.BorelsAndChambers (IsRegular)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.StandardParabolicLevi (leviRoots)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

/-- The roots of the Levi are the ambient roots in the selected span,
with characters transported along the full torus isomorphism. -/
private noncomputable def rootsOfLevi (P : SplitBorelPair k) (D : AttachedDatum P)
    [IsCommMonObj P.T.group.X] {U : RootSubgroupFamily P.T} {I : Set (Root P.T)}
    (L : StandardParabolic P.B D.datum D.base U I) :
    {i : Root P.T // i ∈ leviRoots D.datum I} ≃ Root (G := closedSubgroupAlgebraicGroup L.limitGroups.centralizer) L.leviTorus := by
  let f (i : {i : Root P.T // i ∈ leviRoots D.datum I}) : Root (G := closedSubgroupAlgebraicGroup L.limitGroups.centralizer) L.leviTorus :=
    ⟨L.torusIso.inv ≫ i.val.val, (congrArg (fun R ↦ (L.torusIso.inv ≫ i.val.val) ∈ R)
      L.leviRoots_eq).mpr ⟨i.val, i.property, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    apply Subtype.ext
    apply Subtype.ext
    exact (cancel_epi L.torusIso.inv).mp (congrArg Subtype.val h)
  · intro j
    obtain ⟨i, hi, h⟩ := (congrArg (fun R ↦ j.val ∈ R) L.leviRoots_eq).mp j.property
    exact ⟨⟨i, hi⟩, Subtype.ext h⟩

/-- The ambient regular cocharacter selects the inherited positive system
on the Levi, with the entire same torus transported by the specified isomorphism. -/
private theorem levi_borel_for_regular_cocharacter (P : SplitBorelPair k) (D : AttachedDatum P)
    [IsCommMonObj P.T.group.X] {U : RootSubgroupFamily P.T} {I : Set (Root P.T)}
    (L : StandardParabolic P.B D.datum D.base U I) (c : Cocharacter P.T.group)
    (hc : IsRegular P.T c) :
    ∃ B : ClosedSubgroup L.limitGroups.centralizer.group,
      IsKBorel B ∧ IsSubgroupOf L.leviTorus B ∧
      subgroupRoots L.leviTorus B = positiveRoots L.leviTorus (c ≫ L.torusIso.hom) := by
  let G := closedSubgroupAlgebraicGroup L.limitGroups.centralizer
  have hT : IsSplitTorus L.leviTorus.group := by
    obtain ⟨r, ⟨e⟩⟩ := P.split
    exact ⟨r, ⟨L.torusIso.symm ≪≫ e⟩⟩
  have hreg : IsRegular L.leviTorus (c ≫ L.torusIso.hom) := by
    intro α
    have hα := (congrArg (fun roots ↦ α.val ∈ roots) L.leviRoots_eq).mp α.property
    obtain ⟨i, _, hi⟩ := hα
    have hv : CharacterPairing.pairing L.leviTorus.group α.val (c ≫ L.torusIso.hom) = CharacterPairing.pairing P.T.group i.val c := by
      rw [← hi]
      unfold CharacterPairing.pairing compositionPairing
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hv ▸ hc i
  let S := positiveRoots L.leviTorus (c ≫ L.torusIso.hom)
  have hpos := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G L.leviSplit.1
    L.leviTorus hT L.leviTorusMaximal S).mpr ⟨c ≫ L.torusIso.hom, hreg, rfl⟩
  obtain ⟨B, hB, hTB, hroots, _⟩ :=
    ((RootData.BorelsAndChambers.borelsThroughT G L.leviSplit.1 L.leviTorus hT
      L.leviTorusMaximal).2 S).mp hpos
  exact ⟨B, hB, hTB, hroots⟩

end StandardLevi


section Transport
set_option backward.isDefEq.respectTransparency false

open Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction rankOneWord rootPoint)
open LinearAlgebraicGroups.RootData.RootGroups (corootReflection_of_word)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private rootPoint_comp normalizes_of_point_conjugation
  tangent_weight_of_scalarAction hom_ext_on_affine_tests
  rankOneRepresentative rankOneRepresentative_point rankOneWord_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private cocharacterPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private unitEquiv unitEquiv_unitPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {k : Type u} [Field k] {A : AdditiveLine k}
variable {G H : GroupScheme k} {T : ClosedSubgroup G} {S : ClosedSubgroup H}

private theorem pairing_comp {T S : GroupScheme k} (τ : T ⟶ S) (χ : Character S)
    (c : Cocharacter T) :
    CharacterPairing.pairing T (τ ≫ χ) c = CharacterPairing.pairing S χ (c ≫ τ) := by
  unfold CharacterPairing.pairing compositionPairing
  rw [Category.assoc]

private theorem scalar_action_along_iso (f : G ⟶ H) (e : T.group ≅ S.group)
    (he : T.inclusion ≫ f = e.hom ≫ S.inclusion)
    (β : Character S.group) (x : A.group ⟶ G)
    (hx : HasScalarAction T (e.hom ≫ β) x) :
    HasScalarAction S β (x ≫ f) := by
  intro R t a
  let F := (((groupPointsFunctor k).map f).app R).hom
  let z : GroupPoints T.group R := t ≫ e.inv.hom.hom
  have hz : z ≫ e.hom.hom.hom = t := by
    change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = t
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    exact Category.comp_id t
  have h := congrArg F (hx R z a)
  rw [map_mul, map_mul, map_inv] at h
  have ht : F (z ≫ T.inclusion.hom.hom) = t ≫ S.inclusion.hom.hom := by
    change (z ≫ T.inclusion.hom.hom) ≫ f.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, he, Grp.comp_hom_hom, ← Category.assoc, hz]
  have heval : z ≫ (e.hom ≫ β).hom.hom = t ≫ β.hom.hom := by
    rw [Grp.comp_hom_hom, ← Category.assoc, hz]
  have hval : characterValue (e.hom ≫ β) R z = characterValue β R t := by
    unfold characterValue
    rw [heval]
  have hf (b : R) : F (rootPoint x R b) = rootPoint (x ≫ f) R b :=
    (rootPoint_comp x f R b).symm
  rw [ht, hval, hf, hf] at h
  exact h

private theorem pullback_inverse_character {T S : GroupScheme k} (τ : T ⟶ S) (β : Character S) :
    τ ≫ β⁻¹ = (τ ≫ β)⁻¹ :=
  map_inv (Specs.CellHomomorphism.pullbackCharacters τ) β

private theorem root_of_scalar_action (U : ClosedSubgroup G)
    (α : Character T.group) (x : A.group ≅ U.group)
    (hU : Smooth U.group.X.hom) (hadd : Specs.RankOneFlag.IsSplitAdditive U.group)
    (hx : HasScalarAction T α (x.hom ≫ U.inclusion)) : Specs.RootGroups.IsRootSubgroup T U α := by
  refine ⟨hU, hadd, normalizes_of_point_conjugation T U ?_,
    tangent_weight_of_scalarAction T U α A x hx⟩
  intro R t p
  obtain ⟨a, rfl⟩ := rootPoint_surjective x R p
  refine ⟨rootPoint x.hom R (characterValue α R t * a), ?_⟩
  simpa only [← rootPoint_comp] using (hx R t a).symm

private theorem rational_word_at_one {α : Character T.group} {x y : A.group ⟶ G}
    (r : CorootReflection T α x y) : r.representative = rankOneRepresentative x y := by
  letI := (groundIso (k := k)).isIso_hom
  apply (cancel_epi (groundIso (k := k)).hom).mp
  rw [toUnit_unique (groundIso (k := k)).hom (toUnit _)]
  exact r.representative_word.trans (rankOneRepresentative_point x y _).symm

private theorem map_coroot_word (f : G ⟶ H) (τ : T.group ⟶ S.group)
    (hT : T.inclusion ≫ f = τ ≫ S.inclusion)
    {α : Character T.group} {x y : A.group ⟶ G}
    (r : CorootReflection T α x y) (R : TestAlgebra k) (b : Rˣ) :
    cocharacterPoint (r.coroot ≫ τ) R b ≫ S.inclusion.hom.hom =
      rankOneWord (x ≫ f) (y ≫ f) R b * (rankOneWord (x ≫ f) (y ≫ f) R 1)⁻¹ := by
  rw [cocharacterPoint_comp, Category.assoc, ← Grp.comp_hom_hom, ← hT,
    Grp.comp_hom_hom, ← Category.assoc, r.coroot_word R b, rankOneWord_comp,
    rankOneWord_comp, MonObj.mul_comp, GrpObj.inv_comp]

/-- The word identities determine the cocharacter and representative in the reflection. -/
private theorem reflection_of_linked_word (T : ClosedSubgroup G) (hT : IsSplitTorus T.group)
    (α : Character T.group) (x y : A.group ⟶ G)
    (hx : HasScalarAction T α x) (hy : HasScalarAction T α⁻¹ y)
    (c : Cocharacter T.group) (n : RationalPoint G)
    (hn : ∀ R : TestAlgebra k, toUnit _ ≫ n = rankOneWord x y R 1)
    (hc : ∀ (R : TestAlgebra k) (b : Rˣ),
      cocharacterPoint c R b ≫ T.inclusion.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹)
    (hp : CharacterPairing.pairing T.group α c = 2) :
    ∃ r : CorootReflection T α x y, r.coroot = c ∧ r.representative = n := by
  obtain ⟨r⟩ := corootReflection_of_word T hT α x y hx hy c n hn hc hp
  refine ⟨r, ?_, ?_⟩
  · letI := mono_over T.inclusion.hom.hom T.isClosedImmersion
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro R t
    let b := unitEquiv R t
    have ht : unitPoint R b = t := (unitEquiv R).injective (unitEquiv_unitPoint R b)
    rw [← ht]
    change cocharacterPoint r.coroot R b = cocharacterPoint c R b
    exact (cancel_mono T.inclusion.hom.hom).mp ((r.coroot_word R b).trans (hc R b).symm)
  · letI := (groundIso (k := k)).isIso_hom
    apply (cancel_epi (groundIso (k := k)).hom).mp
    rw [toUnit_unique (groundIso (k := k)).hom (toUnit _)]
    exact r.representative_word.trans (hn (CommAlgCat.of k k)).symm

/-- Transport the linked word with its coroot through a commutative torus diagram. -/
private theorem map_linked_reflection (f : G ⟶ H) (τ : T.group ⟶ S.group)
    (hT : T.inclusion ≫ f = τ ≫ S.inclusion) (hS : IsSplitTorus S.group)
    {α : Character T.group} {β : Character S.group} (hα : τ ≫ β = α)
    {x y : A.group ⟶ G} (r : CorootReflection T α x y)
    (hx : HasScalarAction S β (x ≫ f)) (hy : HasScalarAction S β⁻¹ (y ≫ f)) :
    ∃ s : CorootReflection S β (x ≫ f) (y ≫ f),
      s.coroot = r.coroot ≫ τ ∧ s.representative = sectionMap f _ r.representative := by
  have hn (R : TestAlgebra k) : toUnit _ ≫ sectionMap f _ r.representative =
      rankOneWord (x ≫ f) (y ≫ f) R 1 := by
    rw [rankOneWord_comp]
    change toUnit _ ≫ r.representative ≫ f.hom.hom = _
    rw [← Category.assoc, rational_word_at_one r, rankOneRepresentative_point x y R]
  have hp : CharacterPairing.pairing S.group β (r.coroot ≫ τ) = 2 := by
    rw [← pairing_comp, hα, r.root_pairing]
  exact reflection_of_linked_word S hS β (x ≫ f) (y ≫ f) hx hy
    (r.coroot ≫ τ) (sectionMap f _ r.representative) hn (map_coroot_word f τ hT r) hp

/-- Restrict a linked pair to a subgroup containing its two root coordinates and the torus. -/
private theorem restrict_linked_reflection (f : G ⟶ H) [Mono f.hom.hom]
    (e : T.group ≅ S.group) (he : T.inclusion ≫ f = e.hom ≫ S.inclusion)
    (hT : IsSplitTorus T.group) {α : Character T.group} {β : Character S.group}
    (hα : e.hom ≫ β = α) {x y : A.group ⟶ G} {x' y' : A.group ⟶ H}
    (r : CorootReflection S β x' y') (hxmap : x ≫ f = x') (hymap : y ≫ f = y')
    (hx : HasScalarAction T α x) (hy : HasScalarAction T α⁻¹ y) :
    ∃ s : CorootReflection T α x y,
      s.coroot = r.coroot ≫ e.inv ∧ sectionMap f _ s.representative = r.representative := by
  have hcomm : S.inclusion = e.inv ≫ T.inclusion ≫ f := by
    rw [he, Iso.inv_hom_id_assoc]
  have hword (R : TestAlgebra k) (b : Rˣ) :
      cocharacterPoint (r.coroot ≫ e.inv) R b ≫ T.inclusion.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by
    apply (cancel_mono f.hom.hom).mp
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← rankOneWord_comp, ← rankOneWord_comp,
      cocharacterPoint_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom T.inclusion f,
      ← Grp.comp_hom_hom e.inv (T.inclusion ≫ f), ← hcomm, r.coroot_word, hxmap, hymap]
  have hp : CharacterPairing.pairing T.group α (r.coroot ≫ e.inv) = 2 := by
    rw [← hα, pairing_comp, Category.assoc, e.inv_hom_id, Category.comp_id, r.root_pairing]
  obtain ⟨s, hsc, _⟩ := reflection_of_linked_word T hT α x y hx hy
    (r.coroot ≫ e.inv) (rankOneRepresentative x y) (rankOneRepresentative_point x y) hword hp
  refine ⟨s, hsc, ?_⟩
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (op R)
  have hs_word : toUnit Y ≫ s.representative = rankOneWord x y R 1 := s.representative_word
  have hr_word : toUnit Y ≫ r.representative = rankOneWord x' y' R 1 := r.representative_word
  letI := (groundIso (k := k)).isIso_hom
  apply (cancel_epi (groundIso (k := k)).hom).mp
  rw [toUnit_unique (groundIso (k := k)).hom (toUnit _)]
  change toUnit Y ≫ s.representative ≫ f.hom.hom = toUnit Y ≫ r.representative
  rw [← Category.assoc, hs_word, hr_word, ← rankOneWord_comp, hxmap, hymap]

end Transport


section LeviPinnings

open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot SplitBorelPair IsSimple RootCoordinate)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.BorelsAndChambers (subgroupRoots positiveRoots)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.RootGroups (AdditiveLine HasScalarAction)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.StandardParabolicLevi (StandardParabolic leviRoots)
open Specs.SimpleRoots (evaluate)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.DatumAndWeyl (Identification)
open Specs.CellHomomorphism (pullbackCharacters)

open private scalar_action_of_normalized_tangent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private evaluate_root from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private linked_coroot from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
open private same_subgroup_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k] {A : AdditiveLine k}

private abbrev faceRoots (P : SplitBorelPair k) (D : AttachedDatum P)
    (I : Set (Root P.T)) :=
  letI := D.comm
  {i : Root P.T // i ∈ leviRoots D.datum I}

private def attachedCoroot {P : SplitBorelPair k} (D : AttachedDatum P) (i : Root P.T) :
    Cocharacter P.T.group :=
  letI := D.comm
  Additive.toMul (D.datum.rootDatum.coroot i)

/-- The pinned face centralizer with its full torus and the inherited data. -/
private structure PinnedLevi (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (I : Set (Root P.pair.T)) where
  pinned : PinnedGroup A
  datum : AttachedDatum pinned.pair
  inclusion : pinned.pair.G.val ⟶ P.pair.G.val
  mono : Mono inclusion.hom.hom
  torus : P.pair.T.group ≅ pinned.pair.T.group
  torusInclusion : torus.hom ≫ pinned.pair.T.inclusion ≫ inclusion = P.pair.T.inclusion
  rootIndex : Root pinned.pair.T ≃ faceRoots P.pair D I
  root_eq : ∀ i, torus.hom ≫ i.val = (rootIndex i).val.val
  simple_iff : ∀ i, IsSimple pinned.pair i ↔ (rootIndex i).val ∈ I
  coroot_eq : ∀ i, attachedCoroot D (rootIndex i).val ≫ torus.hom = attachedCoroot datum i
  rootIso : ∀ i, {e : (pinned.roots i).val.group ≅ (P.roots (rootIndex i).val).val.group //
    (pinned.roots i).val.inclusion ≫ inclusion = e.hom ≫ (P.roots (rootIndex i).val).val.inclusion}
  pin_eq : ∀ (i : SimpleRoot pinned.pair) (j : SimpleRoot P.pair), (rootIndex i.val).val = j.val →
    ((pinned.pin i).val.hom ≫ (pinned.roots i.val).val.inclusion) ≫ inclusion =
      (P.pin j).val.hom ≫ (P.roots j.val).val.inclusion

private theorem PinnedLevi.inclusion_torus {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {I : Set (Root P.pair.T)} (L : PinnedLevi P D I) :
    L.pinned.pair.T.inclusion ≫ L.inclusion = L.torus.inv ≫ P.pair.T.inclusion := by
  rw [← L.torusInclusion, Iso.inv_hom_id_assoc]

private theorem simple_in_levi (P K : SplitBorelPair k) (D : AttachedDatum P)
    [IsCommMonObj P.T.group.X]
    {I : Set (Root P.T)} (hI : I ⊆ D.base.support)
    (e : P.T.group ≅ K.T.group) (z : Root K.T ≃ faceRoots P D I)
    (hz : ∀ j, e.hom ≫ j.val = (z j).val.val)
    (hpos : ∀ j, j ∈ subgroupRoots K.T K.B ↔ D.base.IsPos (z j).val)
    (f : Additive (Character P.T.group) →ₗ[ℤ] ℤ)
    (hf : ∀ j : Root P.T, f (D.datum.rootDatum.root j) = 0 ↔ j ∈ leviRoots D.datum I)
    (hzero : ∀ j ∈ I, f (D.datum.rootDatum.root j) = 0)
    (hposf : ∀ j ∈ (D.base.support : Set (Root P.T)) \ I, 0 < f (D.datum.rootDatum.root j))
    (j : Root K.T) : IsSimple K j ↔ (z j).val ∈ I := by
  have hnonneg (i : D.base.support) : 0 ≤ f (D.datum.rootDatum.root i) := by
    by_cases h : i.val ∈ I
    · rw [hzero _ h]
    · exact (hposf _ ⟨i.property, h⟩).le
  have hsub : (z j).val ∈ D.base.support ↔ (z j).val ∈ I := by
    refine ⟨fun hj ↦ ?_, fun hj ↦ hI hj⟩
    by_contra hn
    exact (hposf _ ⟨hj, hn⟩).ne' ((hf _).mpr (z j).property)
  have hsum (i l : Root K.T) :
      j.val = i.val * l.val ↔
        D.datum.rootDatum.root (z j).val =
          D.datum.rootDatum.root (z i).val + D.datum.rootDatum.root (z l).val := by
    simp only [D.datum.root_eq, ← ofMul_mul, Additive.ofMul.injective.eq_iff]
    rw [← hz j, ← hz i, ← hz l]
    change j.val = i.val * l.val ↔
      pullbackCharacters e.hom j.val =
        pullbackCharacters e.hom i.val * pullbackCharacters e.hom l.val
    rw [← map_mul]
    exact ⟨congrArg _, (cancel_epi e.hom).mp⟩
  letI : Finite (Root P.T) := D.datum.finiteRoots
  rw [← hsub, ← simple_on_face_iff D.datum.rootDatum D.base f hnonneg _ ((hf _).mpr (z j).property)]
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨(hpos j).mp hj, ?_⟩
    intro i l hi hl hif hlf
    let a : faceRoots P D I := ⟨i, (hf i).mp hif⟩
    let b : faceRoots P D I := ⟨l, (hf l).mp hlf⟩
    have ha : (z (z.symm a)).val = i := congrArg Subtype.val (z.apply_symm_apply a)
    have hb : (z (z.symm b)).val = l := congrArg Subtype.val (z.apply_symm_apply b)
    have h' := (hsum (z.symm a) (z.symm b)).not.mp
      (h _ ((hpos _).mpr (ha.symm ▸ hi)) _ ((hpos _).mpr (hb.symm ▸ hl)))
    simpa only [ha, hb] using h'
  · rintro ⟨hj, h⟩
    exact ⟨(hpos _).mpr hj, fun i hi l hl ↦ (hsum i l).not.mpr
      (h _ _ ((hpos _).mp hi) ((hpos _).mp hl) ((hf _).mpr (z i).property) ((hf _).mpr (z l).property))⟩

private theorem lift_pinning_to_levi (P : PinnedGroup A) (D : AttachedDatum P.pair)
    [IsCommMonObj P.pair.T.group.X] (I : Set (Root P.pair.T))
    (hI : I ⊆ D.base.support) : Nonempty (PinnedLevi P D I) := by
  classical
  obtain ⟨U, ⟨L⟩⟩ := standard_levi_for_attached P.pair D I hI
  obtain ⟨c, hc, hcB, hb⟩ := regular_positive_system_of_attached P.pair D
  obtain ⟨B, hB, hTB, hBpos⟩ := levi_borel_for_regular_cocharacter P.pair D L c hc
  let C := L.limitGroups.centralizer
  let e := L.torusIso
  have hT : IsSplitTorus L.leviTorus.group := by
    obtain ⟨r, ⟨v⟩⟩ := P.pair.split
    exact ⟨r, ⟨e.symm ≪≫ v⟩⟩
  let K : SplitBorelPair k :=
    ⟨closedSubgroupAlgebraicGroup C, L.leviSplit.1, L.leviTorus, hT, L.leviTorusMaximal, B, hB, hTB⟩
  let E := Pinning.attachedDatum K
  letI := E.comm
  let z : Root K.T ≃ faceRoots P.pair D I := (rootsOfLevi P.pair D L).symm
  have hz (i : Root K.T) : e.hom ≫ i.val = (z i).val.val := by
    have hi : i.val = e.inv ≫ (z i).val.val :=
      congrArg Subtype.val ((rootsOfLevi P.pair D L).apply_symm_apply i).symm
    rw [hi, Iso.hom_inv_id_assoc]
  have htorus : K.T.inclusion ≫ C.inclusion = e.inv ≫ P.pair.T.inclusion := by
    calc
      _ = e.inv ≫ (e.hom ≫ L.leviTorus.inclusion ≫ C.inclusion) :=
        (Iso.inv_hom_id_assoc e _).symm
      _ = _ := congrArg (fun f : P.pair.T.group ⟶ P.pair.G.val ↦ e.inv ≫ f) L.torusInclusion
  have hpos (j : Root K.T) : j ∈ subgroupRoots K.T K.B ↔ D.base.IsPos (z j).val := by
    change j ∈ subgroupRoots L.leviTorus B ↔ _
    rw [hBpos]
    change 0 < CharacterPairing.pairing K.T.group j.val (c ≫ e.hom) ↔ _
    rw [← pairing_comp, hz, hb.positive_iff]
    change 0 < CharacterPairing.pairing P.pair.T.group (z j).val.val c ↔
      0 < evaluate D.datum c (D.datum.rootDatum.root (z j).val)
    rw [evaluate_root]
  have hsimple := simple_in_levi P.pair K D hI e z hz hpos (evaluate D.datum L.cocharacter)
    (fun j ↦ by
      rw [evaluate_root]
      exact (Flag.StandardParabolicLevi.face_root_signs hcB hb L.face j).1)
    (fun j hj ↦ (evaluate_root D.datum _ j).trans (L.face.1 j hj))
    (fun j hj ↦ by rw [evaluate_root]; exact L.face.2 j hj)
  obtain ⟨V, _⟩ := Pinning.pinningsExist A K
  have root_iso (i : Root K.T) :
      Nonempty {v : (V i).val.group ≅ (P.roots (z i).val).val.group //
        (V i).val.inclusion ≫ C.inclusion = v.hom ≫ (P.roots (z i).val).val.inclusion} := by
    let U' := subgroupOfSubgroup C (V i).val
    obtain ⟨ops, hd, he, hi, ⟨v⟩⟩ := (V i).property.2.1
    let A' : AdditiveLine k := ⟨ops, hd, he, hi⟩
    let v' : A'.group ≅ (V i).val.group := v.symm
    have hact := scalar_action_of_normalized_tangent K.T (V i).val K.split i.val (V i).property A' v'
    have hact' : HasScalarAction P.pair.T (z i).val.val (v'.hom ≫ U'.inclusion) := by
      have hχ : e.inv ≫ (z i).val.val = i.val := by rw [← hz i, Iso.inv_hom_id_assoc]
      let x := v'.hom ≫ (V i).val.inclusion
      have hx : HasScalarAction K.T (e.inv ≫ (z i).val.val) x :=
        (congrArg (fun χ ↦ HasScalarAction K.T χ x) hχ).mpr hact
      change HasScalarAction P.pair.T (z i).val.val
        (v'.hom ≫ ((V i).val.inclusion ≫ C.inclusion))
      have hcomp : x ≫ C.inclusion = v'.hom ≫ ((V i).val.inclusion ≫ C.inclusion) :=
        Category.assoc _ _ _
      exact (congrArg (fun f ↦ HasScalarAction P.pair.T (z i).val.val f) hcomp).mp
        (scalar_action_along_iso C.inclusion e.symm htorus (z i).val.val x hx)
    have hU' := root_of_scalar_action U' (z i).val.val v' (V i).property.1
      (V i).property.2.1 hact'
    obtain ⟨_, _, _, _, _, hu⟩ := ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive
      P.pair.T P.pair.split P.pair.maximal).2 _ (z i).val.property).2.2
    have h₁ := hu U' hU'
    have h₂ := hu (P.roots (z i).val).val (P.roots (z i).val).property
    let v := subgroupIso (same_subgroup_trans ⟨h₁.2, h₁.1⟩ h₂)
    exact ⟨⟨v.val, v.property.symm⟩⟩
  let v (i : Root K.T) := Classical.choice (root_iso i)
  let g (i : SimpleRoot K) : SimpleRoot P.pair :=
    ⟨(z i.val).val, (D.simple_iff _).mp (hI ((hsimple i.val).mp i.property))⟩
  let x (i : SimpleRoot K) := (P.pin (g i)).val ≪≫ (v i.val).val.symm
  let p (i : SimpleRoot K) : RootCoordinate A K.T (V i.val).val i.val.val :=
    ⟨x i, scalar_action_of_normalized_tangent K.T (V i.val).val K.split i.val.val
      (V i.val).property A (x i)⟩
  let P' : PinnedGroup A := ⟨K, V, p⟩
  have hcoroot (i : Root K.T) : attachedCoroot D (z i).val ≫ e.hom = attachedCoroot E i := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂, r, hr⟩ := E.datum.attached i
    have hχ : e.inv ≫ (z i).val.val = i.val := by rw [← hz i, Iso.inv_hom_id_assoc]
    have hχ' : e.inv ≫ (z i).val.val⁻¹ = i.val⁻¹ := by
      rw [pullback_inverse_character, hχ]
    obtain ⟨r', hc', _⟩ := map_linked_reflection C.inclusion e.inv htorus P.pair.split hχ r
      (scalar_action_along_iso C.inclusion e.symm htorus _ _ (hχ.symm ▸ h₁))
      (scalar_action_along_iso C.inclusion e.symm htorus _ _ (hχ'.symm ▸ h₂))
    have heq := linked_coroot D.datum (z i).val r'
    change r'.coroot = attachedCoroot D (z i).val at heq
    change r.coroot = attachedCoroot E i at hr
    rw [hc', hr] at heq
    rw [← heq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨⟨P', E, C.inclusion, mono_over _ C.isClosedImmersion, e, L.torusInclusion,
    z, hz, hsimple, hcoroot, v, ?_⟩⟩
  intro i j hj
  have hg : g i = j := Subtype.ext hj
  change (x i).hom ≫ ((V i.val).val.inclusion ≫ C.inclusion) =
    (P.pin j).val.hom ≫ (P.roots j.val).val.inclusion
  rw [(v i.val).property]
  simp only [x, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  subst j
  rfl

end LeviPinnings


section LinkedRepresentatives

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.NormalizerComparison (SimpleRepresentative)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.RankTwoLifting (Compatible)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics
  (oppositeCocharacter oppositeLimit_intersection_onPoints)

open private linked_coroot oppositeRoot oppositeRoot_val
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
open private quotientLabel quotientLabel_spec quotientLabel_conjugates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
open private inducedConjugation_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private opposite_pairing point_onTorus_hasLimit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoRelations
open private rootPoint_contraction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}

private theorem simple_representatives_exist (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    Nonempty (∀ i : SimpleRoot P.pair, SimpleRepresentative P D i) := by
  letI := D.comm
  have hex (i : SimpleRoot P.pair) : Nonempty (SimpleRepresentative P D i) := by
    let β := oppositeRoot D.datum i.val
    have hβ := oppositeRoot_val D.datum i.val
    obtain ⟨y, ⟨r⟩⟩ := RankTwoRelations.linkedOppositeCoordinate P i.val β hβ (P.pin i)
    exact ⟨⟨β, hβ, y, r, linked_coroot D.datum i.val r⟩⟩
  exact ⟨fun i ↦ Classical.choice (hex i)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two linked words for the same pin and coroot have the same representative.
Their ratio belongs to the torus. After conjugation by the positive factor,
it belongs both to the positive limit parabolic and to the opposite contracting subgroup. -/
private theorem linked_representative_eq (D : AttachedDatum P.pair)
    (W : letI := D.comm; Identification D.datum)
    {α : Character P.pair.T.group} {x x' y z : A.group ⟶ P.pair.G.val}
    (r : CorootReflection P.pair.T α x y) (s : CorootReflection P.pair.T α x' z)
    (hpin : x = x') (hc : r.coroot = s.coroot)
    (hx : HasScalarAction P.pair.T α x)
    (hy : HasScalarAction P.pair.T α⁻¹ y) (hz : HasScalarAction P.pair.T α⁻¹ z) :
    r.representative = s.representative := by
  subst x'
  letI := D.comm
  obtain ⟨n, hn⟩ := (W.representsNormalizer _ _).mp r.normalizes
  obtain ⟨m, hm⟩ := (W.representsNormalizer _ _).mp s.normalizes
  have hn' : r.conjugation = W.image.conjugation (quotientLabel W.image n) := by
    apply inducedConjugation_unique r.conjugates
    rw [← hn]
    exact quotientLabel_conjugates W.image n
  have hm' : s.conjugation = W.image.conjugation (quotientLabel W.image m) := by
    apply inducedConjugation_unique s.conjugates
    rw [← hm]
    exact quotientLabel_conjugates W.image m
  have hlabel : quotientLabel W.image m = quotientLabel W.image n := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro χ
    rw [W.image.characterAction, W.image.characterAction, ← hm', ← hn', s.reflection,
      r.reflection, hc]
  have hq : sectionMap W.quotient _ m = sectionMap W.quotient _ n := by
    change m ≫ W.quotient.hom.hom = n ≫ W.quotient.hom.hom
    rw [quotientLabel_spec W.image m, quotientLabel_spec W.image n, hlabel]
  obtain ⟨t, ht⟩ := torus_parameter W.torusInclusion W.quotient W.isQuotient.1 _ m n hq
  have ht' : s.representative = sectionMap P.pair.T.inclusion _ t * r.representative := by
    have h := congrArg (sectionMap W.normalizer.inclusion _) ht
    rw [map_mul, ← sectionMap_comp, W.inclusion_eq] at h
    change sectionMap W.normalizer.inclusion _ m = _ at h
    rw [show sectionMap W.normalizer.inclusion _ n = r.representative from hn,
      show sectionMap W.normalizer.inclusion _ m = s.representative from hm] at h
    exact h
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  let v : GroupPoints P.pair.T.group R := toUnit Y ≫ t
  let p : GroupPoints P.pair.G.val R := rootPoint x R 1
  let a : GroupPoints P.pair.G.val R := rootPoint y R (-1)
  let b : GroupPoints P.pair.G.val R := rootPoint z R (-1)
  let t' : GroupPoints P.pair.G.val R := v ≫ P.pair.T.inclusion.hom.hom
  have hr_word : toUnit Y ≫ r.representative = rankOneWord x y R 1 := r.representative_word
  have hs_word : toUnit Y ≫ s.representative = rankOneWord x z R 1 := s.representative_word
  have hw : p * b * p = t' * (p * a * p) := by
    have h := congrArg (fun q : RationalPoint P.pair.G.val ↦ toUnit Y ≫ q) ht'
    rw [MonObj.comp_mul, hs_word, hr_word] at h
    change rankOneWord x z R 1 = t' * rankOneWord x y R 1 at h
    simpa only [rankOneWord, Units.val_one, inv_one] using h
  have hdiff : b * a⁻¹ = p⁻¹ * t' * p := by
    calc
      _ = p⁻¹ * (p * b * p) * p⁻¹ * a⁻¹ := by group
      _ = _ := by rw [hw]; group
  let c := r.coroot
  have hpos : 0 < CharacterPairing.pairing P.pair.T.group α c := by rw [show c = r.coroot from rfl, r.root_pairing]; decide
  have hneg : 0 < CharacterPairing.pairing P.pair.T.group α⁻¹ (oppositeCocharacter c) := by
    rwa [opposite_pairing P.pair.split]
  have hcontract := rootPoint_contraction hx c hpos R 1
  have htorus := point_onTorus_hasLimit P c R v
  have ha := rootPoint_contraction hy (oppositeCocharacter c) hneg R (-1)
  have hb := rootPoint_contraction hz (oppositeCocharacter c) hneg R (-1)
  have htriv : b * a⁻¹ = 1 := by
    apply oppositeLimit_intersection_onPoints P.pair.G.property.1 (c ≫ P.pair.T.inclusion)
    · rw [hdiff]
      exact ⟨_, (hcontract.inv.mul htorus).mul hcontract⟩
    · rw [show oppositeCocharacter (c ≫ P.pair.T.inclusion) =
        oppositeCocharacter c ≫ P.pair.T.inclusion by simp only [oppositeCocharacter, Category.assoc]]
      simpa only [inv_one, mul_one] using hb.mul ha.inv
  have he := mul_inv_eq_one.mp htriv
  letI := (groundIso (k := k)).isIso_hom
  apply (cancel_epi (groundIso (k := k)).hom).mp
  rw [toUnit_unique (groundIso (k := k)).hom (toUnit _)]
  change toUnit Y ≫ r.representative = toUnit Y ≫ s.representative
  rw [hr_word, hs_word]
  change p * a * p = p * b * p
  rw [he]

private theorem representative_power_in_torus (D : AttachedDatum P.pair)
    [IsCommMonObj P.pair.T.group.X] (W : Identification D.datum)
    (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i) (i j : D.base.support) :
    ∃ t : RationalPoint P.pair.T.group,
      ((n (simpleRootOfIndex D i)).reflection.representative *
        (n (simpleRootOfIndex D j)).reflection.representative) ^
        orderOf (simpleReflection D.datum.rootDatum D.base i *
          simpleReflection D.datum.rootDatum D.base j) = sectionMap P.pair.T.inclusion _ t := by
  let s := simpleReflection D.datum.rootDatum D.base
  have hlift (l : D.base.support) : ∃ a : RationalPoint W.normalizer.group,
      sectionMap W.normalizer.inclusion _ a = (n (simpleRootOfIndex D l)).reflection.representative ∧
      sectionMap W.quotient _ a = W.image.constantGroup.sectionPoint (W.labelEquiv (s l)) := by
    let r := n (simpleRootOfIndex D l)
    obtain ⟨a, ha⟩ := (W.representsNormalizer _ _).mp r.reflection.normalizes
    have hq := (quotientLabel_spec W.image a).trans (constantSection_unit _)
    exact ⟨a, ha, hq.trans (congrArg W.image.constantGroup.sectionPoint
      (representative_label D W (simpleRootOfIndex D l) r a ha _ hq))⟩
  obtain ⟨a, ha, haq⟩ := hlift i
  obtain ⟨b, hb, hbq⟩ := hlift j
  have he : sectionMap W.quotient _ ((a * b) ^ orderOf (s i * s j)) = sectionMap W.quotient _ 1 := by
    rw [map_pow, map_mul, haq, hbq, ← map_mul, ← map_mul, ← map_pow, ← map_pow,
      pow_orderOf_eq_one, map_one, map_one, map_one]
  obtain ⟨t, ht⟩ := torus_parameter W.torusInclusion W.quotient W.isQuotient.1 _ _ 1 he
  have h := congrArg (sectionMap W.normalizer.inclusion _) ht
  rw [map_pow, map_mul, ha, hb, mul_one, ← sectionMap_comp, W.inclusion_eq] at h
  exact ⟨t, h⟩

end LinkedRepresentatives


section LeviComparison

open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot IsSimple RootCoordinate)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.NormalizerComparison (SimpleRepresentative)
open Specs.RootGroups (AdditiveLine HasScalarAction CorootReflection)
open Specs.RankTwoLifting (Compatible MatchesPinning MatchesRootGroups)
open Specs.CellHomomorphism (pullbackCharacters)
open Specs.StandardParabolicLevi (leviRoots)

open private scalar_action_of_normalized_tangent from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k] {A : AdditiveLine k} {P Q : PinnedGroup A}
  {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
  {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}
  {I : Set (Root P.pair.T)}

private theorem levi_rank (L : PinnedLevi P D I) (J : Finset (Root P.pair.T))
    (hI : I = (J : Set (Root P.pair.T))) :
    letI := L.datum.comm; L.datum.base.support.card ≤ J.card := by
  letI := L.datum.comm
  let f (i : L.datum.base.support) : J :=
    ⟨(L.rootIndex i.val).val, hI ▸ (L.simple_iff i.val).mp ((L.datum.simple_iff i.val).mp i.property)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply L.rootIndex.injective
    apply Subtype.ext
    exact congrArg (fun z : J ↦ z.val) h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private theorem compatible_levis (h : Compatible P Q D E d τ)
    (L : PinnedLevi P D I) (M : PinnedLevi Q E (d '' I)) :
    ∃ e : Root L.pinned.pair.T ≃ Root M.pinned.pair.T,
      (∀ i, (M.rootIndex (e i)).val = d (L.rootIndex i).val) ∧
      Compatible L.pinned M.pinned L.datum M.datum e (L.torus.inv ≫ τ ≫ M.torus.hom) := by
  letI := D.comm
  letI := E.comm
  let hZ := (pullbackCharacters τ).toAdditive.toIntLinearMap
  have hroot (i : Root P.pair.T) :
      hZ (E.datum.rootDatum.root (d i)) = D.datum.rootDatum.root i := by
    rw [E.datum.root_eq, D.datum.root_eq]
    exact congrArg Additive.ofMul (h.root i)
  have hspan := mem_root_span_iff_of_injective D.datum.rootDatum.root E.datum.rootDatum.root
    d hZ h.injective hroot I
  let f : faceRoots P.pair D I ≃ faceRoots Q.pair E (d '' I) := d.subtypeEquiv hspan
  let e := L.rootIndex.trans (f.trans M.rootIndex.symm)
  have he (i : Root L.pinned.pair.T) :
      (M.rootIndex (e i)).val = d (L.rootIndex i).val := by
    change (M.rootIndex (M.rootIndex.symm (f (L.rootIndex i)))).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  let t := L.torus.inv ≫ τ ≫ M.torus.hom
  have hmap (a : Character M.pinned.pair.T.group) :
      pullbackCharacters t a =
        pullbackCharacters L.torus.inv (pullbackCharacters τ (pullbackCharacters M.torus.hom a)) := by
    change (L.torus.inv ≫ τ ≫ M.torus.hom) ≫ a = _
    simp only [Category.assoc]
    rfl
  have hinj : Function.Injective (pullbackCharacters t) := by
    intro a b hab
    rw [hmap, hmap] at hab
    exact (cancel_epi M.torus.hom).mp (h.injective ((cancel_epi L.torus.inv).mp hab))
  have hindex : Finite (Character L.pinned.pair.T.group ⧸ (pullbackCharacters t).range) := by
    letI := h.finiteIndex
    let g := pullbackCharacters L.torus.inv
    have hg : Function.Surjective g := by
      intro a
      refine ⟨L.torus.hom ≫ a, ?_⟩
      change L.torus.inv ≫ L.torus.hom ≫ a = a
      rw [Iso.inv_hom_id_assoc]
    have hrange : (pullbackCharacters τ).range ≤ (pullbackCharacters t).range.comap g := by
      rintro _ ⟨a, rfl⟩
      refine ⟨M.torus.inv ≫ a, ?_⟩
      rw [hmap]
      change g (pullbackCharacters τ (M.torus.hom ≫ M.torus.inv ≫ a)) = _
      rw [Iso.hom_inv_id_assoc]
    exact Finite.of_surjective _ (QuotientGroup.map_surjective_of_surjective
      (pullbackCharacters τ).range (pullbackCharacters t).range g
      (QuotientGroup.mk_surjective.comp hg) hrange)
  refine ⟨e, he, ⟨hinj, hindex, ?_, ?_, ?_⟩⟩
  · intro i
    apply (cancel_epi L.torus.hom).mp
    change L.torus.hom ≫ ((L.torus.inv ≫ τ ≫ M.torus.hom) ≫ (e i).val) =
      L.torus.hom ≫ i.val
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      M.root_eq, he, h.root, L.root_eq]
  · intro i
    change attachedCoroot L.datum i ≫ (L.torus.inv ≫ τ ≫ M.torus.hom) =
      attachedCoroot M.datum (e i)
    rw [← L.coroot_eq, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
      show attachedCoroot D (L.rootIndex i).val ≫ τ =
        attachedCoroot E (d (L.rootIndex i).val) from h.coroot _, ← he, M.coroot_eq]
  · intro i
    rw [L.datum.simple_iff, M.datum.simple_iff, L.simple_iff, M.simple_iff, he]
    exact ⟨fun hi ↦ ⟨_, hi, rfl⟩, fun ⟨_, hj, hji⟩ ↦ d.injective hji ▸ hj⟩

private theorem lift_simple_representative (L : PinnedLevi P D I)
    (i : SimpleRoot L.pinned.pair) (j : SimpleRoot P.pair) (hij : (L.rootIndex i.val).val = j.val)
    (r : SimpleRepresentative P D j) :
    ∃ (b : Root L.pinned.pair.T) (y : RootCoordinate A L.pinned.pair.T (L.pinned.roots b).val b.val)
      (s : CorootReflection L.pinned.pair.T i.val.val
        ((L.pinned.pin i).val.hom ≫ (L.pinned.roots i.val).val.inclusion)
        (y.val.hom ≫ (L.pinned.roots b).val.inclusion)),
      b.val = i.val.val⁻¹ ∧ s.coroot = attachedCoroot L.datum i.val ∧
      sectionMap L.inclusion _ s.representative = r.reflection.representative := by
  letI := D.comm
  letI := L.mono
  have hj : j.val ∈ I := hij ▸ (L.simple_iff i.val).mp i.property
  have hopp : r.opposite ∈ leviRoots D.datum I := by
    have hneg : D.datum.rootDatum.root r.opposite = -D.datum.rootDatum.root j.val := by
      rw [D.datum.root_eq, D.datum.root_eq, r.opposite_eq]
      rfl
    change D.datum.rootDatum.root r.opposite ∈ Submodule.span ℤ (D.datum.rootDatum.root '' I)
    rw [hneg]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, hj, rfl⟩)
  let a : faceRoots P.pair D I := ⟨r.opposite, hopp⟩
  let b := L.rootIndex.symm a
  have hb' : (L.rootIndex b).val = r.opposite := congrArg Subtype.val (L.rootIndex.apply_symm_apply a)
  have hα : L.torus.hom ≫ i.val.val = j.val.val := (L.root_eq i.val).trans (congrArg Subtype.val hij)
  have hχ : L.torus.inv ≫ j.val.val = i.val.val := by rw [← hα, Iso.inv_hom_id_assoc]
  have hb : b.val = i.val.val⁻¹ := by
    apply (cancel_epi L.torus.hom).mp
    rw [L.root_eq, hb', r.opposite_eq, pullback_inverse_character, hα]
  obtain ⟨v, hv⟩ : ∃ v : (L.pinned.roots b).val.group ≅ (P.roots r.opposite).val.group,
      (L.pinned.roots b).val.inclusion ≫ L.inclusion = v.hom ≫ (P.roots r.opposite).val.inclusion := by
    rw [← hb']
    exact ⟨(L.rootIso b).val, (L.rootIso b).property⟩
  let y : RootCoordinate A L.pinned.pair.T (L.pinned.roots b).val b.val :=
    ⟨r.negative.val ≪≫ v.symm, scalar_action_of_normalized_tangent _ _ L.pinned.pair.split _
      (L.pinned.roots b).property _ _⟩
  let x' := (L.pinned.pin i).val.hom ≫ (L.pinned.roots i.val).val.inclusion
  let y' := y.val.hom ≫ (L.pinned.roots b).val.inclusion
  have heq : y' ≫ L.inclusion = r.negative.val.hom ≫ (P.roots r.opposite).val.inclusion := by
    simp only [y', y, Iso.trans_hom, Iso.symm_hom, Category.assoc, hv, Iso.inv_hom_id_assoc]
  obtain ⟨s, hs, hsr⟩ := restrict_linked_reflection L.inclusion L.torus.symm L.inclusion_torus
    L.pinned.pair.split hχ r.reflection (show x' ≫ L.inclusion = _ from L.pin_eq i j hij) heq
    (L.pinned.pin i).property (by rw [← hb]; exact y.property)
  refine ⟨b, y, s, hb, ?_, hsr⟩
  rw [hs, r.coroot_eq]
  change attachedCoroot D j.val ≫ L.torus.hom = attachedCoroot L.datum i.val
  rw [← hij, L.coroot_eq]

private theorem match_levi_representative (H : Compatible P Q D E d τ)
    (L : PinnedLevi P D I) (M : PinnedLevi Q E (d '' I))
    (W : letI := E.comm; Identification E.datum)
    (e : Root L.pinned.pair.T ≃ Root M.pinned.pair.T)
    (he : ∀ i, (M.rootIndex (e i)).val = d (L.rootIndex i).val)
    (h : Compatible L.pinned M.pinned L.datum M.datum e (L.torus.inv ≫ τ ≫ M.torus.hom))
    (f : L.pinned.pair.G.val ⟶ M.pinned.pair.G.val)
    (hf : MatchesPinning e (L.torus.inv ≫ τ ≫ M.torus.hom) f) (hg : MatchesRootGroups e f)
    (j : SimpleRoot P.pair) (hj : j.val ∈ I)
    (r : SimpleRepresentative P D j) (s : SimpleRepresentative Q E (compatibleSimpleRoots H j)) :
    ∃ n : RationalPoint L.pinned.pair.G.val,
      sectionMap L.inclusion _ n = r.reflection.representative ∧
      sectionMap (f ≫ M.inclusion) _ n = s.reflection.representative := by
  letI := D.comm
  let v := compatibleSimpleRoots H j
  let a : faceRoots P.pair D I := ⟨j.val, Submodule.subset_span ⟨_, hj, rfl⟩⟩
  let i₀ := L.rootIndex.symm a
  have hi : (L.rootIndex i₀).val = j.val := congrArg Subtype.val (L.rootIndex.apply_symm_apply a)
  let i : SimpleRoot L.pinned.pair := ⟨i₀, (L.simple_iff _).mpr (hi.symm ▸ hj)⟩
  let i' := compatibleSimpleRoots h i
  have hi' : (M.rootIndex i'.val).val = v.val := (he i.val).trans (congrArg d hi)
  obtain ⟨b, y, u, hb, hu, hn⟩ := lift_simple_representative L i j hi r
  let t := L.torus.inv ≫ τ ≫ M.torus.hom
  let θ := t ≫ M.torus.inv
  let F := f ≫ M.inclusion
  have hT : L.pinned.pair.T.inclusion ≫ F = θ ≫ Q.pair.T.inclusion := by
    simp only [F, θ, t, ← Category.assoc L.pinned.pair.T.inclusion, hf.1, Category.assoc, M.inclusion_torus]
  have hα' : M.torus.inv ≫ v.val.val = (e i.val).val := by
    rw [← show (M.rootIndex (e i.val)).val = v.val from hi', ← M.root_eq, Iso.inv_hom_id_assoc]
  have hα : θ ≫ v.val.val = i.val.val := by
    change (t ≫ M.torus.inv) ≫ v.val.val = i.val.val
    rw [Category.assoc, hα']
    exact h.root i.val
  let x₀ := (L.pinned.pin i).val.hom ≫ (L.pinned.roots i.val).val.inclusion
  let y₀ := y.val.hom ≫ (L.pinned.roots b).val.inclusion
  let x₁ := (Q.pin v).val.hom ≫ (Q.roots v.val).val.inclusion
  have hx : x₀ ≫ F = x₁ := by
    change x₀ ≫ (f ≫ M.inclusion) = x₁
    rw [← Category.assoc, show x₀ ≫ f = _ from hf.2 i i' rfl]
    exact M.pin_eq i' v hi'
  have hxb : HasScalarAction Q.pair.T v.val.val (x₀ ≫ F) := hx.symm ▸ (Q.pin v).property
  have hβ : (M.rootIndex (e b)).val.val = v.val.val⁻¹ := by
    rw [← M.root_eq, compatible_opposites h i.val b hb, pullback_inverse_character,
      M.root_eq]
    change ((M.rootIndex i'.val).val.val)⁻¹ = v.val.val⁻¹
    rw [hi']
  obtain ⟨eb, heb⟩ := hg b
  let w := y.val ≪≫ eb ≪≫ (M.rootIso (e b)).val
  have hw : y₀ ≫ F = w.hom ≫ (Q.roots (M.rootIndex (e b)).val).val.inclusion := by
    simp only [y₀, F, w, Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (L.pinned.roots b).val.inclusion, heb, Category.assoc]
    exact congrArg (fun g ↦ y.val.hom ≫ eb.hom ≫ g) (M.rootIso (e b)).property
  have hy : HasScalarAction Q.pair.T v.val.val⁻¹ (y₀ ≫ F) := by
    rw [hw, ← hβ]
    exact scalar_action_of_normalized_tangent _ _ Q.pair.split _
      (Q.roots (M.rootIndex (e b)).val).property _ w
  obtain ⟨w', hc, hr⟩ := map_linked_reflection F θ hT Q.pair.split hα u hxb hy
  have hc' : w'.coroot = s.reflection.coroot := by
    calc
      w'.coroot = (attachedCoroot L.datum i.val ≫ t) ≫ M.torus.inv := by
        rw [hc, hu]
        exact (Category.assoc _ _ _).symm
      _ = attachedCoroot M.datum (e i.val) ≫ M.torus.inv :=
        congrArg (fun c ↦ c ≫ M.torus.inv) (h.coroot i.val)
      _ = attachedCoroot E v.val := by
        rw [← M.coroot_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id,
          show (M.rootIndex (e i.val)).val = v.val from hi']
      _ = s.reflection.coroot := s.coroot_eq.symm
  have hneg : HasScalarAction Q.pair.T v.val.val⁻¹
      (s.negative.val.hom ≫ (Q.roots s.opposite).val.inclusion) := by
    rw [← s.opposite_eq]
    exact s.negative.property
  have heq := linked_representative_eq E W w' s.reflection hx hc' hxb hy hneg
  exact ⟨u.representative, hn, hr.symm.trans heq⟩

end LeviComparison


section Comparison

open Specs.AbstractPairing (Root)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.DatumAndWeyl (Identification)
open Specs.NormalizerComparison (SimpleRepresentative WeylPresentation)
open Specs.RootGroups (AdditiveLine)
open Specs.RankTwoLifting (Compatible)

open private reflection_cancel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots

variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem match_rank_two_power (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    [IsCommMonObj P.pair.T.group.X] [IsCommMonObj Q.pair.T.group.X]
    {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}
    (h : Compatible P Q D E d τ) (W : Identification D.datum) (V : Identification E.datum)
    (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
    (m : ∀ i : SimpleRoot Q.pair, SimpleRepresentative Q E i) (i j : D.base.support) :
    let e := compatibleSimpleRoots h
    let s := simpleReflection D.datum.rootDatum D.base
    ∃ t : RationalPoint P.pair.T.group,
      ((n (simpleRootOfIndex D i)).reflection.representative *
        (n (simpleRootOfIndex D j)).reflection.representative) ^ orderOf (s i * s j) =
          sectionMap P.pair.T.inclusion _ t ∧
      ((m (e (simpleRootOfIndex D i))).reflection.representative *
        (m (e (simpleRootOfIndex D j))).reflection.representative) ^ orderOf (s i * s j) =
          sectionMap (τ ≫ Q.pair.T.inclusion) _ t := by
  classical
  let e := compatibleSimpleRoots h
  let s := simpleReflection D.datum.rootDatum D.base
  let I := ({i.val, j.val} : Finset (Root P.pair.T))
  have hi : i.val ∈ I := Finset.mem_insert_self _ _
  have hj : j.val ∈ I := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hI : (I : Set (Root P.pair.T)) ⊆ D.base.support :=
    Finset.coe_subset.mpr (Finset.insert_subset_iff.mpr ⟨i.property, Finset.singleton_subset_iff.mpr j.property⟩)
  have hI' : d '' (I : Set (Root P.pair.T)) ⊆ E.base.support := by
    rintro _ ⟨α, hα, rfl⟩
    exact (h.simple α).mp (hI hα)
  obtain ⟨L⟩ := lift_pinning_to_levi P D (I : Set (Root P.pair.T)) hI
  obtain ⟨M⟩ := lift_pinning_to_levi Q E (d '' (I : Set (Root P.pair.T))) hI'
  let σ := L.torus.inv ≫ τ ≫ M.torus.hom
  obtain ⟨g, hg, hcompat⟩ := compatible_levis h L M
  have hrank := (levi_rank L I rfl).trans (Finset.card_le_two (a := i.val) (b := j.val))
  obtain ⟨f, hf, _, _, _, _, _, hgroups⟩ :=
    RankTwoLifting.liftTorusMap L.pinned M.pinned L.datum M.datum hrank g σ hcompat
  obtain ⟨a, ha, ha'⟩ := match_levi_representative h L M V g hg hcompat f hf hgroups
    (simpleRootOfIndex D i) hi (n (simpleRootOfIndex D i)) (m (e (simpleRootOfIndex D i)))
  obtain ⟨b, hb, hb'⟩ := match_levi_representative h L M V g hg hcompat f hf hgroups
    (simpleRootOfIndex D j) hj (n (simpleRootOfIndex D j)) (m (e (simpleRootOfIndex D j)))
  obtain ⟨t, ht⟩ := representative_power_in_torus D W n i j
  let tL := L.torus.hom ≫ L.pinned.pair.T.inclusion
  have htL : (a * b) ^ orderOf (s i * s j) = sectionMap tL _ t := by
    letI := L.mono
    apply (cancel_mono L.inclusion.hom.hom).mp
    change sectionMap L.inclusion _ _ = sectionMap L.inclusion _ _
    rw [map_pow, map_mul, ha, hb, ← sectionMap_comp,
      show tL ≫ L.inclusion = P.pair.T.inclusion from
        (Category.assoc _ _ _).trans L.torusInclusion]
    exact ht
  have htorus : tL ≫ (f ≫ M.inclusion) = τ ≫ Q.pair.T.inclusion := by
    simp only [tL, Category.assoc, ← Category.assoc L.pinned.pair.T.inclusion,
      hf.1, Category.assoc, σ, Iso.hom_inv_id_assoc, M.torusInclusion]
  refine ⟨t, ht, ?_⟩
  have hc := congrArg (sectionMap (f ≫ M.inclusion) _) htL
  rw [map_pow, map_mul, ha', hb', ← sectionMap_comp, htorus] at hc
  exact hc

/-- The prescribed torus map and the linked simple representatives determine
a comparison of the scheme normalizers over the ground field. -/
theorem normalizerComparison : Specs.NormalizerComparison.Statement.{u} := by
  intro k _ A P Q D E d τ h
  letI := D.comm
  letI := E.comm
  obtain ⟨W⟩ := identification_of_attached_datum P.pair D
  obtain ⟨V⟩ := identification_of_attached_datum Q.pair E
  obtain ⟨n⟩ := simple_representatives_exist P D
  obtain ⟨m⟩ := simple_representatives_exist Q E
  let e := compatibleSimpleRoots h
  have hpowers (i j : D.base.support) :
      let s := simpleReflection D.datum.rootDatum D.base
      ∃ t : RationalPoint P.pair.T.group,
        ((n (simpleRootOfIndex D i)).reflection.representative *
          (n (simpleRootOfIndex D j)).reflection.representative) ^ orderOf (s i * s j) =
            sectionMap P.pair.T.inclusion _ t ∧
        ((m (e (simpleRootOfIndex D i))).reflection.representative *
          (m (e (simpleRootOfIndex D j))).reflection.representative) ^ orderOf (s i * s j) =
            sectionMap (τ ≫ Q.pair.T.inclusion) _ t :=
    by
      by_cases hij : i = j
      · subst j
        dsimp only
        rw [show simpleReflection D.datum.rootDatum D.base i *
          simpleReflection D.datum.rootDatum D.base i = 1 from reflection_cancel D.datum.rootDatum i.val,
          orderOf_one, pow_one, pow_one]
        exact compatible_simple_squares h (simpleRootOfIndex D i) (e (simpleRootOfIndex D i))
          rfl (n (simpleRootOfIndex D i)) (m (e (simpleRootOfIndex D i)))
      · exact match_rank_two_power P Q D E h W V n m i j
  obtain ⟨f, hf, hmatch⟩ := compare_pinned_from_powers P Q D E d τ h W V.normalizer
    V.representsNormalizer V.torusInclusion V.inclusion_eq n m hpowers
  exact ⟨W.normalizer, V.normalizer, W.torusInclusion, V.torusInclusion, f,
    W.representsNormalizer, V.representsNormalizer, W.inclusion_eq, V.inclusion_eq,
    hf, n, m, hmatch⟩

end Comparison

end

end LinearAlgebraicGroups.Classification.NormalizerComparison
