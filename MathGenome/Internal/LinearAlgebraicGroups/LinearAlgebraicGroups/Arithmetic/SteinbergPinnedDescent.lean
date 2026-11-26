import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent
import Mathlib.Data.Fintype.Perm
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u
set_option backward.isDefEq.respectTransparency false

namespace LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent

open _root_.LinearAlgebraicGroups.Specs
open Specs.SteinbergPinnedDescent
open Pinning (PinnedGroup AttachedDatum SimpleRoot)
open RootGroups (AdditiveLine rootPoint rankOneWord Proportional)
open NormalizerComparison (SimpleRepresentative)
open AdjointRepresentation (GroupPoints)

noncomputable section

open private rootPoint_comp rootPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

theorem fixedMatching : FixedMatching := by
  intro J S H Δ _ e σ a w tr hw htr hc v hv hex
  have hfixed (δ : Δ) : permuteParameters (e δ) (σ δ) v = v := by
    rcases hv with hv | ⟨y, z, rfl, hy⟩
    · exact hv δ
    · have h := congrArg tr (hy δ)
      rw [hc, htr] at h
      exact h
  obtain ⟨t, ht, hunique⟩ := hex
  have htfix (δ : Δ) : permuteParameters (e δ) (σ δ) t = t := by
    apply hunique
    rw [← hw, htr, ht, hfixed]
  exact ⟨t, ht, htfix, fun δ ↦ by rw [hw, htfix]⟩

private theorem mixedCoefficients {I X Y : Type u} [DecidableEq I]
    [AddCommGroup X] [AddCommGroup Y] (p : RootPairing I ℤ X Y)
    (b : p.Base) {i j : I} (hi : i ∈ b.support) (hj : j ∈ b.support) (hne : i ≠ j)
    {a d : ℤ} (ha : a < 0) (hd : 0 < d) :
    a • p.root i + d • p.root j ∉ Set.range p.root := by
  intro h
  let f : I → ℤ := Pi.single i a + Pi.single j d
  have hf : ∑ l ∈ b.support, f l • p.root l = a • p.root i + d • p.root j := by
    simp [f, add_smul, Finset.sum_add_distrib, Pi.single_apply, hi, hj]
  have hsupport : f.support ⊆ b.support := by
    intro l hl
    by_contra hn
    have hil : l ≠ i := fun h ↦ hn (h.symm ▸ hi)
    have hjl : l ≠ j := fun h ↦ hn (h.symm ▸ hj)
    exact hl (by simp [f, hil, hjl])
  rcases b.pos_or_neg_of_sum_smul_root_mem f (hf ▸ h) hsupport with hp | hp
  · have hh := (le_of_lt hp) i
    change 0 ≤ f i at hh
    simp [f, hne] at hh
    omega
  · have hh := (le_of_lt hp) j
    change f j ≤ 0 at hh
    simp [f, hne.symm] at hh
    omega

private theorem orthogonalCone {I X Y : Type u} [DecidableEq I]
    [AddCommGroup X] [AddCommGroup Y] (p : RootPairing I ℤ X Y)
    (b : p.Base) {i j : I} (hi : i ∈ b.support) (hj : j ∈ b.support) (hne : i ≠ j)
    (hij : p.pairing j i = 0) {a d : ℤ} (ha : a ≠ 0) (hd : d ≠ 0) :
    a • p.root i + d • p.root j ∉ Set.range p.root := by
  have flip (c e : ℤ) :
      (∃ l, p.root l = c • p.root i + e • p.root j) →
        ∃ l, p.root l = (-c) • p.root i + e • p.root j := by
    rintro ⟨l, hl⟩
    refine ⟨p.reflectionPerm i l, ?_⟩
    rw [p.root_reflectionPerm, hl, map_add, map_smul, map_smul]
    have hself : p.reflection i (p.root i) = -p.root i := by
      exact p.reflection_apply_self i
    have hother : p.reflection i (p.root j) = p.root j := by
      rw [p.reflection_apply_root, hij, zero_smul, sub_zero]
    rw [hself, hother, smul_neg, neg_smul]
  have invert (c e : ℤ) :
      (∃ l, p.root l = c • p.root i + e • p.root j) →
        ∃ l, p.root l = (-c) • p.root i + (-e) • p.root j := by
    rintro ⟨l, hl⟩
    refine ⟨p.reflectionPerm l l, ?_⟩
    rw [p.root_reflectionPerm, p.reflection_apply_self, hl, neg_add, neg_smul, neg_smul]
  intro h
  change ∃ l, p.root l = a • p.root i + d • p.root j at h
  rcases lt_or_gt_of_ne hd with hd' | hd'
  · obtain ⟨a', ha', he⟩ : ∃ a' : ℤ, a' < 0 ∧
        ∃ l, p.root l = a' • p.root i + (-d) • p.root j := by
      rcases lt_or_gt_of_ne ha with ha' | ha'
      · exact ⟨a, ha', by simpa using invert (-a) d (flip a d h)⟩
      · exact ⟨-a, by omega, invert a d h⟩
    exact mixedCoefficients p b hi hj hne ha' (by omega) he
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · exact mixedCoefficients p b hi hj hne ha' hd' h
    · exact mixedCoefficients p b hi hj hne (a := -a) (by omega) hd' (flip a d h)


private def preservesE6 (e : Equiv.Perm (Fin 6)) : Prop :=
  ∀ i j, CartanMatrix.E 6 (e i) (e j) = CartanMatrix.E 6 i j

private instance (e : Equiv.Perm (Fin 6)) : Decidable (preservesE6 e) :=
  @Nat.decidableForallFin 6 _ (fun _i =>
    @Nat.decidableForallFin 6 _ (fun _j => Int.decEq _ _))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
private theorem preservesE6_cases :
    ∀ e : Equiv.Perm (Fin 6), preservesE6 e → e = 1 ∨ e = e6Involution := by
  decide

theorem e6Diagram : E6Diagram := by
  refine ⟨preservesE6_cases, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩
  change preservesE6 e6Involution
  decide

theorem e6BlockOrder : E6BlockOrder := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro e he b hb
    rcases preservesE6_cases e he with rfl | rfl
    · simp
    · simp only [e6Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> decide
  · intro b hb
    simp only [e6Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide

private theorem bourbakiPermutation_preserves {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) (e : Fin 6 ≃ SimpleRoot P.pair)
    (he : ∀ i j, letI := D.comm
      D.datum.rootDatum.pairing (e i).val (e j).val = CartanMatrix.E 6 i j)
    (d : Aut D.toBased) : preservesE6 ((e.trans (diagramPermutation D d)).trans e.symm) := by
  letI := D.comm
  let p := diagramPermutation D d
  let q : Equiv.Perm (Fin 6) := (e.trans p).trans e.symm
  have hp (i j : SimpleRoot P.pair) :
      D.datum.rootDatum.pairing (p i).val (p j).val =
        D.datum.rootDatum.pairing i.val j.val := by
    let v : D.datum.rootDatum.Equiv D.datum.rootDatum := d.asIso.hom.val
    exact v.toHom.pairing
  have heq (i : Fin 6) : e (q i) = p (e i) := e.apply_symm_apply _
  intro i j
  change CartanMatrix.E 6 (q i) (q j) = CartanMatrix.E 6 i j
  rw [← he, heq, heq, hp, he]

private theorem diagramPermutation_one {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) : diagramPermutation D 1 = 1 := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  rfl

theorem e6DiagramOrbits : E6DiagramOrbits.{u} := by
  intro k _ A P D Γ _ outer e he hnontrivial
  have hcases (σ : Γ) :
      (diagramPermutation D (outer σ) = 1) ∨
        (∀ i, diagramPermutation D (outer σ) (e i) = e (e6Involution i)) := by
    let p := diagramPermutation D (outer σ)
    let q : Equiv.Perm (Fin 6) := (e.trans p).trans e.symm
    have heq (i : Fin 6) : e (q i) = p (e i) := e.apply_symm_apply _
    rcases preservesE6_cases q (bourbakiPermutation_preserves D e he (outer σ)) with hq | hq
    · left
      change p = 1
      apply Equiv.ext
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      rw [← heq, hq]
      rfl
    · right
      intro i
      change p (e i) = _
      rw [← heq, hq]
  obtain ⟨σ, hσ⟩ := hnontrivial
  have hswap := (hcases σ).resolve_left hσ
  intro i j
  constructor
  · rintro ⟨τ, hτ⟩
    rcases hcases τ with h | h
    · rw [h] at hτ
      exact Or.inl (e.injective hτ.symm)
    · exact Or.inr (e.injective (hτ.symm.trans (h i)))
  · rintro (rfl | rfl)
    · refine ⟨1, ?_⟩
      rw [map_one, diagramPermutation_one]
      rfl
    · exact ⟨σ, hswap i⟩

theorem blockEquivariance : BlockEquivariance := by
  intro J S H _ p σ a b f ha hb hc t
  let t' := permuteParameters p σ t
  have hp (i : J) : a (f i (t i)) = f (p i) (t' (p i)) := by
    simpa [t', permuteParameters] using ha i (t i)
  have hl (l : List J) (h₁ : (l.map p).Perm l)
      (h₂ : (l.map fun i ↦ f i (t' i)).Pairwise Commute) :
      a ((l.map fun i ↦ f i (t i)).prod) = (l.map fun i ↦ f i (t' i)).prod := by
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def, hp]
    have hperm := h₁.symm.map (fun i ↦ f i (t' i))
    simpa only [List.map_map, Function.comp_def] using (hperm.prod_eq' h₂).symm
  change a ((b.flatten.map fun i ↦ f i (t i)).prod) =
    (b.flatten.map fun i ↦ f i (t' i)).prod
  induction b with
  | nil => simp
  | cons l b ih =>
      simp only [List.flatten_cons, List.map_append, List.prod_append, map_mul]
      rw [hl l (hb l (by simp)) (hc t' l (by simp))]
      rw [ih (fun B hB ↦ hb B (List.mem_cons_of_mem _ hB))
        (fun t B hB ↦ hc t B (List.mem_cons_of_mem _ hB))]

set_option maxHeartbeats 1600000 in
theorem exceptionalOrbitOrder : ExceptionalOrbitOrder.{u} := by
  classical
  intro k _ A P D Δ outer h
  letI := D.comm
  rcases h with h | ⟨e, he⟩
  · letI := D.datum.finiteRoots
    letI : Fintype (SimpleRoot P.pair) := Fintype.ofFinite _
    let l := (Finset.univ : Finset (SimpleRoot P.pair)).toList
    have hnodup : l.Nodup := Finset.nodup_toList _
    have hmem (i : SimpleRoot P.pair) : i ∈ l := Finset.mem_toList.mpr (Finset.mem_univ _)
    have hflat : (l.map (fun i ↦ [i])).flatten = l := by
      induction l with
      | nil => rfl
      | cons i l ih => simp [ih]
    refine ⟨l.map (fun i ↦ [i]), hflat.symm ▸ hnodup, ?_, ?_, ?_⟩
    · intro i
      rw [hflat]
      exact hmem i
    · intro δ b hb
      simp [h δ]
    · intro b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      simp
  · have horder := e6BlockOrder
    refine ⟨e6Blocks.map (fun b ↦ b.map e), ?_, ?_, ?_, ?_⟩
    · rw [← List.map_flatten]
      exact horder.1.map e.injective
    · intro i
      rw [← List.map_flatten]
      exact List.mem_map.mpr ⟨e.symm i, horder.2.1 _, e.apply_symm_apply _⟩
    · intro δ b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      let d := outer δ
      let p := diagramPermutation D d
      let q : Equiv.Perm (Fin 6) := (e.trans p).trans e.symm
      have heq (i : Fin 6) : e (q i) = p (e i) := e.apply_symm_apply _
      have hq : preservesE6 q := bourbakiPermutation_preserves D e he d
      simpa only [List.map_map, Function.comp_def, heq] using
        (horder.2.2.1 q hq b' hb').map e
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rw [List.pairwise_map]
      refine (horder.2.2.2 b' hb').imp ?_
      intro i j hij
      exact ⟨e.injective.ne hij.1, ⟨(he i j).trans hij.2.1, (he j i).trans hij.2.2⟩⟩

section Orthogonality

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}

private theorem signedRootCommutation (D : AttachedDatum P.pair)
    {i j : SimpleRoot P.pair} (hne : i ≠ j) (h : Orthogonal D i j)
    (α β : AbstractPairing.Root P.pair.T) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hα : α.val = i.val.val ^ a) (hβ : β.val = j.val.val ^ b)
    (R : TestAlgebra k) (p : GroupPoints (P.roots α).val.group R)
    (q : GroupPoints (P.roots β).val.group R) :
    Commute (p ≫ (P.roots α).val.inclusion.hom.hom : GroupPoints P.pair.G.val R)
      (q ≫ (P.roots β).val.inclusion.hom.hom) := by
  classical
  letI := D.comm
  let Q := D.datum.rootDatum
  have hrα : Q.root α = a • Q.root i.val := by
    change D.datum.rootDatum.root α = a • D.datum.rootDatum.root i.val
    rw [D.datum.root_eq, D.datum.root_eq, hα, ofMul_zpow]
  have hrβ : Q.root β = b • Q.root j.val := by
    change D.datum.rootDatum.root β = b • D.datum.rootDatum.root j.val
    rw [D.datum.root_eq, D.datum.root_eq, hβ, ofMul_zpow]
  have hin : ¬ Proportional α.val β.val := by
    rintro ⟨m, n, hm, hn, hmn⟩
    have e : m • Q.root α = n • Q.root β := by
      change m • D.datum.rootDatum.root α = n • D.datum.rootDatum.root β
      simpa only [D.datum.root_eq, ofMul_zpow] using
        congrArg Additive.ofMul hmn
    have v := congrArg (Q.coroot' i.val) e
    rw [hrα, hrβ, map_zsmul, map_zsmul, map_zsmul, map_zsmul] at v
    change m • (a • Q.pairing i.val i.val) = n • (b • Q.pairing j.val i.val) at v
    rw [Q.pairing_same, h.2, smul_zero, smul_zero] at v
    exact hm ((smul_eq_zero.mp v).resolve_right (smul_ne_zero ha (by decide)))
  have hcone (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      α.val ^ m * β.val ^ n ∉ CharacterPairing.absoluteRoots P.pair.T := by
    intro hmem
    let other : AbstractPairing.Root P.pair.T := Subtype.mk (α.val ^ m * β.val ^ n) hmem
    have hr : Q.root other = ((m : ℤ) * a) • Q.root i.val + ((n : ℤ) * b) • Q.root j.val := by
      calc
        Q.root other = m • Q.root α + n • Q.root β := by
          change D.datum.rootDatum.root other = _
          rw [D.datum.root_eq]
          change Additive.ofMul (α.val ^ m * β.val ^ n) =
            m • D.datum.rootDatum.root α + n • D.datum.rootDatum.root β
          rw [D.datum.root_eq, D.datum.root_eq, ofMul_mul,
            ofMul_pow, ofMul_pow]
        _ = _ := by rw [hrα, hrβ, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    exact orthogonalCone Q D.base ((D.simple_iff _).mpr i.property)
      ((D.simple_iff _).mpr j.property) (fun he ↦ hne (Subtype.ext he)) h.2
      (mul_ne_zero (by omega) ha) (mul_ne_zero (by omega) hb) ⟨other, hr⟩
  exact Classification.RankOneRelations.independentRootCommutation
    P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal
    α.val α.property β.val β.property hin hcone
    (P.roots α).val (P.roots β).val (P.roots α).property (P.roots β).property R p q

open private rational_word_at_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison
open private rankOneRepresentative_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private theorem representative_at_test {D : AttachedDatum P.pair}
    (i : SimpleRoot P.pair) (n : SimpleRepresentative P D i) (R : TestAlgebra k) :
    toUnit _ ≫ n.reflection.representative =
      rankOneWord ((P.pin i).val.hom ≫ (P.roots i.val).val.inclusion)
        (n.negative.val.hom ≫ (P.roots n.opposite).val.inclusion) R 1 := by
  rw [rational_word_at_one n.reflection, rankOneRepresentative_point]

theorem orthogonalFactors : OrthogonalFactors.{u} := by
  intro k _ A P D i j hne hij n m R t s
  have cp (a b : R) := signedRootCommutation D hne hij i.val j.val 1 1
    one_ne_zero one_ne_zero (by simp) (by simp) R
    (rootPoint (P.pin i).val.hom R a) (rootPoint (P.pin j).val.hom R b)
  have cn (a b : R) := signedRootCommutation D hne hij i.val m.opposite 1 (-1)
    one_ne_zero (by decide) (by simp) (by simpa using m.opposite_eq) R
    (rootPoint (P.pin i).val.hom R a) (rootPoint m.negative.val.hom R b)
  have np (a b : R) := signedRootCommutation D hne hij n.opposite j.val (-1) 1
    (by decide) one_ne_zero (by simpa using n.opposite_eq) (by simp) R
    (rootPoint n.negative.val.hom R a) (rootPoint (P.pin j).val.hom R b)
  have nn (a b : R) := signedRootCommutation D hne hij n.opposite m.opposite (-1) (-1)
    (by decide) (by decide) (by simpa using n.opposite_eq) (by simpa using m.opposite_eq) R
    (rootPoint n.negative.val.hom R a) (rootPoint m.negative.val.hom R b)
  simp only [← rootPoint_comp] at cp cn np nn
  unfold factor
  rw [representative_at_test i n R, representative_at_test j m R]
  simp only [rankOneWord, Units.val_one, inv_one]
  have hp (a : R) := (cp a s).mul_right (((cp a 1).mul_right (cn a (-1))).mul_right (cp a 1))
  have hn (a : R) := (np a s).mul_right (((np a 1).mul_right (nn a (-1))).mul_right (np a 1))
  exact (hp t).mul_left (((hp 1).mul_left (hn (-1))).mul_left (hp 1))

end Orthogonality

section PinnedFactors

open Pinning (PinnedIso transportCharacter pinGraph)
open CharacterDescent (Character)
open private identification_of_attached_datum map_linked_reflection
  linked_representative_eq scalar_action_along_iso pullback_inverse_character sectionMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}

theorem pinnedFactors : PinnedFactors.{u} := by
  intro k _ A P D d f hf n R i t
  letI := D.comm
  let j := diagramPermutation D d i
  change ((groupPointsFunctor k).map f.group.hom).app R (factor i (n i) R t) =
    factor j (n j) R t
  let x := (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion
  let x' := (P.pin j).val.hom ≫ (P.roots j.val).val.inclusion
  let y := (n i).negative.val.hom ≫ (P.roots (n i).opposite).val.inclusion
  let y' := (n j).negative.val.hom ≫ (P.roots (n j).opposite).val.inclusion
  have hα' : transportCharacter f.torus i.val.val = j.val.val := by
    apply Additive.ofMul.injective
    let F : D.datum.rootDatum.Equiv D.datum.rootDatum := d.asIso.hom.val
    have hm := RootPairing.Hom.root_weightMap_apply _ _ i.val F.toHom
    rw [D.datum.root_eq, D.datum.root_eq] at hm
    have hj : F.indexEquiv i.val = j.val := by
      simp only [F, j, diagramPermutation, Equiv.subtypeEquiv]
      rfl
    rw [← RootPairing.Equiv.weightEquiv_apply, show F.toHom.indexEquiv i.val = j.val from hj] at hm
    exact (hf.1 _).symm.trans hm
  have hα : f.torus.hom ≫ j.val.val = i.val.val := by
    rw [← hα', transportCharacter, Iso.hom_inv_id_assoc]
  have hpin : x ≫ f.group.hom = x' := by
    have hm : (transportCharacter f.torus i.val.val, x ≫ f.group.hom) ∈ pinGraph P := by
      rw [← f.pin_comm]
      exact ⟨(i.val.val, x), ⟨i, rfl⟩, rfl⟩
    obtain ⟨l, hl⟩ := hm
    have hel : l = j := Subtype.ext (Subtype.ext ((congrArg Prod.fst hl).trans hα'))
    subst l
    exact (congrArg Prod.snd hl).symm
  have hposit : RootGroups.HasScalarAction P.pair.T j.val.val (x ≫ f.group.hom) :=
    by rw [hpin]; exact (P.pin j).property
  have hneg (l : SimpleRoot P.pair) :
      RootGroups.HasScalarAction P.pair.T l.val.val⁻¹
        ((n l).negative.val.hom ≫ (P.roots (n l).opposite).val.inclusion) := by
    rw [← (n l).opposite_eq]
    exact (n l).negative.property
  have hnegTransport : RootGroups.HasScalarAction P.pair.T j.val.val⁻¹ (y ≫ f.group.hom) := by
    apply scalar_action_along_iso f.group.hom f.torus f.torus_comm
    rw [pullback_inverse_character, hα]
    exact hneg i
  obtain ⟨s, hcoroot, hrep⟩ :=
    map_linked_reflection f.group.hom f.torus.hom f.torus_comm P.pair.split hα
      (n i).reflection hposit hnegTransport
  have hc : s.coroot = (n j).reflection.coroot := by
    rw [hcoroot, (n i).coroot_eq, (n j).coroot_eq]
    exact hf.2 i.val
  obtain ⟨W⟩ := identification_of_attached_datum P.pair D
  have hrep' := linked_representative_eq D W s (n j).reflection hpin hc
    hposit hnegTransport (hneg j)
  let F : GroupPoints P.pair.G.val R →* GroupPoints P.pair.G.val R :=
    (((groupPointsFunctor k).map f.group.hom).app R).hom
  change F (factor i (n i) R t) = _
  rw [factor, factor, map_mul]
  congr 1
  · change rootPoint x R t ≫ f.group.hom.hom.hom = rootPoint x' R t
    rw [← rootPoint_comp, hpin]
  · change (toUnit _ ≫ (n i).reflection.representative) ≫ f.group.hom.hom.hom = _
    rw [Category.assoc]
    change toUnit _ ≫ sectionMap f.group.hom _ (n i).reflection.representative = _
    rw [← hrep, hrep']

end PinnedFactors

section FieldPoints

open RelativeFormComparison (fieldMap fieldTest)
open Descent.NonabelianCohomology (pointMap pointAction)

theorem traceConjugacy : TraceConjugacy.{u} := by
  intro k I _ _ _ A P ρ R g z
  unfold traceValue
  let f : GroupPoints P.pair.G.val R →* Matrix.GeneralLinearGroup I R := (ρ.app R).hom
  change Matrix.trace (f (z * g * z⁻¹)).val = Matrix.trace (f g).val
  rw [map_mul, map_mul, map_inv]
  exact Matrix.trace_units_conj (f z) (f g).val

theorem traceCoefficients : TraceCoefficients.{u} := by
  intro k S I _ _ _ _ _ A P ρ σ g
  let R := CommAlgCat.of k S
  let a : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  have h := ConcreteCategory.congr_hom (ρ.naturality a) g
  change ρ.app R (coefficientAction S P.pair.G.val σ g) =
    Matrix.GeneralLinearGroup.map σ.toRingHom (ρ.app R g) at h
  change Matrix.trace ((ρ.app R).hom (coefficientAction S P.pair.G.val σ g)).val =
    σ (Matrix.trace ((ρ.app R).hom g).val)
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, Matrix.GeneralLinearGroup.map_apply]
  rfl

set_option maxHeartbeats 1600000 in
theorem rationalPoints : RationalPoints.{u} := by
  intro k S _ _ _ _ G g
  let C := AdjointCocharacters.coordinateHopf G
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let e := AdjointCocharacters.coordinateHopfIso G
  let p : Points G.val.X (CommAlgCat.of k S) := g
  let q : Points (specGroup C).X (CommAlgCat.of k S) :=
    p ≫ e.inv.hom.hom
  let f : CommAlgCat.of k C ⟶ CommAlgCat.of k S := (ff.preimage q).unop
  have hq : (testSpec k).map f.op = q := ff.map_preimage q
  let j : CommAlgCat.of k k ⟶ CommAlgCat.of k S := CommAlgCat.ofHom (Algebra.ofId k S)
  constructor
  · intro h
    have hf (x : C) : f.hom x ∈ Set.range (algebraMap k S) := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (f.hom x)).mpr
      intro σ
      let b : CommAlgCat.of k S ⟶ CommAlgCat.of k S := CommAlgCat.ofHom σ.toAlgHom
      have he : f ≫ b = f := by
        apply Quiver.Hom.op_inj
        apply ff.map_injective
        rw [op_comp, Functor.map_comp, hq]
        change (testSpec k).map b.op ≫ q = q
        change (testSpec k).map b.op ≫ (p ≫ e.inv.hom.hom) = _
        rw [← Category.assoc]
        exact congrArg (fun v : Points G.val.X (CommAlgCat.of k S) => v ≫ e.inv.hom.hom) (h σ)
      have hv := congrArg (fun f : CommAlgCat.of k C ⟶ CommAlgCat.of k S => f.hom x) he
      exact hv
    choose c hc using hf
    have hin : Function.Injective (algebraMap k S) := (algebraMap k S).injective
    let c' : C →ₐ[k] k :=
      { toFun := c
        map_one' := hin (by rw [hc, map_one, map_one])
        map_zero' := hin (by rw [hc, map_zero, map_zero])
        map_add' := fun x y => hin (by simp only [hc, map_add])
        map_mul' := fun x y => hin (by simp only [hc, map_mul])
        commutes' := fun x => hin (by rw [hc, AlgHom.commutes]; rfl) }
    let cf : CommAlgCat.of k C ⟶ CommAlgCat.of k k := CommAlgCat.ofHom c'
    have hcf : cf ≫ j = f := CommAlgCat.hom_ext (AlgHom.ext hc)
    let x : Points G.val.X (CommAlgCat.of k k) := (testSpec k).map cf.op ≫ e.hom.hom.hom
    refine ⟨x, ?_⟩
    change (testSpec k).map j.op ≫ (testSpec k).map cf.op ≫ e.hom.hom.hom = p
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hcf, hq]
    change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    exact Category.comp_id p
  · rintro ⟨x, rfl⟩ σ
    let b : CommAlgCat.of k S ⟶ CommAlgCat.of k S := CommAlgCat.ofHom σ.toAlgHom
    have he : j ≫ b = j := CommAlgCat.hom_ext (AlgHom.ext σ.commutes)
    change (testSpec k).map b.op ≫ (testSpec k).map j.op ≫
      (x : Points G.val.X (CommAlgCat.of k k)) = _
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp, he]

end FieldPoints

section WordEquivariance

open Pinning (PinnedIso)

private theorem coefficientAction_factor {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    (i : SimpleRoot P.pair) (n : SimpleRepresentative P D i)
    (σ : Gal(S/k)) (t : S) :
    coefficientAction S P.pair.G.val σ (factor i n (CommAlgCat.of k S) t) =
      factor i n (CommAlgCat.of k S) (σ t) := by
  let R := CommAlgCat.of k S
  let a : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  let f := (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion
  rw [factor, factor, map_mul]
  congr 1
  · change mapPoints a (rootPoint f R t) = rootPoint f R (σ t)
    exact rootPoint_natural f a t
  · change (testSpec k).map a.op ≫ toUnit _ ≫ n.reflection.representative =
      toUnit _ ≫ n.reflection.representative
    rw [← Category.assoc, comp_toUnit]

theorem wordEquivariance : WordEquivariance.{u} := by
  intro k S _ _ _ A P D d f hf n blocks hblocks horth σ t
  let R := CommAlgCat.of k S
  apply blockEquivariance (diagramPermutation D d) (fun t : S ↦ σ t)
    (pinnedAction S f σ) blocks (fun i ↦ factor i (n i) R) ?_ hblocks ?_ t
  · intro i v
    change pinnedPointMap f (coefficientAction S P.pair.G.val σ (factor i (n i) R v)) = _
    rw [coefficientAction_factor]
    exact pinnedFactors D d f hf n R i (σ v)
  · intro t b hb
    rw [List.pairwise_map]
    exact (horth b hb).imp fun {i j} h ↦ orthogonalFactors D i j h.1 h.2 (n i) (n j) R (t i) (t j)

end WordEquivariance

section RelativeDescent

open AutomorphismSequence (relativePoints restrictIso scalarAut forgetPinning)
open RelativeFormComparison (fieldTest fieldMap transportedAut)

set_option maxHeartbeats 1600000 in
theorem relativeDescent : RelativeDescent.{u} := by
  intro k S _ _ _ _ A P G e p he y hy
  apply (rationalPoints G (comparisonOnPoints e y)).mp
  intro σ
  let V := Over.mk (𝟙 (fieldTest k S))
  let W := Over.mk (fieldMap k S σ)
  let v : W ⟶ V := Over.homMk (fieldMap k S σ) (Category.comp_id _)
  let R := CommAlgCat.of k S
  let a := coefficientAction S P.pair.G.val σ y
  have hn :
      coefficientAction S G.val σ (comparisonOnPoints e y) =
        (e.hom.app (op W)).hom a := by
    exact (ConcreteCategory.congr_hom (e.hom.naturality v.op) y).symm
  have hh := congrArg
    (fun f : AutomorphismSequence.RelativeAut P.pair.G.val (fieldTest k S) =>
      (f.asIso.hom.app (op V)).hom a) (he σ)
  have hh' : comparisonOnPoints e ((pinnedPointMap (p σ).asIso.hom) a) =
      (e.hom.app (op W)).hom a := by
    have ht : comparisonOnPoints e ((e.inv.app (op V)).hom ((e.hom.app (op W)).hom a)) =
        (e.hom.app (op W)).hom a :=
      (comparisonOnPoints e).apply_symm_apply _
    change (e.inv.app (op V)).hom ((e.hom.app (op W)).hom a) =
      (pinnedPointMap (p σ).asIso.hom) a at hh
    rwa [hh] at ht
  rw [hn, ← hh']
  exact congrArg (comparisonOnPoints e) (hy σ)

end RelativeDescent

section TraceTransport

open RootWeightAction (Representation act extendVector)
open PrimitiveLine (IsEquivariant orbitCoefficient)

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] {A : AdditiveLine k} {P : PinnedGroup A}

private theorem trace_eq_of_equivariant (ρ : Representation P.pair.G.val I)
    (τ : Representation P.pair.G.val J) (F : (I → k) ≃ₗ[k] (J → k))
    (hF : IsEquivariant ρ τ F.toLinearMap)
    (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R) :
    traceValue ρ R g = traceValue τ R g := by
  let C := F.toLinearMap.toMatrix'
  let E := F.symm.toLinearMap.toMatrix'
  let C' := C.map (algebraMap k R)
  let E' := E.map (algebraMap k R)
  let M : Matrix I I R := (ρ.app R g : Matrix.GeneralLinearGroup I R).val
  let N : Matrix J J R := (τ.app R g : Matrix.GeneralLinearGroup J R).val
  have hE : E * C = 1 := by
    dsimp only [E, C]
    rw [← LinearMap.toMatrix'_comp]
    have h : F.symm.toLinearMap.comp F.toLinearMap = LinearMap.id := by ext v i; simp
    rw [h, LinearMap.toMatrix'_id]
  have hC : C * E = 1 := by
    dsimp only [E, C]
    rw [← LinearMap.toMatrix'_comp]
    have h : F.toLinearMap.comp F.symm.toLinearMap = LinearMap.id := by ext v i; simp
    rw [h, LinearMap.toMatrix'_id]
  have hE' : E' * C' = 1 := by
    change E.map (algebraMap k R) * C.map (algebraMap k R) = _
    rw [← Matrix.map_mul, hE, Matrix.map_one] <;> simp
  have hC' : C' * E' = 1 := by
    change C.map (algebraMap k R) * E.map (algebraMap k R) = _
    rw [← Matrix.map_mul, hC, Matrix.map_one] <;> simp
  have hM : C' * M = N * C' := by
    ext i j
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro ℓ
    have hu := hF R g ℓ (Pi.single j 1)
    change F.toLinearMap _ = _ at hu
    rw [← LinearMap.toMatrix'_mulVec] at hu
    have h := congrFun hu i
    have hs : extendVector R (Pi.single j 1) = Pi.single j 1 := by
      ext x
      by_cases hx : x = j <;> simp [extendVector, hx]
    have hcol (j : I) : extendVector R (F (Pi.single j 1)) = fun i ↦ C' i j := by
      funext i
      rfl
    change (C *ᵥ fun x ↦ ℓ ((M *ᵥ extendVector R (Pi.single j 1)) x)) i =
      ℓ ((N *ᵥ extendVector R (F (Pi.single j 1))) i) at h
    rw [hs, Matrix.mulVec_single_one, hcol] at h
    have h' : (C *ᵥ fun x ↦ ℓ (M.col j x)) i = ℓ ((N * C') i j) := h
    rw [map_sub, sub_eq_zero, ← h']
    simp only [Matrix.mul_apply, map_sum, Matrix.mulVec, dotProduct, Matrix.col_apply]
    apply Finset.sum_congr rfl
    intro x _
    change ℓ (algebraMap k R (C i x) * M x j) = C i x * ℓ (M x j)
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  change Matrix.trace M = Matrix.trace N
  calc
    Matrix.trace M = Matrix.trace (E' * (C' * M)) := by
      rw [← Matrix.mul_assoc, hE', Matrix.one_mul]
    _ = Matrix.trace ((N * C') * E') := by rw [hM, Matrix.trace_mul_comm]
    _ = Matrix.trace N := by rw [Matrix.mul_assoc, hC', Matrix.mul_one]

end TraceTransport

section HighestWeights

open Pinning (PinnedIso)
open CharacterDescent (Character)
open RootWeightAction (Representation IsPrimitive mem_weightSpace mem_fixedSpace)
open PrimitiveLine (IsSimple IsStable IsEquivariant)
open FlagLineBundle (OppositeBorelPair)
open SimpleClassification (HasHighestWeight)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
  {A : AdditiveLine k} {P : PinnedGroup A}

/-- Pull a representation back along a ground-field pinned automorphism. -/
private def pullRepresentation (f : PinnedIso P P) (ρ : Representation P.pair.G.val I) :
    Representation P.pair.G.val I :=
  (groupPointsFunctor k).map f.group.hom ≫ ρ

set_option maxHeartbeats 1600000 in
private theorem pullRepresentation_simple (f : PinnedIso P P)
    (ρ : Representation P.pair.G.val I) (h : IsSimple ρ) :
    IsSimple (pullRepresentation f ρ) := by
  refine ⟨h.1, fun M hM ↦ h.2 M ?_⟩
  intro v hv
  have hspan :
      CyclicHighestWeight.orbitSpan (G := P.pair.G)
          (pullRepresentation f ρ) (𝟙 P.pair.G.val.X) v =
        CyclicHighestWeight.orbitSpan (G := P.pair.G) ρ (𝟙 P.pair.G.val.X) v := by
    unfold CyclicHighestWeight.orbitSpan
    simp only [Category.comp_id]
    apply iSup_congr
    intro R
    let e := (((groupPointsFunctor k).mapIso f.group).app R).groupIsoToMulEquiv
    let spanAt (g : GroupPoints P.pair.G.val R) : Submodule k (I → k) :=
      Submodule.span k (Set.range fun ℓ : R →ₗ[k] k ↦ PrimitiveLine.orbitCoefficient ρ R g ℓ v)
    change (⨆ g : GroupPoints P.pair.G.val R, spanAt (e g)) =
      ⨆ g : GroupPoints P.pair.G.val R, spanAt g
    exact e.surjective.iSup_comp spanAt
  rw [← hspan]
  exact hM v hv

set_option maxHeartbeats 1200000 in
private theorem pullRepresentation_primitive (f : PinnedIso P P)
    (ρ : Representation P.pair.G.val I) (U : ClosedSubgroup P.pair.B.group)
    (j : U.group ⟶ U.group) (hj : U.inclusion ≫ f.borel.hom = j ≫ U.inclusion)
    (χ : Character P.pair.T.group) (v : I → k)
    (hv : IsPrimitive ρ P.pair.T P.pair.B U χ v) :
    IsPrimitive (pullRepresentation f ρ) P.pair.T P.pair.B U (f.torus.hom ≫ χ) v := by
  refine ⟨hv.1, mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
  · intro R u
    have hB : (U.inclusion ≫ P.pair.B.inclusion) ≫ f.group.hom =
        j ≫ (U.inclusion ≫ P.pair.B.inclusion) := by
      rw [Category.assoc, f.borel_comm, ← Category.assoc U.inclusion, hj, Category.assoc]
    have hBi := congrArg (fun q : U.group ⟶ P.pair.G.val => q.hom.hom) hB
    have h := mem_fixedSpace.mp hv.2.1 R (u ≫ j.hom.hom)
    change RootWeightAction.act ρ R
      ((u ≫ (U.inclusion ≫ P.pair.B.inclusion).hom.hom) ≫ f.group.hom.hom.hom)
      (RootWeightAction.extendVector R v) = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hBi, Grp.comp_hom_hom, ← Category.assoc]
    exact h
  · intro R t
    have h := mem_weightSpace.mp hv.2.2 R (t ≫ f.torus.hom.hom.hom)
    change RootWeightAction.act ρ R ((t ≫ P.pair.T.inclusion.hom.hom) ≫ f.group.hom.hom.hom)
      (RootWeightAction.extendVector R v) = _
    rw [Category.assoc, ← Grp.comp_hom_hom, f.torus_comm, Grp.comp_hom_hom, ← Category.assoc]
    refine h.trans ?_
    unfold CharacterPairing.characterValue
    rw [Grp.comp_hom_hom, Category.assoc]

open private pushRadical pushSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy

private theorem pinnedRadical_stable (f : PinnedIso P P)
    (U : ClosedSubgroup P.pair.B.group)
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U) :
    ∃ j : U.group ⟶ U.group, U.inclusion ≫ f.borel.hom = j ≫ U.inclusion := by
  let B := closedSubgroupAlgebraicGroup P.pair.B
  have h : Specs.GeometricRadicals.IsUnipotentRadical B (pushSubgroup U f.borel) :=
    pushRadical (A := B) (B := B) f.borel hU
  obtain ⟨j, hj⟩ := hU.2.2 (pushSubgroup U f.borel) h.1 h.2.1
  exact ⟨j, hj.symm⟩

set_option maxHeartbeats 1600000 in
theorem pinnedTracePermutation : PinnedTracePermutation.{u} := by
  intro k _ A P D d f N U hU M hweight R g
  obtain ⟨j, hj⟩ := pinnedRadical_stable f U hU
  let p := diagramPermutation D d
  funext l
  let i := p.symm l
  have hil : p i = l := p.apply_symm_apply l
  let ρ := pullRepresentation f (M.representation l)
  have hw : HasHighestWeight N.pair U ρ (M.weight i) := by
    obtain ⟨v, hv⟩ := M.highest l
    refine ⟨v, ?_⟩
    have h' : f.torus.hom ≫ M.weight l = M.weight i := by
      rw [← hil]
      exact hweight i
    rw [← h']
    exact pullRepresentation_primitive f (M.representation l) U j hj (M.weight l) v hv
  have hs : IsSimple ρ := pullRepresentation_simple f (M.representation l) (M.simple l)
  let E := LinearAlgebraicGroups.Representation.SimpleClassification.classification
    P.pair.G N.pair U hU
  have hdom := E.2.1 (M.representation i) (M.simple i) (M.weight i) (M.highest i)
  obtain ⟨V, hV⟩ := E.2.2 (M.weight i) hdom
  obtain ⟨F⟩ := (hV ρ hs).mpr hw
  obtain ⟨F'⟩ := (hV (M.representation i) (M.simple i)).mpr (M.highest i)
  change traceValue ρ R g = traceValue (M.representation i) R g
  calc
    _ = traceValue V.socleAction R g := trace_eq_of_equivariant ρ _ F.val F.property R g
    _ = _ := (trace_eq_of_equivariant _ _ F'.val F'.property R g).symm

theorem tracePermutation : TracePermutation.{u} := by
  intro k S _ _ _ A P D d f N U hU M hweight σ g
  let R := CommAlgCat.of k S
  let g' := coefficientAction S P.pair.G.val σ g
  funext j
  let i := (diagramPermutation D d).symm j
  have h := congrFun (pinnedTracePermutation D d f N U hU M hweight R g') j
  change traceValue (M.representation j) R (pinnedPointMap f g') =
    traceValue (M.representation i) R g' at h
  exact h.trans (traceCoefficients (M.representation i) σ g)

open private pairing_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison

set_option maxHeartbeats 1000000 in
theorem fundamentalWeightPermutation : FundamentalWeightPermutation.{u} := by
  classical
  intro k _ A P D d f hf hin χ hχ i
  letI := D.comm
  let p := diagramPermutation D d
  apply hin
  funext j
  change D.datum.rootDatum.toLinearMap (Additive.ofMul (f.torus.hom ≫ χ (p i)))
    (D.datum.rootDatum.coroot j.val) =
      D.datum.rootDatum.toLinearMap (Additive.ofMul (χ i)) (D.datum.rootDatum.coroot j.val)
  calc
    _ = D.datum.rootDatum.toLinearMap (Additive.ofMul (χ (p i)))
          (D.datum.rootDatum.coroot (p j).val) := by
      let c := Additive.toMul (D.datum.rootDatum.coroot j.val)
      let c' := Additive.toMul (D.datum.rootDatum.coroot (p j).val)
      calc
        _ = CharacterPairing.pairing _ (f.torus.hom ≫ χ (p i)) c := D.datum.pairing_eq _ c
        _ = CharacterPairing.pairing _ (χ (p i)) c' := by
          rw [pairing_comp]
          exact congrArg (CharacterPairing.pairing _ (χ (p i))) (hf.2 j.val)
        _ = _ := (D.datum.pairing_eq _ c').symm
    _ = _ := by
      change simpleCorootValues D (χ (p i)) (p j) = simpleCorootValues D (χ i) j
      rw [hχ (p i) (p j), hχ i j]
      by_cases h : j = i <;> simp [h]

end HighestWeights

section FundamentalModules

open CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open private existsOppositeBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}

private theorem simpleCorootCoordinates (D : AttachedDatum P.pair)
    (hG : IsSemisimple P.pair.G) (hsc : GeometricallySimplyConnected P.pair.G) :
    Function.Bijective (simpleCorootValues D) := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI : Fintype (SimpleRoot P.pair) := Fintype.ofFinite _
  let p := D.datum.rootDatum
  have hspan : Submodule.span ℤ (Set.range p.coroot) = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.pair.G hG P.pair.T
      P.pair.split P.pair.maximal D.datum).mp hsc
  let B₀ : Module.Basis D.base.support ℤ (Additive (Cocharacter P.pair.T.group)) :=
    Module.Basis.mk D.base.linearIndepOn_coroot (ge_of_eq (by
      rw [← Set.image_eq_range, D.base.span_int_coroot_support, hspan]))
  let index : D.base.support ≃ SimpleRoot P.pair :=
    (Equiv.refl _).subtypeEquiv D.simple_iff
  let B := B₀.reindex index
  let e := p.toLinearMap.toPerfPair.trans B.dualBasis.equivFun
  have he : simpleCorootValues D = e ∘ Additive.ofMul := by
    funext χ j
    change _ = B.dualBasis.equivFun (p.toLinearMap (Additive.ofMul χ)) j
    rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
    have hB : B j = p.coroot j.val := by
      rw [Module.Basis.reindex_apply]
      exact Module.Basis.mk_apply _ _ _
    rw [hB]
    rfl
  rw [he]
  exact e.bijective.comp Additive.ofMul.bijective

theorem fundamentalModulesExist : FundamentalModulesExist.{u} := by
  classical
  intro k _ A P D hG hsc
  obtain ⟨comm, _, _, hB, _, _, hrad⟩ := RootData.BorelPositivity.borelPositivity
    P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal
  obtain ⟨Bneg, hBneg, hTneg, hop⟩ :=
    existsOppositeBorel P.pair.borel P.pair.containsTorus hB
  obtain ⟨U, _, _, hU, _⟩ := hrad P.pair.B P.pair.borel P.pair.containsTorus
  let N : OppositeBorel P.pair := ⟨Bneg, hBneg, hTneg, hop⟩
  letI : IsCommMonObj N.pair.torus.group.X := D.comm
  letI := Classical.decEq (SimpleRoot P.pair)
  let basisVector (i j : SimpleRoot P.pair) : ℤ := if j = i then 1 else 0
  choose χ hχ using fun i ↦ (simpleCorootCoordinates D hG hsc).2 (basisVector i)
  have hdom (i : SimpleRoot P.pair) : InducedNonvanishing.Dominant N.pair (χ i) := by
    apply (Representation.InducedNonvanishing.dominant_iff_datum
      Classification.CentralIsogenies.centralIsogenyComparison N.pair D.datum (χ i)).mpr
    intro j
    let j' : SimpleRoot P.pair := j
    change 0 ≤ simpleCorootValues D (χ i) j'
    rw [congrFun (hχ i) j']
    simp only [basisVector]
    split <;> decide
  let V (i : SimpleRoot P.pair) := Classical.choose
    ((Representation.SimpleClassification.classification P.pair.G N.pair U hU).2.2
      (χ i) (hdom i))
  refine ⟨N, U, hU, {
    weight := χ
    index := fun i ↦ (V i).J
    finiteIndex := fun i ↦ (V i).finiteJ
    decidableIndex := fun i ↦ (V i).decJ
    representation := fun i ↦ (V i).socleAction
    simple := fun i ↦ (V i).simple
    highest := fun i ↦ ⟨(V i).socleBasis.equivFun (V i).highestVector, (V i).primitive⟩
  }, ?_⟩
  exact fun i j ↦ congrFun (hχ i) j

end FundamentalModules

section PinnedReference

open AutomorphismSequence (scalarAut forgetPinning)
open QuasiSplitInnerForms (pinnedSection)

theorem referenceDescent : ReferenceDescent.{u} := by
  intro k S _ _ _ _ A P D l Q E ω V y hy
  refine relativeDescent V.model.val V.trivialization (fun σ ↦ l (ω σ)) ?_ y hy
  intro σ
  rw [V.transport_eq]
  exact E.sectionOnConstants _ _

end PinnedReference

section PinnedLifts

open AutomorphismSequence (AdjointQuotient SplitSequence scalarAut forgetPinning)
open CharacterDescent (Character Cocharacter)
open Pinning (PinnedIso transportCharacter)
open private pinnedScalarAligned from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option maxHeartbeats 1800000 in
theorem pinnedSequenceLifts : PinnedSequenceLifts.{u} := by
  intro k _ A P D l Q E d
  letI := D.comm
  let f : PinnedIso P P := (l d).asIso.hom
  let S := 𝟙_ (SchemeOver k)
  let b := Functor.mapAut P (forgetPinning (A := A)) (l d)
  let a := pinnedScalarAligned (l d) S
  let C := AutomorphismSequence.constantGroup (k := k) (Aut D.toBased)
  have hE := congrArg (fun (m : C ⟶ C) => (m.app (op S)).hom ⟨LocallyConstant.const _ d⟩)
    E.rightInverse
  have hS := E.sectionOnConstants S d
  change E.toExactSequence.outer.app (op S)
    (E.sectionMap.app (op S) ⟨LocallyConstant.const _ d⟩) = _ at hE
  rw [hS] at hE
  have ha := E.latticeAction S (scalarAut b S) a d hE
  constructor
  · intro χ
    let T := P.pair.T.group.X
    let V : Over S := Over.mk (toUnit T)
    have he := ha.1 χ V (𝟙 T)
    change (𝟙 T ≫ f.torus.inv.hom.hom) ≫ χ.hom.hom =
      𝟙 T ≫ (Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))).hom.hom at he
    apply Additive.toMul.injective
    apply Grp.hom_ext
    change (Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))).hom.hom =
      (f.torus.inv ≫ χ).hom.hom
    simpa only [Category.id_comp, Grp.comp_hom_hom] using he.symm
  · intro i
    let v : D.datum.rootDatum.Equiv D.datum.rootDatum := d.asIso.hom.val
    let j := v.indexEquiv i
    let c : Cocharacter P.pair.T.group := Additive.toMul (D.datum.rootDatum.coroot j)
    let T := (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X
    let V : Over S := Over.mk (toUnit T)
    have he := ha.2 c V (𝟙 T)
    have hr : v.coweightEquiv (D.datum.rootDatum.coroot j) = D.datum.rootDatum.coroot i := by
      simpa only [j, RootPairing.Equiv.coweightEquiv_apply, v.indexEquiv.symm_apply_apply]
        using RootPairing.Hom.coroot_coweightMap_apply _ _ j v.toHom
    have hv : c ≫ f.torus.inv = Additive.toMul (D.datum.rootDatum.coroot i) := by
      apply Grp.hom_ext
      change (𝟙 T ≫ c.hom.hom) ≫ f.torus.inv.hom.hom =
        𝟙 T ≫ (Additive.toMul (v.coweightEquiv (D.datum.rootDatum.coroot j))).hom.hom at he
      rw [hr, Category.id_comp, Category.id_comp, ← Grp.comp_hom_hom] at he
      exact he
    rw [← hv, Category.assoc, f.torus.inv_hom_id, Category.comp_id]
    rfl

end PinnedLifts

section Matching

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open RelativeFormComparison (fieldTest)
open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open private simple_representatives_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.NormalizerComparison

set_option maxHeartbeats 1800000 in
private theorem matchingOnPoints {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q) {G : AffineAlgebraicGroup k}
    (e : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (outer : Gal(S/k) → Aut D.toBased)
    (descend : ∀ y : GroupPoints P.pair.G.val (CommAlgCat.of k S),
      (∀ σ, pinnedAction S (l (outer σ)).asIso.hom σ y = y) →
      ∃ x : GroupPoints G.val (CommAlgCat.of k k),
        mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x = comparisonOnPoints e y)
    (hG : IsSemisimple P.pair.G) (hsc : GeometricallySimplyConnected P.pair.G)
    {N : OppositeBorel P.pair} {U : ClosedSubgroup P.pair.B.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U)
    (M : HighestWeightModules N U) (hweight : IsFundamental D M.weight)
    (htype : ExceptionalDiagram D outer) : MatchingOnPoints D l outer e M := by
  obtain ⟨n⟩ := simple_representatives_exist P D
  obtain ⟨blocks, hn, hall, hblocks, horth⟩ := exceptionalOrbitOrder D outer htype
  refine ⟨n, blocks, hn, hall, hblocks, horth, ?_⟩
  let R := CommAlgCat.of k S
  let tr := fun g i ↦ traceValue (M.representation i) R g
  let wrd := word n blocks R
  let a := fun σ : Gal(S/k) ↦ pinnedAction S (l (outer σ)).asIso.hom σ
  let π := fun σ : Gal(S/k) ↦ diagramPermutation D (outer σ)
  let scalars := fun (σ : Gal(S/k)) (c : S) ↦ σ c
  let changeParameters := fun σ ↦ permuteParameters (π σ) (scalars σ)
  have hw (σ : Gal(S/k)) (t : SimpleRoot P.pair → S) :
      a σ (wrd t) = wrd (changeParameters σ t) :=
    wordEquivariance D (outer σ) (l (outer σ)).asIso.hom (pinnedSequenceLifts E (outer σ))
      n blocks (hblocks σ) horth σ t
  have ht (σ : Gal(S/k)) (g : GroupPoints P.pair.G.val R) :
      tr (a σ g) = changeParameters σ (tr g) :=
    tracePermutation D (outer σ) (l (outer σ)).asIso.hom N U hU M
      (fundamentalWeightPermutation D (outer σ) (l (outer σ)).asIso.hom
        (pinnedSequenceLifts E (outer σ)) (simpleCorootCoordinates D hG hsc).1 M.weight hweight) σ g
  have hc (g z : GroupPoints P.pair.G.val R) : tr (z * g * z⁻¹) = tr g := by
    funext i
    exact traceConjugacy (M.representation i) R g z
  refine ⟨hw, ht, ?_⟩
  intro v hv hpre
  obtain ⟨t, ht₀, htf, hfix⟩ := fixedMatching π scalars a wrd tr hw ht hc v hv hpre
  obtain ⟨x, hx⟩ := descend (wrd t) hfix
  exact ⟨t, x, ht₀, htf, hx⟩

theorem referenceMatching : ReferenceMatching.{u} := by
  intro k S _ _ _ _ A P D l Q E ω V N U hG hsc hU M hw htype
  exact matchingOnPoints E V.trivialization (fun σ ↦ ω σ) (referenceDescent V)
    hG hsc hU M hw htype

end Matching

section FinitePinnedReference

open AutomorphismSequence (restrictIso scalarAut forgetPinning)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open AdjointCocharacters (coordinateHopfIso)
open private extendedGroupIso extendedSpecIso_hom_fst from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private inversePullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private hopfIsoEquiv hopfIsoEquiv_trans restrict_hopfIso hopfInduced_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
open private transportedDifference from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private pinnedHopfDifference relativeInversePullback conjugatesByTransportedDifference
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

set_option maxHeartbeats 2500000 in
theorem finiteReferenceComparison : FiniteReferenceComparison.{u} := by
  intro k S _ _ _ A P D l G B T V
  let t := extendedGroupIso (k := k) S
  let g := coordinateHopfIso P.pair.G
  let h := coordinateHopfIso G
  let j := hopfIsoEquiv t g h V.groupIso
  refine ⟨t, j, extendedSpecIso_hom_fst S, ?_, ?_⟩
  · exact (hopfInduced_iff t g h V.groupIso j).mpr rfl
  · intro σ
    let f := Functor.mapAut P (forgetPinning (A := A)) (l (V.outer σ))
    let b := inversePullback (K := S) (G := P.pair.G) f
    have hb : transportedDifference V.groupIso σ = b := pinnedHopfDifference V σ
    have hc : RelativeFormComparison.HopfConjugates σ V.groupIso (b.asIso ≪≫ V.groupIso) := by
      rw [← hb]
      exact conjugatesByTransportedDifference V.groupIso σ
    have hj := restrict_hopfIso t (extendedSpecIso_hom_fst S) g h σ hc
    apply Aut.ext
    change restrictIso (fieldMap k S σ) j ≪≫ j.symm = (scalarAut f (fieldTest k S)).asIso
    rw [hj, hopfIsoEquiv_trans t g g h, Iso.trans_assoc]
    change hopfIsoEquiv t g g b.asIso ≪≫ (j ≪≫ j.symm) = _
    rw [Iso.self_symm_id, Iso.trans_refl]
    exact relativeInversePullback (S := S) P.pair.G f

theorem finiteReferenceDescent : FiniteReferenceDescent.{u} := by
  intro k S _ _ _ _ A P D l G B T V
  obtain ⟨t, e, ht, hi, he⟩ := finiteReferenceComparison V
  exact ⟨t, e, ht, hi, fun y hy ↦ relativeDescent G e (fun σ ↦ l (V.outer σ)) he y hy⟩

theorem finiteReferenceMatching : FiniteReferenceMatching.{u} := by
  intro k S _ _ _ _ _ A P D l Q G B T V E N U hG hsc hU M hw htype
  obtain ⟨t, e, ht, hi, hd⟩ := finiteReferenceDescent V
  exact ⟨t, e, ht, hi, matchingOnPoints E e V.outer hd hG hsc hU M hw htype⟩

end FinitePinnedReference

end

end LinearAlgebraicGroups.Arithmetic.SteinbergPinnedDescent
