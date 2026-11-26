import Specs.LinearAlgebraicGroups.Classification.RankTwoLifting
import LinearAlgebraicGroups.Classification.CellHomomorphism
import LinearAlgebraicGroups.Classification.RankTwoRelations
import LinearAlgebraicGroups.Classification.RankOneRelations
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RankTwoRootSystems
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylChambersLength
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.RankTwoLifting

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CellHomomorphism (pullbackCharacters)
open Specs.CharacterDescent (Character)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.RankTwoLifting (Compatible MatchesPinning HasCentralTorusKernel MatchesRootGroups)
open Specs.RankTwoRelations (TypeOfRoots RootIndex)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.RootData (realRoot realRootSpan)
open LieAlgebrasAndRepresentations
open Set Module

noncomputable section

set_option linter.style.haveILetI false

private def kind (τ : TypeOfRoots) : RankTwoKind :=
  match τ with
  | .orthogonal => .A₁A₁
  | .a2 => .A₂
  | .b2 => .B₂
  | .g2 => .G₂

private def ofKind (κ : RankTwoKind) : TypeOfRoots :=
  match κ with
  | .A₁A₁ => .orthogonal
  | .A₂ => .a2
  | .B₂ => .b2
  | .G₂ => .g2

private def firstCartan : TypeOfRoots → ℤ
  | .orthogonal => 0
  | .a2 => -1
  | .b2 => -2
  | .g2 => -3

private def secondCartan : TypeOfRoots → ℤ
  | .orthogonal => 0
  | _ => -1

private theorem cartan_of_gram {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (τ : TypeOfRoots) (a b : V) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : rankTwoGram (kind τ) a b) :
    2 * inner ℝ b a / inner ℝ a a = (firstCartan τ : ℝ) ∧
      2 * inner ℝ a b / inner ℝ b b = (secondCartan τ : ℝ) := by
  rw [real_inner_comm a b]
  have haa := (inner_self_ne_zero (𝕜 := ℝ)).mpr ha
  have hbb := (inner_self_ne_zero (𝕜 := ℝ)).mpr hb
  cases τ <;> simp only [kind, rankTwoGram] at h
  all_goals
    constructor
    · apply (div_eq_iff haa).mpr
      norm_num only [firstCartan]
      linarith only [h]
    · apply (div_eq_iff hbb).mpr
      norm_num only [secondCartan]
      linarith only [h]

private theorem kind_ofKind (κ : RankTwoKind) : kind (ofKind κ) = κ := by
  cases κ <;> rfl

private theorem positiveLabel {τ : TypeOfRoots} {r : RootIndex}
    (hr : r ∈ RankTwoRelations.positiveList τ) :
    0 ≤ r.1 ∧ 0 ≤ r.2 ∧ 0 < r.1 + r.2 := by
  cases τ <;>
    simp [RankTwoRelations.positiveList] at hr <;>
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem mem_coefficients (τ : TypeOfRoots) (r : RootIndex) :
    r ∈ rankTwoCoefficients (kind τ) ↔ RankTwoRelations.IsIndex τ r := by
  have neg_mem (l : List RootIndex) :
      -r ∈ l ↔ r ∈ l.map Neg.neg := by
    rw [List.mem_map]
    exact ⟨fun h => ⟨-r, h, neg_neg r⟩, by
      rintro ⟨q, hq, h⟩
      rw [← h, neg_neg]
      exact hq⟩
  have neg_pair (x y : ℤ) : -(x, y) = (-x, -y) := rfl
  rw [RankTwoRelations.IsIndex, neg_mem]
  cases τ <;>
    simp only [kind, rankTwoCoefficients,
      RankTwoRelations.positiveList, RankTwoRelations.a, RankTwoRelations.b, RankTwoRelations.c,
      RankTwoRelations.d, RankTwoRelations.e, RankTwoRelations.f, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton, neg_pair,
      neg_zero] <;> tauto

private theorem model_in_chamber {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {R : Set V} (hR : IsRootSystem R) {z : V} (hz : RootRegular R z)
    (τ : TypeOfRoots) (hmodel : RankTwoModel R (kind τ)) :
    ∃ a ∈ simpleRoots R z, ∃ b ∈ simpleRoots R z,
      LinearIndependent ℝ ![a, b] ∧ rankTwoGram (kind τ) a b ∧
        R = rankTwoRootSet (kind τ) a b := by
  obtain ⟨a, ha, b, hb, hi, hspan, hgram, hset⟩ := hmodel
  let B : Basis (Fin 2) ℝ V := Basis.mk hi (by
    simpa only [Matrix.range_cons_cons_empty] using hspan.ge)
  have hBa : B 0 = a := congrFun (Basis.coe_mk hi _) 0
  have hBb : B 1 = b := congrFun (Basis.coe_mk hi _) 1
  letI : FiniteDimensional ℝ V := Module.Finite.of_basis B
  let ℓ : V →ₗ[ℝ] ℝ := B.constr ℝ (fun _ => 1)
  let v : V := (InnerProductSpace.toDual ℝ V).symm ℓ.toContinuousLinearMap
  have hva : ℓ a = 1 := by rw [← hBa]; exact Basis.constr_basis B ℝ _ _
  have hvb : ℓ b = 1 := by rw [← hBb]; exact Basis.constr_basis B ℝ _ _
  let coord : RootIndex → V := fun r => r.1 • a + r.2 • b
  have hcoord : Function.Injective coord := pair_coefficient_injective hi
  have hval (r : RootIndex) : inner ℝ v (coord r) = ((r.1 + r.2 : ℤ) : ℝ) := by
    rw [InnerProductSpace.toDual_symm_apply]
    change ℓ (r.1 • a + r.2 • b) = _
    simp [hva, hvb, Int.cast_add]
  have hmem (x : V) : x ∈ R ↔ ∃ r : RootIndex,
      RankTwoRelations.IsIndex τ r ∧ coord r = x := by
    rw [hset]
    simp only [rankTwoRootSet, mem_image, Finset.mem_coe, mem_coefficients, coord]
  have hv : RootRegular R v := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (hmem x).mp hx
    rw [hval, Int.cast_ne_zero]
    rcases hr with hp | hn
    · exact (positiveLabel hp).2.2.ne'
    · have hp := (positiveLabel hn).2.2
      change 0 < -r.1 + -r.2 at hp
      omega
  have coord_pos {x : V} (hx : x ∈ positiveRoots R v) :
      ∃ r ∈ RankTwoRelations.positiveList τ, coord r = x := by
    obtain ⟨r, h | h, rfl⟩ := (hmem x).mp hx.1
    · exact ⟨r, h, rfl⟩
    · have hp := (positiveLabel h).2.2
      change 0 < -r.1 + -r.2 at hp
      have hn := hx.2
      rw [hval, Int.cast_pos] at hn
      omega
  have csimple (r : RootIndex) (hr : RankTwoRelations.IsIndex τ r)
      (ht : r.1 + r.2 = 1) : coord r ∈ simpleRoots R v := by
    refine ⟨⟨(hmem _).mpr ⟨r, hr, rfl⟩, by simp [hval, ht]⟩, ?_⟩
    intro x hx y hy he
    obtain ⟨p, hp, rfl⟩ := coord_pos hx
    obtain ⟨q, hq, rfl⟩ := coord_pos hy
    have hsum : coord (p + q) = coord p + coord q := by
      simp only [coord, Prod.fst_add, Prod.snd_add, add_zsmul]
      abel
    have he' := hcoord (he.trans hsum.symm)
    have hp' := (positiveLabel hp).2.2
    have hq' := (positiveLabel hq).2.2
    have h1 := congrArg Prod.fst he'
    have h2 := congrArg Prod.snd he'
    change r.1 = p.1 + q.1 at h1
    change r.2 = p.2 + q.2 at h2
    omega
  have haS : a ∈ simpleRoots R v := by
    simpa [coord, RankTwoRelations.a] using
      csimple RankTwoRelations.a (Or.inl (by cases τ <;> simp [RankTwoRelations.positiveList])) (by decide)
  have hbS : b ∈ simpleRoots R v := by
    simpa [coord, RankTwoRelations.b] using
      csimple RankTwoRelations.b (Or.inl (by cases τ <;> simp [RankTwoRelations.positiveList])) (by decide)
  obtain ⟨w, hw⟩ := exists_weyl_into_simpleChamber hR hv hz
  let e := w.val.symm
  have heR (x : V) : e x ∈ R ↔ x ∈ R :=
    (rootWeylGroup_mem_iff hR.toRootAxioms ((rootWeylGroup R).inv_mem w.property) x).symm
  have heInner (x y : V) : inner ℝ (e x) (e y) = inner ℝ x y :=
    rootWeylGroup_inner ((rootWeylGroup R).inv_mem w.property) x y
  have hinner (x : V) : inner ℝ z (e x) = inner ℝ (w.val z) x := by
    have h := rootWeylGroup_inner w.property z (e x)
    rw [show w.val (e x) = x from w.val.apply_symm_apply x] at h
    exact h.symm
  have hsimple {x : V} (hx : x ∈ simpleRoots R v) : e x ∈ simpleRoots R z := by
    refine ⟨⟨(heR x).mpr hx.1.1, by rw [hinner]; exact hw x hx⟩, ?_⟩
    intro y hy t ht he
    have hchamberPos (q : V) (hq : q ∈ positiveRoots R z) :
        w.val q ∈ positiveRoots R v := by
      have hqr := (rootWeylGroup_mem_iff hR.toRootAxioms w.property q).mp hq.1
      refine ⟨hqr, ?_⟩
      rcases positive_or_neg_positive hR.toRootAxioms hv hqr with hp | hn
      · exact hp.2
      · have hn' := simpleChamber_pairing_positive hR.toRootAxioms hw hn
        rw [inner_neg_right, rootWeylGroup_inner w.property] at hn'
        exact False.elim (not_lt_of_ge hq.2.le (neg_pos.mp hn'))
    apply hx.2 (w.val y) (hchamberPos y hy) (w.val t) (hchamberPos t ht)
    simpa only [e, LinearEquiv.apply_symm_apply, map_add] using congrArg w.val he
  refine ⟨e a, hsimple haS, e b, hsimple hbS, ?_, ?_, ?_⟩
  · have he : (e.toLinearMap ∘ ![a, b]) = ![e a, e b] := by
      ext i
      fin_cases i <;> rfl
    exact he ▸ hi.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  · cases τ <;> simpa only [kind, rankTwoGram, heInner] using hgram
  · ext x
    constructor
    · intro hx
      have hx' := (rootWeylGroup_mem_iff hR.toRootAxioms w.property x).mp hx
      obtain ⟨r, hr, hrc⟩ := (hmem _).mp hx'
      refine ⟨r, (mem_coefficients τ r).mpr hr, ?_⟩
      simpa only [coord, map_add, map_zsmul, e, LinearEquiv.symm_apply_apply] using congrArg e hrc
    · rintro ⟨r, hr, rfl⟩
      have hrc := (hmem (coord r)).mpr ⟨r, (mem_coefficients τ r).mp hr, rfl⟩
      simpa only [coord, map_add, map_zsmul] using (heR _).mpr hrc


variable {k : Type u} [Field k] {A : AdditiveLine k}

private theorem positive_transfer {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ) :
    letI := D.comm; letI := E.comm; ∀ α, D.base.IsPos α ↔ E.base.IsPos (d α) := by
  letI := D.comm
  letI := E.comm
  letI := D.datum.finiteRoots
  letI := E.datum.finiteRoots
  let L := (pullbackCharacters τ).toAdditive.toIntLinearMap
  have hL : Function.Injective L := h.injective
  have hroot (i : Root P.pair.T) :
      L (E.datum.rootDatum.root (d i)) = D.datum.rootDatum.root i := by
    rw [D.datum.root_eq, E.datum.root_eq]
    exact congrArg Additive.ofMul (h.root i)
  have hs (i : Root Q.pair.T) :
      L (E.datum.rootDatum.root i) = D.datum.rootDatum.root (d.symm i) := by
    simpa only [Equiv.apply_symm_apply] using hroot (d.symm i)
  intro α
  constructor
  · intro hα
    refine hα.induction_on_add (p := fun i => E.base.IsPos (d i)) ?_ ?_
    · intro i hi
      exact E.base.isPos_of_mem_support ((h.simple i).mp hi)
    · intro i j l he hi hj
      apply hi.add (E.base.isPos_of_mem_support ((h.simple j).mp hj))
      apply hL
      simpa only [map_add, hroot] using he
  · have aux (i : Root Q.pair.T) (hi : E.base.IsPos i) : D.base.IsPos (d.symm i) := by
      refine hi.induction_on_add (p := fun i => D.base.IsPos (d.symm i)) ?_ ?_
      · intro i hi
        apply D.base.isPos_of_mem_support
        apply (h.simple (d.symm i)).mpr
        simpa only [Equiv.apply_symm_apply] using hi
      · intro i j l he hi hj
        apply hi.add (D.base.isPos_of_mem_support ((h.simple (d.symm j)).mpr (by simpa using hj)))
        simpa only [map_add, hs] using congrArg L he
    intro hi
    simpa only [Equiv.symm_apply_apply] using aux (d α) hi

open private latticeEmbedding_injective from LinearAlgebraicGroups.RootData.EuclideanComparison

/-- The exact signed coefficient lists in the ordered simple roots of the
given Borel, obtained from the Euclidean rank-two classification. -/
private theorem rankTwoFrame_cartan (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hrank : letI := D.comm; D.base.support.card = 2) :
    letI := D.comm
    ∃ (τ : TypeOfRoots) (F : RankTwoRelations.Frame P τ),
      D.datum.rootDatum.pairing F.second.val F.first.val = firstCartan τ ∧
      D.datum.rootDatum.pairing F.first.val F.second.val = secondCartan τ := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.finiteCocharacters
  letI := D.datum.reduced
  let L := D.datum.rootDatum
  let V := realRootSpan L
  let R := Set.range (realRoot L)
  obtain ⟨_, _, _, _, _, metric, _, hcoroot, _, hR, z, B, hz, _, _, hB, hbase, _, _, _⟩ :=
    RootData.euclideanComparison L D.base
  letI : NormedAddCommGroup V := metric.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore metric.toCore
  have hdim : Module.finrank ℝ V = 2 := by
    rw [Module.finrank_eq_card_basis B]
    simpa using hrank
  obtain ⟨κ, hκ, _⟩ := rank_two_classification R hR hdim
  let τ := ofKind κ
  have hk : kind τ = κ := kind_ofKind κ
  obtain ⟨a, ha, b, hb, hab, hgram, hset⟩ := model_in_chamber hR hz τ (hk.symm ▸ hκ)
  obtain ⟨i, hi⟩ := hbase.symm ▸ ha
  obtain ⟨j, hj⟩ := hbase.symm ▸ hb
  let α : Root P.pair.T := i
  let β : Root P.pair.T := j
  have hα : realRoot L α = a := (hB i).symm.trans hi
  have hβ : realRoot L β = b := (hB j).symm.trans hj
  let f : RootIndex → Character P.pair.T.group := fun r => α.val ^ r.1 * β.val ^ r.2
  let q := TensorProduct.mk ℤ ℝ (Additive (Character P.pair.T.group)) 1
  have hq : Function.Injective q := latticeEmbedding_injective
  have hf (r : RootIndex) :
      q (Additive.ofMul (f r)) =
        (realRootSpan L).subtype (r.1 • a + r.2 • b) := by
    have hroot (root : Root P.pair.T) :
        q (Additive.ofMul root.val) = (realRootSpan L).subtype (realRoot L root) := by
      change q (Additive.ofMul root.val) = q (L.root root)
      rw [D.datum.root_eq]
    change q (r.1 • Additive.ofMul α.val + r.2 • Additive.ofMul β.val) = _
    simp only [map_add, map_zsmul, hroot, hα, hβ]
  have hc := cartan_of_gram τ a b (hR.nonzero a ha.1.1) (hR.nonzero b hb.1.1) hgram
  have hc₁ : L.pairing β α = firstCartan τ := by
    apply (Int.cast_injective (α := ℝ))
    rw [← RootData.realCoroot_apply_root, hcoroot, hα, hβ]
    exact hc.1
  have hc₂ : L.pairing α β = secondCartan τ := by
    apply (Int.cast_injective (α := ℝ))
    rw [← RootData.realCoroot_apply_root, hcoroot, hα, hβ]
    exact hc.2
  refine ⟨τ, ⟨⟨α, (D.simple_iff α).mp i.property⟩,
    ⟨β, (D.simple_iff β).mp j.property⟩, ?_, ?_⟩, hc₁, hc₂⟩
  · intro p r he
    apply pair_coefficient_injective hab
    apply (realRootSpan L).injective_subtype
    rw [← hf, ← hf, show f p = f r from he]
  · intro χ
    constructor
    · intro hχ
      let root : Root P.pair.T := ⟨χ, hχ⟩
      have hm : realRoot L root ∈ Set.range (realRoot L) := Set.mem_range_self root
      rw [hset] at hm
      obtain ⟨r, hr, he⟩ := hm
      refine ⟨⟨r, (mem_coefficients τ r).mp hr⟩, ?_⟩
      change χ = f r
      apply Additive.ofMul.injective
      apply hq
      change r.1 • a + r.2 • b = realRoot L root at he
      rw [hf, he]
      change q (Additive.ofMul χ) = q (L.root root)
      rw [D.datum.root_eq]
    · rintro ⟨r, hr⟩
      have hm : r.val.1 • a + r.val.2 • b ∈ Set.range (realRoot L) := by
        rw [hset]
        exact ⟨r, (mem_coefficients τ r).mpr r.property, rfl⟩
      obtain ⟨root, hroot⟩ := hm
      have he : root.val = f r := by
        apply Additive.ofMul.injective
        apply hq
        rw [hf, ← hroot]
        change q (Additive.ofMul root.val) = q (L.root root)
        rw [D.datum.root_eq]
      change χ = f r at hr
      rw [hr, ← he]
      exact root.property

theorem rankTwoFrame (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hrank : letI := D.comm; D.base.support.card = 2) :
    ∃ τ : TypeOfRoots, Nonempty (RankTwoRelations.Frame P τ) := by
  obtain ⟨τ, F, _, _⟩ := rankTwoFrame_cartan P D hrank
  exact ⟨τ, ⟨F⟩⟩

/-- A based character injection transports the frame, with the same short
root first and the same signed coefficient list. -/
def transportFrame {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ)
    {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ) : RankTwoRelations.Frame Q κ where
  first := ⟨d F.first.val, (E.simple_iff _).mp
    ((h.simple _).mp ((D.simple_iff _).mpr F.first.property))⟩
  second := ⟨d F.second.val, (E.simple_iff _).mp
    ((h.simple _).mp ((D.simple_iff _).mpr F.second.property))⟩
  independent := by
    intro p q he
    apply F.independent
    have h' := congrArg (pullbackCharacters τ) he
    simpa only [map_mul, map_zpow, show ∀ i, pullbackCharacters τ (d i).val = i.val from h.root] using h'
  root_iff := by
    intro χ
    constructor
    · intro hχ
      let β : Root Q.pair.T := ⟨χ, hχ⟩
      let α := d.symm β
      obtain ⟨r, hr⟩ := (F.root_iff _).mp α.property
      refine ⟨r, h.injective ?_⟩
      simp only [map_mul, map_zpow, show ∀ i, pullbackCharacters τ (d i).val = i.val from h.root]
      change pullbackCharacters τ β.val = _
      rw [← d.apply_symm_apply β]
      exact (h.root α).trans hr
    · rintro ⟨r, hr⟩
      have hχ : χ = (d (F.root r)).val := by
        apply h.injective
        rw [hr]
        change pullbackCharacters τ ((d F.first.val).val ^ r.val.1 *
          (d F.second.val).val ^ r.val.2) = pullbackCharacters τ (d (F.root r)).val
        simp only [map_mul, map_zpow, show ∀ i, pullbackCharacters τ (d i).val = i.val from h.root]
        rfl
      exact hχ ▸ (d (F.root r)).property


section SignedCommutators

open Specs.RankTwoRelations (TypeOfRoots RootIndex Index Correction
  a b c d e f positiveList IsIndex correctionTable actionSign reflection wordAction)


private def wordValue {R H : Type*} [CommRing R] [Group H] (xroot : RootIndex → R → H)
    (x y : R) (L : List Correction) : H :=
  (L.map fun t => xroot t.root
    ((t.coefficient : R) * x ^ t.leftDegree * y ^ t.rightDegree)).prod

private def reverseSign (t : Correction) : ℤ := (-1) ^ t.rightDegree * t.coefficient

private def commutatorTable (τ : TypeOfRoots) (r s : RootIndex) : List Correction :=
  if (positiveList τ).idxOf r < (positiveList τ).idxOf s then
    ((correctionTable τ r s).map fun t => { t with coefficient := -reverseSign t }).reverse
  else
    (correctionTable τ s r).map fun t =>
      ⟨t.root, t.rightDegree, t.leftDegree, reverseSign t⟩

private theorem wordValue_reverseSign {R H : Type*} [CommRing R] [Group H]
    (p : RootIndex → R → H) (L : List Correction) (x y : R) :
    wordValue p y x (L.map fun t => ⟨t.root, t.rightDegree, t.leftDegree, reverseSign t⟩) =
      wordValue p x (-y) L := by
  unfold wordValue
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  dsimp [reverseSign]
  push_cast
  rw [show -y = (-1 : R) * y by simp, mul_pow]
  congr 1
  ring

private theorem wordValue_neg_reverseSign {R H : Type*} [CommRing R] [Group H]
    (p : RootIndex → R → H) (hp : ∀ r z, p r (-z) = (p r z)⁻¹)
    (L : List Correction) (x y : R) :
    wordValue p x y ((L.map fun t => { t with coefficient := -reverseSign t }).reverse) =
      (wordValue p x (-y) L)⁻¹ := by
  unfold wordValue
  rw [List.map_reverse, List.prod_inv_reverse, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro t _
  dsimp [reverseSign]
  rw [← hp]
  push_cast
  rw [show -y = (-1 : R) * y by simp, mul_pow]
  congr 1
  ring

private theorem positive_commutator {R H : Type*} [CommRing R] [Group H]
    (τ : TypeOfRoots) (p : RootIndex → R → H) (hp : ∀ r z, p r (-z) = (p r z)⁻¹)
    (hpos : ∀ r s : RootIndex, r ∈ positiveList τ → s ∈ positiveList τ →
      (positiveList τ).idxOf r < (positiveList τ).idxOf s → ∀ x y : R,
        p r x * p s y * p r (-x) = p s y * wordValue p x y (correctionTable τ r s))
    {r s : RootIndex} (hr : r ∈ positiveList τ) (hs : s ∈ positiveList τ) (hne : r ≠ s)
    (x y : R) :
    p r x * p s y * (p r x)⁻¹ * (p s y)⁻¹ = wordValue p x y (commutatorTable τ r s) := by
  have ordered (i j : RootIndex) (hi : i ∈ positiveList τ) (hj : j ∈ positiveList τ)
      (hij : (positiveList τ).idxOf i < (positiveList τ).idxOf j) (z w : R) :
      p i z * p j w * (p i z)⁻¹ * (p j w)⁻¹ =
        (wordValue p z (-w) (correctionTable τ i j))⁻¹ := by
    have he := congrArg Inv.inv (hpos i j hi hj hij z (-w))
    simp only [hp, mul_inv_rev, inv_inv] at he
    rw [mul_assoc (p i z) (p j w) ((p i z)⁻¹), he, mul_inv_cancel_right]
  unfold commutatorTable
  split_ifs with h
  · rw [wordValue_neg_reverseSign p hp]
    exact ordered r s hr hs h x y
  · have hlt : (positiveList τ).idxOf s < (positiveList τ).idxOf r :=
      lt_of_le_of_ne (Nat.le_of_not_gt h) (fun hh => hne ((List.idxOf_inj hr).mp hh.symm))
    have he := congrArg Inv.inv (ordered s r hs hr hlt y x)
    simp only [mul_inv_rev, inv_inv] at he
    rw [wordValue_reverseSign]
    simpa only [mul_assoc] using he

private def ValidCorrection (τ : TypeOfRoots) (r s : RootIndex) (t : Correction) : Prop :=
  IsIndex τ t.root ∧ 0 < t.leftDegree ∧ 0 < t.rightDegree ∧
    t.root = t.leftDegree • r + t.rightDegree • s

local instance (τ : TypeOfRoots) (r : RootIndex) : Decidable (IsIndex τ r) :=
  inferInstanceAs (Decidable (_ ∈ positiveList τ ∨ -r ∈ positiveList τ))

local instance (τ : TypeOfRoots) (r s : RootIndex) (t : Correction) :
    Decidable (ValidCorrection τ r s t) :=
  inferInstanceAs (Decidable (IsIndex τ t.root ∧ 0 < t.leftDegree ∧ 0 < t.rightDegree ∧
    t.root = t.leftDegree • r + t.rightDegree • s))

private theorem correctionTable_valid (τ : TypeOfRoots) (r s : RootIndex) :
    ∀ t ∈ correctionTable τ r s, ValidCorrection τ r s t := by
  classical
  unfold correctionTable
  split_ifs with hab hac hg had hbe hcd
  · obtain ⟨rfl, rfl⟩ := hab
    cases τ <;> decide
  · obtain ⟨rfl, rfl⟩ := hac
    cases τ <;> decide
  · obtain ⟨rfl, rfl⟩ := had
    subst τ
    decide
  · obtain ⟨rfl, rfl⟩ := hbe
    subst τ
    decide
  · obtain ⟨rfl, rfl⟩ := hcd
    subst τ
    decide
  all_goals simp

private theorem commutatorTable_valid (τ : TypeOfRoots) (r s : RootIndex) :
    ∀ t ∈ commutatorTable τ r s, ValidCorrection τ r s t := by
  intro t ht
  unfold commutatorTable at ht
  split_ifs at ht
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ht)
    exact correctionTable_valid τ r s v hv
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hroot, hi, hj, he⟩ := correctionTable_valid τ s r v hv
    exact ⟨hroot, hj, hi, he.trans (add_comm _ _)⟩

private theorem reflection_involutive (τ : TypeOfRoots) (i : Bool) :
    Function.Involutive (reflection τ i) := by
  intro r
  cases i <;> apply Prod.ext <;> simp [RankTwoRelations.reflection]

private def reflectionEquiv (τ : TypeOfRoots) (i : Bool) : RootIndex ≃+ RootIndex where
  toFun := reflection τ i
  invFun := reflection τ i
  left_inv := reflection_involutive τ i
  right_inv := reflection_involutive τ i
  map_add' := by
    intro r s
    cases i <;> cases τ <;> apply Prod.ext <;> simp [RankTwoRelations.reflection] <;> ring

private theorem reflectionEquiv_apply (τ : TypeOfRoots) (i : Bool) (r : RootIndex) :
    reflectionEquiv τ i r = reflection τ i r := rfl

private theorem reflection_mem (τ : TypeOfRoots) (i : Bool) {r : RootIndex}
    (hr : IsIndex τ r) : IsIndex τ (reflection τ i r) := by
  have h : ∀ t ∈ positiveList τ, IsIndex τ (reflection τ i t) ∧ IsIndex τ (reflection τ i (-t)) := by
    cases τ <;> cases i <;> decide
  rcases hr with hr | hr
  · exact (h _ hr).1
  · simpa only [neg_neg] using (h _ hr).2

private def labelAction (τ : TypeOfRoots) : List Bool → RootIndex ≃+ RootIndex
  | [] => AddEquiv.refl _
  | i :: w => (labelAction τ w).trans (reflectionEquiv τ i)

private theorem labelAction_mem (τ : TypeOfRoots) (w : List Bool) {r : RootIndex}
    (hr : IsIndex τ r) : IsIndex τ (labelAction τ w r) := by
  induction w with
  | nil => exact hr
  | cons i w ih => exact reflection_mem τ i ih

private theorem labelAction_symm_mem (τ : TypeOfRoots) (w : List Bool) {r : RootIndex}
    (hr : IsIndex τ r) : IsIndex τ ((labelAction τ w).symm r) := by
  induction w generalizing r with
  | nil => exact hr
  | cons i w ih => exact ih (reflection_mem τ i hr)

private def wordSign (τ : TypeOfRoots) : List Bool → RootIndex → ℤ
  | [], _ => 1
  | i :: w, r => actionSign τ i (labelAction τ w r) * wordSign τ w r

private theorem wordAction_eq (τ : TypeOfRoots) (w : List Bool) (r : RootIndex) (ε : ℤ) :
    wordAction τ w r ε = (labelAction τ w r, wordSign τ w r * ε) := by
  induction w with
  | nil => simp [wordAction, labelAction, wordSign]
  | cons i w ih =>
    rw [wordAction, List.foldr_cons, ← wordAction, ih]
    simp only [labelAction, AddEquiv.trans_apply, reflectionEquiv_apply, wordSign, mul_assoc]

private theorem actionSign_sq (τ : TypeOfRoots) (i : Bool) (r : RootIndex) :
    actionSign τ i r ^ 2 = 1 := by
  unfold actionSign
  split_ifs <;> norm_num

private theorem wordSign_sq (τ : TypeOfRoots) (w : List Bool) (r : RootIndex) :
    wordSign τ w r ^ 2 = 1 := by
  induction w with
  | nil => simp [wordSign]
  | cons i w ih => simp [wordSign, mul_pow, actionSign_sq, ih]

private theorem conjugate_word {R H : Type*} [CommRing R] [Group H]
    (τ : TypeOfRoots) (p : RootIndex → R → H) (n : Bool → H)
    (hact : ∀ i r, IsIndex τ r → ∀ z,
      MulAut.conj (n i) (p r z) = p (reflection τ i r) ((actionSign τ i r : R) * z))
    (w : List Bool) {r : RootIndex} (hr : IsIndex τ r) (z : R) :
    MulAut.conj ((w.map n).prod) (p r z) =
      p (labelAction τ w r) ((wordSign τ w r : R) * z) := by
  induction w with
  | nil => simp [labelAction, wordSign]
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, map_mul, MulAut.mul_apply, ih,
      hact i _ (labelAction_mem τ w hr)]
    simp only [labelAction, AddEquiv.trans_apply, reflectionEquiv_apply, wordSign, Int.cast_mul,
      mul_assoc]

private def transportCorrection (τ : TypeOfRoots) (w : List Bool) (r s : RootIndex)
    (t : Correction) : Correction :=
  let q := (labelAction τ w).symm t.root
  ⟨q, t.leftDegree, t.rightDegree, wordSign τ w q * t.coefficient *
    wordSign τ w r ^ t.leftDegree * wordSign τ w s ^ t.rightDegree⟩

private theorem transportCorrection_valid (τ : TypeOfRoots) (w : List Bool) (r s : RootIndex)
    (t : Correction) (h : ValidCorrection τ (labelAction τ w r) (labelAction τ w s) t) :
    ValidCorrection τ r s (transportCorrection τ w r s t) := by
  have he := congrArg (labelAction τ w).symm h.2.2.2
  simp only [map_add, map_nsmul, AddEquiv.symm_apply_apply] at he
  exact ⟨labelAction_symm_mem τ w h.1, h.2.1, h.2.2.1, he⟩

private def signedTable (τ : TypeOfRoots) (w : List Bool) (r s : RootIndex) : List Correction :=
  (commutatorTable τ (labelAction τ w r) (labelAction τ w s)).map
    (transportCorrection τ w r s)

private theorem signedTable_valid (τ : TypeOfRoots) (w : List Bool) (r s : RootIndex) :
    ∀ t ∈ signedTable τ w r s, ValidCorrection τ r s t := by
  intro t ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  exact transportCorrection_valid τ w r s _ (commutatorTable_valid _ _ _ _ hv)

private theorem signed_commutator {R H : Type*} [CommRing R] [Group H]
    (τ : TypeOfRoots) (p : RootIndex → R → H) (n : Bool → H)
    (hp : ∀ r z, p r (-z) = (p r z)⁻¹)
    (hpos : ∀ r s : RootIndex, r ∈ positiveList τ → s ∈ positiveList τ →
      (positiveList τ).idxOf r < (positiveList τ).idxOf s → ∀ x y : R,
        p r x * p s y * p r (-x) = p s y * wordValue p x y (correctionTable τ r s))
    (hact : ∀ i r, IsIndex τ r → ∀ z,
      MulAut.conj (n i) (p r z) = p (reflection τ i r) ((actionSign τ i r : R) * z))
    (w : List Bool) {r s : RootIndex} (hr : IsIndex τ r) (hs : IsIndex τ s)
    (hne : r ≠ s) (hwr : labelAction τ w r ∈ positiveList τ)
    (hws : labelAction τ w s ∈ positiveList τ) (x y : R) :
    p r x * p s y * (p r x)⁻¹ * (p s y)⁻¹ = wordValue p x y (signedTable τ w r s) := by
  let g := MulAut.conj ((w.map n).prod)
  have hg (t : RootIndex) (ht : IsIndex τ t) (z : R) :
      g (p t z) = p (labelAction τ w t) ((wordSign τ w t : R) * z) :=
    conjugate_word τ p n hact w ht z
  apply g.injective
  simp only [map_mul, map_inv, hg r hr, hg s hs]
  rw [positive_commutator τ p hp hpos hwr hws ((labelAction τ w).injective.ne hne)]
  unfold wordValue signedTable
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  let q := (labelAction τ w).symm t.root
  have hq : IsIndex τ q :=
    labelAction_symm_mem τ w (commutatorTable_valid _ _ _ _ ht).1
  have hsq : (wordSign τ w q : R) ^ 2 = 1 := by
    simpa only [Int.cast_pow, Int.cast_one] using
      congrArg (fun z : ℤ => (z : R)) (wordSign_sq τ w q)
  have hqLabel : labelAction τ w q = t.root := (labelAction τ w).apply_symm_apply t.root
  simp only [Function.comp_apply, transportCorrection, ← show q = (labelAction τ w).symm t.root from rfl,
    hg q hq, hqLabel]
  congr 1
  push_cast
  rw [mul_pow, mul_pow]
  linear_combination -((t.coefficient : R) * (wordSign τ w r : R) ^ t.leftDegree *
    (wordSign τ w s : R) ^ t.rightDegree * x ^ t.leftDegree * y ^ t.rightDegree) * hsq

end SignedCommutators

open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue absoluteRoots)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot RootCoordinate IsSimple)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction
  Proportional rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private coroot_functional_of_reflection from LinearAlgebraicGroups.Classification.Pinning
open private inducedConjugation_unique from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private rootPoint_neg torusPointHom torusPointHom_apply word_eq_torus_mul
  representative_eq_word from LinearAlgebraicGroups.Classification.RankOneRelations
open private rankOneRepresentative rankOneRepresentative_point cocharacterPoint_inv
  from LinearAlgebraicGroups.RootData.RootGroups


set_option backward.isDefEq.respectTransparency false

private def oppositeRoot {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (α : Root T) : Root T :=
  D.rootDatum.reflectionPerm α α

private theorem oppositeRoot_val {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (α : Root T) :
    (oppositeRoot D α).val = α.val⁻¹ := by
  apply Additive.ofMul.injective
  rw [← D.root_eq, ofMul_inv, ← D.root_eq]
  exact D.rootDatum.root_eq_neg_iff.mpr rfl

private theorem oppositeRoot_oppositeRoot {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (α : Root T) :
    oppositeRoot D (oppositeRoot D α) = α := by
  apply Subtype.ext
  rw [oppositeRoot_val, oppositeRoot_val, inv_inv]

private theorem positive_opposite_iff {P : Specs.Pinning.SplitBorelPair k} (D : AttachedDatum P)
    (α : Root P.T) :
    letI := D.comm
    D.base.IsPos (oppositeRoot D.datum α) ↔ ¬ D.base.IsPos α := by
  letI := D.comm
  exact RootPairing.Base.IsPos.neg_iff_not D.base α

private theorem base_isPos_iff_subgroupRoots {P : Specs.Pinning.SplitBorelPair k}
    (D : AttachedDatum P) :
    letI := D.comm
    ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.T P.B := by
  letI := D.comm
  letI := D.datum.finiteRoots
  obtain ⟨c, _, _, _, hc⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let f := Specs.SimpleRoots.evaluate D.datum c
  have hf (i : Root P.T) : f (D.datum.rootDatum.root i) = pairing P.T.group i.val c := by
    change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  have hsimple (i : Root P.T) (hi : i ∈ D.base.support) : 0 < f (D.datum.rootDatum.root i) := by
    rw [hf]
    change i ∈ Specs.BorelsAndChambers.positiveRoots P.T c
    rw [← hc]
    exact ((D.simple_iff i).mp hi).1
  have hpositive (i : Root P.T) (hi : D.base.IsPos i) : 0 < f (D.datum.rootDatum.root i) := by
    refine hi.induction_on_add hsimple ?_
    intro j l m hm hj hl
    rw [hm, map_add]
    exact add_pos hj (hsimple l hl)
  intro i
  rw [hc]
  change D.base.IsPos i ↔ 0 < pairing P.T.group i.val c
  rw [← hf]
  refine ⟨hpositive i, ?_⟩
  intro hi
  by_contra hn
  have hop := hpositive _ ((positive_opposite_iff D i).mpr hn)
  have he : D.datum.rootDatum.root (oppositeRoot D.datum i) = -D.datum.rootDatum.root i :=
    D.datum.rootDatum.root_eq_neg_iff.mpr rfl
  rw [he, map_neg] at hop
  exact (not_lt_of_ge hi.le) (neg_pos.mp hop)

private theorem coroot_pairing {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (α β : Root T) :
    pairing T.group α.val (Additive.toMul (D.rootDatum.coroot β)) =
      D.rootDatum.pairing α β := by
  rw [← D.pairing_eq, ← D.root_eq, ofMul_toMul, D.rootDatum.root_coroot_eq_pairing]

/-- The attached coroot is forced by any linked word inducing the rank-one
reflection in the actual normalizer action. -/
private theorem linked_coroot {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (α : Root T)
    {x y : A.group ⟶ G.val} (r : CorootReflection T α.val x y) :
    r.coroot = Additive.toMul (D.rootDatum.coroot α) := by
  obtain ⟨N, hN, act, hact⟩ := D.normalizerAction
  obtain ⟨n, hn⟩ := (hN _ r.representative).mp r.normalizes
  obtain ⟨e, he, heWeight, _⟩ := hact n
  have he' : InducesTorusConjugation T r.representative e := by
    simpa only [InducesTorusConjugation, ← Category.assoc, hn, Category.assoc] using he
  have heq := inducedConjugation_unique he' r.conjugates
  let p := D.rootDatum.toLinearMap.flip (Additive.ofMul r.coroot)
  have hp : p (D.rootDatum.root α) = 2 := by
    change D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul r.coroot) = 2
    rw [D.root_eq, D.pairing_eq, r.root_pairing]
  have hweight (x : Additive (Character T.group)) :
      (act n).weightEquiv x = x - p x • D.rootDatum.root α := by
    change (act n).weightEquiv (Additive.ofMul x.toMul) = _
    rw [heWeight, heq, r.reflection, D.root_eq]
    have hx : p x = pairing T.group x.toMul r.coroot := D.pairing_eq x.toMul r.coroot
    rw [hx, ofMul_mul, ofMul_zpow, neg_smul, sub_eq_add_neg]
    rfl
  have h := coroot_functional_of_reflection D.rootDatum α (act n) p hp hweight
  apply Additive.ofMul.injective
  change Additive.ofMul r.coroot = D.rootDatum.coroot α
  apply D.rootDatum.flip.toPerfPair.injective
  exact h.symm

private theorem word_swap {G : AffineAlgebraicGroup k} (hG : Specs.GeometricRadicals.IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (α : Root T) {x y : A.group ⟶ G.val} (r : CorootReflection T α.val x y)
    (hx : HasScalarAction T α.val x) (hy : HasScalarAction T α.val⁻¹ y)
    (hpair : pairing T.group α.val⁻¹ r.coroot = -2) (R : TestAlgebra k) (b : Rˣ) :
    rankOneWord y x R b = rankOneWord x y R (-b⁻¹) := by
  let t := -b⁻¹
  let n := rankOneWord x y R 1
  let h := torusPointHom T r.coroot R t
  let w := rankOneWord x y R t
  let p := rootPoint x R (t : R)
  let q := rootPoint y R (b : R)
  have hright : (-(↑t⁻¹ : R)) = (b : R) := by
    simp [t]
  have hn : n * p * n⁻¹ = rootPoint y R (-(t : R)) := by
    have hn' := (RankOneRelations.oppositeRootRelations G hG T hT hmax α.val α.property
      x y r hx hy R).2.2 (t : R)
    rw [representative_eq_word r R] at hn'
    exact hn'
  have hh := hy R (cocharacterPoint r.coroot R t) (-(t : R))
  have hval := (RootData.CharacterPairing.characterPairingComposition T.group α.val⁻¹ r.coroot).2 R t
  rw [hpair] at hval
  have hparam : characterValue α.val⁻¹ R (cocharacterPoint r.coroot R t) * -(t : R) =
      (b : R) := by
    rw [hval, show (-2 : ℤ) = -(2 : ℤ) by decide, zpow_neg, zpow_ofNat, ← inv_pow,
      Units.val_pow_eq_pow_val, pow_two, mul_neg, mul_assoc, Units.inv_mul, mul_one, hright]
  have hscale : h * rootPoint y R (-(t : R)) * h⁻¹ = q := by
    change torusPointHom T r.coroot R t * rootPoint y R (-(t : R)) *
      (torusPointHom T r.coroot R t)⁻¹ = _
    rw [torusPointHom_apply]
    simpa only [hparam] using hh
  have hw : w = h * n := word_eq_torus_mul r R t
  have hc : w * p * w⁻¹ = q := by
    rw [hw, show (h * n) * p * (h * n)⁻¹ = h * (n * p * n⁻¹) * h⁻¹ by group, hn, hscale]
  have hw' : w = p * q * p := by
    change rootPoint x R (t : R) * rootPoint y R (-(↑t⁻¹ : R)) *
      rootPoint x R (t : R) = _
    rw [hright]
  have hqp := congrArg (fun m => m * p⁻¹) (mul_inv_eq_iff_eq_mul.mp hc)
  rw [hw'] at hqp
  change q * p * q = w
  rw [hw']
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hqp.symm

private theorem word_quotient {G : GroupScheme k} {T : ClosedSubgroup G}
    {χ : Character T.group} {x y : A.group ⟶ G}
    (r : CorootReflection T χ x y) (R : TestAlgebra k) (b c : Rˣ) :
    rankOneWord x y R b * (rankOneWord x y R c)⁻¹ =
      torusPointHom T r.coroot R (b / c) := by
  rw [word_eq_torus_mul r R b, word_eq_torus_mul r R c, map_div, div_eq_mul_inv]
  group

private theorem reverse_linkage {G : AffineAlgebraicGroup k} (hG : Specs.GeometricRadicals.IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T) [IsCommMonObj T.group.X]
    (D : Datum T) (α : Root T) {x y : A.group ⟶ G.val} (r : CorootReflection T α.val x y)
    (hx : HasScalarAction T α.val x) (hy : HasScalarAction T (oppositeRoot D α).val y) :
    Nonempty (CorootReflection T (oppositeRoot D α).val y x) := by
  let β := oppositeRoot D α
  have hβ : β.val = α.val⁻¹ := oppositeRoot_val D α
  have hxy : HasScalarAction T β.val⁻¹ x := by simpa only [hβ, inv_inv] using hx
  let c := Additive.toMul (D.rootDatum.coroot β)
  have hcoroot := linked_coroot D α r
  have hc : c = r.coroot⁻¹ := by
    have hneg : D.rootDatum.coroot β = -D.rootDatum.coroot α :=
      D.rootDatum.coroot_eq_neg_iff.mpr rfl
    rw [hcoroot, ← toMul_neg]
    exact congrArg Additive.toMul hneg
  have hpair : pairing T.group α.val⁻¹ r.coroot = -2 := by
    rw [← hβ, hcoroot, coroot_pairing]
    exact (D.rootDatum.pairing_reflectionPerm_self_left α α).trans
      (congrArg Neg.neg (D.rootDatum.pairing_same α))
  have hy' : HasScalarAction T α.val⁻¹ y := by
    rw [← oppositeRoot_val D α]
    exact hy
  apply RootData.RootGroups.corootReflection_of_word T hT β.val y x hy hxy c
    (rankOneRepresentative y x) (rankOneRepresentative_point y x)
  · intro R b
    rw [word_swap hG T hT hmax α r hx hy' hpair R b,
      word_swap hG T hT hmax α r hx hy' hpair R 1,
      word_quotient r R (-b⁻¹) (-(1 : Rˣ)⁻¹), torusPointHom_apply]
    have hh : (-b⁻¹) / (-(1 : Rˣ)⁻¹) = b⁻¹ := by
      apply Units.ext
      simp [div_eq_mul_inv]
    rw [hh, hc, cocharacterPoint_inv]
    change (LinearAlgebraicGroups.CocharacterDynamics.unitPoint R b ≫ r.coroot.hom.hom⁻¹) ≫ _ =
      (LinearAlgebraicGroups.CocharacterDynamics.unitPoint R b ≫ r.coroot.hom.hom)⁻¹ ≫ _
    rw [GrpObj.comp_inv]
  · rw [coroot_pairing, D.rootDatum.pairing_same]

private theorem rank_le_one_roots (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hcard : letI := D.comm; D.base.support.card ≤ 1) (α : Root P.pair.T) :
    letI := D.comm
    ∃ a ∈ D.base.support, ∀ β : Root P.pair.T, β = a ∨ β = oppositeRoot D.datum a := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  let L := D.datum.rootDatum
  obtain ⟨g, _, _, hg⟩ := D.base.exists_root_eq_sum_int α
  have hN : D.base.support.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hg
    exact L.ne_zero α hg
  obtain ⟨a, ha⟩ := hN
  refine ⟨a, ha, fun β => ?_⟩
  have hs : D.base.support = {a} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, fun j hj => Finset.card_le_one_iff.mp hcard hj ha⟩
  obtain ⟨f, _, _, hf⟩ := D.base.exists_root_eq_sum_int β
  rw [hs, Finset.sum_singleton] at hf
  have hf' : β.val = a.val ^ f a := by
    apply Additive.ofMul.injective
    simpa only [D.datum.root_eq, ofMul_zpow] using hf
  have hn : f a ≠ 0 := by
    intro he
    exact β.property.1 (by simpa [he] using hf')
  have hp : Proportional a.val β.val := ⟨f a, 1, hn, one_ne_zero, by rw [zpow_one, hf']⟩
  have h := ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive P.pair.T P.pair.split
    P.pair.maximal).2 a.val a.property).2.1 β.val
  rcases h.mp ⟨β.property, hp⟩ with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr (Subtype.ext (he.trans (oppositeRoot_val D.datum a).symm))

private theorem rank_le_one_simple (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hcard : letI := D.comm; D.base.support.card ≤ 1) (α : Root P.pair.T)
    (hpos : letI := D.comm; D.base.IsPos α) : IsSimple P.pair α := by
  letI := D.comm
  letI := D.datum.finiteRoots
  obtain ⟨a, ha, h⟩ := rank_le_one_roots P D hcard α
  rcases h α with rfl | rfl
  · exact (D.simple_iff _).mp ha
  · exact False.elim ((positive_opposite_iff D a).mp hpos (D.base.isPos_of_mem_support ha))

private theorem small_rank_coordinates (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hpos : letI := D.comm; ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B)
    (hcard : letI := D.comm; D.base.support.card ≤ 1) :
    Nonempty (Specs.RankTwoRelations.Coordinates (P := P)) := by
  classical
  letI := D.comm
  let pos (α : Root P.pair.T) (h : D.base.IsPos α) :=
    P.pin ⟨α, rank_le_one_simple P D hcard α h⟩
  choose neg hneg using fun (α : Root P.pair.T) (h : D.base.IsPos α) =>
    RankTwoRelations.linkedOppositeCoordinate P α (oppositeRoot D.datum α)
      (oppositeRoot_val D.datum α) (pos α h)
  have pos_op (α : Root P.pair.T) (h : ¬ D.base.IsPos α) :
      D.base.IsPos (oppositeRoot D.datum α) := (positive_opposite_iff D α).mpr h
  let coord (α : Root P.pair.T) : RootCoordinate A P.pair.T (P.roots α).val α.val :=
    if h : D.base.IsPos α then pos α h
    else oppositeRoot_oppositeRoot D.datum α ▸ neg (oppositeRoot D.datum α) (pos_op α h)
  refine ⟨⟨coord, ?_, ?_⟩⟩
  · intro α
    rw [show coord α.val = pos α.val ((hpos α.val).mpr α.property.1) from
      dite_eq_left ((hpos α.val).mpr α.property.1)]
  · intro α β hα hβ
    have hβ' : β = oppositeRoot D.datum α :=
      Subtype.ext (hβ.trans (oppositeRoot_val D.datum α).symm)
    subst β
    have hα' := (hpos α).mpr hα
    have hb : ¬ D.base.IsPos (oppositeRoot D.datum α) :=
      fun hp => (positive_opposite_iff D α).mp hp hα'
    have hcoord₁ : coord α = pos α hα' := dite_eq_left hα'
    have hcoord₂ : coord (oppositeRoot D.datum α) = neg α hα' := by
      unfold coord
      rw [dite_eq_right hb]
      have transport (a : Root P.pair.T) (ha : D.base.IsPos a) (e : a = α) :
          (congrArg (oppositeRoot D.datum) e ▸ neg a ha) = neg α hα' := by
        subst a
        rfl
      exact transport _ _ (oppositeRoot_oppositeRoot D.datum α)
    rw [hcoord₁, hcoord₂]
    exact hneg α hα'

private theorem linked_reflections (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hpos : letI := D.comm; ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B)
    (X : Specs.RankTwoRelations.Coordinates (P := P)) :
    letI := D.comm
    ∀ α, Nonempty (CorootReflection P.pair.T α.val
      (Specs.RankTwoRelations.rootMap X α)
      (Specs.RankTwoRelations.rootMap X (oppositeRoot D.datum α))) := by
  classical
  letI := D.comm
  intro α
  by_cases h : D.base.IsPos α
  · exact X.linked α _ ((hpos α).mp h) (oppositeRoot_val D.datum α)
  · let β := oppositeRoot D.datum α
    have hβ := (positive_opposite_iff D α).mpr h
    obtain ⟨r⟩ := X.linked β α ((hpos β).mp hβ) (by
      rw [oppositeRoot_val, inv_inv])
    have hr := reverse_linkage P.pair.reductive P.pair.T P.pair.split P.pair.maximal
      D.datum β (show CorootReflection P.pair.T β.val (Specs.RankTwoRelations.rootMap X β)
        (Specs.RankTwoRelations.rootMap X (oppositeRoot D.datum β)) from by
          rw [show oppositeRoot D.datum β = α from oppositeRoot_oppositeRoot D.datum α]
          exact r)
      (X.coordinate β).property (X.coordinate (oppositeRoot D.datum β)).property
    change Nonempty (CorootReflection P.pair.T (oppositeRoot D.datum β).val _ _) at hr
    rw [show oppositeRoot D.datum β = α from oppositeRoot_oppositeRoot D.datum α] at hr
    exact hr

private def cellCoordinates (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hpos : letI := D.comm; ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B)
    (X : Specs.RankTwoRelations.Coordinates (P := P)) :
    letI := D.comm
    Specs.CellHomomorphism.Coordinates D.datum A :=
  letI := D.comm
  let r := fun α => Classical.choice (linked_reflections P D hpos X α)
  { groups := P.roots
    parametrization := fun α => (X.coordinate α).val
    scalarAction := fun α => (X.coordinate α).property
    opposite := oppositeRoot D.datum
    opposite_eq := oppositeRoot_val D.datum
    reflection := r
    coroot_eq := fun α => linked_coroot D.datum α (r α) }

open Specs.CellHomomorphism (pullbackCharacters)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus)
open LinearAlgebraicGroups.CharacterDescent (monomialCharacterEquiv)

open private splitPresentation charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private splitGroupHomEquiv monomialCharacter from LinearAlgebraicGroups.Multiplicative.CharacterDescent


/-- The specified lattice map on split tori is represented by a unique torus map. -/
private theorem split_torus_pullback {T S : GroupScheme k} (hT : IsSplitTorus T)
    (hS : IsSplitTorus S) :
    Function.Bijective (pullbackCharacters (T := T) (S := S)) := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨s, ⟨j⟩⟩ := splitPresentation hS
  obtain ⟨e, he, _⟩ := CharacterDescent.characterInterpretation (k := k)
  let M := StandardLattice.{u} r
  let N := StandardLattice.{u} s
  let charM := (monomialCharacterEquiv (M := M) k).trans (e (groupAlgebra k M))
  let charN := (monomialCharacterEquiv (M := N) k).trans (e (groupAlgebra k N))
  let a := charM.trans (charactersOfIso i)
  let b := charN.trans (charactersOfIso j)
  let L : (N →* M) ≃ (T ⟶ S) :=
    (splitGroupHomEquiv (k := k) N M).toEquiv.trans (i.homCongr j)
  have hnat (h : N →* M) (n : N) :
      pullbackCharacters (L h) (b n) = a (h n) := by
    have hc : charM (h n) = specGroupMap (groupAlgebraMap k h) ≫ charN n := by
      change e (groupAlgebra k M) (monomialCharacter k (h n)) =
        specGroupMap (groupAlgebraMap k h) ≫
          e (groupAlgebra k N) (monomialCharacter k n)
      rw [← he]
      congr 1
      apply GroupLike.val_injective
      exact (MonoidAlgebra.mapDomainBialgHom_single h n (1 : k)).symm
    change (i.inv ≫ specGroupMap (groupAlgebraMap k h) ≫ j.hom) ≫
      j.inv ≫ charN n = i.inv ≫ charM (h n)
    rw [hc]
    simp
  constructor
  · intro f g hfg
    obtain ⟨p, rfl⟩ := L.surjective f
    obtain ⟨q, rfl⟩ := L.surjective g
    congr 1
    apply MonoidHom.ext
    intro n
    exact a.injective ((hnat p n).symm.trans ((DFunLike.congr_fun hfg (b n)).trans (hnat q n)))
  · intro h
    let l := a.symm.toMonoidHom.comp (h.comp b.toMonoidHom)
    refine ⟨L l, ?_⟩
    apply MonoidHom.ext
    intro χ
    obtain ⟨n, rfl⟩ := b.surjective χ
    rw [hnat]
    exact a.apply_symm_apply (h (b n))

/-- Translate the lattice hypotheses into compatibility of the unique split
torus morphism inducing the given character map. -/
theorem compatibleTorusMap (P Q : PinnedGroup A) (D : AttachedDatum P.pair)
    (E : AttachedDatum Q.pair) (d : Root P.pair.T ≃ Root Q.pair.T)
    (h : Character Q.pair.T.group →* Character P.pair.T.group)
    (hinj : Function.Injective h) (hfinite : Finite (Character P.pair.T.group ⧸ h.range))
    (hroot : ∀ α, h (d α).val = α.val)
    (hdual : letI := D.comm; letI := E.comm;
      ∀ α (χ : Character Q.pair.T.group),
        pairing P.pair.T.group (h χ) (Additive.toMul (D.datum.rootDatum.coroot α)) =
          pairing Q.pair.T.group χ (Additive.toMul (E.datum.rootDatum.coroot (d α))))
    (hsimple : letI := D.comm; letI := E.comm;
      ∀ α, α ∈ D.base.support ↔ d α ∈ E.base.support) :
    ∃! τ : P.pair.T.group ⟶ Q.pair.T.group,
      pullbackCharacters τ = h ∧ Compatible P Q D E d τ := by
  letI := D.comm
  letI := E.comm
  have hb := split_torus_pullback P.pair.split Q.pair.split
  obtain ⟨τ, hτ⟩ := hb.2 h
  refine ⟨τ, ⟨hτ, ⟨hτ.symm ▸ hinj, hτ.symm ▸ hfinite, ?_, ?_, hsimple⟩⟩,
    fun σ hσ => hb.1 (hσ.1.trans hτ.symm)⟩
  · intro α
    change pullbackCharacters τ (d α).val = α.val
    rw [hτ, hroot]
  · intro α
    apply Additive.ofMul.injective
    apply E.datum.rootDatum.flip.toPerfPair.injective
    ext x
    let χ := Additive.toMul x
    change E.datum.rootDatum.toLinearMap (Additive.ofMul χ)
        (Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot α) ≫ τ)) =
      E.datum.rootDatum.toLinearMap (Additive.ofMul χ)
        (Additive.ofMul (Additive.toMul (E.datum.rootDatum.coroot (d α))))
    rw [E.datum.pairing_eq, E.datum.pairing_eq, ← hdual α χ, ← hτ]
    unfold pairing Specs.CharacterDescent.compositionPairing
    rw [Category.assoc]
    rfl

private theorem isIso_of_pullback_bijective {T S : GroupScheme k} (hT : IsSplitTorus T)
    (hS : IsSplitTorus S) (τ : T ⟶ S) (h : Function.Bijective (pullbackCharacters τ)) :
    IsIso τ := by
  let e := MulEquiv.ofBijective (pullbackCharacters τ) h
  obtain ⟨σ, hσ⟩ := (split_torus_pullback hS hT).2 e.symm.toMonoidHom
  refine ⟨⟨σ, (split_torus_pullback hT hT).1 ?_, (split_torus_pullback hS hS).1 ?_⟩⟩
  · apply MonoidHom.ext
    intro χ
    change (τ ≫ σ) ≫ χ = (𝟙 T) ≫ χ
    rw [Category.assoc, Category.id_comp]
    change e (pullbackCharacters σ χ) = χ
    rw [hσ]
    exact e.apply_symm_apply χ
  · apply MonoidHom.ext
    intro χ
    change (σ ≫ τ) ≫ χ = (𝟙 S) ≫ χ
    rw [Category.assoc, Category.id_comp]
    change pullbackCharacters σ (e χ) = χ
    rw [hσ]
    exact e.symm_apply_apply χ

private theorem cellCoordinates_root (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hpos : letI := D.comm; ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B)
    (X : RankTwoRelations.Coordinates (P := P)) (α : Root P.pair.T) :
    letI := D.comm
    (cellCoordinates P D hpos X).root α = RankTwoRelations.rootMap X α := rfl

private theorem cartan_transfer {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ)
    (α β : Root P.pair.T) :
    letI := D.comm
    letI := E.comm
    D.datum.rootDatum.pairing α β = E.datum.rootDatum.pairing (d α) (d β) := by
  letI := D.comm
  letI := E.comm
  rw [← coroot_pairing D.datum, ← coroot_pairing E.datum]
  unfold pairing Specs.CharacterDescent.compositionPairing
  rw [← h.root α, ← Category.assoc, h.coroot β]

private def labelRootEquiv {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ) :
    RankTwoRelations.Index κ ≃ Root P.pair.T :=
  Equiv.ofBijective F.root ⟨fun r s h => Subtype.ext (F.independent (congrArg Subtype.val h)), by
    intro α
    obtain ⟨r, hr⟩ := (F.root_iff _).mp α.property
    exact ⟨r, Subtype.ext hr.symm⟩⟩

private theorem root_transport {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ)
    {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ) (r : RankTwoRelations.Index κ) :
    (transportFrame h F).root r = d (F.root r) := by
  apply Subtype.ext
  apply h.injective
  change pullbackCharacters τ ((d F.first.val).val ^ r.val.1 * (d F.second.val).val ^ r.val.2) =
    pullbackCharacters τ (d (F.root r)).val
  simp only [map_mul, map_zpow, show ∀ i, pullbackCharacters τ (d i).val = i.val from h.root]
  rfl

private def frameCoefficients {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ) :
    RootIndex →+ Additive (Character P.pair.T.group) where
  toFun r := Additive.ofMul (F.character r)
  map_zero' := by simp [RankTwoRelations.Frame.character]
  map_add' r s := by
    apply Additive.toMul.injective
    change F.character (r + s) = F.character r * F.character s
    simp only [RankTwoRelations.Frame.character, Prod.fst_add, Prod.snd_add, zpow_add]
    ac_rfl

private theorem frame_character_cone {P : PinnedGroup A} {κ : TypeOfRoots}
    (F : RankTwoRelations.Frame P κ) (r s : RootIndex) (i j : ℕ) :
    F.character (i • r + j • s) = F.character r ^ i * F.character s ^ j := by
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_pow, ofMul_pow]
  change (frameCoefficients F) (i • r + j • s) =
    i • (frameCoefficients F) r + j • (frameCoefficients F) s
  simp only [map_add, map_nsmul]

private theorem point_label {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ)
    (X : RankTwoRelations.Coordinates (P := P)) (R : TestAlgebra k)
    (r : RootIndex) (hr : RankTwoRelations.IsIndex κ r) (x : R) :
    RankTwoRelations.point F X R r x =
      rootPoint (RankTwoRelations.rootMap X (F.root ⟨r, hr⟩)) R x := by
  have h : F.character r ∈ Specs.CharacterPairing.absoluteRoots P.pair.T :=
    (F.root ⟨r, hr⟩).property
  unfold RankTwoRelations.point
  rw [dite_eq_left h]
  rfl

private theorem labelled_point_neg {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ)
    (X : RankTwoRelations.Coordinates (P := P)) (R : TestAlgebra k) (r : RootIndex) (z : R) :
    RankTwoRelations.point F X R r (-z) = (RankTwoRelations.point F X R r z)⁻¹ := by
  classical
  unfold RankTwoRelations.point
  by_cases h : F.character r ∈ absoluteRoots P.pair.T
  · simp only [dite_eq_left h, rootPoint_neg]
  · simp only [dite_eq_right h, inv_one]

private def cellTerms {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ)
    (r s : RankTwoRelations.Index κ) (L : List RankTwoRelations.Correction)
    (hL : ∀ t ∈ L, ValidCorrection κ r s t) :
    List (CellHomomorphism.CommutatorTerm (F.root r) (F.root s)) :=
  L.attach.map fun v =>
    let h := hL v.val v.property
    { root := F.root ⟨v.val.root, h.1⟩
      i := v.val.leftDegree
      j := v.val.rightDegree
      i_pos := h.2.1
      j_pos := h.2.2.1
      root_eq := by
        change F.character v.val.root = F.character r ^ v.val.leftDegree * F.character s ^ v.val.rightDegree
        rw [h.2.2.2, frame_character_cone]
      coefficient := (v.val.coefficient : k) }

private theorem cellTerms_eval {P : PinnedGroup A} {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ)
    (r s : RankTwoRelations.Index κ) (L : List RankTwoRelations.Correction)
    (hL : ∀ t ∈ L, ValidCorrection κ r s t)
    (R : TestAlgebra k) {H : Type*} [Group H] (p : RootIndex → R → H)
    (a : Root P.pair.T → R → H)
    (ha : ∀ r (hr : RankTwoRelations.IsIndex κ r) z, p r z = a (F.root ⟨r, hr⟩) z) (x y : R) :
    ((cellTerms F r s L hL).map fun t => a t.root
        (algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)).prod =
      wordValue p x y L := by
  unfold cellTerms wordValue
  rw [← List.attach_map_val (l := L) (f := fun (t : RankTwoRelations.Correction) => p t.root
    ((t.coefficient : R) * x ^ t.leftDegree * y ^ t.rightDegree)), List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  dsimp only [Function.comp_apply]
  rw [ha t.val.root (hL t.val t.property).1, map_intCast]

private theorem paired_nonproportional {P : PinnedGroup A} {α β : Root P.pair.T}
    (hne : α ≠ β) (hopp : β.val ≠ α.val⁻¹) : ¬ Proportional α.val β.val := by
  intro he
  have h := ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive P.pair.T P.pair.split
    P.pair.maximal).2 α.val α.property).2.1 β.val
  rcases h.mp ⟨β.property, he⟩ with hsame | hneg
  · exact hne (Subtype.ext hsame.symm)
  · exact hopp hneg

private theorem signed_rank_two {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ)
    (hP : letI := D.comm; ∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B)
    (hQ : letI := E.comm; ∀ β, E.base.IsPos β ↔ β ∈ subgroupRoots Q.pair.T Q.pair.B)
    {κ : TypeOfRoots} (F : RankTwoRelations.Frame P κ)
    (X : RankTwoRelations.Coordinates (P := P)) (Y : RankTwoRelations.Coordinates (P := Q))
    (hX : RankTwoRelations.SimpleActions F X ∧ RankTwoRelations.PositiveRelations F X ∧
      RankTwoRelations.SignedRelations F X)
    (hY : RankTwoRelations.SimpleActions (transportFrame h F) Y ∧
      RankTwoRelations.PositiveRelations (transportFrame h F) Y) :
    letI := D.comm
    letI := E.comm
    CellHomomorphism.SameSignedCommutators (cellCoordinates P D hP X) (cellCoordinates Q E hQ Y) d := by
  letI := D.comm
  letI := E.comm
  let F' := transportFrame h F
  have δ (r : RankTwoRelations.Index κ) : F'.root r = d (F.root r) := root_transport h F r
  rintro α β hne hopp
  obtain ⟨r, hr⟩ := (labelRootEquiv F).surjective α
  obtain ⟨s, hs⟩ := (labelRootEquiv F).surjective β
  change F.root r = α at hr
  change F.root s = β at hs
  subst α
  subst β
  have hindex : r.val ≠ s.val := fun he => hne (congrArg F.root (Subtype.ext he))
  have hnonprop : ¬ Proportional (F.character r) (F.character s) := paired_nonproportional hne hopp
  simp only [cellCoordinates_root]
  by_cases hκ : κ = .orthogonal
  · subst κ
    have hnonprop' : ¬ Proportional (F'.character r) (F'.character s) := by
      rintro ⟨m, n, hm, hn, he⟩
      apply hnonprop
      refine ⟨m, n, hm, hn, ?_⟩
      have he' := congrArg (pullbackCharacters τ) he
      have eqChar (a : RankTwoRelations.Index .orthogonal) :
          pullbackCharacters τ (F'.character a) = F.character a := by
        change pullbackCharacters τ (F'.root a).val = (F.root a).val
        rw [δ]
        exact h.root (F.root a)
      simpa only [map_zpow, eqChar] using he'
    refine ⟨[], fun R x y => ?_⟩
    simp only [List.map_nil, List.prod_nil]
    constructor
    · have hc := RankTwoRelations.orthogonalCommutation P F r s hnonprop R
        (rootPoint (X.coordinate (F.root r)).val.hom R x)
        (rootPoint (X.coordinate (F.root s)).val.hom R y)
      change Commute (rootPoint (RankTwoRelations.rootMap X (F.root r)) R x)
        (rootPoint (RankTwoRelations.rootMap X (F.root s)) R y) at hc
      rw [hc.eq]
      group
    · have hc := RankTwoRelations.orthogonalCommutation Q F' r s hnonprop' R
        (rootPoint (Y.coordinate (F'.root r)).val.hom R x)
        (rootPoint (Y.coordinate (F'.root s)).val.hom R y)
      change Commute (rootPoint (RankTwoRelations.rootMap Y (F'.root r)) R x)
        (rootPoint (RankTwoRelations.rootMap Y (F'.root s)) R y) at hc
      rw [δ, δ] at hc
      rw [hc.eq]
      group
  · obtain ⟨hactX, hposX, hsigned⟩ := hX
    obtain ⟨hactY, hposY⟩ := hY
    obtain ⟨w, hw₁, hw₂, _⟩ := hsigned r s hnonprop
    have hr : labelAction κ w r ∈ RankTwoRelations.positiveList κ := by
      simpa only [wordAction_eq] using hw₁
    have hs : labelAction κ w s ∈ RankTwoRelations.positiveList κ := by
      simpa only [wordAction_eq] using hw₂
    let L := signedTable κ w r s
    let valid := signedTable_valid κ w r s
    refine ⟨cellTerms F r s L valid, ?_⟩
    intro R x y
    have hleft := signed_commutator κ (RankTwoRelations.point F X R)
      (RankTwoRelations.representative F X R) (labelled_point_neg F X R)
      (fun a b ha hb hab z t => by
        simpa only [RankTwoRelations.positiveCorrection, RankTwoRelations.correctionFactors,
          List.map_map, Function.comp_def, wordValue] using hposX a b ha hb hab R z t)
      (fun i a ha => hactX i ⟨a, ha⟩ R) w r.property s.property hindex hr hs x y
    have hright := signed_commutator κ (RankTwoRelations.point F' Y R)
      (RankTwoRelations.representative F' Y R) (labelled_point_neg F' Y R)
      (fun a b ha hb hab z t => by
        simpa only [RankTwoRelations.positiveCorrection, RankTwoRelations.correctionFactors,
          List.map_map, Function.comp_def, wordValue] using hposY a b ha hb hab R z t)
      (fun i a ha => hactY i ⟨a, ha⟩ R) w r.property s.property hindex hr hs x y
    constructor
    · rw [cellTerms_eval F r s L valid R (RankTwoRelations.point F X R)
        (fun a => rootPoint (RankTwoRelations.rootMap X a) R)
        (fun a ha => point_label F X R a ha) x y]
      simpa only [point_label F X R _ r.property, point_label F X R _ s.property] using hleft
    · rw [cellTerms_eval F r s L valid R (RankTwoRelations.point F' Y R)
        (fun a => rootPoint (RankTwoRelations.rootMap Y (d a)) R)
        (fun a ha z => (point_label F' Y R a ha z).trans (by rw [δ])) x y]
      simpa only [point_label F' Y R _ r.property, point_label F' Y R _ s.property, δ] using hright

private theorem same_base_card {P Q : PinnedGroup A} {D : AttachedDatum P.pair}
    {E : AttachedDatum Q.pair} {d : Root P.pair.T ≃ Root Q.pair.T}
    {τ : P.pair.T.group ⟶ Q.pair.T.group} (h : Compatible P Q D E d τ) :
    letI := D.comm
    letI := E.comm
    D.base.support.card = E.base.support.card := by
  classical
  letI := D.comm
  letI := E.comm
  have hs : D.base.support.map d.toEmbedding = E.base.support := by
    ext b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h.simple a).mp ha
    · intro hb
      exact ⟨d.symm b, (h.simple (d.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using hb),
        d.apply_symm_apply b⟩
  rw [← hs, Finset.card_map]

/-- A compatible torus map lifts to a central isogeny with isomorphisms
on all corresponding root subgroups. -/
theorem liftTorusMap (P Q : PinnedGroup A) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (hrank : letI := D.comm; D.base.support.card ≤ 2)
    (d : Root P.pair.T ≃ Root Q.pair.T) (τ : P.pair.T.group ⟶ Q.pair.T.group)
    (h : Compatible P Q D E d τ) :
    ∃ f : P.pair.G.val ⟶ Q.pair.G.val,
      MatchesPinning d τ f ∧
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      HasCentralTorusKernel τ f ∧
      (Function.Surjective (pullbackCharacters τ) → IsIso f) ∧
      MatchesRootGroups d f := by
  classical
  letI := D.comm
  letI := E.comm
  have hP := base_isPos_iff_subgroupRoots D
  have hQ := base_isPos_iff_subgroupRoots E
  have hcoordinates : ∃ (X : RankTwoRelations.Coordinates (P := P))
      (Y : RankTwoRelations.Coordinates (P := Q)),
      CellHomomorphism.SameSignedCommutators
        (cellCoordinates P D hP X) (cellCoordinates Q E hQ Y) d := by
    by_cases hcard : D.base.support.card = 2
    · obtain ⟨κ, ⟨F⟩⟩ := rankTwoFrame P D hcard
      obtain ⟨X, _, hX⟩ := RankTwoRelations.rankTwoRelations P κ F
      obtain ⟨Y, _, hactY, hposY, _⟩ := RankTwoRelations.rankTwoRelations Q κ (transportFrame h F)
      exact ⟨X, Y, signed_rank_two h hP hQ F X Y hX ⟨hactY, hposY⟩⟩
    · have hsmall : D.base.support.card ≤ 1 := Nat.le_of_lt_succ (lt_of_le_of_ne hrank hcard)
      have hsmallQ : E.base.support.card ≤ 1 := (same_base_card h) ▸ hsmall
      obtain ⟨X⟩ := small_rank_coordinates P D hP hsmall
      obtain ⟨Y⟩ := small_rank_coordinates Q E hQ hsmallQ
      refine ⟨X, Y, ?_⟩
      intro α β hne hopp
      obtain ⟨a, _, hall⟩ := rank_le_one_roots P D hsmall α
      have hrel : β = α ∨ β.val = α.val⁻¹ := by
        rcases hall α with hα | hα <;> rcases hall β with hβ | hβ
        · exact Or.inl (hβ.trans hα.symm)
        · exact Or.inr (by rw [hα, hβ, oppositeRoot_val])
        · exact Or.inr (by rw [hα, hβ, oppositeRoot_val, inv_inv])
        · exact Or.inl (hβ.trans hα.symm)
      exact hrel.elim (fun he => (hne he.symm).elim) (fun he => (hopp he).elim)
  obtain ⟨X, Y, hsigned⟩ := hcoordinates
  obtain ⟨f, ⟨hf, hfin, hflat, hsurj, hkernel, _, hiso⟩, _⟩ :=
    CellHomomorphism.cellHomomorphism
      P.pair.G Q.pair.G P.pair.reductive Q.pair.reductive P.pair.T Q.pair.T
      P.pair.split Q.pair.split P.pair.maximal Q.pair.maximal
      P.pair.B Q.pair.B P.pair.borel Q.pair.borel P.pair.containsTorus Q.pair.containsTorus
      D.comm E.comm D.datum E.datum D.base E.base hP hQ A
      (cellCoordinates P D hP X) (cellCoordinates Q E hQ Y) d τ
      h.injective h.finiteIndex h.root h.coroot (positive_transfer h) h.simple hsigned
  refine ⟨f, ⟨hf.1, ?_⟩, hfin, hflat, hsurj, hkernel, ?_, ?_⟩
  · intro α β hab
    have hm := hf.2 α.val
    change RankTwoRelations.rootMap X α.val ≫ f = RankTwoRelations.rootMap Y (d α.val) at hm
    rw [hab] at hm
    simpa only [RankTwoRelations.rootMap, X.pin α, Y.pin β] using hm
  · intro hsur
    exact hiso (isIso_of_pullback_bijective P.pair.split Q.pair.split τ ⟨h.injective, hsur⟩)
  · intro α
    let e := (X.coordinate α).val
    let g := (Y.coordinate (d α)).val
    refine ⟨e.symm ≪≫ g, ?_⟩
    have hm := hf.2 α
    change (e.hom ≫ (P.roots α).val.inclusion) ≫ f =
      g.hom ≫ (Q.roots (d α)).val.inclusion at hm
    calc
      (P.roots α).val.inclusion ≫ f =
          e.inv ≫ ((e.hom ≫ (P.roots α).val.inclusion) ≫ f) := by
        rw [Category.assoc, Iso.inv_hom_id_assoc]
      _ = (e.inv ≫ g.hom) ≫ (Q.roots (d α)).val.inclusion := by
        rw [hm, Category.assoc]

/-- The ordinary pin-compatible central lift in semisimple rank at most two. -/
theorem rankTwoLifting : Specs.RankTwoLifting.Statement.{u} := by
  intro k _ A P Q D E
  letI := D.comm
  letI := E.comm
  dsimp only
  intro _ _ hrank d τ h
  obtain ⟨f, hpins, hfinite, hflat, hsurj, hkernel, hiso, _⟩ :=
    liftTorusMap P Q D E hrank d τ h
  exact ⟨f, hpins, hfinite, hflat, hsurj, hkernel, hiso⟩

/-- The finite-index character injection specifies the lift over the ground field. -/
theorem rankTwoLiftingFromCharacters : Specs.RankTwoLifting.CharacterStatement.{u} := by
  intro k _ A P Q D E
  letI := D.comm
  letI := E.comm
  dsimp only
  intro hrank d h hinj hindex hroot hdual hsimple
  obtain ⟨τ, ⟨hτ, hcompat⟩, _⟩ := compatibleTorusMap P Q D E d h hinj hindex hroot hdual hsimple
  obtain ⟨f, hpins, hfinite, hflat, hsurj, hkernel, hiso, hgroups⟩ :=
    liftTorusMap P Q D E hrank d τ hcompat
  refine ⟨τ, f, hτ, hpins, hfinite, hflat, hsurj, hkernel, ?_, hgroups⟩
  simpa only [hτ] using hiso

end

end LinearAlgebraicGroups.Classification.RankTwoLifting
