import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart

open CategoryTheory CategoryTheory.MonoidalCategory ValuativeRel
open scoped CategoryTheory.MonObj TensorProduct WithZero
open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalFoldedRootChart
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalIwahoriCongruence (CellValues cellValue integralRing rootValuePoint)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus pinnedGroundPoint)
open Specs.ExceptionalMarkedRootDescent hiding normalizedValuation
open Specs.ExceptionalValuedTorusNormalizer hiding normalizedValuation
open Specs.ExceptionalAffineRootSystems
open Specs.IntegralRootRelations (upper diagonal)
open Specs.OrderedRootProducts (Enumerates)

open private cellValue_eq_mul rootWord_cons from
  LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private groundHopfEquiv pinnedGroundPoint_apply from
  LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedTorusPoint_map groundTensorIso from
  LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private affineTorusPointEquiv from
  LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

universe u

attribute [local instance] integerAlgebra

noncomputable section

variable {D : BasedRootDatum.{u}} {k K : Type u} [Field k] [Field K] [Algebra k K]

private def firstLabel (b : TransportedOrbit D) : D.I :=
  weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) b.1.1

private theorem firstLabel_mem (b : TransportedOrbit D) :
    firstLabel b ∈ transportedLabels b := by
  simp [firstLabel, transportedLabels, SimpleRootOrbit.roots]

private theorem blockDirection {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) (a : FoldedRootDirection) :
    direction (firstLabel (o.block a)) = a :=
  (o.fibre a _).mp (firstLabel_mem _)

private theorem block_eq {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) {b : TransportedOrbit D} (hb : b ∈ o.negative ++ o.positive)
    {i : D.I} (hi : i ∈ transportedLabels b) : o.block (direction i) = b := by
  obtain ⟨a, rfl⟩ := o.ordered b hb
  rw [(o.fibre a i).mp hi]

private def gather (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b) :
    (bs : List (TransportedOrbit D)) → rationalOrderedParameters k K bs
  | [] => PUnit.unit
  | b :: bs => (y b, gather y bs)

omit [Field k] [Field K] [Algebra k K] in
private theorem gather_congr
    (y z : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (bs : List (TransportedOrbit D)) (h : ∀ b ∈ bs, y b = z b) :
    gather y bs = gather z bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    exact Prod.ext (h b (List.mem_cons_self ..))
      (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

omit [Algebra k K] in
private theorem gather_surjective (bs : List (TransportedOrbit D)) (hb : bs.Nodup) :
    Function.Surjective (gather (k := k) (K := K) · bs) := by
  classical
  induction bs with
  | nil => exact fun p => ⟨fun _ => 0, PUnit.ext _ _⟩
  | cons b bs ih =>
    intro p
    obtain ⟨y, hy⟩ := ih (List.nodup_cons.mp hb).2 p.2
    refine ⟨Function.update y b p.1, Prod.ext (Function.update_self ..) ?_⟩
    refine (gather_congr _ _ _ fun c hc => Function.update_of_ne ?_ _ _).trans hy
    exact fun e => (List.nodup_cons.mp hb).1 (e ▸ hc)

omit [Algebra k K] in
private theorem gather_both (ns ps : List (TransportedOrbit D)) (h : (ns ++ ps).Nodup)
    (n : rationalOrderedParameters k K ns) (p : rationalOrderedParameters k K ps) :
    ∃ y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b,
      gather y ns = n ∧ gather y ps = p := by
  classical
  obtain ⟨x, hx⟩ := gather_surjective ns (List.nodup_append.mp h).1 n
  obtain ⟨y, hy⟩ := gather_surjective ps (List.nodup_append.mp h).2.1 p
  let z (b : TransportedOrbit D) := if b ∈ ns then x b else y b
  refine ⟨z, (gather_congr _ _ _ fun b hb => ite_eq_left hb).trans hx,
    (gather_congr _ _ _ fun b hb => ite_eq_right ?_).trans hy⟩
  intro hn
  exact (List.nodup_append.mp h).2.2 b hn b hb rfl

private theorem blocks_nodup {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) : (o.negative ++ o.positive).Nodup := by
  have h : ((o.negative ++ o.positive).flatMap transportedLabels).Nodup := by
    rw [List.flatMap_append, List.nodup_append]
    exact ⟨o.negative_enumerates.1, o.positive_enumerates.1, fun i hi j hj e =>
      (o.negative_enumerates.2 i).mp hi (e ▸ (o.positive_enumerates.2 j).mp hj)⟩
  generalize o.negative ++ o.positive = bs at h ⊢
  induction bs with
  | nil => exact List.nodup_nil
  | cons b bs ih =>
    rw [List.flatMap_cons, List.nodup_append] at h
    refine List.nodup_cons.mpr ⟨fun hb => ?_, ih h.2.1⟩
    exact h.2.2 _ (firstLabel_mem b) _ (List.mem_flatMap.mpr ⟨b, hb, firstLabel_mem b⟩) rfl

private def absoluteValue {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k))
    (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b) (i : D.I) : K :=
  let b := o.block (direction i)
  algebraMap Integers.{u} K (slotUnit u b i : Integers.{u}) * slotMap σ b i (y b)

private theorem slotValue_at {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k))
    (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (b : TransportedOrbit D) (hb : b ∈ o.negative ++ o.positive)
    (i : D.I) (hi : i ∈ b.1.roots) :
    absoluteValue o u σ y (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) i) =
      algebraMap Integers.{u} K (u b i : Integers.{u}) *
        slotMap σ b (weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) i) (y b) := by
  have h := block_eq o hb (List.mem_map_of_mem hi :
    weylWordPerm (b.2.flatMap SimpleRootOrbit.roots) i ∈ transportedLabels b)
  unfold absoluteValue
  rw [h]
  simp only [slotUnit, Equiv.symm_apply_apply]

private theorem rootWord_values (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (l : List D.I) (v : D.I → R) :
    rootValuePoint M.line R l (fun i => v l[i]) ≫ rootProduct M.line M.root l =
      orderedRootPoint M R l v := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    rw [rootWord_cons]
    change markedRootPoint M R a (v a) *
      (rootValuePoint M.line R l (fun i => v l[i]) ≫ rootProduct M.line M.root l) =
      markedRootPoint M R a (v a) * orderedRootPoint M R l v
    rw [ih]

private theorem cellValue_values (M : IntegralMarking D) (R : IntegralAlgebra.{u})
    (ns ps : List D.I) (v : D.I → R) (t : TorusValues D R) :
    cellValue M R ns ps (fun i => v ns[i], t, fun i => v ps[i]) =
      markedAbsoluteCell M R ns ps false (v, torusPoint D R t) := by
  rw [cellValue_eq_mul]
  change _ = orderedRootPoint M R ns v *
    ((torusPoint D R t ≫ M.torus.hom.hom) * orderedRootPoint M R ps v)
  rw [rootWord_values, rootWord_values]

set_option backward.isDefEq.respectTransparency false in
private theorem splitOrbit_value {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) (M : IntegralMarking D)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (hu : IsTransportUnitSystem M u)
    (σ : Gal(K/k)) (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (b : TransportedOrbit D) (hb : b ∈ o.negative ++ o.positive)
    (hn : (transportedLabels b).Nodup) :
    splitOrbitPoint M (integralRing K) b (rationalOrbitCoordinates σ b (y b)) =
      orderedRootPoint M (integralRing K) (transportedLabels b) (absoluteValue o u σ y) := by
  classical
  rcases b with ⟨⟨a, c⟩, w⟩
  let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
  cases c with
  | none =>
    change transportedRootPoint M (integralRing K) ((a, none), w) a (algebraMap k K (y ((a, none), w))) =
      markedRootPoint M (integralRing K) (p a) (absoluteValue o u σ y (p a)) * 1
    rw [mul_one, hu, slotValue_at o u σ y ((a, none), w) hb a (by simp [SimpleRootOrbit.roots])]
    rfl
  | some c =>
    have hne : p c.val ≠ p a.val := by
      simpa [p, transportedLabels, SimpleRootOrbit.roots, ne_comm] using hn
    change transportedRootPoint M (integralRing K) ((a, some c), w) a (y ((a, some c), w)) *
      transportedRootPoint M (integralRing K) ((a, some c), w) c (σ (y ((a, some c), w))) =
      markedRootPoint M (integralRing K) (p a) (absoluteValue o u σ y (p a)) *
        (markedRootPoint M (integralRing K) (p c) (absoluteValue o u σ y (p c)) * 1)
    rw [mul_one, hu (integralRing K) ((a, some c), w) a, hu (integralRing K) ((a, some c), w) c,
      slotValue_at o u σ y ((a, some c), w) hb a (by simp [SimpleRootOrbit.roots]),
      slotValue_at o u σ y ((a, some c), w) hb c (by simp [SimpleRootOrbit.roots])]
    simp [slotMap, p, show weylWordPerm (w.flatMap SimpleRootOrbit.roots) c.val ≠
      weylWordPerm (w.flatMap SimpleRootOrbit.roots) a.val from hne]
    rfl

private theorem splitOrdered_values {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) (M : IntegralMarking D)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (hu : IsTransportUnitSystem M u)
    (σ : Gal(K/k)) (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (bs : List (TransportedOrbit D)) (hb : ∀ b ∈ bs, b ∈ o.negative ++ o.positive)
    (hn : (bs.flatMap transportedLabels).Nodup) :
    splitOrderedOrbitPoint M (integralRing K) bs
        (rationalOrderedCoordinates σ bs (gather y bs)) =
      orderedRootPoint M (integralRing K) (bs.flatMap transportedLabels) (absoluteValue o u σ y) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatMap_cons, List.nodup_append] at hn
    simp only [splitOrderedOrbitPoint, rationalOrderedCoordinates, gather, List.flatMap_cons,
      orderedRootPoint, List.map_append, List.prod_append]
    exact congrArg₂ (· * ·) (splitOrbit_value o M u hu σ y b (hb b (List.mem_cons_self ..)) hn.1)
      (ih (fun c hc => hb c (List.mem_cons_of_mem _ hc)) hn.2.1)

private theorem cellValue_blocks {direction : D.I → FoldedRootDirection}
    (o : OrbitOrdering direction) (M : IntegralMarking D)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (hu : IsTransportUnitSystem M u)
    (σ : Gal(K/k)) (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (t : TorusValues D (integralRing K)) :
    let v := absoluteValue o u σ y
    cellValue M (integralRing K) _ _
      (fun i => v (o.negative.flatMap transportedLabels)[i], t,
        fun i => v (o.positive.flatMap transportedLabels)[i]) =
      markedSplitCell M (integralRing K) o.negative o.positive false
        (rationalOrderedCoordinates σ o.negative (gather y o.negative), torusPoint D _ t,
          rationalOrderedCoordinates σ o.positive (gather y o.positive)) := by
  intro v
  rw [cellValue_values]
  change _ * (_ * _) = _ * (_ * _)
  rw [splitOrdered_values o M u hu σ y o.negative (fun _ h => List.mem_append_left _ h) o.negative_enumerates.1,
    splitOrdered_values o M u hu σ y o.positive (fun _ h => List.mem_append_right _ h) o.positive_enumerates.1]

private def blockParameters {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (x : ∀ a, rationalOrbitParameter k K (o.block a)) (b : TransportedOrbit D) :
    rationalOrbitParameter k K b := by
  classical
  exact if h : o.block (direction (firstLabel b)) = b then
    h ▸ x (direction (firstLabel b))
  else 0

omit [Algebra k K] in
private theorem blockParameters_apply {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (x : ∀ a, rationalOrbitParameter k K (o.block a)) (a : FoldedRootDirection) :
    blockParameters o x (o.block a) = x a := by
  unfold blockParameters
  generalize he : direction (firstLabel (o.block a)) = a'
  have h : a' = a := he.symm.trans (blockDirection o a)
  clear he
  subst a'
  simp

private theorem coordinates_eq {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (σ : Gal(K/k))
    (t : TorusValues D (integralRing K))
    (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (x : ∀ a, rationalOrbitParameter k K (o.block a)) (h : ∀ a, y (o.block a) = x a) :
    let v := absoluteValue o u σ y
    o.coordinates u σ t x =
      (fun i => v (o.negative.flatMap transportedLabels)[i], t,
        fun i => v (o.positive.flatMap transportedLabels)[i]) := by
  simp only [OrbitOrdering.coordinates, absoluteValue, h]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The rational points of the marked cell have one parameter per folded
root, and their torus coordinate belongs to the descended torus. -/
theorem foldedOrderedChart : OrderedChart.{u} := by
  classical
  intro k K _ _ _ _ _ D M C l G B T d σ hd hσ hs direction o hb u hu j hj z
  let R := integralRing K
  let ns := o.negative
  let ps := o.positive
  let rel := pinnedRationalRelativeCell C d σ ns ps false
  obtain ⟨_, hrange⟩ :=
    Arithmetic.ExceptionalMarkedRootDescent.pinnedRationalFixedCellCoordinates C d hd σ hσ hs
      ns ps hb o.negative_enumerates o.positive_enumerates false
  have hfix : Set.range (fun p : HopfPoints (Specs.AdjointCocharacters.coordinateHopf G) k =>
      (integralPointFunctor M.group).map (evaluateGroundTensor k K)
        (pinnedMarkedPoint C d (CommAlgCat.of k k) p)) = Set.range j := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(groundHopfEquiv G).symm p, by
        rw [hj, pinnedGroundPoint_apply, MulEquiv.apply_symm_apply]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨groundHopfEquiv G p, (hj p).trans (pinnedGroundPoint_apply C d p) |>.symm⟩
  have hrel : ∀ q, rel q ∈ j.range := by
    intro q
    have h := Set.mem_range_self (f := rel) q
    rw [hrange] at h
    change rel q ∈ Set.range j
    rw [← hfix]
    exact h.2
  let c := cellValue M.toIntegralMarking R (ns.flatMap transportedLabels) (ps.flatMap transportedLabels)
  have hc (t : TorusValues D R) (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b) :
      c (o.coordinates u σ t (fun a => y (o.block a))) =
        markedSplitCell M.toIntegralMarking R ns ps false
          (rationalOrderedCoordinates σ ns (gather y ns), torusPoint D R t,
            rationalOrderedCoordinates σ ps (gather y ps)) := by
    rw [coordinates_eq o u σ t y _ (fun _ => rfl)]
    exact cellValue_blocks o M.toIntegralMarking u hu σ y t
  have habs : c z ∈ Set.range
      (markedAbsoluteCell M.toIntegralMarking R (ns.flatMap transportedLabels)
        (ps.flatMap transportedLabels) false) := by
    -- The two nodup lists have disjoint labels, so the slot functions
    -- extend to one function on the absolute roots.
    let lm := ns.flatMap transportedLabels
    let lp := ps.flatMap transportedLabels
    let label : Fin lm.length ⊕ Fin lp.length → D.I := Sum.elim (fun i => lm[i]) (fun i => lp[i])
    have hinj : Function.Injective label := by
      intro i j h
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          exact congrArg Sum.inl ((List.nodup_iff_injective_get.mp o.negative_enumerates.1) h)
        | inr j =>
          change lm[i] = lp[j] at h
          exact False.elim (((o.negative_enumerates.2 _).mp (List.getElem_mem i.isLt))
            (h ▸ (o.positive_enumerates.2 _).mp (List.getElem_mem j.isLt)))
      | inr i =>
        cases j with
        | inl j =>
          change lp[i] = lm[j] at h
          exact False.elim (((o.negative_enumerates.2 _).mp (List.getElem_mem j.isLt))
            (h.symm ▸ (o.positive_enumerates.2 _).mp (List.getElem_mem i.isLt)))
        | inr j =>
          exact congrArg Sum.inr ((List.nodup_iff_injective_get.mp o.positive_enumerates.1) h)
    let v := Function.extend label (Sum.elim z.1 z.2.2) (fun _ => 0)
    have hv (i) : v (label i) = Sum.elim z.1 z.2.2 i := hinj.extend_apply _ _ i
    refine ⟨(v, torusPoint D R z.2.1), ?_⟩
    rw [← cellValue_values]
    apply congrArg c
    exact Prod.ext (funext (fun i => hv (Sum.inl i))) (Prod.ext rfl (funext (fun i => hv (Sum.inr i))))
  let S := CommAlgCat.of k k
  let ev := ((integralPointFunctor M.group).map (evaluateGroundTensor k K)).hom
  let evT := ((integralPointFunctor (splitTorus D)).map (evaluateGroundTensor k K)).hom
  have hev : Function.Injective ev :=
    (((integralPointFunctor M.group).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).injective
  have hevT : Function.Surjective evT :=
    (((integralPointFunctor (splitTorus D)).mapIso (groundTensorIso k K)).groupIsoToMulEquiv).surjective
  obtain ⟨_, hinc, htor⟩ :=
    Arithmetic.ExceptionalMarkedRootDescent.pinnedMarkedTorusPointComparison C d S
  constructor
  · intro hz
    have h : c z ∈ Set.range rel := by
      rw [hrange, hfix]
      exact ⟨habs, hz⟩
    obtain ⟨⟨n, t, p⟩, hq⟩ := h
    obtain ⟨y, hy₁, hy₂⟩ := gather_both ns ps (blocks_nodup o) n p
    obtain ⟨v, hv⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).surjective
      (evT (pinnedMarkedTorusPoint C d S t))
    have ht : torusPoint D R v = evT (pinnedMarkedTorusPoint C d S t) := hv
    refine ⟨v, fun a => y (o.block a), ?_, ?_⟩
    · change _ ∈ Set.range j
      rw [← hfix]
      refine ⟨descendedTorusInclusion S t, ?_⟩
      change ev (pinnedMarkedPoint C d S (descendedTorusInclusion S t)) = _
      rw [hinc, ht]
      exact markedTorusPoint_map M.toIntegralMarking (evaluateGroundTensor k K) _
    · apply (Arithmetic.ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking _ _
        o.negative_enumerates o.positive_enumerates).1 R
      change c _ = c z
      rw [hc, hy₁, hy₂, ht]
      exact hq
  · rintro ⟨t, x, ht, rfl⟩
    let y := blockParameters o x
    have he : (fun a => y (o.block a)) = x := funext (blockParameters_apply o x)
    change torusPoint D R t ≫ M.torus.hom.hom ∈ Set.range j at ht
    rw [← hfix] at ht
    obtain ⟨p, hp⟩ := ht
    obtain ⟨s, hs⟩ := hevT (torusPoint D R t)
    obtain ⟨t', ht'⟩ := (htor s).mpr ⟨p, hev (hp.trans
      ((congrArg (· ≫ M.torus.hom.hom) hs.symm).trans
        (markedTorusPoint_map M.toIntegralMarking (evaluateGroundTensor k K) s).symm))⟩
    change c (o.coordinates u σ t x) ∈ j.range
    rw [← he, hc, ← hs, ← ht']
    exact hrel (gather y ns, t', gather y ps)

section Walls

open private map_upperMatrix markedRootPoint_zero markedTorusPointHom markedTorusPointHom_apply
  quadraticGalois from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private splitMarkedNormalizerWord valuationRingTorusPoint from
  LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private weylWord_index wallMatrix_map from
  LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private reflection_natural rationalCocharacterAction from
  LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private folded_reflection_action from
  LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

open Matrix (SpecialLinearGroup)

private theorem simpleWord (w : List (SimpleRootOrbit D)) :
    ∀ i ∈ w.flatMap SimpleRootOrbit.roots, i ∈ D.base.support := by
  intro i hi
  obtain ⟨⟨a, b⟩, _, hi⟩ := List.mem_flatMap.mp hi
  cases b with
  | none =>
    have h : i = a.val := by simpa [SimpleRootOrbit.roots] using hi
    exact h ▸ a.property
  | some b =>
    have h : i = a.val ∨ i = b.val := by simpa [SimpleRootOrbit.roots] using hi
    exact h.elim (fun e => e ▸ a.property) (fun e => e ▸ b.property)

private theorem block_mem {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (a : FoldedRootDirection) : o.block a ∈ o.negative ++ o.positive := by
  let i := firstLabel (o.block a)
  have hi : i ∈ transportedLabels (o.block a) := firstLabel_mem _
  classical
  by_cases hp : D.base.IsPos i
  · obtain ⟨b, hb, hbi⟩ := List.mem_flatMap.mp ((o.positive_enumerates.2 i).mpr hp)
    have he := block_eq o (List.mem_append_right o.negative hb) hbi
    rw [(o.fibre a i).mp hi] at he
    exact he ▸ (List.mem_append_right o.negative hb)
  · obtain ⟨b, hb, hbi⟩ := List.mem_flatMap.mp ((o.negative_enumerates.2 i).mpr hp)
    have he := block_eq o (List.mem_append_left o.positive hb) hbi
    rw [(o.fibre a i).mp hi] at he
    exact he ▸ (List.mem_append_left o.positive hb)

set_option backward.isDefEq.respectTransparency false in
private theorem splitOrbit_zero (M : IntegralMarking D) (σ : Gal(K/k)) (b : TransportedOrbit D) :
    splitOrbitPoint M (integralRing K) b
      (rationalOrbitCoordinates σ b (0 : rationalOrbitParameter k K b)) = 1 := by
  rcases b with ⟨⟨a, _ | c⟩, w⟩
  · change transportedRootPoint M (integralRing K) ((a, none), w) a (algebraMap k K 0) = 1
    rw [map_zero]
    simp [transportedRootPoint, markedRootPoint_zero]
  · change transportedRootPoint M (integralRing K) ((a, some c), w) a 0 *
      transportedRootPoint M (integralRing K) ((a, some c), w) c (σ 0) = 1
    rw [map_zero]
    simp [transportedRootPoint, markedRootPoint_zero]

private theorem singleBlock_product (M : IntegralMarking D) (σ : Gal(K/k))
    (y : ∀ b : TransportedOrbit D, rationalOrbitParameter k K b)
    (b : TransportedOrbit D) (hy : ∀ c, c ≠ b → y c = 0)
    (bs : List (TransportedOrbit D)) (hn : bs.Nodup) :
    open scoped Classical in
    splitOrderedOrbitPoint M (integralRing K) bs (rationalOrderedCoordinates σ bs (gather y bs)) =
      if b ∈ bs then splitOrbitPoint M (integralRing K) b (rationalOrbitCoordinates σ b (y b)) else 1 := by
  classical
  induction bs with
  | nil => simp [splitOrderedOrbitPoint]
  | cons c cs ih =>
    change splitOrbitPoint M (integralRing K) c (rationalOrbitCoordinates σ c (y c)) *
      splitOrderedOrbitPoint M (integralRing K) cs (rationalOrderedCoordinates σ cs (gather y cs)) = _
    rw [ih (List.nodup_cons.mp hn).2]
    by_cases h : c = b
    · subst c
      simp [(List.nodup_cons.mp hn).1]
    · simp [hy c h, splitOrbit_zero, Ne.symm h]

set_option backward.isDefEq.respectTransparency false in
private theorem upperCell {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (M : IntegralMarking D) (σ : Gal(K/k))
    (u : TransportedOrbit D → D.I → Integers.{u}ˣ) (hu : IsTransportUnitSystem M u)
    (a : FoldedRootDirection) (z : rationalOrbitParameter k K (o.block a)) :
    cellValue M (integralRing K) _ _ (o.coordinates u σ 1
      (Function.update (fun _ => 0) a z)) =
      splitOrbitPoint M (integralRing K) (o.block a)
        (rationalOrbitCoordinates σ (o.block a) z) := by
  classical
  let b := o.block a
  let x : ∀ a, rationalOrbitParameter k K (o.block a) := Function.update (fun _ => 0) a z
  let y := blockParameters o x
  have hy (c : TransportedOrbit D) (hc : c ≠ b) : y c = 0 := by
    unfold y blockParameters
    split
    next h =>
      have he : direction (firstLabel c) ≠ a := fun e => hc (by simpa only [e] using h.symm)
      have cast_zero {b c : TransportedOrbit D} (h : b = c) :
          (h ▸ (0 : rationalOrbitParameter k K b) : rationalOrbitParameter k K c) = 0 := by
        cases h
        rfl
      simpa only [show x (direction (firstLabel c)) = 0 from Function.update_of_ne he _ _] using
        cast_zero h
    next => rfl
  have hyb : y b = z := (blockParameters_apply o x a).trans (Function.update_self ..)
  rw [coordinates_eq o u σ 1 y x (blockParameters_apply o x), cellValue_blocks o M u hu σ y]
  let R := integralRing K
  have htor : (torusPoint D R 1 ≫ M.torus.hom.hom : IntegralPoints M.group R) = 1 :=
    map_one (markedTorusPointHom M R)
  have hn := List.nodup_append.mp (blocks_nodup o)
  change _ * ((_ : IntegralPoints M.group R) * _) = _
  rw [htor, one_mul,
    singleBlock_product M σ y b hy o.negative hn.1,
    singleBlock_product M σ y b hy o.positive hn.2.1, hyb]
  rcases List.mem_append.mp (block_mem o a) with h | h
  · have hp : b ∉ o.positive := fun h' => hn.2.2 b h b h' rfl
    have hn' : b ∈ o.negative := h
    rw [ite_eq_left hn', ite_eq_right hp, mul_one]
  · have hn' : b ∉ o.negative := fun h' => hn.2.2 b h' b h rfl
    have hp : b ∈ o.positive := h
    rw [ite_eq_right hn', ite_eq_left hp, one_mul]

private theorem diagonal_map {E F : Type*} [CommRing E] [CommRing F]
    (f : E →+* F) (p : Eˣ) :
    SpecialLinearGroup.map f (diagonal p) = diagonal (Units.map f.toMonoidHom p) := by
  apply Subtype.ext
  change (diagonal p).val.map f = (diagonal (Units.map f.toMonoidHom p)).val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

private theorem unitTorus_of_values [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (M : Model D) (t : TorusValues D (integralRing K))
    (ht : ∀ χ, Specs.ExceptionalLocalRootCoordinates.normalizedValuation K (t χ : K) = 1) :
    (torusPoint D (integralRing K) t ≫ M.torus.hom.hom) ∈ integralUnitTorus (K := K) M := by
  classical
  let _ := D.freeY
  let _ := D.finiteY
  let b := Module.Free.chooseBasis ℤ D.Y
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
  obtain ⟨s, hs⟩ :=
    (Arithmetic.ExceptionalValuedTorusNormalizer.integralTorusCoordinates D b t).mp (fun _ => ht _)
  refine ⟨torusPoint D _ s, ?_⟩
  exact (valuationRingTorusPoint M s).trans (congrArg (fun v => torusPoint D _ v ≫ M.torus.hom.hom) hs)

private theorem unitTorus_diagonal [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (M : Model D) (i : D.I) (p : Kˣ)
    (hp : Specs.ExceptionalLocalRootCoordinates.normalizedValuation K (p : K) = 1) :
    ((M.rankOne i).app (integralRing K) (diagonal p) : IntegralPoints M.group (integralRing K)) ∈
      integralUnitTorus (K := K) M := by
  rw [M.rankOneDiagonal]
  apply unitTorus_of_values M
  intro χ
  change Specs.ExceptionalLocalRootCoordinates.normalizedValuation K
    (↑(p ^ D.datum.toLinearMap χ.toAdd (D.datum.coroot i) : Kˣ) : K) = 1
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hp, one_zpow]

set_option backward.isDefEq.respectTransparency false in
private theorem unitTorus_conj_word [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {M : Model D} (F : FibreNormalizer M K)
    (w : List (SimpleRootOrbit D)) {g : IntegralPoints M.group (integralRing K)}
    (hg : g ∈ integralUnitTorus (K := K) M) :
    let H := markedWeylWord M.toIntegralMarking (integralRing K) (w.flatMap SimpleRootOrbit.roots)
    H * g * H⁻¹ ∈ integralUnitTorus (K := K) M := by
  intro H
  let _ := F.torusComm
  obtain ⟨n, hn, _⟩ := splitMarkedNormalizerWord F _ (simpleWord w)
  obtain ⟨f, hf, ha⟩ := Arithmetic.ExceptionalValuedTorusNormalizer.fibreNormalizerTorusAction F
  obtain ⟨p, hp⟩ := hg
  obtain ⟨s, hs⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) _).surjective p
  have hps : torusPoint D _ s = p := hs
  rw [← hps] at hp
  let q := (F.label n).val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  let s' := s.comp q
  refine ⟨torusPoint D _ s', ?_⟩
  let inc := (integralPointFunctor (splitTorus D)).map (valuationRingInclusion K)
  change (inc (torusPoint D _ s') ≫ M.torus.hom.hom) = H * g * H⁻¹
  change (inc (torusPoint D _ s) ≫ M.torus.hom.hom) = g at hp
  rw [← hp, valuationRingTorusPoint, valuationRingTorusPoint]
  have h := congrArg (fun t : F.label.ker => F.point t.val)
    (ha n ((Units.map (valuation K).valuationSubring.subtype.toMonoidHom).comp s))
  change F.point (n * (f _).val * n⁻¹) = F.point (f _).val at h
  rw [map_mul, map_mul, map_inv, hn, hf, hf] at h
  exact h.symm

private theorem transportedCoroot (w : D.datum.weylGroup) (i : D.I) :
    w.val.coweightEquiv.symm (D.datum.coroot i) = D.datum.coroot (w.val.indexEquiv i) := by
  apply w.val.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  simp [RootPairing.Equiv.coweightEquiv_apply, RootPairing.Hom.coroot_coweightMap_apply]

private theorem coroot_baseChange (τ : Pinning.BasedIso D D) (i : D.I) :
    diagramCocharacters (K := ℚ) τ.val ((ApartmentRoots.split D.datum ℚ).coroot i) =
      (ApartmentRoots.split D.datum ℚ).coroot (τ.val.indexEquiv i) := by
  change diagramCocharacters τ.val (1 ⊗ₜ[ℤ] D.datum.coroot i) = 1 ⊗ₜ[ℤ] D.datum.coroot (τ.val.indexEquiv i)
  simp only [diagramCocharacters, LinearEquiv.baseChange_tmul]
  congr 1
  apply τ.val.coweightEquiv.injective
  simp [RootPairing.Equiv.coweightEquiv_apply, RootPairing.Hom.coroot_coweightMap_apply]

private theorem reflection_baseChange (D : BasedRootDatum.{u}) (i : D.I) :
    rationalCocharacterAction D (RootPairing.Equiv.reflection D.datum i) =
      (ApartmentRoots.split D.datum ℚ).linearReflection i := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro q y
  change (q ⊗ₜ[ℤ] ((RootPairing.Equiv.reflection D.datum i).coweightEquiv.symm y)) =
    (ApartmentRoots.split D.datum ℚ).linearReflection i (q ⊗ₜ[ℤ] y)
  rw [RootPairing.Equiv.reflection_coweightEquiv]
  change q ⊗ₜ[ℤ] (Module.reflection _).symm y = Module.reflection _ (q ⊗ₜ[ℤ] y)
  rw [Module.reflection_symm, Module.reflection_apply, Module.reflection_apply, TensorProduct.tmul_sub]
  congr 1
  change q ⊗ₜ[ℤ] (D.datum.root' i y • D.datum.coroot i) =
    RootData.extendFunctional ℚ (D.datum.root' i) (q ⊗ₜ[ℤ] y) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i)
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
  simp only [RootData.extendFunctional, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul]
  change _ = (((D.datum.root' i y) • q) * 1) ⊗ₜ[ℤ] _
  rw [mul_one]


local notation "vNorm" => Specs.ExceptionalLocalRootCoordinates.normalizedValuation

private def rankOneProduct (M : Model D) (σ : Gal(K/k))
    (b : TransportedOrbit D) (U : SpecialLinearGroup (Fin 2) (rationalOrbitParameter k K b)) :
    IntegralPoints M.group (integralRing K) :=
  let word := b.2.flatMap SimpleRootOrbit.roots
  let H := markedWeylWord M.toIntegralMarking (integralRing K) word
  H * ((b.1.1 :: b.1.2.toList).map (fun (i : D.base.support) =>
    (show IntegralPoints M.group (integralRing K) from (M.rankOne i.val).app (integralRing K)
      (SpecialLinearGroup.map (slotMap σ b (weylWordPerm word i.val)) U)))).prod * H⁻¹

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneProduct_upper (M : Model D) (σ : Gal(K/k))
    (b : TransportedOrbit D) (hn : (transportedLabels b).Nodup)
    (z : rationalOrbitParameter k K b) :
    rankOneProduct M σ b (upper z) =
      splitOrbitPoint M.toIntegralMarking (integralRing K) b (rationalOrbitCoordinates σ b z) := by
  rcases b with ⟨⟨a, _ | c⟩, w⟩
  · simp only [rankOneProduct, Option.toList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_upperMatrix, M.rankOneUpper]
    rfl
  · let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots)
    have hne : p c.val ≠ p a.val := by
      simpa [p, transportedLabels, SimpleRootOrbit.roots, ne_comm] using hn
    simp only [rankOneProduct, Option.toList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_upperMatrix, map_upperMatrix, M.rankOneUpper, M.rankOneUpper]
    have hne' : weylWordPerm (w.flatMap SimpleRootOrbit.roots) c.val ≠
        weylWordPerm (w.flatMap SimpleRootOrbit.roots) a.val := hne
    simp only [slotMap, hne', ite_false, ite_true, eq_self,
      rationalOrbitCoordinates, splitOrbitPoint, transportedRootPoint, markedRootPoint]
    group
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneProduct_diagonal [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {M : Model D} (F : FibreNormalizer M K) (σ : Gal(K/k))
    (b : TransportedOrbit D) (z : (rationalOrbitParameter k K b)ˣ)
    (hz : ∀ i, vNorm K (slotMap σ b i (z : rationalOrbitParameter k K b)) = 1) :
    rankOneProduct M σ b (diagonal z) ∈ integralUnitTorus (K := K) M := by
  unfold rankOneProduct
  apply unitTorus_conj_word F
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  rw [diagonal_map]
  exact unitTorus_diagonal M i _ (hz _)

private theorem conjugateReflection (w : D.datum.weylGroup) (i : D.I) :
    w * RootPairing.weylGroup.ofIdx D.datum i * w⁻¹ =
      RootPairing.weylGroup.ofIdx D.datum (w.val.indexEquiv i) := by
  apply Subtype.ext
  change w.val * (RootPairing.Equiv.reflection D.datum i) * w.val⁻¹ = _
  exact mul_inv_eq_iff_eq_mul.mpr (reflection_natural D w.val i)

private theorem pairing_transport (w : D.datum.weylGroup) (i j : D.I) :
    D.datum.pairing (w.val.indexEquiv i) (w.val.indexEquiv j) = D.datum.pairing i j :=
  w.val.toHom.pairing

private theorem label_singleton (τ : Pinning.BasedIso D D) (i : D.I)
    (hi : τ.val.indexEquiv i = i) : RootPairing.weylGroup.ofIdx D.datum i ∈ fixedWeylGroup D τ := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change (RootPairing.Equiv.reflection D.datum i) * τ.val = τ.val * _
  have h := reflection_natural D τ.val i
  rw [hi] at h
  exact h.symm

private theorem label_pair (τ : Pinning.BasedIso D D) (i j : D.I)
    (hi : τ.val.indexEquiv i = j) (hj : τ.val.indexEquiv j = i)
    (horth : D.datum.pairing i j = 0) :
    RootPairing.weylGroup.ofIdx D.datum i * RootPairing.weylGroup.ofIdx D.datum j ∈ fixedWeylGroup D τ := by
  let s := RootPairing.weylGroup.ofIdx D.datum
  have hfix : D.datum.reflectionPerm j i = i := by
    apply D.datum.root.injective
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_root, horth, zero_smul, sub_zero]
  have hcomm : (s j).val * (s i).val = (s i).val * (s j).val := by
    have h := reflection_natural D (s j).val i
    change (s j).val * (s i).val = (s (D.datum.reflectionPerm j i)).val * (s j).val at h
    simpa only [hfix] using h
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Commute.symm
  change τ.val * ((s i).val * (s j).val) = ((s i).val * (s j).val) * τ.val
  have h₁ : τ.val * (s i).val = (s j).val * τ.val := by
    have h := reflection_natural D τ.val i
    rw [hi] at h
    exact h
  have h₂ : τ.val * (s j).val = (s i).val * τ.val := by
    have h := reflection_natural D τ.val j
    rw [hj] at h
    exact h
  rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc, hcomm]

private theorem singleton_fixed {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (τ : Pinning.BasedIso D D)
    (horbit : ∀ i j, direction i = direction j ↔ j = i ∨ j = τ.val.indexEquiv i)
    (a : FoldedRootDirection) (i : D.I) (hl : transportedLabels (o.block a) = [i]) :
    direction i = a ∧ τ.val.indexEquiv i = i := by
  have hi := (o.fibre a i).mp (by simp [hl])
  refine ⟨hi, ?_⟩
  have ht := (o.fibre a (τ.val.indexEquiv i)).mpr
    (((horbit i _).mpr (Or.inr rfl)).symm.trans hi)
  simpa only [hl, List.mem_singleton] using ht

private theorem pair_swapped {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (τ : Pinning.BasedIso D D) (hτ : Function.Involutive τ.val.indexEquiv)
    (horbit : ∀ i j, direction i = direction j ↔ j = i ∨ j = τ.val.indexEquiv i)
    (a : FoldedRootDirection) (i j : D.I) (hl : transportedLabels (o.block a) = [i,j])
    (hne : i ≠ j) : direction i = a ∧ τ.val.indexEquiv i = j ∧ τ.val.indexEquiv j = i := by
  have hi := (o.fibre a i).mp (by simp [hl])
  have hj := (o.fibre a j).mp (by simp [hl])
  have h := ((horbit i j).mp (hi.trans hj.symm)).resolve_left hne.symm
  exact ⟨hi, h.symm, h ▸ hτ i⟩

private theorem orbit_orthogonal {direction : D.I → FoldedRootDirection} (o : OrbitOrdering direction)
    (τ : Pinning.BasedIso D D) (hτ : Function.Involutive τ.val.indexEquiv)
    (horbit : ∀ i j, direction i = direction j ↔ j = i ∨ j = τ.val.indexEquiv i)
    {M : Model D} (C : MarkedFibre M k) (f : Aut C.realization.pinned)
    (hmatch : ∀ a, (o.block a).1.Matches C f)
    (hnodup : ∀ a, (transportedLabels (o.block a)).Nodup)
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (i : D.I) (hi : τ.val.indexEquiv i ≠ i) :
    D.datum.pairing i (τ.val.indexEquiv i) = 0 := by
  let a := direction i
  have hm := hmatch a
  have hn := hnodup a
  have hl := (o.fibre a i).mpr rfl
  generalize hb : o.block a = b at hm hn hl
  rcases b with ⟨⟨r, _ | s⟩, w⟩
  · let q := weylWordPerm (w.flatMap SimpleRootOrbit.roots) r.val
    have hlabel : transportedLabels (o.block a) = [q] := by rw [hb]; rfl
    have e : i = q := by simpa only [← hb, hlabel, List.mem_singleton] using hl
    exact False.elim (hi (e ▸ (singleton_fixed o τ horbit a q hlabel).2))
  · let e := (w.flatMap SimpleRootOrbit.roots |>.map (RootPairing.weylGroup.ofIdx D.datum)).prod
    let q := weylWordPerm (w.flatMap SimpleRootOrbit.roots) r.val
    let p := weylWordPerm (w.flatMap SimpleRootOrbit.roots) s.val
    have hlabel : transportedLabels (o.block a) = [q,p] := by rw [hb]; rfl
    have hne : q ≠ p := by simpa [q, p, transportedLabels, SimpleRootOrbit.roots] using hn
    have ⟨_, hq, hp⟩ := pair_swapped o τ hτ horbit a q p hlabel hne
    have hqp : D.datum.pairing q p = 0 := by
      change D.datum.pairing ((weylWordPerm _) r.val) ((weylWordPerm _) s.val) = _
      rw [weylWord_index]
      exact (pairing_transport e r s).trans hm.1
    have hmem : i = q ∨ i = p := by simpa only [← hb, hlabel, List.mem_cons, List.mem_nil_iff, or_false] using hl
    rcases hmem with h | h
    · simpa only [h, hq] using hqp
    · simpa only [h, hp, hsym p q] using hqp

private theorem splitUnitAt (P : Type u) [Field P] [ValuativeRel P] [TopologicalSpace P]
    [IsNonarchimedeanLocalField P] (m : ℤ) :
    ∃ p : Pˣ, vNorm P (p : P) = WithZero.exp (-m) := by
  obtain ⟨z, hz⟩ := (Arithmetic.ExceptionalIwahoriCongruence.localValuationNormalization P).1 (WithZero.exp (-m))
  change vNorm P z = _ at hz
  refine ⟨Units.mk0 z (fun he => WithZero.exp_ne_zero (a := -m) ?_), hz⟩
  simpa only [he, map_zero] using hz.symm

private theorem tensor_half (y : D.Y) :
    ((1 / 2 : ℚ) ⊗ₜ[ℤ] y) = (2 : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] y) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, one_div]

private theorem half_singleCoroot (D : BasedRootDatum.{u}) (m : ℤ) (i : D.I) :
    ((1 / 2 : ℚ) ⊗ₜ[ℤ] ((2 * -m) • D.datum.coroot i)) =
      (-(m : ℚ)) • (ApartmentRoots.split D.datum ℚ).coroot i := by
  change _ = (-(m : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i)
  rw [TensorProduct.tmul_smul, tensor_half, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  push_cast
  ring

private theorem half_pairCoroot (D : BasedRootDatum.{u}) (m : ℤ) (i j : D.I) :
    ((1 / 2 : ℚ) ⊗ₜ[ℤ] ((-m) • D.datum.coroot i + (-m) • D.datum.coroot j)) =
      (-(m : ℚ)) • ((2 : ℚ)⁻¹ • ((ApartmentRoots.split D.datum ℚ).coroot i +
        (ApartmentRoots.split D.datum ℚ).coroot j)) := by
  change _ = _ • ((2 : ℚ)⁻¹ • (((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i) + ((1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot j)))
  rw [← smul_add, ← TensorProduct.tmul_add, TensorProduct.tmul_smul, tensor_half,
    ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- The pinned rank-one groups give the affine wall lifts in the same
coordinates as the ordered chart. -/
theorem foldedWallLifts : WallLifts.{u} := by
  classical
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ D M C l G B T d σ τ hd hσ hram hsym hτ
    direction o horbit hlong hmatches hnodup u hu j _hj hj N F hpoints V A hroot hcoroot action haction a m
  let W := fixedWeylGroup D τ
  let L := rationalCocharacterAction D
  let E := ApartmentRoots.split D.datum ℚ
  let s := RootPairing.weylGroup.ofIdx D.datum
  let R := integralRing K
  let H := (𝟙_ (SchemeOver k) ⟶ G.val.X)
  have hσ₂ : Function.Involutive σ := by
    intro x
    exact congrArg (fun g : Gal(K/k) => g x) (quadraticGalois hd σ hσ).2
  have hσval (x : K) : vNorm K (σ x) = vNorm K x :=
    Arithmetic.ExceptionalValuedTorusNormalizer.involutiveValuationInvariant σ hσ₂ x
  have hort := orbit_orthogonal o τ hτ horbit C (pinnedDiagram d σ)
    (fun a => (hmatches a).1) hnodup hsym
  have hpartner (i : D.I) : direction (τ.val.indexEquiv i) = direction i :=
    ((horbit i _).mpr (Or.inr rfl)).symm
  have hreflection := folded_reflection_action D.datum τ.val direction A hpartner hlong hort hroot hcoroot
  have hcor (i : D.I) : (A.coroot (direction i)).val =
      (2 : ℚ)⁻¹ • (E.coroot i + E.coroot (τ.val.indexEquiv i)) := by
    rw [hcoroot]
    change (2 : ℚ)⁻¹ • (E.coroot i + diagramCocharacters τ.val (E.coroot i)) = _
    rw [coroot_baseChange]
  have hfinish (n : N.normalizer)
      (hl : ∀ x : V, L (N.label n).val.val x.val = (A.linearReflection a x).val)
      (ht : ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd) =
        (-(m : ℚ)) • (A.coroot a).val) :
      action n = A.wallReflection a m := by
    apply AffineEquiv.ext
    intro x
    apply Subtype.ext
    rw [haction n x]
    change L (N.label n).val.val x.val + _ = _
    rw [hl x, ht, (Arithmetic.ExceptionalAffineRootSystems.affineGroupNormalForms A).1]
    change x.val - A.root a x • (A.coroot a).val + (-(m : ℚ)) • (A.coroot a).val =
      x.val - (A.root a x + (m : ℚ)) • (A.coroot a).val
    simp only [add_smul, neg_smul, sub_eq_add_neg, neg_add, add_assoc]
  dsimp only
  suffices hw :
      ∃ (ρ : SpecialLinearGroup (Fin 2) (rationalOrbitParameter k K (o.block a)) →* H)
        (t : (rationalOrbitParameter k K (o.block a))ˣ) (n : N.normalizer),
        (∀ U, j (ρ U) = rankOneProduct M σ (o.block a) U) ∧
        (∀ z : (rationalOrbitParameter k K (o.block a))ˣ,
          vNorm (rationalOrbitParameter k K (o.block a)) z = 1 →
            ρ (diagonal z) ∈ (integralUnitTorus (K := K) M).comap j) ∧
        vNorm (rationalOrbitParameter k K (o.block a)) t = WithZero.exp (-m) ∧
        (n : H) = ρ (wallMatrix t) ∧ action n = A.wallReflection a m by
    obtain ⟨ρ, t, n, hρ, hdiag, ht, hn, ha⟩ := hw
    refine ⟨ρ, t, n, hρ, ?_, hdiag, ht, hn, ha⟩
    intro z
    rw [hρ, rankOneProduct_upper M σ _ (hnodup a)]
    exact (upperCell o M.toIntegralMarking σ u hu a z).symm
  have hm := hmatches a
  have hnd := hnodup a
  generalize hb : o.block a = b at hm hnd ⊢
  rcases b with ⟨⟨i, _ | i'⟩, w⟩
  all_goals
    let word := w.flatMap SimpleRootOrbit.roots
    let H₀ := markedWeylWord M.toIntegralMarking R word
    let e := (word.map s).prod
    let p := weylWordPerm word
    let q := p i.val
    have hwperm : p = e.val.indexEquiv := weylWord_index word
    have hqi : e.val.indexEquiv i.val = q := congrFun (congrArg DFunLike.coe hwperm.symm) _
    let _ := D.freeY
    let _ := D.finiteY
    let basis := Module.Free.chooseBasis ℤ D.Y
    let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ D.Y)
    have hwalls := Arithmetic.ExceptionalLocalRootCoordinates.pinnedRankOneWallLifts
      C F d hd σ hσ hsym j N W.subtype hj Subtype.val_injective hpoints w hm.2
    have hdis := Arithmetic.ExceptionalLocalRootCoordinates.markedWallDisplacements F basis j N W.subtype
      Subtype.val_injective hpoints word (simpleWord w)
  · have hlabels : transportedLabels (o.block a) = [q] := by rw [hb]; rfl
    obtain ⟨hqa, hqfix⟩ := singleton_fixed o τ horbit a q hlabels
    let v : W := ⟨s q, label_singleton τ q hqfix⟩
    have hconj : e * s i.val * e⁻¹ = s q := (conjugateReflection e i.val).trans (congrArg s hqi)
    obtain ⟨ρ, hρ, hlift⟩ := hwalls.1 i hm.1
    obtain ⟨t, ht⟩ := splitUnitAt k m
    obtain ⟨n, hn, hnL⟩ := hlift v hconj.symm t
    let b : TransportedOrbit D := ((i, none), w)
    have hρ' (U : SpecialLinearGroup (Fin 2) k) : j (ρ U) = rankOneProduct M σ b U := by
      rw [hρ]
      simp only [rankOneProduct, b, slotMap, Option.toList, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      rfl
    let t' := Units.map (algebraMap k K).toMonoidHom t
    have hwall : j n = H₀ * markedWall M.toIntegralMarking R i t' * H₀⁻¹ := by
      rw [hn, hρ, wallMatrix_map]
      rfl
    have hnL' : (N.label n).val = s q := congrArg Subtype.val hnL
    have hδ := hdis.1 i t' n (hnL'.trans hconj.symm) hwall
    have hlog : WithZero.log (vNorm K (t' : K)) = (2 : ℤ) * -m := by
      change WithZero.log (vNorm K (algebraMap k K t)) = _
      rw [hram, ht, WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul]
      rfl
    have hshift : (N.translation (N.torusPart n)).toAdd = (2 * -m) • D.datum.coroot q := by
      change _ = e.val.coweightEquiv.symm (WithZero.log (vNorm K (t' : K)) • D.datum.coroot i.val) at hδ
      simpa only [hlog, map_zsmul, transportedCoroot, hqi] using hδ
    have hc : (A.coroot a).val = E.coroot q := by
      rw [← hqa, hcor, hqfix, ← two_smul ℚ (E.coroot q), smul_smul]
      norm_num
    refine ⟨ρ, t, n, hρ', ?_, ht, hn, hfinish n ?_ ?_⟩
    · intro z hz
      change kˣ at z
      change j (ρ (diagonal z)) ∈ integralUnitTorus (K := K) M
      rw [hρ']
      apply rankOneProduct_diagonal F
      intro l
      change vNorm K (algebraMap k K (z : k)) = 1
      rw [hram]
      change vNorm k (z : k) = 1 at hz
      simp [hz]
    · intro x
      rw [hnL', show L (s q).val = E.linearReflection q from reflection_baseChange D _,
        ← hqa]
      exact ((hreflection q x).1 hqfix).symm
    · rw [hshift, half_singleCoroot, hc]
  · let q' := p i'.val
    have hq'i : e.val.indexEquiv i'.val = q' := congrFun (congrArg DFunLike.coe hwperm.symm) _
    have hlabels : transportedLabels (o.block a) = [q,q'] := by rw [hb]; rfl
    have hne : q ≠ q' := by simpa [← hb, hlabels] using hnd
    obtain ⟨hqa, hswap, hswap'⟩ := pair_swapped o τ hτ horbit a q q' hlabels hne
    have horth : D.datum.pairing q q' = 0 := by
      rw [← hqi, ← hq'i, pairing_transport]
      exact hm.1.1
    let v : W := ⟨s q * s q', label_pair τ q q' hswap hswap' horth⟩
    have hconj : e * (s i.val * s i'.val) * e⁻¹ = s q * s q' := by
      calc
        _ = (e * s i.val * e⁻¹) * (e * s i'.val * e⁻¹) := by group
        _ = _ := by rw [conjugateReflection, conjugateReflection, hqi, hq'i]
    obtain ⟨ρ, hρ, hlift⟩ := hwalls.2 i i' hm.1
    obtain ⟨t, ht⟩ := splitUnitAt K m
    obtain ⟨n, hn, hnL⟩ := hlift v hconj.symm t
    let b : TransportedOrbit D := ((i, some i'), w)
    have hρ' (U : SpecialLinearGroup (Fin 2) K) : j (ρ U) = rankOneProduct M σ b U := by
      rw [hρ]
      have hne' : weylWordPerm (w.flatMap SimpleRootOrbit.roots) i'.val ≠
          weylWordPerm (w.flatMap SimpleRootOrbit.roots) i.val := hne.symm
      simp only [rankOneProduct, b, slotMap, eq_self, ite_true, hne', ite_false, Option.toList,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have hU : SpecialLinearGroup.map (RingHom.id K) U = U := by
        apply Subtype.ext
        ext i j
        rfl
      erw [hU]
      rfl
    let t' := Units.map σ.toRingHom.toMonoidHom t
    have hwall : j n = H₀ * (markedWall M.toIntegralMarking R i t *
        markedWall M.toIntegralMarking R i' t') * H₀⁻¹ := by
      rw [hn, hρ, wallMatrix_map]
      rfl
    have hnL' : (N.label n).val = s q * s q' := congrArg Subtype.val hnL
    have hδ := hdis.2 i i' t t' n hsym hm.1.1 (hnL'.trans hconj.symm) hwall
    have hlog : vNorm K (t' : K) = WithZero.exp (-m) := (hσval t).trans ht
    have hshift : (N.translation (N.torusPart n)).toAdd =
        (-m) • D.datum.coroot q + (-m) • D.datum.coroot q' := by
      change _ = e.val.coweightEquiv.symm (WithZero.log (vNorm K (t : K)) • D.datum.coroot i.val +
        WithZero.log (vNorm K (t' : K)) • D.datum.coroot i'.val) at hδ
      simpa only [ht, hlog, WithZero.log_exp, map_add, map_zsmul, transportedCoroot, hqi, hq'i] using hδ
    have hc : (A.coroot a).val = (2 : ℚ)⁻¹ • (E.coroot q + E.coroot q') := by
      rw [← hqa, hcor, hswap]
    refine ⟨ρ, t, n, hρ', ?_, ht, hn, hfinish n ?_ ?_⟩
    · intro z hz
      change Kˣ at z
      change j (ρ (diagonal z)) ∈ integralUnitTorus (K := K) M
      rw [hρ']
      apply rankOneProduct_diagonal F
      intro l
      change vNorm K ((if l = q then RingHom.id K else σ.toRingHom) (z : K)) = 1
      change vNorm K (z : K) = 1 at hz
      split
      · exact hz
      · exact (hσval z).trans hz
    · intro x
      rw [hnL', Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply,
        show L (s q).val = E.linearReflection q from reflection_baseChange D _,
        show L (s q').val = E.linearReflection q' from reflection_baseChange D _,
        ← hqa]
      rw [← hswap]
      exact ((hreflection q x).2 (hswap.trans_ne hne.symm)).symm
    · rw [hshift, half_pairCoroot, hc]

end Walls

end
end LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart
