import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RealPolynomialChartTriangulation
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.LocallyClosed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Topology.LocalAtTarget

noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs
open RealPolynomialChartTriangulationSpecs (zeroLocus)

private theorem eq_of_eq_in_window {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (U : Submodule R M) (W : Submodule R U) {P Q : Submodule R M}
    (hPU : P ≤ U) (hQU : Q ≤ U)
    (hWP : W ≤ P.comap U.subtype) (hWQ : W ≤ Q.comap U.subtype)
    (h : (P.comap U.subtype).map W.mkQ = (Q.comap U.subtype).map W.mkQ) :
    P = Q := by
  have hcomap := congrArg (Submodule.comap W.mkQ) h
  rw [Submodule.comap_map_eq_self (by simpa using hWP),
    Submodule.comap_map_eq_self (by simpa using hWQ)] at hcomap
  have hmap := congrArg (Submodule.map U.subtype) hcomap
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hPU, inf_eq_right.mpr hQU] using hmap

open private quotientSubspace from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

private theorem boundedSubspace_injective (N : ℕ) :
    Function.Injective (boundedSubspace (r := 2) (N := N)) := by
  let U := (scalarLattice 2 (-(N : ℤ))).val
  let W := windowLower 2 (-(N : ℤ)) (2 * N)
  intro L M h
  unfold boundedSubspace latticeSubspace quotientSubspace at h
  have hEq := Submodule.restrictScalars_injective ℂ O _ h
  have hw (B : BoundedLattice 2 N) : W ≤ B.val.val.comap U.subtype := by
    change (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val.comap U.subtype ≤ _
    rw [boundedExponent]
    exact Submodule.comap_mono B.property.1
  exact Subtype.ext (Subtype.ext (eq_of_eq_in_window U W L.property.2 M.property.2
    (hw L) (hw M) hEq))

private theorem orbitIndex_le_difference (ab : DominantPair) (i : OrbitIndex ab) :
    2 * (i.val : ℤ) ≤ ab.val.1 - ab.val.2 := by
  have hi := i.isLt
  have hab : ab.val.2 ≤ ab.val.1 := ab.property
  unfold difference at hi
  omega

private theorem orbitLabel_bounded {ab : DominantPair} {N : ℕ} (hN : OrbitBound ab N)
    (i : OrbitIndex ab) : OrbitBound (orbitLabel ab i) N := by
  have h0 := hN (0 : Fin 2)
  have h1 := hN (1 : Fin 2)
  simp only [pairCoweight, Fin.val_zero, ↓reduceIte] at h0
  have h1' : -(N : ℤ) ≤ ab.val.2 ∧ ab.val.2 ≤ (N : ℤ) := by
    simpa [pairCoweight] using h1
  have hi := orbitIndex_le_difference ab i
  intro k
  fin_cases k <;> simp [pairCoweight, orbitLabel] <;> omega

private theorem orbitLabel_injective (ab : DominantPair) :
    Function.Injective (orbitLabel ab) := by
  intro i j hij
  have heq := congrArg (fun cd : DominantPair ↦ cd.val.1) hij
  change ab.val.1 - (i.val : ℤ) = ab.val.1 - (j.val : ℤ) at heq
  exact Fin.ext (by omega)

private theorem below_iff_orbitLabel (ab cd : DominantPair) :
    Below cd ab ↔ ∃ i : OrbitIndex ab, cd = orbitLabel ab i := by
  constructor
  · rintro ⟨k, hk, ha, hb⟩
    have hlt : k < difference ab / 2 + 1 := by
      unfold difference
      omega
    exact ⟨⟨k, hlt⟩, Subtype.ext (Prod.ext ha hb)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, orbitIndex_le_difference ab i, rfl, rfl⟩

private theorem mem_orbitPoints_iff {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p : SchubertSpace ab N hN) (i : OrbitIndex ab) :
    p ∈ orbitPoints ab N hN i ↔ (E p).val.val ∈ gl2Orbit (orbitLabel ab i) := by
  constructor
  · rintro ⟨L, hL, hp⟩
    obtain rfl : L = (E p).val := boundedSubspace_injective N (hp.symm.trans (hE p))
    exact hL
  · intro hp
    exact ⟨(E p).val, hp, hE p⟩

private theorem orbitPoints_partition {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (smith : SmithClassification)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p : SchubertSpace ab N hN) : ∃! i : OrbitIndex ab, p ∈ orbitPoints ab N hN i := by
  obtain ⟨cd, hcd, hL⟩ := (E p).property
  obtain ⟨i, rfl⟩ := (below_iff_orbitLabel ab cd).mp hcd
  refine ⟨i, (mem_orbitPoints_iff E hE p i).mpr hL, ?_⟩
  intro j hj
  have hL' := (mem_orbitPoints_iff E hE p j).mp hj
  obtain ⟨ef, _, hef⟩ := smith.1 (E p).val.val
  exact orbitLabel_injective ab ((hef _ hL').trans (hef _ hL).symm)

section OrbitStages

variable {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}

private def tailPoints (i : OrbitIndex ab) : Set (SchubertSpace ab N hN) :=
  {p | ∃ j : OrbitIndex ab, i.val ≤ j.val ∧ p ∈ orbitPoints ab N hN j}

private theorem tailPoints_isClosed
    (smith : SmithClassification) (comparison : BoundedSchubertComparison)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val) (i : OrbitIndex ab) :
    IsClosed (tailPoints (hN := hN) i) := by
  let cd := orbitLabel ab i
  obtain ⟨_, _, _, _, hclosed, _, _⟩ := comparison cd N (orbitLabel_bounded hN i)
  let g : SchubertSpace ab N hN → BoundedLattice 2 N := fun p ↦ (E p).val
  have hg : Continuous g := continuous_subtype_val.comp E.continuous
  convert hclosed.preimage hg using 1
  ext p
  obtain ⟨j, hj, huniq⟩ := orbitPoints_partition smith E hE p
  have hL := (mem_orbitPoints_iff E hE p j).mp hj
  obtain ⟨ha, hb, _⟩ := smith.2 (orbitLabel ab j) (g p).val hL
  change (∃ l : OrbitIndex ab, i.val ≤ l.val ∧ p ∈ orbitPoints ab N hN l) ↔
    Between cd.val.1 cd.val.2 (g p).val
  rw [Between, ha, hb]
  change (∃ l : OrbitIndex ab, i.val ≤ l.val ∧ p ∈ orbitPoints ab N hN l) ↔
    ab.val.1 - (j.val : ℤ) ≤ ab.val.1 - (i.val : ℤ) ∧
      ab.val.2 + (i.val : ℤ) ≤ ab.val.2 + (j.val : ℤ)
  constructor
  · rintro ⟨l, hl, hp⟩
    obtain rfl := huniq l hp
    omega
  · intro h
    exact ⟨j, by omega, hj⟩

private theorem stagePoints_isOpen
    (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i)
    (closedTail : ∀ i, IsClosed (tailPoints (hN := hN) i)) (k : ℕ) :
    IsOpen (stagePoints ab N hN k) := by
  by_cases hk : k + 1 < difference ab / 2 + 1
  · let i : OrbitIndex ab := ⟨k + 1, hk⟩
    convert (closedTail i).isOpen_compl using 1
    ext p
    change (∃ l : OrbitIndex ab, l.val ≤ k ∧ p ∈ orbitPoints ab N hN l) ↔
      ¬ ∃ l : OrbitIndex ab, i.val ≤ l.val ∧ p ∈ orbitPoints ab N hN l
    obtain ⟨j, hj, huniq⟩ := partition p
    have hi : i.val = k + 1 := rfl
    constructor
    · rintro ⟨l, hl, hp⟩ ⟨m, hm, hp'⟩
      obtain rfl := huniq l hp
      obtain rfl := huniq m hp'
      omega
    · intro h
      exact ⟨j, by by_contra! hle; exact h ⟨j, by omega, hj⟩, hj⟩
  · have hall : stagePoints ab N hN k = Set.univ := by
      ext p
      obtain ⟨i, hi, _⟩ := partition p
      have hi' := i.isLt
      exact ⟨fun _ ↦ Set.mem_univ p, fun _ ↦ ⟨i, by omega, hi⟩⟩
    simpa only [hall] using isOpen_univ

private theorem stagePoints_mono :
    Monotone (stagePoints ab N hN) := by
  intro k l hkl p hp
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨i, hi.trans hkl, hpi⟩

private theorem stagePoints_last
    (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i) :
    stagePoints ab N hN (difference ab / 2) = Set.univ := by
  ext p
  obtain ⟨i, hi, _⟩ := partition p
  exact ⟨fun _ ↦ Set.mem_univ p, fun _ ↦ ⟨i, Nat.le_of_lt_succ i.isLt, hi⟩⟩

variable (openStage : ∀ k, IsOpen (stagePoints ab N hN k))
  (closedTail : ∀ i, IsClosed (tailPoints (hN := hN) i))
  {Y : TopCat.{0}} (f : Y ⟶ SchubertSpace ab N hN)

private def orbitStratum (i : OrbitIndex ab) : Stratum Y where
  ambientOpen := ⟨f ⁻¹' stagePoints ab N hN i.val, (openStage i.val).preimage f.hom.continuous⟩
  subset := (f ∘ Subtype.val) ⁻¹' tailPoints i
  closed := (closedTail i).preimage (f.hom.continuous.comp continuous_subtype_val)
  complexDimension := orbitDimension ab i.val

private theorem orbitStratum_range
    (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i)
    (i : OrbitIndex ab) :
    Set.range (orbitStratum openStage closedTail f i).inclusion = f ⁻¹' orbitPoints ab N hN i := by
  ext y
  constructor
  · rintro ⟨⟨⟨y', hstage⟩, htail⟩, rfl⟩
    change f y' ∈ orbitPoints ab N hN i
    obtain ⟨j, hj, hpj⟩ := hstage
    obtain ⟨l, hl, hpl⟩ := htail
    obtain ⟨m, _, hm⟩ := partition (f y')
    have hjl : j = l := (hm j hpj).trans (hm l hpl).symm
    have hij : i = j := Fin.ext (Nat.le_antisymm (hjl ▸ hl) hj)
    simpa only [hij] using hpj
  · intro hy
    change f y ∈ orbitPoints ab N hN i at hy
    exact ⟨⟨⟨y, ⟨i, le_rfl, hy⟩⟩, ⟨i, le_rfl, hy⟩⟩, rfl⟩

variable (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i)

private def stageStratification (k : ℕ) (hf : Set.range f = stagePoints ab N hN k) :
    Stratification Y where
  Index := {i : OrbitIndex ab // i.val ≤ k}
  stratum i := orbitStratum openStage closedTail f i.val
  partition := by
    intro y
    have hfy : f y ∈ stagePoints ab N hN k := hf ▸ Set.mem_range_self y
    obtain ⟨i, hi, hpi⟩ := hfy
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · change y ∈ Set.range (orbitStratum openStage closedTail f i).inclusion
      rwa [orbitStratum_range openStage closedTail f partition i]
    · rintro ⟨j, hj⟩ hpj
      change y ∈ Set.range (orbitStratum openStage closedTail f j).inclusion at hpj
      rw [orbitStratum_range openStage closedTail f partition j] at hpj
      apply Subtype.ext
      obtain ⟨l, _, hl⟩ := partition (f y)
      exact (hl j hpj).trans (hl i hpi).symm

private theorem stageStratification_realizes (k : ℕ)
    (hopen : IsOpenEmbedding f) (hf : Set.range f = stagePoints ab N hN k) :
    RealizesOrbitStage f k (stageStratification openStage closedTail f partition k hf) :=
  ⟨hopen, hf, Equiv.refl _,
    fun i ↦ ⟨orbitStratum_range openStage closedTail f partition i.val, rfl⟩⟩

private def previousStageOpen (k : ℕ) : Opens Y :=
  ⟨f ⁻¹' stagePoints ab N hN k, (openStage k).preimage f.hom.continuous⟩

private theorem previousStage_range (k : ℕ) (hf : Set.range f = stagePoints ab N hN (k + 1)) :
    Set.range (openInclusion (previousStageOpen openStage f k) ≫ f) =
      stagePoints ab N hN k := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hp
    have hp' : p ∈ Set.range f := hf ▸ stagePoints_mono (Nat.le_succ k) hp
    obtain ⟨y, rfl⟩ := hp'
    exact ⟨⟨y, hp⟩, rfl⟩

private def previousOrbitIndexEquiv (k : ℕ) (next : OrbitIndex ab) (hnext : next.val = k + 1) :
    {i : OrbitIndex ab // i.val ≤ k} ≃
      {i : {i : OrbitIndex ab // i.val ≤ k + 1} // i ≠ ⟨next, hnext.le⟩} where
  toFun i := ⟨⟨i.val, i.property.trans (Nat.le_succ k)⟩, by
    intro h
    have hi := i.property
    have heq := congrArg (fun j : {i : OrbitIndex ab // i.val ≤ k + 1} ↦ j.val.val) h
    change i.val.val = next.val at heq
    omega⟩
  invFun i := ⟨i.val.val, by
    have hi := i.val.property
    have hne : i.val.val.val ≠ k + 1 := by
      intro hi'
      exact i.property (Subtype.ext (Fin.ext (hi'.trans hnext.symm)))
    omega⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext (Subtype.ext rfl)

include partition in
private theorem stageAttachment {U : TopCat.{0}} (j : U ⟶ Y) (k : ℕ)
    (hk : k + 1 ≤ difference ab / 2)
    (hf : IsOpenEmbedding f) {P : Stratification Y} {Q : Stratification U}
    (hP : RealizesOrbitStage f (k + 1) P)
    (hQ : RealizesOrbitStage (j ≫ f) k Q) :
    Nonempty (AttachmentStratification j (orbitDimension ab (k + 1)) Q P) := by
  obtain ⟨_, hrP, eP, heP⟩ := hP
  obtain ⟨_, hrQ, eQ, heQ⟩ := hQ
  let next : OrbitIndex ab := ⟨k + 1, Nat.lt_succ_of_le hk⟩
  let index : {i : OrbitIndex ab // i.val ≤ k + 1} := ⟨next, le_rfl⟩
  let closed := eP.symm index
  have hc : eP closed = index := eP.apply_symm_apply index
  let tr : {i : {i : OrbitIndex ab // i.val ≤ k + 1} // i ≠ index} ≃
      {p : P.Index // p ≠ closed} :=
    eP.symm.subtypeEquiv (fun i ↦ not_congr eP.symm.injective.eq_iff.symm)
  let prev := eQ.trans ((previousOrbitIndexEquiv k next rfl).trans tr)
  have hp (q : Q.Index) : (eP (prev q).val).val = (eQ q).val := by
    change (eP (eP.symm _)).val = _
    rw [eP.apply_symm_apply]
    rfl
  refine ⟨{
    closedIndex := closed
    previousIndex := prev
    closedRange := ?_
    closedDimension := ?_
    previousRange := ?_
    previousDimension := ?_
    dimension_lt := ?_ }⟩
  · rw [(heP closed).1, hc]
    ext y
    change f y ∈ orbitPoints ab N hN next ↔ y ∉ Set.range j
    have hrange : y ∈ Set.range j ↔ f y ∈ stagePoints ab N hN k := by
      rw [← hrQ]
      exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, congrArg (fun v : Y ↦ f v) hu⟩,
        fun ⟨u, hu⟩ ↦ ⟨u, hf.injective hu⟩⟩
    rw [hrange]
    constructor
    · intro hn hstage
      obtain ⟨i, hi, hpi⟩ := hstage
      obtain ⟨l, _, hl⟩ := partition (f y)
      have hni : next = i := (hl next hn).trans (hl i hpi).symm
      have hnext : next.val = k + 1 := rfl
      rw [← hni, hnext] at hi
      omega
    · intro hn
      have hstage : f y ∈ stagePoints ab N hN (k + 1) := hrP ▸ Set.mem_range_self y
      obtain ⟨i, hi, hpi⟩ := hstage
      have hni : i.val = k + 1 := by
        by_contra hne
        exact hn ⟨i, by omega, hpi⟩
      rwa [show i = next from Fin.ext hni] at hpi
  · rw [(heP closed).2, hc]
  · intro q
    rw [(heP (prev q).val).1, hp q, (heQ q).1]
    ext y
    change f y ∈ orbitPoints ab N hN (eQ q).val ↔
      y ∈ j '' ((j ≫ f) ⁻¹' orbitPoints ab N hN (eQ q).val)
    constructor
    · intro hy
      have hfy : f y ∈ stagePoints ab N hN k := ⟨(eQ q).val, (eQ q).property, hy⟩
      rw [← hrQ] at hfy
      obtain ⟨u, hu⟩ := hfy
      refine ⟨u, ?_, hf.injective hu⟩
      change (j ≫ f) u ∈ orbitPoints ab N hN (eQ q).val
      rwa [hu]
    · rintro ⟨u, hu, rfl⟩
      exact hu
  · intro q
    rw [(heP (prev q).val).2, (heQ q).2, hp q]
  · intro q
    rw [(heQ q).2]
    have hq := (eQ q).property
    unfold orbitDimension
    omega

end OrbitStages

section Sheaves

open CategoryTheory.Limits

set_option linter.style.haveILetI false

open private constantPullbackIso locallyConstantFiniteRank_of_iso zero_locallyConstantFiniteRank
  pullback_locallyConstantFiniteRank pullbackIsLE pullbackIsGE plusIsLE_iff plusIsGE_iff
  supportedShriekIso closedInverseAdjunction openCounitIsIso constructibleFromOpenClosed
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem rational_locallyConstantFiniteRank (Y : TopCat.{0}) :
    LocallyConstantFiniteRank (rational Y) := by
  intro y
  let V : Coeff.{0} := ModuleCat.of ℚ (ULift.{0} ℚ)
  have hV : Module.Finite ℚ V := inferInstanceAs (Module.Finite ℚ (ULift.{0} ℚ))
  exact ⟨⊤, by trivial, V, hV, ⟨constantPullbackIso (openInclusion ⊤) V⟩⟩

private theorem shiftedConstant_isLE (Y : TopCat.{0}) (d : ℕ) :
    (shiftedConstant Y d).IsLE (-(d : ℤ)) := by
  let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff]
  change (DerivedCategory.TStructure.t (C := Sheaves Y)).IsLE (F⟦(d : ℤ)⟧) (-(d : ℤ))
  exact (DerivedCategory.TStructure.t (C := Sheaves Y)).isLE_shift F 0 _ _ (add_neg_cancel _)

private theorem shiftedConstant_isGE (Y : TopCat.{0}) (d : ℕ) :
    (shiftedConstant Y d).IsGE (-(d : ℤ)) := by
  let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  change (DerivedCategory.TStructure.t (C := Sheaves Y)).IsGE (F⟦(d : ℤ)⟧) (-(d : ℤ))
  exact (DerivedCategory.TStructure.t (C := Sheaves Y)).isGE_shift F 0 _ _ (add_neg_cancel _)

private theorem shiftedConstant_cohomology_zero (Y : TopCat.{0}) (d : ℕ) (q : ℤ)
    (hq : q ≠ -(d : ℤ)) : IsZero ((cohomology Y q).obj (shiftedConstant Y d).obj) := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · exact (plusIsGE_iff _ _).mp (shiftedConstant_isGE Y d) q hlt
  · exact (plusIsLE_iff _ _).mp (shiftedConstant_isLE Y d) q hgt

private def shiftedConstant_cohomologyIso (Y : TopCat.{0}) (d : ℕ) :
    (cohomology Y (-(d : ℤ))).obj (shiftedConstant Y d).obj ≅ rational Y := by
  let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  exact (shiftCohomology Y (-(d : ℤ)) (d : ℤ)).app F ≪≫
    (eqToIso (congrArg (cohomology Y) (neg_add_cancel (d : ℤ)))).app F ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves Y) 0).app (rational Y)

private theorem stratum_subset_eq_univ {Y : TopCat.{0}} (S : Stratum Y)
    (hS : Set.range S.inclusion = Set.univ) : S.subset = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨z, hz⟩ : y.val ∈ Set.range S.inclusion := hS.symm ▸ Set.mem_univ y.val
  have hzy : z.val = y := Subtype.ext hz
  exact hzy ▸ z.property

private theorem whole_closed_shriek_isGE {Y : TopCat.{0}} {Z : Set Y}
    (hZ : IsClosed Z) (hfull : Z = Set.univ) (F : BoundedBelow Y) (n : ℤ)
    (hn : F.IsGE n) : ((derivedExtraordinaryInverseImage hZ).obj F).IsGE n := by
  let A := LocalSheaf.closedExtensionPlus hZ
  let i := closedInclusion Z
  have hs : LocalSheaf.DerivedSupportedOn Z F := by
    subst Z
    intro q x hx
    exact (hx (Set.mem_univ x)).elim
  obtain ⟨G, ⟨e⟩⟩ := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ F).mpr hs
  let a := closedInverseAdjunction hZ
  let ff := Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)
  letI := ff.full
  letI := ff.faithful
  let c := (boundedBelowInverseImage i).mapIso e.symm ≪≫ asIso (a.counit.app G)
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves (TopCat.of Z))
  haveI := pullbackIsGE i F n hn
  exact t.isGE_of_iso (c ≪≫ supportedShriekIso hZ e) n

private theorem shiftedConstant_isMiddlePerverse {Y : TopCat.{0}} (P : Stratification Y) (d : ℕ)
    (hfull : ∀ p, Set.range (P.stratum p).inclusion = Set.univ)
    (hdim : ∀ p, (P.stratum p).complexDimension = d) :
    IsMiddlePerverse P (shiftedConstant Y d).obj := by
  let F := shiftedConstant Y d
  refine ⟨⟨?_, ?_⟩, F.property, ?_⟩
  · apply (Set.finite_singleton (-(d : ℤ))).subset
    intro q hq
    by_contra hne
    exact hq (shiftedConstant_cohomology_zero Y d q hne)
  · intro p q
    apply pullback_locallyConstantFiniteRank
    by_cases hq : q = -(d : ℤ)
    · subst q
      exact locallyConstantFiniteRank_of_iso (shiftedConstant_cohomologyIso Y d).symm
        (rational_locallyConstantFiniteRank Y)
    · exact zero_locallyConstantFiniteRank (shiftedConstant_cohomology_zero Y d q hq)
  · intro p
    let S := P.stratum p
    have hd : (P.stratum p).complexDimension = d := hdim p
    constructor
    · intro q hq
      have hle := pullbackIsLE S.inclusion F (-(d : ℤ)) (shiftedConstant_isLE Y d)
      exact (plusIsLE_iff _ _).mp hle q (by simpa only [hd] using hq)
    · intro q hq
      let G := (boundedBelowInverseImage (openInclusion S.ambientOpen)).obj F
      have hG := pullbackIsGE (openInclusion S.ambientOpen) F (-(d : ℤ))
        (shiftedConstant_isGE Y d)
      have hge := whole_closed_shriek_isGE S.closed (stratum_subset_eq_univ S (hfull p)) G _ hG
      exact (plusIsGE_iff _ _).mp hge q (by simpa only [hd] using hq)

private theorem normalizedOrbitIC_perverse {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {Y : TopCat.{0}} {s k : ℕ} {f : Y ⟶ SchubertSpace ab N hN}
    {P : Stratification Y} {D : DimensionFiltration Y s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) :
    IsMiddlePerverse P (complex D).obj := by
  cases h <;> assumption

private theorem normalizedOrbitIC_realizes {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {Y : TopCat.{0}} {s k : ℕ} {f : Y ⟶ SchubertSpace ab N hN}
    {P : Stratification Y} {D : DimensionFiltration Y s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) :
    RealizesOrbitStage f k P := by
  cases h <;> assumption

private theorem attach_normalizedOrbitIC {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {U Y : TopCat.{0}} {k d : ℕ} {f : Y ⟶ SchubertSpace ab N hN}
    {P : Stratification Y} {Q : Stratification U} {D : DimensionFiltration U d}
    {j : U ⟶ Y} (hj : IsOpenEmbedding j) (hs : orbitDimension ab (k + 1) < d)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D)
    (stage : RealizesOrbitStage f (k + 1) P)
    (strata : AttachmentStratification j (orbitDimension ab (k + 1)) Q P)
    (h : IsConstructibleOnBoundary j ((derivedDirectImage j).obj (complex D))) :
    IsNormalizedOrbitIC ab N hN f (k + 1) P (.attach D j hj hs) := by
  let F := complex D
  have hp := normalizedOrbitIC_perverse prev
  obtain ⟨hnew, hstrict, _⟩ :=
    MiddleExtension.attachmentIsMiddleExtension j hj _ Q P strata F hp h
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData j
  haveI : IsIso (a.counit.app F) := openCounitIsIso hj a F
  have hG := constructibleFromOpenClosed j hj strata F ((derivedDirectImage j).obj F)
    (asIso (a.counit.app F)) hp.1 h
  exact IsNormalizedOrbitIC.attach f P Q j hj hs prev stage strata h hG hnew hstrict

end Sheaves

private theorem zeroStage_isMiddlePerverse {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {P : Stratification Y}
    (h : RealizesOrbitStage f 0 P) :
    IsMiddlePerverse P (shiftedConstant Y (difference ab)).obj := by
  obtain ⟨_, hf, e, he⟩ := h
  apply shiftedConstant_isMiddlePerverse P
  · intro i
    apply Set.eq_univ_of_forall
    intro y
    rw [(he i).1]
    have hy : f y ∈ stagePoints ab N hN 0 := hf ▸ Set.mem_range_self y
    obtain ⟨j, hj, hpj⟩ := hy
    have hji : j = (e i).val := Fin.ext (by
      have hi := (e i).property
      omega)
    simpa only [Set.mem_preimage, hji] using hpj
  · intro i
    have hi : (e i).val.val = 0 := Nat.eq_zero_of_le_zero (e i).property
    simp [(he i).2, orbitDimension, hi]

/-- The constructibility assertion needed on the new orbit at each actual attachment. -/
def OrbitBoundaryConstructibility (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) : Prop :=
  ∀ k : ℕ, k + 1 ≤ difference ab / 2 →
    ∀ {U Y : TopCat.{0}} (f : Y ⟶ SchubertSpace ab N hN) (j : U ⟶ Y),
      IsOpenEmbedding j →
      ∀ (P : Stratification Y) (Q : Stratification U) (D : DimensionFiltration U (orbitDimension ab k)),
        RealizesOrbitStage f (k + 1) P →
        IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D →
        IsConstructibleOnBoundary j ((derivedDirectImage j).obj (complex D))

theorem schubertIntersectionConstructibility_of_boundaryConstructibility
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (hboundary : OrbitBoundaryConstructibility ab N hN) :
    ∃ (P : Stratification (SchubertSpace ab N hN))
      (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
      IsNormalizedOrbitIC ab N hN (𝟙 (SchubertSpace ab N hN)) (difference ab / 2) P D := by
  obtain ⟨E, hE, _⟩ := stratification ab N hN
  let X := SchubertSpace ab N hN
  have partition := orbitPoints_partition smith E hE
  have closedTail := tailPoints_isClosed smith comparison E hE
  have openStage := stagePoints_isOpen partition closedTail
  have build (k : ℕ) (hk : k ≤ difference ab / 2)
      (Y : TopCat.{0}) (f : Y ⟶ X) (hf : IsOpenEmbedding f)
      (hr : Set.range f = stagePoints ab N hN k) :
      ∃ (P : Stratification Y) (D : DimensionFiltration Y (orbitDimension ab k)),
        IsNormalizedOrbitIC ab N hN f k P D := by
    induction k generalizing Y with
    | zero =>
      let P := stageStratification openStage closedTail f partition 0 hr
      have hstage : RealizesOrbitStage f 0 P :=
        stageStratification_realizes openStage closedTail f partition 0 hf hr
      exact ⟨P, .top Y (difference ab), .top f P hstage (zeroStage_isMiddlePerverse hstage)⟩
    | succ k ih =>
      let P := stageStratification openStage closedTail f partition (k + 1) hr
      have hP : RealizesOrbitStage f (k + 1) P :=
        stageStratification_realizes openStage closedTail f partition (k + 1) hf hr
      let V := previousStageOpen openStage f k
      let j := openInclusion V
      have hj : IsOpenEmbedding j := V.isOpenEmbedding
      have hf' : IsOpenEmbedding (j ≫ f) := hf.comp hj
      have hr' := previousStage_range openStage f k hr
      obtain ⟨Q, D, hD⟩ := ih (Nat.le_of_succ_le hk) (TopCat.of V) (j ≫ f) hf' hr'
      have hQ := normalizedOrbitIC_realizes hD
      obtain ⟨strata⟩ := stageAttachment f partition j k hk hf hP hQ
      have hs : orbitDimension ab (k + 1) < orbitDimension ab k := by
        unfold orbitDimension
        omega
      exact ⟨P, .attach D j hj hs,
        attach_normalizedOrbitIC hj hs hD hP strata (hboundary k hk f j hj P Q D hP hD)⟩
  exact build (difference ab / 2) le_rfl X (𝟙 X) IsOpenEmbedding.id (by
    rw [stagePoints_last partition]
    exact Set.range_id)

/-- At difference zero or one the filtration consists of the single open orbit. -/
theorem schubertIntersectionConstructibility_of_difference_le_one
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (hd : difference ab ≤ 1) :
    ∃ (P : Stratification (SchubertSpace ab N hN))
      (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
      IsNormalizedOrbitIC ab N hN (𝟙 (SchubertSpace ab N hN)) (difference ab / 2) P D := by
  apply schubertIntersectionConstructibility_of_boundaryConstructibility comparison stratification smith
  intro k hk
  omega

section OrbitHomeomorphisms

open BoundedLatticeSpecs
open scoped MatrixGroups

private theorem boundedPoint_injective (N : ℕ) :
    Function.Injective (boundedPoint (r := 2) (N := N)) := by
  intro L M h
  have hsub := congrArg windowStageSubspace h
  have image_eq (B : BoundedLattice 2 N) :
      windowStageSubspace (boundedPoint B) = boundedSubspace B := by
    unfold windowStageSubspace boundedPoint windowStagePoint boundedSubspace
    exact subspacePoint_subspace _ _ _ _
  exact boundedSubspace_injective N ((image_eq L).symm.trans (hsub.trans (image_eq M)))

private def schubertStageHomeomorph (ab : DominantPair) (N : ℕ) (hn : OrbitBound ab N)
    (comparison : BoundedSchubertComparison) :
    schubertLatticeSet ab N ≃ₜ stageImage (-(N : ℤ)) (2 * N) (closureLattices ab) := by
  let g : schubertLatticeSet ab N → stageImage (-(N : ℤ)) (2 * N) (closureLattices ab) :=
    fun L ↦ ⟨boundedPoint L.val, ⟨L.val.val, L.property, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro L M hlm
      exact Subtype.ext (boundedPoint_injective N (congrArg Subtype.val hlm))
    · rintro ⟨p, L, hL, rfl⟩
      obtain ⟨B, rfl⟩ := (comparison ab N hn).2.2.1 L hL
      exact ⟨⟨B, hL⟩, rfl⟩
  have hi : IsInducing g := by
    have hb : IsInducing (boundedPoint (r := 2) (N := N)) := IsInducing.induced _
    exact IsInducing.subtypeVal.of_comp_iff.mp (hb.comp IsInducing.subtypeVal)
  exact (Equiv.ofBijective g hg).toHomeomorphOfIsInducing hi

private theorem schubertStageHomeomorph_apply (ab : DominantPair) (N : ℕ) (hn : OrbitBound ab N)
    (comparison : BoundedSchubertComparison) (L : schubertLatticeSet ab N) :
    (schubertStageHomeomorph ab N hn comparison L).val = boundedPoint L.val := rfl

private def actionHomeomorph {G A : Type} [Group G] [TopologicalSpace G] [TopologicalSpace A]
    (action : MulAction G A) (h : Continuous (fun x : G × A ↦ action.smul x.1 x.2)) (g : G) :
    A ≃ₜ A := by
  letI := action
  exact
    { toFun := (g • ·)
      invFun := (g⁻¹ • ·)
      left_inv := inv_smul_smul g
      right_inv := smul_inv_smul g
      continuous_toFun := h.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := h.comp (continuous_const.prodMk continuous_id) }

private theorem gl2Orbit_smul_iff (g : GL (Fin 2) O) (cd : DominantPair) (L : GL2Lattice) :
    positiveGLMap 2 g • L ∈ gl2Orbit cd ↔ L ∈ gl2Orbit cd := by
  let h : PositiveGL 2 := ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩
  change h • L ∈ MulAction.orbit (PositiveGL 2) _ ↔ L ∈ MulAction.orbit (PositiveGL 2) _
  constructor
  · intro hl
    simpa using MulAction.mem_orbit_of_mem_orbit h⁻¹ hl
  · exact MulAction.mem_orbit_of_mem_orbit h

set_option maxHeartbeats 500000 in
/-- The actual analytic Schubert space has orbit-preserving homeomorphisms acting transitively
on every orbit. Each such homeomorphism comes from a single finite jet of a positive loop. -/
theorem exists_orbitPreserving_homeomorph
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions) (ab : DominantPair) (N : ℕ) (hn : OrbitBound ab N)
    (i : OrbitIndex ab) (x y : SchubertSpace ab N hn)
    (hx : x ∈ orbitPoints ab N hn i) (hy : y ∈ orbitPoints ab N hn i) :
    ∃ e : SchubertSpace ab N hn ≃ₜ SchubertSpace ab N hn, e x = y ∧
      ∀ j z, e z ∈ orbitPoints ab N hn j ↔ z ∈ orbitPoints ab N hn j := by
  obtain ⟨E, hE, _⟩ := stratification ab N hn
  let A := stageImage (-(N : ℤ)) (2 * N) (closureLattices ab)
  let H : SchubertSpace ab N hn ≃ₜ A := E.trans (schubertStageHomeomorph ab N hn comparison)
  have hH (z : SchubertSpace ab N hn) : (H z).val = boundedPoint (E z).val :=
    schubertStageHomeomorph_apply ab N hn comparison (E z)
  have ha : -(N : ℤ) ≤ ab.val.2 := by
    simpa [pairCoweight] using (hn (1 : Fin 2)).1
  have hb : ab.val.1 ≤ -(N : ℤ) + ((2 * N : ℕ) : ℤ) := by
    rw [boundedExponent]
    simpa [pairCoweight] using (hn (0 : Fin 2)).2
  let n := 2 * N + 1
  have hn' : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨_, ⟨ρ, _, hred, hcont, _⟩⟩ := jets ab (-(N : ℤ)) (2 * N) n hn'
    (Nat.le_succ _) ha hb
  have hx' := (mem_orbitPoints_iff E hE x i).mp hx
  have hy' := (mem_orbitPoints_iff E hE y i).mp hy
  have hyx : (E y).val.val ∈ MulAction.orbit (PositiveGL 2) (E x).val.val :=
    MulAction.mem_orbit_trans hy' (MulAction.mem_orbit_symm.mp hx')
  obtain ⟨⟨_, g, rfl⟩, hxy⟩ := MulAction.mem_orbit_iff.mp hyx
  let e := H.trans ((actionHomeomorph ρ hcont (reduceGL 2 n hn' g)).trans H.symm)
  have he (z : SchubertSpace ab N hn) :
      (E (e z)).val.val = positiveGLMap 2 g • (E z).val.val := by
    have hHz : H z = ⟨windowStagePoint (-(N : ℤ)) (2 * N) (E z).val.val,
        ⟨(E z).val.val, (E z).property, rfl⟩⟩ := Subtype.ext (hH z)
    have hact : H (e z) = ρ.smul (reduceGL 2 n hn' g) (H z) := by
      change H (H.symm _) = _
      rw [H.apply_symm_apply]
      rfl
    rw [hHz] at hact
    have hh := (hH (e z)).symm.trans (congrArg Subtype.val hact)
    rw [hred g _ (E z).property] at hh
    have hbounded : (scalarLattice 2 (N : ℤ)).val ≤ (positiveGLMap 2 g • (E z).val.val).val ∧
        (positiveGLMap 2 g • (E z).val.val).val ≤ (scalarLattice 2 (-(N : ℤ))).val := by
      obtain ⟨cd, hcd, hl⟩ := (E z).property
      obtain ⟨j, rfl⟩ := (below_iff_orbitLabel ab cd).mp hcd
      exact gl2Orbit_bounded _ (orbitLabel_bounded hn j) ((gl2Orbit_smul_iff g _ _).mpr hl)
    let L' : BoundedLattice 2 N := ⟨positiveGLMap 2 g • (E z).val.val, hbounded⟩
    have hh' : boundedPoint (E (e z)).val = boundedPoint L' := hh
    exact congrArg (fun B : BoundedLattice 2 N ↦ B.val) (boundedPoint_injective N hh')
  refine ⟨e, ?_, ?_⟩
  · apply E.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (he x).trans hxy
  · intro j z
    rw [mem_orbitPoints_iff E hE, mem_orbitPoints_iff E hE, he, gl2Orbit_smul_iff]

end OrbitHomeomorphisms

section Transport

open private embeddingIsoOfRange embeddingIsoOfRange_comp directImageComparisonIsIso
  pullbackCohomologyIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem range_comp_homeomorph {U Y : TopCat.{0}} (j : U ⟶ Y) (e : Y ≅ Y)
    (he : ∀ y : Y, e.hom y ∈ Set.range j ↔ y ∈ Set.range j) :
    Set.range (j ≫ e.hom) = Set.range j := by
  ext y
  obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso e).surjective y
  change (∃ u, e.hom (j u) = e.hom x) ↔ e.hom x ∈ Set.range j
  rw [he]
  exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, (TopCat.homeoOfIso e).injective hu⟩,
    fun ⟨u, hu⟩ ↦ ⟨u, congrArg (fun z : Y ↦ e.hom z) hu⟩⟩

private def restrictHomeomorph {U Y : TopCat.{0}} (j : U ⟶ Y) (hj : IsEmbedding j) (e : Y ≅ Y)
    (he : ∀ y : Y, e.hom y ∈ Set.range j ↔ y ∈ Set.range j) : U ≅ U :=
  embeddingIsoOfRange (j ≫ e.hom) j ((TopCat.homeoOfIso e).isEmbedding.comp hj) hj
    (range_comp_homeomorph j e he)

private theorem restrictHomeomorph_comp {U Y : TopCat.{0}} (j : U ⟶ Y) (hj : IsEmbedding j)
    (e : Y ≅ Y) (he : ∀ y : Y, e.hom y ∈ Set.range j ↔ y ∈ Set.range j) :
    (restrictHomeomorph j hj e he).hom ≫ j = j ≫ e.hom :=
  embeddingIsoOfRange_comp _ _ _ _ _

variable {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}

private theorem stagePoints_homeomorph (e : SchubertSpace ab N hN ≅ SchubertSpace ab N hN)
    (he : ∀ i x, e.hom x ∈ orbitPoints ab N hN i ↔ x ∈ orbitPoints ab N hN i)
    (k : ℕ) (x : SchubertSpace ab N hN) :
    e.hom x ∈ stagePoints ab N hN k ↔ x ∈ stagePoints ab N hN k := by
  change (∃ i : OrbitIndex ab, i.val ≤ k ∧ e.hom x ∈ orbitPoints ab N hN i) ↔
    (∃ i : OrbitIndex ab, i.val ≤ k ∧ x ∈ orbitPoints ab N hN i)
  simp only [he]

private theorem preserves_attachment_range {U Y : TopCat.{0}} (j : U ⟶ Y) (k : ℕ)
    (f : Y ⟶ SchubertSpace ab N hN) (hf : Function.Injective f)
    (hr : Set.range (j ≫ f) = stagePoints ab N hN k)
    (e : SchubertSpace ab N hN ≅ SchubertSpace ab N hN)
    (he : ∀ i x, e.hom x ∈ orbitPoints ab N hN i ↔ x ∈ orbitPoints ab N hN i)
    (v : Y ≅ Y) (hv : v.hom ≫ f = f ≫ e.hom) :
    ∀ y : Y, v.hom y ∈ Set.range j ↔ y ∈ Set.range j := by
  have mem_range_iff (z : Y) : z ∈ Set.range j ↔ f z ∈ stagePoints ab N hN k := by
    rw [← hr]
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, congrArg (fun w : Y ↦ f w) hu⟩,
      fun ⟨u, hu⟩ ↦ ⟨u, hf hu⟩⟩
  intro y
  rw [mem_range_iff, mem_range_iff]
  have hvy : f (v.hom y) = e.hom (f y) :=
    congrArg (fun g : Y ⟶ SchubertSpace ab N hN ↦ g y) hv
  rw [hvy, stagePoints_homeomorph e he]

private theorem filtrationIso_of_orbitPreserving {Y : TopCat.{0}} {d k : ℕ}
    {f : Y ⟶ SchubertSpace ab N hN} {P : Stratification Y} {D : DimensionFiltration Y d}
    (h : IsNormalizedOrbitIC ab N hN f k P D)
    (e : SchubertSpace ab N hN ≅ SchubertSpace ab N hN)
    (he : ∀ i x, e.hom x ∈ orbitPoints ab N hN i ↔ x ∈ orbitPoints ab N hN i) :
    ∀ v : Y ≅ Y, v.hom ≫ f = f ≫ e.hom → FiltrationIso v D D := by
  induction h with
  | top f P stage hP =>
    intro v _
    exact FiltrationIso.top v _
  | attach f P Q j hj hs prev stage strata hb hR hp hstrict ih =>
    intro v hv
    have hQ := normalizedOrbitIC_realizes prev
    have hpres := preserves_attachment_range j _ f stage.1.injective hQ.2.1 e he v hv
    let w := restrictHomeomorph j hj.isEmbedding v hpres
    have hw : w.hom ≫ j = j ≫ v.hom := restrictHomeomorph_comp _ _ _ _
    have hwf : w.hom ≫ (j ≫ f) = (j ≫ f) ≫ e.hom := by
      rw [← Category.assoc, hw, Category.assoc, hv, Category.assoc]
    exact FiltrationIso.attach (ih w hwf) hw.symm

private theorem boundary_mapped_to_orbit {U Y : TopCat.{0}} (j : U ⟶ Y)
    {k : ℕ} {f : Y ⟶ SchubertSpace ab N hN} {P : Stratification Y} {Q : Stratification U}
    (stage : RealizesOrbitStage f (k + 1) P) (prev : RealizesOrbitStage (j ≫ f) k Q)
    (hk : k + 1 ≤ difference ab / 2) (y : boundary j) :
    f y.val ∈ orbitPoints ab N hN ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by
  obtain ⟨i, hi, hpi⟩ : f y.val ∈ stagePoints ab N hN (k + 1) :=
    stage.2.1 ▸ Set.mem_range_self y.val
  have hni : i.val = k + 1 := by
    by_contra hne
    have hf : f y.val ∈ stagePoints ab N hN k := ⟨i, by omega, hpi⟩
    rw [← prev.2.1] at hf
    obtain ⟨u, hu⟩ := hf
    exact y.property ⟨u, stage.1.injective hu⟩
  rwa [show i = ⟨k + 1, Nat.lt_succ_of_le hk⟩ from Fin.ext hni] at hpi

/-- Each pair of points of a new orbit is related by a homeomorphism which preserves the
restriction of the actual untruncated direct image to that orbit. -/
theorem orbitBoundaryCohomology_transitive
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions) {k : ℕ} (hk : k + 1 ≤ difference ab / 2)
    {U Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    {D : DimensionFiltration U (orbitDimension ab k)}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D)
    (x y : boundary j) :
    let B := TopCat.of (boundary j)
    let G := (boundedBelowInverseImage (closedInclusion (boundary j))).obj
      ((derivedDirectImage j).obj (complex D))
    ∃ w : B ≅ B, w.hom x = y ∧ Nonempty ((boundedBelowInverseImage w.hom).obj G ≅ G) := by
  let next : OrbitIndex ab := ⟨k + 1, Nat.lt_succ_of_le hk⟩
  let hQ := normalizedOrbitIC_realizes prev
  have hx := boundary_mapped_to_orbit j stage hQ hk x
  have hy := boundary_mapped_to_orbit j stage hQ hk y
  obtain ⟨e', he'xy, he'⟩ := exists_orbitPreserving_homeomorph comparison stratification jets
    ab N hN next (f x.val) (f y.val) hx hy
  let e := TopCat.isoOfHomeo e'
  have he (i : OrbitIndex ab) (z : SchubertSpace ab N hN) :
      e.hom z ∈ orbitPoints ab N hN i ↔ z ∈ orbitPoints ab N hN i := he' i z
  have hpres (z : SchubertSpace ab N hN) : e.hom z ∈ Set.range f ↔ z ∈ Set.range f := by
    rw [stage.2.1, stagePoints_homeomorph e he]
  let v := restrictHomeomorph f stage.1.isEmbedding e hpres
  have hv : v.hom ≫ f = f ≫ e.hom := restrictHomeomorph_comp _ _ _ _
  have hpresU := preserves_attachment_range j k f stage.1.injective hQ.2.1 e he v hv
  let u := restrictHomeomorph j hj.isEmbedding v hpresU
  have hu : u.hom ≫ j = j ≫ v.hom := restrictHomeomorph_comp _ _ _ _
  have huf : u.hom ≫ (j ≫ f) = (j ≫ f) ≫ e.hom := by
    rw [← Category.assoc, hu, Category.assoc, hv, Category.assoc]
  let i := closedInclusion (boundary j)
  have hpresB (z : Y) : v.hom z ∈ Set.range i ↔ z ∈ Set.range i := by
    change v.hom z ∈ Set.range (Subtype.val : boundary j → Y) ↔
      z ∈ Set.range (Subtype.val : boundary j → Y)
    simp only [Subtype.range_coe, boundary, Set.mem_compl_iff, hpresU]
  let w := restrictHomeomorph i IsEmbedding.subtypeVal v hpresB
  have hw : w.hom ≫ i = i ≫ v.hom := restrictHomeomorph_comp _ _ _ _
  refine ⟨w, ?_, ?_⟩
  · apply Subtype.ext
    apply stage.1.injective
    have hwx : i (w.hom x) = v.hom (i x) := congrArg (fun g ↦ g x) hw
    have hvx : f (v.hom (i x)) = e.hom (f (i x)) := congrArg (fun g ↦ g (i x)) hv
    exact (congrArg (fun z : Y ↦ f z) hwx).trans (hvx.trans he'xy)
  · let F := complex D
    let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData j
    let c := directImageComparison hu.symm a a F
    have : IsIso c := directImageComparisonIsIso v u hu.symm a a F
    obtain ⟨eF⟩ := MiddleExtension.complexTransport u D D
      (filtrationIso_of_orbitPreserving prev e he u huf)
    let eR := asIso c ≪≫ (derivedDirectImage j).mapIso eF
    exact ⟨((pullbackSquare hw.symm).app ((derivedDirectImage j).obj F)).symm ≪≫
      (boundedBelowInverseImage i).mapIso eR⟩

end Transport

section FiniteRefinement

open CategoryTheory.Limits

open private constantPullbackIso locallyConstantFiniteRank_of_iso pullback_locallyConstantFiniteRank
  liftAlongEmbedding liftAlongEmbedding_comp pullbackCohomologyIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem exists_nonempty_interior_of_finite_cover {X I : Type} [TopologicalSpace X]
    [Nonempty X] [Finite I] (S : I → Set X) (hclosed : ∀ i, IsLocallyClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i) : ∃ i, (interior (S i)).Nonempty := by
  by_contra! h
  have hclosure (i : I) : interior (closure (S i)) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨U, hU, hSU⟩ := (isLocallyClosed_tfae (S i)).out 1 5 |>.mp (hclosed i)
    obtain ⟨y, hy, hyo⟩ := (closure_inter_open_nonempty_iff isOpen_interior).mp
      ⟨x, interior_subset hx, hx⟩
    have hyU : y ∈ U := (hSU ▸ hy).1
    have hsubset : U ∩ interior (closure (S i)) ⊆ S i := by
      intro z hz
      exact hSU.symm ▸ ⟨hz.1, interior_subset hz.2⟩
    have hy' := interior_maximal hsubset (hU.inter isOpen_interior) ⟨hyU, hyo⟩
    simp only [h i, Set.notMem_empty] at hy'
  let C : I → Set X := fun i ↦ (closure (S i))ᶜ
  have hdense : Dense (⋂₀ Set.range C) := (Set.finite_range C).dense_sInter
    (by rintro _ ⟨i, rfl⟩; exact isClosed_closure.isOpen_compl)
    (by rintro _ ⟨i, rfl⟩; exact interior_eq_empty_iff_dense_compl.mp (hclosure i))
  obtain ⟨x, hx⟩ := hdense.nonempty
  obtain ⟨i, hi⟩ := hcover x
  exact (Set.mem_sInter.mp hx (C i) (Set.mem_range_self i)) (subset_closure hi)

private theorem local_trivialization_of_open_pullback {X Y : TopCat.{0}}
    (f : Y ⟶ X) (hf : IsOpenEmbedding f) (F : Sheaves X) (y : Y)
    (h : LocallyConstantFiniteRank ((inverseImage f).obj F)) :
    ∃ U : Opens X, f y ∈ U ∧ ∃ V : Coeff.{0}, Module.Finite ℚ V ∧
      Nonempty ((inverseImage (openInclusion U)).obj F ≅ constant (TopCat.of U) V) := by
  obtain ⟨O, hy, V, hV, ⟨c⟩⟩ := h y
  let U : Opens X := ⟨f '' (O : Set Y), hf.isOpenMap _ O.isOpen⟩
  let j := openInclusion O ≫ f
  have hj : IsEmbedding j := hf.isEmbedding.comp O.isOpenEmbedding.isEmbedding
  have hsub : Set.range (openInclusion U) ⊆ Set.range j := by
    rintro x ⟨z, rfl⟩
    obtain ⟨w, hw, heq⟩ := z.property
    exact ⟨⟨w, hw⟩, heq⟩
  let l := liftAlongEmbedding (openInclusion U) j hj hsub
  have hl : l ≫ j = openInclusion U := liftAlongEmbedding_comp _ _ _ _
  refine ⟨U, ⟨y, hy, rfl⟩, V, hV, ⟨?_⟩⟩
  exact eqToIso (congrArg (fun m => (inverseImage m).obj F) hl.symm) ≪≫
    (inverseImageComposition l j).app F ≪≫
    (inverseImage l).mapIso ((inverseImageComposition (openInclusion O) f).app F ≪≫ c) ≪≫
    constantPullbackIso l V

private theorem locallyConstantFiniteRank_of_range_subset
    {A B X : TopCat.{0}} (f : A ⟶ X) (g : B ⟶ X)
    (hg : IsEmbedding g) (h : Set.range f ⊆ Set.range g) (F : Sheaves X)
    (hF : LocallyConstantFiniteRank ((inverseImage g).obj F)) :
    LocallyConstantFiniteRank ((inverseImage f).obj F) := by
  let l := liftAlongEmbedding f g hg h
  have hl : l ≫ g = f := liftAlongEmbedding_comp _ _ _ _
  rw [← hl]
  exact locallyConstantFiniteRank_of_iso ((inverseImageComposition l g).app F).symm
    (pullback_locallyConstantFiniteRank l hF)

private theorem exists_open_with_locallyConstantFiniteRank
    {A : TopCat.{0}} [Nonempty A] (F : Sheaves A) {I : Type} [Finite I]
    (S : I → Set A) (hc : ∀ i, IsLocallyClosed (S i)) (hcover : ∀ x, ∃ i, x ∈ S i)
    (hF : ∀ i, LocallyConstantFiniteRank ((inverseImage (closedInclusion (S i))).obj F)) :
    ∃ V : Opens A, (V : Set A).Nonempty ∧
      LocallyConstantFiniteRank ((inverseImage (openInclusion V)).obj F) := by
  obtain ⟨i, hi⟩ := exists_nonempty_interior_of_finite_cover S hc hcover
  let V : Opens A := ⟨interior (S i), isOpen_interior⟩
  refine ⟨V, hi, ?_⟩
  have range_le : Set.range (openInclusion V) ⊆ Set.range (closedInclusion (S i)) := by
    rintro x ⟨v, rfl⟩
    exact ⟨⟨v.val, interior_subset v.property⟩, rfl⟩
  exact locallyConstantFiniteRank_of_range_subset _ _ IsEmbedding.subtypeVal range_le F (hF i)

private theorem locallyConstantFiniteRank_of_transitive_trivialization
    {X : TopCat.{0}} (F : Sheaves X) {y : X} (V : Opens X) (hy : y ∈ V)
    (M : Coeff.{0}) (hM : Module.Finite ℚ M)
    (c : (inverseImage (openInclusion V)).obj F ≅ constant (TopCat.of V) M)
    (htrans : ∀ x y : X, ∃ v : X ≅ X, v.hom x = y ∧
      Nonempty ((inverseImage v.hom).obj F ≅ F)) :
    LocallyConstantFiniteRank F := by
  intro x
  obtain ⟨v, hv, ⟨e⟩⟩ := htrans x y
  let W := (Opens.map v.hom).obj V
  let l : TopCat.of W ⟶ TopCat.of V := TopCat.ofHom
    ⟨fun z ↦ ⟨v.hom z.val, z.property⟩,
      (v.hom.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hl : openInclusion W ≫ v.hom = l ≫ openInclusion V := rfl
  have hxW : x ∈ W := by
    change v.hom x ∈ V
    exact hv.symm ▸ hy
  refine ⟨W, hxW, M, hM, ⟨?_⟩⟩
  exact (inverseImage (openInclusion W)).mapIso e.symm ≪≫
    ((inverseImageComposition (openInclusion W) v.hom).app F).symm ≪≫
    eqToIso (congrArg (fun r => (inverseImage r).obj F) hl) ≪≫
    (inverseImageComposition l (openInclusion V)).app F ≪≫
    (inverseImage l).mapIso c ≪≫ constantPullbackIso l M

private theorem locallyConstantFiniteRank_of_transitive_finite_cover
    {X : TopCat.{0}} (F : Sheaves X) {I : Type} [Finite I]
    (S : I → Set X) (hclosed : ∀ i, IsLocallyClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i)
    (hlocal : ∀ i, LocallyConstantFiniteRank ((inverseImage (closedInclusion (S i))).obj F))
    (htrans : ∀ x y : X, ∃ v : X ≅ X, v.hom x = y ∧
      Nonempty ((inverseImage v.hom).obj F ≅ F)) :
    LocallyConstantFiniteRank F := by
  intro x
  let : Nonempty X := ⟨x⟩
  obtain ⟨O, ⟨y, hy⟩, hO⟩ := exists_open_with_locallyConstantFiniteRank F S hclosed hcover hlocal
  obtain ⟨U, hyU, V, hV, ⟨c⟩⟩ :=
    local_trivialization_of_open_pullback (openInclusion O) O.isOpenEmbedding F ⟨y, hy⟩ hO
  exact locallyConstantFiniteRank_of_transitive_trivialization F U hyU V hV c htrans x

private def inverseImage_cohomology_iso {B : TopCat.{0}} (v : B ≅ B)
    (G : BoundedBelow B) (e : (boundedBelowInverseImage v.hom).obj G ≅ G) (q : ℤ) :
    (inverseImage v.hom).obj ((cohomology B q).obj G.obj) ≅ (cohomology B q).obj G.obj :=
  (pullbackCohomologyIso v.hom G q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor (Sheaves B) q).mapIso e

/-- On a new orbit, boundedness of the boundary restriction can be checked at one stalk. -/
theorem orbitBoundaryCohomology_bounded_of_one_stalk
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} {k : ℕ}
    (hk : k + 1 ≤ difference ab / 2)
    {U Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    {D : DimensionFiltration U (orbitDimension ab k)}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D) (x : boundary j) :
    let B := TopCat.of (boundary j)
    let G := (boundedBelowInverseImage (closedInclusion (boundary j))).obj
      ((derivedDirectImage j).obj (complex D))
    (Set.Finite {q : ℤ | ¬ IsZero ((stalk x).obj ((cohomology B q).obj G.obj))}) →
    Set.Finite {q : ℤ | ¬ IsZero ((cohomology B q).obj G.obj)} := by
  dsimp only
  let B := TopCat.of (boundary j)
  let G : BoundedBelow B := (boundedBelowInverseImage (closedInclusion (boundary j))).obj
    ((derivedDirectImage j).obj (complex D))
  intro hfinite
  apply hfinite.subset
  intro q hq hx
  apply hq
  change IsZero ((cohomology B q).obj G.obj)
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro y
  obtain ⟨v, hv, ⟨e⟩⟩ :=
    orbitBoundaryCohomology_transitive comparison stratification jets hk hj stage prev y x
  let F := (cohomology B q).obj G.obj
  let h := eqToIso (congrArg (fun z : B ↦ (stalk z).obj F) hv.symm)
  let he := h ≪≫ inverseImageStalkIso v.hom F y ≪≫
    (stalk y).mapIso (inverseImage_cohomology_iso v G e q)
  exact hx.of_iso he.symm

/-- Bounded cohomology and a finite locally closed refinement of the boundary direct image
suffice for constructibility along the entire new orbit. -/
theorem orbitBoundaryConstructible_of_finite_refinement
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} {k : ℕ}
    (hk : k + 1 ≤ difference ab / 2)
    {U Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    {D : DimensionFiltration U (orbitDimension ab k)}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D) :
    let B := TopCat.of (boundary j)
    let R := (derivedDirectImage j).obj (complex D)
    let G := (boundedBelowInverseImage (closedInclusion (boundary j))).obj R
    (Set.Finite {q : ℤ | ¬ IsZero ((cohomology B q).obj G.obj)}) →
    (∀ q : ℤ, ∃ (I : Type) (S : I → Set B), Finite I ∧
      (∀ i, IsLocallyClosed (S i)) ∧ (∀ x, ∃ i, x ∈ S i) ∧
      ∀ i, LocallyConstantFiniteRank
        ((inverseImage (closedInclusion (S i))).obj ((cohomology B q).obj G.obj))) →
    IsConstructibleOnBoundary j R := by
  dsimp only
  let B := TopCat.of (boundary j)
  let G : BoundedBelow B := (boundedBelowInverseImage (closedInclusion (boundary j))).obj
    ((derivedDirectImage j).obj (complex D))
  intro hfinite hrefine
  change _ ∧ ∀ q : ℤ, LocallyConstantFiniteRank ((cohomology B q).obj G.obj)
  refine ⟨hfinite, fun q ↦ ?_⟩
  obtain ⟨I, S, hI, hclosed, hcover, hlocal⟩ := hrefine q
  let := hI
  apply locallyConstantFiniteRank_of_transitive_finite_cover _ S hclosed hcover hlocal
  intro x y
  obtain ⟨v, hxy, ⟨e⟩⟩ :=
    orbitBoundaryCohomology_transitive comparison stratification jets hk hj stage prev x y
  exact ⟨v, hxy, ⟨inverseImage_cohomology_iso v G e q⟩⟩

end FiniteRefinement

section ChartEquations

open AlgebraicGeometry
open LinearAlgebraicGroups (Points)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv)

private theorem chartPoint_mem_closed_iff_polynomials
    {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d)
    (Z : Set (grassmannianCharts b hd).scheme.left) (hZ : IsClosed Z) :
    ∃ F : Finset (chartAlgebra (k := ℂ) I), ∀ A : Matrix (Outside I) (Inside I) ℂ,
      pointLocation (grassmannianChartPoint b hd I A) ∈ Z ↔
        ∀ f ∈ F, MvPolynomial.aeval (chartVariables I A) f = 0 := by
  classical
  let j := chartInclusion b hd I
  have hz : IsClosed (j ⁻¹' Z) := hZ.preimage j.continuous
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hz
  obtain ⟨F, hF⟩ := J.fg_of_isNoetherianRing
  refine ⟨F, fun A ↦ ?_⟩
  rw [grassmannianChartPoint, pointLocation_comp, ← Set.mem_preimage]
  change pointLocation ((chartMatrixEquiv I complexAlgebra).symm A) ∈ j ⁻¹' Z ↔ _
  rw [hJ, ← hF, PrimeSpectrum.zeroLocus_span, chart_location]
  change (∀ f ∈ F, f ∈ MvPolynomial.vanishingIdeal ℂ {chartVariables I A}) ↔ _
  simp_rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]

private theorem mem_closureLattices_orbitLabel_iff {ab : DominantPair} (i : OrbitIndex ab)
    (L : GL2Lattice) :
    L ∈ closureLattices (orbitLabel ab i) ↔
      ∃ j : OrbitIndex ab, i.val ≤ j.val ∧ L ∈ gl2Orbit (orbitLabel ab j) := by
  change (∃ cd : DominantPair, Below cd (orbitLabel ab i) ∧ L ∈ gl2Orbit cd) ↔ _
  constructor
  · rintro ⟨cd, ⟨k, hk, ha, hb⟩, hL⟩
    change 2 * (k : ℤ) ≤ ab.val.1 - (i.val : ℤ) - (ab.val.2 + (i.val : ℤ)) at hk
    have hij : i.val + k < difference ab / 2 + 1 := by
      unfold difference
      omega
    let j : OrbitIndex ab := ⟨i.val + k, hij⟩
    have he : cd = orbitLabel ab j := by
      apply Subtype.ext
      apply Prod.ext
      · change cd.val.1 = ab.val.1 - ((i.val + k : ℕ) : ℤ)
        change cd.val.1 = ab.val.1 - (i.val : ℤ) - (k : ℤ) at ha
        omega
      · change cd.val.2 = ab.val.2 + ((i.val + k : ℕ) : ℤ)
        change cd.val.2 = ab.val.2 + (i.val : ℤ) + (k : ℤ) at hb
        omega
    exact ⟨j, Nat.le_add_right _ _, he ▸ hL⟩
  · rintro ⟨j, hij, hL⟩
    refine ⟨orbitLabel ab j, ⟨j.val - i.val, ?_, ?_, ?_⟩, hL⟩
    · have h := orbitIndex_le_difference ab j
      change 2 * ((j.val - i.val : ℕ) : ℤ) ≤
        ab.val.1 - (i.val : ℤ) - (ab.val.2 + (i.val : ℤ))
      omega
    · change ab.val.1 - (j.val : ℤ) =
        ab.val.1 - (i.val : ℤ) - ((j.val - i.val : ℕ) : ℤ)
      omega
    · change ab.val.2 + (j.val : ℤ) =
        ab.val.2 + (i.val : ℤ) + ((j.val - i.val : ℕ) : ℤ)
      omega

private theorem closureLattices_orbitLabel_subset {ab : DominantPair} (i : OrbitIndex ab) :
    closureLattices (orbitLabel ab i) ⊆ closureLattices ab := by
  intro L hL
  obtain ⟨j, _, hj⟩ := (mem_closureLattices_orbitLabel_iff i L).mp hL
  exact ⟨orbitLabel ab j, (below_iff_orbitLabel ab _).mpr ⟨j, rfl⟩, hj⟩

private theorem mem_tailPoints_iff_window_closure {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p : SchubertSpace ab N hN) (i : OrbitIndex ab) :
    p ∈ tailPoints (hN := hN) i ↔ (E p).val.val ∈ closureLattices (orbitLabel ab i) := by
  rw [mem_closureLattices_orbitLabel_iff]
  exact exists_congr fun j ↦ and_congr_right fun _ ↦ mem_orbitPoints_iff E hE p j

/-- In each ordinary graph chart, the closed union of orbits at and below a fixed label
is the vanishing set of finitely many complex polynomials in the chart coordinates. -/
theorem schubertTail_chartEquations
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (i : OrbitIndex ab)
    (I : Pivot (Fin 2 × Fin (2 * N)) (occupiedDimension ab N hN).val) :
    ∃ F : Finset (chartAlgebra (k := ℂ) I), ∀ A : Matrix (Outside I) (Inside I) ℂ,
      (∃ (p : SchubertSpace ab N hN), p ∈ tailPoints (hN := hN) i ∧
        p ≫ schubertToGrassmannian ab N hN _ =
          grassmannianChartPoint (windowBasis 2 (-(N : ℤ)) (2 * N))
            (windowDimension_le (occupiedDimension ab N hN)) I A) ↔
         ∀ f ∈ F, MvPolynomial.aeval (chartVariables I A) f = 0 := by
  let d := occupiedDimension ab N hN
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  let cd := orbitLabel ab i
  let hcd := orbitLabel_bounded hN i
  let Z : Set (BoundedGrassmannian N d).left :=
    closure (pointLocation '' schubertOrbitPoints cd N hcd d)
  obtain ⟨E, hE, _⟩ := stratification ab N hN
  obtain ⟨_, _, _, _, _, _, hC⟩ := comparison cd N hcd
  obtain ⟨F, hF⟩ := chartPoint_mem_closed_iff_polynomials b (windowDimension_le d) I Z isClosed_closure
  refine ⟨F, fun A ↦ (Iff.trans ?_ (hF A))⟩
  let q := grassmannianChartPoint b (windowDimension_le d) I A
  change (∃ (p : SchubertSpace ab N hN), p ∈ tailPoints (hN := hN) i ∧
    p ≫ schubertToGrassmannian ab N hN d = q) ↔ pointLocation q ∈ Z
  change _ ↔ pointLocation q ∈ closure (pointLocation '' schubertOrbitPoints cd N hcd d)
  rw [hC]
  constructor
  · rintro ⟨p, hp, hpq⟩
    refine ⟨(E p).val, (mem_tailPoints_iff_window_closure E hE p i).mp hp, ?_⟩
    rw [← hpq]
    exact hE p
  · rintro ⟨L, hL, hq⟩
    let B : schubertLatticeSet ab N := ⟨L, closureLattices_orbitLabel_subset i hL⟩
    let p := E.symm B
    have hEB : E p = B := E.apply_symm_apply B
    have hL' : (E p).val.val ∈ closureLattices cd := hEB.symm ▸ hL
    refine ⟨p, (mem_tailPoints_iff_window_closure E hE p i).mpr hL', ?_⟩
    apply grassmannianSubspace_injective b (windowDimension_le d)
    change schubertPointSubspace p = _
    exact (hE p).trans ((congrArg (fun x : schubertLatticeSet ab N ↦
      boundedSubspace x.val) hEB).trans hq.symm)

end ChartEquations

section ChartTopology

open AlgebraicGeometry
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts
  (chartMatrixEquiv graphPlane graphPlane_toSubmodule isPivot_graphPlane_iff)
open private pivotMinor_apply bijective_pivotChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.GrassmannianCharts
open scoped Matrix

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
  {d : ℕ} (I J : Pivot ι d)

private def orderedGraph (A : Matrix (Outside I) (Inside I) ℂ) : Matrix ι (Fin d) ℂ :=
  (graphMatrix I A).submatrix id (pivotOrder I).symm

omit [Fintype ι] in
private theorem orderedGraph_range (A : Matrix (Outside I) (Inside I) ℂ) :
    (Matrix.toLin' (orderedGraph I A)).range = (Matrix.toLin' (graphMatrix I A)).range := by
  ext x
  simp only [LinearMap.mem_range, Matrix.toLin'_apply, orderedGraph,
    Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id]
  exact ⟨fun ⟨v, hv⟩ ↦ ⟨v ∘ pivotOrder I, hv⟩,
    fun ⟨v, hv⟩ ↦ ⟨v ∘ (pivotOrder I).symm, by simpa [Function.comp_def] using hv⟩⟩

omit [Fintype ι] in
private theorem orderedGraph_pivotRows (A : Matrix (Outside I) (Inside I) ℂ) :
    (orderedGraph I A).submatrix (Subtype.val ∘ (pivotOrder J).symm) id =
      pivotMinor I J complexAlgebra A := by
  ext r c
  rw [pivotMinor_apply]
  let i := (pivotOrder J).symm r
  let j := (pivotOrder I).symm c
  change graphMatrix I A i.val j =
    if h : i.val ∈ I.val then (Pi.single j (1 : ℂ) : Inside I → ℂ) ⟨i.val, h⟩ else A ⟨i.val, h⟩ j
  split_ifs with h
  · rw [graphMatrix, Matrix.of_apply, dite_eq_left h, Pi.single_apply]
    have heq : (⟨i.val, h⟩ : Inside I) = j ↔ i.val = j.val :=
      Subtype.ext_iff
    simp only [heq]
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_right h]

private def transitionMatrix (A : Matrix (Outside I) (Inside I) ℂ) :
    Matrix (Outside J) (Inside J) ℂ :=
  (orderedGraph I A * (pivotMinor I J complexAlgebra A)⁻¹).submatrix Subtype.val (pivotOrder J)

omit [Fintype ι] in
private theorem transitionMatrix_graph (A : Matrix (Outside I) (Inside I) ℂ)
    (hA : IsUnit (pivotMinor I J complexAlgebra A).det) :
    orderedGraph J (transitionMatrix I J A) =
      orderedGraph I A * (pivotMinor I J complexAlgebra A)⁻¹ := by
  let M := orderedGraph I A * (pivotMinor I J complexAlgebra A)⁻¹
  have hrows : M.submatrix (Subtype.val ∘ (pivotOrder J).symm) id = 1 := by
    dsimp only [M]
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      orderedGraph_pivotRows, Matrix.submatrix_id_id, Matrix.mul_nonsing_inv _ hA]
  ext r c
  let j := (pivotOrder J).symm c
  change graphMatrix J (transitionMatrix I J A) r j = M r c
  by_cases hr : r ∈ J.val
  · let u : Inside J := ⟨r, hr⟩
    have hc' := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ ↦ A (pivotOrder J u) c) hrows
    simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply, id_eq] at hc'
    rw [graphMatrix, Matrix.of_apply, dite_eq_left hr]
    change (if r = j.val then 1 else 0) = M r c
    calc
      _ = (1 : Matrix (Fin d) (Fin d) ℂ) (pivotOrder J u) c := by
        have hj : pivotOrder J j = c := Equiv.apply_symm_apply _ _
        have heq : pivotOrder J u = c ↔ r = j.val := by
          rw [← hj]
          exact (pivotOrder J).injective.eq_iff.trans Subtype.ext_iff
        simp only [Matrix.one_apply, heq]
      _ = M r c := hc'.symm
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hr, transitionMatrix, Matrix.submatrix_apply]
    rw [show pivotOrder J j = c from Equiv.apply_symm_apply _ _]

private theorem transitionMatrix_chartPoint (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) (A : Matrix (Outside I) (Inside I) ℂ)
    (hA : IsUnit (pivotMinor I J complexAlgebra A).det) :
    grassmannianChartPoint b hd J (transitionMatrix I J A) = grassmannianChartPoint b hd I A := by
  apply grassmannianSubspace_injective b hd
  apply Submodule.map_injective_of_injective b.equivFun.injective
  rw [grassmannianChartSubspace, grassmannianChartSubspace,
    ← orderedGraph_range J, ← orderedGraph_range I, transitionMatrix_graph I J A hA]
  rw [Matrix.toLin'_mul, LinearMap.range_comp_of_range_eq_top]
  apply LinearMap.range_eq_top.mpr
  rw [Matrix.toLin'_apply']
  exact Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hA))

private theorem grassmannianChartPoint_injective (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) : Function.Injective (grassmannianChartPoint b hd I) := by
  let C := grassmannianCharts b hd
  let _ : IsOpenImmersion (C.chart I).left := C.openChart I
  intro A B h
  apply (chartMatrixEquiv I complexAlgebra).symm.injective
  apply Over.OverMorphism.ext
  apply (cancel_mono (C.chart I).left).mp
  exact congrArg (fun p : GrassmannianPoints b hd ↦ p.left) h

private theorem unit_pivotMinor_of_chartPoint_eq (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) {A : Matrix (Outside I) (Inside I) ℂ}
    {B : Matrix (Outside J) (Inside J) ℂ}
    (h : grassmannianChartPoint b hd I A = grassmannianChartPoint b hd J B) :
    IsUnit (pivotMinor I J complexAlgebra A).det := by
  let C := grassmannianCharts b hd
  let a := (chartMatrixEquiv I complexAlgebra).symm A
  let b' := (chartMatrixEquiv J complexAlgebra).symm B
  have ha : matrixOfPoint I complexAlgebra a = A :=
    (chartMatrixEquiv I complexAlgebra).apply_symm_apply A
  have hg : grassmannianPlane b hd (grassmannianChartPoint b hd I A) =
      graphPlane b I complexAlgebra A := by
    apply Module.Grassmannian.ext
    rw [graphPlane_toSubmodule]
    have hC := C.coordinates_eq I complexAlgebra a
    rw [ha] at hC
    exact hC
  have hj := (C.factor_iff J complexAlgebra (grassmannianChartPoint b hd I A)).mp ⟨b', h.symm⟩
  change IsPivot b J complexAlgebra (grassmannianPlane b hd (grassmannianChartPoint b hd I A)) at hj
  rw [hg, isPivot_graphPlane_iff, bijective_pivotChange_iff] at hj
  exact hj

omit [Fintype ι] in
private theorem continuous_orderedGraph :
    Continuous (orderedGraph (d := d) I) := by
  apply continuous_matrix
  intro r c
  change Continuous fun A : Matrix (Outside I) (Inside I) ℂ ↦
    graphMatrix I A r ((pivotOrder I).symm c)
  by_cases hr : r ∈ I.val
  · simpa only [graphMatrix, Matrix.of_apply, dite_eq_left hr] using continuous_const
      (y := if r = ((pivotOrder I).symm c).val then (1 : ℂ) else 0)
  · have heq (A : Matrix (Outside I) (Inside I) ℂ) :
        graphMatrix I A r ((pivotOrder I).symm c) = A ⟨r, hr⟩ ((pivotOrder I).symm c) := by
      rw [graphMatrix, Matrix.of_apply, dite_eq_right hr]
    simp_rw [heq]
    exact continuous_id.matrix_elem (⟨r, hr⟩ : Outside I) ((pivotOrder I).symm c)

omit [Fintype ι] in
private theorem continuous_pivotMinor :
    Continuous (pivotMinor (d := d) I J complexAlgebra) := by
  rw [show pivotMinor I J complexAlgebra =
    fun A ↦ (orderedGraph I A).submatrix (Subtype.val ∘ (pivotOrder J).symm) id
    from funext fun A ↦ (orderedGraph_pivotRows I J A).symm]
  exact (continuous_orderedGraph I).matrix_submatrix _ _

omit [Fintype ι] in
private theorem continuousOn_transitionMatrix :
    ContinuousOn (transitionMatrix I J) {A | IsUnit (pivotMinor I J complexAlgebra A).det} := by
  intro A hA
  have hu : IsUnit (pivotMinor I J complexAlgebra A).det := hA
  obtain ⟨u, hu⟩ := hu
  have hu' : ContinuousAt Ring.inverse (pivotMinor I J complexAlgebra A).det :=
    hu ▸ NormedRing.inverse_continuousAt u
  have hinv : ContinuousAt (fun A ↦ (pivotMinor I J complexAlgebra A)⁻¹) A :=
    (continuousAt_matrix_inv _ hu').comp (continuous_pivotMinor I J).continuousAt
  have hmul : Continuous (fun q : Matrix ι (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ ↦ q.1 * q.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hsub : Continuous (fun M : Matrix ι (Fin d) ℂ ↦ M.submatrix (Subtype.val : Outside J → ι) (pivotOrder J)) :=
    continuous_id.matrix_submatrix _ _
  exact (hsub.continuousAt.comp (hmul.continuousAt.comp
    ((continuous_orderedGraph I).continuousAt.prodMk hinv))).continuousWithinAt

/-- Each standard graph chart is an open embedding for the specified analytic topology. -/
theorem grassmannianChartPoint_isOpenEmbedding (b : Module.Basis ι ℂ V)
    (hd : d ≤ Module.finrank ℂ V) : IsOpenEmbedding (grassmannianChartPoint b hd I) := by
  have hcont : Continuous (grassmannianChartPoint b hd I) :=
    continuous_iff_coinduced_le.mpr (le_iSup (fun J : Pivot ι d ↦
      TopologicalSpace.coinduced (grassmannianChartPoint b hd J) inferInstance) I)
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hcont (grassmannianChartPoint_injective I b hd)
  intro U hU
  change IsOpen[⨆ J : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd J) inferInstance] (grassmannianChartPoint b hd I '' U)
  rw [isOpen_iSup_iff]
  intro J
  rw [isOpen_coinduced]
  let O := {A | IsUnit (pivotMinor J I complexAlgebra A).det}
  have hO : IsOpen O := by
    change IsOpen {A | IsUnit (pivotMinor J I complexAlgebra A).det}
    simp only [isUnit_iff_ne_zero]
    exact isClosed_eq (continuous_pivotMinor J I).matrix_det continuous_const |>.isOpen_compl
  have heq : (grassmannianChartPoint b hd J) ⁻¹' (grassmannianChartPoint b hd I '' U) =
      O ∩ (transitionMatrix J I) ⁻¹' U := by
    ext A
    constructor
    · rintro ⟨B, hB, hAB⟩
      have hA := unit_pivotMinor_of_chartPoint_eq J I b hd hAB.symm
      refine ⟨hA, ?_⟩
      have hB' := grassmannianChartPoint_injective I b hd
        ((transitionMatrix_chartPoint J I b hd A hA).trans hAB.symm)
      change transitionMatrix J I A ∈ U
      rwa [hB']
    · rintro ⟨hA, hU'⟩
      exact ⟨transitionMatrix J I A, hU', transitionMatrix_chartPoint J I b hd A hA⟩
  rw [heq]
  exact (continuousOn_transitionMatrix J I).isOpen_inter_preimage hO hU

end ChartTopology

section SchubertCharts

open LinearAlgebraicGroups.Specs.GrassmannianCharts

private abbrev topOrbitIndex (ab : DominantPair) : OrbitIndex ab := ⟨0, Nat.zero_lt_succ _⟩

private theorem mem_tailPoints_top {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (smith : SmithClassification)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (p : SchubertSpace ab N hN) : p ∈ tailPoints (hN := hN) (topOrbitIndex ab) := by
  obtain ⟨i, hi, _⟩ := orbitPoints_partition smith E hE p
  exact ⟨i, Nat.zero_le _, hi⟩

private abbrev schubertGrassmannianPoint (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (p : SchubertSpace ab N hN) := p ≫ schubertToGrassmannian ab N hN (occupiedDimension ab N hN)

private theorem schubertGrassmannianPoint_injective {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val) :
    Function.Injective (schubertGrassmannianPoint ab N hN) := by
  intro p q hpq
  apply E.injective
  apply Subtype.ext
  apply boundedSubspace_injective N
  rw [← hE p, ← hE q]
  unfold schubertPointSubspace
  exact congrArg (grassmannianSubspace _ _) hpq

private def chartZeroSet {ι : Type} [DecidableEq ι] {d : ℕ} {I : Pivot ι d}
    (F : Finset (chartAlgebra (k := ℂ) I)) : Set (Matrix (Outside I) (Inside I) ℂ) :=
  {A | ∀ f ∈ F, MvPolynomial.aeval (chartVariables I A) f = 0}

/-- The prescribed analytic Schubert space is covered by chart patches homeomorphic
to polynomial zero sets, with the smaller closed Schubert unions cut out by further
polynomials in the same coordinates. -/
theorem schubertChart_model
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (I : Pivot (Fin 2 × Fin (2 * N)) (occupiedDimension ab N hN).val) :
    ∃ (F : OrbitIndex ab → Finset (chartAlgebra (k := ℂ) I))
      (e : chartZeroSet (F (topOrbitIndex ab)) → SchubertSpace ab N hN),
      IsOpenEmbedding e ∧
      (∀ A, schubertGrassmannianPoint ab N hN (e A) =
        grassmannianChartPoint (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le (occupiedDimension ab N hN)) I A.val) ∧
      (∀ i A, e A ∈ tailPoints (hN := hN) i ↔ A.val ∈ chartZeroSet (F i)) ∧
      Set.range e = (schubertGrassmannianPoint ab N hN) ⁻¹' Set.range
        (grassmannianChartPoint (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le (occupiedDimension ab N hN)) I) := by
  classical
  let d := occupiedDimension ab N hN
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  let g := schubertGrassmannianPoint ab N hN
  let h := grassmannianChartPoint b (windowDimension_le d) I
  obtain ⟨E, hE, _⟩ := stratification ab N hN
  have hkinj := schubertGrassmannianPoint_injective E hE
  have hg : IsInducing g := IsInducing.induced _
  have hh := grassmannianChartPoint_isOpenEmbedding I b (windowDimension_le d)
  choose F hF using fun i ↦ schubertTail_chartEquations comparison stratification ab N hN i I
  let Z := chartZeroSet (F (topOrbitIndex ab))
  have hl (A : Z) : ∃ p : SchubertSpace ab N hN, g p = h A.val := by
    obtain ⟨p, _, hp⟩ := (hF (topOrbitIndex ab) A.val).mpr A.property
    exact ⟨p, hp⟩
  choose e he using hl
  have hecomp : g ∘ e = h ∘ Subtype.val := funext he
  have hr : Set.range e = g ⁻¹' Set.range h := by
    ext p
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A.val, (he A).symm⟩
    · rintro ⟨A, hA⟩
      have hp := mem_tailPoints_top smith E hE p
      have hmem : A ∈ Z := (hF (topOrbitIndex ab) A).mp ⟨p, hp, hA.symm⟩
      exact ⟨⟨A, hmem⟩, hkinj ((he ⟨A, hmem⟩).trans hA)⟩
  have hEmb : IsEmbedding (g ∘ e) := hecomp ▸ hh.isEmbedding.comp IsEmbedding.subtypeVal
  have heEmb : IsEmbedding e := ⟨hg.of_comp_iff.mp hEmb.isInducing, hEmb.injective.of_comp⟩
  have heOpen : IsOpenEmbedding e :=
    ⟨heEmb, hr ▸ hh.isOpen_range.preimage hg.continuous⟩
  refine ⟨F, e, heOpen, he, ?_, hr⟩
  intro i A
  rw [show (A.val ∈ chartZeroSet (F i)) ↔ _ from (hF i A.val).symm]
  constructor
  · exact fun hi ↦ ⟨e A, hi, he A⟩
  · rintro ⟨p, hp, hAp⟩
    have hep : e A = p := hkinj ((he A).trans hAp.symm)
    exact hep.symm ▸ hp

end SchubertCharts

section RealChartEquations

open LinearAlgebraicGroups.Specs.GrassmannianCharts

private def complexOfCoordinates {σ : Type} (z : σ × Bool → ℝ) (v : σ) : ℂ :=
  ⟨z (v, false), z (v, true)⟩

private theorem complexPolynomial_real_and_imaginary {σ : Type} (p : MvPolynomial σ ℂ) :
    ∃ r s : MvPolynomial (σ × Bool) ℝ, ∀ z : σ × Bool → ℝ,
      (MvPolynomial.aeval (complexOfCoordinates z) p).re = MvPolynomial.aeval z r ∧
        (MvPolynomial.aeval (complexOfCoordinates z) p).im = MvPolynomial.aeval z s := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨MvPolynomial.C c.re, MvPolynomial.C c.im, fun z ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨pr, pi, hp⟩ := hp
    obtain ⟨qr, qi, hq⟩ := hq
    exact ⟨pr + qr, pi + qi, fun z ↦ by simp only [map_add, Complex.add_re, Complex.add_im,
      (hp z).1, (hp z).2, (hq z).1, (hq z).2, and_self]⟩
  | mul_X p v hp =>
    obtain ⟨r, s, hp⟩ := hp
    refine ⟨r * MvPolynomial.X (v, false) - s * MvPolynomial.X (v, true),
      r * MvPolynomial.X (v, true) + s * MvPolynomial.X (v, false), fun z ↦ ?_⟩
    simp only [map_add, map_sub, map_mul, MvPolynomial.aeval_X, Complex.mul_re, Complex.mul_im,
      (hp z).1, (hp z).2, complexOfCoordinates, and_self]

private def chartRealHomeomorph {ι : Type} [DecidableEq ι] {d : ℕ} (I : Pivot ι d) :
    (((Outside I × Inside I) × Bool) → ℝ) ≃ₜ Matrix (Outside I) (Inside I) ℂ where
  toFun z := Matrix.of fun j i ↦ complexOfCoordinates z (j, i)
  invFun A v := if v.2 then (A v.1.1 v.1.2).im else (A v.1.1 v.1.2).re
  left_inv z := by
    funext v
    rcases v with ⟨⟨j, i⟩, b⟩
    cases b <;> rfl
  right_inv A := by
    ext j i
    apply Complex.ext <;> rfl
  continuous_toFun := by
    apply continuous_matrix
    intro j i
    have hc : Continuous (fun z : (((Outside I × Inside I) × Bool) → ℝ) ↦
        (z ((j, i), false), z ((j, i), true))) :=
      (continuous_apply _).prodMk (continuous_apply _)
    exact Complex.equivRealProdCLM.symm.continuous.comp hc
  continuous_invFun := by
    apply continuous_pi
    rintro ⟨⟨j, i⟩, b⟩
    cases b
    · exact Complex.continuous_re.comp (continuous_id.matrix_elem j i)
    · exact Complex.continuous_im.comp (continuous_id.matrix_elem j i)

private theorem chartZeroSet_real_polynomials {ι : Type} [DecidableEq ι] {d : ℕ} (I : Pivot ι d)
    (F : Finset (chartAlgebra (k := ℂ) I)) :
    ∃ G : Finset (MvPolynomial ((Outside I × Inside I) × Bool) ℝ),
      (chartRealHomeomorph I) ⁻¹' chartZeroSet F = zeroLocus G := by
  classical
  choose r s hs using
    (complexPolynomial_real_and_imaginary (σ := Outside I × Inside I))
  refine ⟨F.image r ∪ F.image s, ?_⟩
  ext z
  simp only [Set.mem_preimage, chartZeroSet, zeroLocus, Set.mem_ofPred_eq]
  have hparts (p : chartAlgebra (k := ℂ) I) :
      MvPolynomial.aeval (chartVariables I (chartRealHomeomorph I z)) p = 0 ↔
      MvPolynomial.aeval z (r p) = 0 ∧ MvPolynomial.aeval z (s p) = 0 := by
    change MvPolynomial.aeval (complexOfCoordinates z) p = 0 ↔ _
    rw [Complex.ext_iff, (hs p z).1, (hs p z).2, Complex.zero_re, Complex.zero_im]
  constructor
  · intro h q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact ((hparts p).mp (h p hp)).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact ((hparts p).mp (h p hp)).2
  · intro h p hp
    exact (hparts p).mpr
      ⟨h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem r hp)),
        h _ (Finset.mem_union_right _ (Finset.mem_image_of_mem s hp))⟩

/-- The analytic Schubert chart and every closed Schubert union in it have finite real
polynomial equations in the same real and imaginary coordinates. -/
theorem schubertChart_realPolynomialModel
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (I : Pivot (Fin 2 × Fin (2 * N)) (occupiedDimension ab N hN).val) :
    ∃ (G : OrbitIndex ab → Finset (MvPolynomial ((Outside I × Inside I) × Bool) ℝ))
      (e : zeroLocus (G (topOrbitIndex ab)) → SchubertSpace ab N hN),
      IsOpenEmbedding e ∧
      (∀ i z, e z ∈ tailPoints (hN := hN) i ↔ z.val ∈ zeroLocus (G i)) ∧
      Set.range e = (schubertGrassmannianPoint ab N hN) ⁻¹' Set.range
        (grassmannianChartPoint (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le (occupiedDimension ab N hN)) I) := by
  classical
  obtain ⟨F, e, he, _, ht, hr⟩ := schubertChart_model comparison stratification smith ab N hN I
  choose G hG using fun i ↦ chartZeroSet_real_polynomials I (F i)
  let H := chartRealHomeomorph I
  let f : zeroLocus (G (topOrbitIndex ab)) → chartZeroSet (F (topOrbitIndex ab)) :=
    fun z ↦ ⟨H z.val, by
      change z.val ∈ (chartRealHomeomorph I) ⁻¹' chartZeroSet (F (topOrbitIndex ab))
      rw [hG]
      exact z.property⟩
  have hf_inj : Function.Injective f :=
    fun _ _ h ↦ Subtype.ext (H.injective (congrArg Subtype.val h))
  have hf_surj : Function.Surjective f := by
    intro A
    have hA : H.symm A.val ∈ zeroLocus (G (topOrbitIndex ab)) := by
      rw [← hG]
      change H (H.symm A.val) ∈ chartZeroSet (F (topOrbitIndex ab))
      rw [H.apply_symm_apply]
      exact A.property
    exact ⟨⟨H.symm A.val, hA⟩, Subtype.ext (H.apply_symm_apply A.val)⟩
  have hf : IsInducing f :=
    IsInducing.subtypeVal.of_comp_iff.mp (H.isInducing.comp IsInducing.subtypeVal)
  have hfopen : IsOpenEmbedding f := ⟨⟨hf, hf_inj⟩, hf_surj.range_eq ▸ isOpen_univ⟩
  refine ⟨G, e ∘ f, he.comp hfopen, ?_, ?_⟩
  · intro i z
    change e (f z) ∈ tailPoints i ↔ z.val ∈ zeroLocus (G i)
    rw [ht i, ← hG]
    rfl
  · rw [Set.range_comp, hf_surj.range_eq, Set.image_univ, hr]

private theorem mem_stagePoints_iff_avoids_tail {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i)
    (k : ℕ) (p : SchubertSpace ab N hN) :
    p ∈ stagePoints ab N hN k ↔ ∀ i : OrbitIndex ab, k < i.val → p ∉ tailPoints i := by
  obtain ⟨j, hj, huniq⟩ := partition p
  constructor
  · rintro ⟨i, hi, hpi⟩ m hm ⟨l, hml, hl⟩
    have hli : l = i := (huniq l hl).trans (huniq i hpi).symm
    rw [hli] at hml
    omega
  · intro ht
    refine ⟨j, ?_, hj⟩
    by_contra! h
    exact ht j h ⟨j, le_rfl, hj⟩

private theorem mem_orbitPoints_iff_tail_and_stage {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (partition : ∀ p : SchubertSpace ab N hN, ∃! i, p ∈ orbitPoints ab N hN i)
    (i : OrbitIndex ab) (p : SchubertSpace ab N hN) :
    p ∈ orbitPoints ab N hN i ↔ p ∈ tailPoints i ∧ p ∈ stagePoints ab N hN i.val := by
  constructor
  · exact fun hp ↦ ⟨⟨i, le_rfl, hp⟩, ⟨i, le_rfl, hp⟩⟩
  · rintro ⟨⟨j, hij, hj⟩, l, hli, hl⟩
    obtain ⟨m, _, hm⟩ := partition p
    have hlj := (hm l hl).trans (hm j hj).symm
    rw [hlj] at hli
    have hij' : i = j := Fin.ext (Nat.le_antisymm hij hli)
    rwa [hij']

/-- Every point has an open chart with a real polynomial description of the stage
and of each orbit. The same finite family of polynomial equations suffices for
all earlier stages and all orbits in the chart. -/
theorem schubert_real_chart_at
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (p : SchubertSpace ab N hN) :
    ∃ (I : Pivot (Fin 2 × Fin (2 * N)) (occupiedDimension ab N hN).val)
      (G : OrbitIndex ab → Finset (MvPolynomial ((Outside I × Inside I) × Bool) ℝ))
      (e : zeroLocus (G (topOrbitIndex ab)) → SchubertSpace ab N hN),
      IsOpenEmbedding e ∧ p ∈ Set.range e ∧
      (∀ k z, e z ∈ stagePoints ab N hN k ↔
        ∀ i : OrbitIndex ab, k < i.val → z.val ∉ zeroLocus (G i)) ∧
      ∀ i z, e z ∈ orbitPoints ab N hN i ↔ z.val ∈ zeroLocus (G i) ∧
        ∀ j : OrbitIndex ab, i.val < j.val → z.val ∉ zeroLocus (G j) := by
  let d := occupiedDimension ab N hN
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  obtain ⟨I, A, hp⟩ := grassmannianChartPoint_cover b (windowDimension_le d)
    (schubertGrassmannianPoint ab N hN p)
  obtain ⟨G, e, he, hT, hR⟩ := schubertChart_realPolynomialModel comparison stratification smith ab N hN I
  obtain ⟨E, hE, _⟩ := stratification ab N hN
  have hpart := orbitPoints_partition smith E hE
  have hs (k : ℕ) (z : zeroLocus (G (topOrbitIndex ab))) :
      e z ∈ stagePoints ab N hN k ↔ ∀ i : OrbitIndex ab, k < i.val → z.val ∉ zeroLocus (G i) := by
    rw [mem_stagePoints_iff_avoids_tail hpart]
    simp only [hT]
  refine ⟨I, G, e, he, hR.symm ▸ ⟨A, hp⟩, hs, fun i z ↦ ?_⟩
  rw [mem_orbitPoints_iff_tail_and_stage hpart, hT, hs]

theorem chartZeroSet_inter_box_isCompact {σ : Type} (G : Finset (MvPolynomial σ ℝ))
    (a b : σ → ℝ) : IsCompact (zeroLocus G ∩ Set.Icc a b) :=
  RealPolynomialChartTriangulation.isCompact_boxZeroLocus G a b

end RealChartEquations

section LocalCohomology

open CategoryTheory.Limits Opposite

private theorem stalk_finite_of_cofinal_rank_bound {X : TopCat.{0}} (P : X.Presheaf Coeff.{0})
    (x : X) (r : ℕ)
    (h : ∀ U : Opens X, x ∈ U → ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧
      Module.Finite ℚ (P.obj (op V)) ∧ Module.finrank ℚ (P.obj (op V)) ≤ r) :
    Module.Finite ℚ (P.stalk x) ∧ Module.finrank ℚ (P.stalk x) ≤ r := by
  have hr : Module.rank ℚ (P.stalk x) ≤ (r : Cardinal) := by
    by_contra! hr
    have hr' : ((r + 1 : ℕ) : Cardinal) ≤ Module.rank ℚ (P.stalk x) := by
      rw [Nat.cast_add_one, Cardinal.natCast_add_one_le_iff]
      exact hr
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_rank hr'
    choose U hx s hs using fun i ↦ P.exists_germ_eq (f i)
    let W : Opens X := ⨅ i, U i
    have hxW : x ∈ W := by
      show x ∈ (W : Set X)
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.mpr hx
    obtain ⟨V, hVW, hxV, hfinite, hdim⟩ := h W hxW
    let : Module.Finite ℚ (P.obj (op V)) := hfinite
    let g (i : Fin (r + 1)) : V ⟶ U i := homOfLE (hVW.trans (iInf_le U i))
    let t (i : Fin (r + 1)) : P.obj (op V) := P.map (g i).op (s i)
    let m := (P.germ V x hxV).hom
    have hcomp : m ∘ t = f := by
      funext i
      change P.germ V x hxV (P.map (g i).op (s i)) = f i
      rw [P.germ_res_apply (g i) x hxV (s i)]
      exact hs i
    have hind : LinearIndependent ℚ t := LinearIndependent.of_comp m (hcomp.symm ▸ hf)
    have hcard := hind.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    exact (Nat.not_succ_le_self r) (hcard.trans hdim)
  have hfinite : Module.Finite ℚ (P.stalk x) :=
    Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0))
  let : Module.Finite ℚ (P.stalk x) := hfinite
  refine ⟨hfinite, ?_⟩
  have hd := (Module.finrank_eq_rank ℚ (P.stalk x)).trans_le hr
  exact_mod_cast hd

private theorem stalk_isZero_of_cofinal_vanishing {X : TopCat.{0}} (P : X.Presheaf Coeff.{0})
    (x : X) (h : ∀ U : Opens X, x ∈ U → ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧ IsZero (P.obj (op V))) :
    IsZero (P.stalk x) := by
  have hzero (a : P.stalk x) : a = 0 := by
    obtain ⟨U, hxU, s, hs⟩ := P.exists_germ_eq a
    obtain ⟨V, hVU, hxV, hz⟩ := h U hxU
    let g : V ⟶ U := homOfLE hVU
    have hg : P.map g.op = 0 := hz.eq_of_tgt _ _
    calc
      a = P.germ U x hxU s := hs.symm
      _ = P.germ V x hxV (P.map g.op s) := (P.germ_res_apply g x hxV s).symm
      _ = 0 := by simp [hg]
  let : Subsingleton (P.stalk x) := ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- A cofinal system of uniformly finite-dimensional neighborhood hypercohomology gives a
finite-dimensional stalk of the actual higher direct image. -/
theorem higherDirectImage_stalk_finite_of_cofinal_rank_bound
    {U Y : TopCat.{0}} (j : U ⟶ Y) (F : BoundedBelow U) (x : Y) (q : ℤ) (r : ℕ) :
    let P := (Opens.map j).op ⋙ LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves U)) F q
    (∀ W : Opens Y, x ∈ W → ∃ V : Opens Y, V ≤ W ∧ x ∈ V ∧
      Module.Finite ℚ (P.obj (op V)) ∧ Module.finrank ℚ (P.obj (op V)) ≤ r) →
    let M := (stalk x).obj ((cohomology Y q).obj ((derivedDirectImage j).obj F).obj)
    Module.Finite ℚ M ∧ Module.finrank ℚ M ≤ r := by
  dsimp only
  intro h
  obtain ⟨e⟩ := DerivedLocalSheaves.higherDirectImageStalk j x q F
  let P := (Opens.map j).op ⋙ LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves U)) F q
  obtain ⟨hfinite, hdim⟩ := stalk_finite_of_cofinal_rank_bound P x r h
  let : Module.Finite ℚ (LocalSheaf.stalkColimit P x) := hfinite
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, e.toLinearEquiv.finrank_eq.trans_le hdim⟩

/-- Cofinal vanishing of the neighborhood hypercohomology implies vanishing of the
corresponding higher direct image stalk. -/
theorem higherDirectImage_stalk_zero_of_cofinal_vanishing
    {U Y : TopCat.{0}} (j : U ⟶ Y) (F : BoundedBelow U) (x : Y) (q : ℤ) :
    let P := (Opens.map j).op ⋙ LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves U)) F q
    (∀ W : Opens Y, x ∈ W → ∃ V : Opens Y, V ≤ W ∧ x ∈ V ∧ IsZero (P.obj (op V))) →
    IsZero ((stalk x).obj ((cohomology Y q).obj ((derivedDirectImage j).obj F).obj)) := by
  dsimp only
  intro h
  obtain ⟨e⟩ := DerivedLocalSheaves.higherDirectImageStalk j x q F
  exact (stalk_isZero_of_cofinal_vanishing _ x h).of_iso e

end LocalCohomology

section BoundedStalkCohomology

open CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated Opposite

open private truncationTriangle truncationTriangle_distinguished truncationTriangle_isLE
  truncationTriangle_isGE truncationCohomologyIsIso plusIsGE_iff plusIsLE_iff
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

open LocalSheaf

private abbrev stalkCohomology {Y : TopCat.{0}} (x : Y) (q : ℤ) (F : BoundedBelow Y) : Coeff.{0} :=
  (stalk x).obj ((DerivedCategory.Plus.homologyFunctor (Sheaves Y) q).obj F)

/-- Bounded, finite-dimensional stalk cohomology at one point. -/
def HasBoundedFiniteStalkCohomology {Y : TopCat.{0}} (x : Y) (F : BoundedBelow Y) : Prop :=
  Set.Finite {q : ℤ | ¬ IsZero (stalkCohomology x q F)} ∧
    ∀ q : ℤ, Module.Finite ℚ (stalkCohomology x q F)

theorem hasBoundedFiniteStalkCohomology_of_cofinal_models
    {U Y : TopCat.{0}} (j : U ⟶ Y) (F : BoundedBelow U) (x : Y)
    (S : Finset ℤ) (r : ℤ → ℕ)
    (h : ∀ (q : ℤ) (W : Opens Y), x ∈ W →
      let P := (Opens.map j).op ⋙ derivedOpenCohomology (𝟭 (Sheaves U)) F q
      ∃ V : Opens Y, V ≤ W ∧ x ∈ V ∧
        Module.Finite ℚ (P.obj (op V)) ∧ Module.finrank ℚ (P.obj (op V)) ≤ r q ∧
        (q ∉ S → IsZero (P.obj (op V)))) :
    HasBoundedFiniteStalkCohomology x ((derivedDirectImage j).obj F) := by
  constructor
  · apply S.finite_toSet.subset
    intro q hq
    by_contra hn
    apply hq
    apply higherDirectImage_stalk_zero_of_cofinal_vanishing
    intro W hx
    obtain ⟨V, hv, hV, _, _, hz⟩ := h q W hx
    exact ⟨V, hv, hV, hz hn⟩
  · intro q
    apply (higherDirectImage_stalk_finite_of_cofinal_rank_bound j F x q (r q) ?_).1
    intro W hx
    obtain ⟨V, hv, hV, hfin, hd, _⟩ := h q W hx
    exact ⟨V, hv, hV, hfin, hd⟩

private theorem hasBoundedFiniteStalkCohomology_of_iso
    {Y : TopCat.{0}} (x : Y) {F G : BoundedBelow Y} (e : F ≅ G)
    (h : HasBoundedFiniteStalkCohomology x F) : HasBoundedFiniteStalkCohomology x G := by
  let m (q : ℤ) := (DerivedCategory.Plus.homologyFunctor (Sheaves Y) q ⋙ stalk x).mapIso e
  exact ⟨h.1.subset (fun q hq h0 ↦ hq (h0.of_iso (m q).symm)),
    fun q ↦ by
      let : Module.Finite ℚ ((DerivedCategory.Plus.homologyFunctor (Sheaves Y) q ⋙ stalk x).obj F) :=
        h.2 q
      exact Module.Finite.equiv (m q).toLinearEquiv⟩

private theorem finite_middle_exact (S : ShortComplex Coeff.{0}) (hS : S.Exact)
    (hL : Module.Finite ℚ S.X₁) (hR : Module.Finite ℚ S.X₃) : Module.Finite ℚ S.X₂ := by
  let g := S.g.hom
  let : Module.Finite ℚ g.range := Module.Finite.of_injective _ g.range.injective_subtype
  have hker : LinearMap.ker g.rangeRestrict = LinearMap.ker g := by
    ext x
    simp [LinearMap.mem_ker, g]
  have hex : Function.Exact S.f.hom g.rangeRestrict := LinearMap.exact_iff.mpr
    (hker.trans hS.moduleCat_range_eq_ker.symm)
  exact Module.Finite.of_exact hex g.surjective_rangeRestrict

private theorem boundedFiniteStalk_of_triangle {Y : TopCat.{0}} (x : Y)
    (T : Triangle (BoundedBelow Y)) (hT : T ∈ distTriang (BoundedBelow Y))
    (h₁ : HasBoundedFiniteStalkCohomology x T.obj₁)
    (h₃ : HasBoundedFiniteStalkCohomology x T.obj₃) : HasBoundedFiniteStalkCohomology x T.obj₂ := by
  let H := DerivedCategory.Plus.homologyFunctor (Sheaves Y) 0
  let S (q : ℤ) := (ShortComplex.mk _ _ (H.homologySequence_comp T hT q)).map (stalk x)
  have hex (q : ℤ) : (S q).Exact := (H.homologySequence_exact₂ T hT q).map (stalk x)
  constructor
  · apply (h₁.1.union h₃.1).subset
    intro q hq
    by_contra h
    change ¬ (¬ IsZero (S q).X₁ ∨ ¬ IsZero (S q).X₃) at h
    have hz₁ : IsZero (S q).X₁ := Classical.not_not.mp (not_or.mp h).1
    have hz₃ : IsZero (S q).X₃ := Classical.not_not.mp (not_or.mp h).2
    exact hq ((hex q).isZero_of_both_zeros (hz₁.eq_of_src _ _) (hz₃.eq_of_tgt _ _))
  · intro q
    exact finite_middle_exact (S q) (hex q) (h₁.2 q) (h₃.2 q)

private theorem nonempty_iso_single_cohomology {U : TopCat.{0}} (F : BoundedBelow U) (q : ℤ)
    (hle : F.IsLE q) (hge : F.IsGE q) :
    Nonempty (F ≅ (DerivedCategory.Plus.singleFunctor (Sheaves U) q).obj
      ((cohomology U q).obj F.obj)) := by
  let S := DerivedCategory.singleFunctor (Sheaves U) q
  let H := cohomology U q
  have : F.obj.IsLE q := (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mpr hle
  have : F.obj.IsGE q := (DerivedCategory.Plus.isGE_ι_obj_iff _ _).mpr hge
  obtain ⟨A, ⟨e⟩⟩ := F.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE q
  let eH : H.obj F.obj ≅ A :=
    H.mapIso e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves U) q).app A
  exact ⟨ObjectProperty.isoMk _ (e ≪≫ S.mapIso eH.symm)⟩

private theorem truncationGT_cohomology_isIso {U : TopCat.{0}}
    (a q : ℤ) (F : BoundedBelow U) (hq : a < q) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (Sheaves U) q).map (truncationTriangle a F).mor₂) := by
  let T := truncationTriangle a F
  let H := DerivedCategory.Plus.homologyFunctor (Sheaves U) 0
  have hT := truncationTriangle_distinguished a F
  have hz (m : ℤ) (hm : a < m) : IsZero ((H.shift m).obj T.obj₁) :=
    (plusIsLE_iff _ _).mp (truncationTriangle_isLE a F) m hm
  have hmono : Mono ((H.shift q).map T.mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff T hT q).mpr ((hz q hq).eq_of_src _ _)
  have hepi : Epi ((H.shift q).map T.mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff T hT q (q + 1) rfl).mpr
      ((hz (q + 1) (by omega)).eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

/-- For bounded complexes, finite bounded stalk cohomology of the higher direct image
follows from the corresponding checks on the ordinary cohomology sheaves. -/
theorem boundedFiniteDirectImageStalk_of_cohomology
    {U Y : TopCat.{0}} (j : U ⟶ Y) (x : Y) (F : BoundedBelow U)
    (a b : ℤ) (hab : a ≤ b) (hge : F.IsGE a) (hle : F.IsLE b)
    (hF : ∀ q : ℤ, a ≤ q → q ≤ b →
      HasBoundedFiniteStalkCohomology x ((derivedDirectImage j).obj
        ((DerivedCategory.Plus.singleFunctor (Sheaves U) q).obj ((cohomology U q).obj F.obj)))) :
    HasBoundedFiniteStalkCohomology x ((derivedDirectImage j).obj F) := by
  let R := derivedDirectImage j
  let t := DerivedCategory.TStructure.t (C := Sheaves U)
  let : R.CommShift ℤ := by unfold R derivedDirectImage; infer_instance
  let : R.IsTriangulated := by unfold R derivedDirectImage; infer_instance
  let S (q : ℤ) := DerivedCategory.Plus.singleFunctor (Sheaves U) q
  have single_transfer (G : BoundedBelow U) (q : ℤ) (hle : G.IsLE q) (hge : G.IsGE q)
      (h : HasBoundedFiniteStalkCohomology x (R.obj ((S q).obj ((cohomology U q).obj G.obj)))) :
      HasBoundedFiniteStalkCohomology x (R.obj G) := by
    obtain ⟨e⟩ := nonempty_iso_single_cohomology G q hle hge
    exact hasBoundedFiniteStalkCohomology_of_iso x (R.mapIso e.symm) h
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n generalizing F with
  | zero =>
    simp only [Nat.cast_zero, add_zero] at hle hF
    exact single_transfer F a hle hge (hF a le_rfl le_rfl)
  | succ n ih =>
    let c := a + (n : ℤ)
    let T := truncationTriangle c F
    have hT := truncationTriangle_distinguished c F
    have ha₁ : T.obj₁.IsGE a := by
      have : F.obj.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff _ _).mpr hge
      apply (DerivedCategory.Plus.isGE_ι_obj_iff _ _).mp
      change t.IsGE ((t.truncLT (c + 1)).obj F.obj) a
      infer_instance
    have hb₁ : T.obj₁.IsLE c := truncationTriangle_isLE c F
    have hb₃ : T.obj₃.IsLE (c + 1) := by
      have : F.obj.IsLE (c + 1) := (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mpr
        (by simpa only [Nat.cast_succ, ← add_assoc, c] using hle)
      apply (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mp
      change t.IsLE ((t.truncGE (c + 1)).obj F.obj) (c + 1)
      infer_instance
    have hL : HasBoundedFiniteStalkCohomology x (R.obj T.obj₁) :=
      ih T.obj₁ ha₁ hb₁ (by
        intro q hqa hqc
        have : IsIso ((DerivedCategory.Plus.homologyFunctor (Sheaves U) q).map T.mor₁) :=
          truncationCohomologyIsIso c q F hqc
        let e := asIso ((DerivedCategory.Plus.homologyFunctor (Sheaves U) q).map T.mor₁)
        exact hasBoundedFiniteStalkCohomology_of_iso x (R.mapIso ((S q).mapIso e.symm))
          (hF q hqa (by omega)))
    have hR : HasBoundedFiniteStalkCohomology x (R.obj T.obj₃) := by
      apply single_transfer T.obj₃ (c + 1) hb₃ (truncationTriangle_isGE c F)
      have : IsIso ((DerivedCategory.Plus.homologyFunctor (Sheaves U) (c + 1)).map T.mor₂) :=
        truncationGT_cohomology_isIso c (c + 1) F (by omega)
      let e := asIso ((DerivedCategory.Plus.homologyFunctor (Sheaves U) (c + 1)).map T.mor₂)
      exact hasBoundedFiniteStalkCohomology_of_iso x (R.mapIso ((S (c + 1)).mapIso e))
        (hF (c + 1) (by omega) (by omega))
    exact boundedFiniteStalk_of_triangle x (R.mapTriangle.obj T) (R.map_distinguished _ hT) hL hR

open private pullbackCohomologyIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

/-- A single bounded finite-dimensional direct-image stalk gives boundedness and
finite-dimensional stalks everywhere on the newly attached orbit. -/
theorem orbitBoundaryCohomology_finite_of_one_stalk
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} {k : ℕ}
    (hk : k + 1 ≤ difference ab / 2)
    {U Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    {D : DimensionFiltration U (orbitDimension ab k)}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D) (x : boundary j)
    (hx : HasBoundedFiniteStalkCohomology x.val ((derivedDirectImage j).obj (complex D))) :
    HasBoundedFiniteStalkCohomology x ((boundedBelowInverseImage (closedInclusion (boundary j))).obj
      ((derivedDirectImage j).obj (complex D))) ∧
    ∀ y : boundary j, ∀ q : ℤ, Module.Finite ℚ (stalkCohomology y q
      ((boundedBelowInverseImage (closedInclusion (boundary j))).obj
        ((derivedDirectImage j).obj (complex D)))) := by
  let B := TopCat.of (boundary j)
  let i : B ⟶ Y := closedInclusion (boundary j)
  let R := (derivedDirectImage j).obj (complex D)
  let G : BoundedBelow B := (boundedBelowInverseImage i).obj R
  let b (q : ℤ) : stalkCohomology x.val q R ≅ stalkCohomology x q G :=
    inverseImageStalkIso i ((cohomology Y q).obj R.obj) x ≪≫
      (stalk x).mapIso (pullbackCohomologyIso i R q).symm
  have hGx (q : ℤ) : Module.Finite ℚ (stalkCohomology x q G) := by
    let : Module.Finite ℚ (stalkCohomology x.val q R) := hx.2 q
    exact Module.Finite.equiv (b q).toLinearEquiv
  refine ⟨⟨hx.1.subset (fun q hq h0 ↦ hq (h0.of_iso (b q).symm)), hGx⟩, ?_⟩
  intro y q
  let F := (cohomology B q).obj G.obj
  obtain ⟨v, hv, ⟨e⟩⟩ :=
    orbitBoundaryCohomology_transitive comparison stratification jets hk hj stage prev y x
  let u := eqToIso (congrArg (fun z : B ↦ (stalk z).obj F) hv.symm)
  let v' := u ≪≫ inverseImageStalkIso v.hom F y ≪≫
    (stalk y).mapIso (inverseImage_cohomology_iso v G e q)
  let : Module.Finite ℚ ((stalk x).obj F) := hGx q
  exact Module.Finite.equiv v'.toLinearEquiv

end BoundedStalkCohomology

section ConstantSheaves

open CategoryTheory.Limits Opposite

private abbrev constantPresheaf (X : TopCat.{0}) (V : Coeff.{0}) : X.Presheaf Coeff.{0} :=
  (Functor.const _).obj V

/-- The stalk of the actual sheafified constant presheaf identifies with its coefficient module. -/
def constantSheafStalkIso (X : TopCat.{0}) (V : Coeff.{0}) (x : X) :
    (stalk x).obj (constant X V) ≅ V := by
  let P := constantPresheaf X V
  let C := TopCat.Presheaf.stalkFunctor Coeff.{0} x
  let u := toSheafify (Opens.grothendieckTopology X) P
  let : IsIso (C.map u) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ P
  let J := (OpenNhds x)ᵒᵖ
  let h : IsColimit (constCocone J V) := isColimitConstCocone J V
  let e : C.obj P ≅ V := (colimit.isColimit ((Functor.const J).obj V)).coconePointUniqueUpToIso h
  exact (asIso (C.map u)).symm ≪≫ e

/-- The finite-rank part of local constructibility gives a finite-dimensional analytic stalk. -/
theorem finite_stalk_of_locallyConstantFiniteRank {X : TopCat.{0}} (F : Sheaves X)
    (h : LocallyConstantFiniteRank F) (x : X) : Module.Finite ℚ ((stalk x).obj F) := by
  obtain ⟨U, hx, V, hV, ⟨e⟩⟩ := h x
  let y : TopCat.of U := ⟨x, hx⟩
  let h' : (stalk x).obj F ≅ V :=
    inverseImageStalkIso (openInclusion U) F y ≪≫
      (stalk y).mapIso e ≪≫ constantSheafStalkIso (TopCat.of U) V y
  exact Module.Finite.equiv h'.toLinearEquiv.symm

/-- A map from a finite-dimensional coefficient module to a stalk is represented
by a linear family of sections on one neighborhood of the point. -/
theorem finite_map_to_stalk_lifts {X : TopCat.{0}} (P : X.Presheaf Coeff.{0}) (x : X)
    (V : Coeff.{0}) [Module.Finite ℚ V] (f : V ⟶ P.stalk x) :
    ∃ (U : Opens X) (hx : x ∈ U) (g : V ⟶ P.obj (op U)),
      g ≫ P.germ U x hx = f := by
  let b := Module.finBasis ℚ V
  choose U hx s hs using fun i ↦ P.exists_germ_eq (f (b i))
  let W := ⨅ i, U i
  have hW : x ∈ W := by
    show x ∈ (W : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  let m (i : Fin (Module.finrank ℚ V)) : W ⟶ U i := homOfLE (iInf_le U i)
  let g := ModuleCat.ofHom (b.constr ℚ fun i ↦ P.map (m i).op (s i))
  refine ⟨W, hW, g, ?_⟩
  apply ModuleCat.hom_ext
  apply b.ext
  intro i
  change P.germ W x hW (b.constr ℚ (fun i ↦ P.map (m i).op (s i)) (b i)) = f (b i)
  rw [b.constr_basis, P.germ_res_apply]
  exact hs i

/-- Equality of germs of two finite-dimensional families of sections holds on
one common smaller neighborhood. -/
theorem finite_map_to_stalk_eq_on_neighborhood {X : TopCat.{0}} (P : X.Presheaf Coeff.{0})
    (x : X) (V : Coeff.{0}) [Module.Finite ℚ V] {U : Opens X} (hx : x ∈ U)
    (f g : V ⟶ P.obj (op U)) (h : f ≫ P.germ U x hx = g ≫ P.germ U x hx) :
    ∃ (W : Opens X), x ∈ W ∧ ∃ m : W ⟶ U, f ≫ P.map m.op = g ≫ P.map m.op := by
  let b := Module.finBasis ℚ V
  have hl (i : Fin (Module.finrank ℚ V)) :
      P.germ U x hx (f (b i)) = P.germ U x hx (g (b i)) := by
    exact congrArg (fun k : V ⟶ P.stalk x ↦ k (b i)) h
  choose W hW l l' hEq using fun i ↦ P.germ_eq x hx hx (f (b i)) (g (b i)) (hl i)
  let O := U ⊓ ⨅ i, W i
  have hO : x ∈ O := by
    show x ∈ (O : Set X)
    rw [Opens.coe_inf, Opens.coe_iInf]
    exact ⟨hx, Set.mem_iInter.mpr hW⟩
  let m : O ⟶ U := homOfLE inf_le_left
  let n (i : Fin (Module.finrank ℚ V)) : O ⟶ W i := homOfLE (inf_le_right.trans (iInf_le W i))
  refine ⟨O, hO, m, ?_⟩
  apply ModuleCat.hom_ext
  apply b.ext
  intro i
  change P.map m.op (f (b i)) = P.map m.op (g (b i))
  have heq := congrArg (fun s ↦ P.map (n i).op s) (hEq i)
  have hlc : n i ≫ l i = m := Subsingleton.elim _ _
  have hlc' : n i ≫ l' i = m := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, Category.assoc,
    ← P.map_comp, ← op_comp, hlc, hlc'] using heq

private def openNeighborhoodImage {U Y : TopCat.{0}} (j : U ⟶ Y) (hj : IsOpenMap j) (x : U) :
    OpenNhds x ⥤ OpenNhds (j x) where
  obj W := ⟨hj.functor.obj W.val, ⟨x, W.property, rfl⟩⟩
  map i := hj.functor.map ((OpenNhds.inclusion x).map i)
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem openNeighborhoodImage_final {U Y : TopCat.{0}} (j : U ⟶ Y) (hj : IsOpenMap j)
    (x : U) : (openNeighborhoodImage j hj x).op.Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun W ↦ ?_)
    (fun {_ c} _ _ ↦ ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)
  let W' : OpenNhds x := ⟨(Opens.map j).obj W.unop.val, W.unop.property⟩
  have i : hj.functor.obj W'.val ⟶ W.unop.val := hj.adjunction.counit.app W.unop.val
  exact ⟨op W', ⟨(show (openNeighborhoodImage j hj x).obj W' ⟶ W.unop from i).op⟩⟩

private def openPresheafRestriction {U Y : TopCat.{0}} {j : U ⟶ Y} (hj : IsOpenMap j) :
    Y.Presheaf Coeff.{0} ⥤ U.Presheaf Coeff.{0} :=
  (Functor.whiskeringLeft _ _ _).obj hj.functor.op

private def openPresheafRestrictionStalkIso {U Y : TopCat.{0}} {j : U ⟶ Y}
    (hj : IsOpenMap j) (x : U) :
    openPresheafRestriction hj ⋙ TopCat.Presheaf.stalkFunctor Coeff.{0} x ≅
      TopCat.Presheaf.stalkFunctor Coeff.{0} (j x) := by
  let K := (openNeighborhoodImage j hj x).op
  let : K.Final := openNeighborhoodImage_final j hj x
  let L := (Functor.whiskeringLeft _ _ Coeff.{0}).obj (OpenNhds.inclusion (j x)).op
  exact Functor.isoWhiskerLeft L (Functor.Final.colimIso K)

private def constantOpenRestrictionHom {U Y : TopCat.{0}} {j : U ⟶ Y} (hj : IsOpenEmbedding j)
    (V : Coeff.{0}) :
    constant U V ⟶ (hj.sheafPullback Coeff.{0}).obj (constant Y V) :=
  let P := constantPresheaf Y V
  let T := (hj.sheafPullback Coeff.{0}).obj (constant Y V)
  let u := toSheafify (Opens.grothendieckTopology Y) P
  let v : constantPresheaf U V ⟶ T.obj := (openPresheafRestriction hj.isOpenMap).map u
  ⟨sheafifyLift (Opens.grothendieckTopology U) v T.property⟩

private theorem constantOpenRestrictionHom_fac {U Y : TopCat.{0}} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) (V : Coeff.{0}) :
    toSheafify (Opens.grothendieckTopology U) (constantPresheaf U V) ≫
      (constantOpenRestrictionHom hj V).hom =
      (openPresheafRestriction hj.isOpenMap).map
        (toSheafify (Opens.grothendieckTopology Y) (constantPresheaf Y V)) :=
  toSheafify_sheafifyLift _ _ _

private def constantOpenRestrictionIso {U Y : TopCat.{0}} {j : U ⟶ Y}
    (hj : IsOpenEmbedding j) (V : Coeff.{0}) :
    constant U V ≅ (hj.sheafPullback Coeff.{0}).obj (constant Y V) := by
  let P := constantPresheaf Y V
  let Q := (constant Y V).obj
  let u : P ⟶ Q := toSheafify (Opens.grothendieckTopology Y) P
  let v := toSheafify (Opens.grothendieckTopology U) (constantPresheaf U V)
  let T := openPresheafRestriction hj.isOpenMap
  let g := constantOpenRestrictionHom hj V
  letI (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Coeff.{0} x).map g.hom) := by
    let F := TopCat.Presheaf.stalkFunctor Coeff.{0} x
    let G := TopCat.Presheaf.stalkFunctor Coeff.{0} (j x)
    let e := openPresheafRestrictionStalkIso hj.isOpenMap x
    let : IsIso (G.map u) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (j x) _ _
    let : IsIso (F.map v) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ _
    have hnat : F.map (T.map u) ≫ e.hom.app Q = e.hom.app P ≫ G.map u :=
      e.hom.naturality u
    have : IsIso (F.map (T.map u) ≫ e.hom.app Q) := by
      rw [hnat]
      infer_instance
    have : IsIso (F.map (T.map u)) := IsIso.of_isIso_comp_right _ (e.hom.app Q)
    let w : sheafify (Opens.grothendieckTopology U) (constantPresheaf U V) ⟶ T.obj Q := g.hom
    have hw : v ≫ w = T.map u := constantOpenRestrictionHom_fac hj V
    have hc : F.map v ≫ F.map w = F.map (T.map u) :=
      (F.map_comp v w).symm.trans (congrArg (fun k ↦ F.map k) hw)
    let : IsIso (F.map v ≫ F.map w) :=
      hc.symm ▸ (inferInstance : IsIso (F.map (T.map u)))
    exact IsIso.of_isIso_comp_left (F.map v) (F.map w)
  haveI : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso g
  exact asIso g

end ConstantSheaves

section OpenDirectImage

open CategoryTheory.Limits LocalSheaf

open private embeddingIsoOfRange embeddingIsoOfRange_comp
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private existsInjectiveRepresentative exactPlusFactors derivedRepresentative
  isIsoDerivedUnitOfInjectives from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private def inverseImageEquivalence {X Y : TopCat.{0}} (e : X ≅ Y) :
    Sheaves Y ≌ Sheaves X :=
  let idIso (Z : TopCat.{0}) : inverseImage (𝟙 Z) ≅ 𝟭 (Sheaves Z) :=
    (inverseDirectAdjunction (𝟙 Z)).leftAdjointUniq Adjunction.id
  CategoryTheory.Equivalence.mk (inverseImage e.hom) (inverseImage e.inv)
    ((idIso Y).symm ≪≫ eqToIso (congrArg (fun f => inverseImage f) e.inv_hom_id.symm) ≪≫
      inverseImageComposition e.inv e.hom)
    ((inverseImageComposition e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun f => inverseImage f) e.hom_inv_id) ≪≫ idIso X)

private theorem inverseImage_injective_of_openEmbedding {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsOpenEmbedding f) (F : Sheaves Y) (hF : Injective F) :
    Injective ((inverseImage f).obj F) := by
  let V : Opens Y := ⟨Set.range f, hf.isOpen_range⟩
  let e := embeddingIsoOfRange f (openInclusion V) hf.isEmbedding V.isOpenEmbedding.isEmbedding
    (Subtype.range_coe (s := (V : Set Y))).symm
  have he : e.hom ≫ openInclusion V = f := embeddingIsoOfRange_comp _ _ _ _ _
  let : Injective ((inverseImage (openInclusion V)).obj F) :=
    DerivedLocalSheaves.restrictionPreservesInjectives V F hF
  let E := inverseImageEquivalence e
  have h : Injective (E.functor.obj ((inverseImage (openInclusion V)).obj F)) :=
    E.functor.injective_obj _
  rw [← he]
  exact Injective.of_iso ((inverseImageComposition e.hom (openInclusion V)).app F).symm
    (show Injective ((inverseImage e.hom).obj ((inverseImage (openInclusion V)).obj F)) from h)

/-- Restricting a pushforward to an open subset is pushforward on the preimage. -/
private def directImageOpenRestrictionIso {U Y U' Y' : TopCat.{0}}
    (j : U ⟶ Y) (k : U' ⟶ Y') (a : U' ⟶ U) (b : Y' ⟶ Y)
    (ha : IsOpenEmbedding a) (hb : IsOpenEmbedding b)
    (h : k ≫ b = a ≫ j) (hrange : Set.range a = j ⁻¹' Set.range b) :
    directImage j ⋙ inverseImage b ≅ inverseImage a ⋙ directImage k := by
  refine Functor.isoWhiskerLeft _ (hb.sheafPullbackIso Coeff.{0}) ≪≫ ?_ ≪≫
    Functor.isoWhiskerRight (ha.sheafPullbackIso Coeff.{0}).symm _
  let JU := Opens.grothendieckTopology U
  let JY := Opens.grothendieckTopology Y
  let JU' := Opens.grothendieckTopology U'
  let JY' := Opens.grothendieckTopology Y'
  haveI : hb.functor.IsContinuous JY' JY := hb.functor_isContinuous
  haveI : ha.functor.IsContinuous JU' JU := ha.functor_isContinuous
  have eq : hb.functor ⋙ Opens.map j = Opens.map k ⋙ ha.functor := by
    refine CategoryTheory.Functor.ext ?_ (by intros; subsingleton)
    intro O
    apply Opens.ext
    change j ⁻¹' (b '' (O : Set Y')) = a '' (k ⁻¹' (O : Set Y'))
    ext u
    have hcomm (v : U') : b (k v) = j (a v) := congrArg (fun g : U' ⟶ Y => g v) h
    constructor
    · rintro ⟨y, hy, ey⟩
      have hu : u ∈ Set.range a := hrange.symm ▸ (show j u ∈ Set.range b from ⟨y, ey⟩)
      obtain ⟨v, rfl⟩ := hu
      have hkv : k v = y := hb.injective ((hcomm v).trans ey.symm)
      exact ⟨v, show k v ∈ O from hkv.symm ▸ hy, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨k v, hv, hcomm v⟩
  letI := Functor.isContinuous_comp hb.functor (Opens.map j) JY' JY JU
  letI := Functor.isContinuous_comp (Opens.map k) ha.functor JY' JU' JU
  exact (Functor.sheafPushforwardContinuousComp hb.functor (Opens.map j) Coeff.{0} JY' JY JU) ≪≫
    Functor.sheafPushforwardContinuousIso (eqToIso eq) Coeff.{0} JY' JU ≪≫
    (Functor.sheafPushforwardContinuousComp (Opens.map k) ha.functor Coeff.{0} JY' JU' JU).symm

/-- Open restriction commutes with the actual bounded-below derived direct image. -/
private theorem derivedDirectImageOpenRestrictionIso {U Y U' Y' : TopCat.{0}}
    (j : U ⟶ Y) (k : U' ⟶ Y') (a : U' ⟶ U) (b : Y' ⟶ Y)
    (ha : IsOpenEmbedding a) (hb : IsOpenEmbedding b)
    (h : k ≫ b = a ≫ j) (hrange : Set.range a = j ⁻¹' Set.range b)
    (F : BoundedBelow U) :
    Nonempty ((boundedBelowInverseImage b).obj ((derivedDirectImage j).obj F) ≅
      (derivedDirectImage k).obj ((boundedBelowInverseImage a).obj F)) := by
  obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
  let J := injectiveComplex I
  let A := inverseImage a
  let B := inverseImage b
  let R := directImage j
  let S := directImage k
  let C := A.mapCochainComplexPlus.obj J
  have hC (n : ℤ) : Injective (C.obj.X n) :=
    inverseImage_injective_of_openEmbedding a ha _ (I.obj.X n).property
  let : IsIso (S.rightDerivedFunctorPlusUnit.app C) :=
    isIsoDerivedUnitOfInjectives S C hC
  let α := directImageOpenRestrictionIso j k a b ha hb h hrange
  let β :
      B.mapCochainComplexPlus.obj (R.mapCochainComplexPlus.obj J) ≅
        S.mapCochainComplexPlus.obj C :=
    (CochainComplex.Plus.ι (Sheaves Y')).preimageIso
      ((NatIso.mapHomologicalComplex α (.up ℤ)).app J.obj)
  let ρ : DerivedCategory.Plus.Q.obj C ≅ (boundedBelowInverseImage a).obj F :=
    ((exactPlusFactors A).app J).symm ≪≫ (boundedBelowInverseImage a).mapIso e
  exact ⟨(boundedBelowInverseImage b).mapIso (derivedRepresentative R I e).symm ≪≫
    (exactPlusFactors B).app (R.mapCochainComplexPlus.obj J) ≪≫
    DerivedCategory.Plus.Q.mapIso β ≪≫ asIso (S.rightDerivedFunctorPlusUnit.app C) ≪≫
    (derivedDirectImage k).mapIso ρ⟩

end OpenDirectImage

section TriangulatedPatches

open SimplicialConstructibleDirectImage

open private liftAlongEmbedding liftAlongEmbedding_comp
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option maxHeartbeats 700000 in
private theorem unionOfFaceInteriors_membership {σ : Type} {K : Geometry.SimplicialComplex ℝ (σ → ℝ)}
    (hpart : ∀ x : K.space, ∃! s : K.faces, x ∈ facePiece (complexInclusion K) s.val)
    {A : Set K.space} (hA : RealPolynomialChartTriangulationSpecs.IsUnionOfFaceInteriors K A)
    (s : K.faces) {x y : K.space}
    (hx : x ∈ facePiece (complexInclusion K) s.val)
    (hy : y ∈ facePiece (complexInclusion K) s.val) : x ∈ A ↔ y ∈ A := by
  obtain ⟨T, hTK, rfl⟩ := hA
  have transfer {v w : K.space} (hv : v ∈ facePiece (complexInclusion K) s.val)
      (hw : w ∈ facePiece (complexInclusion K) s.val)
      (h : v ∈ ⋃ t ∈ T, (Subtype.val : K.space → σ → ℝ) ⁻¹' faceInterior t) :
      w ∈ ⋃ t ∈ T, (Subtype.val : K.space → σ → ℝ) ⁻¹' faceInterior t := by
    simp only [Set.mem_iUnion, Set.mem_preimage] at h ⊢
    obtain ⟨t, htT, ht⟩ := h
    obtain ⟨q, _, hq⟩ := hpart v
    let u : K.faces := ⟨t, hTK htT⟩
    have hmem : v ∈ facePiece (complexInclusion K) u.val := by
      change v.val ∈ faceInterior t
      exact ht
    have hu : u = q := hq u hmem
    have hs : s = q := hq s hv
    have he : t = s.val := congrArg (fun r : K.faces => r.val) (hu.trans hs.symm)
    exact ⟨t, htT, he.symm ▸ (show w.val ∈ faceInterior s.val from hw)⟩
  exact ⟨transfer hx hy, transfer hy hx⟩

private theorem isUnionOfFaceInteriors_of_membership {σ : Type}
    {K : Geometry.SimplicialComplex ℝ (σ → ℝ)}
    (hpart : ∀ x : K.space, ∃! s : K.faces, x ∈ facePiece (complexInclusion K) s.val)
    {A : Set K.space}
    (hA : ∀ (s : K.faces) {x y : K.space},
      x ∈ facePiece (complexInclusion K) s.val →
      y ∈ facePiece (complexInclusion K) s.val → (x ∈ A ↔ y ∈ A)) :
    IsUnionOfFaceInteriors K A := by
  refine ⟨{s | (A ∩ facePiece (complexInclusion K) s.val).Nonempty}, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, _⟩ := hpart x
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨x, hx, hs⟩, hs⟩⟩
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨⟨y, hyA, hy⟩, hx⟩ := Set.mem_iUnion.mp hs
    exact (hA s hy hx).mp hyA

private theorem strictBox_subset_Icc {σ : Type} {a b : σ → ℝ} :
    RealPolynomialChartTriangulationSpecs.strictBox a b ⊆ Set.Icc a b :=
  fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2.le⟩

private theorem range_liftAlongEmbedding {A B X : TopCat.{0}} (f : A ⟶ X) (g : B ⟶ X)
    (hg : IsEmbedding g) (h : Set.range f ⊆ Set.range g) :
    Set.range (liftAlongEmbedding f g hg h) = g ⁻¹' Set.range f := by
  have eq := liftAlongEmbedding_comp f g hg h
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (congrArg (fun m : A ⟶ X => m y) eq).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hg.injective ((congrArg (fun m : A ⟶ X => m y) eq).trans hy)⟩

/-- A common simplicial chart for two nested open stages of the orbit filtration. -/
private structure TriangulatedAttachment {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {U Y : TopCat.{0}} (j : U ⟶ Y) (f : Y ⟶ SchubertSpace ab N hN) (x : Y) where
  coordinates : Type
  finiteCoordinates : Finite coordinates
  K : Geometry.SimplicialComplex ℝ (coordinates → ℝ)
  finiteFaces : K.faces.Finite
  smaller : Opens (TopCat.of K.space)
  larger : Opens (TopCat.of K.space)
  nested : smaller ≤ larger
  smallerUnion : IsUnionOfFaceInteriors K (smaller : Set K.space)
  largerUnion : IsUnionOfFaceInteriors K (larger : Set K.space)
  source : TopCat.of smaller ⟶ U
  target : TopCat.of larger ⟶ Y
  sourceOpen : IsOpenEmbedding source
  targetOpen : IsOpenEmbedding target
  commutes : stageInclusion nested ≫ target = source ≫ j
  preimageRange : Set.range source = j ⁻¹' Set.range target
  contains : x ∈ Set.range target
  sourceOrbit : ∀ (s : K.faces) (i : OrbitIndex ab)
    {v w : TopCat.of smaller},
    v ∈ facePiece (openInclusion smaller ≫ complexInclusion K) s.val →
    w ∈ facePiece (openInclusion smaller ≫ complexInclusion K) s.val →
    ((source ≫ (j ≫ f)) v ∈ orbitPoints ab N hN i ↔
      (source ≫ (j ≫ f)) w ∈ orbitPoints ab N hN i)

set_option maxHeartbeats 900000 in
private theorem exists_triangulatedAttachment
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} {k : ℕ}
    {U Y : TopCat.{0}} {j : U ⟶ Y} {f : Y ⟶ SchubertSpace ab N hN}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : RealizesOrbitStage (j ≫ f) k Q) (x : Y) :
    Nonempty (TriangulatedAttachment j f x) := by
  obtain ⟨I, G, g, hg, ⟨c, hc⟩, hStage, hOrbit⟩ :=
    schubert_real_chart_at comparison stratification smith ab N hN (f x)
  let σ := (LinearAlgebraicGroups.Specs.GrassmannianCharts.Outside I ×
    LinearAlgebraicGroups.Specs.GrassmannianCharts.Inside I) × Bool
  let lo : σ → ℝ := fun i => c.val i - 1
  let hi : σ → ℝ := fun i => c.val i + 1
  have bounds (i : σ) : lo i < hi i := by dsimp [lo, hi]; linarith
  let H := RealPolynomialChartTriangulationSpecs.strictBox lo hi
  have hH : IsOpen H := RealPolynomialChartTriangulation.isOpen_strictBox lo hi
  have hcH : c.val ∈ H := by
    intro i
    dsimp [lo, hi]
    constructor <;> linarith
  obtain ⟨K, e, hK, hZeroLoci, hBoxBoundary⟩ :=
    RealPolynomialChartTriangulation.realPolynomialChartTriangulation
      σ (OrbitIndex ab) G (topOrbitIndex ab) lo hi bounds
  let z (v : K.space) : zeroLocus (G (topOrbitIndex ab)) := ⟨(e v).val, (e v).property.1⟩
  have hsub : zeroLocus (G (topOrbitIndex ab)) ∩
      Set.Icc lo hi ⊆ zeroLocus (G (topOrbitIndex ab)) := Set.inter_subset_left
  have hz : IsEmbedding z := (IsEmbedding.inclusion hsub).comp e.isEmbedding
  let p (v : K.space) : SchubertSpace ab N hN := g (z v)
  have hp : IsEmbedding p := hg.isEmbedding.comp hz
  obtain ⟨E, hE, _⟩ := stratification ab N hN
  have part := orbitPoints_partition smith E hE
  have openStage := stagePoints_isOpen part (tailPoints_isClosed smith comparison E hE)
  let V (l : ℕ) : Opens (TopCat.of K.space) :=
    ⟨{v | (e v).val ∈ H ∧ p v ∈ stagePoints ab N hN l},
      (hH.preimage (continuous_subtype_val.comp e.continuous)).inter
        ((openStage l).preimage hp.continuous)⟩
  have hpart := (faceInteriorsPartition σ K hK).2.1.2.2
  have zeroLocus_membership (s : K.faces) (i : OrbitIndex ab) {v w : K.space}
      (hv : v ∈ facePiece (complexInclusion K) s.val)
      (hw : w ∈ facePiece (complexInclusion K) s.val) :
      (z v).val ∈ zeroLocus (G i) ↔ (z w).val ∈ zeroLocus (G i) :=
    unionOfFaceInteriors_membership hpart (hZeroLoci i) s hv hw
  have insideBox (s : K.faces) {v w : K.space}
      (hv : v ∈ facePiece (complexInclusion K) s.val)
      (hw : w ∈ facePiece (complexInclusion K) s.val) :
      (e v).val ∈ H ↔ (e w).val ∈ H := by
    have h := unionOfFaceInteriors_membership hpart hBoxBoundary s hv hw
    change ((e v).val ∈ Set.Icc lo hi ∧ (e v).val ∉ H) ↔
      ((e w).val ∈ Set.Icc lo hi ∧ (e w).val ∉ H) at h
    simpa only [(e v).property.2, (e w).property.2, true_and, not_iff_not] using h
  have union (l : ℕ) : IsUnionOfFaceInteriors K (V l : Set K.space) := by
    apply isUnionOfFaceInteriors_of_membership hpart
    intro s v w hv hw
    change ((e v).val ∈ H ∧ g (z v) ∈ stagePoints ab N hN l) ↔
      ((e w).val ∈ H ∧ g (z w) ∈ stagePoints ab N hN l)
    rw [hStage, hStage]
    exact and_congr (insideBox s hv hw) (forall_congr' fun i =>
      imp_congr_right fun _ => not_congr (zeroLocus_membership s i hv hw))
  have hV : V k ≤ V (k + 1) :=
    fun _ hv => ⟨hv.1, stagePoints_mono (Nat.le_succ k) hv.2⟩
  let chart (l : ℕ) : TopCat.of (V l) ⟶ SchubertSpace ab N hN :=
    TopCat.ofHom ⟨fun v => p v.val, hp.continuous.comp continuous_subtype_val⟩
  let A : Set (SchubertSpace ab N hN) :=
    g '' ((Subtype.val : zeroLocus (G (topOrbitIndex ab)) → (σ → ℝ)) ⁻¹' H)
  have hA : IsOpen A := hg.isOpenMap _ (hH.preimage continuous_subtype_val)
  have chart_range (l : ℕ) : Set.range (chart l) = A ∩ stagePoints ab N hN l := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨z v.val, v.property.1, rfl⟩, v.property.2⟩
    · rintro ⟨⟨w, hw, rfl⟩, hws⟩
      let q : ↥(zeroLocus (G (topOrbitIndex ab)) ∩
          Set.Icc lo hi) :=
        ⟨w.val, w.property, strictBox_subset_Icc hw⟩
      let v : K.space := e.symm q
      have hv : z v = w := by
        apply Subtype.ext
        change (e (e.symm q)).val = q.val
        rw [e.apply_symm_apply]
      have hvH : (e v).val ∈ H := by
        change (z v).val ∈ H
        rw [hv]
        exact hw
      have hvS : p v ∈ stagePoints ab N hN l := by
        change g (z v) ∈ _
        rwa [hv]
      exact ⟨⟨v, hvH, hvS⟩, congrArg g hv⟩
  have chart_open (l : ℕ) : IsOpenEmbedding (chart l) :=
    ⟨hp.comp IsEmbedding.subtypeVal, chart_range l ▸ (hA.inter (openStage l))⟩
  have hr₀ : Set.range (chart k) ⊆ Set.range (j ≫ f) := by
    rw [chart_range, prev.2.1]
    exact Set.inter_subset_right
  have hr₁ : Set.range (chart (k + 1)) ⊆ Set.range f := by
    rw [chart_range, stage.2.1]
    exact Set.inter_subset_right
  let a := liftAlongEmbedding (chart k) (j ≫ f) (stage.1.isEmbedding.comp hj.isEmbedding) hr₀
  let b := liftAlongEmbedding (chart (k + 1)) f stage.1.isEmbedding hr₁
  have ha : a ≫ (j ≫ f) = chart k := liftAlongEmbedding_comp _ _ _ _
  have hb : b ≫ f = chart (k + 1) := liftAlongEmbedding_comp _ _ _ _
  have haOpen : IsOpenEmbedding a := by
    apply IsOpenEmbedding.of_comp _ (stage.1.comp hj)
    change IsOpenEmbedding (a ≫ (j ≫ f))
    rw [ha]
    exact chart_open k
  have hbOpen : IsOpenEmbedding b := by
    apply IsOpenEmbedding.of_comp _ stage.1
    change IsOpenEmbedding (b ≫ f)
    rw [hb]
    exact chart_open (k + 1)
  have hcomm : stageInclusion hV ≫ b = a ≫ j := by
    let : Mono f := (TopCat.mono_iff_injective _).mpr stage.1.injective
    apply (cancel_mono f).mp
    rw [Category.assoc, Category.assoc, ha, hb]
    rfl
  have hpre : Set.range a = j ⁻¹' Set.range b := by
    change Set.range (liftAlongEmbedding _ _ _ _) =
      j ⁻¹' Set.range (liftAlongEmbedding _ _ _ _)
    rw [range_liftAlongEmbedding, range_liftAlongEmbedding, chart_range, chart_range]
    ext u
    change (f (j u) ∈ A ∧ f (j u) ∈ stagePoints ab N hN k) ↔
      (f (j u) ∈ A ∧ f (j u) ∈ stagePoints ab N hN (k + 1))
    have hprev : f (j u) ∈ stagePoints ab N hN k := prev.2.1 ▸ Set.mem_range_self u
    simp only [hprev, stagePoints_mono (Nat.le_succ k) hprev, and_true]
  have hx : x ∈ Set.range b := by
    change x ∈ Set.range (liftAlongEmbedding _ _ _ _)
    rw [range_liftAlongEmbedding, chart_range]
    exact ⟨⟨c, hcH, hc⟩, stage.2.1 ▸ Set.mem_range_self x⟩
  refine ⟨⟨σ, inferInstance, K, hK, V k, V (k + 1), hV, union _, union _, a, b,
    haOpen, hbOpen, hcomm, hpre, hx, ?_⟩⟩
  intro s i v w hv hw
  rw [ha]
  change (g (z v.val) ∈ orbitPoints ab N hN i ↔ g (z w.val) ∈ orbitPoints ab N hN i)
  rw [hOrbit, hOrbit]
  exact and_congr (zeroLocus_membership s i hv hw) (forall_congr' fun t =>
    imp_congr_right fun _ => not_congr (zeroLocus_membership s t hv hw))

end TriangulatedPatches

section PatchSheaves

open CategoryTheory.Limits SimplicialConstructibleDirectImage

open private stratumEmbedding pullbackCohomologyIso
  locallyConstantFiniteRank_of_iso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem finiteCohomology_pullback {A X : TopCat.{0}} (f : A ⟶ X)
    (F : BoundedBelow X) (hF : Set.Finite {q : ℤ | ¬ IsZero ((cohomology X q).obj F.obj)}) :
    Set.Finite {q : ℤ | ¬ IsZero ((cohomology A q).obj ((boundedBelowInverseImage f).obj F).obj)} := by
  apply hF.subset
  intro q hq hz
  exact hq (((inverseImage f).map_isZero hz).of_iso (pullbackCohomologyIso f F q))

set_option maxHeartbeats 600000 in
private theorem constructible_on_smaller_faces
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N} {k : ℕ}
    {U Y : TopCat.{0}} {j : U ⟶ Y} {f : Y ⟶ SchubertSpace ab N hN} {x : Y}
    (T : TriangulatedAttachment j f x) {Q : Stratification U}
    (prev : RealizesOrbitStage (j ≫ f) k Q) (F : BoundedBelow U)
    (hF : IsConstructible Q F.obj) :
    IsConstructibleOnFaceInteriors T.K (openInclusion T.smaller ≫ complexInclusion T.K)
      ((boundedBelowInverseImage T.source).obj F) := by
  refine ⟨finiteCohomology_pullback T.source F hF.1, fun s q => ?_⟩
  let S := facePiece (openInclusion T.smaller ≫ complexInclusion T.K) s.val
  let i := pieceInclusion S
  let H := (cohomology U q).obj F.obj
  have hlocal : LocallyConstantFiniteRank ((inverseImage (i ≫ T.source)).obj H) := by
    by_cases hn : S.Nonempty
    · obtain ⟨v, hv⟩ := hn
      obtain ⟨p, hp, _⟩ := Q.partition (T.source v)
      obtain ⟨e, he⟩ := prev.2.2
      have hvo : (T.source ≫ (j ≫ f)) v ∈ orbitPoints ab N hN (e p).val := by
        change T.source v ∈ (j ≫ f) ⁻¹' orbitPoints ab N hN (e p).val
        rwa [← (he p).1]
      have hs : Set.range (i ≫ T.source) ⊆ Set.range (Q.stratum p).inclusion := by
        rintro _ ⟨⟨w, hw⟩, rfl⟩
        rw [(he p).1]
        exact (T.sourceOrbit s (e p).val hv hw).mp hvo
      exact locallyConstantFiniteRank_of_range_subset _ _ (stratumEmbedding _) hs H (hF.2 p q)
    · intro z
      exact (hn ⟨z.val, z.property⟩).elim
  exact locallyConstantFiniteRank_of_iso ((inverseImageComposition i T.source).app H ≪≫
    (inverseImage i).mapIso (pullbackCohomologyIso T.source F q).symm) hlocal

set_option maxHeartbeats 1200000 in
private theorem boundary_constructible_of_triangulatedAttachment
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (jets : SchubertJetActions) {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {k : ℕ} (hk : k + 1 ≤ difference ab / 2)
    {U Y : TopCat.{0}} {j : U ⟶ Y} {f : Y ⟶ SchubertSpace ab N hN}
    (hj : IsOpenEmbedding j) {P : Stratification Y} {Q : Stratification U}
    {D : DimensionFiltration U (orbitDimension ab k)}
    (stage : RealizesOrbitStage f (k + 1) P)
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D) (x : boundary j)
    (T : TriangulatedAttachment j f x.val) :
    IsConstructibleOnBoundary j ((derivedDirectImage j).obj (complex D)) := by
  let : Finite T.coordinates := T.finiteCoordinates
  let := Fintype.ofFinite T.coordinates
  let : Finite T.K.faces := T.finiteFaces.to_subtype
  let F := complex D
  let R := (derivedDirectImage j).obj F
  let F' := (boundedBelowInverseImage T.source).obj F
  let j' := stageInclusion T.nested
  let R' := (derivedDirectImage j').obj F'
  have hF := constructible_on_smaller_faces T (normalizedOrbitIC_realizes prev) F
    (normalizedOrbitIC_perverse prev).1
  have hR := openInclusionConstructibility T.coordinates T.K T.finiteFaces
    T.smaller T.larger T.nested T.smallerUnion T.largerUnion F' hF
  obtain ⟨e⟩ := derivedDirectImageOpenRestrictionIso j j' T.source T.target T.sourceOpen
    T.targetOpen T.commutes T.preimageRange F
  let B := TopCat.of (boundary j)
  let B' : Set (TopCat.of T.larger) := T.target ⁻¹' boundary j
  let i := closedInclusion (boundary j)
  let i' := closedInclusion B'
  let t : TopCat.of B' ⟶ B := TopCat.ofHom (T.target.hom.restrictPreimage (boundary j))
  have ht : IsOpenEmbedding t := T.targetOpen.restrictPreimage _
  let G := (boundedBelowInverseImage i).obj R
  let G' := (boundedBelowInverseImage t).obj G
  have htcomm : i' ≫ T.target = t ≫ i := rfl
  let eG : G' ≅ (boundedBelowInverseImage i').obj R' :=
    ((pullbackSquare htcomm).app R).symm ≪≫ (boundedBelowInverseImage i').mapIso e
  obtain ⟨z, hz⟩ := T.contains
  have hzB : z ∈ B' := by
    change T.target z ∈ boundary j
    rw [hz]
    exact x.property
  let z₀ : B' := ⟨z, hzB⟩
  let : Nonempty (TopCat.of B') := ⟨z₀⟩
  -- Finite cohomological support on the patch bounds the stalk at its chosen point.
  have hfinite : Set.Finite {q : ℤ | ¬ IsZero ((cohomology _ q).obj G'.obj)} := by
    apply (finiteCohomology_pullback i' R' hR.1).subset
    intro q hq hz
    exact hq (hz.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso eG))
  have hstalk : Set.Finite {q : ℤ | ¬ IsZero ((stalk (t z₀)).obj ((cohomology B q).obj G.obj))} := by
    apply hfinite.subset
    intro q hq hz
    let H := (cohomology B q).obj G.obj
    let a := inverseImageStalkIso t H z₀ ≪≫
      (stalk z₀).mapIso (pullbackCohomologyIso t G q).symm
    exact hq (((stalk z₀).map_isZero hz).of_iso a)
  refine ⟨orbitBoundaryCohomology_bounded_of_one_stalk comparison stratification jets hk hj
    stage prev (t z₀) hstalk, fun q => ?_⟩
  let H := (cohomology B q).obj G.obj
  let H' := (cohomology (TopCat.of T.larger) q).obj R'.obj
  let eH : (inverseImage t).obj H ≅ (inverseImage i').obj H' :=
    (pullbackCohomologyIso t G q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso eG ≪≫ pullbackCohomologyIso i' R' q
  let p := openInclusion T.larger ≫ complexInclusion T.K
  let S (s : T.K.faces) : Set (TopCat.of B') := facePiece (i' ≫ p) s.val
  have hS (s : T.K.faces) : IsLocallyClosed (S s) :=
    (isLocallyClosed_faceInterior s.val).preimage (i' ≫ p).hom.continuous
  have hcover (w : B') : ∃ s, w ∈ S s := by
    obtain ⟨s, hs, _⟩ :=
      (faceInteriorsPartition T.coordinates T.K T.finiteFaces).2.1.2.2
        ((openInclusion T.larger) (i' w))
    exact ⟨s, hs⟩
  have hlocal (s : T.K.faces) :
      LocallyConstantFiniteRank
        ((inverseImage (closedInclusion (S s))).obj ((inverseImage t).obj H)) := by
    let v := closedInclusion (S s)
    let w := pieceInclusion (facePiece p s.val)
    have hs : Set.range (v ≫ i') ⊆ Set.range w := by
      rintro _ ⟨u, rfl⟩
      exact ⟨⟨i' u.val, u.property⟩, rfl⟩
    exact locallyConstantFiniteRank_of_iso ((inverseImageComposition v i').app H' ≪≫
      (inverseImage v).mapIso eH.symm)
      (locallyConstantFiniteRank_of_range_subset _ _ IsEmbedding.subtypeVal hs H' (hR.2 s q))
  -- A finite locally closed cover gives a nonempty open set on which to trivialize.
  obtain ⟨V, ⟨y, hy⟩, hV⟩ :=
    exists_open_with_locallyConstantFiniteRank ((inverseImage t).obj H) S hS hcover hlocal
  let l := openInclusion V ≫ t
  have hL : LocallyConstantFiniteRank ((inverseImage l).obj H) :=
    locallyConstantFiniteRank_of_iso ((inverseImageComposition (openInclusion V) t).app H).symm hV
  obtain ⟨W, hyW, M, hM, ⟨c⟩⟩ := local_trivialization_of_open_pullback l
    (ht.comp V.isOpenEmbedding) H ⟨y, hy⟩ hL
  apply locallyConstantFiniteRank_of_transitive_trivialization H W hyW M hM c
  intro a b
  obtain ⟨v, hab, ⟨ev⟩⟩ :=
    orbitBoundaryCohomology_transitive comparison stratification jets hk hj stage prev a b
  exact ⟨v, hab, ⟨inverseImage_cohomology_iso v G ev q⟩⟩

private theorem orbitBoundaryConstructibility
    (comparison : BoundedSchubertComparison) (stratification : SchubertStratification)
    (smith : SmithClassification) (jets : SchubertJetActions)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    OrbitBoundaryConstructibility ab N hN := by
  intro k hk U Y f j hj P Q D stage prev
  by_cases hB : Nonempty (boundary j)
  · obtain ⟨x⟩ := hB
    obtain ⟨T⟩ := exists_triangulatedAttachment comparison stratification smith hj
      stage (normalizedOrbitIC_realizes prev) x.val
    exact boundary_constructible_of_triangulatedAttachment comparison stratification jets hk hj
      stage prev x T
  · constructor
    · apply Set.finite_empty.subset
      intro q hq
      exact False.elim (hq ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
        (fun x => (hB ⟨x⟩).elim)))
    · exact fun _ x => (hB ⟨x⟩).elim

/-- The normalized rational intersection complex is bounded and constructible along
the orbit stratification of every reduced rank-two Schubert variety. -/
theorem schubertIntersectionConstructibility : SchubertIntersectionConstructibility := by
  intro ab N hN
  exact schubertIntersectionConstructibility_of_boundaryConstructibility
    RankTwoSchubertStrata.boundedSchubertComparison RankTwoSchubertStrata.schubertStratification
    RankTwoSchubertStrata.smithClassification ab N hN
    (orbitBoundaryConstructibility RankTwoSchubertStrata.boundedSchubertComparison
      RankTwoSchubertStrata.schubertStratification RankTwoSchubertStrata.smithClassification
      RankTwoSchubertStrata.schubertJetActions ab N hN)

end PatchSheaves

end RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
