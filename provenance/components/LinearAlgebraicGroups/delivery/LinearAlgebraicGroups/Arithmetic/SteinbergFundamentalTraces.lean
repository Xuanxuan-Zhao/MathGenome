import Specs.LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
import LinearAlgebraicGroups.Classification.NormalizerComparison
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Representation.SimpleClassification
import LinearAlgebraicGroups.Representation.DominantOrder
import LinearAlgebraicGroups.Representation.PrimitiveLine
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Ring.List

open scoped BigOperators

namespace LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces

noncomputable section

set_option linter.style.haveILetI false

open Specs.SteinbergFundamentalTraces

section MatrixProducts

variable {J B X R : Type*} [DecidableEq B] [Fintype B] [AddCommGroup X] [CommRing R]

/-- The entries of a factor can shift weights only in its own root direction. -/
private def RootSteps (α : J → X) (wt : B → X)
    (M : J → Matrix B B R) : Prop :=
  ∀ i a b, M i a b ≠ 0 → ∃ z : ℤ, wt a - wt b = z • α i

/-- Restrict a matrix to a single weight space, leaving its other entries zero. -/
private def weightBlock (wt : B → X) (μ : X) (M : Matrix B B R) : Matrix B B R :=
  haveI := Classical.decEq X
  fun a b ↦ if wt a = μ ∧ wt b = μ then M a b else 0

private theorem product_weight_difference (α : J → X) (wt : B → X)
    (M : J → Matrix B B R) (hM : RootSteps α wt M) (l : List J) (a b : B)
    (h : (l.map M).prod a b ≠ 0) :
    wt a - wt b ∈ Submodule.span ℤ (α '' {i | i ∈ l}) := by
  classical
  induction l generalizing a b with
  | nil =>
    by_cases hab : a = b
    · subst b
      simp
    · exact False.elim (h (by simp [hab]))
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply] at h
    obtain ⟨c, _, hc⟩ : ∃ c ∈ (Finset.univ : Finset B),
        M i a c * (l.map M).prod c b ≠ 0 := by
      by_contra! he
      exact h (Finset.sum_eq_zero he)
    obtain ⟨z, hz⟩ := hM i a c (left_ne_zero_of_mul hc)
    have htail := ih c b (right_ne_zero_of_mul hc)
    rw [← sub_add_sub_cancel (wt a) (wt c) (wt b), hz]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · exact Submodule.subset_span ⟨i, List.mem_cons_self, rfl⟩
    · exact Submodule.span_mono (Set.image_mono (fun j hj ↦ List.mem_cons_of_mem i hj)) htail

/-- In a word with independent, distinct root directions, a matrix entry
returning to its initial weight only uses the block of that weight at every
step. This statement allows arbitrary weight multiplicities. -/
private theorem product_weightBlock (α : J → X) (hα : LinearIndependent ℤ α)
    (wt : B → X) (M : J → Matrix B B R) (hM : RootSteps α wt M)
    (l : List J) (hl : l.Nodup) {μ : X} (a b : B) (ha : wt a = μ) (hb : wt b = μ) :
    (l.map M).prod a b = (l.map fun i ↦ weightBlock wt μ (M i)).prod a b := by
  classical
  induction l generalizing a b with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases hc : wt c = μ
    · rw [ih (List.nodup_cons.mp hl).2 c b hc hb]
      simp [weightBlock, ha, hc]
    · simp only [weightBlock, ha, hc, and_false, ite_false, zero_mul]
      by_contra hne
      obtain ⟨z, hz⟩ := hM i a c (left_ne_zero_of_mul hne)
      have htail := product_weight_difference α wt M hM l c b (right_ne_zero_of_mul hne)
      have hzmem : z • α i ∈ Submodule.span ℤ (α '' {j | j ∈ l}) := by
        rw [← hz, ha, ← hb]
        exact (neg_sub (wt c) (wt b)) ▸ Submodule.neg_mem _ htail
      have hi := (List.nodup_cons.mp hl).1
      have hα' : LinearIndepOn ℤ α (Set.univ : Set J) := hα.linearIndepOn_univ
      have hsubset : {j : J | j ∈ l} ⊆ (Set.univ : Set J) \ {i} := by
        intro j hj
        exact ⟨Set.mem_univ j, fun hji ↦ hi ((Set.mem_singleton_iff.mp hji) ▸ hj)⟩
      have hz0 : z = 0 := hα'.eq_zero_of_smul_mem_span (Set.mem_univ i) z <|
        Submodule.span_mono (Set.image_mono hsubset) hzmem
      rw [hz0, zero_smul, sub_eq_zero, ha] at hz
      exact hc hz.symm

private theorem list_prod_smul (l : List J) (f : J → R) (M : J → Matrix B B R) :
    (l.map fun i ↦ f i • M i).prod = (l.map f).prod • (l.map M).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm (List.map f l).prod]

end MatrixProducts

section TracePolynomial

variable {k J B W : Type*} [Field k] [Fintype J] [DecidableEq J] [Fintype B]
  [DecidableEq B] [AddCommGroup W]

open MvPolynomial

/-- For a fixed weight, the surviving block of a factor has just the degree
given by the corresponding simple coroot. A negative pairing kills the
whole returning contribution. -/
private theorem trace_of_weight_blocks (α : J → W) (hα : LinearIndependent ℤ α)
    (wt : B → W) (M : J → Matrix B B (MvPolynomial J k)) (hM : RootSteps α wt M)
    (A : J → Matrix B B k) (q : W → J → ℤ) (l : List J) (hl : l.Nodup)
    (hcover : ∀ i, i ∈ l)
    (hblock : ∀ μ i, weightBlock wt μ (M i) =
      if 0 ≤ q μ i then (X i : MvPolynomial J k) ^ (q μ i).toNat • (weightBlock wt μ (A i)).map C else 0)
    (a : B) :
    (l.map M).prod a a =
      if ∀ i, 0 ≤ q (wt a) i then
        monomial (Finsupp.indicator Finset.univ fun i _ ↦ (q (wt a) i).toNat)
          ((l.map fun i ↦ weightBlock wt (wt a) (A i)).prod a a)
      else 0 := by
  classical
  rw [product_weightBlock α hα wt M hM l hl a a rfl rfl]
  by_cases h : ∀ i, 0 ≤ q (wt a) i
  · rw [ite_eq_left h]
    simp_rw [hblock, ite_eq_left (h _)]
    rw [list_prod_smul]
    have hset : l.toFinset = Finset.univ := by
      ext i
      simp [hcover i]
    rw [← List.prod_toFinset _ hl, hset, prod_X_pow]
    let F : Matrix B B k →+* Matrix B B (MvPolynomial J k) := (C : k →+* _).mapMatrix
    have hmap : (l.map fun i ↦ (weightBlock wt (wt a) (A i)).map C).prod =
        F ((l.map fun i ↦ weightBlock wt (wt a) (A i)).prod) := by
      rw [map_list_prod, List.map_map]
      rfl
    rw [hmap]
    rw [Matrix.smul_apply, smul_eq_mul]
    simp only [F, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [mul_comm, C_mul_monomial, mul_one]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : weightBlock wt (wt a) (M i) = 0 := by simp [hblock, not_le.mpr hi]
    have he : (l.map fun j ↦ weightBlock wt (wt a) (M j)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨i, hcover i, hz⟩)
    rw [he]
    rfl

private theorem trace_polynomial_of_weight_blocks
    (α : J → W) (hα : LinearIndependent ℤ α) (wt : B → W)
    (M : J → Matrix B B (MvPolynomial J k)) (hM : RootSteps α wt M)
    (A : J → Matrix B B k) (q : W → J → ℤ) (l : List J) (hl : l.Nodup)
    (hcover : ∀ i, i ∈ l)
    (hblock : ∀ μ i, weightBlock wt μ (M i) =
      if 0 ≤ q μ i then (X i : MvPolynomial J k) ^ (q μ i).toNat • (weightBlock wt μ (A i)).map C else 0)
    (a₀ : B) (j : J)
    (hfund : ∀ i, q (wt a₀) i = if i = j then 1 else 0)
    (hd : (l.map fun i ↦ weightBlock wt (wt a₀) (A i)).prod a₀ a₀ ≠ 0)
    (H : J → ℤ)
    (hlower : ∀ a ≠ a₀, (∀ i, 0 ≤ q (wt a) i) → ∀ i, 0 < q (wt a) i → H i < H j) :
    ∃ (d : k) (p : MvPolynomial J k), d ≠ 0 ∧
      (∀ m ∈ p.support, ∀ i ∈ m.support, H i < H j) ∧
      Matrix.trace (l.map M).prod = C d * X j + p := by
  classical
  let d := (l.map fun i ↦ weightBlock wt (wt a₀) (A i)).prod a₀ a₀
  let m (a : B) : J →₀ ℕ := Finsupp.indicator Finset.univ fun i _ ↦ (q (wt a) i).toNat
  let c (a : B) := (l.map fun i ↦ weightBlock wt (wt a) (A i)).prod a a
  let S := (Finset.univ.erase a₀).filter (fun a ↦ ∀ i, 0 ≤ q (wt a) i)
  let p := ∑ a ∈ S, monomial (m a) (c a)
  refine ⟨d, p, hd, ?_, ?_⟩
  · intro v hv i hi
    have hv' := support_sum hv
    obtain ⟨a, ha, hmem⟩ := Finset.mem_biUnion.mp hv'
    have hma : v = m a := Finset.mem_singleton.mp (support_monomial_subset hmem)
    have he := Finset.mem_filter.mp ha
    apply hlower a (Finset.mem_erase.mp he.1).1 he.2 i
    have hne : m a i ≠ 0 := Finsupp.mem_support_iff.mp (hma ▸ hi)
    have hi' : m a i = (q (wt a) i).toNat := by simp [m, Finsupp.indicator_apply]
    omega
  · have h0 : ∀ i, 0 ≤ q (wt a₀) i := by intro i; by_cases h : i = j <;> simp [hfund, h]
    have hm : m a₀ = Finsupp.single j 1 := by
      ext i
      by_cases h : i = j
      · subst i; simp [m, Finsupp.indicator_apply, hfund]
      · simp [m, Finsupp.indicator_apply, hfund, h]
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a₀)]
    simp_rw [trace_of_weight_blocks α hα wt M hM A q l hl hcover hblock]
    rw [ite_eq_left h0, ← Finset.sum_filter]
    change p + monomial (m a₀) d = _
    rw [hm, ← C_mul_X_eq_monomial, add_comm]

end TracePolynomial

open private regular_positive_system_of_attached from LinearAlgebraicGroups.Classification.NormalizerComparison
open private sum_coroot_pairing positive_flip eval_pos_root_nonneg from LinearAlgebraicGroups.Representation.DominantOrder

section AttachedLattice

open CategoryTheory
open scoped CategoryTheory.MonObj
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.SimplyConnectedLattice (corootLattice)

universe u
variable {k : Type u} [Field k] {L : AdditiveLine k} {P : PinnedGroup L} {r : ℕ}

private def simpleIndex (D : AttachedDatum P.pair) (e : Fin r ≃ SimpleRoot P.pair) :
    letI := D.comm
    D.base.support ≃ Fin r :=
  letI := D.comm
  (Equiv.subtypeEquivRight fun α ↦ D.simple_iff α).trans e.symm

private theorem fundamentalCoordinates (D : AttachedDatum P.pair)
    (e : Fin r ≃ SimpleRoot P.pair) (hspan : corootLattice D = ⊤) :
    letI := D.comm
    ∃ F : Additive (Character P.pair.T.group) ≃ₗ[ℤ] (Fin r → ℤ),
      ∀ χ i, F χ i = D.datum.rootDatum.toLinearMap χ (D.datum.rootDatum.coroot (e i).val) := by
  classical
  letI := D.comm
  let C := D.datum.rootDatum
  have hgen : Submodule.span ℤ (Set.range fun i : D.base.support ↦ C.coroot i.val) = ⊤ := by
    change Submodule.span ℤ (Set.range fun i : (↑D.base.support : Set _) ↦ C.coroot i.val) = ⊤
    rw [← Set.image_eq_range, D.base.span_int_coroot_support]
    exact hspan
  let b : Module.Basis D.base.support ℤ (Additive (Specs.CharacterDescent.Cocharacter P.pair.T.group)) :=
    Module.Basis.mk D.base.linearIndepOn_coroot (ge_of_eq hgen)
  let E := simpleIndex D e
  refine ⟨(C.toLinearMap.toPerfPair.trans b.dualBasis.equivFun).trans
    (LinearEquiv.funCongrLeft ℤ ℤ E.symm), ?_⟩
  intro χ i
  change b.dualBasis.equivFun (C.toLinearMap χ) (E.symm i) = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  change C.toLinearMap χ (b (E.symm i)) = _
  have hb (a : D.base.support) : b a = C.coroot a.val := Module.Basis.mk_apply _ _ _
  rw [hb]
  rfl

private theorem positiveSystem_isBaseFor (D : AttachedDatum P.pair) :
    letI := D.comm
    Specs.DominantOrder.IsBaseFor D.datum.rootDatum (subgroupRoots P.pair.T P.pair.B) D.base := by
  letI := D.comm
  obtain ⟨c, _, hc, hb⟩ := regular_positive_system_of_attached P.pair D
  intro α
  rw [← hc]
  exact (hb.positive_iff α).trans (by
    change 0 < D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root α) (Additive.ofMul c) ↔ _
    rw [D.datum.root_eq, D.datum.pairing_eq]
    rfl)

private def heightLinear (D : AttachedDatum P.pair) :
    Additive (Character P.pair.T.group) →ₗ[ℤ] ℤ :=
  letI := D.comm
  letI := D.datum.finiteRoots
  D.datum.rootDatum.toLinearMap.flip
    (Specs.DominantOrder.twoRhoCoroot D.datum.rootDatum (subgroupRoots P.pair.T P.pair.B))

private theorem height_simple (D : AttachedDatum P.pair) (α : SimpleRoot P.pair) :
    heightLinear D (Additive.ofMul α.val.val) = 2 := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCocharacters
  letI := D.datum.reduced
  letI := D.datum.reducedCoroots
  change D.datum.rootDatum.toLinearMap (Additive.ofMul α.val.val)
    (Specs.DominantOrder.twoRhoCoroot _ _) = _
  rw [← D.datum.root_eq]
  exact sum_coroot_pairing _ D.base (positiveSystem_isBaseFor D) ((D.simple_iff _).mpr α.property)

private theorem height_fundamental_pos (D : AttachedDatum P.pair)
    (e : Fin r ≃ SimpleRoot P.pair) (ω : Fin r → Character P.pair.T.group)
    (hω : IsFundamental D e ω) (j : Fin r) : 0 < height D (ω j) := by
  classical
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  letI := D.datum.reducedCoroots
  letI : Fintype (Specs.AbstractPairing.Root P.pair.T) := Fintype.ofFinite _
  let C := D.datum.rootDatum
  let S := subgroupRoots P.pair.T P.pair.B
  let f := C.toLinearMap (Additive.ofMul (ω j))
  have hnonneg (α : Specs.AbstractPairing.Root P.pair.T) (hα : α ∈ S) :
      0 ≤ f (C.coroot α) := by
    apply eval_pos_root_nonneg C.flip D.base.flip f
    · intro β hβ
      let i := e.symm ⟨β, (D.simple_iff _).mp hβ⟩
      have he : (e i).val = β := congrArg Subtype.val (e.apply_symm_apply _)
      change 0 ≤ f (C.coroot β)
      rw [← he]
      change 0 ≤ C.toLinearMap (Additive.ofMul (ω j)) (C.coroot (e i).val)
      rw [hω i j]
      split <;> omega
    · exact (positive_flip C D.base α).mpr ((positiveSystem_isBaseFor D α).mpr hα)
  change f (∑ α ∈ Finset.univ.filter (· ∈ S), C.coroot α) > 0
  rw [map_sum]
  refine Finset.sum_pos' (fun α hα ↦ hnonneg α (Finset.mem_filter.mp hα).2) ?_
  refine ⟨(e j).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e j).property.1⟩, ?_⟩
  change 0 < C.toLinearMap (Additive.ofMul (ω j)) (C.coroot (e j).val)
  rw [hω j j]
  simp

private theorem height_strict_of_dominance (D : AttachedDatum P.pair)
    {χ ψ : Character P.pair.T.group} (hneq : χ ≠ ψ)
    (hdom : Specs.RootWeightAction.DominanceLE P.pair.T P.pair.B χ ψ) :
    height D χ < height D ψ := by
  classical
  obtain ⟨c, hc⟩ := hdom
  have hcn : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro he
    apply hneq
    rw [he, Finsupp.sum_zero_index] at hc
    exact (div_eq_one.mp (show ψ / χ = 1 from hc)).symm
  have hf := congrArg (heightLinear D) hc
  change heightLinear D (Additive.ofMul ψ - Additive.ofMul χ) = _ at hf
  rw [map_sub] at hf
  change height D ψ - height D χ = _ at hf
  unfold Finsupp.sum at hf
  have hpair (i : Specs.RootWeightAction.SimpleRoot P.pair.T P.pair.B) :
      heightLinear D (Additive.ofMul i.val.val) = 2 := height_simple D i
  simp only [map_sum, map_nsmul, hpair] at hf
  have hp : 0 < ∑ i ∈ c.support, c i • (2 : ℤ) := by
    obtain ⟨i, hi⟩ := hcn
    refine Finset.sum_pos' (fun i _ ↦ by positivity) ⟨i, hi, ?_⟩
    have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    positivity
  omega

open AlgebraicGeometry
open Specs.GeometricRadicals (IsSemisimple IsUnipotentRadical)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

private theorem corootLattice_eq_top (D : AttachedDatum P.pair) (hG : IsSemisimple P.pair.G)
    (hsc : GeometricallySimplyConnected P.pair.G) : corootLattice D = ⊤ := by
  letI := D.comm
  exact (Classification.SimplyConnectedLattice.latticeCriterion P.pair.G hG
    P.pair.T P.pair.split P.pair.maximal D.datum).mp hsc

private theorem oppositePair (P : PinnedGroup L) :
    ∃ Q : OppositeBorelPair P.pair.G, Q.torus = P.pair.T ∧ Q.positive = P.pair.B := by
  obtain ⟨comm, _, _, corr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.pair.G P.pair.reductive
      P.pair.T P.pair.split P.pair.maximal
  letI := comm
  obtain ⟨f, hf, hfS⟩ := corr.1 P.pair.B P.pair.borel P.pair.containsTorus
  have hneg : Specs.BorelsAndChambers.IsPositiveSystem P.pair.T
      (subgroupRoots P.pair.T P.pair.B)ᶜ := by
    refine ⟨-f, fun α ↦ by simpa using hf α, ?_⟩
    rw [hfS]
    ext α
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, LinearMap.neg_apply]
    exact ⟨fun h ↦ neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) (hf α)),
      fun h ↦ not_lt_of_ge (neg_pos.mp h).le⟩
  obtain ⟨Bneg, hBneg, hTneg, hOpp⟩ := corr.2.1 _ hneg
  exact ⟨⟨P.pair.T, P.pair.B, Bneg, P.pair.reductive, P.pair.split, P.pair.maximal,
    P.pair.borel, hBneg, P.pair.containsTorus, hTneg, hOpp⟩, rfl, rfl⟩

theorem fundamentalModulesExist : FundamentalModulesExist.{u} := by
  classical
  intro k _ L P hG hsc D r e U hU
  letI := D.comm
  obtain ⟨F, hF⟩ := fundamentalCoordinates D e (corootLattice_eq_top D hG hsc)
  refine ⟨fun j ↦ Additive.toMul (F.symm (fun i ↦ if i = j then 1 else 0)), ?_, ?_⟩
  · intro i j
    exact (hF _ _).symm.trans (congrFun (F.apply_symm_apply _) i)
  · intro ω hω j
    have hdom : Specs.RootWeightAction.IsDominant D.datum P.pair.B (ω j) := by
      intro α
      obtain ⟨i, rfl⟩ := e.surjective (show SimpleRoot P.pair from α)
      rw [hω i j]
      split <;> omega
    obtain ⟨Q, hT, hB⟩ := oppositePair P
    cases Q with
    | mk T B Bneg red split maximal borel borelNeg inB inBneg opposite =>
      dsimp only at hT hB
      subst T
      subst B
      let Q : OppositeBorelPair P.pair.G :=
        ⟨P.pair.T, P.pair.B, Bneg, red, split, maximal, borel, borelNeg, inB, inBneg, opposite⟩
      have hdom' : Specs.InducedNonvanishing.Dominant Q (ω j) :=
        (Representation.InducedNonvanishing.dominant_iff_datum
          Classification.CentralIsogenies.centralIsogenyComparison Q D.datum (ω j)).mpr hdom
      obtain ⟨S, _⟩ := (Representation.SimpleClassification.classification
        P.pair.G Q U hU).2.2 (ω j) hdom'
      exact ⟨⟨S.J, S.socleAction, S.simple, ⟨_, S.primitive⟩⟩⟩

end AttachedLattice

section WeightBasis

open CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj DirectSum
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.RootWeightAction (Representation weightSpace act actLinear extendVector)
open Specs.GeometricRadicals (IsSplitTorus)

open private torusPoint_weights charactersOfIso from LinearAlgebraicGroups.Representation.RootWeightAction

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {G : AffineAlgebraicGroup k}

private theorem internalWeightSpaces (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) :
    letI : DecidableEq (Character T.group) := Classical.decEq _
    DirectSum.IsInternal (weightSpace ρ T) := by
  classical
  obtain ⟨n, ⟨iT⟩⟩ := hT
  obtain ⟨iA⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  let i := iA ≪≫ iT.symm
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) n
  obtain ⟨c, hc⟩ := torusPoint_weights ρ i χ hχ
  letI : DecidableEq (StandardLattice.{u} n) := Classical.decEq _
  let E := χ.toEquiv.trans (charactersOfIso i)
  have he : (weightSpace ρ T) ∘ E = LinearAlgebraicGroups.WeightDecomposition.weightSpace c :=
    funext hc
  have hh := LinearAlgebraicGroups.WeightDecomposition.weightDecomposition c
  have hi := DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    (LinearAlgebraicGroups.WeightDecomposition.weightSpace c)
  obtain ⟨hind, htop⟩ := hi.mp hh
  rw [← he] at hind htop
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact iSupIndep.comp' (f := E) hind E.surjective
  · simpa only [Function.comp_def, E.surjective.iSup_comp] using htop

/-- Coordinates of a vector in a single weight vanish in every other weight
in the chosen basis. -/
private theorem exists_weightBasis (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) :
    ∃ (b : Module.Basis I k (I → k)) (wt : I → Character T.group),
      (∀ i, b i ∈ weightSpace ρ T (wt i)) ∧
      ∀ (nu : Character T.group) (v : I → k), v ∈ weightSpace ρ T nu →
        ∀ i, wt i ≠ nu → b.repr v i = 0 := by
  classical
  let W := weightSpace ρ T
  let h := internalWeightSpaces ρ T hT
  let d (nu : Character T.group) := Module.Free.chooseBasis k (W nu)
  let B := h.collectedBasis d
  let E := (Pi.basisFun k I).indexEquiv B
  refine ⟨B.reindex E.symm, fun i ↦ (E i).1, ?_, ?_⟩
  · intro i
    simp [B]
  · intro nu v hv i hne
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm]
    exact h.collectedBasis_repr_of_mem_ne d hne.symm hv

private def basisMatrix (b : Module.Basis I k (I → k)) : (Matrix I I k)ˣ where
  val := (Pi.basisFun k I).toMatrix b
  inv := b.toMatrix (Pi.basisFun k I)
  val_inv := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Module.Basis.toMatrix_mul_toMatrix_flip _ _

private def matrixInBasis (b : Module.Basis I k (I → k)) (ρ : Representation G.val I)
    (R : TestAlgebra k) : GroupPoints G.val R →* Matrix I I R :=
  let S := Units.map ((algebraMap k R).mapMatrix.toMonoidHom) (basisMatrix b)
  let val : (Matrix I I R)ˣ →* Matrix I I R := ⟨⟨Units.val, rfl⟩, fun _ _ ↦ rfl⟩
  val.comp ((MulAut.conj S⁻¹).toMonoidHom.comp (ρ.app R).hom)

private theorem matrixInBasis_formula (b : Module.Basis I k (I → k)) (ρ : Representation G.val I)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    matrixInBasis b ρ R g =
      (b.toMatrix (Pi.basisFun k I)).map (algebraMap k R) * (ρ.app R g).val *
        ((Pi.basisFun k I).toMatrix b).map (algebraMap k R) := by
  rfl

private theorem matrixInBasis_trace (b : Module.Basis I k (I → k)) (ρ : Representation G.val I)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    Matrix.trace (matrixInBasis b ρ R g) = Matrix.trace (ρ.app R g).val := by
  rw [matrixInBasis_formula, Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.map_mul,
    Module.Basis.toMatrix_mul_toMatrix_flip]
  change Matrix.trace (((algebraMap k R).mapMatrix (1 : Matrix I I k)) * (ρ.app R g).val) = _
  rw [map_one, one_mul]

private theorem matrixInBasis_natural (b : Module.Basis I k (I → k))
    (ρ : Representation G.val I) {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints G.val R) :
    (a.hom.toRingHom.mapMatrix (matrixInBasis b ρ R g)) = matrixInBasis b ρ S (mapPoints a g) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
  have hm := congrArg (fun v : Matrix.GeneralLinearGroup I S ↦ v.val) h.symm
  change a.hom.toRingHom.mapMatrix (ρ.app R g).val = (ρ.app S (mapPoints a g)).val at hm
  have hmap (M : Matrix I I k) :
      a.hom.toRingHom.mapMatrix (M.map (algebraMap k R)) = M.map (algebraMap k S) := by
    ext i j
    exact a.hom.commutes (M i j)
  rw [matrixInBasis_formula b ρ R g]
  simp only [map_mul, hm, hmap]
  exact (matrixInBasis_formula b ρ S (mapPoints a g)).symm

private theorem matrixInBasis_entry (b : Module.Basis I k (I → k)) (ρ : Representation G.val I)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (a c : I) :
    matrixInBasis b ρ R g a c =
      ∑ l, algebraMap k R (b.repr (Pi.basisFun k I l) a) *
        act ρ R g (extendVector R (b c)) l := by
  rw [matrixInBasis_formula, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
    Matrix.mulVec, act, dotProduct, extendVector]
  rfl

end WeightBasis

section RootFactors

open private act_mul act_one act_smul rootOrbit rootPoint_natural characterValue_comp
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private act_rational from LinearAlgebraicGroups.Representation.CyclicHighestWeight

open CategoryTheory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue pairing)
open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot)
open Specs.NormalizerComparison (SimpleRepresentative)
open Specs.RootGroups (AdditiveLine rootPoint rankOneWord CorootReflection)
open Specs.RootWeightAction (Representation act actLinear extendVector weightSpace mem_weightSpace)

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {L : AdditiveLine k} {P : PinnedGroup L}
variable [IsCommMonObj P.pair.T.group.X]
variable {D : AttachedDatum P.pair} {i : SimpleRoot P.pair}

private abbrev positiveCoordinate (P : PinnedGroup L) (i : SimpleRoot P.pair) :=
  (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion

private abbrev negativeCoordinate (n : SimpleRepresentative P D i) :=
  n.negative.val.hom ≫ (P.roots n.opposite).val.inclusion

private abbrev representativePoint (n : SimpleRepresentative P D i) (R : TestAlgebra k) :
    GroupPoints P.pair.G.val R := toUnit _ ≫ n.reflection.representative

private abbrev ground (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev polynomialAlgebra (k : Type u) [Field k] := CommAlgCat.of k (Polynomial k)

private def simplePairing (D : AttachedDatum P.pair) (χ : Character P.pair.T.group)
    (i : SimpleRoot P.pair) : ℤ :=
  D.datum.rootDatum.toLinearMap (Additive.ofMul χ) (D.datum.rootDatum.coroot i.val)

omit [IsCommMonObj P.pair.T.group.X] in
private theorem representative_pairing (n : SimpleRepresentative P D i)
    (χ : Character P.pair.T.group) :
    pairing P.pair.T.group χ n.reflection.coroot = simplePairing D χ i := by
  letI := D.comm
  rw [n.coroot_eq]
  exact (D.datum.pairing_eq χ _).symm

private def reflectedCharacter (n : SimpleRepresentative P D i)
    (χ : Character P.pair.T.group) : Character P.pair.T.group :=
  n.reflection.conjugation.inv ≫ χ

omit [IsCommMonObj P.pair.T.group.X] in
private theorem reflectedCharacter_eq (n : SimpleRepresentative P D i)
    (χ : Character P.pair.T.group) :
    Additive.ofMul (reflectedCharacter n χ) =
      Additive.ofMul χ - simplePairing D χ i • Additive.ofMul i.val.val := by
  rw [reflectedCharacter, n.reflection.reflection, representative_pairing n,
    ofMul_mul, ofMul_zpow, neg_smul, sub_eq_add_neg]

omit [IsCommMonObj P.pair.T.group.X] in
private theorem representative_smul_weight (ρ : Representation P.pair.G.val I)
    (n : SimpleRepresentative P D i) {χ : Character P.pair.T.group} {v : I → k}
    (hv : v ∈ weightSpace ρ P.pair.T χ) :
    act ρ (ground k) (representativePoint n (ground k)) v ∈
      weightSpace ρ P.pair.T (reflectedCharacter n χ) := by
  apply mem_weightSpace.mpr
  intro R t
  let t' : GroupPoints P.pair.T.group R := t ≫ n.reflection.conjugation.inv.hom.hom
  let nt := representativePoint n R
  let q : GroupPoints P.pair.G.val R := t ≫ P.pair.T.inclusion.hom.hom
  let q' : GroupPoints P.pair.G.val R := t' ≫ P.pair.T.inclusion.hom.hom
  have hpoint : q = nt * q' * nt⁻¹ := by
    have h := congrArg (fun z : P.pair.T.group.X ⟶ P.pair.G.val.X ↦ t' ≫ z)
      n.reflection.conjugates
    have hcomp : n.reflection.conjugation.inv.hom.hom ≫
        n.reflection.conjugation.hom.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map n.reflection.conjugation.inv_hom_id
    have hleft : t' ≫ (n.reflection.conjugation.hom ≫ P.pair.T.inclusion).hom.hom = q := by
      change (t ≫ n.reflection.conjugation.inv.hom.hom) ≫
        n.reflection.conjugation.hom.hom.hom ≫ P.pair.T.inclusion.hom.hom = _
      rw [Category.assoc t, ← Category.assoc n.reflection.conjugation.inv.hom.hom,
        hcomp, Category.id_comp]
    rw [hleft, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv] at h
    simp only [comp_toUnit_assoc] at h
    exact h
  have hcomm : q * nt = nt * q' := by
    rw [hpoint, mul_assoc, inv_mul_cancel, mul_one]
  change act ρ R q (extendVector R (act ρ (ground k) (representativePoint n (ground k)) v)) =
    characterValue (reflectedCharacter n χ) R t •
      extendVector R (act ρ (ground k) (representativePoint n (ground k)) v)
  have hact : act ρ R nt (extendVector R v) =
      extendVector R (act ρ (ground k) (representativePoint n (ground k)) v) :=
    act_rational ρ n.reflection.representative R v
  have ht := mem_weightSpace.mp hv R t'
  change act ρ R q' (extendVector R v) = characterValue χ R t' • extendVector R v at ht
  have hc : characterValue (reflectedCharacter n χ) R t = characterValue χ R t' :=
    characterValue_comp n.reflection.conjugation.inv χ R t
  rw [← hact, ← act_mul ρ R q nt, hcomm, act_mul ρ R nt q', ht, act_smul, hc]

omit [IsCommMonObj P.pair.T.group.X] in
private theorem representative_act_injective (ρ : Representation P.pair.G.val I)
    (n : SimpleRepresentative P D i) :
    Function.Injective (act ρ (ground k) (representativePoint n (ground k))) := by
  let g := representativePoint n (ground k)
  intro v w h
  have he := congrArg (act ρ (ground k) g⁻¹) h
  change act ρ (ground k) g⁻¹ (act ρ (ground k) g v) =
    act ρ (ground k) g⁻¹ (act ρ (ground k) g w) at he
  simpa only [← act_mul, inv_mul_cancel, act_one] using he

private def orbitPolynomial {H : GroupScheme k} (ρ : Representation H I)
    (x : L.group ⟶ H) (v : I → k) : I → Polynomial k :=
  act ρ (polynomialAlgebra k) (rootPoint x (polynomialAlgebra k) Polynomial.X)
    (extendVector (polynomialAlgebra k) v)

omit [IsCommMonObj P.pair.T.group.X] in
private theorem orbitPolynomial_data (ρ : Representation P.pair.G.val I)
    (α : Specs.AbstractPairing.Root P.pair.T) (χ : Character P.pair.T.group)
    (x : Specs.Pinning.RootCoordinate L P.pair.T (P.roots α).val α.val)
    (v : I → k) (hv : v ∈ weightSpace ρ P.pair.T χ) :
    let p := orbitPolynomial ρ (x.val.hom ≫ (P.roots α).val.inclusion) v
    (fun a ↦ (p a).coeff 0) = v ∧
    (∀ m : ℕ, (fun a ↦ (p a).coeff m) ∈ weightSpace ρ P.pair.T (χ * α.val ^ m)) ∧
    ∀ (R : TestAlgebra k) (c : R),
      act ρ R (rootPoint (x.val.hom ≫ (P.roots α).val.inclusion) R c) (extendVector R v) =
        fun a ↦ Polynomial.aeval c (p a) := by
  obtain ⟨p, h0, hm, he⟩ := rootOrbit ρ P.pair.T α (P.roots α).val (P.roots α).property
    L x.val x.property χ ⟨v, hv⟩
  have hp : orbitPolynomial ρ (x.val.hom ≫ (P.roots α).val.inclusion) v = p := by
    exact (he (polynomialAlgebra k) Polynomial.X).trans (funext fun j ↦
      Polynomial.aeval_X_left_apply _)
  dsimp only
  rw [hp]
  refine ⟨h0, ?_, he⟩
  intro m
  by_cases hz : m = 0
  · subst m
    simpa [h0] using hv
  · exact hm m (Nat.pos_of_ne_zero hz)

private def factorPolynomial (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (n : SimpleRepresentative P D i) :
    Matrix I I (Polynomial k) :=
  let R := polynomialAlgebra k
  matrixInBasis b ρ R (rootPoint (positiveCoordinate P i) R Polynomial.X * representativePoint n R)

private theorem factorPolynomial_coefficient (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (n : SimpleRepresentative P D i) (a c : I) (m : ℕ) :
    (factorPolynomial ρ b n a c).coeff m =
      b.repr (fun l ↦
        (orbitPolynomial ρ (positiveCoordinate P i)
          (act ρ (ground k) (representativePoint n (ground k)) (b c)) l).coeff m) a := by
  let R := polynomialAlgebra k
  let g := rootPoint (positiveCoordinate P i) R Polynomial.X
  let nR := representativePoint n R
  let w := act ρ (ground k) (representativePoint n (ground k)) (b c)
  change (matrixInBasis b ρ R (g * nR) a c).coeff m = _
  rw [matrixInBasis_entry, act_mul ρ R g nR]
  have hw : act ρ R nR (extendVector R (b c)) = extendVector R w :=
    act_rational ρ n.reflection.representative R (b c)
  rw [hw]
  change (∑ l, Polynomial.C (b.repr (Pi.basisFun k I l) a) *
    orbitPolynomial ρ (positiveCoordinate P i) w l).coeff m = _
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  let z : I → k := fun l ↦ (orbitPolynomial ρ (positiveCoordinate P i) w l).coeff m
  have hz := b.sum_repr_mul_repr (Pi.basisFun k I) z a
  simpa only [Pi.basisFun_repr] using hz

private theorem factorPolynomial_route (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (wt : I → Character P.pair.T.group)
    (hw : ∀ i, b i ∈ weightSpace ρ P.pair.T (wt i))
    (hb : ∀ χ (v : I → k), v ∈ weightSpace ρ P.pair.T χ →
      ∀ i, wt i ≠ χ → b.repr v i = 0)
    (n : SimpleRepresentative P D i) (a c : I) (m : ℕ)
    (hm : (factorPolynomial ρ b n a c).coeff m ≠ 0) :
    Additive.ofMul (wt a) - Additive.ofMul (wt c) =
      ((m : ℤ) - simplePairing D (wt c) i) • Additive.ofMul i.val.val := by
  let w := act ρ (ground k) (representativePoint n (ground k)) (b c)
  have hw' := representative_smul_weight ρ n (hw c)
  have hcoeff := (orbitPolynomial_data ρ i.val (reflectedCharacter n (wt c))
    (P.pin i) w hw').2.1 m
  have he : wt a = reflectedCharacter n (wt c) * i.val.val ^ m := by
    by_contra hn
    exact hm ((factorPolynomial_coefficient ρ b n a c m).trans (hb _ _ hcoeff a hn))
  rw [he, ofMul_mul, ofMul_pow, reflectedCharacter_eq, sub_smul]
  simp only [natCast_zsmul]
  abel

omit [IsCommMonObj P.pair.T.group.X] in
private theorem simplePairing_root (n : SimpleRepresentative P D i) :
    simplePairing D i.val.val i = 2 :=
  (representative_pairing n _).symm.trans n.reflection.root_pairing

private theorem negativeOrbit_degree (ρ : Representation P.pair.G.val I)
    {χ : Character P.pair.T.group} {v : I → k}
    (hv : v ∈ weightSpace ρ P.pair.T χ)
    (habove : ∀ ν, height D χ < height D ν → weightSpace ρ P.pair.T ν = ⊥)
    (n : SimpleRepresentative P D i) (m : ℕ)
    (hm : simplePairing D χ i < m) :
    (fun a ↦ (orbitPolynomial ρ (negativeCoordinate n) v a).coeff m) = 0 := by
  let ν := χ * n.opposite.val ^ m
  let w := fun a ↦ (orbitPolynomial ρ (negativeCoordinate n) v a).coeff m
  have hw : w ∈ weightSpace ρ P.pair.T ν :=
    (orbitPolynomial_data ρ n.opposite χ n.negative v hv).2.1 m
  have hneg : Additive.ofMul ν =
      Additive.ofMul χ - (m : ℤ) • Additive.ofMul i.val.val := by
    simp only [ν, n.opposite_eq, ofMul_mul, ofMul_pow, ofMul_inv, smul_neg,
      natCast_zsmul, sub_eq_add_neg]
  let f := D.datum.rootDatum.toLinearMap.flip (D.datum.rootDatum.coroot i.val)
  have hf : simplePairing D ν i = simplePairing D χ i - (m : ℤ) * 2 := by
    change f (Additive.ofMul ν) = f (Additive.ofMul χ) - _
    rw [hneg, map_sub, map_zsmul]
    change _ - (m : ℤ) • simplePairing D i.val.val i = _
    rw [simplePairing_root n, zsmul_eq_mul, Int.cast_id]
  have hheight : height D χ < height D (reflectedCharacter n ν) := by
    change heightLinear D (Additive.ofMul χ) <
      heightLinear D (Additive.ofMul (reflectedCharacter n ν))
    rw [reflectedCharacter_eq, hneg, map_sub, map_sub, map_zsmul, map_zsmul, height_simple D i, hf]
    simp only [zsmul_eq_mul, Int.cast_id]
    omega
  have hz := representative_smul_weight ρ n hw
  rw [habove _ hheight, Submodule.mem_bot] at hz
  apply representative_act_injective ρ n
  exact hz.trans ((actLinear ρ (ground k) (representativePoint n (ground k))).map_zero).symm

omit [IsCommMonObj P.pair.T.group.X] in
private theorem positiveOrbit_degree (ρ : Representation P.pair.G.val I)
    {χ ν : Character P.pair.T.group} {v : I → k}
    (hv : v ∈ weightSpace ρ P.pair.T ν)
    (habove : ∀ ψ, height D χ < height D ψ → weightSpace ρ P.pair.T ψ = ⊥)
    (q : ℤ) (hν : Additive.ofMul ν =
      Additive.ofMul χ - q • Additive.ofMul i.val.val)
    (m : ℕ) (hm : q < m) :
    (fun a ↦ (orbitPolynomial ρ (positiveCoordinate P i) v a).coeff m) = 0 := by
  have hw := (orbitPolynomial_data ρ i.val ν (P.pin i) v hv).2.1 m
  have hheight : height D χ < height D (ν * i.val.val ^ m) := by
    change heightLinear D (Additive.ofMul χ) <
      heightLinear D (Additive.ofMul (ν * i.val.val ^ m))
    rw [ofMul_mul, ofMul_pow, ← natCast_zsmul, hν, map_add, map_sub, map_zsmul, map_zsmul,
      height_simple D i]
    simp only [zsmul_eq_mul, Int.cast_id]
    omega
  rw [habove _ hheight, Submodule.mem_bot] at hw
  exact hw

private theorem polynomial_eq_constant {p : Polynomial k}
    (h : ∀ m : ℕ, 0 < m → p.coeff m = 0) : p = Polynomial.C (p.coeff 0) := by
  ext m
  obtain rfl | m := m
  · simp
  · simp [h (m + 1) (Nat.succ_pos _)]

private theorem polynomial_eq_linear {p : Polynomial k}
    (h : ∀ m : ℕ, 1 < m → p.coeff m = 0) :
    p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X := by
  ext m
  obtain _ | _ | m := m
  · simp
  · simp
  · simp [h (m + 2) (by omega)]

omit [Fintype I] [DecidableEq I] in
private theorem extendVector_ground (v : I → k) : extendVector (ground k) v = v := by
  funext a
  exact RingHom.id_apply _

omit [IsCommMonObj P.pair.T.group.X] in
private theorem rankOne_on_fixed_top (ρ : Representation P.pair.G.val I)
    (n : SimpleRepresentative P D i) (v : I → k)
    (hfix : act ρ (ground k) (rootPoint (positiveCoordinate P i) (ground k) 1) v = v) :
    act ρ (ground k) (representativePoint n (ground k)) v =
      act ρ (ground k) (rootPoint (positiveCoordinate P i) (ground k) 1)
        (act ρ (ground k) (rootPoint (negativeCoordinate n) (ground k) (-1)) v) := by
  change act ρ (ground k) (toUnit _ ≫ n.reflection.representative) v = _
  rw [n.reflection.representative_word]
  simp only [rankOneWord, Units.val_one, inv_one, act_mul, hfix]

/-- The highest weight has simple pairings zero and one. At a zero pairing
both root coordinates fix its vector. At a unit pairing the rank-one word
forces a nonzero linear raising coefficient. -/
private theorem leading_factor_nonzero (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (wt : I → Character P.pair.T.group)
    (hw : ∀ a, b a ∈ weightSpace ρ P.pair.T (wt a))
    (hb : ∀ ν (v : I → k), v ∈ weightSpace ρ P.pair.T ν →
      ∀ a, wt a ≠ ν → b.repr v a = 0)
    (n : SimpleRepresentative P D i) (a₀ : I)
    (hline : weightSpace ρ P.pair.T (wt a₀) = Submodule.span k {b a₀})
    (habove : ∀ ν, height D (wt a₀) < height D ν → weightSpace ρ P.pair.T ν = ⊥)
    (hq : simplePairing D (wt a₀) i = 0 ∨ simplePairing D (wt a₀) i = 1) :
    (factorPolynomial ρ b n a₀ a₀).coeff (simplePairing D (wt a₀) i).toNat ≠ 0 := by
  let χ := wt a₀
  let v := b a₀
  let K := ground k
  let w := act ρ K (representativePoint n K) v
  let pp := orbitPolynomial ρ (positiveCoordinate P i)
  let pn := orbitPolynomial ρ (negativeCoordinate n)
  have hp := orbitPolynomial_data ρ i.val χ (P.pin i) v (hw a₀)
  have hn := orbitPolynomial_data ρ n.opposite χ n.negative v (hw a₀)
  have hfix : act ρ K (rootPoint (positiveCoordinate P i) K 1) v = v := by
    have he := hp.2.2 K 1
    rw [extendVector_ground] at he
    refine he.trans (funext fun a ↦ ?_)
    change Polynomial.aeval (1 : k) (pp v a) = v a
    have hconst := polynomial_eq_constant (p := pp v a) fun m hm ↦ by
      have hz := positiveOrbit_degree ρ (D := D) (i := i) (hw a₀) habove 0
        (by rw [zero_smul, sub_zero]) m (by omega)
      exact congrFun hz a
    rw [hconst, congrFun hp.1 a, Polynomial.aeval_C]
    exact RingHom.id_apply _
  have hword := rankOne_on_fixed_top ρ n v hfix
  rcases hq with hq | hq
  · have hnfix : act ρ K (rootPoint (negativeCoordinate n) K (-1)) v = v := by
      have he := hn.2.2 K (-1)
      rw [extendVector_ground] at he
      refine he.trans (funext fun a ↦ ?_)
      change Polynomial.aeval (-1 : k) (pn v a) = v a
      have hconst := polynomial_eq_constant (p := pn v a) fun m hm ↦
        congrFun (negativeOrbit_degree ρ (hw a₀) habove n m (by omega)) a
      rw [hconst, congrFun hn.1 a, Polynomial.aeval_C]
      exact RingHom.id_apply _
    rw [hq, factorPolynomial_coefficient]
    change b.repr (fun l ↦ (pp w l).coeff 0) a₀ ≠ 0
    have hwv : w = v := by
      change w = act ρ K (rootPoint (positiveCoordinate P i) K 1)
        (act ρ K (rootPoint (negativeCoordinate n) K (-1)) v) at hword
      rw [hnfix, hfix] at hword
      exact hword
    rw [hwv, hp.1, Module.Basis.repr_self, Finsupp.single_eq_same]
    exact one_ne_zero
  · have hw' := representative_smul_weight ρ n (hw a₀)
    have hwData := orbitPolynomial_data ρ i.val (reflectedCharacter n χ) (P.pin i) w hw'
    have hwbelow : χ ≠ reflectedCharacter n χ := by
      intro he
      have hh := congrArg (heightLinear D ∘ Additive.ofMul) he
      change heightLinear D (Additive.ofMul χ) =
        heightLinear D (Additive.ofMul (reflectedCharacter n χ)) at hh
      rw [reflectedCharacter_eq, hq, one_smul, map_sub, height_simple D i] at hh
      omega
    rw [hq, factorPolynomial_coefficient]
    intro hz
    let z : I → k := fun a ↦ (pp w a).coeff 1
    have hz' : z ∈ weightSpace ρ P.pair.T χ := by
      have he : reflectedCharacter n χ * i.val.val ^ (1 : ℕ) = χ := by
        apply Additive.ofMul.injective
        rw [ofMul_mul, ofMul_pow, reflectedCharacter_eq, hq, one_smul, one_smul, sub_add_cancel]
      exact he ▸ hwData.2.1 1
    rw [hline, Submodule.mem_span_singleton] at hz'
    obtain ⟨c, hc⟩ := hz'
    have hc0 : c = 0 := by
      have he := congrArg (fun y ↦ b.repr y a₀) hc
      change b.repr (c • b a₀) a₀ = b.repr z a₀ at he
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one] at he
      exact he.trans hz
    have hz0 : z = 0 := by simpa [hc0] using hc.symm
    have hwfix : act ρ K (rootPoint (positiveCoordinate P i) K 1) w = w := by
      have he := hwData.2.2 K 1
      rw [extendVector_ground] at he
      refine he.trans (funext fun a ↦ ?_)
      change Polynomial.aeval (1 : k) (pp w a) = w a
      have hconst := polynomial_eq_constant (p := pp w a) fun m hm ↦ by
        by_cases h : m = 1
        · subst m
          exact congrFun hz0 a
        · exact congrFun (positiveOrbit_degree ρ hw' habove 1
            (by rw [reflectedCharacter_eq, hq]) m (by omega)) a
      rw [hconst, congrFun hwData.1 a, Polynomial.aeval_C]
      exact RingHom.id_apply _
    let g := rootPoint (positiveCoordinate P i) K 1
    let y := act ρ K (rootPoint (negativeCoordinate n) K (-1)) v
    have hyw : y = w := by
      have hh : act ρ K g y = act ρ K g w := hword.symm.trans hwfix.symm
      have hh' := congrArg (act ρ K g⁻¹) hh
      simpa only [← act_mul, inv_mul_cancel, act_one] using hh'
    let c : I → k := fun a ↦ (pn v a).coeff 1
    have hc : c ∈ weightSpace ρ P.pair.T (χ * n.opposite.val ^ (1 : ℕ)) := hn.2.1 1
    have hcne : χ ≠ χ * n.opposite.val ^ (1 : ℕ) := by
      intro he
      apply hwbelow
      apply Additive.ofMul.injective
      rw [reflectedCharacter_eq, hq, one_smul]
      conv_lhs => rw [he, ofMul_mul, ofMul_pow, n.opposite_eq, ofMul_inv, one_smul]
      rw [sub_eq_add_neg]
    have hy : y = v - c := by
      have he := hn.2.2 K (-1)
      rw [extendVector_ground] at he
      refine he.trans (funext fun a ↦ ?_)
      change Polynomial.aeval (-1 : k) (pn v a) = v a - c a
      have he' := polynomial_eq_linear (p := pn v a) fun m hm ↦
        congrFun (negativeOrbit_degree ρ (hw a₀) habove n m (by omega)) a
      rw [he', congrFun hn.1 a]
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply, c, mul_neg, mul_one, sub_eq_add_neg]
    have hcontra := congrArg (fun y ↦ b.repr y a₀) (hyw.symm.trans hy)
    rw [hb _ _ hw' a₀ hwbelow, map_sub, Finsupp.sub_apply,
      hb _ _ hc a₀ hcne, sub_zero] at hcontra
    change 0 = b.repr (b a₀) a₀ at hcontra
    rw [Module.Basis.repr_self, Finsupp.single_eq_same] at hcontra
    exact zero_ne_one hcontra

omit [IsCommMonObj P.pair.T.group.X] in
private theorem factorPolynomial_eval (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (n : SimpleRepresentative P D i)
    (R : TestAlgebra k) (t : R) :
    (Polynomial.aeval t).toRingHom.mapMatrix (factorPolynomial ρ b n) =
      matrixInBasis b ρ R (rootPoint (positiveCoordinate P i) R t * representativePoint n R) := by
  let Q := polynomialAlgebra k
  let f : Q ⟶ R := CommAlgCat.ofHom (Polynomial.aeval t)
  let g := rootPoint (positiveCoordinate P i) Q Polynomial.X
  let nQ := representativePoint n Q
  have hn : mapPoints f nQ = representativePoint n R := by
    simp [mapPoints, nQ, representativePoint]
  have hg : mapPoints f g = rootPoint (positiveCoordinate P i) R t := by
    rw [rootPoint_natural]
    change rootPoint _ _ (Polynomial.aeval t (Polynomial.X : Polynomial k)) = _
    rw [Polynomial.aeval_X]
  have hmap : mapPoints f (g * nQ) = mapPoints f g * mapPoints f nQ :=
    (((groupPointsFunctor k).obj P.pair.G.val).map f).hom.map_mul g nQ
  have h := matrixInBasis_natural b ρ f (g * nQ)
  rw [hmap, hg, hn] at h
  exact h

private theorem rootFactors_supported (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (wt : I → Character P.pair.T.group)
    (hw : ∀ i, b i ∈ weightSpace ρ P.pair.T (wt i))
    (hb : ∀ χ (v : I → k), v ∈ weightSpace ρ P.pair.T χ →
      ∀ i, wt i ≠ χ → b.repr v i = 0)
    {r : ℕ} (e : Fin r ≃ SimpleRoot P.pair) (n : ∀ i, SimpleRepresentative P D i) :
    RootSteps (R := MvPolynomial (Fin r) k) (fun i ↦ Additive.ofMul (e i).val.val)
      (fun a ↦ Additive.ofMul (wt a))
      (fun i ↦ (factorPolynomial ρ b (n (e i))).map
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin r) k))) := by
  intro i a c h
  have hp : factorPolynomial ρ b (n (e i)) a c ≠ 0 := by
    intro hz
    apply h
    change Polynomial.aeval _ (factorPolynomial ρ b (n (e i)) a c) = 0
    rw [hz, map_zero]
  obtain ⟨m, hm⟩ : ∃ m, (factorPolynomial ρ b (n (e i)) a c).coeff m ≠ 0 := by
    by_contra! hall
    exact hp (Polynomial.ext fun m ↦ (hall m).trans (Polynomial.coeff_zero _).symm)
  exact ⟨_, factorPolynomial_route ρ b wt hw hb (n (e i)) a c m hm⟩

private def factorCoefficientMatrix (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (wt : I → Character P.pair.T.group)
    (n : SimpleRepresentative P D i) : Matrix I I k :=
  fun a c ↦ (factorPolynomial ρ b n a c).coeff (simplePairing D (wt c) i).toNat

private theorem factorBlock (ρ : Representation P.pair.G.val I)
    (b : Module.Basis I k (I → k)) (wt : I → Character P.pair.T.group)
    (hw : ∀ i, b i ∈ weightSpace ρ P.pair.T (wt i))
    (hb : ∀ χ (v : I → k), v ∈ weightSpace ρ P.pair.T χ →
      ∀ i, wt i ≠ χ → b.repr v i = 0)
    (n : SimpleRepresentative P D i) (χ : Character P.pair.T.group)
    {J : Type*} (j : J) :
    weightBlock wt χ ((factorPolynomial ρ b n).map
      (Polynomial.aeval (MvPolynomial.X j : MvPolynomial J k))) =
      if 0 ≤ simplePairing D χ i then
        (MvPolynomial.X j : MvPolynomial J k) ^ (simplePairing D χ i).toNat •
          (weightBlock wt χ (factorCoefficientMatrix ρ b wt n)).map MvPolynomial.C
      else 0 := by
  classical
  apply Matrix.ext
  intro a c
  by_cases hac : wt a = χ ∧ wt c = χ
  · let p := factorPolynomial ρ b n a c
    let q := simplePairing D χ i
    have route (m : ℕ) (hm : p.coeff m ≠ 0) : (m : ℤ) = q := by
      have he := factorPolynomial_route ρ b wt hw hb n a c m hm
      rw [hac.1, hac.2, sub_self] at he
      have hh := congrArg (heightLinear D) he
      rw [map_zero, map_zsmul, height_simple D i, zsmul_eq_mul, Int.cast_id] at hh
      omega
    have hf : factorCoefficientMatrix ρ b wt n a c = p.coeff q.toNat := by
      change p.coeff (simplePairing D (wt c) i).toNat = _
      rw [hac.2]
    by_cases hq : 0 ≤ q
    · have he : p = Polynomial.C (p.coeff q.toNat) * Polynomial.X ^ q.toNat := by
        ext m
        rw [Polynomial.coeff_C_mul_X_pow]
        by_cases heq : m = q.toNat
        · simp [heq]
        · rw [ite_eq_right heq]
          by_contra hm
          exact heq (by have := route m hm; omega)
      rw [ite_eq_left hq]
      simp only [weightBlock, ite_eq_left hac, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hf]
      change Polynomial.aeval (MvPolynomial.X j : MvPolynomial J k) p = _
      conv_lhs => rw [he]
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        MvPolynomial.algebraMap_eq, mul_comm]
    · have he : p = 0 := Polynomial.ext fun m ↦ by
        rw [Polynomial.coeff_zero]
        by_contra hm
        have := route m hm
        omega
      rw [ite_eq_right hq]
      simp only [weightBlock, ite_eq_left hac, Matrix.map_apply, Matrix.zero_apply]
      change Polynomial.aeval (MvPolynomial.X j : MvPolynomial J k) p = 0
      rw [he, map_zero]
  · by_cases hq : 0 ≤ simplePairing D χ i <;>
      simp [hq, weightBlock, hac]

open private generates_of_simple from LinearAlgebraicGroups.Representation.PrimitiveLine
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

omit [IsCommMonObj P.pair.T.group.X] in
private theorem highestWeight_bound
    {U : ClosedSubgroup P.pair.B.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.pair.B) U)
    {χ : Character P.pair.T.group} (V : HighestWeightModule U χ) :
    ∃ v : V.I → k, v ≠ 0 ∧ v ∈ weightSpace V.action P.pair.T χ ∧
      weightSpace V.action P.pair.T χ = Submodule.span k {v} ∧
      ∀ ν, ν ≠ χ → weightSpace V.action P.pair.T ν ≠ ⊥ →
        Specs.RootWeightAction.DominanceLE P.pair.T P.pair.B ν χ := by
  obtain ⟨v, hv⟩ := V.primitive
  let G' : AffineGroupCategory k := ⟨P.pair.G.val, P.pair.G.property.1⟩
  let A := coordinateHopf G'
  let E : convolutionPoints A ≅ (groupPointsFunctor k).obj P.pair.G.val :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso
      ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G'))
  have hc := Representation.CyclicHighestWeight.cyclicHighestWeight
  have hg := generates_of_simple hc.1 V.action A E V.simple hv.1
  obtain ⟨comm, D', H⟩ := hc.2 P.pair.G P.pair.reductive P.pair.T P.pair.B
    P.pair.split P.pair.maximal P.pair.borel P.pair.containsTorus
  letI := comm
  obtain ⟨hl, hdom, _⟩ := (H U hU V.action χ v hv).2 hg
  exact ⟨v, hv.1, hv.2.2, hl, hdom⟩

omit [IsCommMonObj P.pair.T.group.X] in
private theorem topBasisIndex
    (ρ : Representation P.pair.G.val I) (b : Module.Basis I k (I → k))
    (wt : I → Character P.pair.T.group) (χ : Character P.pair.T.group)
    (hw : ∀ i, b i ∈ weightSpace ρ P.pair.T (wt i))
    (hb : ∀ χ (v : I → k), v ∈ weightSpace ρ P.pair.T χ →
      ∀ i, wt i ≠ χ → b.repr v i = 0)
    (v : I → k) (hv0 : v ≠ 0) (hv : v ∈ weightSpace ρ P.pair.T χ)
    (hl : weightSpace ρ P.pair.T χ = Submodule.span k {v}) :
    ∃ a₀ : I, wt a₀ = χ ∧ (∀ a, wt a = χ → a = a₀) ∧
      weightSpace ρ P.pair.T (wt a₀) = Submodule.span k {b a₀} := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a, wt a = χ := by
    by_contra! hn
    apply hv0
    apply b.repr.injective
    ext a
    simpa using hb χ v hv a (hn a)
  have hmem : b a₀ ∈ Submodule.span k {v} := by
    rw [← hl, ← ha₀]
    exact hw a₀
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by
    intro he
    exact b.ne_zero a₀ (by simpa [he] using hc.symm)
  have hs : weightSpace ρ P.pair.T χ = Submodule.span k {b a₀} := by
    rw [hl, ← hc, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0)]
  refine ⟨a₀, ha₀, ?_, by rw [ha₀, hs]⟩
  intro a ha
  by_contra hne
  have hmem := hw a
  rw [ha, hs, Submodule.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  have h := congrArg (fun y ↦ b.repr y a) hd
  change b.repr (d • b a₀) a = b.repr (b a) a at h
  simp [Module.Basis.repr_self, Finsupp.single_eq_of_ne hne] at h

omit [IsCommMonObj P.pair.T.group.X] in
private theorem product_single_weight (wt : I → Character P.pair.T.group)
    (χ : Character P.pair.T.group) (a₀ : I) (h : ∀ a, wt a = χ ↔ a = a₀)
    {J : Type*} (l : List J) (M : J → Matrix I I k) :
    (l.map fun i ↦ weightBlock wt χ (M i)).prod a₀ a₀ = (l.map fun i ↦ M i a₀ a₀).prod := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [Finset.sum_eq_single a₀, ih]
    · simp [weightBlock, h]
    · intro a _ ha
      simp [weightBlock, h, ha]
    · simp

theorem tracePolynomial : TracePolynomial.{u} := by
  classical
  intro k _ L P hG hsc D r e n ω hω U hU j V
  letI := D.comm
  let ρ := V.action
  let q (χ : Character P.pair.T.group) (i : Fin r) := simplePairing D χ (e i)
  obtain ⟨F, hF⟩ := fundamentalCoordinates D e (corootLattice_eq_top D hG hsc)
  have hq (i j : Fin r) : q (ω j) i = if i = j then 1 else 0 := hω i j
  let α (i : Fin r) := Additive.ofMul (e i).val.val
  have hα : LinearIndependent ℤ α := by
    let E := (simpleIndex D e).symm
    have h := D.base.linearIndepOn_root.comp E E.injective
    convert h using 1
    funext i
    exact (D.datum.root_eq (e i).val).symm
  obtain ⟨v, hv0, hv, hline, hlower⟩ := highestWeight_bound hU V
  obtain ⟨b, wt, hw, hb⟩ := exists_weightBasis ρ P.pair.T P.pair.split
  obtain ⟨a₀, ha₀, huniq, hline'⟩ := topBasisIndex ρ b wt (ω j) hw hb v hv0 hv hline
  have habove (ν : Character P.pair.T.group) (hν : height D (ω j) < height D ν) :
      weightSpace ρ P.pair.T ν = ⊥ := by
    by_contra hne
    have hneq : ν ≠ ω j := fun h ↦ (lt_irrefl _ (h ▸ hν))
    exact (not_lt_of_ge hν.le) (height_strict_of_dominance D hneq (hlower _ hneq hne))
  let H i := height D (ω i)
  have hlower' (a : V.I) (ha : a ≠ a₀) (hdom : ∀ i, 0 ≤ q (wt a) i)
      (i : Fin r) (hi : 0 < q (wt a) i) : H i < H j := by
    have hne : wt a ≠ ω j := fun he ↦ ha (huniq _ he)
    have hn : weightSpace ρ P.pair.T (wt a) ≠ ⊥ := by
      intro h
      have hx := hw a
      rw [h, Submodule.mem_bot] at hx
      exact b.ne_zero a hx
    have ht := height_strict_of_dominance D hne (hlower _ hne hn)
    have hex : Additive.ofMul (wt a) =
        ∑ i, q (wt a) i • Additive.ofMul (ω i) := by
      apply F.injective
      ext l
      simp only [map_sum, Finset.sum_apply, map_zsmul, zsmul_eq_mul]
      change F (Additive.ofMul (wt a)) l = ∑ x, q (wt a) x * F (Additive.ofMul (ω x)) l
      have hF' (x : Fin r) : F (Additive.ofMul (ω x)) l = if l = x then 1 else 0 :=
        (hF _ _).trans (hω l x)
      calc
        F (Additive.ofMul (wt a)) l = q (wt a) l := hF _ _
        _ = ∑ x, q (wt a) x * (if l = x then 1 else 0) := by
          simp [mul_ite]
        _ = _ := Finset.sum_congr rfl fun x _ ↦ congrArg (_ * ·) (hF' x).symm
    have hh := congrArg (heightLinear D) hex
    simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_id] at hh
    change height D (wt a) = ∑ l, q (wt a) l * H l at hh
    have hpos (i : Fin r) : 0 < H i := height_fundamental_pos D e ω hω i
    have hle : H i ≤ height D (wt a) := by
      rw [hh]
      calc
        H i ≤ q (wt a) i * H i := by nlinarith [hpos i]
        _ ≤ _ := Finset.single_le_sum (f := fun l ↦ q (wt a) l * H l)
          (fun l _ ↦ mul_nonneg (hdom l) (hpos l).le) (Finset.mem_univ i)
    exact hle.trans_lt ht
  let pol (i : Fin r) := factorPolynomial ρ b (n (e i))
  let M (i : Fin r) := (pol i).map (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin r) k))
  let C (i : Fin r) := factorCoefficientMatrix ρ b wt (n (e i))
  let l := List.finRange r
  have hM := rootFactors_supported ρ b wt hw hb e n
  have hblock (χ : Character P.pair.T.group) (i : Fin r) :=
    factorBlock ρ b wt hw hb (n (e i)) χ i
  have htop : (l.map fun i ↦ weightBlock wt (wt a₀) (C i)).prod a₀ a₀ ≠ 0 := by
    rw [ha₀, product_single_weight wt (ω j) a₀ (fun a ↦ ⟨huniq _, fun h ↦ h ▸ ha₀⟩)]
    apply List.prod_ne_zero
    intro hc
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hc
    have hD : ∀ ν, height D (wt a₀) < height D ν → weightSpace ρ P.pair.T ν = ⊥ := by
      rw [ha₀]
      exact habove
    have hn := leading_factor_nonzero ρ b wt hw hb (n (e i)) a₀ hline' hD (by
      change q (wt a₀) i = 0 ∨ q (wt a₀) i = 1
      rw [ha₀, hq]
      split <;> simp)
    exact hn hi
  obtain ⟨d, p, hd, hs, he⟩ := trace_polynomial_of_weight_blocks α hα wt M hM C q l
    (List.nodup_finRange r) List.mem_finRange hblock a₀ j
    (fun i ↦ ha₀.symm ▸ hq i j) htop H hlower'
  refine ⟨d, p, hd, hs, ?_⟩
  intro R t
  let E : MvPolynomial (Fin r) k →ₐ[k] R := MvPolynomial.aeval t
  let EMat : Matrix V.I V.I (MvPolynomial (Fin r) k) →+* Matrix V.I V.I R :=
    E.toRingHom.mapMatrix
  have hEval (i : Fin r) :
      EMat (M i) =
        matrixInBasis b ρ R (rootPoint (positiveCoordinate P (e i)) R (t i) *
          representativePoint (n (e i)) R) := by
    rw [← factorPolynomial_eval]
    have hcomp : E.comp (Polynomial.aeval (MvPolynomial.X i)) = Polynomial.aeval (t i) := by
      apply Polynomial.algHom_ext
      simp [E]
    apply Matrix.ext
    intro a c
    exact DFunLike.congr_fun hcomp (pol i a c)
  have hh := congrArg E he
  rw [AddMonoidHom.map_trace E] at hh
  change Matrix.trace (EMat (l.map M).prod) =
    E (MvPolynomial.C d * MvPolynomial.X j + p) at hh
  rw [map_list_prod, List.map_map] at hh
  have hmt : (l.map (EMat ∘ M)).prod = matrixInBasis b ρ R (sectionWord D e n R t) := by
    have hprod (a : Fin r) :
        EMat (M a) =
          matrixInBasis b ρ R
            (rootPoint (positiveCoordinate P (e a)) R (t a) * representativePoint (n (e a)) R) :=
      hEval a
    simp only [Function.comp_def, hprod, sectionWord, map_list_prod, List.map_map]
    rfl
  rw [hmt, matrixInBasis_trace] at hh
  exact hh

end RootFactors

end

end LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
