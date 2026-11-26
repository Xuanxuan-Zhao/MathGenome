import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts
import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl
import LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import LinearAlgebraicGroups.RootData.RootGroups
import LinearAlgebraicGroups.Classification.RankOneRelations
import LinearAlgebraicGroups.Classification.NormalizerComparison
import LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Tactic.Module

import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport
import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts

open AlgebraicGeometry CategoryTheory Topology
open scoped BigOperators CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open LieAlgebrasAndRepresentations
open LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalOuterTorus (MarkedPair complexTest)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open Specs.CharacterPairing (characterValue pairing)

open private rootPoint_comp characterUnit characterValue_eq_unit
  conjugation_by_word rootPoint_eq additivePoints_add
  characterUnit_cocharacter characterUnit_inv rootPoint_natural from LinearAlgebraicGroups.RootData.RootGroups
open private unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private representative_eq_word from LinearAlgebraicGroups.Classification.RankOneRelations
open private asMatrix_mapCoefficients from LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
open Specs.ExceptionalCompactInner (fixedSubgroup)
open Specs.ExceptionalOuterTorus (fixedCompact identityComponent
  OuterInvolutions OuterTorusComparison FixedNormalizerRepresentatives FixedTorusConjugacy
  MaximalFixedTorusExistence)
open Specs.ExceptionalFoldedWeyl
open Specs.ExceptionalOuterFoldedWallTransport
open Specs.ExceptionalOuterCompactRankOneLifts


variable {G : Specs.AffineAlgebraicGroup ℝ} {i : Specs.IntegralModels.MatrixRealization G}
  {ω θ : MulAut (AdelicGroups.PointsIn i ℂ)} {S : Subgroup (AdelicGroups.PointsIn i ℂ)}
  (D : MarkedTorus ω θ S)

private theorem exp_add (y z : E6Space) :
    D.exp (y + z) = D.exp y * D.exp z := D.expAdd y z

private theorem exp_zero : D.exp 0 = 1 :=
  (D.expKernel 0).2 ⟨0, by ext j; simp⟩

private theorem exp_neg (y : E6Space) : D.exp (-y) = (D.exp y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← exp_add, neg_add_cancel, exp_zero]

private theorem exp_sub (y z : E6Space) :
    D.exp (y - z) = D.exp y * (D.exp z)⁻¹ := by
  rw [sub_eq_add_neg, exp_add, exp_neg]

private theorem exp_mem (y : E6Space) : D.exp y ∈ D.T := by
  change D.exp y ∈ (D.T : Set _)
  rw [D.expRange]
  exact ⟨y, rfl⟩

private theorem exists_exp {g : AdelicGroups.PointsIn i ℂ} (hg : g ∈ D.T) :
    ∃ y, D.exp y = g := by
  change g ∈ (D.T : Set _) at hg
  rw [D.expRange] at hg
  exact hg

private theorem torus_commutes {a b : AdelicGroups.PointsIn i ℂ}
    (ha : a ∈ D.T) (hb : b ∈ D.T) : Commute a b := by
  obtain ⟨y, rfl⟩ := exists_exp D ha
  obtain ⟨z, rfl⟩ := exists_exp D hb
  rw [Commute, SemiconjBy, ← exp_add, ← exp_add, add_comm]


private theorem fixed_torus_kernel (x : E6Space) : D.T ⊓ D.fixedAt x = S := by
  refine Eq.trans ?_ D.fixedTorus.symm
  ext g
  change (g ∈ D.T ∧ g ∈ fixedSubgroup ω ∧ D.twisted x g = g) ↔
    (g ∈ D.T ∧ D.δ g = g)
  constructor
  · rintro ⟨hg, _, hfix⟩
    obtain ⟨y, hy⟩ := exists_exp D hg
    have hd : D.δ g ∈ D.T := by rw [← hy, D.diagramExp]; exact exp_mem D _
    refine ⟨hg, ?_⟩
    change D.exp x * D.δ g * (D.exp x)⁻¹ = g at hfix
    rwa [(torus_commutes D (exp_mem D x) hd).eq, mul_inv_cancel_right] at hfix
  · rintro ⟨hg, hd⟩
    refine ⟨hg, ?_, ?_⟩
    · rw [D.centralizer] at hg
      exact hg.1
    · change D.exp x * D.δ g * (D.exp x)⁻¹ = g
      rw [hd, (torus_commutes D (exp_mem D x) hg).eq, mul_inv_cancel_right]


private theorem mem_component_map {H : Type*} [Group H] [TopologicalSpace H]
    {J L : Subgroup H} (f : H →* H) (hf : Continuous f)
    (hm : ∀ g ∈ J, f g ∈ L) {g : H} (hg : g ∈ identityComponent J) :
    f g ∈ identityComponent L := by
  let F : J → L := fun u => ⟨f u.val, hm _ u.property⟩
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have h1 : F 1 = 1 := Subtype.ext (map_one f)
  obtain ⟨u, hu, rfl⟩ := hg
  refine ⟨F u, ?_, rfl⟩
  exact h1 ▸ hF.image_connectedComponent_subset 1 ⟨u, hu, rfl⟩

private theorem conj_intertwine {H : Type*} [Group H] (σ : MulAut H) (a : H) :
    σ * MulAut.conj a = MulAut.conj (σ a) * σ := by
  ext g
  change σ (a * g * a⁻¹) = σ a * σ g * (σ a)⁻¹
  rw [map_mul, map_mul, map_inv]


private theorem torus_subset_compact : D.T ≤ fixedSubgroup ω := by
  rw [D.centralizer]
  exact inf_le_left


private def markedPointMap {A : AdditiveLine ℂ} (M : MarkedPair G A) {Q : GroupScheme ℂ}
    (f : Q ⟶ M.P.pair.G.val) : GroupPoints Q complexTest →* AdelicGroups.PointsIn i ℂ :=
  (baseChangePointGroupEquiv ℂ G.val complexTest).toMonoidHom.comp
    (((groupPointsFunctor ℂ).map (f ≫ M.comparison.hom)).app complexTest).hom

private theorem markedPointMap_apply {A : AdditiveLine ℂ} (M : MarkedPair G A)
    {Q : GroupScheme ℂ} (f : Q ⟶ M.P.pair.G.val) (p : GroupPoints Q complexTest) :
    markedPointMap (i := i) M f p = M.onPoints (i := i) f p := rfl


private theorem e6Inner_basis_row (j : Fin 6) (y : E6Space) :
    e6Inner (Pi.single j 1) y = ∑ k, (CartanMatrix.E 6 j k : ℝ) * y k := by
  unfold e6Inner
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_mul]
  · intro k hk hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

private theorem simple_evaluation (j : Fin 6) (y : E6Space) :
    (∑ k, D.M.rootValues (D.M.simple j).val k * y k) = e6Inner (Pi.single j 1) y := by
  classical
  let := D.M.datum.comm
  have hcartan (k : Fin 6) :
      pairing D.M.P.pair.T.group (D.M.simple j).val.val (D.M.coroot k) =
        CartanMatrix.E 6 k j := by
    have h := D.cartan (D.M.numbering.symm k) (D.M.numbering.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    change D.M.datum.datum.rootDatum.pairing (D.M.simple j).val (D.M.simple k).val = _ at h
    rw [← h]
    change _ = D.M.datum.datum.rootDatum.toLinearMap
      (D.M.datum.datum.rootDatum.root (D.M.simple j).val)
      (D.M.datum.datum.rootDatum.coroot (D.M.simple k).val)
    rw [D.M.datum.datum.root_eq]
    exact (D.M.datum.datum.pairing_eq _ (D.M.coroot k)).symm
  have hsym (k : Fin 6) : CartanMatrix.E 6 k j = CartanMatrix.E 6 j k :=
    congrFun (congrFun (CartanMatrix.E_isSymm 6).eq j) k
  rw [e6Inner_basis_row]
  exact Finset.sum_congr rfl (fun k _ => by
    change ((pairing D.M.P.pair.T.group (D.M.simple j).val.val (D.M.coroot k) : ℤ) : ℝ) * y k = _
    rw [hcartan, hsym])


private theorem torus_conj_on_self {a : AdelicGroups.PointsIn i ℂ} (ha : a ∈ D.T)
    {b : AdelicGroups.PointsIn i ℂ} (hb : b ∈ D.T) :
    MulAut.conj a b = b := by
  change a * b * a⁻¹ = b
  rw [(torus_commutes D ha hb).eq, mul_inv_cancel_right]


private theorem e6Inner_smul_right (β y : E6Space) (r : ℝ) :
    e6Inner β (r • y) = r * e6Inner β y := by
  unfold e6Inner
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem reflection_smul (β y : E6Space) (r : ℝ) :
    reflection β (r • y) = r • reflection β y := by
  unfold reflection
  rw [e6Inner_smul_right]
  module

private theorem weyl_smul {w : Function.End E6Space} (hw : w ∈ e6Weyl) (r : ℝ) (y : E6Space) :
    w (r • y) = r • w y := by
  revert y
  induction hw using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    exact fun y => reflection_smul _ y r
  | one => intro y; rfl
  | mul u v _ _ hu hv =>
    intro y
    change u (v (r • y)) = r • u (v y)
    rw [hv, hu]


private theorem list_prod_single_supported {H : Type*} [Monoid H] {k : ℕ}
    (f : Fin k → H) (j : Fin k) (h : ∀ l ≠ j, f l = 1) :
    (List.ofFn f).prod = f j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j h
    · intro h
      have hf : (fun l : Fin k => f l.succ) = fun _ => 1 :=
        funext fun l => h l.succ (Fin.succ_ne_zero l)
      rw [hf, List.ofFn_const, List.prod_replicate, one_pow, mul_one]
    · intro h
      rw [h 0 (Fin.succ_ne_zero j').symm, one_mul,
        ih (fun l => f l.succ) j' (fun l hl => h l.succ (by simpa using hl))]

private theorem torusPoint_on_coroot (j : Fin 6) (s : ℝ) :
    D.M.torusPoint (s • Pi.single j 1) =
      cocharacterPoint (D.M.coroot j) complexTest (Circle.toUnits (Circle.exp (2 * Real.pi * s))) := by
  unfold MarkedPair.torusPoint
  rw [list_prod_single_supported _ j]
  · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro k hk
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, mul_zero, Circle.exp_zero,
      map_one, cocharacterPoint, ← unitPointHom_apply, map_one]

private theorem markedPointMap_eval {A : AdditiveLine ℂ} (M : MarkedPair G A)
    {Q : GroupScheme ℂ} (f : Q ⟶ M.P.pair.G.val) (p : GroupPoints Q complexTest) :
    markedPointMap (i := i) M (𝟙 _) (((groupPointsFunctor ℂ).map f).app complexTest p) =
      markedPointMap M f p := by
  simp only [markedPointMap_apply, MarkedPair.onPoints, Category.id_comp, Functor.map_comp]
  rfl

private theorem markedPointMap_diagram (p : GroupPoints D.M.P.pair.G.val complexTest) :
    D.δ (markedPointMap (i := i) D.M (𝟙 _) p) =
      markedPointMap D.M (𝟙 _) (((groupPointsFunctor ℂ).map D.d.group.hom).app complexTest p) := by
  rw [markedPointMap_eval, markedPointMap_apply, markedPointMap_apply]
  unfold MarkedPair.onPoints
  rw [Category.id_comp, D.diagramAction]
  have heq : D.M.comparison.hom ≫
      (Aut.of (D.M.comparison.symm ≪≫ D.d.group ≪≫ D.M.comparison)).asIso.hom =
      D.d.group.hom ≫ D.M.comparison.hom := by
    change D.M.comparison.hom ≫ (D.M.comparison.inv ≫ D.d.group.hom ≫ D.M.comparison.hom) = _
    rw [← Category.assoc, D.M.comparison.hom_inv_id, Category.id_comp]
  have h := congrArg
    (fun f : D.M.P.pair.G.val ⟶ (groupBaseChange ℝ ℂ).obj G.val =>
      (baseChangePoint ℝ ℂ G.val.X complexTest
        (((groupPointsFunctor ℂ).map f).app complexTest p) : AdelicGroups.PointsIn i ℂ)) heq
  simp only [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply] at h
  exact h

private theorem simple_coroot_reflection (j : Fin 6) :
    foldedCoroot (Pi.single j 1) = Pi.single j 1 := by
  have h : e6Inner (Pi.single j 1) (Pi.single j 1) = 2 := by
    rw [e6Inner_basis_row, Finset.sum_eq_single j]
    · simp [CartanMatrix.E]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  simp [foldedCoroot, h]

private theorem simple_word_represents (j : Fin 6) (neg : D.A.group ⟶ D.M.P.pair.G.val)
    (r : CorootReflection D.M.P.pair.T (D.M.simple j).val.val (D.M.simpleCoordinate j) neg)
    (hneg : HasScalarAction D.M.P.pair.T (D.M.simple j).val.val⁻¹ neg)
    (hcoroot : r.coroot = D.M.coroot j) :
    D.RepresentsWeyl (markedPointMap (i := i) D.M (𝟙 _)
      (rankOneWord (D.M.simpleCoordinate j) neg complexTest 1)) (reflection (Pi.single j 1)) := by
  intro y
  let s := e6Inner (Pi.single j 1) y
  let F := markedPointMap (i := i) D.M (𝟙 D.M.P.pair.G.val)
  let t := D.M.torusPoint y
  let α := (D.M.simple j).val.val
  have hunit : characterUnit α complexTest t = Circle.toUnits (Circle.exp (2 * Real.pi * s)) := by
    apply Units.ext
    rw [← characterValue_eq_unit, D.rootEvaluation, simple_evaluation]
    rfl
  have h := conjugation_by_word D.M.P.pair.T α (D.M.P.pin (D.M.simple j)).property hneg
    r.coroot r.representative (representative_eq_word r) r.coroot_word complexTest t
  dsimp only at h
  rw [r.representative_word, hcoroot, hunit, ← torusPoint_on_coroot D j s] at h
  let I := ((groupPointsFunctor ℂ).map D.M.P.pair.T.inclusion).app complexTest
  let n := rankOneWord (D.M.simpleCoordinate j) neg complexTest 1
  have hh' : n * I t * n⁻¹ = (I (D.M.torusPoint (s • Pi.single j 1)))⁻¹ * I t := h
  have hh := congrArg F hh'
  simp only [map_mul, map_inv] at hh
  change F n * F (((groupPointsFunctor ℂ).map D.M.P.pair.T.inclusion).app complexTest t) *
    (F n)⁻¹ =
      (F (((groupPointsFunctor ℂ).map D.M.P.pair.T.inclusion).app complexTest
        (D.M.torusPoint (s • Pi.single j 1))))⁻¹ *
      F (((groupPointsFunctor ℂ).map D.M.P.pair.T.inclusion).app complexTest t) at hh
  simp only [F, markedPointMap_eval] at hh
  change F n * D.exp y * (F n)⁻¹ =
      (D.exp (s • Pi.single j 1))⁻¹ * D.exp y at hh
  rw [(torus_commutes D (D.T.inv_mem (exp_mem D _)) (exp_mem D _)).eq, ← exp_sub] at hh
  simpa only [reflection, simple_coroot_reflection] using hh

private theorem positive_root_diagram (j : Fin 6) (z : ℂ) :
    D.δ (markedPointMap (i := i) D.M (𝟙 _) (rootPoint (D.M.simpleCoordinate j) complexTest z)) =
      markedPointMap D.M (𝟙 _) (rootPoint (D.M.simpleCoordinate
        (Specs.AbsoluteDynkinTypes.E6Reflection j)) complexTest z) := by
  rw [markedPointMap_diagram]
  have h : (((groupPointsFunctor ℂ).map D.d.group.hom).app complexTest)
      (rootPoint (D.M.simpleCoordinate j) complexTest z) =
        rootPoint (D.M.simpleCoordinate j ≫ D.d.group.hom) complexTest z := by
    exact (rootPoint_comp (D.M.simpleCoordinate j) D.d.group.hom complexTest z).symm
  rw [h, D.diagramPin]


private theorem represents_mul {a b : AdelicGroups.PointsIn i ℂ} {w v : Function.End E6Space}
    (ha : D.RepresentsWeyl a w) (hb : D.RepresentsWeyl b v) :
    D.RepresentsWeyl (a * b) (w * v) := by
  intro y
  change MulAut.conj (a * b) (D.exp y) = D.exp (w (v y))
  rw [map_mul, MulAut.mul_apply]
  change MulAut.conj a (b * D.exp y * b⁻¹) = _
  rw [hb y]
  exact ha (v y)

private theorem simple_reflection_involutive (j : Fin 6) :
    Function.Involutive (reflection (Pi.single j 1)) := by
  intro y
  let s := e6Inner (Pi.single j 1) y
  have he : e6Inner (Pi.single j 1) (y - s • (Pi.single j 1)) = -s := by
    have h2 : e6Inner (Pi.single j 1) (Pi.single j 1) = 2 := by
      rw [e6Inner_basis_row, Finset.sum_eq_single j]
      · simp [CartanMatrix.E]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · simp
    rw [e6Inner_basis_row] at h2 ⊢
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    have hm (k : Fin 6) :
        (CartanMatrix.E 6 j k : ℝ) * (s * (Pi.single j 1 : E6Space) k) =
          s * ((CartanMatrix.E 6 j k : ℝ) * (Pi.single j 1 : E6Space) k) := by ring
    simp only [hm, ← Finset.mul_sum, h2]
    rw [← e6Inner_basis_row]
    change s - s * 2 = -s
    ring
  simp only [reflection, simple_coroot_reflection]
  change (y - s • Pi.single j 1) -
    e6Inner (Pi.single j 1) (y - s • Pi.single j 1) • Pi.single j 1 = y
  rw [he]
  module

private theorem weyl_surjective {w : Function.End E6Space} (hw : w ∈ e6Weyl) :
    Function.Surjective w := by
  induction hw using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    exact (simple_reflection_involutive j).surjective
  | one => exact fun y => ⟨y, rfl⟩
  | mul u v _ _ hu hv => exact hu.comp hv

private theorem conj_mem_torus_iff {n : AdelicGroups.PointsIn i ℂ}
    {w : Function.End E6Space} (hw : w ∈ e6Weyl) (hnw : D.RepresentsWeyl n w)
    (t : AdelicGroups.PointsIn i ℂ) : MulAut.conj n t ∈ D.T ↔ t ∈ D.T := by
  constructor
  · intro ht
    obtain ⟨y, hy⟩ := exists_exp D ht
    obtain ⟨z, rfl⟩ := weyl_surjective hw y
    have h := (MulAut.conj n).injective ((hnw z).trans hy)
    exact h ▸ exp_mem D z
  · intro ht
    obtain ⟨y, rfl⟩ := exists_exp D ht
    rw [show MulAut.conj n (D.exp y) = _ from hnw y]
    exact exp_mem D _

private theorem diagram_lift_normalizes {n : AdelicGroups.PointsIn i ℂ}
    (hδ : n ∈ fixedSubgroup D.δ)
    {w : Function.End E6Space} (hw : w ∈ e6Weyl) (hnw : D.RepresentsWeyl n w) :
    n ∈ Subgroup.normalizer (S : Set _) := by
  have hT := conj_mem_torus_iff D hw hnw
  have hd : ∀ t, MulAut.conj n t ∈ fixedSubgroup D.δ ↔ t ∈ fixedSubgroup D.δ := by
    intro t
    have hc : D.δ * MulAut.conj n = MulAut.conj n * D.δ :=
      (conj_intertwine _ _).trans (congrArg (fun g => MulAut.conj g * D.δ)
        (show D.δ n = n from hδ))
    change D.δ (MulAut.conj n t) = MulAut.conj n t ↔ D.δ t = t
    rw [show D.δ (MulAut.conj n t) = MulAut.conj n (D.δ t) from DFunLike.congr_fun hc t]
    exact (MulAut.conj n).injective.eq_iff
  refine Subgroup.mem_normalizer_iff.mpr fun t => ?_
  have hS (v) : v ∈ S ↔ v ∈ D.T ∧ v ∈ fixedSubgroup D.δ :=
    SetLike.ext_iff.mp D.fixedTorus v
  change t ∈ S ↔ MulAut.conj n t ∈ S
  rw [hS, hS, hT, hd]

/-- The simple orbit words generate compact representatives for the commuting Weyl group. -/
private theorem diagram_lifts_of_simple_words (weyl : FoldedWeylCalculation)
    (n : Fin 6 → AdelicGroups.PointsIn i ℂ)
    (hω : ∀ j, n j ∈ fixedSubgroup ω)
    (hδ : ∀ j, D.δ (n j) = n (Specs.AbsoluteDynkinTypes.E6Reflection j))
    (hrep : ∀ j, D.RepresentsWeyl (n j) (reflection (Pi.single j 1)))
    (h₀₅ : Commute (n 0) (n 5)) (h₂₄ : Commute (n 2) (n 4)) :
    ∀ w ∈ diagramCentralizingWeyl, ∃ m ∈ fixedCompact ω D.δ,
      m ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl m w := by
  have hgen : ∀ j : Fin 4, ∃ m ∈ fixedCompact ω D.δ, D.RepresentsWeyl m (orbitReflection j) := by
    let K := fixedSubgroup ω
    let σ := Specs.AbsoluteDynkinTypes.E6Reflection
    have hσ₀ : σ 0 = 5 := by decide
    have hσ₅ : σ 5 = 0 := by decide
    have hσ₂ : σ 2 = 4 := by decide
    have hσ₄ : σ 4 = 2 := by decide
    have hσ₃ : σ 3 = 3 := by decide
    have hσ₁ : σ 1 = 1 := by decide
    have hs₀ : D.δ (n 0 * n 5) = n 0 * n 5 := by
      rw [map_mul, hδ, hδ, hσ₀, hσ₅]
      exact h₀₅.eq.symm
    have hs₂ : D.δ (n 2 * n 4) = n 2 * n 4 := by
      rw [map_mul, hδ, hδ, hσ₂, hσ₄]
      exact h₂₄.eq.symm
    intro j
    fin_cases j
    · exact ⟨n 0 * n 5, ⟨K.mul_mem (hω 0) (hω 5), hs₀⟩, represents_mul D (hrep 0) (hrep 5)⟩
    · exact ⟨n 2 * n 4, ⟨K.mul_mem (hω 2) (hω 4), hs₂⟩, represents_mul D (hrep 2) (hrep 4)⟩
    · exact ⟨n 3, ⟨hω 3, (hδ 3).trans (congrArg n hσ₃)⟩, hrep 3⟩
    · exact ⟨n 1, ⟨hω 1, (hδ 1).trans (congrArg n hσ₁)⟩, hrep 1⟩
  intro w hw
  have hw' : w ∈ Submonoid.closure (Set.range orbitReflection) := by
    change w ∈ (Submonoid.closure (Set.range orbitReflection) : Set _)
    rwa [← weyl.1]
  obtain ⟨m, hm, hmact⟩ : ∃ m ∈ fixedCompact ω D.δ, D.RepresentsWeyl m w := by
    clear hw
    induction hw' using Submonoid.closure_induction with
    | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      exact hgen j
    | one =>
      refine ⟨1, (fixedCompact ω D.δ).one_mem, ?_⟩
      intro y
      change MulAut.conj (1 : AdelicGroups.PointsIn i ℂ) (D.exp y) = D.exp y
      rw [map_one]
      rfl
    | mul u v _ _ hu hv =>
      obtain ⟨a, ha, hact⟩ := hu
      obtain ⟨b, hb, hbact⟩ := hv
      exact ⟨a * b, (fixedCompact ω D.δ).mul_mem ha hb, represents_mul D hact hbact⟩
  exact ⟨m, hm, diagram_lift_normalizes D hm.2 hw.1 hmact, hmact⟩

section RankOneMatrixHomomorphism

open Specs.IntegralRootRelations (upper lower diagonal)
open private Gauss Gauss.mk Gauss.l Gauss.r Gauss.a Gauss.matrix Gauss.matrix_val Gauss.ofMatrix Gauss.matrix_ofMatrix
  Gauss.matrix_injective Gauss.product_matrix Gauss.upperFactor Gauss.lowerFactor
  Gauss.diagonalFactor Gauss.matrix_upper Gauss.matrix_lower Gauss.matrix_diagonal rankOne_gauss_mul
  from LinearAlgebraicGroups.Classification.IntegralRankOneExtension

variable {K H : Type*} [Field K] [Group H]

private abbrev SL₂ (K : Type*) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

private theorem upper_entries_mul (u v : K) :
    upper (u + v) = upper u * upper v := by
  apply Subtype.ext
  change (!![1, u + v; 0, 1] : Matrix (Fin 2) (Fin 2) K) =
    !![1, u; 0, 1] * !![1, v; 0, 1]
  ext row col
  fin_cases row <;> fin_cases col <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem upper_entries_zero : upper (0 : K) = 1 := by
  apply Subtype.ext
  ext row col
  fin_cases row <;> fin_cases col <;> simp [upper]

private theorem pivot_after_upper (g : SL₂ K) (u : K) :
    (upper u * g).val 0 0 = g.val 0 0 + u * g.val 1 0 := by
  change (Matrix.of ![![1, u], ![0, 1]] * g.val) 0 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem pivot_exists [Infinite K] (g h : SL₂ K) :
    ∃ u : K, (upper u * g).val 0 0 ≠ 0 ∧ (upper u * h).val 0 0 ≠ 0 := by
  classical
  have hbad (f : SL₂ K) : (upper (0 : K) * f).val 0 0 ≠ 0 ∨ f.val 1 0 ≠ 0 := by
    have hdet : f.val 0 0 * f.val 1 1 - f.val 0 1 * f.val 1 0 = 1 :=
      (Matrix.det_fin_two f.val).symm.trans f.property
    rw [upper_entries_zero, one_mul]
    by_contra! hh
    rw [hh.1, hh.2, zero_mul, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset
    ({-(g.val 0 0) / g.val 1 0, -(h.val 0 0) / h.val 1 0} : Finset K)
  have hf (f : SL₂ K) (hf : u ≠ -(f.val 0 0) / f.val 1 0) :
      (upper u * f).val 0 0 ≠ 0 := by
    rw [pivot_after_upper]
    by_cases hn : f.val 1 0 = 0
    · simpa only [hn, mul_zero, add_zero, upper_entries_zero, one_mul] using
        ((hbad f).resolve_right (not_not_intro hn))
    · exact fun e => hf ((eq_div_iff hn).mpr (eq_neg_of_add_eq_zero_right e))
  exact ⟨u, hf g (fun e => hu (by simp [e])),
    hf h (fun e => hu (by simp [e]))⟩

private def gaussValue (U L : Multiplicative K →* H) (T : Kˣ →* H) (b : Gauss K) : H :=
  L (.ofAdd (Gauss.l b)) * T (Gauss.a b) * U (.ofAdd (Gauss.r b))

private def pivotValue (U L : Multiplicative K →* H) (T : Kˣ →* H) (g : SL₂ K)
    (hg : g.val 0 0 ≠ 0) : H :=
  gaussValue U L T (Gauss.ofMatrix g (Units.mk0 _ hg))

private theorem pivotValue_congr (U L : Multiplicative K →* H) (T : Kˣ →* H)
    {g h : SL₂ K} (he : g = h) (hg : g.val 0 0 ≠ 0) (hh : h.val 0 0 ≠ 0) :
    pivotValue U L T g hg = pivotValue U L T h hh := by
  subst h
  rfl

private theorem pivotValue_gauss (U L : Multiplicative K →* H) (T : Kˣ →* H)
    (b : Gauss K) (hb : (Gauss.matrix b).val 0 0 ≠ 0) :
    pivotValue U L T (Gauss.matrix b) hb = gaussValue U L T b := by
  unfold pivotValue
  congr 1
  apply Gauss.matrix_injective
  exact Gauss.matrix_ofMatrix (Gauss.matrix b) (Units.mk0 _ hb) rfl

private theorem pivotValue_mul (U L : Multiplicative K →* H) (T : Kˣ →* H)
    (opposite : ∀ (u v : K) (c : Kˣ), (c : K) = 1 + u * v →
      U (.ofAdd u) * L (.ofAdd v) =
        L (.ofAdd (v * (↑c⁻¹ : K))) * T c * U (.ofAdd (u * (↑c⁻¹ : K))))
    (hU : ∀ (a : Kˣ) (u : K),
      T a * U (.ofAdd u) * (T a)⁻¹ = U (.ofAdd ((a : K)^2 * u)))
    (hL : ∀ (a : Kˣ) (v : K),
      T a * L (.ofAdd v) * (T a)⁻¹ = L (.ofAdd ((↑a⁻¹ : K)^2 * v)))
    (g h : SL₂ K) (hg : g.val 0 0 ≠ 0) (hh : h.val 0 0 ≠ 0)
    (hgh : (g * h).val 0 0 ≠ 0) :
    pivotValue U L T (g * h) hgh = pivotValue U L T g hg * pivotValue U L T h hh := by
  let b := Gauss.ofMatrix g (Units.mk0 _ hg)
  let c := Gauss.ofMatrix h (Units.mk0 _ hh)
  have hb : Gauss.matrix b = g := Gauss.matrix_ofMatrix g (Units.mk0 _ hg) rfl
  have hc : Gauss.matrix c = h := Gauss.matrix_ofMatrix h (Units.mk0 _ hh) rfl
  have hp : ((g * h).val 0 0 : K) = ((Gauss.a b) : K) * ((Gauss.a c) : K) * (1 + (Gauss.r b) * (Gauss.l c)) := by
    rw [← hb, ← hc]
    change ((Gauss.matrix b).val * (Gauss.matrix c).val) 0 0 = _
    rw [Gauss.matrix_val, Gauss.matrix_val]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hs : 1 + (Gauss.r b) * (Gauss.l c) ≠ 0 := fun e => hgh (by rw [hp, e, mul_zero])
  let s := Units.mk0 (1 + (Gauss.r b) * (Gauss.l c)) hs
  let d : Gauss K := Gauss.mk ((Gauss.l b) + (↑(Gauss.a b)⁻¹ : K)^2 * ((Gauss.l c) * ↑s⁻¹))
    ((Gauss.a b) * s * (Gauss.a c)) ((↑(Gauss.a c)⁻¹ : K)^2 * ((Gauss.r b) * ↑s⁻¹) + (Gauss.r c))
  have hd : Gauss.matrix d = g * h := (Gauss.product_matrix b c s rfl).symm.trans (by rw [hb, hc])
  change pivotValue U L T (g * h) hgh = gaussValue U L T b * gaussValue U L T c
  have hv : pivotValue U L T (g * h) hgh = gaussValue U L T d := by
    exact (pivotValue_congr U L T hd.symm _ (hd.symm ▸ hgh)).trans (pivotValue_gauss U L T d _)
  rw [hv]
  exact (rankOne_gauss_mul U L T opposite hU hL (Gauss.l b) (Gauss.r b) (Gauss.l c) (Gauss.r c) (Gauss.a b) (Gauss.a c) s rfl).symm

private theorem pivotValue_upper (U L : Multiplicative K →* H) (T : Kˣ →* H)
    (u : K) (hu : (upper u).val 0 0 ≠ 0) :
    pivotValue U L T (upper u) hu = U (.ofAdd u) := by
  let b := Gauss.upperFactor u
  have he : Gauss.matrix b = upper u := Gauss.matrix_upper u
  rw [pivotValue_congr U L T he.symm hu (he.symm ▸ hu), pivotValue_gauss]
  change L (Multiplicative.ofAdd 0) * T 1 * U (.ofAdd u) = _
  simp

/-- The two pivot charts turn linked root and coroot point homomorphisms
into a homomorphism on the actual determinant-one matrices. -/
private theorem rankOne_hom_of_pivots [Infinite K]
    (U L : Multiplicative K →* H) (T : Kˣ →* H)
    (opposite : ∀ (u v : K) (c : Kˣ), (c : K) = 1 + u * v →
      U (.ofAdd u) * L (.ofAdd v) =
        L (.ofAdd (v * (↑c⁻¹ : K))) * T c * U (.ofAdd (u * (↑c⁻¹ : K))))
    (hU : ∀ (a : Kˣ) (u : K),
      T a * U (.ofAdd u) * (T a)⁻¹ = U (.ofAdd ((a : K)^2 * u)))
    (hL : ∀ (a : Kˣ) (v : K),
      T a * L (.ofAdd v) * (T a)⁻¹ = L (.ofAdd ((↑a⁻¹ : K)^2 * v))) :
    ∃ f : SL₂ K →* H,
      (∀ g (hg : g.val 0 0 ≠ 0), f g = pivotValue U L T g hg) ∧
      (∀ u, f (upper u) = U (.ofAdd u)) ∧
      (∀ v, f (lower v) = L (.ofAdd v)) ∧
      ∀ a, f (diagonal a) = T a := by
  classical
  let shift (g : SL₂ K) := (pivot_exists g g).choose
  have hshift (g : SL₂ K) : (upper (shift g) * g).val 0 0 ≠ 0 :=
    (pivot_exists g g).choose_spec.1
  let f (g : SL₂ K) := U (.ofAdd (-shift g)) * pivotValue U L T (upper (shift g) * g) (hshift g)
  have hupper (u : K) : (upper u).val 0 0 ≠ 0 := one_ne_zero
  have hpiv := pivotValue_mul U L T opposite hU hL
  have hchart (g : SL₂ K) (u : K) (hu : (upper u * g).val 0 0 ≠ 0) :
      f g = U (.ofAdd (-u)) * pivotValue U L T (upper u * g) hu := by
    let v := shift g - u
    have he : upper v * (upper u * g) = upper (shift g) * g := by
      rw [← mul_assoc, ← upper_entries_mul, sub_add_cancel]
    have hh := hpiv (upper v) (upper u * g) (hupper v) hu (he.symm ▸ hshift g)
    rw [pivotValue_upper] at hh
    change pivotValue U L T (upper v * (upper u * g)) _ = _ at hh
    have hh' := (pivotValue_congr U L T he _ (hshift g)).symm.trans hh
    dsimp only [f]
    rw [hh', ← mul_assoc, ← U.map_mul]
    have hv : -shift g + v = -u := by dsimp [v]; ring
    exact congrArg (· * pivotValue U L T (upper u * g) hu) (congrArg (fun k : K => U (.ofAdd k)) hv)
  have hQ (g : SL₂ K) (hg : g.val 0 0 ≠ 0) : f g = pivotValue U L T g hg := by
    have hh : (upper 0 * g).val 0 0 ≠ 0 := by rwa [upper_entries_zero, one_mul]
    have he : upper (0 : K) * g = g := by rw [upper_entries_zero, one_mul]
    have hc := hchart g 0 hh
    rw [pivotValue_congr U L T he hh hg] at hc
    simpa only [neg_zero, ofAdd_zero, map_one, one_mul] using hc
  have hmul (g h : SL₂ K) (hh : h.val 0 0 ≠ 0) : f (g * h) = f g * f h := by
    obtain ⟨u, hg, hgh⟩ := pivot_exists g (g * h)
    have e : (upper u * g) * h = upper u * (g * h) := mul_assoc _ _ _
    have hv : ((upper u * g) * h).val 0 0 ≠ 0 := e.symm ▸ hgh
    have hp := (pivotValue_congr U L T e hv hgh).symm.trans
      (hpiv (upper u * g) h hg hh hv)
    rw [hchart _ u hgh, hp, hchart _ u hg, hQ _ hh, mul_assoc]
  have hall (g h : SL₂ K) : f (g * h) = f g * f h := by
    let u := shift h
    have hk : g * h = (g * upper (-u)) * (upper u * h) := by
      rw [mul_assoc, ← mul_assoc (upper (-u)), ← upper_entries_mul,
        neg_add_cancel, upper_entries_zero, one_mul]
    rw [hk, hmul _ _ (hshift h), hmul _ _ (hupper _), mul_assoc]
    congr 1
    rw [← hmul _ _ (hshift h), ← mul_assoc, ← upper_entries_mul,
      neg_add_cancel, upper_entries_zero, one_mul]
  refine ⟨MonoidHom.mk' f hall, hQ, ?_, ?_, ?_⟩
  · intro u
    exact (hQ _ (hupper u)).trans (pivotValue_upper U L T u _)
  · intro v
    have hv : (lower v).val 0 0 ≠ 0 := one_ne_zero
    rw [show (MonoidHom.mk' f hall) (lower v) = f (lower v) from rfl, hQ _ hv]
    let b := Gauss.lowerFactor v
    have he : Gauss.matrix b = lower v := Gauss.matrix_lower v
    rw [pivotValue_congr U L T he.symm hv (he.symm ▸ hv), pivotValue_gauss]
    change L (.ofAdd v) * T 1 * U (.ofAdd 0) = _
    simp
  · intro a
    have ha : (diagonal a).val 0 0 ≠ 0 := a.ne_zero
    rw [show (MonoidHom.mk' f hall) (diagonal a) = f (diagonal a) from rfl, hQ _ ha]
    let b := Gauss.diagonalFactor a
    have he : Gauss.matrix b = diagonal a := Gauss.matrix_diagonal a
    rw [pivotValue_congr U L T he.symm ha (he.symm ▸ ha), pivotValue_gauss]
    change L (.ofAdd 0) * T a * U (.ofAdd 0) = _
    simp

end RankOneMatrixHomomorphism

section ActualRankOne

open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.CharacterDescent (Cocharacter)
open Specs.Pinning (SplitBorelPair)
open Specs.AbstractPairing (Root)

private abbrev schemePointHom {Q Q' : GroupScheme ℂ} (f : Q ⟶ Q') :
    GroupPoints Q complexTest →* GroupPoints Q' complexTest :=
  (((groupPointsFunctor ℂ).map f).app complexTest).hom

private def rootCoordinateHom {Q : GroupScheme ℂ} {A : AdditiveLine ℂ} (p : A.group ⟶ Q) :
    Multiplicative ℂ →* GroupPoints Q complexTest :=
  (schemePointHom p).comp <| MonoidHom.mk'
    (fun z : Multiplicative ℂ => RootData.RootGroups.additivePoints A complexTest z.toAdd)
    (fun z v => additivePoints_add A complexTest (z.toAdd : complexTest) v.toAdd)

private theorem rootCoordinateHom_apply {Q : GroupScheme ℂ} {A : AdditiveLine ℂ}
    (p : A.group ⟶ Q) (z : ℂ) :
    rootCoordinateHom p (.ofAdd z) = rootPoint p complexTest z :=
  (rootPoint_eq p complexTest z).symm

private def corootCoordinateHom {Q : GroupScheme ℂ} (T : Specs.ClosedSubgroup Q)
    (c : Cocharacter T.group) : ℂˣ →* GroupPoints Q complexTest :=
  (schemePointHom (c ≫ T.inclusion)).comp (unitPointHom complexTest)

private theorem corootCoordinateHom_apply {Q : GroupScheme ℂ} (T : Specs.ClosedSubgroup Q)
    (c : Cocharacter T.group) (u : ℂˣ) :
    corootCoordinateHom T c u = schemePointHom T.inclusion (cocharacterPoint c complexTest u) := by
  change unitPointHom complexTest u ≫ (c ≫ T.inclusion).hom.hom = _
  rw [unitPointHom_apply]
  rfl

/-- The linked rank-one coordinates define a homomorphism on the actual
complex determinant-one matrices, matching the two root groups and the coroot. -/
private theorem linkedRankOne_matrixHom (P : SplitBorelPair ℂ) (α : Root P.T)
    {A : AdditiveLine ℂ} (p n : A.group ⟶ P.G.val) (r : CorootReflection P.T α.val p n)
    (hp : HasScalarAction P.T α.val p) (hn : HasScalarAction P.T α.val⁻¹ n) :
    ∃ f : SL₂ ℂ →* GroupPoints P.G.val complexTest,
      (∀ z, f (upper z) = rootPoint p complexTest z) ∧
      (∀ z, f (lower z) = rootPoint n complexTest z) ∧
      ∀ t, f (diagonal t) = schemePointHom P.T.inclusion
        (cocharacterPoint r.coroot complexTest t) := by
  let U := rootCoordinateHom p
  let L := rootCoordinateHom n
  let T := corootCoordinateHom P.T r.coroot
  have hop (u v : ℂ) (c : ℂˣ) (hc : (c : ℂ) = 1 + u * v) :
      U (.ofAdd u) * L (.ofAdd v) =
        L (.ofAdd (v * (↑c⁻¹ : ℂ))) * T c * U (.ofAdd (u * (↑c⁻¹ : ℂ))) := by
    change _ = L (.ofAdd (v * (↑c⁻¹ : ℂ))) *
      corootCoordinateHom P.T r.coroot c * U (.ofAdd (u * (↑c⁻¹ : ℂ)))
    rw [corootCoordinateHom_apply]
    dsimp only [U, L]
    rw [rootCoordinateHom_apply, rootCoordinateHom_apply, rootCoordinateHom_apply,
      rootCoordinateHom_apply]
    exact (Classification.RankOneRelations.oppositeRootRelations
      P.G P.reductive P.T P.split P.maximal α.val α.property p n r hp hn complexTest).1 u v c hc
  have hα (a : ℂˣ) : characterUnit α.val complexTest (cocharacterPoint r.coroot complexTest a) =
      a ^ 2 := by
    rw [characterUnit_cocharacter, r.root_pairing, zpow_ofNat]
  have hU (a : ℂˣ) (u : ℂ) :
      T a * U (.ofAdd u) * (T a)⁻¹ = U (.ofAdd ((a : ℂ)^2 * u)) := by
    change corootCoordinateHom P.T r.coroot a * _ * (corootCoordinateHom P.T r.coroot a)⁻¹ = _
    dsimp only [U]
    rw [corootCoordinateHom_apply, rootCoordinateHom_apply, rootCoordinateHom_apply]
    have h := hp complexTest (cocharacterPoint r.coroot complexTest a) u
    dsimp only at h
    rw [characterValue_eq_unit, hα, Units.val_pow_eq_pow_val] at h
    exact h
  have hL (a : ℂˣ) (v : ℂ) :
      T a * L (.ofAdd v) * (T a)⁻¹ = L (.ofAdd ((↑a⁻¹ : ℂ)^2 * v)) := by
    change corootCoordinateHom P.T r.coroot a * _ * (corootCoordinateHom P.T r.coroot a)⁻¹ = _
    dsimp only [L]
    rw [corootCoordinateHom_apply, rootCoordinateHom_apply, rootCoordinateHom_apply]
    have h := hn complexTest (cocharacterPoint r.coroot complexTest a) v
    dsimp only at h
    rw [characterValue_eq_unit, characterUnit_inv, hα, ← inv_pow, Units.val_pow_eq_pow_val] at h
    exact h
  obtain ⟨f, _, hpos, hneg, hdiag⟩ := rankOne_hom_of_pivots U L T hop hU hL
  exact ⟨f, fun z => (hpos z).trans (rootCoordinateHom_apply p z),
    fun z => (hneg z).trans (rootCoordinateHom_apply n z),
    fun t => (hdiag t).trans (corootCoordinateHom_apply P.T r.coroot t)⟩

end ActualRankOne

/-- Polynomial root coordinates are continuous in the topology of the specified real matrix realization. -/
private theorem continuous_markedRootPoint {A : AdditiveLine ℂ} (M : MarkedPair G A)
    (p : A.group ⟶ M.P.pair.G.val) :
    Continuous (fun z : ℂ => M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z)) := by
  let R := CommAlgCat.of ℂ (Polynomial ℂ)
  let P₀ := rootPoint p R (Polynomial.X : Polynomial ℂ)
  let P₁ := ((groupPointsFunctor ℂ).map M.comparison.hom).app R P₀
  let g : AdelicGroups.PointsIn i (Polynomial ℂ) := baseChangePoint ℝ ℂ G.val.X R P₁
  let a (z : ℂ) : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval z).restrictScalars ℝ
  have h (z : ℂ) : M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z) =
      ((groupPointsFunctor ℝ).obj G.val).map (CommAlgCat.ofHom (a z)) g := by
    let b : R ⟶ complexTest := CommAlgCat.ofHom (Polynomial.aeval z)
    have h₀ : mapPoints b P₀ = rootPoint p complexTest z := by
      dsimp only [P₀]
      rw [rootPoint_natural]
      exact congrArg (rootPoint p complexTest) (Polynomial.aeval_X z)
    have h₁ : mapPoints b P₁ = ((groupPointsFunctor ℂ).map M.comparison.hom).app complexTest
        (rootPoint p complexTest z) := by
      have hn := congrArg (fun f => f P₀) (((groupPointsFunctor ℂ).map M.comparison.hom).naturality b)
      change ((groupPointsFunctor ℂ).map M.comparison.hom).app complexTest (mapPoints b P₀) =
        mapPoints b P₁ at hn
      exact hn.symm.trans (congrArg (fun u : GroupPoints M.P.pair.G.val complexTest =>
        ((groupPointsFunctor ℂ).map M.comparison.hom).app complexTest u) h₀)
    unfold MarkedPair.onPoints
    rw [Category.id_comp, ← h₁]
    exact baseChangePointsNaturality ℝ ℂ G.val.X b P₁
  have hmat (z : ℂ) : AdelicGroups.asMatrix i ℂ
      (M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z)) =
      Matrix.GeneralLinearGroup.map (a z).toRingHom (AdelicGroups.asMatrix i (Polynomial ℂ) g) :=
    (congrArg (AdelicGroups.asMatrix i ℂ) (h z)).trans (asMatrix_mapCoefficients i (a z) g)
  refine (IsInducing.induced (AdelicGroups.asMatrix i ℂ)).continuous_iff.mpr ?_
  change Continuous (fun z => AdelicGroups.asMatrix i ℂ
    (M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z)))
  simp_rw [hmat]
  let B := AdelicGroups.asMatrix i (Polynomial ℂ) g
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun l m => ?_,
    continuous_matrix fun l m => ?_⟩
  · change Continuous (fun z => Polynomial.eval z (B.val l m))
    exact (B.val l m).continuous
  · change Continuous (fun z => Polynomial.eval z (B⁻¹.val l m))
    exact (B⁻¹.val l m).continuous

section RankOneTopology

open Specs.IntegralRootRelations (upper lower diagonal)
open private rankOne_pivot_factorization
  from LinearAlgebraicGroups.Classification.IntegralRankOneExtension

private def elementaryWeyl (t : ℂˣ) : SL₂ ℂ :=
  upper (t : ℂ) * lower (-(↑t⁻¹ : ℂ)) * upper (t : ℂ)

private theorem elementaryWeyl_val (t : ℂˣ) :
    (elementaryWeyl t).val = !![0, (t : ℂ); -(↑t⁻¹ : ℂ), 0] := by
  change (!![1, (t : ℂ); 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *
    !![1, 0; -(↑t⁻¹ : ℂ), 1] * !![1, (t : ℂ); 0, 1] = _
  ext row col
  fin_cases row <;> fin_cases col <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagonal_as_word (t : ℂˣ) :
    diagonal t = elementaryWeyl t * elementaryWeyl (-1) := by
  apply Subtype.ext
  change (diagonal t).val = (elementaryWeyl t).val * (elementaryWeyl (-1)).val
  rw [elementaryWeyl_val, elementaryWeyl_val]
  ext row col
  fin_cases row <;> fin_cases col <;> simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two elementary root families determine a homomorphism on complex SL(2). -/
private theorem rankOne_hom_ext {H : Type*} [Group H] {f g : SL₂ ℂ →* H}
    (hu : ∀ z : ℂ, f (upper z) = g (upper z))
    (hl : ∀ z : ℂ, f (lower z) = g (lower z)) : f = g := by
  have hd (t : ℂˣ) : f (diagonal t) = g (diagonal t) := by
    simp only [diagonal_as_word, elementaryWeyl, map_mul, hu, hl]
  have hchart (m : SL₂ ℂ) (hm : m.val 0 0 ≠ 0) : f m = g m := by
    let t := Units.mk0 (m.val 0 0) hm
    rw [rankOne_pivot_factorization m t rfl]
    simp only [map_mul, hl, hu, hd]
  ext m
  obtain ⟨u, h, _⟩ := pivot_exists m m
  apply mul_left_cancel (a := f (upper u))
  rw [← map_mul, hchart _ h, map_mul, hu]

/-- Continuity of the elementary root families gives continuity of a complex
rank-one homomorphism, via the nonzero pivot chart at the identity. -/
private theorem continuous_rankOne_hom {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : SL₂ ℂ →* H) (hu : Continuous (fun z : ℂ => f (upper z)))
    (hl : Continuous (fun z : ℂ => f (lower z))) : Continuous f := by
  have hd : Continuous fun t : ℂˣ => f (diagonal t) := by
    simp only [diagonal_as_word, elementaryWeyl, map_mul]
    have ht : Continuous (fun t : ℂˣ => (t : ℂ)) := Units.continuous_val
    have ht' : Continuous (fun t : ℂˣ => (↑t⁻¹ : ℂ)) := ht.comp continuous_inv
    exact ((((hu.comp ht).mul (hl.comp ht'.neg)).mul (hu.comp ht)).mul continuous_const)
  let P := {m : SL₂ ℂ | m.val 0 0 ≠ 0}
  have h_entry (r s : Fin 2) : Continuous (fun m : SL₂ ℂ => m.val r s) :=
    (continuous_apply s).comp ((continuous_apply r).comp continuous_subtype_val)
  have ho : IsOpen P := isOpen_ne_fun (h_entry 0 0) continuous_const
  have h1 : (1 : SL₂ ℂ) ∈ P := by change (1 : ℂ) ≠ 0; exact one_ne_zero
  apply continuous_of_continuousAt_one f
  suffices hb : ContinuousOn f P from hb.continuousAt (ho.mem_nhds h1)
  rw [continuousOn_iff_continuous_domRestrict]
  let unit (m : P) : ℂˣ := Units.mk0 (m.val.val 0 0) m.property
  have he (r s : Fin 2) : Continuous (fun m : P => m.val.val r s) :=
    (h_entry _ _).comp continuous_subtype_val
  have hi : Continuous (fun m : P => (↑(unit m)⁻¹ : ℂ)) :=
    (he 0 0).inv₀ (fun m => m.property)
  have hunit : Continuous unit := Units.continuous_iff.mpr ⟨he 0 0, hi⟩
  have hval (m : P) : f m.val =
      f (lower (m.val.val 1 0 * ↑(unit m)⁻¹)) * f (diagonal (unit m)) *
        f (upper (m.val.val 0 1 * ↑(unit m)⁻¹)) := by
    have h := congrArg f (rankOne_pivot_factorization m.val (unit m) rfl)
    simpa only [map_mul] using h
  change Continuous (fun m : P => f m.val)
  simp_rw [hval]
  exact ((hl.comp ((he 1 0).mul hi)).mul (hd.comp hunit)).mul (hu.comp ((he 0 1).mul hi))

end RankOneTopology

section CompactRankOne

open Specs.IntegralRootRelations (upper lower diagonal)

private abbrev SU₂ := Matrix.specialUnitaryGroup (Fin 2) ℂ

private def unitaryToSpecialLinear : SU₂ →* SL₂ ℂ where
  toFun m := ⟨m.val, (Matrix.mem_specialUnitaryGroup_iff.mp m.property).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem continuous_unitaryToSpecialLinear : Continuous unitaryToSpecialLinear :=
  continuous_subtype_val.subtype_mk _

private def adjointMatrix (m : SL₂ ℂ) : SL₂ ℂ :=
  ⟨star m.val, by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    simp [m.property]⟩

private def compactMatrixConjugation : SL₂ ℂ →* SL₂ ℂ where
  toFun m := (adjointMatrix m)⁻¹
  map_one' := by
    change (adjointMatrix 1)⁻¹ = 1
    rw [show adjointMatrix 1 = 1 from Subtype.ext (star_one _), inv_one]
  map_mul' a b := by
    change (adjointMatrix (a * b))⁻¹ = (adjointMatrix a)⁻¹ * (adjointMatrix b)⁻¹
    rw [show adjointMatrix (a * b) = adjointMatrix b * adjointMatrix a from
      Subtype.ext (star_mul a.val b.val), mul_inv_rev]

private theorem compactMatrixConjugation_upper (z : ℂ) :
    compactMatrixConjugation (upper z) = lower (-Complex.conjAe z) := by
  apply Subtype.ext
  change Matrix.adjugate (star (!![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) = _
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose, lower]

private theorem compactMatrixConjugation_lower (z : ℂ) :
    compactMatrixConjugation (lower z) = upper (-Complex.conjAe z) := by
  apply Subtype.ext
  change Matrix.adjugate (star (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ)) = _
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose, upper]

private theorem compactMatrixConjugation_fixed (m : SU₂) :
    compactMatrixConjugation (unitaryToSpecialLinear m) = unitaryToSpecialLinear m := by
  have h : adjointMatrix (unitaryToSpecialLinear m) * unitaryToSpecialLinear m = 1 :=
    Subtype.ext (Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp m.property).1)
  change (adjointMatrix (unitaryToSpecialLinear m))⁻¹ = unitaryToSpecialLinear m
  rw [eq_inv_of_mul_eq_one_left h, inv_inv]

/-- An SL(2) map whose elementary coordinates are exchanged by compact
conjugation takes SU(2) into the compact fixed group. -/
private theorem compact_rankOne_range {H : Type*} [Group H] (ω : MulAut H) (hω : Function.Involutive ω)
    (f : SL₂ ℂ →* H) (h : ∀ z : ℂ, ω (f (upper z)) = f (lower (-Complex.conjAe z))) :
    Set.range (f.comp unitaryToSpecialLinear) ⊆ (fixedSubgroup ω : Set H) := by
  have hc (z : ℂ) : -Complex.conjAe (-Complex.conjAe z) = z := by
    simp [Complex.conjAe]
  have e : ω.toMonoidHom.comp f = f.comp compactMatrixConjugation := by
    apply rankOne_hom_ext
    · intro z
      change ω (f (upper z)) = f (compactMatrixConjugation (upper z))
      rw [compactMatrixConjugation_upper, h]
    · intro z
      change ω (f (lower z)) = f (compactMatrixConjugation (lower z))
      rw [compactMatrixConjugation_lower, ← hω (f (upper (-Complex.conjAe z))), h, hc]
  rintro _ ⟨m, rfl⟩
  change ω (f (unitaryToSpecialLinear m)) = f (unitaryToSpecialLinear m)
  have hm := DFunLike.congr_fun e (unitaryToSpecialLinear m)
  change ω (f (unitaryToSpecialLinear m)) =
    f (compactMatrixConjugation (unitaryToSpecialLinear m)) at hm
  rwa [compactMatrixConjugation_fixed] at hm

end CompactRankOne

section UnitaryTopology

open scoped Matrix

private def unitaryForm (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, b; -star b, star a]

private theorem unitaryForm_mem (a b : ℂ)
    (h : Complex.normSq a + Complex.normSq b = 1) :
    unitaryForm a b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hd : a * star a + b * star b = 1 := by
    simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, mul_comm a,
      mul_comm b, ← Complex.ofReal_add, Complex.ofReal_inj, Complex.ofReal_one] using
      congrArg Complex.ofReal h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [unitaryForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
    all_goals first | exact hd | (
      change star b * b + star a * a = 1
      calc
        _ = a * star a + b * star b := by ring
        _ = 1 := hd) | ring
  · simpa [unitaryForm, Matrix.det_fin_two] using hd

private theorem unitaryForm_of_mem (m : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    m.val = unitaryForm (m.val 0 0) (m.val 0 1) ∧
      Complex.normSq (m.val 0 0) + Complex.normSq (m.val 0 1) = 1 := by
  let a := m.val 0 0
  let b := m.val 0 1
  have h := congrArg Inv.inv (compactMatrixConjugation_fixed m)
  change (adjointMatrix (unitaryToSpecialLinear m))⁻¹⁻¹ = (unitaryToSpecialLinear m)⁻¹ at h
  rw [inv_inv] at h
  have hm : star m.val = Matrix.adjugate m.val := congrArg Subtype.val h
  rw [Matrix.adjugate_fin_two, Matrix.star_eq_conjTranspose] at hm
  have h₁ : m.val 1 1 = star a := by
    have p := congrFun (congrFun hm 0) 0
    exact p.symm
  have h₂ : m.val 1 0 = -star b := by
    have p := congrFun (congrFun hm 1) 0
    change star b = -m.val 1 0 at p
    rw [p, neg_neg]
  have he : m.val = unitaryForm a b := by
    ext r s
    fin_cases r <;> fin_cases s
    · rfl
    · rfl
    · exact h₂
    · exact h₁
  refine ⟨he, ?_⟩
  have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp m.property).2
  have hsum : a * star a + b * star b = 1 := by
    rw [Matrix.det_fin_two, h₁, h₂] at hdet
    simpa [a, b] using hdet
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, Complex.ofReal_one]
  change (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) = 1
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  change star a * a + star b * b = 1
  rw [mul_comm (star a), mul_comm (star b), hsum]

private theorem specialUnitary_connected : ConnectedSpace ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  let V := EuclideanSpace ℝ (Fin 4)
  let Q := Metric.sphere (0 : V) 1
  have hrank : 1 < Module.rank ℝ V := by
    have hfin : Module.finrank ℝ V = 4 := finrank_euclideanSpace_fin
    rw [← Module.finrank_eq_rank, hfin]
    norm_num
  let : ConnectedSpace Q := isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  let a (v : V) : ℂ := ⟨v 0, v 1⟩
  let b (v : V) : ℂ := ⟨v 2, v 3⟩
  have hnorm (v : V) : Complex.normSq (a v) + Complex.normSq (b v) = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    change v 0 * v 0 + v 1 * v 1 + (v 2 * v 2 + v 3 * v 3) =
      v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2
    ring
  let f (v : Q) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    ⟨unitaryForm (a v.val) (b v.val), unitaryForm_mem _ _ (by
      have hv : ‖v.val‖ = 1 := by
        have h := v.property
        simpa only [Q, Metric.mem_sphere, dist_zero_right] using h
      rw [hnorm, hv, one_pow])⟩
  have hv (j : Fin 4) : Continuous (fun v : Q => v.val j) :=
    (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val
  have ha : Continuous (fun v : Q => a v.val) := by
    have ha' (v : Q) : a v.val = (v.val 0 : ℂ) + (v.val 1 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [a, Complex.mul_re, Complex.mul_im]
    simp_rw [ha']
    exact (Complex.continuous_ofReal.comp (hv 0)).add
      ((Complex.continuous_ofReal.comp (hv 1)).mul continuous_const)
  have hb : Continuous (fun v : Q => b v.val) := by
    have hb' (v : Q) : b v.val = (v.val 2 : ℂ) + (v.val 3 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [b, Complex.mul_re, Complex.mul_im]
    simp_rw [hb']
    exact (Complex.continuous_ofReal.comp (hv 2)).add
      ((Complex.continuous_ofReal.comp (hv 3)).mul continuous_const)
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro r s
    fin_cases r <;> fin_cases s
    · exact ha
    · exact hb
    · exact (Complex.continuous_conj.comp hb).neg
    · exact Complex.continuous_conj.comp ha
  have hs : Function.Surjective f := by
    intro m
    obtain ⟨hm, hnormm⟩ := unitaryForm_of_mem m
    let v : V := WithLp.toLp 2 ![(m.val 0 0).re, (m.val 0 0).im,
      (m.val 0 1).re, (m.val 0 1).im]
    have h₁ : a v = m.val 0 0 := by apply Complex.ext <;> rfl
    have h₂ : b v = m.val 0 1 := by apply Complex.ext <;> rfl
    have hsq : ‖v‖ ^ 2 = 1 := (hnorm v).symm.trans (by rw [h₁, h₂, hnormm])
    have hmem : v ∈ Q := by
      change dist v (0 : V) = 1
      rw [dist_zero_right]
      nlinarith [norm_nonneg v]
    exact ⟨⟨v, hmem⟩, Subtype.ext (show unitaryForm (a v) (b v) = m.val from by
      rw [h₁, h₂, ← hm])⟩
  exact hs.connectedSpace hc

end UnitaryTopology

section MarkedCompactRankOne

open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.AbstractPairing (Root)

/-- The linked rank-one map evaluated on the original matrix-topologized group. -/
private theorem exists_markedRankOne {A : AdditiveLine ℂ} (M : MarkedPair G A)
    (α : Root M.P.pair.T) (p n : A.group ⟶ M.P.pair.G.val)
    (r : CorootReflection M.P.pair.T α.val p n)
    (hp : HasScalarAction M.P.pair.T α.val p) (hn : HasScalarAction M.P.pair.T α.val⁻¹ n) :
    ∃ f : SL₂ ℂ →* AdelicGroups.PointsIn i ℂ, Continuous f ∧
      (∀ z, f (upper z) = M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z)) ∧
      (∀ z, f (lower z) = M.onPoints (i := i) (𝟙 _) (rootPoint n complexTest z)) ∧
      ∀ t, f (diagonal t) = M.onPoints (i := i) M.P.pair.T.inclusion
        (cocharacterPoint r.coroot complexTest t) := by
  obtain ⟨F, hup, hlo, hd⟩ := linkedRankOne_matrixHom M.P.pair α p n r hp hn
  let f := (markedPointMap (i := i) M (𝟙 _)).comp F
  have hu (z) : f (upper z) = M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z) := by
    change markedPointMap (i := i) M (𝟙 _) (F (upper z)) = _
    rw [hup, markedPointMap_apply]
  have hl (z) : f (lower z) = M.onPoints (i := i) (𝟙 _) (rootPoint n complexTest z) := by
    change markedPointMap (i := i) M (𝟙 _) (F (lower z)) = _
    rw [hlo, markedPointMap_apply]
  refine ⟨f, continuous_rankOne_hom f ?_ ?_, hu, hl, ?_⟩
  · simp_rw [hu]
    exact continuous_markedRootPoint M p
  · simp_rw [hl]
    exact continuous_markedRootPoint M n
  · intro t
    change markedPointMap (i := i) M (𝟙 _) (F (diagonal t)) = _
    rw [hd]
    exact markedPointMap_eval M _ _

private theorem connected_range_in_component {X H : Type*} [Group X] [TopologicalSpace X]
    [ConnectedSpace X] [Group H] [TopologicalSpace H] (f : X →* H) (hf : Continuous f)
    {J : Subgroup H} (hJ : Set.range f ⊆ (J : Set H)) :
    Set.range f ⊆ identityComponent J := by
  let F (x : X) : J := ⟨f x, hJ ⟨x, rfl⟩⟩
  have hcont : Continuous F := hf.subtype_mk _
  rintro _ ⟨x, rfl⟩
  refine ⟨F x, ?_, rfl⟩
  have h1 : F 1 = 1 := Subtype.ext (map_one f)
  have hx : x ∈ connectedComponent (1 : X) := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  exact h1 ▸ hcont.image_connectedComponent_subset 1 ⟨x, hx, rfl⟩

private theorem marked_torus_conj_root (D : MarkedTorus ω θ S) (α : Root D.M.P.pair.T)
    (p : D.A.group ⟶ D.M.P.pair.G.val) (hp : HasScalarAction D.M.P.pair.T α.val p)
    (x : E6Space) (z : ℂ) :
    MulAut.conj (D.exp x) (D.M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest z)) =
      D.M.onPoints (i := i) (𝟙 _) (rootPoint p complexTest
        (characterValue α.val complexTest (D.M.torusPoint x) * z)) := by
  let Q := D.M.P.pair.G.val
  let t := schemePointHom D.M.P.pair.T.inclusion (D.M.torusPoint x)
  let F := markedPointMap (i := i) D.M (𝟙 Q)
  have ht : F t = D.exp x := markedPointMap_eval D.M _ _
  have h : t * rootPoint p complexTest z * t⁻¹ = rootPoint p complexTest
      (characterValue α.val complexTest (D.M.torusPoint x) * z) :=
    hp complexTest (D.M.torusPoint x) z
  have h' := congrArg F h
  rwa [map_mul, map_mul, map_inv, ht, markedPointMap_apply, markedPointMap_apply] at h'

private theorem diagonal_from_circle (s : ℝ) (a : SU₂)
    (h : a.val = Matrix.diagonal
      (![↑(Circle.exp (2 * Real.pi * s)), ↑((Circle.exp (2 * Real.pi * s))⁻¹)] :
        Fin 2 → ℂ)) :
    unitaryToSpecialLinear a = diagonal (Circle.toUnits (Circle.exp (2 * Real.pi * s))) := by
  apply Subtype.ext
  change a.val = _
  rw [h]
  ext r t
  fin_cases r <;> fin_cases t <;> rfl

private theorem exists_unitaryDiagonal (s : ℝ) :
    ∃ a : SU₂, a.val = Matrix.diagonal
      (![↑(Circle.exp (2 * Real.pi * s)), ↑((Circle.exp (2 * Real.pi * s))⁻¹)] :
        Fin 2 → ℂ) := by
  let u := Circle.exp (2 * Real.pi * s)
  refine ⟨⟨unitaryForm u 0, unitaryForm_mem u 0 (by simp)⟩, ?_⟩
  change unitaryForm u 0 = Matrix.diagonal (![↑u, ↑u⁻¹] : Fin 2 → ℂ)
  ext r t
  fin_cases r <;> fin_cases t <;> simp [unitaryForm]
  exact (Circle.coe_inv_eq_conj u).symm

private def unitaryWeylMatrix : SU₂ :=
  ⟨unitaryForm 0 1, unitaryForm_mem 0 1 (by simp)⟩

private theorem unitaryWeylMatrix_val : unitaryWeylMatrix.val = !![0, 1; -1, 0] := by
  simp [unitaryWeylMatrix, unitaryForm]

private theorem unitaryWeylMatrix_eq_word :
    unitaryToSpecialLinear unitaryWeylMatrix = elementaryWeyl 1 := by
  apply Subtype.ext
  change unitaryWeylMatrix.val = (elementaryWeyl 1).val
  rw [unitaryWeylMatrix_val, elementaryWeyl_val]
  simp

/-- A diagram-fixed simple root gives the required compact rank-one map whenever
its wall passes through the normalized compact logarithm. -/
private theorem fixed_simple_wall_group (D : MarkedTorus ω θ S)
    (hω : Function.Involutive ω) (x : E6Space) (j : Fin 6)
    (hj : Specs.AbsoluteDynkinTypes.E6Reflection j = j) (hwall : OnWall (Pi.single j 1) x) :
    D.RealizesFoldedRoot x (Pi.single j 1) := by
  let p := D.M.simpleCoordinate j
  let α := (D.M.simple j).val
  obtain ⟨n, r, hn, hcoroot, hωroot⟩ := D.compactPinning j
  let hp : HasScalarAction D.M.P.pair.T α.val p := (D.M.P.pin (D.M.simple j)).property
  obtain ⟨f, hcont, hu, hl, hd⟩ := exists_markedRankOne (i := i) D.M α p n r hp hn
  have hωf (z : ℂ) : ω (f (upper z)) = f (lower (-Complex.conjAe z)) := by
    rw [hu, hl]
    exact hωroot z
  have ht : characterValue α.val complexTest (D.M.torusPoint x) = 1 := by
    obtain ⟨k, hk⟩ := hwall
    rw [simple_coroot_reflection] at hk
    change characterValue (D.M.simple j).val.val complexTest (D.M.torusPoint x) = 1
    rw [D.rootEvaluation, simple_evaluation, hk, Circle.exp_two_pi_mul_int, Circle.coe_one]
  have hδu (z : ℂ) : D.δ (f (upper z)) = f (upper z) := by
    rw [hu]
    have h := positive_root_diagram D j z
    rw [hj] at h
    exact h
  have hδf : D.δ.toMonoidHom.comp f = f := by
    apply rankOne_hom_ext
    · exact hδu
    · intro z
      have hz : -Complex.conjAe (-Complex.conjAe z) = z := by simp [Complex.conjAe]
      change D.δ (f (lower z)) = f (lower z)
      rw [← hz, ← hωf, D.diagramCommutes, hδu]
  have hτu (z : ℂ) : D.twisted x (f (upper z)) = f (upper z) := by
    change MulAut.conj (D.exp x) (D.δ (f (upper z))) = _
    rw [hδu, hu, marked_torus_conj_root D α p hp, ht, one_mul]
  have hτcommutes : Function.Commute (D.twisted x) ω := by
    have htx : ω (D.exp x) = D.exp x :=
      torus_subset_compact D (exp_mem D x)
    intro g
    change MulAut.conj (D.exp x) (D.δ (ω g)) = ω (MulAut.conj (D.exp x) (D.δ g))
    rw [D.diagramCommutes, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, htx]
  have hτf : (D.twisted x).toMonoidHom.comp f = f := by
    apply rankOne_hom_ext
    · exact hτu
    · intro z
      have hz : -Complex.conjAe (-Complex.conjAe z) = z := by simp [Complex.conjAe]
      change D.twisted x (f (lower z)) = f (lower z)
      rw [← hz, ← hωf, hτcommutes, hτu]
  let F := f.comp unitaryToSpecialLinear
  have hJ : Set.range F ⊆ (D.fixedAt x : Set _) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨compact_rankOne_range ω hω f hωf ⟨u, rfl⟩,
      DFunLike.congr_fun hτf (unitaryToSpecialLinear u)⟩
  let : ConnectedSpace SU₂ := specialUnitary_connected
  have hc : Continuous F := hcont.comp continuous_unitaryToSpecialLinear
  refine ⟨F, hc, connected_range_in_component F hc hJ, ?_, ?_⟩
  · intro s
    obtain ⟨a, ha⟩ := exists_unitaryDiagonal s
    refine ⟨a, ha, ?_⟩
    change f (unitaryToSpecialLinear a) = _
    rw [diagonal_from_circle s a ha, hd, hcoroot, simple_coroot_reflection]
    change _ = D.M.onPoints D.M.P.pair.T.inclusion (D.M.torusPoint (s • Pi.single j 1))
    rw [torusPoint_on_coroot]
  · let a := unitaryWeylMatrix
    have ha : F a = markedPointMap (i := i) D.M (𝟙 _)
        (rankOneWord p n complexTest 1) := by
      change f (unitaryToSpecialLinear unitaryWeylMatrix) = _
      rw [unitaryWeylMatrix_eq_word]
      simp only [elementaryWeyl, rankOneWord, map_mul, hu, hl, markedPointMap_apply]
    have hlabel := simple_word_represents D j n r hn hcoroot
    change D.RepresentsWeyl _ (reflection (Pi.single j 1)) at hlabel
    rw [← ha] at hlabel
    have hδ : F a ∈ fixedSubgroup D.δ :=
      DFunLike.congr_fun hδf (unitaryToSpecialLinear a)
    refine ⟨a, unitaryWeylMatrix_val,
      diagram_lift_normalizes D hδ (Submonoid.subset_closure ⟨j, rfl⟩) hlabel, ?_⟩
    exact fun y _ => hlabel y

end MarkedCompactRankOne

section OrthogonalSimpleRoots

open RootPairing

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum Idx X Y) (base : P.Base)

private theorem two_simple_sum_has_consistent_sign {j k : base.support}
    (hne : j ≠ k) (a b : ℤ)
    (h : a • P.root j.val + b • P.root k.val ∈ Set.range P.root) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  classical
  let f : Idx → ℤ := Pi.single j.val a + Pi.single k.val b
  have hsupp : f.support ⊆ base.support := by
    intro i hi
    by_contra h
    have hj : i ≠ j.val := fun e => h (e.symm ▸ j.property)
    have hk : i ≠ k.val := fun e => h (e.symm ▸ k.property)
    exact hi (by simp [f, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hk])
  have hsum (l : base.support) (c : ℤ) :
      ∑ i ∈ base.support, (Pi.single l.val c : Idx → ℤ) i • P.root i =
        c • P.root l.val := by
    rw [Finset.sum_eq_single_of_mem _ l.property]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
  have he : ∑ i ∈ base.support, f i • P.root i = a • P.root j.val + b • P.root k.val := by
    simp only [f, Pi.add_apply, add_smul, Finset.sum_add_distrib, hsum]
  have hne' : j.val ≠ k.val := fun he => hne (Subtype.ext he)
  have hj' : f j.val = a := by simp [f, Pi.single_eq_of_ne hne']
  have hk' : f k.val = b := by simp [f, Pi.single_eq_of_ne hne'.symm]
  rcases base.pos_or_neg_of_sum_smul_root_mem f (he.symm ▸ h) hsupp with hp | hn
  · exact Or.inl ⟨hj' ▸ (le_of_lt hp) j.val, hk' ▸ (le_of_lt hp) k.val⟩
  · exact Or.inr ⟨hj' ▸ (le_of_lt hn) j.val, hk' ▸ (le_of_lt hn) k.val⟩

/-- A root using two orthogonal simple directions must have zero coefficient
in at least one direction. Reflections independently change their signs. -/
private theorem orthogonal_simple_no_mixed_root {j k : base.support} (hne : j ≠ k)
    (hzero : P.pairing k.val j.val = 0) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a • P.root j.val + b • P.root k.val ∉ Set.range P.root := by
  intro h
  have hs := two_simple_sum_has_consistent_sign P base hne a b h
  obtain ⟨r, hr⟩ := h
  have hreflection : P.reflection j.val (a • P.root j.val + b • P.root k.val) =
      (-a) • P.root j.val + b • P.root k.val := by
    rw [map_add, map_smul, map_smul, P.reflection_apply_self, P.reflection_apply_root, hzero]
    simp
  have he : (-a) • P.root j.val + b • P.root k.val ∈ Set.range P.root :=
    ⟨P.reflectionPerm j.val r,
      (P.root_reflectionPerm _ _).trans ((congrArg (P.reflection j.val) hr).trans hreflection)⟩
  have hs' := two_simple_sum_has_consistent_sign P base hne (-a) b he
  omega

end OrthogonalSimpleRoots

section CommutingRootGroups

open Specs.AbstractPairing (Root)
open Specs.RootGroups (Proportional)
open Specs.CharacterPairing (absoluteRoots)
open Additive
open private oppositeRoot oppositeRoot_val linked_coroot
  from LinearAlgebraicGroups.Classification.RankTwoLifting
open private exists_weylIdentification
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private linked_representative_eq
  from LinearAlgebraicGroups.Classification.NormalizerComparison

private theorem compact_negative_in_root_group (D : MarkedTorus ω θ S) (j : Fin 6)
    (n : D.A.group ⟶ D.M.P.pair.G.val)
    (r : CorootReflection D.M.P.pair.T (D.M.simple j).val.val (D.M.simpleCoordinate j) n)
    (hn : HasScalarAction D.M.P.pair.T (D.M.simple j).val.val⁻¹ n) :
    letI := D.M.datum.comm
    let b := oppositeRoot D.M.datum.datum (D.M.simple j).val
    ∀ z : ℂ, rootPoint n complexTest z ∈
      Set.range (schemePointHom (D.M.P.roots b).val.inclusion) := by
  let := D.M.datum.comm
  let a := (D.M.simple j).val
  let b := oppositeRoot D.M.datum.datum a
  dsimp only
  have hβ : b.val = a.val⁻¹ := oppositeRoot_val D.M.datum.datum a
  obtain ⟨q, ⟨s⟩⟩ := Classification.RankTwoRelations.linkedOppositeCoordinate
    D.M.P a b hβ (D.M.P.pin (D.M.simple j))
  let n' := q.val.hom ≫ (D.M.P.roots b).val.inclusion
  have hn' : HasScalarAction D.M.P.pair.T a.val⁻¹ n' := hβ ▸ q.property
  obtain ⟨W⟩ := exists_weylIdentification D.M.P.pair D.M.datum
  have hrep : r.representative = s.representative :=
    linked_representative_eq D.M.datum W r s rfl
      ((linked_coroot D.M.datum.datum a r).trans (linked_coroot D.M.datum.datum a s).symm)
      (D.M.P.pin (D.M.simple j)).property hn hn'
  intro z
  let P := D.M.P.pair
  have h₁ := (Classification.RankOneRelations.oppositeRootRelations P.G P.reductive P.T
    P.split P.maximal a.val a.property (D.M.simpleCoordinate j) n r
    (D.M.P.pin (D.M.simple j)).property hn complexTest).2.2 (-z)
  have h₂ := (Classification.RankOneRelations.oppositeRootRelations P.G P.reductive P.T
    P.split P.maximal a.val a.property (D.M.simpleCoordinate j) n' s
    (D.M.P.pin (D.M.simple j)).property hn' complexTest).2.2 (-z)
  rw [hrep, neg_neg] at h₁
  rw [neg_neg] at h₂
  exact ⟨rootPoint q.val.hom complexTest z,
    ((rootPoint_comp q.val.hom (D.M.P.roots b).val.inclusion complexTest z).symm.trans
      (h₂.symm.trans h₁))⟩

private theorem signed_roots_commute_of_orthogonal_simple (D : MarkedTorus ω θ S) (j k : Fin 6)
    (hne : j ≠ k) (hzero : CartanMatrix.E 6 j k = 0) (a b : Root D.M.P.pair.T)
    (p q : ℤ) (hp : p ≠ 0) (hq : q ≠ 0)
    (ha : letI := D.M.datum.comm
      D.M.datum.datum.rootDatum.root a = p • D.M.datum.datum.rootDatum.root (D.M.simple j).val)
    (hb : letI := D.M.datum.comm
      D.M.datum.datum.rootDatum.root b = q • D.M.datum.datum.rootDatum.root (D.M.simple k).val) :
    ∀ g h : GroupPoints D.M.P.pair.G.val complexTest,
      g ∈ Set.range (schemePointHom (D.M.P.roots a).val.inclusion) →
      h ∈ Set.range (schemePointHom (D.M.P.roots b).val.inclusion) → Commute g h := by
  let := D.M.datum.comm
  let P := D.M.datum.datum.rootDatum
  let r := D.M.numbering.symm j
  let s := D.M.numbering.symm k
  have hne' : r ≠ s := fun h => hne (D.M.numbering.symm.injective h)
  have hz : P.pairing s.val r.val = 0 := by
    have h := D.cartan r s
    change P.pairing s.val r.val = CartanMatrix.E 6 (D.M.numbering r) (D.M.numbering s) at h
    rw [show D.M.numbering r = j from Equiv.apply_symm_apply _ _,
      show D.M.numbering s = k from Equiv.apply_symm_apply _ _, hzero] at h
    exact h
  change P.root a = p • P.root r.val at ha
  change P.root b = q • P.root s.val at hb
  have P_datum_root_eq (c : Root D.M.P.pair.T) :
      P.root c = Additive.ofMul c.val := D.M.datum.datum.root_eq c
  have hind : ¬ Proportional a.val b.val := by
    rintro ⟨m, n, hm, hn, he⟩
    have e := congrArg Additive.ofMul he
    rw [ofMul_zpow, ofMul_zpow, ← P_datum_root_eq a, ← P_datum_root_eq b, ha, hb] at e
    have e' := congrArg (fun z => P.toLinearMap z (P.coroot r.val)) e
    simp only [map_smul, LinearMap.smul_apply, RootPairing.root_coroot_eq_pairing, P.pairing_same,
      hz, smul_zero, Int.zsmul_eq_mul] at e'
    exact (mul_ne_zero hm (mul_ne_zero hp (show (2 : ℤ) ≠ 0 by decide))) e'
  have hcone (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      a.val ^ m * b.val ^ n ∉ absoluteRoots D.M.P.pair.T := by
    intro h
    let c : Root D.M.P.pair.T := ⟨_, h⟩
    have hc : P.root c = (m : ℤ) • P.root a + (n : ℤ) • P.root b := by
      rw [P_datum_root_eq, P_datum_root_eq, P_datum_root_eq]
      change Additive.ofMul (a.val ^ m * b.val ^ n) = _
      simp
    rw [ha, hb, smul_smul, smul_smul] at hc
    exact orthogonal_simple_no_mixed_root P D.M.datum.base hne' hz
      (mul_ne_zero (by exact_mod_cast hm.ne') hp) (mul_ne_zero (by exact_mod_cast hn.ne') hq)
      ⟨c, hc⟩
  rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
  exact Classification.RankOneRelations.independentRootCommutation
    D.M.P.pair.G D.M.P.pair.reductive D.M.P.pair.T D.M.P.pair.split D.M.P.pair.maximal
    a.val a.property b.val b.property hind hcone (D.M.P.roots a).val (D.M.P.roots b).val
    (D.M.P.roots a).property (D.M.P.roots b).property complexTest g h

end CommutingRootGroups

section SimpleRankOneMaps

open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.AbstractPairing (Root)
open private oppositeRoot oppositeRoot_val from LinearAlgebraicGroups.Classification.RankTwoLifting

private structure SimpleRankOneMap (D : MarkedTorus ω θ S) (j : Fin 6) where
  neg : D.A.group ⟶ D.M.P.pair.G.val
  link : CorootReflection D.M.P.pair.T (D.M.simple j).val.val (D.M.simpleCoordinate j) neg
  negAction : HasScalarAction D.M.P.pair.T (D.M.simple j).val.val⁻¹ neg
  coroot_eq : link.coroot = D.M.coroot j
  f : SL₂ ℂ →* AdelicGroups.PointsIn i ℂ
  continuous : Continuous f
  upper_eq : ∀ z, f (upper z) =
    D.M.onPoints (i := i) (𝟙 _) (rootPoint (D.M.simpleCoordinate j) complexTest z)
  lower_eq : ∀ z, f (lower z) =
    D.M.onPoints (i := i) (𝟙 _) (rootPoint neg complexTest z)
  diagonal_eq : ∀ t, f (diagonal t) = D.M.onPoints (i := i) D.M.P.pair.T.inclusion
    (cocharacterPoint link.coroot complexTest t)
  compact : ∀ z : ℂ, ω (f (upper z)) = f (lower (-Complex.conjAe z))

private theorem simpleRankOneMap_exists (D : MarkedTorus ω θ S) (j : Fin 6) :
    Nonempty (SimpleRankOneMap D j) := by
  obtain ⟨n, r, hn, hcoroot, hωroot⟩ := D.compactPinning j
  obtain ⟨f, hc, hu, hl, hd⟩ := exists_markedRankOne (i := i) D.M (D.M.simple j).val
    (D.M.simpleCoordinate j) n r (D.M.P.pin (D.M.simple j)).property hn
  exact ⟨⟨n, r, hn, hcoroot, f, hc, hu, hl, hd,
    fun z => by rw [hu, hl]; exact hωroot z⟩⟩

private theorem rankOneMap_weyl (D : MarkedTorus ω θ S) (j : Fin 6)
    (U : SimpleRankOneMap D j) :
    D.RepresentsWeyl (U.f (elementaryWeyl 1)) (reflection (Pi.single j 1)) := by
  have hword : U.f (elementaryWeyl 1) = markedPointMap (i := i) D.M (𝟙 _)
      (rankOneWord (D.M.simpleCoordinate j) U.neg complexTest 1) := by
    simp only [elementaryWeyl, map_mul, rankOneWord, U.upper_eq, U.lower_eq, markedPointMap_apply]
  rw [hword]
  exact simple_word_represents D j U.neg U.link U.negAction U.coroot_eq

private theorem rankOneMap_diagram (D : MarkedTorus ω θ S) {j k : Fin 6}
    (U : SimpleRankOneMap D j) (V : SimpleRankOneMap D k)
    (h : Specs.AbsoluteDynkinTypes.E6Reflection j = k) :
    D.δ.toMonoidHom.comp U.f = V.f := by
  have hu (z : ℂ) : D.δ (U.f (upper z)) = V.f (upper z) := by
    rw [U.upper_eq, V.upper_eq]
    have e := positive_root_diagram D j z
    rw [h] at e
    exact e
  apply rankOne_hom_ext hu
  intro z
  have hz : -Complex.conjAe (-Complex.conjAe z) = z := by simp [Complex.conjAe]
  change D.δ (U.f (lower z)) = V.f (lower z)
  rw [← hz, ← U.compact, ← V.compact, D.diagramCommutes, hu]

private theorem commute_rankOne_maps {H : Type*} [Group H] (f g : SL₂ ℂ →* H)
    (h₁ : ∀ u v, Commute (f (upper u)) (g (upper v)))
    (h₂ : ∀ u v, Commute (f (upper u)) (g (lower v)))
    (h₃ : ∀ u v, Commute (f (lower u)) (g (upper v)))
    (h₄ : ∀ u v, Commute (f (lower u)) (g (lower v))) :
    ∀ a b, Commute (f a) (g b) := by
  have he (x y : H) : MulAut.conj x y = y ↔ Commute x y :=
    mul_inv_eq_iff_eq_mul
  have hfix (x : H)
      (hu : ∀ v, Commute x (g (upper v))) (hl : ∀ v, Commute x (g (lower v))) :
      ∀ v, Commute x (g v) := by
    have h : (MulAut.conj x).toMonoidHom.comp g = g :=
      rankOne_hom_ext (fun v => (he _ _).2 (hu v)) (fun v => (he _ _).2 (hl v))
    exact fun v => (he _ _).1 (DFunLike.congr_fun h v)
  intro a b
  have h := rankOne_hom_ext
    (f := (MulAut.conj (g b)).toMonoidHom.comp f) (g := f)
    (fun u => (he _ _).2 ((hfix _ (h₁ u) (h₂ u) b).symm))
    (fun u => (he _ _).2 ((hfix _ (h₃ u) (h₄ u) b).symm))
  exact ((he _ _).1 (DFunLike.congr_fun h a)).symm

private theorem orthogonal_rankOne_maps_commute (D : MarkedTorus ω θ S)
    {j k : Fin 6} (hne : j ≠ k) (hzero : CartanMatrix.E 6 j k = 0)
    (U : SimpleRankOneMap D j) (V : SimpleRankOneMap D k) :
    ∀ a b, Commute (U.f a) (V.f b) := by
  let := D.M.datum.comm
  let R := D.M.datum.datum.rootDatum
  let a := (D.M.simple j).val
  let b := (D.M.simple k).val
  let na := oppositeRoot D.M.datum.datum a
  let nb := oppositeRoot D.M.datum.datum b
  have hna : R.root na = (-1 : ℤ) • R.root a := by
    change D.M.datum.datum.rootDatum.root na = _
    rw [D.M.datum.datum.root_eq, D.M.datum.datum.root_eq, oppositeRoot_val]
    simp
  have hnb : R.root nb = (-1 : ℤ) • R.root b := by
    change D.M.datum.datum.rootDatum.root nb = _
    rw [D.M.datum.datum.root_eq, D.M.datum.datum.root_eq, oppositeRoot_val]
    simp
  have hrange (l : Fin 6) (z : ℂ) :
      rootPoint (D.M.simpleCoordinate l) complexTest z ∈
        Set.range (schemePointHom (D.M.P.roots (D.M.simple l).val).val.inclusion) := by
    refine ⟨rootPoint (D.M.P.pin (D.M.simple l)).val.hom complexTest z, ?_⟩
    exact (rootPoint_comp (D.M.P.pin (D.M.simple l)).val.hom
      (D.M.P.roots (D.M.simple l).val).val.inclusion complexTest z).symm
  have hUneg := compact_negative_in_root_group D j U.neg U.link U.negAction
  have hVneg := compact_negative_in_root_group D k V.neg V.link V.negAction
  let F := markedPointMap (i := i) D.M (𝟙 _)
  have map_commute {x y : GroupPoints D.M.P.pair.G.val complexTest} (h : Commute x y) :
      Commute (D.M.onPoints (i := i) (𝟙 _) x) (D.M.onPoints (i := i) (𝟙 _) y) := h.map F
  apply commute_rankOne_maps
  · intro u v
    rw [U.upper_eq, V.upper_eq]
    exact map_commute (signed_roots_commute_of_orthogonal_simple D j k hne hzero a b
      1 1 one_ne_zero one_ne_zero (by simp [a]) (by simp [b]) _ _ (hrange j u) (hrange k v))
  · intro u v
    rw [U.upper_eq, V.lower_eq]
    exact map_commute (signed_roots_commute_of_orthogonal_simple D j k hne hzero a nb
      1 (-1) one_ne_zero (by decide) (by simp [a]) hnb _ _ (hrange j u) (hVneg v))
  · intro u v
    rw [U.lower_eq, V.upper_eq]
    exact map_commute (signed_roots_commute_of_orthogonal_simple D j k hne hzero na b
      (-1) 1 (by decide) one_ne_zero hna (by simp [b]) _ _ (hUneg u) (hrange k v))
  · intro u v
    rw [U.lower_eq, V.lower_eq]
    exact map_commute (signed_roots_commute_of_orthogonal_simple D j k hne hzero na nb
      (-1) (-1) (by decide) (by decide) hna hnb _ _ (hUneg u) (hVneg v))

end SimpleRankOneMaps

section PairedWalls

open Specs.IntegralRootRelations (upper lower diagonal)

private theorem twisted_commutes_compact (D : MarkedTorus ω θ S) (x : E6Space) :
    Function.Commute (D.twisted x) ω := by
  have htx : ω (D.exp x) = D.exp x :=
    torus_subset_compact D (exp_mem D x)
  intro g
  change MulAut.conj (D.exp x) (D.δ (ω g)) = ω (MulAut.conj (D.exp x) (D.δ g))
  rw [D.diagramCommutes, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, htx]

private theorem fixedAt_normalizes_of_label (D : MarkedTorus ω θ S) (x : E6Space)
    {n : AdelicGroups.PointsIn i ℂ} (hn : n ∈ D.fixedAt x)
    {w : Function.End E6Space} (hw : w ∈ e6Weyl) (hrep : D.RepresentsWeyl n w) :
    n ∈ Subgroup.normalizer (S : Set _) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  have hh (v : AdelicGroups.PointsIn i ℂ) : v ∈ S ↔ v ∈ D.T ∧ v ∈ D.fixedAt x :=
    SetLike.ext_iff.mp (fixed_torus_kernel D x).symm v
  change g ∈ S ↔ MulAut.conj n g ∈ S
  have hJ : g ∈ D.fixedAt x ↔ MulAut.conj n g ∈ D.fixedAt x := by
    constructor
    · intro hg
      exact (D.fixedAt x).mul_mem ((D.fixedAt x).mul_mem hn hg) ((D.fixedAt x).inv_mem hn)
    · intro hg
      have h := (D.fixedAt x).mul_mem ((D.fixedAt x).mul_mem ((D.fixedAt x).inv_mem hn) hg) hn
      change n⁻¹ * (n * g * n⁻¹) * n ∈ D.fixedAt x at h
      simpa only [mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  rw [hh, hh, conj_mem_torus_iff D hw hrep, hJ]

private theorem exp_simpleRankOne_diagonal (D : MarkedTorus ω θ S)
    (j : Fin 6) (U : SimpleRankOneMap D j) (s : ℝ) :
    U.f (diagonal (Circle.toUnits (Circle.exp (2 * Real.pi * s)))) =
      D.exp (s • Pi.single j 1) := by
  rw [U.diagonal_eq, U.coroot_eq]
  change _ = D.M.onPoints D.M.P.pair.T.inclusion (D.M.torusPoint (s • Pi.single j 1))
  rw [torusPoint_on_coroot]

private theorem pairedWord_in_e6Weyl (j k : Fin 6) :
    reflection (Pi.single j 1) * reflection (Pi.single k 1) ∈ e6Weyl :=
  e6Weyl.mul_mem (Submonoid.subset_closure ⟨j, rfl⟩) (Submonoid.subset_closure ⟨k, rfl⟩)

private theorem paired_wall_group (D : MarkedTorus ω θ S)
    (hω : Function.Involutive ω) (x : E6Space) (hτ : Function.Involutive (D.twisted x))
    {j k : Fin 6} (hswap : Specs.AbsoluteDynkinTypes.E6Reflection j = k)
    (hne : j ≠ k) (hzero : CartanMatrix.E 6 j k = 0) (β : E6Space)
    (hβ : foldedCoroot β = Pi.single j 1 + Pi.single k 1)
    (hwall : Set.EqOn (reflection (Pi.single j 1) * reflection (Pi.single k 1))
      (reflection β) foldedSpace) :
    D.RealizesFoldedRoot x β := by
  obtain ⟨U⟩ := simpleRankOneMap_exists D j
  obtain ⟨V⟩ := simpleRankOneMap_exists D k
  let τ := D.twisted x
  let v := τ.toMonoidHom.comp U.f
  have hδ (a : SL₂ ℂ) : D.δ (U.f a) = V.f a :=
    DFunLike.congr_fun (rankOneMap_diagram D U V hswap) a
  have hv (a : SL₂ ℂ) : v a = MulAut.conj (D.exp x) (V.f a) := by
    change MulAut.conj (D.exp x) (D.δ (U.f a)) = _
    rw [hδ]
  have hτc : Function.Commute τ ω := twisted_commutes_compact D x
  let c := characterValue (D.M.simple k).val.val complexTest (D.M.torusPoint x)
  have hvup (z : ℂ) : v (upper z) = V.f (upper (c * z)) := by
    rw [hv, V.upper_eq, V.upper_eq, marked_torus_conj_root D (D.M.simple k).val
      (D.M.simpleCoordinate k) (D.M.P.pin (D.M.simple k)).property]
  have hvlo (z : ℂ) : v (lower z) = V.f (lower (-Complex.conjAe (c * (-Complex.conjAe z)))) := by
    have hz : -Complex.conjAe (-Complex.conjAe z) = z := by simp [Complex.conjAe]
    have he : v (lower z) = ω (v (upper (-Complex.conjAe z))) := by
      change τ (U.f (lower z)) = ω (τ (U.f (upper (-Complex.conjAe z))))
      rw [← hτc, U.compact, hz]
    rw [he, hvup, V.compact]
  have hUV := orthogonal_rankOne_maps_commute D hne hzero U V
  have huv : ∀ a b, Commute (U.f a) (v b) := by
    apply commute_rankOne_maps
    · intro a b; rw [hvup]; exact hUV _ _
    · intro a b; rw [hvlo]; exact hUV _ _
    · intro a b; rw [hvup]; exact hUV _ _
    · intro a b; rw [hvlo]; exact hUV _ _
  let f : SL₂ ℂ →* AdelicGroups.PointsIn i ℂ :=
    MonoidHom.mk' (fun a => U.f a * v a) fun a b => by
      rw [map_mul, map_mul]
      calc
        _ = U.f a * (U.f b * v a) * v b := by simp only [mul_assoc]
        _ = _ := by rw [(huv b a).eq]; simp only [mul_assoc]
  have hcontV : Continuous v :=
    (IsTopologicalGroup.continuous_conj (D.exp x)).comp V.continuous |>.congr (fun a => (hv a).symm)
  have hcont : Continuous f := U.continuous.mul hcontV
  let F := f.comp unitaryToSpecialLinear
  have hcore : Set.range F ⊆ (D.fixedAt x : Set _) := by
    rintro _ ⟨a, rfl⟩
    let g := U.f (unitaryToSpecialLinear a)
    have hg : g ∈ fixedSubgroup ω := compact_rankOne_range ω hω U.f U.compact ⟨a, rfl⟩
    change ω g = g at hg
    refine ⟨?_, ?_⟩
    · change ω (g * τ g) = g * τ g
      rw [map_mul, ← hτc, hg]
    · change τ (g * τ g) = g * τ g
      rw [map_mul, hτ]
      exact (huv (unitaryToSpecialLinear a) (unitaryToSpecialLinear a)).eq.symm
  let : ConnectedSpace SU₂ := specialUnitary_connected
  have hc : Continuous F := hcont.comp continuous_unitaryToSpecialLinear
  refine ⟨F, hc, connected_range_in_component F hc hcore, ?_, ?_⟩
  · intro s
    obtain ⟨a, ha⟩ := exists_unitaryDiagonal s
    refine ⟨a, ha, ?_⟩
    change U.f (unitaryToSpecialLinear a) * v (unitaryToSpecialLinear a) = _
    rw [diagonal_from_circle s a ha, hv, exp_simpleRankOne_diagonal,
      exp_simpleRankOne_diagonal, torus_conj_on_self D (exp_mem D x) (exp_mem D _),
      ← exp_add, hβ, smul_add]
  · let a := unitaryWeylMatrix
    have hva : D.RepresentsWeyl (v (elementaryWeyl 1)) (reflection (Pi.single k 1)) := by
      rw [hv]
      have he (q : AdelicGroups.PointsIn i ℂ) (hq : q ∈ D.T) :
          D.RepresentsWeyl q 1 := fun y => torus_conj_on_self D hq (exp_mem D y)
      change D.RepresentsWeyl (D.exp x * V.f (elementaryWeyl 1) * (D.exp x)⁻¹) _
      simpa only [one_mul, mul_one] using represents_mul D
        (represents_mul D (he _ (exp_mem D x)) (rankOneMap_weyl D k V))
        (he _ (D.T.inv_mem (exp_mem D x)))
    have hrep : D.RepresentsWeyl (F a)
        (reflection (Pi.single j 1) * reflection (Pi.single k 1)) := by
      change D.RepresentsWeyl (U.f (unitaryToSpecialLinear a) * v (unitaryToSpecialLinear a)) _
      rw [show unitaryToSpecialLinear a = elementaryWeyl 1 from unitaryWeylMatrix_eq_word]
      exact represents_mul D (rankOneMap_weyl D j U) hva
    have hn : F a ∈ D.fixedAt x := hcore ⟨a, rfl⟩
    refine ⟨a, unitaryWeylMatrix_val,
      fixedAt_normalizes_of_label D x hn (pairedWord_in_e6Weyl j k) hrep, ?_⟩
    intro y hy
    exact (hrep y).trans (congrArg D.exp (hwall hy))

/-- Every commuting Weyl label has a representative fixed by the pinned diagram
automorphism in the actual compact group. -/
private theorem diagram_fixed_normalizer_lift (D : MarkedTorus ω θ S)
    (hω : Function.Involutive ω) (weyl : FoldedWeylCalculation) :
    ∀ w ∈ diagramCentralizingWeyl, ∃ m ∈ fixedCompact ω D.δ,
      m ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl m w := by
  classical
  let U (j : Fin 6) := Classical.choice (simpleRankOneMap_exists D j)
  let n (j : Fin 6) := (U j).f (elementaryWeyl 1)
  apply diagram_lifts_of_simple_words D weyl n
  · intro j
    have h := compact_rankOne_range ω hω (U j).f (U j).compact ⟨unitaryWeylMatrix, rfl⟩
    change (U j).f (unitaryToSpecialLinear unitaryWeylMatrix) ∈ fixedSubgroup ω at h
    rwa [unitaryWeylMatrix_eq_word] at h
  · intro j
    exact DFunLike.congr_fun (rankOneMap_diagram D (U j) (U _) rfl) (elementaryWeyl 1)
  · exact fun j => rankOneMap_weyl D j (U j)
  · exact orthogonal_rankOne_maps_commute D (show (0 : Fin 6) ≠ 5 by decide)
      (by decide) (U 0) (U 5) _ _
  · exact orthogonal_rankOne_maps_commute D (show (2 : Fin 6) ≠ 4 by decide)
      (by decide) (U 2) (U 4) _ _

end PairedWalls

section FoldedGeometry

open Specs.AbsoluteDynkinTypes (E6Reflection)

private theorem diagram_basis (j : Fin 6) :
    e6Diagram (Pi.single j 1) = Pi.single (E6Reflection j) 1 := by
  funext l
  have h : ∀ i : Fin 6, E6Reflection (E6Reflection i) = i := by decide
  have he : E6Reflection l = j ↔ l = E6Reflection j := by
    constructor
    · intro hh
      rw [← hh, h]
    · intro hh
      rw [hh, h]
  simp only [e6Diagram, Pi.single_apply, he]

private theorem e6Inner_symm (a b : E6Space) : e6Inner a b = e6Inner b a := by
  unfold e6Inner
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    have h : CartanMatrix.E 6 k j = CartanMatrix.E 6 j k :=
      congrFun (congrFun (CartanMatrix.E_isSymm 6).eq j) k
    rw [h]
    ring

private theorem e6Inner_add_right (a b c : E6Space) :
    e6Inner a (b + c) = e6Inner a b + e6Inner a c := by
  simp only [e6Inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem e6Inner_add_left (a b c : E6Space) :
    e6Inner (a + b) c = e6Inner a c + e6Inner b c := by
  rw [e6Inner_symm, e6Inner_add_right, e6Inner_symm c a, e6Inner_symm c b]

private theorem e6Inner_smul_left (a b : E6Space) (r : ℝ) :
    e6Inner (r • a) b = r * e6Inner a b := by
  rw [e6Inner_symm, e6Inner_smul_right, e6Inner_symm b a]

private theorem e6Inner_simple_pair (j k : Fin 6) :
    e6Inner (Pi.single j 1) (Pi.single k 1) = (CartanMatrix.E 6 j k : ℝ) := by
  rw [e6Inner_basis_row, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp

private theorem e6Inner_simple_self (j : Fin 6) : e6Inner (Pi.single j 1) (Pi.single j 1) = 2 := by
  rw [e6Inner_simple_pair]
  simp [CartanMatrix.E]

private theorem project_simple_fixed (j : Fin 6) (hj : E6Reflection j = j) :
    project (Pi.single j 1) = Pi.single j 1 := by
  rw [project, diagram_basis, hj]
  module

private theorem foldedCoroot_project_pair (j k : Fin 6) (h : E6Reflection j = k)
    (hzero : CartanMatrix.E 6 j k = 0) :
    foldedCoroot (project (Pi.single j 1)) = Pi.single j 1 + Pi.single k 1 := by
  have hh : project (Pi.single j 1) = (1 / 2 : ℝ) • (Pi.single j 1 + Pi.single k 1) := by
    rw [project, diagram_basis, h]
  have hi : e6Inner (project (Pi.single j 1)) (project (Pi.single j 1)) = 1 := by
    rw [hh, e6Inner_smul_left, e6Inner_smul_right, e6Inner_add_left,
      e6Inner_add_right, e6Inner_add_right, e6Inner_symm (Pi.single k 1) (Pi.single j 1),
      e6Inner_simple_self, e6Inner_simple_self, e6Inner_simple_pair, hzero]
    norm_num
  rw [foldedCoroot, hi, hh]
  module

/-- The four simple folded walls are realized by the compact rank-one maps
at fixed vertices and by the diagonal maps on the two paired factors. -/
private theorem folded_simple_wall_groups (D : MarkedTorus ω θ S) (hω : Function.Involutive ω)
    (weyl : FoldedWeylCalculation) (x : E6Space) (hτ : Function.Involutive (D.twisted x)) :
    ∀ l : Fin 4, OnWall (foldedSimple l) x → D.RealizesFoldedRoot x (foldedSimple l) := by
  intro l
  fin_cases l
  · intro _
    exact paired_wall_group D hω x hτ (j := 0) (k := 5)
      (by decide) (by decide) (by decide) _
      (foldedCoroot_project_pair 0 5 (by decide) (by decide)) (weyl.2.1 0)
  · intro _
    exact paired_wall_group D hω x hτ (j := 2) (k := 4)
      (by decide) (by decide) (by decide) _
      (foldedCoroot_project_pair 2 4 (by decide) (by decide)) (weyl.2.1 1)
  · change OnWall (project (Pi.single 3 1)) x → D.RealizesFoldedRoot x (project (Pi.single 3 1))
    rw [project_simple_fixed 3 (by decide)]
    exact fixed_simple_wall_group D hω x 3 (by decide)
  · change OnWall (project (Pi.single 1 1)) x → D.RealizesFoldedRoot x (project (Pi.single 1 1))
    rw [project_simple_fixed 1 (by decide)]
    exact fixed_simple_wall_group D hω x 1 (by decide)

end FoldedGeometry

private theorem folded_wall_groups (hω : Function.Involutive ω)
    (rootOrbit : FoldedRootOrbit) (equivariance : FoldedWallEquivariance)
    (inverseActions : WeylInverseActions) (x : E6Space) (_hx : x ∈ foldedSpace)
    (hτx : Function.Involutive (D.twisted x))
    (β : E6Space) (hβroot : β ∈ foldedRoots) (hwall : OnWall β x) :
    D.RealizesFoldedRoot x β := by
  let weyl := ExceptionalFoldedWeyl.foldedWeylCalculation
  obtain ⟨word, j, hw, hβ⟩ := rootOrbit β hβroot
  let w := (word.map orbitReflection).prod
  change w ∈ diagramCentralizingWeyl at hw
  change β = w (foldedSimple j) at hβ
  obtain ⟨v, _, hwv, _, _, hvFixed, _, _⟩ := inverseActions w hw
  let y := v x
  have hwy : w y = x := congrFun hwv x
  obtain ⟨n, hn, hnS, hnrep⟩ := diagram_fixed_normalizer_lift D hω weyl w hw
  have hωn : ω n = n := hn.1
  have hδn : D.δ n = n := hn.2
  have hnexp : MulAut.conj n (D.exp y) = D.exp x := (hnrep y).trans (congrArg D.exp hwy)
  have hprod : D.exp x * n = n * D.exp y := (mul_inv_eq_iff_eq_mul.mp hnexp).symm
  have hintertwine : D.twisted x * MulAut.conj n = MulAut.conj n * D.twisted y := by
    change (MulAut.conj (D.exp x) * D.δ) * MulAut.conj n =
      MulAut.conj n * (MulAut.conj (D.exp y) * D.δ)
    rw [mul_assoc, conj_intertwine, hδn, ← mul_assoc, ← map_mul, hprod, map_mul, mul_assoc]
  have htwist (g : AdelicGroups.PointsIn i ℂ) :
      D.twisted x (MulAut.conj n g) = MulAut.conj n (D.twisted y g) :=
    DFunLike.congr_fun hintertwine g
  have hτy : Function.Involutive (D.twisted y) := by
    intro g
    apply (MulAut.conj n).injective
    rw [← htwist (D.twisted y g), ← htwist g, hτx]
  have hcompact (g : AdelicGroups.PointsIn i ℂ) :
      ω (MulAut.conj n g) = MulAut.conj n (ω g) := by
    have h := conj_intertwine ω n
    rw [hωn] at h
    exact DFunLike.congr_fun h g
  have hnFixed (g : AdelicGroups.PointsIn i ℂ) (hg : g ∈ D.fixedAt y) :
      MulAut.conj n g ∈ D.fixedAt x := by
    constructor
    · change ω (MulAut.conj n g) = MulAut.conj n g
      rw [hcompact, show ω g = g from hg.1]
    · change D.twisted x (MulAut.conj n g) = MulAut.conj n g
      rw [htwist, show D.twisted y g = g from hg.2]
  have hsimple : OnWall (foldedSimple j) y := by
    apply (equivariance w hw (foldedSimple j) y).2.2.mp
    rwa [← hβ, hwy]
  obtain ⟨f, hf, himage, hdiag, aW, haW, haS, haact⟩ :=
    folded_simple_wall_groups D hω weyl y hτy j hsimple
  let F := (MulAut.conj n).toMonoidHom.comp f
  have hc : Continuous (MulAut.conj n : AdelicGroups.PointsIn i ℂ → _) :=
    IsTopologicalGroup.continuous_conj n
  refine ⟨F, hc.comp hf, ?_, ?_, aW, haW, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact mem_component_map (MulAut.conj n).toMonoidHom hc hnFixed (himage ⟨a, rfl⟩)
  · intro s
    obtain ⟨a, ha, heval⟩ := hdiag s
    refine ⟨a, ha, ?_⟩
    change MulAut.conj n (f a) = D.exp (s • foldedCoroot β)
    rw [heval, show MulAut.conj n (D.exp _) = _ from hnrep _,
      weyl_smul hw.1, (equivariance w hw (foldedSimple j) y).1, ← hβ]
  · let N := Subgroup.normalizer (S : Set (AdelicGroups.PointsIn i ℂ))
    change n * f aW * n⁻¹ ∈ N
    exact N.mul_mem (N.mul_mem hnS haS) (N.inv_mem hnS)
  · intro z hz
    have hwvz : w (v z) = z := congrFun hwv z
    have hconjz : MulAut.conj n (D.exp (v z)) = D.exp z :=
      (hnrep (v z)).trans (congrArg D.exp hwvz)
    calc
      F aW * D.exp z * (F aW)⁻¹ =
          MulAut.conj n (f aW * D.exp (v z) * (f aW)⁻¹) := by
        change MulAut.conj n (f aW) * D.exp z * (MulAut.conj n (f aW))⁻¹ = _
        rw [map_mul, map_mul, map_inv, hconjz]
      _ = MulAut.conj n (D.exp (reflection (foldedSimple j) (v z))) := by
        rw [haact (v z) (hvFixed hz)]
      _ = D.exp (reflection β z) := by
        change n * D.exp (reflection (foldedSimple j) (v z)) * n⁻¹ = _
        rw [hnrep, (equivariance w hw (foldedSimple j) (v z)).2.1, ← hβ, hwvz]

/-- Diagram-fixed compact normalizers with their full absolute Weyl action. -/
theorem diagramFixedNormalizerLifts_conditional
    (_fixedNormalizerRepresentatives : FixedNormalizerRepresentatives)
    (_fixedTorusConjugacy : FixedTorusConjugacy)
    (_maximalFixedTorusExistence : MaximalFixedTorusExistence)
    (_outerTorusComparison : OuterTorusComparison)
    (_foldedRootOrbit : FoldedRootOrbit)
    (_foldedRootPrimitivity : FoldedRootPrimitivity)
    (_foldedWallEquivariance : FoldedWallEquivariance)
    (_reflectionShiftCriterion : ReflectionShiftCriterion)
    (_weylInverseActions : WeylInverseActions) : DiagramFixedNormalizerLifts := by
  intro G i _ _ _ ω θ hωθ S _ D
  exact diagram_fixed_normalizer_lift D hωθ.compact_involutive
    ExceptionalFoldedWeyl.foldedWeylCalculation

/-- Compact rank-one maps realizing every folded wall through the given twist. -/
theorem compactRankOneWallLifts_conditional
    (_fixedNormalizerRepresentatives : FixedNormalizerRepresentatives)
    (_fixedTorusConjugacy : FixedTorusConjugacy)
    (_maximalFixedTorusExistence : MaximalFixedTorusExistence)
    (_outerTorusComparison : OuterTorusComparison)
    (foldedRootOrbit : FoldedRootOrbit)
    (_foldedRootPrimitivity : FoldedRootPrimitivity)
    (foldedWallEquivariance : FoldedWallEquivariance)
    (_reflectionShiftCriterion : ReflectionShiftCriterion)
    (weylInverseActions : WeylInverseActions) : CompactRankOneWallLifts := by
  intro G i _ _ _ ω θ hωθ S _ D x hx hτx β hβ hwall
  exact folded_wall_groups D hωθ.compact_involutive foldedRootOrbit foldedWallEquivariance
    weylInverseActions x hx hτx β hβ hwall

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts

theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactRankOneLifts».«compactRankOneWallLifts» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalOuterCompactRankOneLifts».«CompactRankOneWallLifts» :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactRankOneLifts».«compactRankOneWallLifts_conditional» (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedNormalizerRepresentatives») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedTorusConjugacy») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«maximalFixedTorusExistence») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«outerTorusComparison») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedRootOrbit») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedRootPrimitivity») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedWallEquivariance») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«reflectionShiftCriterion») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«weylInverseActions»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactRankOneLifts».«diagramFixedNormalizerLifts» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalOuterCompactRankOneLifts».«DiagramFixedNormalizerLifts» :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactRankOneLifts».«diagramFixedNormalizerLifts_conditional» (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedNormalizerRepresentatives») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedTorusConjugacy») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«maximalFixedTorusExistence») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«outerTorusComparison») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedRootOrbit») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedRootPrimitivity») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«foldedWallEquivariance») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«reflectionShiftCriterion») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterFoldedWallTransport».«weylInverseActions»)
