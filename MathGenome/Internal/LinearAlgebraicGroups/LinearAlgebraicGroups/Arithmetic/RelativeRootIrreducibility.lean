import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Group
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis

open LinearAlgebraicGroups.Specs.Arithmetic.RelativeRootIrreducibility
open LieAlgebrasAndRepresentations

namespace LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

set_option linter.style.haveILetI false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {R : Set E}

private theorem proportionalScalars (hR : IsPossiblyNonreducedRootSystem R)
    {a : E} (ha : a ∈ R) {t : ℝ} (ht : t • a ∈ R) :
    t = 1 ∨ t = -1 ∨ t = 2 ∨ t = -2 ∨ t = 1 / 2 ∨ t = -(1 / 2) := by
  have ha0 := hR.nonzero _ ha
  have hself : inner ℝ a a ≠ 0 := inner_self_ne_zero.mpr ha0
  have ht0 : t ≠ 0 := by
    intro hz
    apply hR.nonzero _ ht
    simp [hz]
  obtain ⟨m, hm⟩ := hR.integral a ha (t • a) ht
  obtain ⟨n, hn⟩ := hR.integral (t • a) ht a ha
  rw [real_inner_smul_left] at hm
  rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_right] at hn
  have hm' : (m : ℝ) = 2 * t := by
    rw [← hm]
    field_simp
  have hn' : (n : ℝ) = 2 / t := by
    rw [← hn]
    field_simp
  have hmn : m * n = 4 := by
    exact_mod_cast (show (m : ℝ) * (n : ℝ) = 4 by
      rw [hm', hn']
      field_simp
      norm_num)
  have hmabs : m.natAbs ≤ 4 := by
    have habs := congrArg Int.natAbs hmn
    rw [Int.natAbs_mul] at habs
    exact Nat.le_of_dvd (by decide) ⟨n.natAbs, habs.symm⟩
  have hlow : -4 ≤ m := by omega
  have hhigh : m ≤ 4 := by omega
  interval_cases m
  all_goals try norm_num at hm'
  all_goals try norm_num at hmn
  all_goals try omega
  all_goals
    first
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))

private theorem root_or_half (hR : IsPossiblyNonreducedRootSystem R) {a : E}
    (ha : a ∈ R) :
    a ∈ indivisibleRoots R ∨ (1 / 2 : ℝ) • a ∈ indivisibleRoots R := by
  by_cases hh : (1 / 2 : ℝ) • a ∈ R
  · right
    refine ⟨hh, ?_⟩
    rw [smul_smul]
    intro h
    rcases proportionalScalars hR ha h with h | h | h | h | h | h <;> norm_num at h
  · exact Or.inl ⟨ha, hh⟩

theorem indivisible_isRootSystem (hR : IsPossiblyNonreducedRootSystem R) :
    IsRootSystem (indivisibleRoots R) where
  finite := hR.finite.subset fun _ hx ↦ hx.1
  nonzero := fun a ha ↦ hR.nonzero a ha.1
  reflection_mem := by
    intro a ha b hb
    refine ⟨hR.reflection_mem a ha.1 b hb.1, ?_⟩
    intro hh
    apply hb.2
    have h := hR.reflection_mem a ha.1 _ hh
    rwa [reflection_smul, reflection_involutive] at h
  integral := fun a ha b hb ↦ hR.integral a ha.1 b hb.1
  reduced := by
    intro a ha b hb hspan
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hspan
    have opposite (a : E) (ha : a ∈ R) : -a ∈ R :=
      reflection_self (hR.nonzero a ha) ▸ hR.reflection_mem a ha a ha
    rcases proportionalScalars hR ha.1 hb.1 with ht | ht | ht | ht | ht | ht
    · left
      simp [ht]
    · right
      simp [ht]
    · exfalso
      apply hb.2
      simpa [ht, smul_smul] using ha.1
    · exfalso
      apply hb.2
      rw [ht, smul_smul, show (1 / 2 : ℝ) * -2 = -1 by norm_num, neg_one_smul]
      exact opposite a ha.1
    · exact (ha.2 (ht ▸ hb.1)).elim
    · exfalso
      apply ha.2
      simpa [ht, neg_smul] using opposite _ hb.1
  span_eq_top := by
    apply top_unique
    rw [← hR.span_eq_top]
    refine Submodule.span_le.mpr fun a ha ↦ ?_
    rcases root_or_half hR ha with hh | hh
    · exact Submodule.subset_span hh
    · have h := (Submodule.span ℝ (indivisibleRoots R)).smul_mem (2 : ℝ)
        (Submodule.subset_span hh)
      rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at h
      exact h

private theorem orthogonal_span {A B : Set E}
    (h : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = 0)
    {a b : E} (ha : a ∈ Submodule.span ℝ A) (hb : b ∈ Submodule.span ℝ B) :
    inner ℝ a b = 0 := by
  have hb' : ∀ x ∈ A, inner ℝ x b = 0 := by
    intro x hx
    induction hb using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul r y _ hy => simp [real_inner_smul_right, hy]
  induction ha using Submodule.span_induction with
  | mem x hx => exact hb' x hx
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul r x _ hx => simp [real_inner_smul_left, hx]

private theorem orbit_mem_span {P A : Set E} {v : E}
    (hA : ∀ a ∈ simpleRoots P v,
      a ∈ A ∨ ∀ x ∈ A, inner ℝ x a = 0)
    (w : simpleWeylGroup P v) {x : E} (hx : x ∈ Submodule.span ℝ A) :
    w.val x ∈ Submodule.span ℝ A := by
  let M := Submodule.span ℝ A
  have hmem (g : E ≃ₗ[ℝ] E) (hg : g ∈ simpleWeylGroup P v) :
      ∀ y, y ∈ M ↔ g y ∈ M := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, rfl⟩ := hg
      have image (y : E) (hy : y ∈ M) : rootReflectionEquiv a y ∈ M := by
        rw [rootReflectionEquiv_apply]
        rcases hA a ha with h | h
        · exact M.sub_mem hy (M.smul_mem _ (Submodule.subset_span h))
        · have hz := orthogonal_span (B := {a})
              (fun x hx z hz ↦ (Set.mem_singleton_iff.mp hz).symm ▸ h x hx) hy
              (Submodule.subset_span (Set.mem_singleton a))
          simp [rootReflection, hz, hy]
      intro y
      refine ⟨image y, fun hy ↦ ?_⟩
      simpa only [rootReflectionEquiv_apply, reflection_involutive] using
        image (rootReflectionEquiv a y) hy
    | one => intro y; rfl
    | mul f g _ _ hf hg => intro y; exact (hg y).trans (hf (g y))
    | inv f _ hf =>
      intro y
      simpa using (hf (f.symm y)).symm
  exact (hmem w.val w.property x).mp hx

theorem simpleDiagram_of_irreducible
    (hR : IsPossiblyNonreducedRootSystem R) (hI : LieAlgebrasAndRepresentations.IsIrreducible R)
    {v : E} (hv : RootRegular R v) :
    simpleDiagramConnected (indivisibleRoots R) v := by
  classical
  let P := indivisibleRoots R
  let Δ := simpleRoots P v
  have hP : IsRootSystem P := indivisible_isRootSystem hR
  have hvP : RootRegular P v := fun a ha ↦ hv a ha.1
  let adj : E → E → Prop :=
    fun x y ↦ x ∈ Δ ∧ y ∈ Δ ∧ x ≠ y ∧ inner ℝ x y ≠ 0
  intro a ha b hb
  change Relation.EqvGen adj a b
  by_contra hn
  let A : Set E := {x ∈ Δ | Relation.EqvGen adj a x}
  let B : Set E := {x ∈ Δ | ¬ Relation.EqvGen adj a x}
  have hab : ∀ x ∈ A, ∀ y ∈ B, inner ℝ x y = 0 := by
    intro x hx y hy
    by_contra hxy
    apply hy.2
    have hne : x ≠ y := fun he ↦ hy.2 (he ▸ hx.2)
    exact Relation.EqvGen.trans _ _ _ hx.2
      (Relation.EqvGen.rel _ _ ⟨hx.1, hy.1, hne, hxy⟩)
  have hA : ∀ x ∈ Δ, x ∈ A ∨ ∀ y ∈ A, inner ℝ y x = 0 := by
    intro x hx
    by_cases hc : Relation.EqvGen adj a x
    · exact Or.inl ⟨hx, hc⟩
    · exact Or.inr fun y hy ↦ hab y hy x ⟨hx, hc⟩
  have hB : ∀ x ∈ Δ, x ∈ B ∨ ∀ y ∈ B, inner ℝ y x = 0 := by
    intro x hx
    by_cases hc : Relation.EqvGen adj a x
    · exact Or.inr fun y hy ↦ (real_inner_comm x y).trans (hab x ⟨hx, hc⟩ y hy)
    · exact Or.inl ⟨hx, hc⟩
  let MA := Submodule.span ℝ A
  let MB := Submodule.span ℝ B
  have hcoverP : ∀ x ∈ P, x ∈ MA ∨ x ∈ MB := by
    intro x hx
    obtain ⟨w, y, hy, rfl⟩ := (show x ∈ {z | ∃ w : rootWeylGroup P,
        ∃ y ∈ simpleRoots P v, w.val y = z} from
      (simpleRoots_orbit P hP v hvP) ▸ hx)
    let w' : simpleWeylGroup P v := ⟨w.val, (simpleRoots_generate P hP v hvP).symm ▸ w.property⟩
    by_cases hc : Relation.EqvGen adj a y
    · exact Or.inl (orbit_mem_span hA w' (Submodule.subset_span (show y ∈ A from ⟨hy, hc⟩)))
    · exact Or.inr (orbit_mem_span hB w' (Submodule.subset_span (show y ∈ B from ⟨hy, hc⟩)))
  have hcover : (R ∩ (MA : Set E)) ∪ (R ∩ (MB : Set E)) = R := by
    ext x
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases root_or_half hR hx with hp | hp
      · rcases hcoverP x hp with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · have twice (M : Submodule ℝ E) (h : (1 / 2 : ℝ) • x ∈ M) : x ∈ M := by
          simpa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num] using M.smul_mem 2 h
        rcases hcoverP _ hp with h | h
        · exact Or.inl ⟨hx, twice MA h⟩
        · exact Or.inr ⟨hx, twice MB h⟩
  have horth : ∀ x ∈ R ∩ (MA : Set E), ∀ y ∈ R ∩ (MB : Set E), inner ℝ x y = 0 :=
    fun x hx y hy ↦ orthogonal_span hab hx.2 hy.2
  have ha' : a ∈ R ∩ (MA : Set E) :=
    ⟨(simpleRoots_subset P v ha).1, Submodule.subset_span ⟨ha, Relation.EqvGen.refl _⟩⟩
  have hb' : b ∈ R ∩ (MB : Set E) :=
    ⟨(simpleRoots_subset P v hb).1, Submodule.subset_span ⟨hb, hn⟩⟩
  rcases ((irreducible_iff_no_orthogonal_partition R hR.nonzero).mp hI).2 _ _ hcover horth with h | h
  · exact (Set.notMem_empty a) (h ▸ ha')
  · exact (Set.notMem_empty b) (h ▸ hb')

section InvariantForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [Group W] [Fintype W] (ρ : W →* Module.End ℝ V)

private def coordinateForm (x y : V) : ℝ :=
  let b := Module.finBasis ℝ V
  ∑ i, b.repr x i * b.repr y i

private def averagedForm (x y : V) : ℝ :=
  (Fintype.card W : ℝ)⁻¹ * ∑ w : W, coordinateForm (ρ w x) (ρ w y)

private theorem averagedForm_invariant (g : W) (x y : V) :
    averagedForm ρ (ρ g x) (ρ g y) = averagedForm ρ x y := by
  unfold averagedForm
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight g)
  intro w
  change coordinateForm (ρ w (ρ g x)) (ρ w (ρ g y)) =
    coordinateForm (ρ (w * g) x) (ρ (w * g) y)
  rw [map_mul]
  rfl

private theorem coordinateForm_self_nonneg (x : V) :
    0 ≤ coordinateForm x x := by
  unfold coordinateForm
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

private theorem coordinateForm_self_pos {x : V} (hx : x ≠ 0) :
    0 < coordinateForm x x := by
  classical
  let b := Module.finBasis ℝ V
  have h : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ ↦ mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

@[instance_reducible] private def averagedCore : InnerProductSpace.Core ℝ V where
  inner := averagedForm ρ
  conj_inner_symm x y := by
    change averagedForm ρ y x = averagedForm ρ x y
    simp only [averagedForm, coordinateForm, mul_comm]
  re_inner_nonneg x := by
    change 0 ≤ averagedForm ρ x x
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ ↦ coordinateForm_self_nonneg _)
  add_left x y z := by
    simp only [averagedForm, coordinateForm, map_add, Finsupp.add_apply, add_mul,
      Finset.sum_add_distrib, mul_add]
  smul_left x y r := by
    change averagedForm ρ (r • x) y = r * averagedForm ρ x y
    simp only [averagedForm, coordinateForm, map_smul, Finsupp.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
    ring
  definite x hx := by
    by_contra hn
    have hp : 0 < averagedForm ρ x x := by
      apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
      apply Finset.sum_pos' (fun w _ ↦ coordinateForm_self_nonneg _)
      refine ⟨1, Finset.mem_univ _, ?_⟩
      simpa using coordinateForm_self_pos hn
    exact hp.ne' hx

end InvariantForm

section Realization

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.Relative.RelativeChambers (relativeRoots IsChamber)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open Specs.Relative.RelativeReflections (Datum Root)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {S : ClosedSubgroup G.val}

private theorem realRoots_eq_range : realRoots S = Set.range (realRoot (S := S)) := by
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨⟨a, ha⟩, Subtype.ext hax⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩

private theorem realCharacter_injective [Module.Free ℤ (Additive (Character S.group))] :
    Function.Injective (realCharacter S) := by
  intro a b hab
  let basis := Module.Free.chooseBasis ℤ (Additive (Character S.group))
  change Additive.ofMul a = Additive.ofMul b
  apply basis.repr.injective
  ext i
  have h := congrArg (fun x : RealCharacters S ↦ (basis.baseChange ℝ).repr x i) hab
  simpa [realCharacter, Module.Basis.baseChange_repr_tmul, zsmul_eq_mul] using h

private theorem realRoot_ne_zero [Module.Free ℤ (Additive (Character S.group))]
    (a : Root S) : realRoot a ≠ 0 := by
  intro ha
  apply a.property.1
  apply realCharacter_injective (S := S)
  simpa [realRoot, realCharacter] using
    congrArg (fun x : RealRootSpan S ↦ (x : RealCharacters S)) ha

private def ambientAction {D : QuotientData S} (w : D.splitImage.labels) :
    Module.End ℝ (RealCharacters S) :=
  (w.val.toMonoidHom.toAdditive.toIntLinearMap).baseChange ℝ

private theorem ambientAction_mul {D : QuotientData S} (g h : D.splitImage.labels) :
    ambientAction (g * h) = ambientAction g * ambientAction h := by
  unfold ambientAction
  rw [← LinearMap.baseChange_mul]
  rfl

private theorem ambientAction_one {D : QuotientData S} :
    ambientAction (1 : D.splitImage.labels) = 1  := by unfold ambientAction; exact LinearMap.baseChange_one ℤ _

private def relativeAction {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) : D.splitImage.labels →* Module.End ℝ (RealRootSpan S) where
  toFun w := (ambientAction w).restrict (fun x hx ↦ by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have h := (realRoot (d.normalizerPerm w ⟨a, ha⟩)).property
      simpa [realRoot, ambientAction, realCharacter, d.rootAction] using h
    | zero => simp
    | add x y _ _ hx hy => exact (map_add (ambientAction w) x y).symm ▸ add_mem hx hy
    | smul r x _ hx => exact (map_smul (ambientAction w) r x).symm ▸ Submodule.smul_mem _ r hx)
  map_one' := by
    ext x
    exact LinearMap.congr_fun (ambientAction_one (D := D)) (x : RealCharacters S)
  map_mul' g h := by
    ext x
    exact LinearMap.congr_fun (ambientAction_mul g h) x

private theorem relativeAction_root {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (w : D.splitImage.labels) (a : Root S) :
    relativeAction d w (realRoot a) = realRoot (d.normalizerPerm w a) := by
  apply Subtype.ext
  simp [relativeAction, ambientAction, realRoot, realCharacter, d.rootAction]

private def extendFunctional (f : Additive (Character S.group) →ₗ[ℤ] ℝ) :
    RealCharacters S →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r ↦ r • f
      map_add' := fun r t ↦ add_smul r t f
      map_smul' := fun r t ↦ (smul_smul r t f).symm }

private theorem extendFunctional_root (f : Additive (Character S.group) →ₗ[ℤ] ℝ)
    (a : Root S) :
    extendFunctional f (realRoot a : RealCharacters S) = f (Additive.ofMul a.val) := by
  simp [extendFunctional, realRoot, realCharacter]

private theorem action_reflection {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (a b : Root S) :
    relativeAction d (d.reflection a).label (realRoot b) =
      realRoot b - (pairing S.group b.val (d.reflection a).coroot : ℝ) • realRoot a := by
  apply Subtype.ext
  change ambientAction (d.reflection a).label (realCharacter S b.val) =
    realCharacter S b.val - (pairing S.group b.val (d.reflection a).coroot : ℝ) • realCharacter S a.val
  let n := pairing S.group b.val (d.reflection a).coroot
  unfold ambientAction realCharacter
  rw [LinearMap.baseChange_tmul]
  change (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul ((d.reflection a).label.val b.val) = _
  rw [(d.reflection a).characterFormula]
  change (1 : ℝ) ⊗ₜ[ℤ] (Additive.ofMul b.val + (-n) • Additive.ofMul a.val) = _
  rw [TensorProduct.tmul_add, TensorProduct.tmul_smul]
  change (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul b.val +
    (-n : ℤ) • ((1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a.val) = _
  rw [← Int.cast_smul_eq_zsmul ℝ, Int.cast_neg, neg_smul, sub_eq_add_neg]

private theorem spanFinite {D : QuotientData S} [IsCommMonObj S.group.X] (d : Datum D) :
    FiniteDimensional ℝ (RealRootSpan S) := by
  haveI := d.finiteRoots
  exact Module.Finite.span_of_finite ℝ ((Set.toFinite (relativeRoots S)).image _)

@[instance_reducible] private def relativeForm {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) : InnerProductSpace.Core ℝ (RealRootSpan S) :=
  letI := spanFinite d
  letI := D.splitImage.finite
  letI := Fintype.ofFinite D.splitImage.labels
  averagedCore (relativeAction d)

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

private theorem relative_inner_invariant {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (w : D.splitImage.labels) (x y : RealRootSpan S) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    inner ℝ (relativeAction d w x) (relativeAction d w y) = inner ℝ x y := by
  letI := spanFinite d
  letI := D.splitImage.finite
  letI := Fintype.ofFinite D.splitImage.labels
  exact averagedForm_invariant (relativeAction d) w x y

private theorem relative_cartan {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) (a b : Root S) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    2 * inner ℝ (realRoot b) (realRoot a) / inner ℝ (realRoot a) (realRoot a) =
      (pairing S.group b.val (d.reflection a).coroot : ℝ) := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  let g := (d.reflection a).label
  let n := pairing S.group b.val (d.reflection a).coroot
  haveI := d.freeCharacters
  have ha : inner ℝ (realRoot a) (realRoot a) ≠ 0 := inner_self_ne_zero.mpr (realRoot_ne_zero a)
  have hn : relativeAction d g (realRoot a) = -realRoot a := by
    rw [action_reflection d a a, (d.reflection a).rootPairing]
    rw [Int.cast_ofNat, two_smul]
    abel
  have h := relative_inner_invariant d g (realRoot b) (realRoot a)
  rw [action_reflection d a b, hn, inner_neg_right, inner_sub_left] at h
  have hs := real_inner_smul_left (x := realRoot a) (y := realRoot a) (r := (n : ℝ))
  change -(inner ℝ (realRoot b) (realRoot a) -
    inner ℝ ((n : ℝ) • realRoot a) (realRoot a)) = _ at h
  rw [hs] at h
  apply (div_eq_iff ha).mpr
  linarith

private theorem relative_root_axioms {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    IsPossiblyNonreducedRootSystem (realRoots S) := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  haveI := d.finiteRoots
  haveI := d.freeCharacters
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [realRoots_eq_range]
    exact Set.finite_range _
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩
    exact realRoot_ne_zero a
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨d.normalizerPerm (d.reflection a).label b, ?_⟩
    rw [← relativeAction_root d, action_reflection d a b]
    rw [rootReflection, relative_cartan d a b]
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨_, relative_cartan d a b⟩
  · exact Submodule.span_setOfPred_mem_eq_top

private theorem relative_chamber_vector {D : QuotientData S} [IsCommMonObj S.group.X]
    (d : Datum D) {A : Set (Root S)} (hA : IsChamber S A) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    ∃ v : RealRootSpan S, RootRegular (realRoots S) v ∧
      ∀ a : Root S, a ∈ A ↔ 0 < inner ℝ v (realRoot a) := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  obtain ⟨f, hf, rfl⟩ := hA
  letI := spanFinite d
  letI := FiniteDimensional.complete ℝ (RealRootSpan S)
  let L := LinearMap.toContinuousLinearMap ((extendFunctional f).comp (RealRootSpan S).subtype)
  let v := (InnerProductSpace.toDual ℝ (RealRootSpan S)).symm L
  have hv (a : Root S) : inner ℝ v (realRoot a) = f (Additive.ofMul a.val) := by
    rw [InnerProductSpace.toDual_symm_apply]
    exact extendFunctional_root f a
  refine ⟨v, ?_, fun a ↦ ?_⟩
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩
    simpa only [hv] using hf a
  · rw [hv]
    rfl

/-- A partition orthogonal in the averaged form is detected by the actual
character–coroot pairings. -/
private theorem irreducible_of_pairing_partitions
    {D : QuotientData S} [IsCommMonObj S.group.X] (d : Datum D)
    (hne : Nonempty (Root S))
    (hpartition : ∀ A B : Set (Root S), A ∪ B = Set.univ →
      (∀ a ∈ A, ∀ b ∈ B,
        pairing S.group b.val (d.reflection a).coroot = 0 ∧
        pairing S.group a.val (d.reflection b).coroot = 0) →
      A = ∅ ∨ B = ∅) :
    letI := relativeForm d
    letI := InnerProductSpace.ofCore (relativeForm d).toCore
    LieAlgebrasAndRepresentations.IsIrreducible (realRoots S) := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  let R := realRoots S
  have hr : R = Set.range (realRoot (S := S)) := realRoots_eq_range
  apply (irreducible_iff_no_orthogonal_partition R (relative_root_axioms d).nonzero).mpr
  refine ⟨hne.elim (fun a ↦ ⟨realRoot a, hr.symm ▸ Set.mem_range_self a⟩), ?_⟩
  intro A B hAB horth
  let A' := realRoot (S := S) ⁻¹' A
  let B' := realRoot (S := S) ⁻¹' B
  have hcover : A' ∪ B' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    change realRoot a ∈ A ∪ B
    rw [hAB, hr]
    exact Set.mem_range_self a
  have hp : ∀ a ∈ A', ∀ b ∈ B',
      pairing S.group b.val (d.reflection a).coroot = 0 ∧
      pairing S.group a.val (d.reflection b).coroot = 0 := by
    intro a ha b hb
    have hzero := horth (realRoot a) ha (realRoot b) hb
    have hzero' := (real_inner_comm (realRoot a) (realRoot b)).trans hzero
    constructor
    · exact_mod_cast ((relative_cartan d a b).symm.trans (by rw [hzero']; simp) :
        (pairing S.group b.val (d.reflection a).coroot : ℝ) = 0)
    · exact_mod_cast ((relative_cartan d b a).symm.trans (by rw [hzero]; simp) :
        (pairing S.group a.val (d.reflection b).coroot : ℝ) = 0)
  rcases hpartition A' B' hcover hp with h | h
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxR : x ∈ R := hAB ▸ (show x ∈ A ∪ B from Or.inl hx)
    obtain ⟨a, rfl⟩ := hr ▸ hxR
    exact Set.notMem_empty a (h ▸ (show a ∈ A' from hx))
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxR : x ∈ R := hAB ▸ (show x ∈ A ∪ B from Or.inr hx)
    obtain ⟨a, rfl⟩ := hr ▸ hxR
    exact Set.notMem_empty a (h ▸ (show a ∈ B' from hx))

/-- The Lie and Weyl data give all the root-system and chamber conclusions once
orthogonal partitions of the relative roots have been ruled out. -/
private theorem rootConclusion_of_pairing_partitions
    {D : QuotientData S} [IsCommMonObj S.group.X] (d : Datum D)
    (hne : Nonempty (Root S))
    (hpartition : ∀ A B : Set (Root S), A ∪ B = Set.univ →
      (∀ a ∈ A, ∀ b ∈ B,
        pairing S.group b.val (d.reflection a).coroot = 0 ∧
        pairing S.group a.val (d.reflection b).coroot = 0) →
      A = ∅ ∨ B = ∅) :
    RootConclusion S := by
  letI := relativeForm d
  letI := InnerProductSpace.ofCore (relativeForm d).toCore
  have hR := relative_root_axioms d
  have hI := irreducible_of_pairing_partitions d hne hpartition
  have hP := indivisible_isRootSystem hR
  letI := d.freeCharacters
  refine ⟨relativeForm d, hR, hI, hP, realCharacter_injective, ?_,
    fun _ ha ↦ root_or_half hR ha, ?_, ?_⟩
  · intro a ha t hpos ht
    rcases proportionalScalars hR ha ht with h | h | h | h | h | h
    · exact Or.inl h
    · linarith
    · exact Or.inr (Or.inl h)
    · linarith
    · exact Or.inr (Or.inr h)
    · linarith
  · exact ⟨D, inferInstance, d, relativeAction d, relativeAction_root d,
      relative_inner_invariant d, relative_cartan d⟩
  · intro A hA
    obtain ⟨v, hv, hsign⟩ := relative_chamber_vector d hA
    let P := indivisibleRoots (realRoots S)
    have hvP : RootRegular P v := fun a ha ↦ hv a ha.1
    refine ⟨v, hv, hsign, simpleRoots_basis P hP v hvP,
      simpleRoots_coefficients P hP v hvP, ?_, simpleDiagram_of_irreducible hR hI hv⟩
    intro a ha
    rw [simpleRoots_generate P hP v hvP]
    change a ∈ P at ha
    rw [simpleRoots_orbit P hP v hvP] at ha
    exact ha

end Realization

section NormalClosure

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {k : Type u} [Field k] {G H : GroupScheme k}

private theorem conjugate_contracting {c : Cocharacter G} (D : LimitDecomposition c)
    {X : SchemeOver k} (z : X ⟶ D.centralizer.group.X)
    (p : X ⟶ D.contracting.group.X) :
    ∃ q : X ⟶ D.contracting.group.X,
      q ≫ D.contracting.inclusion.hom.hom =
        (z ≫ D.centralizer.inclusion.hom.hom) * (p ≫ D.contracting.inclusion.hom.hom) *
          (z ≫ D.centralizer.inclusion.hom.hom)⁻¹ := by
  let z' := z ≫ D.sectionMap.hom.hom
  let p' := p ≫ D.contractingToParabolic.hom.hom
  have hp : p' ≫ D.limit.hom.hom = 1 := by
    change (p ≫ D.contractingToParabolic.hom.hom) ≫ D.limit.hom.hom = _
    rw [Category.assoc, D.isKernel.w, comp_toUnit_assoc]
    rfl
  have h : (z' * p' * z'⁻¹) ≫ D.limit.hom.hom = toUnit X ≫ η[D.centralizer.group.X] := by
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hp, mul_one, mul_inv_cancel]
    rfl
  refine ⟨D.isKernel.lift (z' * p' * z'⁻¹) (toUnit X) h, ?_⟩
  have hf := D.isKernel.lift_fst (z' * p' * z'⁻¹) (toUnit X) h
  have hinc := congrArg (Grp.forget (SchemeOver k)).map D.contracting_in_G
  have hz := congrArg (Grp.forget (SchemeOver k)).map D.section_in_G
  change D.contractingToParabolic.hom.hom ≫ D.parabolic.inclusion.hom.hom =
    D.contracting.inclusion.hom.hom at hinc
  change D.sectionMap.hom.hom ≫ D.parabolic.inclusion.hom.hom =
    D.centralizer.inclusion.hom.hom at hz
  rw [← hinc, ← Category.assoc, hf, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  simp only [z', p', Category.assoc, hinc, hz]

private theorem centralizes_comp {d : H ⟶ G} {X Y : SchemeOver k}
    {f : X ⟶ G.X} (h : Centralizes d f) (g : Y ⟶ X) :
    Centralizes d (g ≫ f) := by
  apply (centralizes_iff ..).mpr
  intro Z p t
  exact (Category.assoc p g f) ▸ (centralizes_iff ..).mp h Z (p ≫ g) t

private theorem universal_conjugates_on_cell {c d : Cocharacter G}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hc : Centralizes d c.hom.hom)
    (hpos : Centralizes d D.contracting.inclusion.hom.hom)
    (hneg : Centralizes d E.contracting.inclusion.hom.hom) :
    Centralizes d
      (((bigCellMap D E) ⊗ₘ 𝟙 _) ≫ Specs.subgroupConjugation c) := by
  let N := E.contracting.group.X
  let Z := D.centralizer.group.X
  let P := D.contracting.group.X
  let T := (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X
  let M : T ⟶ G.X := c.hom.hom
  let U := N ⊗ (Z ⊗ P)
  let X := U ⊗ T
  let q₀ := fst U T ≫ fst N (Z ⊗ P)
  let z₀ := fst U T ≫ snd N (Z ⊗ P) ≫ fst Z P
  let p₀ := fst U T ≫ snd N (Z ⊗ P) ≫ snd Z P
  let q := q₀ ≫ E.contracting.inclusion.hom.hom
  let z := z₀ ≫ D.centralizer.inclusion.hom.hom
  let p := p₀ ≫ D.contracting.inclusion.hom.hom
  let s := snd U T ≫ M
  obtain ⟨p₁, hp₁⟩ := conjugate_contracting D z₀ p₀
  have hz : Commute z s := by
    have hz' : Centralizes c D.centralizer.inclusion.hom.hom :=
      (D.centralizer_points _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
    exact (centralizes_iff ..).mp hz' X z₀ (snd U T)
  have he : ((bigCellMap D E) ⊗ₘ 𝟙 _) ≫ Specs.subgroupConjugation c =
      (q * (z * p)) * s * (q * (z * p))⁻¹ := by
    simp only [Specs.subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      tensorHom_fst, tensorHom_snd, Category.comp_id]
    simp only [bigCellMap, multiplyFactors, MonObj.comp_mul, Category.assoc, q, z, p, s, q₀, z₀, p₀, U, M]
    rfl
  rw [he]
  have eq : (q * (z * p)) = (q * (p₁ ≫ D.contracting.inclusion.hom.hom)) * z := by
    rw [hp₁]
    change q * (z * p) = q * (z * p * z⁻¹) * z
    group
  have eq' : (q * (z * p)) * s * (q * (z * p))⁻¹ =
      (q * (p₁ ≫ D.contracting.inclusion.hom.hom)) * s *
        (q * (p₁ ≫ D.contracting.inclusion.hom.hom))⁻¹ := by
    rw [eq]
    let r := q * (p₁ ≫ D.contracting.inclusion.hom.hom)
    change (r * z) * s * (r * z)⁻¹ = r * s * r⁻¹
    calc
      _ = r * (z * s * z⁻¹) * r⁻¹ := by group
      _ = _ := by rw [hz.mul_inv_cancel]
  rw [eq']
  apply (centralizes_iff ..).mpr
  intro Y y t
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  have hq := (centralizes_iff ..).mp hneg Y (y ≫ q₀) t
  have hp := (centralizes_iff ..).mp hpos Y (y ≫ p₁) t
  have hs := (centralizes_iff ..).mp hc Y (y ≫ snd U T) t
  simp only [Category.assoc] at hq hp hs ⊢
  exact (((hq.mul_left hp).mul_left hs).mul_left ((hq.mul_left hp).inv_left))

private theorem fst_base_change {X Y T : SchemeOver k} (f : X ⟶ Y) :
    IsPullback (f ⊗ₘ 𝟙 T).left (fst X T).left (fst Y T).left f.left := by
  have hb (Z : SchemeOver k) : IsPullback (snd Z T).left (fst Z T).left T.hom Z.hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct Z T)).flip
  apply IsPullback.of_right (h₁₂ := (snd Y T).left) (v₁₃ := T.hom) (h₂₂ := Y.hom)
    ?_ ?_ (hb Y)
  · simpa only [← Over.comp_left, tensorHom_snd, Category.comp_id, Over.w] using hb X
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]

private theorem factor_through_dominant {X Y Z T : SchemeOver k}
    (f : X ⟶ Y) (i : T ⟶ Z) (g : Y ⟶ Z)
    [IsSchemeTheoreticallyDominant f.left] [IsClosedImmersion i.left]
    (h : ∃ r : X ⟶ T, r ≫ i = f ≫ g) : ∃ r : Y ⟶ T, r ≫ i = g := by
  obtain ⟨r, hr⟩ := h
  have hle : i.left.ker ≤ g.left.ker := by
    calc
      i.left.ker ≤ (r.left ≫ i.left).ker := r.left.le_ker_comp i.left
      _ = (f.left ≫ g.left).ker :=
        by
          change (r ≫ i).left.ker = (f ≫ g).left.ker
          rw [hr]
      _ = g.left.ker := by rw [Scheme.Hom.ker_comp, f.left.ker_eq_bot,
        Scheme.IdealSheafData.map_bot]
  let p := IsClosedImmersion.lift i.left g.left hle
  have hp := IsClosedImmersion.lift_fac i.left g.left hle
  exact ⟨Over.homMk p (by rw [← Over.w i, ← Category.assoc, hp, Over.w g]),
    Over.OverMorphism.ext hp⟩

private theorem universal_conjugates_factor {c d : Cocharacter G}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (F : LimitDecomposition d)
    (hc : Centralizes d c.hom.hom)
    (hpos : Centralizes d D.contracting.inclusion.hom.hom)
    (hneg : Centralizes d E.contracting.inclusion.hom.hom)
    [IsOpenImmersion (bigCellMap D E).left]
    [IsIntegral (G.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X).left] :
    ∃ p, p ≫ F.centralizer.inclusion.hom.hom = Specs.subgroupConjugation c := by
  let T := (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X
  let j := bigCellMap D E ⊗ₘ 𝟙 T
  let q : 𝟙_ (SchemeOver k) ⟶
      (E.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X)) ⊗ T :=
    lift (lift 1 (lift 1 1)) 1
  letI : Nonempty ((E.contracting.group.X ⊗ (D.centralizer.group.X ⊗
      D.contracting.group.X)) ⊗ T).left :=
    ⟨q.left (IsLocalRing.closedPoint k)⟩
  haveI : IsOpenImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (fst_base_change (bigCellMap D E)).flip
      inferInstance
  haveI : IsDominant j.left :=
    ⟨j.left.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  haveI := IsSchemeTheoreticallyDominant.of_isDominant j.left
  haveI := F.centralizer.isClosedImmersion
  exact factor_through_dominant j F.centralizer.inclusion.hom.hom _
    ((F.centralizer_points _ _).mp (universal_conjugates_on_cell D E hc hpos hneg))

open Specs.FiniteWordClosure (ConjugationStable power wordDomain)
open Specs.GeometricRadicals (IsSmoothConnectedNormal IsTrivialSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

private theorem conjugates_stable {J : GroupScheme k} (c : J ⟶ G) :
    ConjugationStable (Specs.subgroupConjugation c) := by
  intro X g p
  let z := p ≫ fst G.X J.X
  let t := p ≫ snd G.X J.X
  let q := lift (g * z) t
  refine ⟨q, ?_⟩
  simp only [q, Specs.subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    lift_fst, lift_snd]
  change (g * z) * (t ≫ c.hom.hom) * (g * z)⁻¹ =
    g * (z * (t ≫ c.hom.hom) * z⁻¹) * g⁻¹
  group

private theorem conjugates_of_nontrivial_into_proper_centralizer [PerfectField k]
    (G : AffineAlgebraicGroup k)
    (hSimple : ∀ N : ClosedSubgroup G.val,
      IsSmoothConnectedNormal N → IsTrivialSubgroup N ∨ IsIso N.inclusion)
    (c d : Cocharacter G.val) (F : LimitDecomposition d)
    (hne : c.hom.hom ≠ 1) (hd : ¬ ∀ X (g : X ⟶ G.val.X), Centralizes d g)
    (hfac : ∃ p, p ≫ F.centralizer.inclusion.hom.hom = Specs.subgroupConjugation c)
    (hA : IsAffine ((G.val.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X).left))
    (hft : LocallyOfFiniteType (G.val.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X).hom)
    (hc : QuasiCompact (G.val.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X).hom)
    (haff : ∀ m, IsAffine (power (G.val.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X) m).left)
    (hpow : ∀ m, IsIntegral (power (G.val.X ⊗ (specGroup (DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters)).X) m).left) : False := by
  let T := (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X
  let X := G.val.X ⊗ T
  let f := Specs.subgroupConjugation c
  let x : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx : x ≫ f = 1 := by
    change (lift (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) (1 : 𝟙_ (SchemeOver k) ⟶ T)) ≫ f = 1
    dsimp only [f, Specs.subgroupConjugation]
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc,
      MonObj.one_comp, mul_one, inv_one, mul_one]
  obtain ⟨N, n, w, _, hn, hw, ⟨j, hj⟩, hmin, _⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x hA hft hc hx hpow (conjugates_stable c)
  letI : IsIntegral (wordDomain X n).left := hpow (2 * n)
  letI : IsAffine (wordDomain X n).left := haff (2 * n)
  letI : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup (G := G) N).property.1
  haveI : IsAffineHom w.left := isAffineHom_of_isAffine w.left
  haveI : QuasiCompact w.left := inferInstance
  haveI : IsReduced N.group.X.left := IsSchemeTheoreticallyDominant.isReduced w.left
  have hirr : IrreducibleSpace N.group.X.left := by
    have h := ((IrreducibleSpace.isIrreducible_univ _).image w.left
      w.left.continuous.continuousOn).closure
    rw [Set.image_univ, w.left.denseRange.closure_eq] at h
    exact (irreducibleSpace_def _).mpr h
  letI := hirr
  letI : LocallyOfFiniteType N.group.X.hom :=
    (closedSubgroupAlgebraicGroup (G := G) N).property.2.1
  have hsmooth : Smooth N.group.X.hom :=
    LinearAlgebraicGroups.smoothOfReducedOverPerfectField k N.group inferInstance
  have hN := hSimple N ⟨hsmooth, inferInstance, hn⟩
  rcases hN with hN | hN
  · apply hne
    let p : T ⟶ X := lift 1 (𝟙 T)
    have hp : p ≫ f = c.hom.hom := by
      dsimp only [p, f, Specs.subgroupConjugation]
      rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc,
        Category.id_comp, one_mul, inv_one, mul_one]
    obtain ⟨e⟩ := hN
    have h1 : p ≫ j = 1 := by
      apply (cancel_mono e.hom.hom.hom).mp
      exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    rw [← hp, ← hj, ← Category.assoc, h1, MonObj.one_comp]
  · obtain ⟨a, ha⟩ := hmin F.centralizer hfac
    apply hd
    intro Y g
    apply (F.centralizer_points Y g).mpr
    letI := hN
    refine ⟨g ≫ (inv N.inclusion ≫ a).hom.hom, ?_⟩
    have hf : (inv N.inclusion ≫ a) ≫ F.centralizer.inclusion = 𝟙 _ := by
      rw [Category.assoc, ha, IsIso.inv_hom_id]
    let U := Grp.forget (SchemeOver k)
    change g ≫ U.map (inv N.inclusion ≫ a) ≫ U.map F.centralizer.inclusion = g
    rw [← Functor.map_comp, hf]
    exact Category.comp_id g


open Specs.BorelsAndChambers (positiveRoots)
open Specs.OrderedRootProducts (RootSubgroupFamily rootProduct)
open Specs.AbstractPairing (Root)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterPairing (pairing)

private theorem centralizes_mul {d : H ⟶ G} {X : SchemeOver k} {f g : X ⟶ G.X}
    (hf : Centralizes d f) (hg : Centralizes d g) : Centralizes d (f * g) := by
  apply (centralizes_iff ..).mpr
  intro Y y t
  rw [MonObj.comp_mul]
  exact ((centralizes_iff ..).mp hf Y y t).mul_left ((centralizes_iff ..).mp hg Y y t)

private theorem centralizes_root_product {A : AffineAlgebraicGroup k}
    {d : H ⟶ A.val} {T : ClosedSubgroup A.val}
    {U : RootSubgroupFamily T} (l : List (Root T))
    (hl : ∀ α ∈ l, Centralizes d (U α).val.inclusion.hom.hom) :
    Centralizes d (rootProduct U l) := by
  induction l with
  | nil =>
    apply (centralizes_iff ..).mpr
    intro Y y t
    rw [rootProduct, MonObj.comp_one]
    exact Commute.one_left _
  | cons α l ih =>
    exact centralizes_mul (centralizes_comp (hl α List.mem_cons_self) (fst _ _))
      (centralizes_comp (ih (fun β hb ↦ hl β (List.mem_cons_of_mem _ hb))) (snd _ _))

private theorem centralizes_contracting_of_centralizes_root_groups
    (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (U : RootSubgroupFamily T) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (d : Cocharacter A.val)
    (h : ∀ α ∈ positiveRoots T c, Centralizes d (U α).val.inclusion.hom.hom) :
    Centralizes d D.contracting.inclusion.hom.hom := by
  classical
  have hprod := RootData.OrderedRootProducts.contractingProduct A hA T hT hmax
  letI : Finite (Root T) := hprod.1.to_subtype
  letI := Fintype.ofFinite (Root T)
  let l := (Finset.univ.filter (· ∈ positiveRoots T c)).toList
  have hl : Specs.OrderedRootProducts.Enumerates l (positiveRoots T c) :=
    ⟨Finset.nodup_toList _, fun α ↦ by simp [l]⟩
  obtain ⟨e, he⟩ := (hprod.2.2 c).2 D U l hl
  have h1 := centralizes_comp
    (centralizes_root_product (d := d) l (fun α ha ↦ h α ((hl.2 α).mp ha))) e.inv
  rwa [← he, Iso.inv_hom_id_assoc] at h1

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.GeometricRadicals (GeometricGroup IsSemisimple baseChangedSubgroup
  geometricUnipotentRadical geometricSolvableRadical)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open Specs.RootGroups (rootPoint)

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private unitEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private rootPoint_surjective RootCoordinate rootCoordinate_exists cocharacterPoint_postcompose
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private affine_tensor affine_power from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private power_geometry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private multiplicativeGroupAlgebra
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private oppositeCocharacter_eq_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private connected_of_geometricallyConnected cocharacter_weight_coordinates differential_comp
  geometricallyMaximal_of_maximal_split reductive_geometricGroup pairing_one splitTorus_connected
  splitTorus_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private split_of_maximal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private unipotent_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private trivial_of_subgroup_of_trivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private characterValue_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
open private laurentParameter_zpow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLieWeights

private abbrev multiplicativeGroup (F : Type u) [Field F] : GroupScheme F :=
  specGroup (groupAlgebra F IntegerCharacters)

private theorem reductive_of_semisimple (A : AffineAlgebraicGroup k) (h : IsSemisimple A) :
    IsReductive A := by
  let U := geometricUnipotentRadical A
  have hU := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest A
  have hs := unipotent_solvable (closedSubgroupAlgebraicGroup (G := GeometricGroup A) U)
    hU.1.1 hU.1.2.1 hU.2.1
  have hSol := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest A
  exact ⟨h.1, h.2.1, trivial_of_subgroup_of_trivial (hSol.2.2 U hU.1 hs) h.2.2⟩

private theorem gm_split (F : Type u) [Field F] : IsSplitTorus (multiplicativeGroup F) := by
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := F) 1
  let a : StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) IntegerCharacters
  exact ⟨1, ⟨(hopfSpec (CommRingCat.of F)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv F F a)).op ≪≫ e⟩⟩

private theorem not_central_of_nonzero_pairing (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (d : Cocharacter T.group)
    (D : LimitDecomposition (d ≫ T.inclusion)) (a : Root T)
    (ha : pairing T.group a.val d ≠ 0) :
    ¬ ∀ X (g : X ⟶ A.val.X), Centralizes (d ≫ T.inclusion) g := by
  intro h
  obtain ⟨p, hp⟩ := (D.centralizer_points _ _).mp (h _ (𝟙 A.val.X))
  obtain ⟨i, hi⟩ := factor_group_through_subgroup D.centralizer (𝟙 A.val) p hp
  obtain ⟨v, hv, hv0⟩ := a.property.2
  have hvZ : v ∈ lieImage D.centralizer := by
    refine ⟨mapPointKernel i v, ?_⟩
    rw [← differential_comp, hi]
    exact (lieFunctoriality k).2.1 A.val v
  let s := identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, _, _, hZ⟩ := lieWeights A _ D s
  rw [hZ] at hvZ
  apply hv0
  have hzero (j : ULift.{u} (Fin W.dimension)) : W.basis.equivFun v j = 0 := by
    by_cases hj : W.weight j = pairing T.group a.val d
    · exact hvZ j (hj.trans_ne ha)
    · exact cocharacter_weight_coordinates T d s W hv j hj
  exact (W.basis.equivFun.injective
    ((funext hzero).trans W.basis.equivFun.map_zero.symm)).trans (canonicalZero_eq s).symm

private theorem cocharacter_ne_one_of_not_central {d : Cocharacter G}
    (hd : ¬ ∀ X (g : X ⟶ G.X), Centralizes d g) : d.hom.hom ≠ 1 := by
  intro h
  apply hd
  intro X g
  apply (centralizes_iff ..).mpr
  intro Y p t
  rw [h, MonObj.comp_one]
  exact Commute.one_right _

/-- A root coordinate with weight zero for a cocharacter is fixed over every
test scheme. -/
private theorem centralizes_root_group (A : AffineAlgebraicGroup k)
    {T : ClosedSubgroup A.val} {U : RootSubgroupFamily T} (a : Root T)
    (x : RootCoordinate U a) (d : Cocharacter T.group) (hd : pairing T.group a.val d = 0) :
    Centralizes (d ≫ T.inclusion) (U a).val.inclusion.hom.hom := by
  rcases x with ⟨line, e, hscalar, _⟩
  letI : IsAffine (multiplicativeGroup k).X.left := (multiplicativeGroupAlgebra k).property.1
  letI : IsAffine (U a).val.group.X.left :=
    (closedSubgroupAlgebraicGroup (G := A) (U a).val).property.1
  unfold Centralizes conjugateFamily
  apply hom_ext_of_points affine_tensor
  intro R p
  obtain ⟨s, hs⟩ := (unitEquiv R).symm.surjective (p ≫ fst _ _)
  change unitPoint R s = p ≫ fst _ _ at hs
  obtain ⟨b, hb⟩ := rootPoint_surjective e R (p ≫ snd _ _)
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  rw [← hs, ← hb]
  let t : GroupPoints A.val R := cocharacterPoint d R s ≫ T.inclusion.hom.hom
  let z := rootPoint (e.hom ≫ (U a).val.inclusion) R b
  have h := hscalar R (cocharacterPoint d R s) b
  rw [(RootData.CharacterPairing.characterPairingComposition T.group a.val d).2,
    hd, zpow_zero, Units.val_one, one_mul] at h
  change t * z * t⁻¹ = z at h
  have ht : unitPoint R s ≫ (d ≫ T.inclusion).hom.hom = t := Category.assoc _ _ _ |>.symm
  have hz : rootPoint e.hom R b ≫ (U a).val.inclusion.hom.hom = z := Category.assoc _ _ _
  rw [ht, hz]
  exact mul_inv_eq_iff_eq_mul.mpr (mul_inv_eq_iff_eq_mul.mp h).symm

private theorem centralizes_cocharacters (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (c d : Cocharacter T.group) :
    Centralizes (d ≫ T.inclusion) (c ≫ T.inclusion).hom.hom := by
  apply (centralizes_iff ..).mpr
  intro Y p t
  obtain ⟨hComm, _, _, _, _, _, _, _⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hT
  letI := hComm
  have h : Commute (p ≫ c.hom.hom) (t ≫ d.hom.hom) := mul_comm' _ _
  have hm := h.map (IsMonHom.monoidHom T.inclusion.hom.hom Y)
  change Commute ((p ≫ c.hom.hom) ≫ T.inclusion.hom.hom)
    ((t ≫ d.hom.hom) ≫ T.inclusion.hom.hom) at hm
  change Commute (p ≫ c.hom.hom ≫ T.inclusion.hom.hom)
    (t ≫ d.hom.hom ≫ T.inclusion.hom.hom)
  simpa only [Category.assoc] using hm

private theorem pairing_extended (K : Type u) [Field K] [Algebra k K]
    (e : multiplicativeGroup K ≅ (groupBaseChange k K).obj (multiplicativeGroup k))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      baseChangePoint k K (multiplicativeGroup k).X R (unitPoint R s ≫ e.hom.hom.hom) =
        unitPoint ((restrictTestAlgebra k K).obj R) s)
    {S T : GroupScheme k} (i : S ⟶ T) (a : Character S)
    (b : Character ((groupBaseChange k K).obj T))
    (hb : (groupBaseChange k K).map i ≫ b = (groupBaseChange k K).map a ≫ e.inv)
    (c : Cocharacter S) :
    pairing _ b (e.hom ≫ (groupBaseChange k K).map c ≫ (groupBaseChange k K).map i) =
      pairing S a c := by
  let F := groupBaseChange k K
  let R₀ := CommAlgCat.of K K
  let R := laurentAlgebra R₀
  let s := laurentParameter R₀
  let cK : Cocharacter (F.obj S) := e.hom ≫ F.map c
  have hR := characterValue_extend a e he R (cocharacterPoint cK R s)
  have hr : baseChangePoint k K S.X R (cocharacterPoint cK R s) =
      cocharacterPoint c ((restrictTestAlgebra k K).obj R) s := by
    have h := baseChangePointsSchemeNaturality k K c.hom.hom R
      (unitPoint R s ≫ e.hom.hom.hom)
    change baseChangePoint k K S.X R
      ((unitPoint R s ≫ e.hom.hom.hom) ≫ (F.map c).hom.hom) = _ at h
    rw [Category.assoc] at h
    exact h.trans (congrArg (fun p ↦ p ≫ c.hom.hom) (he R s))
  rw [hr, (RootData.CharacterPairing.characterPairingComposition S a c).2,
    ← hb] at hR
  have hv : characterValue (F.map i ≫ b) R (cocharacterPoint cK R s) =
      characterValue b R (cocharacterPoint (cK ≫ F.map i) R s) := by
    rw [cocharacterPoint_postcompose cK (F.map i) R s]
    unfold characterValue
    dsimp only [Grp.comp_hom_hom]
    rw [Category.assoc]
  rw [hv, (RootData.CharacterPairing.characterPairingComposition _ b _).2] at hR
  have hpow : (↑(s ^ pairing _ b (cK ≫ F.map i)) : LaurentPolynomial K) =
      (↑(s ^ pairing S a c) : LaurentPolynomial K) := hR
  dsimp only [s] at hpow
  rw [laurentParameter_zpow, laurentParameter_zpow] at hpow
  have hn : Function.Injective (LaurentPolynomial.T (R := K)) := by
    intro m n h
    apply WithBot.coe_injective
    simpa only [LaurentPolynomial.degree_T] using congrArg LaurentPolynomial.degree h
  have h := hn hpow
  simpa only [cK, Category.assoc] using h

private theorem pairing_restriction (K : Type u) [Field K] [Algebra k K]
    (e : multiplicativeGroup K ≅ (groupBaseChange k K).obj (multiplicativeGroup k))
    {S T : GroupScheme k} (i : S ⟶ T) (b : Character ((groupBaseChange k K).obj T))
    (hb : (groupBaseChange k K).map i ≫ b = 1)
    (hS : IsSplitTorus ((groupBaseChange k K).obj S)) (c : Cocharacter S) :
    pairing _ b (e.hom ≫ (groupBaseChange k K).map c ≫ (groupBaseChange k K).map i) = 0 := by
  let F := groupBaseChange k K
  let cK : Cocharacter (F.obj S) := e.hom ≫ F.map c
  have h : pairing (F.obj T) b (cK ≫ F.map i) =
      pairing (F.obj S) (F.map i ≫ b) cK := by
    apply (RootData.CharacterPairing.characterPairingComposition _ b _).1 _ |>.mp
    have heq := (RootData.CharacterPairing.characterPairingComposition _ (F.map i ≫ b) cK).1 _ |>.mpr rfl
    exact (Category.assoc _ _ _).trans heq
  rw [← Category.assoc]
  change pairing _ b (cK ≫ F.map i) = _
  rw [h, hb, pairing_one _ hS]

/-- In an almost simple group, two cocharacters with nonzero root pairings
cannot have disjoint sets of roots on which they pair nontrivially. The
normal closure of the first cocharacter would lie in the second centralizer. -/
private theorem incompatible_cocharacters [PerfectField k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A)
    (hSimple : ∀ N : ClosedSubgroup A.val,
      IsSmoothConnectedNormal N → IsTrivialSubgroup N ∨ IsIso N.inclusion)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (c d : Cocharacter T.group) (a b : Root T)
    (ha : pairing T.group a.val c ≠ 0) (hb : pairing T.group b.val d ≠ 0)
    (hpair : ∀ α : Root T, pairing T.group α.val c = 0 ∨ pairing T.group α.val d = 0) :
    False := by
  let U := Classical.choice (RootData.OrderedRootProducts.contractingProduct A hA T hT hmax).2.1
  obtain ⟨D⟩ := existsLimitDecomposition A (c ≫ T.inclusion)
  obtain ⟨E⟩ := existsLimitDecomposition A (oppositeCocharacter c ≫ T.inclusion)
  obtain ⟨F⟩ := existsLimitDecomposition A (d ≫ T.inclusion)
  have ha' := not_central_of_nonzero_pairing A T c D a ha
  have hb' := not_central_of_nonzero_pairing A T d F b hb
  have hroot (α : Root T) (hα : pairing T.group α.val c ≠ 0) :
      Centralizes (d ≫ T.inclusion) (U α).val.inclusion.hom.hom := by
    obtain ⟨x⟩ := rootCoordinate_exists RootData.RootGroups.rootSubgroups A hA T hT hmax U α
    exact centralizes_root_group A α x d ((hpair α).resolve_left hα)
  have hpos := centralizes_contracting_of_centralizes_root_groups
    A hA T hT hmax U c D (d ≫ T.inclusion)
      (fun α hα ↦ hroot α (ne_of_gt hα))
  have hOpp (χ : Character T.group) :
      pairing T.group χ (oppositeCocharacter c) = -pairing T.group χ c := by
    obtain ⟨hComm, _, _, _, _, P, _, hP⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hT
    letI := hComm
    rw [oppositeCocharacter_eq_inv, ← hP, ← hP]
    exact map_neg (P (Additive.ofMul χ)) (Additive.ofMul c)
  have hneg := centralizes_contracting_of_centralizes_root_groups
    A hA T hT hmax U (oppositeCocharacter c) E
      (d ≫ T.inclusion) (fun α hα ↦ hroot α (by
        intro hz
        change 0 < pairing T.group α.val (oppositeCocharacter c) at hα
        rw [hOpp, hz, neg_zero] at hα
        exact lt_irrefl _ hα))
  have hop : oppositeCocharacter c ≫ T.inclusion = oppositeCocharacter (c ≫ T.inclusion) :=
    Category.assoc _ _ _
  let E' := hop ▸ E
  have hneg' : Centralizes (d ≫ T.inclusion) E'.contracting.inclusion.hom.hom := by
    cases hop
    exact hneg
  letI := hA.1
  letI := connected_of_geometricallyConnected hA.2.1
  let M := multiplicativeGroupAlgebra k
  letI : IsAffine A.val.X.left := A.property.1
  letI : IsAffine (multiplicativeGroup k).X.left := M.property.1
  letI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
  letI : LocallyOfFiniteType (multiplicativeGroup k).X.hom := M.property.2.1
  letI : QuasiCompact A.val.X.hom := A.property.2.2
  letI : QuasiCompact (multiplicativeGroup k).X.hom := M.property.2.2
  letI : Smooth (multiplicativeGroup k).X.hom := splitTorusSmooth (gm_split k)
  letI : ConnectedSpace M.val.X.left := splitTorus_connected (gm_split k)
  letI := geometricallyIrreducible_of_connected A
  letI : GeometricallyIrreducible (multiplicativeGroup k).X.hom := geometricallyIrreducible_of_connected M
  let X := A.val.X ⊗ (multiplicativeGroup k).X
  letI : IsAffine X.left := affine_tensor (A := A.val.X) (B := (multiplicativeGroup k).X)
  obtain ⟨hx, hi⟩ : Smooth X.hom ∧ GeometricallyIrreducible X.hom :=
    smooth_geometricallyIrreducible_tensor _ _
  haveI : IsIntegral (A.val.X ⊗ (multiplicativeGroup k).X).left :=
    (geometry_of_smooth_geometricallyIrreducible X).2.2
  letI := bigCell A (c ≫ T.inclusion) D E'
  have hf := universal_conjugates_factor D E' F
    (centralizes_cocharacters A T hT c d) hpos hneg'
  refine conjugates_of_nontrivial_into_proper_centralizer A hSimple (c ≫ T.inclusion) (d ≫ T.inclusion) F
    (cocharacter_ne_one_of_not_central ha') hb' hf (affine_tensor (A := A.val.X)
      (B := (multiplicativeGroup k).X)) ?_ ?_ (fun m ↦ affine_power (X := X) m) ?_
  · change LocallyOfFiniteType X.hom
    rw [Over.tensorObj_hom]
    infer_instance
  · change QuasiCompact X.hom
    rw [Over.tensorObj_hom]
    infer_instance
  · intro m
    obtain ⟨hs, hir⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2

private theorem relative_pairing_partition (A : AffineAlgebraicGroup k)
    (hA : IsAbsolutelyAlmostSimple A) (hRed : IsReductive A)
    (S : ClosedSubgroup A.val) (hS : IsMaximalSplitTorus S)
    {Q : QuotientData S} [IsCommMonObj S.group.X] (r : Specs.Relative.RelativeReflections.Datum Q)
    (P₁ P₂ : Set (relativeRoots S)) (hcover : P₁ ∪ P₂ = Set.univ)
    (hcross : ∀ a ∈ P₁, ∀ b ∈ P₂,
      pairing S.group b.val (r.reflection a).coroot = 0 ∧
      pairing S.group a.val (r.reflection b).coroot = 0) : P₁ = ∅ ∨ P₂ = ∅ := by
  classical
  by_contra! h
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨b, hb⟩ := h.2
  let c := (r.reflection a).coroot
  let d := (r.reflection b).coroot
  obtain ⟨T, _, ⟨hTK, hmax⟩, i, hi⟩ :=
    Relative.RelativeChambers.maximalTorusOverSplitTorus A hRed S hS
  let K := AlgebraicClosure k
  let A' := GeometricGroup A
  let T' : ClosedSubgroup A'.val := baseChangedSubgroup K T hTK
  have hT' : IsSplitTorus T'.group := split_of_maximal hmax
  have hmax' := geometricallyMaximal_of_maximal_split A' T' hmax hT'
  obtain ⟨e, he, _, hre⟩ := Relative.RelativeChambers.relativeRootsByRestriction A S T i hi
    hS.1 hTK hT'
  let F := groupBaseChange k K
  let c' : Cocharacter T'.group := e.hom ≫ F.map c ≫ F.map i
  let d' : Cocharacter T'.group := e.hom ≫ F.map d ≫ F.map i
  have liftRoot (x : relativeRoots S) :
      ∃ α : Root T', F.map i ≫ α.val = F.map x.val ≫ e.inv := by
    have hx := Set.mem_image_of_mem (fun a : Character S.group ↦ F.map a ≫ e.inv) x.property
    rw [hre] at hx
    obtain ⟨⟨α, hα, hEq⟩, _⟩ := hx
    exact ⟨⟨α, hα⟩, hEq⟩
  obtain ⟨α, hα⟩ := liftRoot a
  obtain ⟨β, hβ⟩ := liftRoot b
  have hαc : pairing T'.group α.val c' = 2 :=
    (pairing_extended K e he i a.val α.val hα c).trans (r.reflection a).rootPairing
  have hβd : pairing T'.group β.val d' = 2 :=
    (pairing_extended K e he i b.val β.val hβ d).trans (r.reflection b).rootPairing
  apply incompatible_cocharacters A' (reductive_geometricGroup A hRed) hA.2.2 T' hT' hmax'
    c' d' α β (hαc.trans_ne (by decide)) (hβd.trans_ne (by decide))
  intro root
  by_cases hroot : F.map i ≫ root.val = 1
  · exact Or.inl (pairing_restriction K e i root.val hroot (splitTorus_baseChange hS.1) c)
  have hg : F.map i ≫ root.val ∈
      (fun a : Character S.group ↦ F.map a ≫ e.inv) '' relativeRoots S := by
    rw [hre]
    exact ⟨⟨root.val, root.property, rfl⟩, hroot⟩
  obtain ⟨x, hx, hxroot⟩ := hg
  have hmem : (⟨x, hx⟩ : relativeRoots S) ∈ P₁ ∪ P₂ := by rw [hcover]; trivial
  rcases hmem with hp | hp
  · exact Or.inr ((pairing_extended K e he i x root.val hxroot.symm d).trans
      (hcross ⟨x, hx⟩ hp b hb).2)
  · exact Or.inl ((pairing_extended K e he i x root.val hxroot.symm c).trans
      (hcross a ha ⟨x, hx⟩ hp).1)

/-- The relative roots of an isotropic absolutely almost simple group form an
irreducible root system, with a connected simple diagram in every chamber. -/
theorem relativeRootIrreducibility : Statement.{u} := by
  intro k _ G hG S hS hnoncentral
  have hRed := reductive_of_semisimple G hG.1
  obtain ⟨D, _⟩ := Relative.RelativeWeylScheme.finiteConstantQuotient G hRed S hS
  obtain ⟨comm, hDatum⟩ := Relative.RelativeReflections.relativeRootDatum G hRed S hS D
  letI := comm
  obtain ⟨d⟩ := hDatum
  obtain ⟨c, X, g, hg⟩ := hnoncentral
  have hne : Nonempty (relativeRoots S) := by
    classical
    by_contra! h
    have he : Specs.Relative.RelativeChambers.relativeRoots S = ∅ := by
      ext a
      exact ⟨fun ha ↦ h.false ⟨a, ha⟩, False.elim⟩
    have hc := (Relative.RelativeChambers.emptyRelativeRoots G hRed S hS he).2.2 X g
    apply hg
    apply (centralizes_iff ..).mpr
    intro Y p t
    change Commute (p ≫ g) (t ≫ c.hom.hom ≫ S.inclusion.hom.hom)
    simpa only [Category.assoc] using (centralizes_iff ..).mp hc Y p (t ≫ c.hom.hom)
  exact rootConclusion_of_pairing_partitions d hne (relative_pairing_partition G hG hRed S hS d)

end NormalClosure

end
end LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
