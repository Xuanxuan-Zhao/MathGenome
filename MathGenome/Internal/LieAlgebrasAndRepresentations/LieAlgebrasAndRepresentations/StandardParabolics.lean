import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.StandardParabolics
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.BorelSubalgebras
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactFlagOrbit
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Batteries.Tactic.OpenPrivate
import Mathlib.Order.WellFoundedSet

noncomputable section

universe u

namespace LieAlgebrasAndRepresentations.StandardParabolics

open Module Set
open Specs.LieAlgebrasAndRepresentations.BorelSubalgebras
open Specs.LieAlgebrasAndRepresentations.CompactFlagOrbit
open Specs.LieAlgebrasAndRepresentations.CompactConjugation (PositiveRoot)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.StandardParabolics

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L}

section RealRoots

variable [Fact (Realization H)]

set_option hygiene false in
local notation "d" => (Fact.out : Realization H)
local instance : NormedAddCommGroup (E H) := (d).normedAddCommGroup
local instance : InnerProductSpace ℝ (E H) := (d).innerProductSpace

set_option hygiene false in
local notation "R" => realRoots H
set_option hygiene false in
local notation "ρ" => restrictRoot H
set_option hygiene false in
local notation "ε" => extension H (d).killing_positive

omit [Fact (Realization H)] in
private theorem restrict_mem {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) :
    ρ a ∈ R :=
  ⟨a, ha, rfl⟩

private theorem extend_restrict {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) :
    ε (ρ a) = a :=
  (d).extension_root a ha

private theorem extend_root {a : E H} (ha : a ∈ R) :
    ε a ∈ rootSet H ∧ ρ (ε a) = a := by
  obtain ⟨b, hb, rfl⟩ := ha
  change ε (ρ b) ∈ rootSet H ∧ ρ (ε (ρ b)) = ρ b
  rw [extend_restrict hb]
  exact ⟨hb, rfl⟩

variable {v : E H}
set_option hygiene false in
local notation "φ" => positiveFunctional d v
set_option hygiene false in
local notation "Π" => Simple d v

private theorem functional_apply (a : Module.Dual ℂ H) :
    φ a = inner ℝ v (ρ a) := rfl

private theorem functional_regular (hv : RootRegular R v) :
    ∀ a ∈ rootSet H, φ a ≠ 0 :=
  fun _ ha => hv _ (restrict_mem ha)

private theorem extend_positive {a : E H} (ha : a ∈ positiveRoots R v) :
    ε a ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ := by
  obtain ⟨hr, he⟩ := extend_root ha.1
  exact ⟨hr, by rw [functional_apply, he]; exact ha.2⟩

private theorem neg_root {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) :
    -a ∈ rootSet H := by
  have hn := (d).root_system.toRootAxioms.neg_mem (restrict_mem ha)
  simpa only [map_neg, extend_restrict ha] using (extend_root hn).1

variable (b : Basis Π ℝ (E H)) (hb : ∀ i, b i = (i : E H))
  (S : Set Π)

include hb in
private theorem coord_nonneg {a : E H} (ha : a ∈ positiveRoots R v) :
    ∀ i, 0 ≤ b.repr a i := by
  classical
  have h := positive_mem_closure_simple (d).root_system.toRootAxioms v ha
  refine AddSubmonoid.closure_induction (motive := fun a _ => ∀ i, 0 ≤ b.repr a i)
    (fun a ha i => ?_) (by simp) (fun x y _ _ hx hy i => ?_) h
  · have he : b ⟨a, ha⟩ = a := hb ⟨a, ha⟩
    rw [← he, b.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num
  · simpa only [map_add, Finsupp.add_apply] using add_nonneg (hx i) (hy i)

include hb in
private theorem mem_subsystem_iff {a : E H} :
    a ∈ subsystemSpan d v S ↔ ∀ i ∉ S, b.repr a i = 0 := by
  have he : b '' S = Subtype.val '' S := by
    ext x
    simp only [Set.mem_image, hb]
  change a ∈ Submodule.span ℝ (Subtype.val '' S) ↔ _
  rw [← he, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i hn)
  · intro h i hi
    by_contra hn
    exact hi (h i hn)

/-- The weights with nonnegative simple-root coordinates outside `S`.
This condition is closed under addition, so it gives bracket closure. -/
private def allowed : Set (Module.Dual ℂ H) :=
  {a | ∀ i ∉ S, 0 ≤ b.repr (ρ a) i}

private theorem zero_allowed : 0 ∈ allowed b S := by
  simp [allowed]

private theorem add_allowed {a c : Module.Dual ℂ H}
    (ha : a ∈ allowed b S) (hc : c ∈ allowed b S) :
    a + c ∈ allowed b S := by
  intro i hi
  simpa only [map_add, Finsupp.add_apply] using add_nonneg (ha i hi) (hc i hi)

include hb in
private theorem positive_allowed {a : Module.Dual ℂ H}
    (ha : a ∈ rootSet H) (hp : 0 < φ a) :
    a ∈ allowed b S :=
  fun i _ => coord_nonneg b hb ⟨restrict_mem ha, hp⟩ i

include hb in
private theorem negative_allowed_iff {a : Module.Dual ℂ H}
    (ha : a ∈ rootSet H) (hp : 0 < φ a) :
    -a ∈ allowed b S ↔ ρ a ∈ subsystemSpan d v S := by
  rw [mem_subsystem_iff b hb S]
  constructor
  · intro h i hi
    have hn := h i hi
    simp only [map_neg, Finsupp.neg_apply, neg_nonneg] at hn
    exact le_antisymm hn (coord_nonneg b hb ⟨restrict_mem ha, hp⟩ i)
  · intro h i hi
    simp only [map_neg, Finsupp.neg_apply, h i hi, neg_zero, le_refl]

private def allowedSpace : Submodule ℂ L :=
  ⨆ a ∈ allowed b S, rootSpace H a

private theorem rootSpace_le_allowedSpace {a : Module.Dual ℂ H} (ha : a ∈ allowed b S) :
    rootSpace H a ≤ allowedSpace b S :=
  le_iSup_of_le a (le_iSup (fun _ : a ∈ allowed b S => rootSpace H a) ha)

include hb in
private theorem allowedSpace_eq (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) :
    allowedSpace b S = parabolicSpace d v S := by
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    by_cases hz : a = 0
    · subst a
      rw [rootSpace_zero hss H hH]
      exact le_sup_left.trans le_sup_left
    by_cases hr : a ∈ rootSet H
    · rcases lt_or_gt_of_ne (functional_regular hv a hr) with hn | hp
      · have hn' : 0 < φ (-a) := by simpa only [map_neg, neg_pos] using hn
        have hr' := neg_root hr
        have hs := (negative_allowed_iff b hb S hr' hn').mp (by simpa only [neg_neg] using ha)
        let i : {a : PositiveRoot H φ // ρ a.val ∈ subsystemSpan d v S} :=
          ⟨⟨-a, hr', hn'⟩, hs⟩
        have hle : rootSpace H (-i.val.val) ≤ parabolicSpace d v S :=
          (le_iSup (fun j : {a : PositiveRoot H φ // ρ a.val ∈ subsystemSpan d v S} =>
            rootSpace H (-j.val.val)) i).trans le_sup_right
        change rootSpace H (-(-a)) ≤ _ at hle
        rwa [neg_neg] at hle
      · exact (le_iSup (fun a : PositiveRoot H φ => rootSpace H a.val) ⟨a, hr, hp⟩).trans
          (le_sup_right.trans le_sup_left)
    · rw [rootSpace_eq_bot_of_not_mem H a hz hr]
      exact bot_le
  · refine sup_le (sup_le ?_ (iSup_le fun a => ?_)) (iSup_le fun a => ?_)
    · rw [← rootSpace_zero hss H hH]
      exact rootSpace_le_allowedSpace b S (zero_allowed b S)
    · exact rootSpace_le_allowedSpace b S (positive_allowed b hb S a.property.1 a.property.2)
    · exact rootSpace_le_allowedSpace b S
        ((negative_allowed_iff b hb S a.val.property.1 a.val.property.2).mpr a.property)

private theorem allowedSpace_lie_mem {x y : L}
    (hx : x ∈ allowedSpace b S) (hy : y ∈ allowedSpace b S) :
    ⁅x, y⁆ ∈ allowedSpace b S := by
  rw [allowedSpace, ← iSup_subtype'' (allowed b S) (rootSpace H)] at hx hy
  let F := fun a : allowed b S => rootSpace H a.val
  refine Submodule.iSup_induction F (motive := fun z => ⁅z, y⁆ ∈ allowedSpace b S)
    hx ?_ (by simp) ?_
  · intro a x hx
    refine Submodule.iSup_induction F (motive := fun z => ⁅x, z⁆ ∈ allowedSpace b S)
      hy ?_ (by simp) ?_
    · intro c y hy
      exact rootSpace_le_allowedSpace b S (add_allowed b S a.property c.property)
        (rootSpace_bracket H a.val c.val x y hx hy)
    · intro u w hu hw
      rw [lie_add]
      exact Submodule.add_mem _ hu hw
  · intro u w hu hw
    rw [add_lie]
    exact Submodule.add_mem _ hu hw

private def subalgebraOfSubset (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) (B : LieSubalgebra ℂ L) (hB : B.toSubmodule = borel H φ) :
    {P : LieSubalgebra ℂ L // B ≤ P} := by
  refine ⟨{ toSubmodule := allowedSpace b S, lie_mem' := allowedSpace_lie_mem b S }, ?_⟩
  change B.toSubmodule ≤ allowedSpace b S
  rw [hB, allowedSpace_eq b hb S hss hH hv]
  exact le_sup_left

include b hb in
private theorem negative_le_parabolic_iff (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) (hp : 0 < φ a) :
    rootSpace H (-a) ≤ parabolicSpace d v S ↔ ρ a ∈ subsystemSpan d v S := by
  rw [← allowedSpace_eq b hb S hss hH hv, ← negative_allowed_iff b hb S ha hp]
  refine ⟨fun h => ?_, rootSpace_le_allowedSpace b S⟩
  by_contra hn
  have hd := (rootSpace_independent H hH.1).disjoint_biSup hn
  exact (neg_root ha).2 (disjoint_self.mp (hd.mono_right h))

omit [Fact (Realization H)] in
private theorem rootSpace_le_of_nonzero_mem (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) {Q : Submodule ℂ L} {x : L}
    (hx : x ∈ rootSpace H a) (hx₀ : x ≠ 0) (hxQ : x ∈ Q) :
    rootSpace H a ≤ Q := by
  intro y hy
  let x' : rootSpace H a := ⟨x, hx⟩
  have hx' : x' ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' x' hx').mp
    (finrank_rootSpace_eq_one hss H hH a ha) ⟨y, hy⟩
  have he : c • x = y := congrArg Subtype.val hc
  rw [← he]
  exact Q.smul_mem c hxQ

omit [Fact (Realization H)] in
private theorem rootSpace_add_le (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (P : LieSubalgebra ℂ L) {a c : Module.Dual ℂ H}
    (ha : a ∈ rootSet H) (hc : c ∈ rootSet H) (hac : a + c ∈ rootSet H)
    (haP : rootSpace H a ≤ P.toSubmodule) (hcP : rootSpace H c ≤ P.toSubmodule) :
    rootSpace H (a + c) ≤ P.toSubmodule := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha.2
  obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  exact rootSpace_le_of_nonzero_mem hss hH hac (rootSpace_bracket H a c x y hx hy)
    (RootStrings.root_bracket_ne_zero hss H hH a c ha hc hac x y hx hy hx₀ hy₀)
    (P.lie_mem (haP hx) (hcP hy))

private theorem positive_le_borel {a : Module.Dual ℂ H} (ha : a ∈ rootSet H)
    (hp : 0 < φ a) :
    rootSpace H a ≤ borel H φ :=
  (le_iSup (fun i : PositiveRoot H φ => rootSpace H i.val) ⟨a, ha, hp⟩).trans le_sup_right

private def subsetOfSubalgebra (P : LieSubalgebra ℂ L) : Set Π :=
  {a | rootSpace H (-ε a.val) ≤ P.toSubmodule}

include b hb in
private theorem simple_mem_subsystem_iff (i : Π) :
    (i : E H) ∈ subsystemSpan d v S ↔ i ∈ S := by
  classical
  rw [mem_subsystem_iff b hb S, ← hb i, b.repr_self]
  constructor
  · intro h
    by_contra hi
    simpa using h i hi
  · intro hi j hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]

include b hb in
/-- The negative root spaces present in an over-algebra are exactly those
supported on its included negative simple root spaces. -/
private theorem negative_le_iff (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) (P : LieSubalgebra ℂ L) (hBP : borel H φ ≤ P.toSubmodule)
    {β : E H} (hβ : β ∈ positiveRoots R v) :
    rootSpace H (-ε β) ≤ P.toSubmodule ↔ β ∈ subsystemSpan d v (subsetOfSubalgebra P) := by
  let T := positiveRoots R v
  let f : T → ℝ := fun x => inner ℝ v x.val
  have hfin : (Set.range f).Finite := by
    let : Finite T := ((d).root_system.toRootAxioms.finite.subset
      (fun _ h => h.1) : T.Finite).to_subtype
    exact Set.finite_range f
  have hw : WellFounded (fun x y : T => f x < f y) :=
    (Set.wellFoundedOn_range (r := (· < ·))).mp hfin.wellFoundedOn
  let β' : T := ⟨β, hβ⟩
  change rootSpace H (-ε β'.val) ≤ P.toSubmodule ↔
    β'.val ∈ subsystemSpan d v (subsetOfSubalgebra P)
  refine hw.induction (C := fun x => rootSpace H (-ε x.val) ≤ P.toSubmodule ↔
    x.val ∈ subsystemSpan d v (subsetOfSubalgebra P)) β' ?_
  intro x ih
  by_cases hsimple : x.val ∈ simpleRoots R v
  · exact (simple_mem_subsystem_iff b hb (subsetOfSubalgebra P) ⟨x.val, hsimple⟩).symm
  obtain ⟨α, hα, hγ⟩ := simpleRoots_lowering R (d).root_system v hv x.val x.property hsimple
  let γ := x.val - α
  have hx : x.val = α + γ := by dsimp [γ]; abel
  have hαp := extend_positive hα.1
  have hγp := extend_positive hγ
  have hxp := extend_positive x.property
  have hsum : ε x.val = ε α + ε γ := by rw [hx, map_add]
  have hγlt : f ⟨γ, hγ⟩ < f x := by
    dsimp [f]
    rw [hx, inner_add_right]
    have := hα.1.2
    linarith
  have hγih := ih ⟨γ, hγ⟩ hγlt
  have hαP := (positive_le_borel hαp.1 hαp.2).trans hBP
  have hγP := (positive_le_borel hγp.1 hγp.2).trans hBP
  have he₁ : ε α + -ε x.val = -ε γ := by rw [hsum]; abel
  have he₂ : ε γ + -ε x.val = -ε α := by rw [hsum]; abel
  have he₃ : -ε α + -ε γ = -ε x.val := by rw [hsum]; abel
  have hnx := neg_root hxp.1
  have hnα := neg_root hαp.1
  have hnγ := neg_root hγp.1
  have hαspan : α ∈ subsystemSpan d v (subsetOfSubalgebra P) ↔
      rootSpace H (-ε α) ≤ P.toSubmodule :=
    simple_mem_subsystem_iff b hb (subsetOfSubalgebra P) ⟨α, hα⟩
  constructor
  · intro hxP
    have hg : rootSpace H (-ε γ) ≤ P.toSubmodule := by
      rw [← he₁]
      exact rootSpace_add_le hss hH P hαp.1 hnx (he₁.symm ▸ hnγ) hαP hxP
    have ha : rootSpace H (-ε α) ≤ P.toSubmodule := by
      rw [← he₂]
      exact rootSpace_add_le hss hH P hγp.1 hnx (he₂.symm ▸ hnα) hγP hxP
    rw [hx]
    exact Submodule.add_mem _ (hαspan.mpr ha) (hγih.mp hg)
  · intro hxs
    have hparts : α ∈ subsystemSpan d v (subsetOfSubalgebra P) ∧
        γ ∈ subsystemSpan d v (subsetOfSubalgebra P) := by
      rw [mem_subsystem_iff b hb, mem_subsystem_iff b hb]
      have hcoord := (mem_subsystem_iff b hb (subsetOfSubalgebra P)).mp hxs
      rw [hx, map_add] at hcoord
      have hzeros (i : Π) (hi : i ∉ subsetOfSubalgebra P) :
          b.repr α i = 0 ∧ b.repr γ i = 0 := by
        have h := hcoord i hi
        change b.repr α i + b.repr γ i = 0 at h
        have ha := coord_nonneg b hb hα.1 i
        have hg := coord_nonneg b hb hγ i
        exact ⟨by linarith, by linarith⟩
      exact ⟨fun i hi => (hzeros i hi).1, fun i hi => (hzeros i hi).2⟩
    rw [← he₃]
    exact rootSpace_add_le hss hH P hnα hnγ (he₃.symm ▸ hnx)
      (hαspan.mp hparts.1) (hγih.mpr hparts.2)

open private rootSpace_eq_gen from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition

include b hb in
private theorem parabolicSpace_subsetOfSubalgebra (hss : IsSemisimple ℂ L)
    (hH : IsMaximalToral H) (hv : RootRegular R v)
    (P : LieSubalgebra ℂ L) (hBP : borel H φ ≤ P.toSubmodule) :
    parabolicSpace d v (subsetOfSubalgebra P) = P.toSubmodule := by
  have hHP : H.toSubmodule ≤ P.toSubmodule := le_sup_left.trans hBP
  have hneg (a : PositiveRoot H φ) :
      rootSpace H (-a.val) ≤ P.toSubmodule ↔ ρ a.val ∈ subsystemSpan d v (subsetOfSubalgebra P) := by
    have hp : ρ a.val ∈ positiveRoots R v := ⟨restrict_mem a.property.1, a.property.2⟩
    simpa only [extend_restrict a.property.1] using negative_le_iff b hb hss hH hv P hBP hp
  apply le_antisymm
  · exact sup_le hBP (iSup_le fun a => (hneg a.val).mpr a.property)
  let : IsLieAbelian H := hH.1.1
  let N : LieSubmodule ℂ H L :=
    { P.toSubmodule with lie_mem := fun {x y} hy => P.lie_mem (hHP x.property) hy }
  have hN := congrArg LieSubmodule.toSubmodule (LieModule.eq_iSup_inf_genWeightSpace ℂ H L N)
  simp only [LieSubmodule.iSup_toSubmodule, LieSubmodule.inf_toSubmodule] at hN
  change P.toSubmodule = _ at hN
  rw [hN]
  refine iSup_le fun χ => ?_
  let a : Module.Dual ℂ H := χ
  have he := rootSpace_eq_gen H hH.1 a
  simp only [a, LieModule.Weight.coe_coe] at he
  rw [← he]
  change P.toSubmodule ⊓ rootSpace H a ≤ _
  by_cases ha₀ : a = 0
  · rw [ha₀, rootSpace_zero hss H hH]
    exact inf_le_right.trans (le_sup_left.trans le_sup_left)
  by_cases hi : P.toSubmodule ⊓ rootSpace H a = ⊥
  · rw [hi]
    exact bot_le
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
  have ha : a ∈ rootSet H := ⟨ha₀, fun h => hx₀ ((Submodule.mem_bot ℂ).mp (h ▸ hx.2))⟩
  rcases lt_or_gt_of_ne (functional_regular hv a ha) with hn | hp
  · have hp' : 0 < φ (-a) := by simpa only [map_neg, neg_pos] using hn
    let i : PositiveRoot H φ := ⟨-a, neg_root ha, hp'⟩
    have haP := rootSpace_le_of_nonzero_mem hss hH ha hx.2 hx₀ hx.1
    have hiP : rootSpace H (-i.val) ≤ P.toSubmodule := by
      change rootSpace H (-(-a)) ≤ _
      simpa only [neg_neg] using haP
    let j : {a : PositiveRoot H φ // ρ a.val ∈ subsystemSpan d v (subsetOfSubalgebra P)} :=
      ⟨i, (hneg i).mp hiP⟩
    have hle : rootSpace H (-j.val.val) ≤ parabolicSpace d v (subsetOfSubalgebra P) :=
      (le_iSup (fun k : {a : PositiveRoot H φ //
        ρ a.val ∈ subsystemSpan d v (subsetOfSubalgebra P)} => rootSpace H (-k.val.val)) j).trans
        le_sup_right
    change rootSpace H (-(-a)) ≤ _ at hle
    rw [neg_neg] at hle
    exact inf_le_right.trans hle
  · exact inf_le_right.trans ((positive_le_borel ha hp).trans le_sup_left)

include b hb in
private theorem subsetOfSubalgebra_ofSubset (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) (B : LieSubalgebra ℂ L) (hB : B.toSubmodule = borel H φ) :
    subsetOfSubalgebra (subalgebraOfSubset b hb S hss hH hv B hB).val = S := by
  ext i
  have hi := extend_positive i.property.1
  have hir := (extend_root i.property.1.1).2
  change rootSpace H (-ε i.val) ≤ allowedSpace b S ↔ i ∈ S
  rw [allowedSpace_eq b hb S hss hH hv,
    negative_le_parabolic_iff b hb S hss hH hv hi.1 hi.2, hir,
    simple_mem_subsystem_iff b hb S]

include b hb in
private def subsetEquiv (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hv : RootRegular R v) (B : LieSubalgebra ℂ L) (hB : B.toSubmodule = borel H φ) :
    Set Π ≃ {P : LieSubalgebra ℂ L // B ≤ P} where
  toFun S := subalgebraOfSubset b hb S hss hH hv B hB
  invFun P := subsetOfSubalgebra P.val
  left_inv S := subsetOfSubalgebra_ofSubset b hb S hss hH hv B hB
  right_inv P := by
    apply Subtype.ext
    apply LieSubalgebra.toSubmodule_injective
    change allowedSpace b (subsetOfSubalgebra P.val) = P.val.toSubmodule
    rw [allowedSpace_eq b hb _ hss hH hv]
    exact parabolicSpace_subsetOfSubalgebra b hb hss hH hv P.val (hB ▸ P.property)

private theorem parabolicSpace_empty : parabolicSpace d v ∅ = borel H φ := by
  apply sup_eq_left.mpr
  refine iSup_le fun a => ?_
  have h := a.property
  have hz : ρ a.val.val = 0 := by simpa [subsystemSpan] using h
  have hp := a.val.property.2
  change 0 < φ a.val.val at hp
  rw [functional_apply, hz, inner_zero_right] at hp
  exact (lt_irrefl _ hp).elim

private theorem allowedSpace_univ (hH : IsMaximalToral H) :
    allowedSpace b Set.univ = ⊤ := by
  have he : allowed b Set.univ = Set.univ := by ext a; simp [allowed]
  rw [allowedSpace, he]
  simpa using iSup_rootSpace_eq_top H hH.1

private theorem rootSummands_independent (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) :
    Disjoint (borel H φ) (negativeSpace d v S) ∧
      iSupIndep (fun a : SubsystemPositiveRoot d v S => rootSpace H (-a.val.val)) := by
  let I := insert 0 (Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ)
  let index := fun a : SubsystemPositiveRoot d v S => -a.val.val
  have hi := rootSpace_independent H hH.1
  refine ⟨?_, hi.comp (fun a c hac => Subtype.ext (Subtype.ext (neg_injective hac)))⟩
  have hdisj : Disjoint I (Set.range index) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨j, rfl⟩
    have hp := j.val.property.2
    change 0 < φ j.val.val at hp
    have hn : φ (index j) < 0 := by
      change φ (-j.val.val) < 0
      rw [map_neg]
      exact neg_neg_of_pos hp
    rcases Set.mem_insert_iff.mp ha with hz | hpos
    · rw [hz, map_zero] at hn
      exact (lt_irrefl 0) hn
    · exact (not_lt_of_ge hpos.2.le) hn
  refine (hi.disjoint_biSup_biSup hdisj).mono ?_ ?_
  · refine sup_le ?_ (iSup_le fun a => ?_)
    · rw [← rootSpace_zero hss H hH]
      exact le_iSup_of_le 0 (le_iSup (fun _ : (0 : Module.Dual ℂ H) ∈ I => rootSpace H 0)
        (Set.mem_insert _ _))
    · exact le_iSup_of_le a.val (le_iSup (fun _ : a.val ∈ I => rootSpace H a.val)
        (Set.mem_insert_of_mem _ a.property))
  · refine iSup_le fun a => le_iSup_of_le (index a) ?_
    exact le_iSup (fun _ : index a ∈ Set.range index => rootSpace H (index a))
      (Set.mem_range_self a)

end RealRoots

open private identityComponent_automorphisms_eq_innerGroup
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactFlagOrbit

/-- Standard parabolics are indexed by subsets of the chosen simple roots.
Every subalgebra containing a Borel is an inner conjugate of one of them. -/
theorem classification : classificationType.{u} := by
  intro L _ _ _ hss H hH
  let d₀ := RealRootSpace.realization_of_maximalToral hss H hH
  let : Fact (Realization H) := ⟨d₀⟩
  let := d₀.normedAddCommGroup
  let := d₀.innerProductSpace
  refine ⟨d₀, ?_⟩
  intro v hv
  let φ₀ := positiveFunctional d₀ v
  obtain ⟨B, hB, hBorel, _⟩ :=
    BorelSubalgebras.standard_borel hss H hH φ₀ (functional_regular hv)
  obtain ⟨b, hb⟩ := simpleRoots_basis (realRoots H) d₀.root_system v hv
  let e := subsetEquiv b hb hss hH hv B hB
  have he (S : Set (Simple d₀ v)) : (e S).val.toSubmodule = parabolicSpace d₀ v S :=
    allowedSpace_eq b hb S hss hH hv
  refine ⟨B, hB, hBorel, e, he, ?_, ?_, ?_, ?_⟩
  · intro S
    rw [hB]
    exact rootSummands_independent S hss hH
  · apply LieSubalgebra.toSubmodule_injective
    rw [he, parabolicSpace_empty, hB]
  · apply LieSubalgebra.toSubmodule_injective
    change allowedSpace b univ = ⊤
    exact allowedSpace_univ b hH
  obtain ⟨τ, hs, hp, hc⟩ := BorelSubalgebras.all_borels_conjugate hss
  let c := hermitianCore τ hs hp
  let : InnerProductSpace.Core ℂ L := c
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
  let : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
  refine ⟨τ, hs, hp, ?_⟩
  intro P hP
  obtain ⟨A, hA, hAP⟩ := hP
  obtain ⟨g, hg, hAg⟩ := hc B A hBorel hA
  let G := automorphisms (fun v w : L => ⁅v, w⁆)
  have hgG : g ∈ G := by
    have hgi := hg
    rw [← identityComponent_automorphisms_eq_innerGroup hss] at hgi
    obtain ⟨g', _, rfl⟩ := Subgroup.mem_map.mp hgi
    exact g'.property
  let f : L →ₗ⁅ℂ⁆ L := { g.val.toLinearMap with map_lie' := fun {x y} => hgG x y }
  let Q : {Q : LieSubalgebra ℂ L // B ≤ Q} :=
    ⟨P.comap f, fun x hx => by
      apply hAP
      change g.val x ∈ A.toSubmodule
      rw [hAg]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩⟩
  refine ⟨e.symm Q, g, hg, ?_⟩
  rw [e.apply_symm_apply]
  change P.toSubmodule = (P.toSubmodule.comap g.val.toLinearMap).map g.val.toLinearMap
  exact (Submodule.map_comap_eq_of_surjective (unitEquiv g).surjective _).symm

end LieAlgebrasAndRepresentations.StandardParabolics
