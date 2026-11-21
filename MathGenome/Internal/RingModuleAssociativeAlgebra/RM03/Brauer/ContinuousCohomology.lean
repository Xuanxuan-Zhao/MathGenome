import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ContinuousCohomology
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.FiniteCochains
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
import Mathlib.Data.Fin.VecNotation

/-! The finite Galois stages compute continuous scalar second cohomology. -/

namespace RM03.Brauer.ContinuousCohomology

open ScalarObstruction groupCohomology
open Specs.RM03.Brauer.ContinuousCohomology

universe u v

noncomputable section

variable {k : Type u} {S : Type v} [Field k] [Field S] [Algebra k S]

/-- Continuous scalar second cohomology of the absolute Galois group. -/
abbrev H2Continuous (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S] :=
  H2ContinuousValue k S

local instance : TopologicalSpace Sˣ := ⊥
local instance : DiscreteTopology Sˣ := ⟨rfl⟩

theorem coboundary_continuous : CoboundaryContinuous.{u,v} := by
  intro k S _ _ _ _
  let : TopologicalSpace Sˣ := ⊥
  let : DiscreteTopology Sˣ := ⟨rfl⟩
  let := continuousUnitAction (k := k) (S := S)
  intro a
  have ha : Continuous a.val := a.property
  change Continuous (fun p : Gal(S/k) × Gal(S/k) =>
    p.1 • a.val p.2 / a.val (p.1 * p.2) * a.val p.1)
  simp only [div_eq_mul_inv]
  exact ((continuous_fst.smul (ha.comp continuous_snd)).mul
    (ha.comp (continuous_fst.mul continuous_snd)).inv).mul (ha.comp continuous_fst)

variable {E F L : Stage k S}

@[simp] theorem inflateCocycle_apply (h : E ≤ F) (c : ScalarCocycle k E) (g j : Gal(F/k)) :
    (inflateCocycle h c).val (g,j) =
      stageUnits h (c.val (stageRestrict h g, stageRestrict h j)) := rfl

@[simp] theorem inflate_class (h : E ≤ F) (c : ScalarCocycle k E) :
    inflate h (cocycleClass k E c) = cocycleClass k F (inflateCocycle h c) := rfl

theorem inflate_formula : InflateFormula.{u,v} :=
  fun h c => ⟨fun _ _ => inflateCocycle_apply h c _ _, inflate_class h c⟩

@[simp] theorem toContinuousCocycle_apply (E : Stage k S) (c : ScalarCocycle k E)
    (g j : Gal(S/k)) :
    (toContinuousCocycle E c).val.val (g,j) =
      absoluteUnits E (c.val (absoluteRestrict E g, absoluteRestrict E j)) := rfl

@[simp] theorem toContinuous_class (E : Stage k S) (c : ScalarCocycle k E) :
    toContinuous E (cocycleClass k E c) = continuousClass (toContinuousCocycle E c) := rfl

theorem toContinuous_formula : ToContinuousFormula.{u,v} :=
  fun E c => ⟨fun _ _ => toContinuousCocycle_apply E c _ _, toContinuous_class E c⟩

private theorem absoluteUnits_injective (E : Stage k S) :
    Function.Injective (absoluteUnits E) :=
  Units.map_injective Subtype.val_injective

private theorem stageRestrict_absoluteRestrict (h : E ≤ F) (g : Gal(S/k)) :
    stageRestrict h (absoluteRestrict F g) = absoluteRestrict E g := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  have heq := congrArg (fun y : F => (y : S)) (stageRestrict_apply h (absoluteRestrict F g) x)
  change (((stageRestrict h (absoluteRestrict F g)) x : E) : S) =
    (absoluteRestrict F g ((IntermediateField.inclusion h) x) : S) at heq
  simpa only [AlgEquiv.restrictNormalHom_apply, IntermediateField.coe_inclusion] using heq

private theorem toContinuousCocycle_inflate (h : E ≤ F) (c : ScalarCocycle k E) :
    toContinuousCocycle F (inflateCocycle h c) = toContinuousCocycle E c := by
  apply Subtype.ext
  apply Subtype.ext
  funext p
  rcases p with ⟨g,j⟩
  simp only [toContinuousCocycle_apply, inflateCocycle_apply, stageRestrict_absoluteRestrict]
  rfl

variable [IsSepClosure k S]

private theorem absoluteRestrict_surjective (E : Stage k S) :
    Function.Surjective (absoluteRestrict E) :=
  (restrictionQuotient E).surjective

private theorem toContinuousCocycle_injective (E : Stage k S) :
    Function.Injective (toContinuousCocycle E) := by
  intro c d h
  apply Subtype.ext
  funext p
  obtain ⟨g, hg⟩ := absoluteRestrict_surjective E p.1
  obtain ⟨j, hj⟩ := absoluteRestrict_surjective E p.2
  apply absoluteUnits_injective E
  have heq := congrArg (fun a : continuousCocycles k S => a.val.val (g,j)) h
  simpa only [toContinuousCocycle_apply, hg, hj, Prod.eta] using heq

omit [IsSepClosure k S] in
theorem toContinuous_compatible (h : E ≤ F) :
    (toContinuous F).comp (inflate h) = toContinuous E := by
  apply MonoidHom.ext
  intro a
  obtain ⟨c, rfl⟩ := cocycleClass_surjective a
  simp only [MonoidHom.comp_apply, inflate_class, toContinuous_class, toContinuousCocycle_inflate]

private theorem inflateCocycle_refl (E : Stage k S) (c : ScalarCocycle k E) :
    inflateCocycle (le_refl E) c = c :=
  toContinuousCocycle_injective E (toContinuousCocycle_inflate (le_refl E) c)

private theorem inflateCocycle_trans (hEF : E ≤ F) (hFL : F ≤ L) (c : ScalarCocycle k E) :
    inflateCocycle hFL (inflateCocycle hEF c) = inflateCocycle (hEF.trans hFL) c := by
  apply toContinuousCocycle_injective L
  simp only [toContinuousCocycle_inflate]

theorem inflation_directedSystem :
    DirectedSystem (fun E : Stage k S => H2 k E) (fun _ _ h => inflate h) where
  map_self E a := by
    obtain ⟨c, rfl⟩ := cocycleClass_surjective a
    simp only [inflate_class, inflateCocycle_refl]
  map_map E F L hEF hFL a := by
    obtain ⟨c, rfl⟩ := cocycleClass_surjective a
    simp only [inflate_class, inflateCocycle_trans]

/-- Every continuous two-cocycle comes from a finite Galois stage. -/
theorem finite_cocycle_representative (c : continuousCocycles k S) :
    ∃ (E : Stage k S) (a : ScalarCocycle k E), toContinuousCocycle E a = c := by
  let f (t : Fin 2 → Gal(S/k)) := c.val.val (t 0, t 1)
  have hf : Continuous f := c.property.comp ((continuous_apply 0).prodMk (continuous_apply 1))
  obtain ⟨E, fE, hE⟩ := finiteCochainFactorization 2 f hf
  let a (p : Gal(E/k) × Gal(E/k)) := fE ![p.1,p.2]
  have ha (g j : Gal(S/k)) :
      absoluteUnits E (a (absoluteRestrict E g, absoluteRestrict E j)) = c.val.val (g,j) := by
    have htuple : (fun i => absoluteRestrict E (![g,j] i)) =
        ![absoluteRestrict E g, absoluteRestrict E j] := by
      funext i
      fin_cases i <;> rfl
    change absoluteUnits E (fE ![absoluteRestrict E g, absoluteRestrict E j]) = _
    rw [← htuple]
    exact hE ![g,j]
  have law : IsMulCocycle₂ a := by
    intro g j m
    obtain ⟨g', rfl⟩ := absoluteRestrict_surjective E g
    obtain ⟨j', rfl⟩ := absoluteRestrict_surjective E j
    obtain ⟨m', rfl⟩ := absoluteRestrict_surjective E m
    apply absoluteUnits_injective E
    simp only [map_mul (absoluteUnits E), absoluteUnits_smul, ← map_mul (absoluteRestrict E), ha]
    exact c.val.property g' j' m'
  refine ⟨E, ⟨a, law⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext p
  exact ha p.1 p.2

/-- Every continuous class is the inflation of a class at a finite stage. -/
theorem finite_class_representative (x : H2Continuous k S) :
    ∃ (E : Stage k S) (a : H2 k E), toContinuous E a = x := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨E, a, ha⟩ := finite_cocycle_representative c
  exact ⟨E, cocycleClass k E a, congrArg continuousClass ha⟩

private theorem one_cochain_at_stage (t : continuousOneCochains k S) (E₀ : Stage k S) :
    ∃ (L : Stage k S), E₀ ≤ L ∧ ∃ b : Gal(L/k) → Lˣ,
      ∀ g, absoluteUnits L (b (absoluteRestrict L g)) = t.val g := by
  let f (_ : Unit) (p : Fin 1 → Gal(S/k)) := t.val (p 0)
  have hf (i : Unit) : Continuous (f i) := t.property.comp (continuous_apply 0)
  obtain ⟨L, hEL, fL, hL⟩ := commonCochainFactorization Unit (fun _ => 1) f hf E₀
  exact ⟨L, hEL, fun g => fL () (fun _ => g), fun g => hL () (fun _ => g)⟩

/-- Equality of inflated classes is equivalent to equality at a common finite stage. -/
theorem equal_at_finite_stage {E F : Stage k S} (a : H2 k E) (b : H2 k F) :
    toContinuous E a = toContinuous F b ↔
    ∃ (L : Stage k S) (hE : E ≤ L) (hF : F ≤ L), inflate hE a = inflate hF b := by
  constructor
  · obtain ⟨c, rfl⟩ := cocycleClass_surjective a
    obtain ⟨d, rfl⟩ := cocycleClass_surjective b
    intro h
    simp only [toContinuous_class] at h
    have hmem : toContinuousCocycle E c / toContinuousCocycle F d ∈ continuousCoboundaries k S :=
      QuotientGroup.eq_iff_div_mem.mp h
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨L, hL, tL, htL⟩ := one_cochain_at_stage t (E ⊔ F)
    have hE : E ≤ L := le_sup_left.trans hL
    have hF : F ≤ L := le_sup_right.trans hL
    refine ⟨L, hE, hF, ?_⟩
    simp only [inflate_class]
    apply QuotientGroup.eq_iff_div_mem.mpr
    refine ⟨tL, toContinuousCocycle_injective L ?_⟩
    rw [map_div, toContinuousCocycle_inflate, toContinuousCocycle_inflate]
    apply Subtype.ext
    apply Subtype.ext
    funext p
    rcases p with ⟨g,j⟩
    have hval := congrArg (fun a : ScalarCocycle k S => a.val (g,j)) ht
    change g • t.val j / t.val (g * j) * t.val g = _ at hval
    rw [toContinuousCocycle_apply]
    change absoluteUnits L (absoluteRestrict L g • tL (absoluteRestrict L j) /
      tL (absoluteRestrict L g * absoluteRestrict L j) * tL (absoluteRestrict L g)) = _
    simpa only [map_mul (absoluteUnits L), map_div (absoluteUnits L), absoluteUnits_smul,
      ← map_mul (absoluteRestrict L), htL]
      using hval
  · rintro ⟨L, hE, hF, h⟩
    have he := DFunLike.congr_fun (toContinuous_compatible hE) a
    have hf := DFunLike.congr_fun (toContinuous_compatible hF) b
    exact he.symm.trans ((congrArg (toContinuous L) h).trans hf)

private def comparisonStage (I : Stage k S) : StageCohomology I →+ Additive (H2Continuous k S) :=
  (toContinuous I).toAdditive

omit [IsSepClosure k S] in
private theorem comparisonStage_compatible (I J : Stage k S) (h : I ≤ J)
    (x : StageCohomology I) :
    comparisonStage J (stageTransition I J h x) = comparisonStage I x :=
  DFunLike.congr_fun (toContinuous_compatible h) x.toMul

private def directedLimitEquiv {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    [DecidableEq ι] {A : ι → Type v} [∀ i, AddCommMonoid (A i)] {B : Type v} [AddCommMonoid B]
    (f : ∀ i j, i ≤ j → A i →+ A j) (g : ∀ i, A i →+ B)
    (compatible : ∀ i j hij x, g j (f i j hij x) = g i x)
    (covers : ∀ y, ∃ i x, g i x = y)
    (reflects : ∀ {i j} (x : A i) (y : A j), g i x = g j y →
      ∃ (l : ι) (hi : i ≤ l) (hj : j ≤ l), f i l hi x = f j l hj y) :
    {e : AddCommGroup.DirectLimit A f ≃+ B //
      ∀ i x, e (AddCommGroup.DirectLimit.of A f i x) = g i x} := by
  let m := AddCommGroup.DirectLimit.lift A f B g compatible
  have hm (i : ι) (x : A i) : m (AddCommGroup.DirectLimit.of A f i x) = g i x :=
    AddCommGroup.DirectLimit.lift_of B g compatible i x
  have hinj : Function.Injective m := by
    intro a b hab
    induction a using AddCommGroup.DirectLimit.induction_on with
    | ih i x =>
      induction b using AddCommGroup.DirectLimit.induction_on with
      | ih j y =>
        simp only [hm] at hab
        obtain ⟨l, hi, hj, h⟩ := reflects x y hab
        calc
          AddCommGroup.DirectLimit.of A f i x =
              AddCommGroup.DirectLimit.of A f l (f i l hi x) :=
            (AddCommGroup.DirectLimit.of_f hi x).symm
          _ = AddCommGroup.DirectLimit.of A f l (f j l hj y) :=
            congrArg (AddCommGroup.DirectLimit.of A f l) h
          _ = AddCommGroup.DirectLimit.of A f j y := AddCommGroup.DirectLimit.of_f hj y
  have hsurj : Function.Surjective m := by
    intro y
    obtain ⟨i, x, hx⟩ := covers y
    exact ⟨AddCommGroup.DirectLimit.of A f i x, (hm i x).trans hx⟩
  exact ⟨AddEquiv.ofBijective m ⟨hinj, hsurj⟩, hm⟩

private def comparison :
    {e : FiniteH2Limit k S ≃+ Additive (H2Continuous k S) //
      ∀ (I : Stage k S) (x : StageCohomology I), e (limitOf I x) = comparisonStage I x} := by
  letI := Classical.decEq (Stage k S)
  refine directedLimitEquiv (ι := Stage k S) (A := @StageCohomology k S _ _ _)
    (B := Additive (H2Continuous k S)) (@stageTransition k S _ _ _)
    (@comparisonStage k S _ _ _) (@comparisonStage_compatible k S _ _ _) ?_ ?_
  · intro x
    obtain ⟨I, a, ha⟩ := finite_class_representative x.toMul
    exact ⟨I, Additive.ofMul a, congrArg Additive.ofMul ha⟩
  · intro I J x y h
    obtain ⟨L, hI, hJ, hEq⟩ := (equal_at_finite_stage x.toMul y.toMul).mp
      (Additive.ofMul.injective h)
    exact ⟨L, hI, hJ, congrArg Additive.ofMul hEq⟩

/-- The canonical comparison identifies the filtered colimit with continuous second cohomology. -/
def limitEquiv : FiniteH2Limit k S ≃+ Additive (H2Continuous k S) :=
  (comparison (k := k) (S := S)).val

@[simp] theorem limitEquiv_of (E : Stage k S) (a : H2 k E) :
    limitEquiv (k := k) (S := S) (limitOf E (Additive.ofMul a)) = Additive.ofMul (toContinuous E a) :=
  (comparison (k := k) (S := S)).property E (Additive.ofMul a)

theorem finite_limit_comparison : FiniteLimitComparison.{u,v} :=
  ⟨limitEquiv, limitEquiv_of⟩

end
end RM03.Brauer.ContinuousCohomology
