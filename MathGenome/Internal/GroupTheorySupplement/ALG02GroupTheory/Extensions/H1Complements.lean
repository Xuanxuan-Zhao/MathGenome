import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.SectionFactorSystem
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.H1Complements
import Mathlib.Tactic.Abel

/-! Complements and first cohomology for a split extension (paper.tex:438–457). -/

namespace ALG02GroupTheory.Extensions

open Multiplicative (ofAdd toAdd)
open groupCohomology (cocycles₁ H1 H1π)
open Specs.ALG02GroupTheory.Extensions
  (actualComplements complementConjugacySetoid complementGraph cocycleCoordinate
    kernelAction kernelConjugate kernelCohomologyRep)

variable {A E Q : Type*} [AddCommGroup A] [Group E] [Group Q]
variable (S : AbelianKernelExtension A E Q) (s₀ : S.Splitting)

/-- The actual complements modulo conjugacy by the embedded kernel. -/
abbrev ComplementConjugacyClasses :=
  Specs.ALG02GroupTheory.Extensions.ComplementConjugacyClassesValue S

@[simp] private theorem rightHom_graph (z : Q → A) (q : Q) :
    S.rightHom (complementGraph S s₀ z q) = q := by
  simp [complementGraph]

private theorem inl_kernelAction (q : Q) (a : A) :
    S.inl (ofAdd (kernelAction S q a)) = s₀ q * S.inl (ofAdd a) * (s₀ q)⁻¹ := by
  change S.inl (abelianAction S q (ofAdd a)) = _
  have h : abelianAction S q = S.conjAct (s₀ q) := by
    simpa only [s₀.rightHom_splitting] using abelianActionFormula S (s₀ q)
  rw [h, S.inl_conjAct_comm]

private theorem graph_mul (z : Q → A) (q r : Q) :
    complementGraph S s₀ z q * complementGraph S s₀ z r =
      S.inl (ofAdd (z q + kernelAction S q (z r))) * s₀ (q * r) := by
  unfold complementGraph
  change _ = S.inl (ofAdd (z q) * ofAdd (kernelAction S q (z r))) * _
  rw [map_mul, inl_kernelAction S s₀, map_mul s₀]
  group

private theorem graphCoordinate_cancel (q : Q) {a b : A}
    (h : S.inl (ofAdd a) * s₀ q = S.inl (ofAdd b) * s₀ q) : a = b :=
  S.inl_injective (mul_right_cancel h)

private def graphSplitting (z : Q → A)
    (hz : ∀ q r, z (q * r) = z q + kernelAction S q (z r)) : S.Splitting where
  toFun := complementGraph S s₀ z
  map_one' := by
    have hact (a : A) : kernelAction S 1 a = a := by
      rw [kernelAction, map_one]
      rfl
    have he : z 1 + 0 = z 1 + z 1 := by
      simpa only [one_mul, hact, add_zero] using hz 1 1
    have h₁ := (add_left_cancel he).symm
    simp [complementGraph, h₁, show ofAdd (0 : A) = 1 from rfl]
  map_mul' q r := by
    rw [graph_mul]
    exact congrArg (fun a => S.inl (ofAdd a) * s₀ (q * r)) (hz q r)
  rightInverse_rightHom := rightHom_graph S s₀ z

theorem graphSplittingIff : Specs.ALG02GroupTheory.Extensions.GraphSplittingIff := by
  intro A E Q _ _ _ S s₀ z
  constructor
  · rintro ⟨s, hs⟩ q r
    apply graphCoordinate_cancel S s₀ (q * r)
    change complementGraph S s₀ z (q * r) = _
    rw [← hs, map_mul s, hs q, hs r, graph_mul]
  · intro hz
    exact ⟨graphSplitting S s₀ z hz, fun _ => rfl⟩

private theorem graphRange_eq_iff (z z' : Q → A) :
    Set.range (complementGraph S s₀ z') = Set.range (complementGraph S s₀ z) ↔
      ∀ q, z' q = z q := by
  constructor
  · intro h q
    obtain ⟨r, hr⟩ : complementGraph S s₀ z' q ∈ Set.range (complementGraph S s₀ z) := by
      rw [← h]
      exact Set.mem_range_self q
    have hrq := congrArg S.rightHom hr
    simp only [rightHom_graph] at hrq
    subst r
    exact graphCoordinate_cancel S s₀ q hr.symm
  · intro h
    rw [funext h]

private theorem conj_graph_apply (a : A) (z : Q → A) (q : Q) :
    MulAut.conj (S.inl (ofAdd a)) (complementGraph S s₀ z q) =
      complementGraph S s₀ (fun r => z r + a - kernelAction S r a) q := by
  rw [MulAut.conj_apply]
  unfold complementGraph
  dsimp only
  rw [sub_eq_add_neg, add_comm (z q) a]
  change _ = S.inl (ofAdd a * ofAdd (z q) * (ofAdd (kernelAction S q a))⁻¹) * _
  rw [map_mul, map_mul, map_inv, inl_kernelAction S s₀]
  group

theorem graphConjugacyIff : Specs.ALG02GroupTheory.Extensions.GraphConjugacyIff := by
  intro A E Q _ _ _ S s₀ a H K z z' hH hK
  have hmap : (kernelConjugate S a H.val : Set E) =
      Set.range (complementGraph S s₀ (fun q => z q + a - kernelAction S q a)) := by
    rw [kernelConjugate, Subgroup.coe_map, hH, ← Set.range_comp]
    congr 1
    funext q
    exact conj_graph_apply S s₀ a z q
  rw [← SetLike.coe_set_eq, hK, hmap, graphRange_eq_iff]

private theorem coordinate_mul (z : cocycles₁ (kernelCohomologyRep S)) (q r : Q) :
    cocycleCoordinate S z (q * r) =
      cocycleCoordinate S z q + kernelAction S q (cocycleCoordinate S z r) := by
  have h := congrArg ULift.down
    ((groupCohomology.mem_cocycles₁_iff _).1 z.property (ULift.up q) (ULift.up r))
  exact h.trans (add_comm _ _)

private def cocycleOfCoordinate (z : Q → A)
    (hz : ∀ q r, z (q * r) = z q + kernelAction S q (z r)) :
    cocycles₁ (kernelCohomologyRep S) :=
  ⟨fun q => ULift.up (z q.down), (groupCohomology.mem_cocycles₁_iff _).2 fun q r =>
    ULift.ext ((hz q.down r.down).trans (add_comm _ _))⟩

private theorem cocycleCoordinate_injective : Function.Injective (cocycleCoordinate S) := by
  intro z z' h
  apply groupCohomology.cocycles₁_ext
  intro q
  exact ULift.ext (congrFun h q.down)

private noncomputable def splittingCoordinate (s : S.Splitting) (q : Q) : A :=
  toAdd (sectionChange S ⟨s₀.toSection, map_one s₀⟩ ⟨s.toSection, map_one s⟩ q)

private theorem splitting_eq_graph (s : S.Splitting) (q : Q) :
    s q = complementGraph S s₀ (splittingCoordinate S s₀ s) q :=
  (sectionChangeUnique S ⟨s₀.toSection, map_one s₀⟩ ⟨s.toSection, map_one s⟩).2.1 q

private noncomputable def complementCocycle (H : actualComplements S) :
    cocycles₁ (kernelCohomologyRep S) :=
  let s := splittingOfComplement S H
  cocycleOfCoordinate S (splittingCoordinate S s₀ s)
    (graphSplittingIff S s₀ _ |>.mp ⟨s, splitting_eq_graph S s₀ s⟩)

private theorem complement_eq_graph (H : actualComplements S) :
    (H.val : Set E) = Set.range (complementGraph S s₀ (cocycleCoordinate S
      (complementCocycle S s₀ H))) := by
  have hs : (splittingComplementEquiv S).symm H = splittingOfComplement S H := rfl
  have h := congrArg Subtype.val ((splittingComplementEquiv S).apply_symm_apply H)
  rw [hs] at h
  change (splittingOfComplement S H).toMonoidHom.range = H.val at h
  rw [← h]
  change Set.range (⇑(splittingOfComplement S H)) =
    Set.range (complementGraph S s₀ (splittingCoordinate S s₀ (splittingOfComplement S H)))
  rw [funext (splitting_eq_graph S s₀ (splittingOfComplement S H))]

private theorem class_eq_iff (z z' : cocycles₁ (kernelCohomologyRep S)) :
    H1π (kernelCohomologyRep S) z = H1π (kernelCohomologyRep S) z' ↔
      ∃ a : A, ∀ q, cocycleCoordinate S z' q =
        cocycleCoordinate S z q + a - kernelAction S q a := by
  rw [groupCohomology.H1π_eq_iff, groupCohomology.coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.down, fun q => ?_⟩
    have h := congrArg ULift.down (congrFun ha (ULift.up q))
    change kernelAction S q a.down - a.down =
      cocycleCoordinate S z q - cocycleCoordinate S z' q at h
    calc
      cocycleCoordinate S z' q =
          cocycleCoordinate S z q - (cocycleCoordinate S z q - cocycleCoordinate S z' q) := by abel
      _ = cocycleCoordinate S z q + a.down - kernelAction S q a.down := by rw [← h]; abel
  · rintro ⟨a, ha⟩
    refine ⟨ULift.up a, funext fun q => ULift.ext ?_⟩
    change kernelAction S q.down a - a =
      cocycleCoordinate S z q.down - cocycleCoordinate S z' q.down
    rw [ha]
    abel

private theorem complement_class_eq_iff (H K : actualComplements S) :
    H1π (kernelCohomologyRep S) (complementCocycle S s₀ H) =
      H1π (kernelCohomologyRep S) (complementCocycle S s₀ K) ↔
      (complementConjugacySetoid S).r H K := by
  rw [class_eq_iff]
  change (∃ a : A, ∀ q, cocycleCoordinate S (complementCocycle S s₀ K) q =
    cocycleCoordinate S (complementCocycle S s₀ H) q + a - kernelAction S q a) ↔
    ∃ a : A, K.val = kernelConjugate S a H.val
  exact exists_congr fun a =>
    (graphConjugacyIff S s₀ a H K _ _ (complement_eq_graph S s₀ H)
      (complement_eq_graph S s₀ K)).symm

private noncomputable def classToH1 : ComplementConjugacyClasses S → H1 (kernelCohomologyRep S) :=
  Quotient.lift (fun H => H1π (kernelCohomologyRep S) (complementCocycle S s₀ H))
    (fun H K => (complement_class_eq_iff S s₀ H K).2)

private theorem classToH1_graph (H : actualComplements S) (z : cocycles₁ (kernelCohomologyRep S))
    (h : (H.val : Set E) = Set.range (complementGraph S s₀ (cocycleCoordinate S z))) :
    classToH1 S s₀ (Quotient.mk (complementConjugacySetoid S) H) =
      H1π (kernelCohomologyRep S) z := by
  change H1π (kernelCohomologyRep S) (complementCocycle S s₀ H) = _
  congr 1
  apply cocycleCoordinate_injective S
  exact funext ((graphRange_eq_iff S s₀ _ _).mp ((complement_eq_graph S s₀ H).symm.trans h))

private noncomputable def complementOfCocycle (z : cocycles₁ (kernelCohomologyRep S)) :
    actualComplements S :=
  splittingComplementEquiv S
    (graphSplitting S s₀ (cocycleCoordinate S z) (coordinate_mul S z))

private theorem classToH1_bijective : Function.Bijective (classToH1 S s₀) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | _ H =>
      induction y using Quotient.inductionOn with
      | _ K =>
        intro h
        exact Quotient.sound ((complement_class_eq_iff S s₀ H K).1 h)
  · intro x
    refine groupCohomology.H1_induction_on x fun z => ?_
    let H := complementOfCocycle S s₀ z
    exact ⟨Quotient.mk (complementConjugacySetoid S) H, classToH1_graph S s₀ H z rfl⟩

theorem complementsCorrespondToH1 : Specs.ALG02GroupTheory.Extensions.ComplementsCorrespondToH1 := by
  intro A E Q _ _ _ S s₀
  refine ⟨Equiv.ofBijective (classToH1 S s₀) (classToH1_bijective S s₀),
    fun H => ⟨complementCocycle S s₀ H, complement_eq_graph S s₀ H⟩,
    fun z => ⟨complementOfCocycle S s₀ z, rfl⟩,
    classToH1_graph S s₀, ?_⟩
  let H : actualComplements S := splittingComplementEquiv S s₀
  refine ⟨H, rfl, ?_⟩
  change classToH1 S s₀ (Quotient.mk (complementConjugacySetoid S) H) = 0
  rw [classToH1_graph S s₀ H 0, map_zero]
  change Set.range (⇑s₀) = Set.range (complementGraph S s₀ (cocycleCoordinate S 0))
  congr 1
  funext q
  simp [complementGraph, show cocycleCoordinate S 0 q = 0 from rfl,
    show ofAdd (0 : A) = 1 from rfl]

end ALG02GroupTheory.Extensions
