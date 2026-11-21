import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Duality
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Cocircuits

/-! W68: loops, coloops, and cocircuits on the original finite ground.
The definitions agree literally with the source; the library predicates
are connected below rather than used as alternative definitions. -/

namespace FiniteCombinatorics.Matroid
open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

def Loop (M : _root_.Matroid α) (e : α) : Prop := M.IsCircuit {e}

def Coloop (M : _root_.Matroid α) (e : α) : Prop :=
  ∀ B, M.IsBase B → e ∈ B

def Cocircuit (M : _root_.Matroid α) (C : Set α) : Prop := M✶.IsCircuit C

def MeetsEveryBasis (M : _root_.Matroid α) (C : Set α) : Prop :=
  ∀ B, M.IsBase B → (C ∩ B).Nonempty

def MinimalBasisHitting (M : _root_.Matroid α) (C : Set α) : Prop :=
  C ⊆ M.E ∧ MeetsEveryBasis M C ∧
    ∀ D, D ⊂ C → ¬ MeetsEveryBasis M D

def MaximalNonspanning (M : _root_.Matroid α) (H : Set α) : Prop :=
  H ⊆ M.E ∧ ¬ M.Spanning H ∧
    ∀ A, H ⊂ A → A ⊆ M.E → M.Spanning A

theorem loopIffIsLoop (M : _root_.Matroid α) [M.Finite] (e : α) :
    Loop M e ↔ M.IsLoop e := _root_.Matroid.singleton_isCircuit

theorem coloopIffIsColoop (M : _root_.Matroid α) [M.Finite] (e : α) :
    Coloop M e ↔ M.IsColoop e := by
  exact ⟨fun h => _root_.Matroid.isColoop_iff_forall_mem_isBase.mpr (fun {_} => h _),
    fun h B hB => _root_.Matroid.isColoop_iff_forall_mem_isBase.mp h hB⟩

theorem cocircuitMinimalHitting (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    Cocircuit M C ↔ MinimalBasisHitting M C := by
  constructor
  · intro hC
    have hm := _root_.Matroid.isCocircuit_iff_minimal.mp hC
    refine ⟨hC.subset_ground, hm.1, ?_⟩
    intro D hDC hD
    exact hDC.not_ge (hm.2 hD hDC.subset)
  · rintro ⟨_, hC, hmin⟩
    apply _root_.Matroid.isCocircuit_iff_minimal.mpr
    refine ⟨hC, ?_⟩
    intro D hD hDC
    by_contra hn
    exact hmin D ⟨hDC, hn⟩ hD

theorem spanningContainsBasis (M : _root_.Matroid α) [M.Finite] (A : Set α)
    (hA : A ⊆ M.E) : M.Spanning A ↔ ∃ B, M.IsBase B ∧ B ⊆ A :=
  _root_.Matroid.spanning_iff_exists_isBase_subset hA

theorem hittingComplementNonspanning (M : _root_.Matroid α) [M.Finite] (C : Set α)
    (_hC : C ⊆ M.E) :
    MeetsEveryBasis M C ↔ ¬ M.Spanning (relativeCompl M.E C) := by
  classical
  unfold relativeCompl
  rw [spanningContainsBasis M _ sdiff_subset]
  constructor
  · rintro h ⟨B, hB, hBC⟩
    obtain ⟨e, heC, heB⟩ := h B hB
    exact (hBC heB).2 heC
  · intro h B hB
    by_contra hmiss
    apply h
    refine ⟨B, hB, ?_⟩
    intro e heB
    exact ⟨hB.subset_ground heB, fun heC => hmiss ⟨e, heC, heB⟩⟩

theorem cocircuitComplementMaximal (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    Cocircuit M C ↔ C ⊆ M.E ∧ MaximalNonspanning M (relativeCompl M.E C) := by
  classical
  rw [cocircuitMinimalHitting]
  constructor
  · rintro ⟨hC, hh, hmin⟩
    refine ⟨hC, sdiff_subset, (hittingComplementNonspanning M C hC).mp hh, ?_⟩
    intro A hCA hA
    by_contra hnon
    have hhit := (hittingComplementNonspanning M (M.E \ A) sdiff_subset).mpr
      (by simpa only [relativeCompl, sdiff_sdiff_cancel_left hA] using hnon)
    have hsub : M.E \ A ⊆ C := by
      intro x hx
      by_contra hxC
      exact hx.2 (hCA.subset ⟨hx.1, hxC⟩)
    have hstrict : M.E \ A ⊂ C := by
      refine ⟨hsub, ?_⟩
      intro hrev
      apply hCA.not_ge
      intro x hx
      exact ⟨hA hx, fun hxC => (hrev hxC).2 hx⟩
    exact hmin _ hstrict hhit
  · rintro ⟨hC, _, hnon, hmax⟩
    refine ⟨hC, (hittingComplementNonspanning M C hC).mpr hnon, ?_⟩
    intro D hDC hhit
    have hD := hDC.subset.trans hC
    have hsub : M.E \ C ⊆ M.E \ D := by
      intro x hx
      exact ⟨hx.1, fun hxD => hx.2 (hDC.subset hxD)⟩
    have hstrict : M.E \ C ⊂ M.E \ D := by
      refine ⟨hsub, ?_⟩
      intro hrev
      apply hDC.not_ge
      intro x hxC
      by_contra hxD
      exact (hrev ⟨hC hxC, hxD⟩).2 hxC
    exact (hittingComplementNonspanning M D hD).mp hhit
      (hmax _ hstrict sdiff_subset)

theorem cocircuitComplementExists (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    Cocircuit M C ↔ ∃ H, MaximalNonspanning M H ∧ C = relativeCompl M.E H := by
  constructor
  · intro h
    obtain ⟨hC, hmax⟩ := (cocircuitComplementMaximal M C).mp h
    exact ⟨relativeCompl M.E C, hmax, (sdiff_sdiff_cancel_left hC).symm⟩
  · rintro ⟨H, hH, rfl⟩
    apply (cocircuitComplementMaximal M _).mpr
    exact ⟨sdiff_subset, by simpa only [relativeCompl, sdiff_sdiff_cancel_left hH.1] using hH⟩

theorem coloopDualLoop (M : _root_.Matroid α) [M.Finite] (e : α) :
    Coloop M e ↔ Loop M✶ e := by
  rw [coloopIffIsColoop, loopIffIsLoop]
  exact _root_.Matroid.dual_isLoop_iff_isColoop.symm

theorem emptyBaseNoHitting (M : _root_.Matroid α) [M.Finite]
    (h : M.IsBase ∅) (C : Set α) : ¬ MeetsEveryBasis M C := by
  intro hh
  simpa using hh ∅ h

theorem emptyBaseNoCocircuit (M : _root_.Matroid α) [M.Finite]
    (h : M.IsBase ∅) (C : Set α) : ¬ Cocircuit M C := by
  intro hc
  exact emptyBaseNoHitting M h C ((cocircuitMinimalHitting M C).mp hc).2.1

theorem emptyGroundNoCocircuit (M : _root_.Matroid α) [M.Finite]
    (h : M.E = ∅) (C : Set α) : ¬ Cocircuit M C := by
  intro hc
  have hsub : C ⊆ (∅ : Set α) := by
    simpa only [_root_.Matroid.dual_ground, h] using hc.subset_ground
  exact hc.nonempty.ne_empty (subset_empty_iff.mp hsub)

end FiniteCombinatorics.Matroid
