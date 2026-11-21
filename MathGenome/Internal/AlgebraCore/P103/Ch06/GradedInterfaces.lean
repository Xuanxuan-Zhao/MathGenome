import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.GradedInterfaces
import Lean.Elab.Tactic.Omega

namespace P103.Graded
open DirectSum
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Standard graded over the actual degree-zero subring. -/
def IsStandard : Specs.P103.Graded.standardType (A := A) :=
  Specs.P103.Graded.standardValue

/-- The conventional shift by minus one. -/
def shiftPiece (G : NonnegativeGrading A) :
    Specs.P103.Graded.shiftPieceType (M := M) G :=
  Specs.P103.Graded.shiftPieceValue G

/-- Replace finite generators by all of their homogeneous components. -/
theorem exists_homogeneous_generators (G : NonnegativeGrading A)
    (U : ModuleGrading G M) [Module.Finite A M] :
    Specs.P103.Graded.homogeneousGeneratorsType G U := by
  classical
  obtain ⟨F, hF⟩ := (Module.Finite.fg_top (R := A) (M := M))
  let I := Σ (x : F), (decompose U.piece x.1).support
  let x (i : I) : M := (decompose U.piece i.1.1 i.2.1 : M)
  refine ⟨Finset.univ.image x, ?_, ?_⟩
  · rw [← top_le_iff, ← hF]
    apply Submodule.span_le.mpr
    intro m hm
    rw [← sum_support_decompose U.piece m]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨⟨⟨m, hm⟩, j, hj⟩, Finset.mem_univ _, rfl⟩
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨i.2.1, (decompose U.piece i.1.1 i.2.1).2⟩


variable {G : NonnegativeGrading A}

/-- Elements whose components below b vanish. -/
def supportedAbove (U : ModuleGrading G M) (b : ℤ) : AddSubgroup M where
  carrier := {m | ∀ j, j < b → (decompose U.piece m j : M) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj
    rw [decompose_add]
    change (decompose U.piece x j : M) + (decompose U.piece y j : M) = 0
    rw [hx j hj, hy j hj, add_zero]
  neg_mem' := by
    intro x hx j hj
    rw [decompose_neg]
    change -(decompose U.piece x j : M) = 0
    rw [hx j hj, neg_zero]

lemma homogeneous_supportedAbove (U : ModuleGrading G M) {b d : ℤ}
    {m : M} (hm : m ∈ U.piece d) (hd : b ≤ d) : m ∈ supportedAbove U b := by
  intro j hj
  exact decompose_of_mem_ne U.piece hm (by omega)

/-- Nonnegative scalar degrees preserve a lower bound on module degrees. -/
lemma supportedAbove_smul (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (b : ℤ) (a : A) {m : M} (hm : m ∈ supportedAbove U b) :
    a • m ∈ supportedAbove U b := by
  classical
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | add a a' ha ha' =>
    simpa only [add_smul] using (supportedAbove U b).add_mem ha ha'
  | @homogeneous i a =>
    by_cases hi : i < 0
    · have hz : (a : A) = 0 := by
        have h := a.2
        simp only [G.negative i hi, AddSubgroup.mem_bot] at h
        exact h
      simp [hz]
    · rw [← sum_support_decompose U.piece m, Finset.smul_sum]
      apply (supportedAbove U b).sum_mem
      intro j hj
      by_cases hjb : j < b
      · have hz := hm j hjb
        rw [hz, smul_zero]
        exact (supportedAbove U b).zero_mem
      · apply homogeneous_supportedAbove U
        · exact SetLike.GradedSMul.smul_mem a.2 (decompose U.piece m j).2
        · change b ≤ i + j
          omega

/-- The elements supported in degrees at least b form an A-submodule. -/
def aboveSubmodule (G : NonnegativeGrading A) (U : ModuleGrading G M) (b : ℤ) :
    Submodule A M where
  __ := supportedAbove U b
  smul_mem' := fun a _ hm => supportedAbove_smul G U b a hm

lemma finite_homogeneous_degrees_bounded (U : ModuleGrading G M) (s : Finset M)
    (hs : ∀ m ∈ s, ∃ j : ℤ, m ∈ U.piece j) :
    ∃ b : ℤ, ∀ m ∈ s, m ∈ supportedAbove U b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨d, hd⟩ := hs x (Finset.mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun m hm => hs m (Finset.mem_insert_of_mem hm))
    refine ⟨min d b, ?_⟩
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact homogeneous_supportedAbove U hd (min_le_left _ _)
    · intro j hj
      exact hb m hm j (lt_of_lt_of_le hj (min_le_right _ _))

/-- Ordinary finite generation implies vanishing in sufficiently negative degrees. -/
theorem bounded_below (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [Module.Finite A M] : Specs.P103.Graded.boundedBelowType G U := by
  obtain ⟨s, hspan, hs⟩ := exists_homogeneous_generators G U
  obtain ⟨b, hb⟩ := finite_homogeneous_degrees_bounded U s hs
  have htop : aboveSubmodule G U b = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hb
  refine ⟨b, ?_⟩
  intro j hj
  apply le_antisymm _ bot_le
  intro m hm
  have hm' : m ∈ aboveSubmodule G U b := by rw [htop]; trivial
  have hz := hm' j hj
  rwa [decompose_of_mem_same U.piece hm] at hz


/-- Shifting relabels the decomposition; the A-module itself does not change. -/
noncomputable def shift (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    ModuleGrading G M where
  piece := shiftPiece G U
  decomposition := by
    classical
    let e : ℤ ≃ ℤ :=
      { toFun := fun j => j + 1
        invFun := fun j => j - 1
        left_inv := by intro j; dsimp; omega
        right_inv := by intro j; dsimp; omega }
    let f := (DirectSum.equivCongrLeft (β := fun j => U.piece j) e).toAddMonoidHom.comp
      (decomposeAddEquiv U.piece).toAddMonoidHom
    have hf : Function.Injective f :=
      (DirectSum.equivCongrLeft (β := fun j => U.piece j) e).injective.comp
        (decomposeAddEquiv U.piece).injective
    have hr : f.comp (DirectSum.coeAddMonoidHom (shiftPiece G U)) = .id _ := by
      apply DirectSum.addHom_ext
      intro j m
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      change DirectSum.equivCongrLeft e (decompose U.piece (m : M)) =
        DirectSum.of (fun j => U.piece (j - 1)) j m
      rw [decompose_of_mem U.piece m.2]
      exact DirectSum.equivCongrLeft_of (β := fun j => U.piece j) e j m
    refine DirectSum.Decomposition.ofAddHom (ℳ := shiftPiece G U) f ?_ hr
    apply AddMonoidHom.ext
    intro m
    apply hf
    exact DFunLike.congr_fun hr (f m)
  compatible := by
    constructor
    intro i j a m ha hm
    change a • m ∈ U.piece (i + j - 1)
    have h : a • m ∈ U.piece (i + (j - 1)) :=
      SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece)
        (i := i) (j := j - 1) ha hm
    simpa only [add_sub_assoc] using h

theorem shift_exists (G : NonnegativeGrading A) (U : ModuleGrading G M) :
    Specs.P103.Graded.shiftType G U := ⟨shift G U, fun _ => rfl⟩

end P103.Graded
