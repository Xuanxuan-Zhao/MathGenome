import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroCocycle
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.BorelInduction
import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The induced highest-weight model in KM13, over the canonical Virasoro algebra. -/

noncomputable section

namespace LieNotes.Virasoro.VermaSpec

open RepTheorySurvey.CategoryO.BorelInduction (U Induced inclusion induceTensor)
open UniversalEnvelopingAlgebra (ι)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

abbrev V := VirasoroSpec.Vir
local notation "L" => VirasoroSpec.mode
local notation "C" => VirasoroSpec.central

/-- The nonnegative modes and the central generator. -/
def borelLetter : ℕ ⊕ Unit → V
  | .inl n => L n
  | .inr _ => C

/-- The negative mode of absolute index (n+1). -/
def negativeLetter (n : ℕ) : V := L (Int.negSucc n)

abbrev Word := Shared.Lie.PBW.OrderedWord ℕ

/-- The weight increment of an ordered word, including zero for the empty word. -/
def wordDegree (w : Word) : ℕ := (w.val.map Nat.succ).sum

section Lie

variable [r : LieRing V] [a : LieAlgebra ℂ V]

/-- A target vector with central charge (c) and highest weight (h). -/
def IsHighestWeight {X : Type*} [AddCommGroup X] [Module ℂ X]
    [LieRingModule V X] [LieModule ℂ V X] (c h : ℂ) (x : X) : Prop :=
  ⁅C, x⁆ = c • x ∧ ⁅L 0, x⁆ = h • x ∧ ∀ j : ℤ, 0 < j → ⁅L j, x⁆ = 0

/-- The inducing subalgebra and its one-dimensional characters. -/
structure InducingData where
  borel : LieSubalgebra ℂ V
  span_eq : borel.toSubmodule =
    @Submodule.span ℂ V _ r.toAddCommGroup.toAddCommMonoid a.toModule (Set.range borelLetter)
  character : ℂ → ℂ → U borel →ₐ[ℂ] ℂ
  character_central (c h : ℂ) (hm : C ∈ borel) :
    character c h (ι ℂ (⟨C, hm⟩ : borel)) = c
  character_zero (c h : ℂ) (hm : L 0 ∈ borel) :
    character c h (ι ℂ (⟨L 0, hm⟩ : borel)) = h
  character_positive (c h : ℂ) (j : ℤ) (hj : 0 < j) (hm : L j ∈ borel) :
    character c h (ι ℂ (⟨L j, hm⟩ : borel)) = 0

namespace InducingData

variable (D : InducingData) (c h : ℂ)

/-- The action of the Borel enveloping algebra on the complex line. -/
abbrev characterModule : Module (U D.borel) ℂ :=
  Module.compHom ℂ (D.character c h).toRingHom

/-- The balanced tensor `U(Vir) ⊗_{U(borel)} ℂ_{c,h}`. -/
abbrev Verma : Type :=
  letI := D.characterModule c h
  Induced (inclusion D.borel) ℂ

instance : Module (U V) (D.Verma c h) := by
  letI := D.characterModule c h
  unfold Verma
  infer_instance

instance : LieRingModule V (D.Verma c h) :=
  letI : LieRingModule (U V) (D.Verma c h) := LieRingModule.ofAssociativeModule
  LieRingModule.compLieHom (D.Verma c h) (ι ℂ)

instance : LieModule ℂ V (D.Verma c h) :=
  letI : LieRingModule (U V) (D.Verma c h) := LieRingModule.ofAssociativeModule
  letI : LieModule ℂ (U V) (D.Verma c h) := LieModule.ofAssociativeModule
  LieModule.compLieHom (D.Verma c h) (ι ℂ)

/-- The vector `1 ⊗ 1`. -/
def top : D.Verma c h :=
  letI := D.characterModule c h
  induceTensor (inclusion D.borel) 1 1

/-- A product of negative modes acting on the top, with the leftmost mode acting last. -/
def applyWord : List ℕ → D.Verma c h
  | [] => D.top c h
  | i :: w => ⁅negativeLetter i, applyWord w⁆

/-- The (h+d) eigenspace of (L_0). Integer labels include the vanishing
spaces below the top. -/
def degree (d : ℤ) : Submodule ℂ (D.Verma c h) :=
  (LieModule.toEnd ℂ V (D.Verma c h) (L 0)).eigenspace (h + (d : ℂ))

end InducingData

open InducingData

/-- The highest-weight construction, on a single module for each (c,h). -/
structure ModelProperties (D : InducingData) : Prop where
  top_ne_zero : ∀ c h, D.top c h ≠ 0
  highestWeight : ∀ c h, IsHighestWeight c h (D.top c h)
  cyclic : ∀ c h, LieSubmodule.lieSpan ℂ V {D.top c h} = ⊤
  universal : ∀ c h {X : Type u} [AddCommGroup X] [Module ℂ X]
    [LieRingModule V X] [LieModule ℂ V X] (x : X), IsHighestWeight c h x →
    ∃! f : D.Verma c h →ₗ⁅ℂ,V⁆ X, f (D.top c h) = x
  central_action : ∀ c h (x : D.Verma c h), ⁅C, x⁆ = c • x
  orderedBasis : ∀ c h, ∃ b : Module.Basis Word ℂ (D.Verma c h),
    ∀ w, b w = D.applyWord c h w.val
  word_weight : ∀ c h (w : Word), D.applyWord c h w.val ∈ D.degree c h (wordDegree w)
  degree_span : ∀ c h d, D.degree c h d =
    Submodule.span ℂ {x | ∃ w : Word, (wordDegree w : ℤ) = d ∧ x = D.applyWord c h w.val}
  degree_zero : ∀ c h, D.degree c h 0 = Submodule.span ℂ {D.top c h}
  shift : ∀ c h (j d : ℤ) (x : D.Verma c h), x ∈ D.degree c h d →
    ⁅L j, x⁆ ∈ D.degree c h (d - j)
  kills_below : ∀ c h (j d : ℤ) (x : D.Verma c h), x ∈ D.degree c h d →
    d - j < 0 → ⁅L j, x⁆ = 0

end Lie

/-- Construct the model over the canonical complex vector space and bracket of Virasoro. -/
def ModelExists : Prop :=
  ∃ r : LieRing V, ∃ a : @LieAlgebra ℂ V _ r,
    r.toAddCommGroup = (inferInstance : AddCommGroup V) ∧
    HEq a.toModule (inferInstance : Module ℂ V) ∧
    letI : LieRing V := r
    letI : LieAlgebra ℂ V := a
    (∀ x y : V, ⁅x, y⁆ = VirasoroSpec.bracket x y) ∧
    ∃ D : InducingData, ModelProperties.{u} D

end LieNotes.Virasoro.VermaSpec
