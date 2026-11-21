import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.Germ
import Mathlib.Topology.UnitInterval

/-!
Independent interface for paper.tex, d12:19-01 (lines 3135--3144).
A total complex function represents its restriction to the stated open set.
The ambient `Filter.Germ` is the actual quotient by neighborhood equality;
`HolomorphicGerm` retains exactly the classes with a holomorphic local
representative. Connected representatives are established in the implementation.
Parameter neighborhoods use the subspace topology on the closed unit interval,
so the same definition applies at both endpoints. No path regularity beyond
continuity and no existence of a continuation is assumed.
-/

open scoped Topology

noncomputable section

namespace D12Complex

/-- A holomorphic function on a nonempty connected open plane set. -/
structure FunctionElement where
  domain : Set ℂ
  isDomain : IsDomain domain
  toFun : ℂ → ℂ
  holomorphic : HolomorphicOn domain toFun

/-- Agreement on an open neighborhood contained in both representing domains. -/
def SameGermAt (a : ℂ) (e d : FunctionElement) : Prop :=
  ∃ W : Set ℂ, IsOpen W ∧ a ∈ W ∧ W ⊆ e.domain ∩ d.domain ∧
    Set.EqOn e.toFun d.toFun W

/-- The intrinsic local holomorphy predicate on neighborhood-equivalence classes. -/
def IsHolomorphicGerm (a : ℂ) (g : Filter.Germ (𝓝 a) ℂ) : Prop :=
  ∃ (U : Set ℂ) (f : ℂ → ℂ), a ∈ U ∧ HolomorphicOn U f ∧
    (f : Filter.Germ (𝓝 a) ℂ) = g

/-- Holomorphic germs at a fixed basepoint, as a subtype of an actual quotient. -/
def HolomorphicGerm (a : ℂ) :=
  {g : Filter.Germ (𝓝 a) ℂ // IsHolomorphicGerm a g}

/-- The germ of a holomorphic function at a point of its open domain. -/
def HolomorphicGerm.ofFunction {a : ℂ} {U : Set ℂ} (f : ℂ → ℂ)
    (hf : HolomorphicOn U f) (ha : a ∈ U) : HolomorphicGerm a :=
  ⟨(f : Filter.Germ (𝓝 a) ℂ), U, f, ha, hf, rfl⟩

/-- The common value of all representatives of a germ at its basepoint. -/
def HolomorphicGerm.value {a : ℂ} (g : HolomorphicGerm a) : ℂ :=
  g.val.value

/-- A function element determines a germ at every point of its domain. -/
def FunctionElement.germAt (e : FunctionElement) (a : ℂ) (ha : a ∈ e.domain) :
    HolomorphicGerm a :=
  HolomorphicGerm.ofFunction e.toFun e.holomorphic ha

/-- A family whose germ at time t has basepoint γ(t). -/
def GermFamily (γ : unitInterval → ℂ) :=
  ∀ t : unitInterval, HolomorphicGerm (γ t)

/-- One holomorphic function represents every member of the family on I. -/
def RepresentsOn (γ : unitInterval → ℂ) (Φ : GermFamily γ)
    (U : Set ℂ) (f : ℂ → ℂ) (I : Set unitInterval) : Prop :=
  HolomorphicOn U f ∧ ∀ t ∈ I, γ t ∈ U ∧
    (Φ t).val = (f : Filter.Germ (𝓝 (γ t)) ℂ)

/-- Local representation at every parameter, including 0 and 1. -/
def LocallyRepresented (γ : unitInterval → ℂ) (Φ : GermFamily γ) : Prop :=
  ∀ s : unitInterval, ∃ (U : Set ℂ) (f : ℂ → ℂ) (I : Set unitInterval),
    IsOpen I ∧ s ∈ I ∧ RepresentsOn γ Φ U f I

/-- Continuation of an initial germ along a continuous path in a plane domain. -/
def IsContinuation (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ : HolomorphicGerm (γ 0)) (Φ : GermFamily γ) : Prop :=
  IsDomain Ω ∧ Continuous γ ∧ (∀ t, γ t ∈ Ω) ∧
    Φ 0 = φ ∧ LocallyRepresented γ Φ

/-- A continuation consists of the family together with the defining properties. -/
def Continuation (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0)) :=
  {Φ : GermFamily γ // IsContinuation Ω γ φ Φ}

end D12Complex

namespace Specs.D12Complex.Ch19.GermsContinuation

open _root_.D12Complex

def FunctionElement_type := Type

def FunctionElement_value : FunctionElement_type :=
  _root_.D12Complex.FunctionElement

def SameGermAt_type := ℂ → FunctionElement → FunctionElement → Prop

def SameGermAt_value : SameGermAt_type :=
  _root_.D12Complex.SameGermAt

def IsHolomorphicGerm_type := (a : ℂ) → Filter.Germ (𝓝 a) ℂ → Prop

def IsHolomorphicGerm_value : IsHolomorphicGerm_type :=
  _root_.D12Complex.IsHolomorphicGerm

def HolomorphicGerm_type := ℂ → Type

def HolomorphicGerm_value : HolomorphicGerm_type :=
  _root_.D12Complex.HolomorphicGerm

def germOfFunction_type := ∀ {a : ℂ} {U : Set ℂ} (f : ℂ → ℂ), HolomorphicOn U f → a ∈ U → HolomorphicGerm a

def germOfFunction_value : germOfFunction_type :=
  @_root_.D12Complex.HolomorphicGerm.ofFunction

def germValue_type := ∀ {a : ℂ}, HolomorphicGerm a → ℂ

def germValue_value : germValue_type :=
  @_root_.D12Complex.HolomorphicGerm.value

def elementGerm_type := (e : FunctionElement) → (a : ℂ) → a ∈ e.domain → HolomorphicGerm a

def elementGerm_value : elementGerm_type :=
  _root_.D12Complex.FunctionElement.germAt

def GermFamily_type := (unitInterval → ℂ) → Type

def GermFamily_value : GermFamily_type :=
  _root_.D12Complex.GermFamily

def RepresentsOn_type := (γ : unitInterval → ℂ) → GermFamily γ → Set ℂ → (ℂ → ℂ) → Set unitInterval → Prop

def RepresentsOn_value : RepresentsOn_type :=
  _root_.D12Complex.RepresentsOn

def LocallyRepresented_type := (γ : unitInterval → ℂ) → GermFamily γ → Prop

def LocallyRepresented_value : LocallyRepresented_type :=
  _root_.D12Complex.LocallyRepresented

def IsContinuation_type := (Ω : Set ℂ) → (γ : unitInterval → ℂ) → HolomorphicGerm (γ 0) → GermFamily γ → Prop

def IsContinuation_value : IsContinuation_type :=
  _root_.D12Complex.IsContinuation

def Continuation_type := (Ω : Set ℂ) → (γ : unitInterval → ℂ) → HolomorphicGerm (γ 0) → Type

def Continuation_value : Continuation_type :=
  _root_.D12Complex.Continuation

def sameGermAt_iff_eventuallyEq_type : Prop :=
  ∀ (a : ℂ) (e d : FunctionElement) (_he : a ∈ e.domain) (_hd : a ∈ d.domain),
  SameGermAt a e d ↔ e.toFun =ᶠ[𝓝 a] d.toFun

def sameGermAt_refl_type : Prop :=
  ∀ (a : ℂ) (e : FunctionElement), a ∈ e.domain → SameGermAt a e e

def sameGermAt_symm_type : Prop :=
  ∀ (a : ℂ) (e d : FunctionElement), SameGermAt a e d → SameGermAt a d e

def sameGermAt_trans_type : Prop :=
  ∀ (a : ℂ) (e d k : FunctionElement),
  SameGermAt a e d → SameGermAt a d k → SameGermAt a e k

def elementGerm_eq_iff_type : Prop :=
  ∀ (a : ℂ) (e d : FunctionElement) (he : a ∈ e.domain) (hd : a ∈ d.domain),
  e.germAt a he = d.germAt a hd ↔ SameGermAt a e d

def germOfFunction_eq_iff_type : Prop :=
  ∀ (a : ℂ) (U V : Set ℂ) (f g : ℂ → ℂ)
  (hf : HolomorphicOn U f) (hg : HolomorphicOn V g) (ha : a ∈ U) (hb : a ∈ V),
  HolomorphicGerm.ofFunction f hf ha = HolomorphicGerm.ofFunction g hg hb ↔
    ∃ W : Set ℂ, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∩ V ∧ Set.EqOn f g W

def germOfFunction_congr_type : Prop :=
  ∀ (a : ℂ) (U V : Set ℂ) (f g : ℂ → ℂ)
  (hf : HolomorphicOn U f) (hg : HolomorphicOn V g) (ha : a ∈ U) (hb : a ∈ V),
  f =ᶠ[𝓝 a] g → HolomorphicGerm.ofFunction f hf ha = HolomorphicGerm.ofFunction g hg hb

def germValue_ofFunction_type : Prop :=
  ∀ (a : ℂ) (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f) (ha : a ∈ U),
  (HolomorphicGerm.ofFunction f hf ha).value = f a

def exists_functionElement_type : Prop :=
  ∀ (a : ℂ) (g : HolomorphicGerm a),
  ∃ (e : FunctionElement) (ha : a ∈ e.domain), e.germAt a ha = g

def holomorphicGerm_ext_type : Prop :=
  ∀ (a : ℂ) (g h : HolomorphicGerm a), g.val = h.val → g = h

def representsOn_iff_type : Prop :=
  ∀ (γ : unitInterval → ℂ) (Φ : GermFamily γ) (U : Set ℂ) (f : ℂ → ℂ)
  (I : Set unitInterval), RepresentsOn γ Φ U f I ↔
    ∃ hf : HolomorphicOn U f, ∀ t ∈ I, ∃ ha : γ t ∈ U,
      Φ t = HolomorphicGerm.ofFunction f hf ha

def representsOn_congr_type : Prop :=
  ∀ (γ : unitInterval → ℂ) (Φ : GermFamily γ) (U V : Set ℂ)
  (f g : ℂ → ℂ) (I : Set unitInterval), RepresentsOn γ Φ U f I →
  HolomorphicOn V g → (∀ t ∈ I, γ t ∈ V) →
  (∀ t ∈ I, f =ᶠ[𝓝 (γ t)] g) → RepresentsOn γ Φ V g I

def locallyRepresented_iff_type : Prop :=
  ∀ (γ : unitInterval → ℂ) (Φ : GermFamily γ),
  LocallyRepresented γ Φ ↔ ∀ s : unitInterval,
    ∃ (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f),
      ∀ᶠ t in 𝓝 s, ∃ ha : γ t ∈ U, Φ t = HolomorphicGerm.ofFunction f hf ha

def isContinuation_iff_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
  (Φ : GermFamily γ), IsContinuation Ω γ φ Φ ↔
    IsDomain Ω ∧ Continuous γ ∧ (∀ t, γ t ∈ Ω) ∧ Φ 0 = φ ∧
      ∀ s : unitInterval, ∃ (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f)
        (I : Set unitInterval), IsOpen I ∧ s ∈ I ∧
          ∀ t ∈ I, ∃ ha : γ t ∈ U, Φ t = HolomorphicGerm.ofFunction f hf ha

def isContinuation_congr_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ ψ : HolomorphicGerm (γ 0))
  (Φ Ψ : GermFamily γ), φ = ψ → (∀ t, Φ t = Ψ t) →
    (IsContinuation Ω γ φ Φ ↔ IsContinuation Ω γ ψ Ψ)

end Specs.D12Complex.Ch19.GermsContinuation
