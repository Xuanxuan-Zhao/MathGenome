import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Fin.Basic

/-! Chief series and their conjugation factors (paper.tex, Definition 1.1). -/

namespace Specs.ALG02GroupTheory.Chief.Series

universe u v w

/-- For normal endpoints, this is the cover relation in the poset of
normal subgroups of the fixed ambient group. -/
def ambientCovByValue {G : Type u} [Group G] (K L : Subgroup G) : Prop :=
  K < L ∧ ∀ M : Subgroup G, M.Normal → K < M → ¬ M < L

def AmbientCovByType : Type (u + 1) :=
  {G : Type u} → [Group G] → Subgroup G → Subgroup G → Prop

/-- An unbundled chain from the trivial subgroup to the whole finite group. -/
def isChiefSeriesValue {G : Type u} [Group G] [Finite G] (r : ℕ)
    (N : Fin (r + 1) → Subgroup G) : Prop :=
  N 0 = ⊥ ∧ N (Fin.last r) = ⊤ ∧ (∀ i, (N i).Normal) ∧
    ∀ i : Fin r, ambientCovByValue (N i.castSucc) (N i.succ)

def IsChiefSeriesType : Type (u + 1) :=
  {G : Type u} → [Group G] → [Finite G] → (r : ℕ) → (Fin (r + 1) → Subgroup G) → Prop

/-- A chief series has one more term than it has steps. -/
structure Chain (G : Type u) [Group G] [Finite G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  first_eq_bot : term 0 = ⊥
  last_eq_top : term (Fin.last length) = ⊤
  normal : ∀ i, (term i).Normal
  step : ∀ i : Fin length, ambientCovByValue (term i.castSucc) (term i.succ)

def ChiefSeriesType : Type (u + 1) :=
  (G : Type u) → [Group G] → [Finite G] → Type u

abbrev chiefSeriesValue : ChiefSeriesType.{u} := Chain

/-- An action on a group preserving its identity and multiplication.
The inverse of the map for g is the map for g⁻¹. -/
abbrev gGroupValue (G : Type u) (A : Type v) [Group G] [Group A] : Type (max u v) :=
  MulDistribMulAction G A

set_option linter.checkUnivs false in
def GGroupType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (A : Type v) → [Group G] → [Group A] → Type (max u v)

/-- Multiplicative equivalences intertwining the two actions of the same G. -/
def gEquivValue (G : Type u) (A : Type v) (B : Type w)
    [Group G] [Group A] [Group B] [gGroupValue G A] [gGroupValue G B] :
    Type (max v w) :=
  {e : A ≃* B // ∀ (g : G) (x : A), e (g • x) = g • e x}

set_option linter.checkUnivs false in
def GEquivType : Type (max (u + 1) (v + 1) (w + 1)) :=
  (G : Type u) → (A : Type v) → (B : Type w) →
    [Group G] → [Group A] → [Group B] → [gGroupValue G A] → [gGroupValue G B] → Type (max v w)

/-- Stability under every element of G, including inverses. -/
def gInvariantValue {G : Type u} {A : Type v} [Group G] [Group A] [gGroupValue G A]
    (H : Subgroup A) : Prop :=
  ∀ (g : G) (x : A), x ∈ H → g • x ∈ H

set_option linter.checkUnivs false in
def GInvariantType : Type (max (u + 1) (v + 1)) :=
  {G : Type u} → {A : Type v} → [Group G] → [Group A] → [gGroupValue G A] →
    Subgroup A → Prop

section Factor

variable {G : Type u} [Group G]

/-- The quotient of L by the restriction of K to L. For K ≤ L this is L/K. -/
abbrev factorValue (K L : Subgroup G) : Type u := L ⧸ K.subgroupOf L

def FactorType : Type (u + 1) :=
  {G : Type u} → [Group G] → Subgroup G → Subgroup G → Type u

/-- The canonical quotient projection from L. -/
def factorMkValue (K L : Subgroup G) [K.Normal] : L →* factorValue K L :=
  QuotientGroup.mk' (K.subgroupOf L)

def FactorMkType : Type (u + 1) :=
  {G : Type u} → [Group G] → (K L : Subgroup G) → [K.Normal] → L →* factorValue K L

/-- Conjugation by an ambient element restricts to a homomorphism on L. -/
def conjugate (L : Subgroup G) [hL : L.Normal] (g : G) : L →* L :=
  ((MulAut.conj g).toMonoidHom.comp L.subtype).codRestrict L
    (fun x => hL.conj_mem x x.property g)

/-- The map of the quotient induced by ambient conjugation. Normality of K
gives the membership condition for the quotient map. -/
def conjugationMap (K L : Subgroup G) [hK : K.Normal] [L.Normal] (g : G) :
    factorValue K L →* factorValue K L :=
  QuotientGroup.map (K.subgroupOf L) (K.subgroupOf L) (conjugate L g)
    (fun {x} hx => hK.conj_mem x hx g)

instance factorActionValue (K L : Subgroup G) [K.Normal] [L.Normal] :
    gGroupValue G (factorValue K L) where
  smul g z := conjugationMap K L g z
  one_smul z := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
    change factorMkValue K L (conjugate L 1 x) = factorMkValue K L x
    congr 1
    apply Subtype.ext
    change (1 : G) * (x : G) * (1 : G)⁻¹ = x
    simp
  mul_smul g h z := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
    change factorMkValue K L (conjugate L (g * h) x) =
      factorMkValue K L (conjugate L g (conjugate L h x))
    congr 1
    apply Subtype.ext
    change (g * h) * (x : G) * (g * h)⁻¹ = g * (h * (x : G) * h⁻¹) * g⁻¹
    simp [mul_inv_rev, mul_assoc]
  smul_one g := (conjugationMap K L g).map_one
  smul_mul g x y := (conjugationMap K L g).map_mul x y

def FactorActionType : Type (u + 1) :=
  {G : Type u} → [Group G] → (K L : Subgroup G) → [K.Normal] → [L.Normal] →
    gGroupValue G (factorValue K L)

end Factor

/-- The quotient at step i, where term i.castSucc is the lower term. -/
def chiefFactorValue {G : Type u} [Group G] [Finite G]
    (s : Chain G) (i : Fin s.length) : Type u :=
  factorValue (s.term i.castSucc) (s.term i.succ)

instance chiefFactorGroup {G : Type u} [Group G] [Finite G]
    (s : Chain G) (i : Fin s.length) : Group (chiefFactorValue s i) :=
  letI := s.normal i.castSucc
  inferInstanceAs (Group (factorValue (s.term i.castSucc) (s.term i.succ)))

instance chiefFactorActionValue {G : Type u} [Group G] [Finite G] (s : Chain G)
    (i : Fin s.length) : gGroupValue G (chiefFactorValue s i) :=
  letI := s.normal i.castSucc
  letI := s.normal i.succ
  factorActionValue (s.term i.castSucc) (s.term i.succ)

def ChiefFactorType : Type (u + 1) :=
  {G : Type u} → [Group G] → [Finite G] → (s : Chain G) → Fin s.length → Type u

def ChiefFactorActionType : Type (u + 1) :=
  {G : Type u} → [Group G] → [Finite G] →
    (s : Chain G) → (i : Fin s.length) → gGroupValue G (chiefFactorValue s i)

/-- The quotient types in order, with one entry per step. The group and
action for each entry are supplied by the instances for that step. -/
def chiefFactorTypesValue {G : Type u} [Group G] [Finite G] (s : Chain G) : List (Type u) :=
  List.ofFn (chiefFactorValue s)

def ChiefFactorTypesType : Type (u + 1) :=
  {G : Type u} → [Group G] → [Finite G] → Chain G → List (Type u)

def ChainCharacterization : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (r : ℕ) (N : Fin (r + 1) → Subgroup G),
    isChiefSeriesValue r N ↔
      ∃ s : Chain G, ∃ h : s.length = r,
        ∀ i : Fin (s.length + 1), s.term i = N (Fin.cast (congrArg (· + 1) h) i)

def StrictIncrease : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (s : Chain G), StrictMono s.term

def FactorActionOnRepresentatives : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [hL : L.Normal] (g : G) (x : L),
    g • factorMkValue K L x =
      factorMkValue K L ⟨g * (x : G) * g⁻¹, hL.conj_mem x x.property g⟩

def RestrictedActionIsInner : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal] (x : L),
    MulDistribMulAction.toMulAut G (factorValue K L) (x : G) =
      MulAut.conj (factorMkValue K L x)

def EveryInnerAutomorphismOccurs : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal] (z : factorValue K L),
    ∃ x : L, MulDistribMulAction.toMulAut G (factorValue K L) (x : G) = MulAut.conj z

def InvariantSubgroupNormal : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal]
    (H : Subgroup (factorValue K L)), gInvariantValue (G := G) H → H.Normal

def FactorListLength : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (s : Chain G), (chiefFactorTypesValue s).length = s.length

def ZeroLengthIffTrivial : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (s : Chain G), s.length = 0 ↔ Subsingleton G

def TrivialSeries : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Subsingleton G],
    ∃ s : Chain G, s.length = 0 ∧ chiefFactorTypesValue s = []

end Specs.ALG02GroupTheory.Chief.Series
