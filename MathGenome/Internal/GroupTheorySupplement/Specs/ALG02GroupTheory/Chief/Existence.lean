import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series

/-! Existence and the minimal normal criterion (paper.tex, Proposition 1.2). -/

namespace Specs.ALG02GroupTheory.Chief.Existence

open Specs.ALG02GroupTheory.Chief.Series

universe u

/-- A nontrivial normal subgroup with no smaller nontrivial normal subgroup
of the same ambient group. -/
def isMinimalNormalValue {G : Type u} [Group G] (L : Subgroup G) : Prop :=
  L.Normal ∧ ⊥ < L ∧
    ∀ M : Subgroup G, M.Normal → ⊥ < M → M ≤ L → M = L

def IsMinimalNormalType : Type (u + 1) :=
  {G : Type u} → [Group G] → Subgroup G → Prop

def ChiefSeriesExists : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nonempty (Chain G)

/-- The canonical identification with the image inside the ambient quotient. -/
def FactorEquivQuotientImage : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] (_ : K ≤ L),
    ∃ e : factorValue K L ≃* L.map (QuotientGroup.mk' K),
      ∀ x : L, (e (factorMkValue K L x) : G ⧸ K) = QuotientGroup.mk' K (x : G)

def AmbientCoverIffMinimalNormal : Prop :=
  ∀ {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal],
    K < L → (ambientCovByValue K L ↔ isMinimalNormalValue (L.map (QuotientGroup.mk' K)))

def ChiefIffMinimalNormal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (r : ℕ) (N : Fin (r + 1) → Subgroup G),
    N 0 = ⊥ → N (Fin.last r) = ⊤ →
    ∀ (hNormal : ∀ i, (N i).Normal), StrictMono N →
    (isChiefSeriesValue r N ↔ ∀ i : Fin r,
      letI := hNormal i.castSucc
      isMinimalNormalValue ((N i.succ).map (QuotientGroup.mk' (N i.castSucc))))

end Specs.ALG02GroupTheory.Chief.Existence
