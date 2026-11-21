import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.FilteredContinua

/-!
Independent definitions and statements for paper.tex,
`d10:06:irreducible-continuum` and the continuum convention in
`d10:06:continuum-scope`. A continuum is nonempty, compact by open
covers, connected, and Hausdorff. No metric or countability assumption
is imposed. Subsets always have their induced topology.
-/

open Set
universe u

namespace D10Topology.Ch06.IrreducibleContinuaData

/-- The manuscript's nonmetric convention for a continuum. -/
def Continuum (K : Type u) [TopologicalSpace K] : Prop :=
  Nonempty K ∧ Specs.D10Topology.Ch05.Compactness.CoverCompact K ∧
    ConnectednessData.Connected K ∧ T2Space K

/-- A subset is a subcontinuum when its induced space is a continuum. -/
def Subcontinuum {K : Type u} [TopologicalSpace K] (L : Set K) : Prop :=
  Continuum L

/-- Minimality among subcontinua containing both specified points. -/
def IrreducibleBetween {K : Type u} [TopologicalSpace K]
    (L : Set K) (x y : K) : Prop :=
  Subcontinuum L ∧ x ∈ L ∧ y ∈ L ∧
    ∀ M : Set K, Subcontinuum M → x ∈ M → y ∈ M → M ⊆ L → M = L

end D10Topology.Ch06.IrreducibleContinuaData

namespace Specs.D10Topology.Ch06.IrreducibleContinua

open _root_.D10Topology.Ch06.IrreducibleContinuaData

def continuumType : Type (u + 1) :=
  (K : Type u) → [TopologicalSpace K] → Prop
def continuumValue : continuumType := Continuum

def subcontinuumType : Type (u + 1) :=
  {K : Type u} → [TopologicalSpace K] → Set K → Prop
def subcontinuumValue : subcontinuumType := @Subcontinuum

def irreducibleBetweenType : Type (u + 1) :=
  {K : Type u} → [TopologicalSpace K] → Set K → K → K → Prop
def irreducibleBetweenValue : irreducibleBetweenType := @IrreducibleBetween

/-- This also records that Hausdorffness is inherited by a subcontinuum. -/
def subcontinuum_iff : Prop :=
  ∀ {K : Type u} [TopologicalSpace K] [T2Space K] (L : Set K),
    Subcontinuum L ↔ L.Nonempty ∧ Ch05.Compactness.SubspaceCompact L ∧
      _root_.D10Topology.Ch06.ConnectednessData.ConnectedSubset L

def univ_subcontinuum : Prop :=
  ∀ (K : Type u) [TopologicalSpace K], Continuum K → Subcontinuum (univ : Set K)

/-- A is arbitrary and need not be closed; minimality is not uniqueness. -/
def exists_minimal_subcontinuum : Prop :=
  ∀ (K : Type u) [TopologicalSpace K], Continuum K →
    ∀ A : Set K, A.Nonempty →
      ∃ L : Set K, Subcontinuum L ∧ A ⊆ L ∧
        ∀ M : Set K, Subcontinuum M → A ⊆ M → M ⊆ L → M = L

def exists_irreducible_between : Prop :=
  ∀ (K : Type u) [TopologicalSpace K], Continuum K →
    ∀ x y : K, ∃ L : Set K, IrreducibleBetween L x y

end Specs.D10Topology.Ch06.IrreducibleContinua
