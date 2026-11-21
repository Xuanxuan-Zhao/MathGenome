import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions

/-! Independent specifications for the reduced-ring assertion in CM-14,
paper.tex:3753–3760. The local and global statements with dimension at most one
also include the zero-dimensional localizations of a one-dimensional ring. -/

universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def isField_of_isReduced_dim_eq_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsReduced R] [IsLocalRing R],
    ringKrullDim R = 0 → IsField R

def depth_eq_one_of_isReduced_dim_eq_oneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] [IsLocalRing R],
    ringKrullDim R = 1 → IsLocalRing.depth (ModuleCat.of R R) = 1

def localCohenMacaulay_of_isReduced_dim_le_oneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] [IsLocalRing R],
    ringKrullDim R ≤ 1 → LocalCohenMacaulayValue R R

def cohenMacaulayRing_of_isReduced_dim_le_oneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R],
    ringKrullDim R ≤ 1 → CohenMacaulayRingValue R

def cohenMacaulayRing_of_isReduced_dim_eq_oneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R],
    ringKrullDim R = 1 → CohenMacaulayRingValue R

end AdvCommAlg.CohenMacaulay.Specs
